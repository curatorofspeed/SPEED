#!/usr/bin/env python3
"""
============================================================================
 AUCTION RADAR — ingestion worker
 Pulls upcoming collector-car lots from a source, normalizes them to the
 `auction_lots` schema, and upserts into Supabase. Ships with a Bring a
 Trailer adapter; adding a source is a ~20-line subclass.
============================================================================

WHAT IT DOES
  1. Discovers current listing URLs for a source.
  2. Extracts each lot from schema.org JSON-LD (the machine-readable block
     sites publish for crawlers) -> Open Graph meta -> an HTML fallback hook.
  3. Normalizes messy titles into year / make / model / trim and derives
     reserve status, price, currency, and a rough category.
  4. Upserts on (source_name, external_lot_id) so re-runs update in place.
  5. Reconciles: lots not seen for STALE_DAYS get marked 'withdrawn'.

RESPECTFUL BY DEFAULT  (matches the product's own rules: link back, facts only)
  - Identifies itself with a contactable User-Agent.
  - Honors robots.txt (skips disallowed URLs; use --no-robots only if you
    have explicit permission).
  - Rate-limits every request (RADAR_REQUEST_DELAY) and backs off on 429/5xx.
  - Captures listing image URLs by default (RADAR_CAPTURE_IMAGES=false to
    disable). The page hotlinks them and never rehosts; confirm each source
    permits hotlinking. Stores facts + a source link, not galleries.
  - For sources whose terms require it, prefer an official feed / partner
    data / a licensed Apify actor over HTML. Confirm each source's ToS.

SETUP
  pip install -r requirements.txt
  export SUPABASE_URL="https://YOURPROJECT.supabase.co"
  export SUPABASE_SERVICE_KEY="<service_role key>"   # SERVER-SIDE ONLY. Never ship this.

RUN
  python radar_worker.py --selftest                  # offline: prove the parser
  python radar_worker.py --list-sources
  python radar_worker.py --source bringatrailer --limit 10 --dry-run   # print rows, no DB
  python radar_worker.py --source bringatrailer                        # ingest + upsert
  # schedule with cron / a Vercel cron / GitHub Action, e.g. every 30 min.

ADD A SOURCE
  Subclass JSONLDListingAdapter, set `config`, implement discover(), and
  override the small hooks (make_external_id / detect_reserve / end time /
  location) as needed. Register it in ADAPTERS. See BringATrailerAdapter.
============================================================================
"""
from __future__ import annotations

import argparse
import datetime as dt
import html
import json
import logging
import os
import re
import time
from dataclasses import dataclass
from typing import Iterator, Optional
from urllib.parse import urlparse, quote
from urllib import robotparser

import requests

# ---------------------------------------------------------------------------
# config (env-driven)
# ---------------------------------------------------------------------------
SUPABASE_URL = os.environ.get("SUPABASE_URL", "").rstrip("/")
SUPABASE_SERVICE_KEY = os.environ.get("SUPABASE_SERVICE_KEY", "")  # service_role — server-side only

USER_AGENT = os.environ.get(
    "RADAR_USER_AGENT",
    "AuctionRadarBot/0.1 (+https://curatorofspeed.com; contact: hello@kittitasdigital.com)",
)
REQUEST_DELAY = float(os.environ.get("RADAR_REQUEST_DELAY", "2.5"))   # seconds between requests
REQUEST_TIMEOUT = float(os.environ.get("RADAR_TIMEOUT", "20"))
MAX_RETRIES = int(os.environ.get("RADAR_MAX_RETRIES", "3"))
CAPTURE_IMAGE_URLS = os.environ.get("RADAR_CAPTURE_IMAGES", "true").lower() == "true"
STALE_DAYS = float(os.environ.get("RADAR_STALE_DAYS", "2"))

logging.basicConfig(
    level=os.environ.get("RADAR_LOG", "INFO").upper(),
    format="%(asctime)s  %(levelname)-7s %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("radar")


# ---------------------------------------------------------------------------
# normalization helpers
# ---------------------------------------------------------------------------
# Multi-word makes MUST come before single-word ones so prefix matching wins.
MAKES = [
    "Mercedes-Benz", "Alfa Romeo", "Aston Martin", "Land Rover", "Rolls-Royce",
    "De Tomaso", "Ferrari", "Porsche", "Lamborghini", "McLaren", "Maserati",
    "Bugatti", "Pagani", "Koenigsegg", "Lancia", "Lotus", "Jaguar", "Bentley",
    "BMW", "Audi", "Volkswagen", "Mercedes", "Chevrolet", "Ford", "Dodge",
    "Shelby", "Pontiac", "Cadillac", "Buick", "Plymouth", "Nissan", "Datsun",
    "Toyota", "Lexus", "Honda", "Acura", "Mazda", "Subaru", "Mitsubishi",
    "Alpine", "Renault", "Peugeot", "Citroen", "Saab", "Volvo", "Fiat",
    "Abarth", "Triumph", "MG", "Austin-Healey", "Healey", "Morgan", "TVR",
    "Tesla", "Hummer", "GMC", "AMG", "Bizzarrini", "Iso", "Facel",
]
_MAKES_SORTED = sorted(MAKES, key=len, reverse=True)
YEAR_RE = re.compile(r"\b(19[0-9]{2}|20[0-4][0-9])\b")
NORESERVE_RE = re.compile(r"\bno\s*reserve\b", re.I)

RACE_HINTS = re.compile(
    r"\b(gt3|gt2|gt4|cup|trofeo|works|race|racing|competiz|le\s*mans|fia|"
    r"group\s*[abc4-9]|tubolare|stradale\b.*race|homolog|rally)\b", re.I)
SUPERCAR_HINTS = re.compile(
    r"\b(f40|f50|enzo|laferrari|carrera\s*gt|zonda|huayra|918|senna|"
    r"speedtail|veyron|chiron|mclaren\s*f1|countach|reventon|sesto)\b", re.I)


def split_make_model(rest: str) -> tuple[Optional[str], Optional[str]]:
    low = rest.lower()
    for mk in _MAKES_SORTED:
        if low.startswith(mk.lower() + " ") or low == mk.lower():
            model = rest[len(mk):].strip(" -–—")
            return mk, (model or None)
    # fallback: first token is the make, remainder the model
    parts = rest.split()
    if not parts:
        return None, None
    if len(parts) == 1:
        return parts[0], None
    return parts[0], " ".join(parts[1:])


def normalize_title(title: str) -> tuple[Optional[int], Optional[str], Optional[str], Optional[str]]:
    """messy listing title -> (year, make, model, reserve_or_None)."""
    reserve = None
    t = html.unescape(title or "").strip()
    m = re.match(r"^\s*no\s*reserve\s*[:\-]\s*", t, re.I)
    if m:
        reserve = "no-reserve"
        t = t[m.end():]
    # drop trailing par/sale noise
    t = re.sub(r"\s*\((?:lot|no\.?)\s*[\w\-]+\)\s*$", "", t, flags=re.I).strip()
    ym = YEAR_RE.search(t)
    year = int(ym.group(0)) if ym else None
    rest = (t[ym.end():] if ym else t).strip(" -–—,")
    make, model = split_make_model(rest)
    return year, make, model, reserve


def category_for(year: Optional[int], title: str) -> str:
    if SUPERCAR_HINTS.search(title):
        return "Supercar"
    if RACE_HINTS.search(title):
        return "Race"
    if year is not None:
        if year >= 2015:
            return "Modern"
        if year < 1990:
            return "Classic"
        return "Modern"
    return "Classic"


_CUR = {"$": "USD", "£": "GBP", "€": "EUR", "USD": "USD", "GBP": "GBP", "EUR": "EUR"}


def to_float(v) -> Optional[float]:
    if v is None:
        return None
    try:
        s = re.sub(r"[^0-9.]", "", str(v))
        return float(s) if s else None
    except ValueError:
        return None


def parse_money(s: str) -> tuple[Optional[float], str]:
    if not s:
        return None, "USD"
    cur = "USD"
    for sym, code in _CUR.items():
        if sym in s:
            cur = code
            break
    return to_float(s), cur


# ---------------------------------------------------------------------------
# JSON-LD / meta extraction (standards-based, stable across redesigns)
# ---------------------------------------------------------------------------
LD_RE = re.compile(
    r'<script[^>]+type=["\']application/ld\+json["\'][^>]*>(.*?)</script>', re.S | re.I)


def extract_jsonld(text: str) -> list[dict]:
    blocks: list[dict] = []
    for m in LD_RE.finditer(text):
        raw = m.group(1).strip()
        try:
            data = json.loads(raw)
        except Exception:
            continue
        if isinstance(data, dict) and "@graph" in data:
            blocks.extend(x for x in data["@graph"] if isinstance(x, dict))
        elif isinstance(data, list):
            blocks.extend(x for x in data if isinstance(x, dict))
        elif isinstance(data, dict):
            blocks.append(data)
    return blocks


def find_type(blocks: list[dict], *types: str) -> Optional[dict]:
    want = {t.lower() for t in types}
    for b in blocks:
        t = b.get("@type")
        if isinstance(t, list) and any(str(x).lower() in want for x in t):
            return b
        if isinstance(t, str) and t.lower() in want:
            return b
    return None


def meta_content(text: str, prop: str) -> Optional[str]:
    p = re.escape(prop)
    for pat in (
        r'<meta[^>]+(?:property|name)=["\']' + p + r'["\'][^>]+content=["\'](.*?)["\']',
        r'<meta[^>]+content=["\'](.*?)["\'][^>]+(?:property|name)=["\']' + p + r'["\']',
    ):
        m = re.search(pat, text, re.I)
        if m:
            return html.unescape(m.group(1))
    return None


def first_image(img) -> Optional[str]:
    if not img:
        return None
    if isinstance(img, str):
        return img
    if isinstance(img, list) and img:
        return first_image(img[0])
    if isinstance(img, dict):
        return img.get("url") or img.get("contentUrl")
    return None


# ---------------------------------------------------------------------------
# small helpers for JSON-API sources (key names vary; be forgiving)
# ---------------------------------------------------------------------------
def _first(d: dict, *keys):
    """First present, non-empty value among keys. ([]/'' are treated empty;
    a literal False is returned, since it's a real value, not 'missing'.)"""
    if not isinstance(d, dict):
        return None
    for k in keys:
        if k in d:
            v = d[k]
            if v is not None and v != "" and v != []:
                return v
    return None


def _first_num(d: dict, *keys) -> Optional[float]:
    return to_float(_first(d, *keys))


def _abs_url(base: str, u: Optional[str]) -> Optional[str]:
    """Resolve a possibly-relative URL against a site base."""
    if not u or not isinstance(u, str):
        return None
    u = u.strip()
    if u.startswith("//"):
        return "https:" + u
    if u.startswith("http"):
        return u
    return base.rstrip("/") + "/" + u.lstrip("/")


def _slugify(s: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", (s or "").lower()).strip("-")[:80] or "lot"


_DATE_FORMATS = (
    "%Y-%m-%dT%H:%M:%S", "%Y-%m-%dT%H:%M", "%Y-%m-%d %H:%M:%S",
    "%Y-%m-%d", "%d %B %Y", "%d %b %Y", "%B %d, %Y", "%b %d, %Y",
    "%A, %d %B %Y", "%m/%d/%Y",
)


def _to_iso(v) -> Optional[str]:
    """Best-effort parse of a date string/epoch into an ISO-8601 timestamp.
    Returns None (never a non-ISO string) so a timestamptz upsert can't break."""
    if v is None:
        return None
    s = str(v).strip()
    if not s:
        return None
    try:                                   # already ISO-ish (handles date-only + offsets)
        return dt.datetime.fromisoformat(s.replace("Z", "+00:00")).isoformat()
    except ValueError:
        pass
    if re.fullmatch(r"\d{10,13}", s):      # epoch seconds / millis
        n = int(s)
        if len(s) == 13:
            n //= 1000
        return dt.datetime.fromtimestamp(n, dt.timezone.utc).isoformat()
    s2 = re.sub(r"\s+(?:GMT|UTC|EST|EDT|PST|PDT|CET|CEST)\b.*$", "", s).strip()
    for fmt in _DATE_FORMATS:
        try:
            return dt.datetime.strptime(s2, fmt).isoformat()
        except ValueError:
            continue
    return None


def _to_iso_tz(naive, tzname) -> Optional[str]:
    """Localize a NAIVE wall-clock datetime string (e.g. '2026-06-29 12:00:00')
    in an IANA timezone (e.g. 'Europe/London') and return an ISO-8601 *UTC*
    timestamp. For sources that ship a local close time + a tz name rather than
    an absolute instant. If the value already carries tz info (a 'T'/'Z'/offset)
    or the tz database is unavailable, fall back to _to_iso (which treats the
    value as naive/UTC) so a timestamptz upsert can never break."""
    if not naive:
        return None
    s = str(naive).strip()
    if (not tzname) or ("T" in s) or s.endswith("Z") or re.search(r"[+\-]\d\d:?\d\d$", s):
        return _to_iso(naive)
    try:
        from zoneinfo import ZoneInfo
        for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M", "%Y-%m-%d"):
            try:
                naive_dt = dt.datetime.strptime(s, fmt)
            except ValueError:
                continue
            aware = naive_dt.replace(tzinfo=ZoneInfo(str(tzname)))
            return aware.astimezone(dt.timezone.utc).isoformat()
    except Exception:
        pass
    return _to_iso(naive)


def _parse_estimate_range(s) -> tuple[Optional[float], Optional[float], Optional[str]]:
    """(low, high, currency) from an RM-style estimate string such as
    '€450,000 - €550,000' or '$1,000,000 - $1,500,000'. Returns (None, None,
    None) for 'Estimate available upon request' / empty. Assumes comma
    thousands separators (RM renders EUR/GBP that way too)."""
    if not s or not isinstance(s, str):
        return None, None, None
    cur = None
    for sym, c in _CUR.items():
        if sym in s:
            cur = c
            break
    vals = []
    for n in re.findall(r"\d[\d,]*(?:\.\d+)?", s):
        f = to_float(n)
        if f is not None and f >= 100:        # skip stray small numbers
            vals.append(f)
    low = vals[0] if vals else None
    high = vals[1] if len(vals) > 1 else None
    return low, high, cur


def _parse_money(s) -> tuple[Optional[float], Optional[str]]:
    """Single realized/hammer figure + currency from a sold lot's value string
    (e.g. '£1,200,000 GBP', 'Sold for $2,500,000', 'Bid to €410,000'): the
    largest number present is taken as the price. Reuses the estimate parser's
    currency + number detection so symbol handling stays in one place."""
    low, high, cur = _parse_estimate_range(s)
    nums = [v for v in (low, high) if v is not None]
    return (max(nums) if nums else None), cur


_FLAG_CC_RE = re.compile(r"/([A-Za-z]{2})\.png", re.I)
_COUNTRY_BY_CC = {
    "us": "USA", "gb": "United Kingdom", "de": "Germany", "it": "Italy",
    "fr": "France", "es": "Spain", "ch": "Switzerland", "nl": "Netherlands",
    "be": "Belgium", "at": "Austria", "jp": "Japan", "ca": "Canada",
    "au": "Australia", "mc": "Monaco", "pt": "Portugal", "se": "Sweden",
    "dk": "Denmark", "no": "Norway", "ie": "Ireland", "lu": "Luxembourg",
    "ae": "United Arab Emirates", "sg": "Singapore", "hk": "Hong Kong",
    "nz": "New Zealand", "za": "South Africa", "br": "Brazil",
}


def _country_from_flag(s) -> Optional[str]:
    """RM ships location as a flag image path '/media/.../Flags/<id>/gb.png';
    the 2-letter code before .png is the country. Map it to a name."""
    if not s or not isinstance(s, str):
        return None
    m = _FLAG_CC_RE.search(s)
    if not m:
        return None
    cc = m.group(1).lower()
    return _COUNTRY_BY_CC.get(cc, cc.upper())


# ---------------------------------------------------------------------------
# the normalized record -> maps 1:1 to the `auction_lots` table
# ---------------------------------------------------------------------------
def _now_iso() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


@dataclass
class Lot:
    source_name: str
    external_lot_id: str
    auction_type: str                  # 'online' | 'live'
    source_url: Optional[str] = None
    auction_event_name: Optional[str] = None
    auction_start_date: Optional[str] = None
    auction_end_date: Optional[str] = None
    lot_number: Optional[str] = None
    year: Optional[int] = None
    make: Optional[str] = None
    model: Optional[str] = None
    trim: Optional[str] = None
    chassis: Optional[str] = None
    engine: Optional[str] = None
    transmission: Optional[str] = None
    mileage: Optional[str] = None
    location: Optional[str] = None
    estimate_low: Optional[float] = None
    estimate_high: Optional[float] = None
    current_bid: Optional[float] = None
    currency: str = "USD"
    reserve_status: str = "reserve"
    image_url: Optional[str] = None
    description_short: Optional[str] = None
    category: Optional[str] = None
    status: str = "upcoming"

    def is_valid(self) -> bool:
        return bool(self.source_name and self.external_lot_id and self.year and self.make)

    def to_row(self) -> dict:
        """Only emit fields we actually have, so upsert never nulls out
        manually-enriched columns. Always refresh last_seen_at + status."""
        always = {"source_name", "external_lot_id", "auction_type", "status"}
        row = {}
        for k, v in self.__dict__.items():
            if v is not None or k in always:
                row[k] = v
        row["last_seen_at"] = _now_iso()
        return row


# ---------------------------------------------------------------------------
# polite fetcher: robots.txt + rate-limit + backoff
# ---------------------------------------------------------------------------
class Fetcher:
    def __init__(self, respect_robots: bool = True):
        self.s = requests.Session()
        self.s.headers.update({
            "User-Agent": USER_AGENT,
            "Accept": "text/html,application/xhtml+xml,application/json;q=0.9,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.9",
        })
        self.respect_robots = respect_robots
        self._robots: dict[str, Optional[robotparser.RobotFileParser]] = {}
        self._last = 0.0

    def _allowed(self, url: str) -> bool:
        if not self.respect_robots:
            return True
        u = urlparse(url)
        host = f"{u.scheme}://{u.netloc}"
        if host not in self._robots:
            rp = robotparser.RobotFileParser()
            rp.set_url(host + "/robots.txt")
            try:
                rp.read()
            except Exception:
                rp = None
            self._robots[host] = rp
        rp = self._robots[host]
        return True if rp is None else rp.can_fetch(USER_AGENT, url)

    def _throttle(self):
        wait = REQUEST_DELAY - (time.monotonic() - self._last)
        if wait > 0:
            time.sleep(wait)
        self._last = time.monotonic()

    def get(self, url: str, headers: Optional[dict] = None) -> Optional[requests.Response]:
        if not self._allowed(url):
            log.warning("robots.txt disallows %s — skipping", url)
            return None
        for attempt in range(1, MAX_RETRIES + 1):
            self._throttle()
            try:
                r = self.s.get(url, timeout=REQUEST_TIMEOUT, headers=headers)
                if r.status_code == 429 or r.status_code >= 500:
                    backoff = min(60, REQUEST_DELAY * (2 ** attempt))
                    log.warning("HTTP %s on %s — backoff %.1fs", r.status_code, url, backoff)
                    time.sleep(backoff)
                    continue
                r.raise_for_status()
                return r
            except requests.RequestException as e:
                log.warning("request error %s (attempt %d/%d): %s", url, attempt, MAX_RETRIES, e)
                time.sleep(min(30, REQUEST_DELAY * (2 ** attempt)))
        log.error("giving up on %s after %d attempts", url, MAX_RETRIES)
        return None

    def post_json(self, url: str, payload: dict,
                  headers: Optional[dict] = None) -> Optional[requests.Response]:
        """POST a JSON body with the same throttle/backoff/robots policy as
        get(). Reuses the session, so cookies picked up by a prior get() (e.g.
        an ASP.NET antiforgery token) are sent automatically."""
        if not self._allowed(url):
            log.warning("robots.txt disallows %s — skipping", url)
            return None
        hdrs = {"Content-Type": "application/json;charset=utf-8",
                "Accept": "application/json, text/plain, */*"}
        if headers:
            hdrs.update(headers)
        body = json.dumps(payload)
        for attempt in range(1, MAX_RETRIES + 1):
            self._throttle()
            try:
                r = self.s.post(url, data=body, headers=hdrs, timeout=REQUEST_TIMEOUT)
                if r.status_code == 429 or r.status_code >= 500:
                    backoff = min(60, REQUEST_DELAY * (2 ** attempt))
                    log.warning("HTTP %s on %s — backoff %.1fs", r.status_code, url, backoff)
                    time.sleep(backoff)
                    continue
                r.raise_for_status()
                return r
            except requests.RequestException as e:
                log.warning("post error %s (attempt %d/%d): %s", url, attempt, MAX_RETRIES, e)
                time.sleep(min(30, REQUEST_DELAY * (2 ** attempt)))
        log.error("giving up on POST %s after %d attempts", url, MAX_RETRIES)
        return None


# ---------------------------------------------------------------------------
# Supabase REST client (service role; writes bypass RLS)
# ---------------------------------------------------------------------------
class Supabase:
    def __init__(self, url: str, key: str):
        self.url = url
        self.enabled = bool(url and key)
        self.h = {
            "apikey": key,
            "Authorization": f"Bearer {key}",
            "Content-Type": "application/json",
        }

    def ensure_source(self, cfg: "SourceConfig"):
        if not self.enabled:
            return
        payload = [{
            "name": cfg.name, "base_url": cfg.base_url,
            "scrape_method": cfg.scrape_method, "terms_notes": cfg.terms_notes,
        }]
        r = requests.post(
            f"{self.url}/rest/v1/auction_sources?on_conflict=name",
            headers={**self.h, "Prefer": "resolution=ignore-duplicates,return=minimal"},
            json=payload, timeout=REQUEST_TIMEOUT)
        r.raise_for_status()

    def upsert_lots(self, rows: list[dict]) -> int:
        if not self.enabled or not rows:
            return 0
        # PostgREST runs one INSERT ... ON CONFLICT; the same conflict target
        # appearing twice in a single batch trips PG 21000 ("cannot affect row a
        # second time"). Happens when a lot is cross-listed across sub-auctions.
        # Dedupe on (source_name, external_lot_id) — last write wins.
        deduped: dict = {}
        for row in rows:
            deduped[(row.get("source_name"), row.get("external_lot_id"))] = row
        if len(deduped) != len(rows):
            log.info("deduped %d -> %d row(s) on (source_name, external_lot_id)",
                     len(rows), len(deduped))
        rows = list(deduped.values())
        # PostgREST bulk insert requires every object to share the same keys,
        # but optional specs (mileage, engine, …) are only on some lots. Union
        # all keys and backfill the missing ones with None so the batch is uniform.
        all_keys: set = set()
        for row in rows:
            all_keys.update(row.keys())
        rows = [{k: row.get(k) for k in all_keys} for row in rows]
        r = requests.post(
            f"{self.url}/rest/v1/auction_lots?on_conflict=source_name,external_lot_id",
            headers={**self.h, "Prefer": "resolution=merge-duplicates,return=minimal"},
            json=rows, timeout=REQUEST_TIMEOUT)
        if r.status_code >= 400:
            log.error("Supabase upsert %s: %s", r.status_code, r.text[:600])
        r.raise_for_status()
        return len(rows)

    def reconcile_stale(self, source_name: str, stale_days: float) -> None:
        if not self.enabled:
            return
        cutoff = (dt.datetime.now(dt.timezone.utc) - dt.timedelta(days=stale_days)).isoformat()
        url = (f"{self.url}/rest/v1/auction_lots"
               f"?source_name=eq.{quote(source_name)}"
               f"&status=eq.upcoming&last_seen_at=lt.{quote(cutoff)}")
        r = requests.patch(url, headers={**self.h, "Prefer": "return=minimal"},
                           json={"status": "withdrawn"}, timeout=REQUEST_TIMEOUT)
        r.raise_for_status()

    def rpc(self, fn: str, args: dict):
        r = requests.post(f"{self.url}/rest/v1/rpc/{fn}", headers=self.h,
                          json=args, timeout=REQUEST_TIMEOUT)
        r.raise_for_status()
        return r.json()

    def record_alerts(self, triples: list) -> int:
        if not triples:
            return 0
        rows = [{"query_id": q, "lot_id": l, "reason": rs} for (q, l, rs) in triples]
        r = requests.post(
            f"{self.url}/rest/v1/alerts_sent?on_conflict=query_id,lot_id,reason",
            headers={**self.h, "Prefer": "resolution=ignore-duplicates,return=minimal"},
            json=rows, timeout=REQUEST_TIMEOUT)
        r.raise_for_status()
        return len(rows)

    def hot_lots(self, hot_hours: int, limit: int = 200) -> list:
        now = dt.datetime.now(dt.timezone.utc)
        cutoff = now + dt.timedelta(hours=hot_hours)
        url = (f"{self.url}/rest/v1/auction_lots"
               f"?select=id,source_url,source_name,external_lot_id"
               f"&auction_type=eq.online&status=eq.upcoming"
               f"&auction_end_date=gt.{quote(now.isoformat())}"
               f"&auction_end_date=lt.{quote(cutoff.isoformat())}"
               f"&order=auction_end_date.asc&limit={limit}")
        r = requests.get(url, headers=self.h, timeout=REQUEST_TIMEOUT)
        r.raise_for_status()
        return r.json()

    def closed_lots(self, limit: int = 200) -> list:
        now = dt.datetime.now(dt.timezone.utc).isoformat()
        url = (f"{self.url}/rest/v1/auction_lots"
               f"?select=id,source_url,source_name,external_lot_id,year,make,model,trim,mileage,currency"
               f"&auction_type=eq.online&status=in.(upcoming,live)"
               f"&auction_end_date=lt.{quote(now)}"
               f"&order=auction_end_date.asc&limit={limit}")
        r = requests.get(url, headers=self.h, timeout=REQUEST_TIMEOUT)
        r.raise_for_status()
        return r.json()

    def insert_sales(self, rows: list) -> int:
        if not rows:
            return 0
        r = requests.post(
            f"{self.url}/rest/v1/sales_history?on_conflict=source,external_id",
            headers={**self.h, "Prefer": "resolution=ignore-duplicates,return=minimal"},
            json=rows, timeout=REQUEST_TIMEOUT)
        r.raise_for_status()
        return len(rows)

    def finalize_lot(self, lot_id, status: str, final_price=None) -> None:
        body = {"status": status}
        if final_price is not None:
            body["current_bid"] = final_price
        r = requests.patch(f"{self.url}/rest/v1/auction_lots?id=eq.{lot_id}",
                           headers={**self.h, "Prefer": "return=minimal"},
                           json=body, timeout=REQUEST_TIMEOUT)
        r.raise_for_status()


# ---------------------------------------------------------------------------
# adapters
# ---------------------------------------------------------------------------
@dataclass
class SourceConfig:
    name: str
    base_url: str
    auction_type: str                # 'online' | 'live'
    scrape_method: str = "html"
    terms_notes: str = ""


class SourceAdapter:
    config: SourceConfig

    def discover(self, fetcher: Fetcher) -> Iterator[str]:
        raise NotImplementedError

    def parse(self, url: str, fetcher: Fetcher) -> Optional[Lot]:
        resp = fetcher.get(url)
        if not resp:
            return None
        return self.parse_html(url, resp.text)

    def parse_html(self, url: str, text: str) -> Optional[Lot]:
        raise NotImplementedError

    def collect(self, fetcher: Fetcher, limit: Optional[int] = None) -> list[Lot]:
        lots, seen = [], 0
        for url in self.discover(fetcher):
            if limit and seen >= limit:
                break
            seen += 1
            try:
                lot = self.parse(url, fetcher)
                if lot:
                    lots.append(lot)
            except Exception as e:  # never let one listing kill the run
                log.warning("parse failed %s: %s", url, e)
        return lots


class JSONLDListingAdapter(SourceAdapter):
    """Generic per-listing extractor: JSON-LD -> Open Graph -> HTML hook.
    Subclasses set `config`, implement discover(), and override the small
    hooks below for site-specific bits."""

    # --- hooks subclasses may override ---
    def make_external_id(self, url: str) -> str:
        return url.rstrip("/").rsplit("/", 1)[-1]

    def detect_reserve(self, text: str, title: str) -> Optional[str]:
        if NORESERVE_RE.search(title) or NORESERVE_RE.search(text[:20000]):
            return "no-reserve"
        return None

    def extract_end_time(self, text: str, offers: dict) -> Optional[str]:
        for k in ("priceValidUntil", "availabilityEnds", "validThrough"):
            if offers.get(k):
                return offers[k]
        # documented HTML hook — confirm against the live page if JSON-LD lacks it
        m = re.search(r'"(?:auction_?end|end_?(?:time|date)|ends_at)"\s*:\s*"([^"]+)"', text, re.I)
        return m.group(1) if m else None

    def extract_location(self, text: str, product: dict) -> Optional[str]:
        return None

    def extract_specs(self, product: dict) -> dict:
        """pull structured vehicle props when present (schema.org Vehicle)."""
        out = {}
        eng = product.get("vehicleEngine")
        if isinstance(eng, dict):
            out["engine"] = eng.get("name") or eng.get("engineType")
        trans = product.get("vehicleTransmission")
        if isinstance(trans, str):
            out["transmission"] = trans
        odo = product.get("mileageFromOdometer")
        if isinstance(odo, dict) and odo.get("value"):
            unit = "mi" if str(odo.get("unitCode", "")).upper() in ("SMI", "MI") else "km"
            out["mileage"] = f"{int(to_float(odo['value'])):,} {unit}"
        vin = product.get("vehicleIdentificationNumber")
        if isinstance(vin, str):
            out["chassis"] = vin
        return out

    # --- shared parse ---
    def parse_html(self, url: str, text: str) -> Optional[Lot]:
        blocks = extract_jsonld(text)
        product = find_type(blocks, "Product", "Car", "Vehicle", "IndividualProduct", "ProductModel")

        title = image = end = bid = location = desc = None
        currency = "USD"
        specs: dict = {}

        if product:
            title = product.get("name")
            image = first_image(product.get("image"))
            desc = product.get("description")
            location = self.extract_location(text, product)
            specs = self.extract_specs(product)
            offers = product.get("offers") or {}
            if isinstance(offers, list):
                offers = offers[0] if offers else {}
            if isinstance(offers, dict):
                bid = to_float(offers.get("price") or offers.get("lowPrice"))
                currency = offers.get("priceCurrency") or "USD"
                end = self.extract_end_time(text, offers)

        if not title:
            title = meta_content(text, "og:title")
            image = image or meta_content(text, "og:image")
            desc = desc or meta_content(text, "og:description")
            if bid is None:
                amt = meta_content(text, "product:price:amount")
                cur = meta_content(text, "product:price:currency")
                bid = to_float(amt)
                currency = cur or currency

        if not title:
            title = self.parse_html_fallback(text)   # <- site-specific, confirm on live DOM
        if not title:
            return None

        year, make, model, reserve = normalize_title(title)
        reserve = reserve or self.detect_reserve(text, title) or "reserve"
        if end is None:
            end = self.extract_end_time(text, {})

        cfg = self.config
        lot = Lot(
            source_name=cfg.name,
            external_lot_id=self.make_external_id(url),
            auction_type=cfg.auction_type,
            source_url=url,
            auction_event_name=("Online" if cfg.auction_type == "online" else None),
            auction_end_date=end if cfg.auction_type == "online" else None,
            auction_start_date=end if cfg.auction_type == "live" else None,
            year=year, make=make, model=model,
            currency=currency,
            current_bid=bid if cfg.auction_type == "online" else None,
            reserve_status=reserve,
            image_url=(image if CAPTURE_IMAGE_URLS else None),
            description_short=(desc[:400] if desc else None),
            category=category_for(year, title),
            location=location,
            **specs,
        )
        return lot

    def parse_html_fallback(self, text: str) -> Optional[str]:
        """Last-resort title pull. Override per source with a confirmed
        selector if the site exposes neither JSON-LD nor OG title."""
        m = re.search(r"<title[^>]*>(.*?)</title>", text, re.S | re.I)
        return html.unescape(m.group(1)).strip() if m else None

    def parse_result(self, url: str, text: str) -> dict:
        """Best-effort final outcome for a CLOSED listing. Returns
        {'sold':bool,'sold_price':float|None,'currency':str,'sold_date':str|None}.
        For a reserve-not-met / 'Bid to' close it returns sold=False but a
        'final_bid' (the high bid the auction reached) so the displayed figure
        can be corrected to reality even though no sale occurred. Confirm the
        patterns against a real completed page for each source."""
        head = text[:40000]
        _CUR = {"£": "GBP", "€": "EUR", "$": "USD"}
        sold_m = re.search(r"sold\s+for[^0-9$£€]*([$£€])?\s*([\d][\d,]*)", head, re.I)
        if sold_m:
            price = to_float(sold_m.group(2))
            currency = _CUR.get(sold_m.group(1) or "", "USD")
            sold_date = None
            dm = re.search(r"sold\s+for[^.]*?on\s+([A-Z][a-z]+ \d{1,2},? \d{4})", head, re.I)
            if dm:
                try:
                    sold_date = dt.datetime.strptime(dm.group(1).replace(",", ""), "%B %d %Y").date().isoformat()
                except ValueError:
                    sold_date = None
            if price:
                return {"sold": True, "sold_price": price, "currency": currency, "sold_date": sold_date}
        # Not sold: capture the final high bid if the page shows one ("Bid to
        # $76,000", "Reserve not met"). Records the real figure without logging
        # it as a comp.
        bid_m = re.search(r"bid\s+to[^0-9$£€]*([$£€])?\s*([\d][\d,]*)", head, re.I)
        if bid_m:
            fb = to_float(bid_m.group(2))
            if fb:
                return {"sold": False, "final_bid": fb, "currency": _CUR.get(bid_m.group(1) or "", "USD")}
        return {"sold": False}


class BringATrailerAdapter(JSONLDListingAdapter):
    config = SourceConfig(
        name="Bring a Trailer",
        base_url="https://bringatrailer.com",
        auction_type="online",
        scrape_method="html",
        terms_notes="Honor robots.txt; link back; facts + one placeholder only; no gallery rehosting.",
    )
    # The /auctions/ index now loads lots via JS (empty to a raw fetch); the
    # homepage serves them in the HTML. Confirmed live: ~170+ listing links.
    INDEX = "https://bringatrailer.com/"
    # Listing URLs look like https://bringatrailer.com/listing/<slug>/. The live
    # markup often omits the trailing slash and may be scheme-relative, so we
    # normalize in discover().
    LISTING_RE = re.compile(r"bringatrailer\.com/listing/[a-z0-9][a-z0-9\-]+", re.I)

    def discover(self, fetcher: Fetcher) -> Iterator[str]:
        resp = fetcher.get(self.INDEX)
        if not resp:
            return
        seen = set()
        for frag in self.LISTING_RE.findall(resp.text):
            url = "https://" + frag.split("//")[-1].rstrip("/") + "/"
            if url not in seen:
                seen.add(url)
                yield url

    # Real auction close time. Confirmed live, BaT exposes the same epoch three
    # ways: "end_timestamp":<n>, data-ends="<n>", data-until="<n>" (seconds).
    END_RE = re.compile(
        r'"end_timestamp"\s*:\s*(\d{10})'
        r'|data-(?:ends|until)="(\d{10})"',
        re.I)

    def extract_end_time(self, text: str, offers: dict) -> Optional[str]:
        m = self.END_RE.search(text)
        if m:
            epoch = int(m.group(1) or m.group(2))
            return dt.datetime.fromtimestamp(epoch, dt.timezone.utc).isoformat()
        # fall back to the generic JSON-LD / HTML hook
        return super().extract_end_time(text, offers)

    def make_external_id(self, url: str) -> str:
        return "bat:" + url.rstrip("/").rsplit("/", 1)[-1]

    def extract_location(self, text: str, product: dict) -> Optional[str]:
        # BaT shows seller location in the page; default to Online and let a
        # confirmed selector refine it later.
        return "Online"


class CarsAndBidsAdapter(JSONLDListingAdapter):
    config = SourceConfig(
        name="Cars & Bids",
        base_url="https://carsandbids.com",
        auction_type="online",
        scrape_method="html",
        terms_notes="Honor robots.txt; link back; facts + one placeholder only; no gallery rehosting.",
    )
    # Cars & Bids is a client-rendered SPA, so the homepage HTML usually has NO
    # listing links. Reliable discovery order: (1) the sitemap, which lists
    # auction URLs; (2) failing that, confirm the JSON the site itself fetches
    # and read that. The per-LISTING pages do expose server-rendered OG/JSON-LD
    # meta, so once a URL is known, parse_html works the same as for BaT.
    SITEMAP = "https://carsandbids.com/sitemap.xml"
    INDEX = "https://carsandbids.com/"
    LISTING_RE = re.compile(
        r"https://carsandbids\.com/auctions/[A-Za-z0-9]+/[a-z0-9][a-z0-9\-]+/?", re.I)

    def discover(self, fetcher: Fetcher) -> Iterator[str]:
        seen: set = set()
        for src in (self.SITEMAP, self.INDEX):
            resp = fetcher.get(src)
            if not resp:
                continue
            for href in self.LISTING_RE.findall(resp.text):
                u = href if href.endswith("/") else href + "/"
                if u not in seen:
                    seen.add(u)
                    yield u
            if seen:            # sitemap produced URLs; don't bother scraping the SPA index
                break

    def make_external_id(self, url: str) -> str:
        # .../auctions/<id>/<slug>/ -> cab:<id>
        parts = [p for p in url.split("/") if p]
        try:
            return "cab:" + parts[parts.index("auctions") + 1]
        except (ValueError, IndexError):
            return "cab:" + url.rstrip("/").rsplit("/", 1)[-1]

    def detect_reserve(self, text: str, title: str) -> Optional[str]:
        # C&B labels no-reserve sales prominently in-page; otherwise defer to base.
        if re.search(r"no\s*reserve", text[:20000], re.I):
            return "no-reserve"
        return super().detect_reserve(text, title)

    def extract_location(self, text: str, product: dict) -> Optional[str]:
        return "Online"


class RMSothebysAdapter(SourceAdapter):
    """RM Sotheby's — consumes the site's own JSON search API instead of HTML.

    The public lots grid is an Angular SPA, but it populates from a clean
    endpoint:  POST /api/search/SearchLots?page=&pageSize=  with a small JSON
    body {"Auction": "<CODE>", ...}. There is NO bearer token / API key — the
    only credential is an AspNetCore.Antiforgery cookie that any visitor is
    handed, so we warm a session with one GET, then POST per auction and page
    through `pager`. These are physical-sale lots (scheduled date + pre-sale
    estimate, no live countdown), so they ingest as auction_type='live'.

    Auction codes roll over as sales come and go. Discovery order at runtime:
      1. RADAR_RM_AUCTIONS env (comma list) — pins exact codes, highest pri.
      2. scrape the upcoming/auctions pages + sitemap for /auctions/<code>/.
      3. a built-in seed of known-upcoming codes (safety net).
    Discovered + seed are unioned, so a stale seed never blocks a fresh sale
    and a failed scrape never blocks a known one. Codes with no lots just
    return empty and are skipped.

    Field names in the JSON can vary, so mapping is defensive (_first/_first_num
    over several candidate keys) and the FIRST lot's raw keys are logged on each
    run — set RADAR_DUMP_RAW=1 to print the whole first item. Use that to lock
    any key that doesn't map on the first live run.

    Terms: facts + link back only, same rule as every other source. The data is
    the site's own public API with no auth token; still, confirm RM's ToS.
    """
    config = SourceConfig(
        name="RM Sotheby's",
        base_url="https://rmsothebys.com",
        auction_type="live",
        scrape_method="api",
        terms_notes="Public JSON search API; antiforgery-cookie only, no token. Facts + link back; confirm ToS.",
    )

    API = "https://rmsothebys.com/api/search/SearchLots"
    WARMUP = "https://rmsothebys.com/auctions/{code}/lots/"
    DISCOVERY_PAGES = (
        "https://rmsothebys.com/auctions",          # serves the codes; try first
        "https://rmsothebys.com/auctions/upcoming",  # 404s currently — fallback only
        "https://rmsothebys.com/sitemap.xml",
    )
    PAGE_SIZE = 40
    MAX_PAGES = 50                         # hard stop; pagers shouldn't exceed this
    # Known upcoming sale codes (recon 2026-06). Safety net only — runtime
    # discovery extends/overrides this. Update, or set RADAR_RM_AUCTIONS.
    SEED_CODES = ("tc26", "mo26", "wp26", "hf26", "lf26", "mu26")
    CODE_RE = re.compile(r"/auctions/([a-z0-9]{3,7})/", re.I)
    _NON_CODES = {"upcoming", "results", "lots", "past", "calendar", "all", "live", "online"}

    # ---- auction-code discovery -------------------------------------------
    def discover_codes(self, fetcher: Fetcher) -> list[str]:
        env = os.getenv("RADAR_RM_AUCTIONS", "").strip()
        if env:
            codes = [c.strip().lower() for c in env.split(",") if c.strip()]
            log.info("RM: auction codes from RADAR_RM_AUCTIONS: %s", codes)
            return codes
        found: set[str] = set()
        for page in self.DISCOVERY_PAGES:
            try:
                resp = fetcher.get(page)
            except Exception:
                resp = None
            if not resp:
                continue
            for c in self.CODE_RE.findall(resp.text):
                c = c.lower()
                if c not in self._NON_CODES:
                    found.add(c)
            if found:
                log.info("RM: discovered %d code(s) via %s", len(found), page)
                break
        union = list(dict.fromkeys(list(found) + list(self.SEED_CODES)))
        log.info("RM: auction codes to query: %s", union)
        return union

    # ---- the API call ------------------------------------------------------
    def _warm(self, fetcher: Fetcher) -> None:
        """Grab the session-wide antiforgery cookie ONCE (best-effort). The
        cookie is shared across all subsequent POSTs, so there's no need to warm
        per-auction — and warming a per-code lots page that 404s would burn the
        retry/backoff budget for nothing."""
        for url in ("https://rmsothebys.com/auctions", "https://rmsothebys.com/"):
            try:
                if fetcher.get(url):
                    return
            except Exception:
                pass

    def _search(self, fetcher: Fetcher, code: str, page: int) -> Optional[dict]:
        url = f"{self.API}?page={page}&pageSize={self.PAGE_SIZE}"
        payload = {
            "LocationCountry": [], "Collection": None, "Auction": code.upper(),
            "Day": None, "SortBy": "Default", "CategoryTag": [],
            "StillForSaleOnly": False,
        }
        headers = {"Origin": self.config.base_url,
                   "Referer": f"{self.config.base_url}/auctions/{code.lower()}/lots/"}
        resp = fetcher.post_json(url, payload, headers=headers)
        if not resp:
            return None
        try:
            return resp.json()
        except ValueError:
            log.warning("RM: non-JSON response for %s p%d", code, page)
            return None

    # ---- auction-level metadata (date/name/location) -----------------------
    # The per-lot JSON has no date; it lives on the auction. We look first in the
    # SearchLots response envelope (already fetched), then fall back to the
    # auction page's schema.org Event block.
    AUCTION_PAGE = "https://rmsothebys.com/auctions/{code}/"
    _DATE_KEYS = ("auctionDate", "date", "startDate", "saleDate", "auctionStartDate",
                  "dateFrom", "startsAt", "start", "beginDate", "startDateTime",
                  "auctionEndDate", "endDate", "dateUtc")

    def _meta_from_response(self, data: dict) -> dict:
        """Pull date/name/location from the response envelope's options blocks."""
        out: dict = {}
        opts: dict = {}
        for k in ("options", "Options", "availableOptions", "AvailableOptions",
                  "auction", "Auction"):
            v = data.get(k)
            if isinstance(v, dict):
                opts.update(v)
        for k in self._DATE_KEYS:
            iso = _to_iso(opts.get(k))
            if iso:
                out["date"] = iso
                break
        if "date" not in out:                       # multi-day sales: take earliest
            for k in ("days", "auctionDays", "Days", "dates"):
                arr = opts.get(k)
                if isinstance(arr, list) and arr:
                    cands = []
                    for d in arr:
                        if isinstance(d, dict):
                            for dk in ("date", "startDate", "day", "value", "dateUtc"):
                                iso = _to_iso(d.get(dk))
                                if iso:
                                    cands.append(iso)
                        else:
                            iso = _to_iso(d)
                            if iso:
                                cands.append(iso)
                    if cands:
                        out["date"] = min(cands)
                        break
        name = _first(opts, "auctionName", "name", "title", "header", "saleName")
        if name:
            out["name"] = name
        loc = _first(opts, "location", "city", "venue", "saleLocation", "locationName")
        if loc:
            out["location"] = loc
        return out

    def _meta_from_page(self, fetcher: Fetcher, code: str) -> dict:
        """Fallback: parse the auction page's schema.org Event for a start date."""
        out: dict = {}
        try:
            resp = fetcher.get(self.AUCTION_PAGE.format(code=code.lower()))
        except Exception:
            resp = None
        if not resp:
            return out
        text = resp.text
        try:
            ev = find_type(extract_jsonld(text), "Event", "SaleEvent",
                           "ExhibitionEvent", "BusinessEvent")
            if ev:
                iso = _to_iso(ev.get("startDate") or ev.get("startTime"))
                if iso:
                    out["date"] = iso
                if ev.get("name"):
                    out.setdefault("name", ev["name"])
                loc = ev.get("location")
                if isinstance(loc, dict):
                    out.setdefault("location", loc.get("name") or loc.get("address"))
        except Exception:
            pass
        if "date" not in out:                       # a visible "4 July 2026"-style date
            m = re.search(r'\b(\d{1,2}\s+(?:January|February|March|April|May|June|July|'
                          r'August|September|October|November|December)\s+20\d{2})\b', text)
            if m:
                iso = _to_iso(m.group(1))
                if iso:
                    out["date"] = iso
        return out

    def _auction_meta(self, fetcher: Fetcher, code: str, data: dict,
                      cache: dict) -> dict:
        if code not in cache:
            meta = self._meta_from_response(data)
            if "date" not in meta:                  # only hit the page if needed
                for k, v in self._meta_from_page(fetcher, code).items():
                    meta.setdefault(k, v)
            cache[code] = meta
            if meta.get("date"):
                log.info("RM: %s sale date %s", code.upper(), meta["date"][:10])
            else:
                log.info("RM: %s — no sale date found (lots show 'Date TBA')", code.upper())
        return cache[code]

    # ---- orchestration (overrides SourceAdapter.collect) -------------------
    def collect(self, fetcher: Fetcher, limit: Optional[int] = None) -> list[Lot]:
        lots: list[Lot] = []
        dumped = False
        codes = self.discover_codes(fetcher)
        self._warm(fetcher)                     # once; cookie is session-wide
        meta_cache: dict[str, dict] = {}
        for code in codes:
            total: Optional[int] = None
            for page in range(self.MAX_PAGES):
                data = self._search(fetcher, code, page)
                if not data:
                    break
                items = data.get("items") or data.get("Items") or []
                pager = data.get("pager") or data.get("Pager") or {}
                meta = self._auction_meta(fetcher, code, data, meta_cache)
                if total is None:
                    total = (pager.get("totalItems") or pager.get("TotalItems")
                             or (len(items) if items else 0))
                    if items:
                        log.info("RM: %s -> %s lot(s)", code.upper(), total)
                if items and not dumped:
                    log.info("RM: first lot raw keys: %s", sorted(items[0].keys()))
                    if os.getenv("RADAR_DUMP_RAW"):
                        print(json.dumps(items[0], indent=2, default=str))
                        envelope = {k: v for k, v in data.items()
                                    if k.lower() not in ("items",)}
                        print("--- RESPONSE ENVELOPE (options / availableOptions / pager) ---")
                        print(json.dumps(envelope, indent=2, default=str)[:3500])
                    dumped = True
                for raw in items:
                    if not isinstance(raw, dict):
                        continue
                    try:
                        lot = self._to_lot(raw, code, meta)
                    except Exception as e:
                        log.warning("RM: lot parse failed (%s): %s", code, e)
                        continue
                    if lot:
                        lots.append(lot)
                        if limit and len(lots) >= limit:
                            return lots
                if not items or (page + 1) * self.PAGE_SIZE >= (total or 0):
                    break
        return lots

    # ---- field mapping (defensive; refine from the logged raw keys) --------
    # value must look like an image ref before we trust an ambiguous key
    _IMG_LIKE = re.compile(r"https?://|^//|^/|\.(?:jpe?g|png|webp|avif|gif)", re.I)

    def _extract_image(self, raw: dict) -> Optional[str]:
        # RM puts the lot photo in "crop" (a CDN .webp). "header" is the sale
        # NAME text, never an image — do not include it here.
        for k in ("crop", "image", "imageUrl", "primaryImage", "mainImage",
                  "heroImage", "coverImage", "thumbnail", "thumbnailUrl", "photo", "photoUrl"):
            v = raw.get(k)
            if isinstance(v, str) and v.strip() and self._IMG_LIKE.search(v.strip()):
                return _abs_url(self.config.base_url, v)
            if v and not isinstance(v, str):
                got = first_image(v)
                if got:
                    return _abs_url(self.config.base_url, got)
        for k in ("images", "photos", "media", "gallery", "lotImages", "assets"):
            v = raw.get(k)
            if not v:
                continue
            got = first_image(v)
            if not got and isinstance(v, list) and v and isinstance(v[0], dict):
                d0 = v[0]
                got = (d0.get("url") or d0.get("imageUrl") or d0.get("src")
                       or d0.get("contentUrl") or d0.get("href"))
            if got:
                return _abs_url(self.config.base_url, got)
        return None

    def _extract_url(self, raw: dict, code: str) -> Optional[str]:
        for k in ("url", "lotUrl", "detailUrl", "permalink", "path", "link",
                  "seoUrl", "canonicalUrl", "pageUrl"):
            v = raw.get(k)
            if isinstance(v, str) and v.strip():
                return _abs_url(self.config.base_url, v)
        slug = _first(raw, "slug", "seoName", "seoSlug", "urlSlug")
        if slug:
            return f"{self.config.base_url}/auctions/{code.lower()}/lots/{slug}/"
        return self.WARMUP.format(code=code.lower())   # always a valid link-back

    @staticmethod
    def _currency_from_text(s: str) -> Optional[str]:
        for sym, c in _CUR.items():
            if sym in (s or ""):
                return c
        return None

    def _to_lot(self, raw: dict, code: str, meta: Optional[dict] = None) -> Optional[Lot]:
        meta = meta or {}
        title = _first(raw, "publicName", "PublicName", "title", "name",
                       "lotTitle", "displayName", "headline")
        if not title:
            return None
        title = html.unescape(str(title)).strip()
        year, make, model, trim = normalize_title(title)

        # Estimates live in "value" (e.g. "£500,000 - £800,000 GBP"); the
        # "preSaleEstimate" key exists but is usually empty. Currency is the
        # symbol inside the string. "valueType" flags non-estimate values
        # (a realized/bid price on sold lots) — skip those as estimates.
        est = raw.get("estimate") if isinstance(raw.get("estimate"), dict) else {}
        vtype = (_first(raw, "valueType") or "")
        is_sold = raw.get("sold") is True or (isinstance(vtype, str) and
                  re.search(r"sold|bid|hammer|real[i]?[sz]ed|price", vtype, re.I))
        est_text = _first(raw, "value", "preSaleEstimate", "estimateText",
                          "estimateDisplay", "formattedEstimate", "estimate")
        if not isinstance(est_text, str):
            est_text = ""
        sold_price = None
        if is_sold:
            # Sold/withdrawn lot: the "value" string is the realized (or final
            # bid) figure, not an estimate. Capture it as the result.
            low = high = None
            sold_price, est_cur = _parse_money(est_text)
        else:
            low, high, est_cur = _parse_estimate_range(est_text)
            if low is None:
                low = (_first_num(raw, "lowEstimate", "LowEstimate", "estimateLow")
                       or _first_num(est, "low", "lowEstimate", "min"))
            if high is None:
                high = (_first_num(raw, "highEstimate", "HighEstimate", "estimateHigh")
                        or _first_num(est, "high", "highEstimate", "max"))

        currency = (est_cur or _parse_estimate_range(est_text)[2]
                    or _first(raw, "currency", "currencyCode", "estimateCurrency", "Currency")
                    or _first(est, "currency", "currencyCode") or "USD")
        if not isinstance(currency, str):
            currency = "USD"

        # "header" is the actual sale name ("THE LONDON AUCTION 2026");
        # "auctionStyleName" is just the generic "RM | SOTHEBY'S" brand label.
        auction_name = (_first(raw, "header", "auctionName", "saleName",
                               "auctionTitle", "eventName")
                        or meta.get("name") or f"RM Sotheby's {code.upper()}")
        # The lot itself has no date; use the auction-level date resolved per sale.
        sale_iso = (_to_iso(_first(raw, "auctionDate", "saleDate", "date", "startDate",
                                   "auctionStartDate", "dateTime", "endDate"))
                    or meta.get("date"))
        # Location ships as a flag-image path; decode the country code.
        location = (_first(raw, "location", "lotLocation", "saleLocation", "city", "geography")
                    or _country_from_flag(_first(raw, "locationFlag"))
                    or meta.get("location"))
        # "lot" is the printed lot number but is sometimes blank; fall back to
        # the reference id ("r0002") so a lot is never numberless.
        lot_no = _first(raw, "lot", "lotNumber", "LotNumber", "lotNo", "number", "referenceId")
        lot_no = str(lot_no).strip() if lot_no is not None else None
        lot_no = lot_no or None

        reserve = "reserve"
        wr = _first(raw, "withoutReserve", "noReserve", "isWithoutReserve")
        if wr is True or (isinstance(wr, str) and wr.strip().lower() in ("true", "yes", "1")):
            reserve = "no-reserve"

        lot_id = (_first(raw, "id", "Id", "lotId", "uuid", "guid")
                  or (f"{code.upper()}-{lot_no}" if lot_no else _slugify(title)))

        return Lot(
            source_name=self.config.name,
            external_lot_id=f"rm:{lot_id}",
            auction_type="live",
            source_url=self._extract_url(raw, code),
            auction_event_name=auction_name,
            auction_end_date=sale_iso,
            lot_number=lot_no,
            year=year, make=make, model=model, trim=trim,
            location=location,
            estimate_low=low, estimate_high=high,
            current_bid=sold_price,
            currency=currency.upper(),
            reserve_status=reserve,
            image_url=self._extract_image(raw),
            description_short=_first(raw, "collection", "alt", "subHeading",
                                    "subtitle", "shortDescription", "summary"),
            category=category_for(year, title),
            status=("sold" if is_sold else "upcoming"),
        )


class TheMarketAdapter(SourceAdapter):
    """The Market by Bonhams — online daily timed auctions (themarket.co.uk).

    A Nuxt (Vue) app: the listing data is NOT served as a standalone XHR — it's
    rendered into window.__NUXT__ on the server. But that same data is produced
    by a public Nuxt server route the app calls during render and on client nav:
        GET /api/listings/<stage>?page=<n>
    (stage = live | results | coming-soon | sealed | no-reserve). It returns
    clean JSON {data:[...lots], meta:{pagination}} with no auth, so we hit it
    directly instead of parsing __NUXT__ out of HTML.

    Online house: each lot carries an exact close time (`end_date` wall-clock +
    `timezone` IANA name) and a current high bid, so lots ingest as
    auction_type='online' (status 'upcoming' while live, like BaT). The
    /results stage feeds sold comps into sales_history through the normal run()
    path — the same way a live house reports realized prices at ingest.

    Money is in MINOR units (pence/cents): highest_bid 2800000 == £28,000, so we
    divide by 100. The detail-page slug is rebuilt from make/model with The
    Market's own rule (lowercase; keep [a-z0-9 -]; spaces->'-'; runs are NOT
    collapsed, so '... & ...' -> '--'); routing is on the trailing UUID.

    Terms: facts + link back only, same rule as every other source. Public
    server route, no token; still, confirm The Market's ToS.
    """
    config = SourceConfig(
        name="The Market by Bonhams",
        base_url="https://www.themarket.co.uk",
        auction_type="online",
        scrape_method="api",
        terms_notes="Public Nuxt server route (/api/listings/*); no token. Facts + link back; confirm ToS.",
    )

    SITE = "https://www.themarket.co.uk"
    CDN = "https://cdn.themarket.co.uk"          # bunny.url from the page config
    API = SITE + "/api/listings/{stage}"
    PAGE_SIZE = 50                               # server default; used only as a 'last page' hint
    MAX_PAGES = 15                               # hard stop for the live pager
    # Pages of the (recent-first) results feed to pull for comps each run. Recent
    # sales make the best comps and a couple pages covers far more than one
    # ingest interval of closings. Override with RADAR_TM_RESULT_PAGES.
    RESULT_PAGES = int(os.getenv("RADAR_TM_RESULT_PAGES", "2"))

    def __init__(self) -> None:
        self._live_by_id: Optional[dict] = None  # lazy cache for the hot-refresh parse()

    # The Market sits behind Cloudflare; the worker's contactable-bot User-Agent
    # gets a 403 on the public API route. These headers mirror the same-origin
    # fetch() the site's own page makes to /api/listings/* (browser UA + JSON
    # Accept + a Referer to its own site), which is what clears the WAF for this
    # public route. Site-specific and opt-in — every other source keeps the
    # worker's default identifying UA. Override the UA with RADAR_TM_UA (e.g.
    # paste your own browser's UA string) if the default is ever blocked.
    _HEADERS = {
        "User-Agent": os.getenv(
            "RADAR_TM_UA",
            "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36"),
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "en-GB,en;q=0.9",
        "Referer": "https://www.themarket.co.uk/auctions/live",
        "Sec-Fetch-Site": "same-origin",
        "Sec-Fetch-Mode": "cors",
        "Sec-Fetch-Dest": "empty",
    }

    # ---- slug (matches The Market's own client-side route builder) ---------
    @staticmethod
    def _tm_slug(s: str) -> str:
        s = (s or "").lower()
        s = re.sub(r"[^a-z0-9 -]", "", s)        # drop '/', '&', accents, …
        return s.replace(" ", "-")               # runs preserved ('... & ...' -> '--')

    def _detail_url(self, raw: dict) -> str:
        uuid = str(raw.get("id") or "").strip()
        mk = self._tm_slug(_first(raw, "make") or "") or "car"
        md = self._tm_slug(_first(raw, "model") or "") or "lot"
        return f"{self.SITE}/listings/{mk}/{md}/{uuid}"

    # ---- one page of a stage ----------------------------------------------
    def _page(self, fetcher: Fetcher, stage: str, page: int) -> tuple[list, dict]:
        url = self.API.format(stage=stage) + f"?page={page}"
        resp = fetcher.get(url, headers=self._HEADERS)
        if not resp:
            return [], {}
        try:
            body = resp.json()
        except ValueError:
            log.warning("TheMarket: non-JSON from %s", url)
            return [], {}
        if isinstance(body, dict):
            return (body.get("data") or []), (body.get("meta") or {})
        return (body or []), {}

    def _paginate(self, fetcher: Fetcher, stage: str, max_pages: int,
                  limit: Optional[int] = None) -> Iterator[dict]:
        seen = 0
        for page in range(1, max_pages + 1):
            data, meta = self._page(fetcher, stage, page)
            if not data:
                break
            for raw in data:
                if isinstance(raw, dict):
                    yield raw
                    seen += 1
                    if limit and seen >= limit:
                        return
            total_pages = to_float(meta.get("total_pages")) if isinstance(meta, dict) else None
            if total_pages and page >= int(total_pages):
                break
            if len(data) < self.PAGE_SIZE:       # short page -> last page
                break

    # ---- field mapping -----------------------------------------------------
    @staticmethod
    def _minor_to_major(v) -> Optional[float]:
        n = to_float(v)
        return round(n / 100.0, 2) if n is not None else None

    def _to_lot(self, raw: dict, sold: bool = False) -> Optional[Lot]:
        uuid = str(raw.get("id") or "").strip()
        make = _first(raw, "make")
        model = _first(raw, "model")
        if not uuid or not make:
            return None
        year = None
        ys = _first(raw, "year")
        if ys is not None:
            try:
                year = int(str(ys)[:4])
            except (TypeError, ValueError):
                year = None
        title = " ".join(str(x) for x in (year, make, model) if x)

        currency = _first(raw, "currency") or "GBP"
        currency = currency.upper() if isinstance(currency, str) else "GBP"

        # exact close time: naive wall-clock 'end_date' read in 'timezone'.
        end_iso = _to_iso_tz(_first(raw, "end_date"), _first(raw, "timezone"))

        wr = _first(raw, "reserve_status") or ""
        reserve = "no-reserve" if (isinstance(wr, str) and wr.lower() == "no-reserve") else "reserve"

        lot_no = _first(raw, "lot_number")
        lot_no = str(lot_no).strip() if lot_no is not None else None

        location = _first(raw, "location_country_name", "location") or None

        img = _first(raw, "image", "original_image")
        image_url = _abs_url(self.CDN, img) if (img and CAPTURE_IMAGE_URLS) else None

        common = dict(
            source_name=self.config.name,
            external_lot_id=f"tm:{uuid}",
            auction_type="online",
            source_url=self._detail_url(raw),
            auction_end_date=end_iso,
            lot_number=lot_no,
            year=year, make=make, model=model,
            location=location,
            currency=currency,
            reserve_status=reserve,
            image_url=image_url,
            description_short=_first(raw, "tagline"),
            category=category_for(year, title),
        )
        if sold:
            sold_price = self._minor_to_major(
                _first_num(raw, "final_price", "offline_sold_price", "highest_bid"))
            return Lot(auction_event_name="The Market", current_bid=sold_price,
                       status="sold", **common)
        return Lot(auction_event_name="Online",
                   current_bid=self._minor_to_major(_first_num(raw, "highest_bid")),
                   status="upcoming", **common)

    # ---- collect: live board (+ recent results for comps) ------------------
    def collect(self, fetcher: Fetcher, limit: Optional[int] = None) -> list[Lot]:
        lots: list[Lot] = []
        dumped = False
        # 1) live board: status 1 == actively biddable; skip buy-now/ended (5).
        for raw in self._paginate(fetcher, "live", self.MAX_PAGES, limit):
            if not dumped:
                log.info("TheMarket: first live lot raw keys: %s", sorted(raw.keys()))
                if os.getenv("RADAR_DUMP_RAW"):
                    print(json.dumps(raw, indent=2, default=str))
                dumped = True
            if raw.get("status") not in (1, "1") or raw.get("visible", True) is False:
                continue
            lot = self._to_lot(raw, sold=False)
            if lot:
                lots.append(lot)
                if limit and len(lots) >= limit:
                    return lots
        # 2) recent results -> sold comps. run() routes status='sold' into
        #    sales_history. Best-effort: never let it break the live ingest.
        try:
            n = 0
            for raw in self._paginate(fetcher, "results", self.RESULT_PAGES):
                lot = self._to_lot(raw, sold=True)
                if lot and lot.current_bid:           # only real sales become comps
                    lots.append(lot)
                    n += 1
            if n:
                log.info("TheMarket: %d recent result(s) captured for comps", n)
        except Exception as e:
            log.warning("TheMarket: results pull skipped (%s)", e)
        return lots

    # ---- hot-refresh hook: resolve a lot from the (cached) live feed --------
    def parse(self, url: str, fetcher: Fetcher) -> Optional[Lot]:
        """refresh_hot calls this per closing-soon lot. Rather than fetch the
        Nuxt detail page (data lives in __NUXT__, not a simple parse), pull the
        live feed ONCE per refresh cycle and index it by id; each hot lot is then
        a dict lookup. The adapter instance is recreated per refresh_hot run, so
        the cache is always current within a run and never stale across runs."""
        if self._live_by_id is None:
            cache: dict = {}
            for raw in self._paginate(fetcher, "live", self.MAX_PAGES):
                if raw.get("status") in (1, "1") and raw.get("visible", True) is not False:
                    lot = self._to_lot(raw, sold=False)
                    if lot:
                        cache[lot.external_lot_id] = lot
            self._live_by_id = cache
        uuid = url.rstrip("/").rsplit("/", 1)[-1]
        return self._live_by_id.get(f"tm:{uuid}")

    # ---- harvest hook: closed online lot -> outcome ------------------------
    def parse_result(self, url: str, text: str) -> dict:
        """harvest_results calls this for a closed online lot, passing the
        detail-page HTML. The Market's authoritative outcome comes from the
        /results feed pulled during collect() (which marks sold lots 'sold'
        before harvest runs), so this is a light best-effort over the rendered
        page; otherwise it reports no sale and the lot is finalized 'withdrawn'
        until the next results ingest corrects it if it did in fact sell."""
        head = text[:60000]
        m = re.search(r"sold\s+for[^0-9£€$]*([£€$])?\s*([\d][\d,]*)", head, re.I)
        if m:
            price = to_float(m.group(2))
            cur = {"£": "GBP", "€": "EUR", "$": "USD"}.get(m.group(1) or "", "GBP")
            if price:
                return {"sold": True, "sold_price": price, "currency": cur, "sold_date": None}
        return {"sold": False}


# ---------------------------------------------------------------------------
# Bonhams Cars (cars.bonhams.com) — server-rendered Next.js live auction house
# ---------------------------------------------------------------------------
# The /cars/ department page ships a __NEXT_DATA__ JSON blob with the full,
# UNGATED feed (unlike The Market's cookie-gated /api/listings):
#   props.pageProps.lots.hits          -> upcoming/preview lots (estimates + sale date)
#   props.pageProps.department.exceptionalResults -> past record sales we keep as comps
# One GET per page, no API key, no cf_clearance gate. Currency note: the site
# *displays* prices in the visitor's currency, but every lot's underlying
# currency.iso_code + price.estimateLow/High are NATIVE (GBP/EUR/USD per lot),
# so comps never get muddled — the USD pixel payload was only the display layer.
NEXT_DATA_RE = re.compile(
    r'<script[^>]+id=["\']__NEXT_DATA__["\'][^>]*>(.*?)</script>', re.S | re.I)
_TAG_RE = re.compile(r"<[^>]+>")
_BR_RE = re.compile(r"<\s*br\s*/?\s*>", re.I)
_YEAR_RE = re.compile(r"\b(1[89]\d{2}|20\d{2})\b")
# space-separated marques (hyphenated ones like Mercedes-Benz are single tokens)
_TWO_WORD_MARQUES = {
    "aston martin", "alfa romeo", "rolls royce", "land rover", "de tomaso",
    "iso rivolta", "facel vega", "la salle", "general motors",
}
# tokens that terminate the model string in a Bonhams lot title
_MODEL_STOP_RE = re.compile(
    r"\s*(?:chassis\s*no\.?|chassis\s*number|engine\s*no\.?|body\s*no\.?|vin\.?)\b", re.I)
_COMP_CUR = {"US$": "USD", "$": "USD", "£": "GBP", "€": "EUR", "CHF": "CHF",
             "AU$": "AUD", "CA$": "CAD"}
_BONHAMS_SENTINEL_TS = 4_000_000_000   # biddableFrom 'year 2100' = no scheduled sale


def _strip_tags(s: str) -> str:
    return html.unescape(_TAG_RE.sub(" ", s or "")).replace("\xa0", " ")


def _parse_ymm(name: str) -> tuple[Optional[int], Optional[str], Optional[str]]:
    """(year, make, model) from a Bonhams lot name. Names may be multi-line
    (provenance prefix + '<BR>' + the YEAR MAKE MODEL line + '<BR>' coachwork/
    chassis lines). Split on <BR>, strip tags, and parse from the first segment
    bearing a leading 4-digit year; the upcoming-lots `title` field is a single
    clean line so it parses directly."""
    parts = [re.sub(r"\s{2,}", " ", _strip_tags(p).strip())
             for p in _BR_RE.split(name or "")]
    parts = [p for p in parts if p]
    line = next((p for p in parts if _YEAR_RE.search(p)), " ".join(parts))
    m = _YEAR_RE.search(line)
    if not m:
        return None, None, None
    year = int(m.group(1))
    after = line[m.end():].strip(" ,")
    stop = _MODEL_STOP_RE.search(after)
    body = (after[:stop.start()] if stop else after).strip(" ,")
    words = body.split()
    if not words:
        return year, None, None
    if len(words) >= 2 and " ".join(words[:2]).lower() in _TWO_WORD_MARQUES:
        make, model = " ".join(words[:2]), " ".join(words[2:])
    else:
        make, model = words[0], " ".join(words[1:])
    return year, (make or None), (model.strip(" ,") or None)


def _parse_chassis(name: str) -> Optional[str]:
    txt = _strip_tags(name or "")
    m = (re.search(r"chassis\s*no\.?\s*([A-Za-z0-9][\w ./\-]{1,40})", txt, re.I)
         or re.search(r"\bVIN\.?\s*([A-Za-z0-9][\w ./\-]{1,40})", txt, re.I))
    if not m:
        return None
    val = re.split(r"\s+(?:engine|body)\s*no\.?", m.group(1).strip(), flags=re.I)[0]
    return val.strip() or None


def _bonhams_img(img: dict) -> Optional[str]:
    """Hotlinkable CDN image URL from {url, URLParams}; url already carries
    '?src=…', so append the crop params + a sane width."""
    if not isinstance(img, dict) or not img.get("url"):
        return None
    url = img["url"]
    params = (img.get("URLParams") or "").strip()
    out = url + (("&" + params) if params else "")
    return out + ("&width=640" if "width=" not in out else "")


def _bonhams_date_from_img(url: str) -> Optional[str]:
    """Approximate sale date for an exceptionalResults comp from its image path
    '…/Images/live/YYYY-MM/DD/…' (uploaded around sale time). Used only as the
    comp's sold_date — the highlights payload ships no date field."""
    m = re.search(r"/live/(\d{4})-(\d{2})/(\d{2})/", url or "")
    return f"{m.group(1)}-{m.group(2)}-{m.group(3)}T00:00:00+00:00" if m else None


class BonhamsCarsAdapter(SourceAdapter):
    SITE = "https://cars.bonhams.com"
    GRID = "/cars/"
    MAX_PAGES = int(os.getenv("RADAR_BONHAMS_MAX_PAGES", "10"))
    config = SourceConfig(
        name="Bonhams Cars",
        base_url=SITE,
        auction_type="live",
        scrape_method="ssr-next",
        terms_notes="cars.bonhams.com /cars/ __NEXT_DATA__ (Next.js getServerSideProps); "
                    "public, server-rendered, no auth.",
    )

    def __init__(self):
        self._upcoming_by_id: Optional[dict] = None     # hot-refresh cache

    # ---- fetch + extract the embedded Next.js page data --------------------
    def _next_data(self, fetcher: Fetcher, page: int) -> Optional[dict]:
        url = self.SITE + self.GRID + (f"?page={page}" if page > 1 else "")
        resp = fetcher.get(url)
        if not resp:
            return None
        m = NEXT_DATA_RE.search(resp.text)
        if not m:
            log.warning("Bonhams: no __NEXT_DATA__ on %s", url)
            return None
        try:
            return json.loads(m.group(1))
        except Exception as e:
            log.warning("Bonhams: __NEXT_DATA__ JSON parse failed (%s)", e)
            return None

    @staticmethod
    def _lots_block(data: Optional[dict]) -> dict:
        return (((data or {}).get("props") or {}).get("pageProps") or {}).get("lots") or {}

    # ---- upcoming / preview lot -> Lot ------------------------------------
    def _to_lot(self, hit: dict) -> Optional[Lot]:
        ext = _first(hit, "id", "lotUniqueId")
        if not ext:
            return None
        title = hit.get("title") or hit.get("styledDescription") or ""
        year, make, model = _parse_ymm(title)
        price = hit.get("price") or {}
        lo = to_float(price.get("estimateLow")) or None
        hi = to_float(price.get("estimateHigh")) or None
        # scheduled sale window: trust the Unix timestamps (unambiguous UTC) — the
        # feed's paired 'datetime' strings mislabel local time as +00:00. A year-
        # 2100 sentinel = private sale / no scheduled date, so drop those dates.
        start_ts = ((hit.get("biddableFrom") or {}).get("timestamp")
                    or (hit.get("hammerTime") or {}).get("timestamp"))
        end_ts = (hit.get("auctionEndDate") or {}).get("timestamp")
        sentinel = bool(start_ts and start_ts >= _BONHAMS_SENTINEL_TS)
        cur = (((hit.get("currency") or {}).get("iso_code")) or "USD").upper()
        flags = hit.get("flags") or {}
        auction_id = str(hit.get("auctionId") or "").strip()
        slug = hit.get("slug") or _slugify(title)
        lotno = ((hit.get("lotNo") or {}).get("full") or "").strip()
        return Lot(
            source_name=self.config.name,
            external_lot_id=f"bonhams:{ext}",
            auction_type="live",
            source_url=(f"{self.SITE}/auction/{auction_id}/preview-lot/{ext}/{slug}/"
                        if auction_id else None),
            auction_event_name=("Private Sales" if hit.get("auctionType") == "PRIAUC"
                                else None),
            auction_start_date=(None if sentinel else _to_iso(start_ts)),
            auction_end_date=(None if (sentinel or not end_ts) else _to_iso(end_ts)),
            lot_number=(lotno if lotno and lotno != "0" else None),
            year=year, make=make, model=model,
            chassis=_parse_chassis(title),
            location=((hit.get("country") or {}).get("name")),
            estimate_low=(lo if (lo and lo > 0) else None),
            estimate_high=(hi if (hi and hi > 0) else None),
            current_bid=None,
            currency=_CUR.get(cur, cur),
            reserve_status=("no-reserve" if flags.get("isWithoutReserve") else "reserve"),
            image_url=_bonhams_img(hit.get("image") or {}),
            description_short=(_strip_tags(hit.get("styledDescription") or "").strip()
                               or (hit.get("image") or {}).get("caption") or None),
            category=category_for(year, title),
            status="upcoming",
        )

    # ---- exceptionalResults -> sold comp Lot ------------------------------
    def _to_comp(self, ex: dict) -> Optional[Lot]:
        price = to_float(ex.get("hammerPremium")) or to_float(ex.get("hammerPrice"))
        if not price or price <= 0:                 # highlight reel includes 0s
            return None
        uniq = _first(ex, "saleLotNoUnique", "saleNo")
        name = ex.get("lotName") or ""
        year, make, model = _parse_ymm(name)
        if not (uniq and year and make):
            return None
        sale_no, lot_no = str(ex.get("saleNo") or "").strip(), str(ex.get("lotNo") or "").strip()
        return Lot(
            source_name=self.config.name,
            external_lot_id=f"bonhams:{uniq}",
            auction_type="live",
            source_url=(f"{self.SITE}/auction/{sale_no}/lot/{lot_no}/"
                        if sale_no and lot_no else None),
            year=year, make=make, model=model,
            chassis=_parse_chassis(name),
            current_bid=price,
            currency=_COMP_CUR.get((ex.get("currencySymbol") or "").strip(), "USD"),
            image_url=_bonhams_img({"url": ex.get("imageURL"),
                                    "URLParams": ex.get("imageURLParams")}),
            description_short=(_strip_tags(name).strip()[:300] or None),
            category=category_for(year, name),
            auction_end_date=_bonhams_date_from_img(ex.get("imageURL") or ""),
            status="sold",
        )

    # ---- collect: upcoming lots (+ record-sale comps) ---------------------
    def collect(self, fetcher: Fetcher, limit: Optional[int] = None) -> list[Lot]:
        lots: list[Lot] = []
        data = self._next_data(fetcher, 1)
        if not data:
            return lots
        block = self._lots_block(data)
        hits = block.get("hits") or []
        log.info("Bonhams: page 1 — %d upcoming lot(s) (found=%s)",
                 len(hits), block.get("found"))
        if hits and os.getenv("RADAR_DUMP_RAW"):
            print(json.dumps(hits[0], indent=2, default=str))

        def _take(hs) -> bool:
            for h in hs:
                lot = self._to_lot(h)
                if lot:
                    lots.append(lot)
                    if limit and len(lots) >= limit:
                        return True
            return False

        if not _take(hits):
            pages = int(to_float(block.get("nbPages")) or 1)
            page = 2
            while page <= min(pages, self.MAX_PAGES):
                hs = self._lots_block(self._next_data(fetcher, page)).get("hits") or []
                if not hs:
                    break
                log.info("Bonhams: page %d — %d lot(s)", page, len(hs))
                if _take(hs):
                    break
                page += 1

        # record-sale comps from the same page-1 payload. run() routes any
        # status='sold' lot into sales_history (the same path The Market uses).
        try:
            dept = (((data.get("props") or {}).get("pageProps") or {}).get("department") or {})
            n = 0
            for ex in (dept.get("exceptionalResults") or []):
                comp = self._to_comp(ex)
                if comp:
                    lots.append(comp)
                    n += 1
            if n:
                log.info("Bonhams: %d record-sale comp(s) captured", n)
        except Exception as e:
            log.warning("Bonhams: comps pull skipped (%s)", e)
        return lots

    # ---- hot-refresh hook (effectively unused: live lots never go 'hot') ---
    def parse(self, url: str, fetcher: Fetcher) -> Optional[Lot]:
        """refresh_hot only targets online lots closing soon; Bonhams lots are
        'live', so this is unused in practice. Kept correct: index the upcoming
        feed once per call and resolve by the id embedded in the lot URL."""
        if self._upcoming_by_id is None:
            cache: dict = {}
            for h in (self._lots_block(self._next_data(fetcher, 1)).get("hits") or []):
                lot = self._to_lot(h)
                if lot:
                    cache[lot.external_lot_id] = lot
            self._upcoming_by_id = cache
        m = re.search(r"/(?:preview-lot|lot)/(\d+)/", url)
        return self._upcoming_by_id.get(f"bonhams:{m.group(1)}") if m else None

    # ---- harvest hook (unused: live lots aren't post-close harvested) ------
    def parse_result(self, url: str, text: str) -> dict:
        m = re.search(r"sold\s+for[^0-9£€$]*([£€$])?\s*([\d][\d,]*)", text[:60000], re.I)
        if m and to_float(m.group(2)):
            return {"sold": True, "sold_price": to_float(m.group(2)),
                    "currency": {"£": "GBP", "€": "EUR", "$": "USD"}.get(m.group(1) or "", "GBP"),
                    "sold_date": None}
        return {"sold": False}


# register adapters here as you add them (Collecting Cars, PCARMARKET, …)
ADAPTERS: dict[str, type[SourceAdapter]] = {
    "bringatrailer": BringATrailerAdapter,
    "carsandbids": CarsAndBidsAdapter,
    "rmsothebys": RMSothebysAdapter,
    "bonhamscars": BonhamsCarsAdapter,
    # "themarket": TheMarketAdapter,   # PARKED: /api/listings is app-gated (403 w/o
    #   a browser cf_clearance cookie) — unreachable from an unattended worker.
    #   Adapter + self-tests retained above; re-enable if Bonhams ungates the route.
}
# resolve a stored source_name (e.g. "Bring a Trailer") back to its adapter
ADAPTERS_BY_NAME = {cls.config.name: cls for cls in ADAPTERS.values()}


# ---------------------------------------------------------------------------
# alerts: match saved searches -> email digests
# ---------------------------------------------------------------------------
RESEND_API_KEY = os.environ.get("RESEND_API_KEY", "")
ALERT_FROM = os.environ.get("ALERT_FROM", "Auction Radar <onboarding@resend.dev>")

_SYM = {"USD": "$", "GBP": "£", "EUR": "€"}


def fmt_money(v, cur) -> str:
    if v is None:
        return "—"
    try:
        return _SYM.get(cur, "") + f"{int(float(v)):,}"
    except (TypeError, ValueError):
        return "—"


def closes_phrase(iso: Optional[str]) -> str:
    if not iso:
        return ""
    try:
        end = dt.datetime.fromisoformat(str(iso).replace("Z", "+00:00"))
    except ValueError:
        return ""
    secs = (end - dt.datetime.now(dt.timezone.utc)).total_seconds()
    if secs <= 0:
        return "closing now"
    d, rem = divmod(int(secs), 86400)
    h, rem = divmod(rem, 3600)
    return f"closes in {d}d {h}h" if d else f"closes in {h}h {rem // 60}m"


def price_line(m: dict) -> str:
    if m.get("auction_type") == "online" and m.get("current_bid") is not None:
        return "Current bid " + fmt_money(m["current_bid"], m.get("currency", "USD"))
    if m.get("estimate_low") and m.get("estimate_high"):
        return ("Estimate " + fmt_money(m["estimate_low"], m.get("currency", "USD"))
                + "–" + fmt_money(m["estimate_high"], m.get("currency", "USD")))
    return ""


class EmailSender:
    def send(self, to: str, subject: str, html_body: str, text_body: str) -> bool:
        raise NotImplementedError


class ConsoleSender(EmailSender):
    def send(self, to, subject, html_body, text_body):
        log.info("EMAIL (console) -> %s | %s", to, subject)
        print(f"\n----- EMAIL (dry) -----\nTo: {to}\nSubject: {subject}\n\n{text_body}\n-----------------------\n")
        return True


class ResendSender(EmailSender):
    def __init__(self, api_key: str, sender: str):
        self.key, self.sender = api_key, sender

    def send(self, to, subject, html_body, text_body):
        try:
            r = requests.post(
                "https://api.resend.com/emails",
                headers={"Authorization": f"Bearer {self.key}", "Content-Type": "application/json"},
                json={"from": self.sender, "to": [to], "subject": subject,
                      "html": html_body, "text": text_body},
                timeout=REQUEST_TIMEOUT)
            if r.status_code >= 300:
                log.error("Resend %s: %s", r.status_code, r.text[:300])
                return False
            return True
        except requests.RequestException as e:
            log.error("Resend send failed: %s", e)
            return False


def build_sender(dry_run: bool) -> EmailSender:
    if dry_run or not RESEND_API_KEY:
        if not dry_run:
            log.info("No RESEND_API_KEY set — printing emails instead of sending.")
        return ConsoleSender()
    return ResendSender(RESEND_API_KEY, ALERT_FROM)


def render_email(email: str, matches: list) -> tuple:
    n = len(matches)
    nq = len({m["query_id"] for m in matches})
    subject = f"{n} car{'' if n == 1 else 's'} match your Auction Radar alert{'' if nq == 1 else 's'}"
    groups: dict = {}
    for m in matches:
        groups.setdefault(m.get("label") or "Saved search", []).append(m)

    text = [f"You have {n} new match{'' if n == 1 else 'es'} on Auction Radar.\n"]
    htmlp = ['<div style="font-family:Georgia,serif;max-width:560px;margin:0 auto;color:#211e18">',
             f'<h2 style="font-weight:500;letter-spacing:.01em">Auction Radar — {n} match{"" if n == 1 else "es"}</h2>']
    for label, items in groups.items():
        text.append(f"\n— {label} —")
        htmlp.append(f'<h3 style="margin:22px 0 6px;padding-bottom:6px;border-bottom:1px solid #dcd6ca;'
                     f'color:#7e2230;font-size:13px;letter-spacing:.08em;text-transform:uppercase">{html.escape(label)}</h3>')
        for m in items:
            title = f"{m.get('year') or ''} {m.get('make') or ''} {m.get('model') or ''}".strip()
            meta = " · ".join(x for x in (m.get("source_name") or "", price_line(m),
                                          closes_phrase(m.get("closes_at"))) if x)
            tag = "New listing" if m.get("reason") == "new" else "Closing soon"
            url = m.get("source_url") or "#"
            text.append(f"  • {title} — {meta} [{tag}]")
            text.append(f"    {url}")
            htmlp.append(
                f'<p style="margin:12px 0"><a href="{html.escape(url)}" '
                f'style="color:#211e18;text-decoration:none;font-weight:600;font-size:17px">{html.escape(title)}</a><br>'
                f'<span style="color:#8a8478;font-size:13px">{html.escape(meta)} '
                f'&middot; <b style="color:#7e2230">{tag}</b></span></p>')
    htmlp.append('<p style="margin-top:22px;border-top:1px solid #dcd6ca;padding-top:10px;color:#aba493;font-size:11px">'
                 'You\'re receiving this because you saved a search on Auction Radar. '
                 'Links go to the auction house listing.</p></div>')
    return subject, "\n".join(htmlp), "\n".join(text)


def run_alerts(soon_hours: int, new_within: int, dry_run: bool, bootstrap: bool) -> None:
    if not (SUPABASE_URL and SUPABASE_SERVICE_KEY):
        log.error("Alerts require SUPABASE_URL + SUPABASE_SERVICE_KEY (service role).")
        return
    sb = Supabase(SUPABASE_URL, SUPABASE_SERVICE_KEY)
    rows = sb.rpc("alerts_pending", {"soon_hours": soon_hours, "new_within_hours": new_within})
    log.info("%d pending alert row(s)", len(rows))
    if not rows:
        return
    if bootstrap:
        n = sb.record_alerts([(r["query_id"], r["lot_id"], r["reason"]) for r in rows])
        log.info("Bootstrap: recorded %d existing match(es) as already-sent (no email).", n)
        return

    sender = build_sender(dry_run)
    by_email: dict = {}
    for r in rows:
        by_email.setdefault(r["email"], []).append(r)

    sent, recorded = 0, []
    for email, matches in by_email.items():
        subject, html_body, text_body = render_email(email, matches)
        if sender.send(email, subject, html_body, text_body):
            sent += 1
            if not dry_run:
                recorded += [(m["query_id"], m["lot_id"], m["reason"]) for m in matches]
    if recorded:
        sb.record_alerts(recorded)
    log.info("Sent %d digest email(s); recorded %d alert(s).%s",
             sent, len(recorded), "  (dry-run: nothing recorded)" if dry_run else "")


# ---------------------------------------------------------------------------
# runner
# ---------------------------------------------------------------------------
def sold_sales_rows(lots: list[Lot]) -> list[dict]:
    """sales_history comp records derived from lots that came back already sold
    at ingest. Live houses (RM) report the realized price in the same feed, so
    the result is captured directly; current_bid holds the hammer figure and
    auction_end_date the sale date. on_conflict(source,external_id) makes the
    insert idempotent across repeated ingests."""
    out = []
    for l in lots:
        if l.is_valid() and l.status == "sold" and l.current_bid:
            out.append({
                "source": l.source_name, "source_url": l.source_url,
                "external_id": l.external_lot_id,
                "year": l.year, "make": l.make, "model": l.model, "trim": l.trim,
                "mileage": l.mileage,
                "sold_price": l.current_bid, "currency": l.currency,
                "sold_date": (l.auction_end_date or "")[:10] or None,
            })
    return out


def run(source_key: str, dry_run: bool, limit: Optional[int], no_robots: bool) -> None:
    adapter = ADAPTERS[source_key]()
    fetcher = Fetcher(respect_robots=not no_robots)
    log.info("Collecting from %s …", adapter.config.name)

    lots = adapter.collect(fetcher, limit=limit)
    rows = [l.to_row() for l in lots if l.is_valid()]
    log.info("Parsed %d lot(s); %d valid after validation", len(lots), len(rows))

    have_creds = bool(SUPABASE_URL and SUPABASE_SERVICE_KEY)
    if dry_run or not have_creds:
        if not have_creds:
            log.info("No Supabase creds set — dry run only.")
        print(json.dumps(rows[: (limit or 10)], indent=2, default=str))
        return

    sb = Supabase(SUPABASE_URL, SUPABASE_SERVICE_KEY)
    sb.ensure_source(adapter.config)
    n = sb.upsert_lots(rows)
    log.info("Upserted %d row(s) into auction_lots", n)

    # Live houses (e.g. RM) report realized prices in the same catalog feed, so
    # any lot that came back already sold becomes a comp at ingest time. Online
    # houses (BaT) are handled post-close by --harvest-results instead.
    sales = sold_sales_rows(lots)
    if sales:
        sb.insert_sales(sales)
        log.info("Recorded %d sold lot(s) into sales_history (ingest comps)", len(sales))

    sb.reconcile_stale(adapter.config.name, STALE_DAYS)
    log.info("Reconciled stale lots ( > %.1f days unseen -> withdrawn )", STALE_DAYS)


def refresh_hot(hot_hours: int, dry_run: bool, limit: Optional[int]) -> None:
    """Re-pull only the lots closing soon (where bids actually move). Targets
    known source_urls, so it's cheap to run on a tight cadence."""
    if not (SUPABASE_URL and SUPABASE_SERVICE_KEY):
        log.error("Hot refresh requires SUPABASE_URL + SUPABASE_SERVICE_KEY.")
        return
    sb = Supabase(SUPABASE_URL, SUPABASE_SERVICE_KEY)
    hot = sb.hot_lots(hot_hours, limit or 200)
    log.info("%d hot lot(s) closing within %dh", len(hot), hot_hours)
    if not hot:
        return
    fetcher = Fetcher()
    cache: dict = {}
    updated = []
    for h in hot:
        url = h.get("source_url")
        cls = ADAPTERS_BY_NAME.get(h.get("source_name"))
        if not url or not cls:
            continue
        adapter = cache.setdefault(cls, cls())
        try:
            lot = adapter.parse(url, fetcher)
            if lot and lot.is_valid():
                updated.append(lot.to_row())
        except Exception as e:
            log.warning("hot re-parse failed %s: %s", url, e)
    log.info("Re-parsed %d hot lot(s)", len(updated))
    if dry_run:
        print(json.dumps(updated[:10], indent=2, default=str))
        return
    if updated:
        sb.upsert_lots(updated)
        log.info("Upserted %d refreshed lot(s)", len(updated))


def run_loop(source_key: str, hot_hours: int, full_every_min: int,
             hot_every_sec: int, alert_every_min: int, no_robots: bool) -> None:
    """Always-on scheduler: interleaves full ingest, hot refresh, and alerts.
    Use this on an always-on host when you want sub-5-minute hot cadence."""
    log.info("Loop start — full=%dm, hot=%ds, alerts=%dm. Ctrl-C to stop.",
             full_every_min, hot_every_sec, alert_every_min)
    next_full = next_hot = next_alert = 0.0
    while True:
        now = time.time()
        if now >= next_full:
            try: run(source_key, False, None, no_robots)
            except Exception as e: log.error("full ingest error: %s", e)
            try: harvest_results(False, None)
            except Exception as e: log.error("harvest error: %s", e)
            next_full = now + full_every_min * 60
        if now >= next_hot:
            try: refresh_hot(hot_hours, False, None)
            except Exception as e: log.error("hot refresh error: %s", e)
            next_hot = now + hot_every_sec
        if now >= next_alert:
            try: run_alerts(24, 48, False, False)
            except Exception as e: log.error("alerts error: %s", e)
            next_alert = now + alert_every_min * 60
        time.sleep(5)


def harvest_results(dry_run: bool, limit: Optional[int]) -> None:
    """Re-fetch lots whose auction has ended, read the final result, and record
    sold prices into sales_history (our comps data) + finalize lot status."""
    if not (SUPABASE_URL and SUPABASE_SERVICE_KEY):
        log.error("Harvest requires SUPABASE_URL + SUPABASE_SERVICE_KEY.")
        return
    sb = Supabase(SUPABASE_URL, SUPABASE_SERVICE_KEY)
    closed = sb.closed_lots(limit or 200)
    log.info("%d closed lot(s) to finalize", len(closed))
    if not closed:
        return
    fetcher = Fetcher()
    cache: dict = {}
    sales, finals = [], []
    for c in closed:
        url = c.get("source_url")
        cls = ADAPTERS_BY_NAME.get(c.get("source_name"))
        if not url or not cls:
            continue
        adapter = cache.setdefault(cls, cls())
        resp = fetcher.get(url)
        if not resp:
            continue                       # couldn't fetch; leave for stale reconcile
        res = adapter.parse_result(url, resp.text)
        if res and res.get("sold") and res.get("sold_price"):
            sales.append({
                "source": c.get("source_name"), "source_url": url,
                "external_id": c.get("external_lot_id") or url,
                "year": c.get("year"), "make": c.get("make"), "model": c.get("model"),
                "trim": c.get("trim"), "mileage": c.get("mileage"),
                "sold_price": res["sold_price"], "currency": res.get("currency", "USD"),
                "sold_date": res.get("sold_date"),
            })
            finals.append((c["id"], "sold", res["sold_price"]))
        else:
            # Reserve not met / no sale: still correct current_bid to the final
            # high bid when the page reports one, but don't record it as a comp.
            finals.append((c["id"], "withdrawn", (res or {}).get("final_bid")))
    log.info("Found %d sold result(s) across %d closed lot(s)", len(sales), len(closed))
    if dry_run:
        print(json.dumps(sales[:10], indent=2, default=str))
        return
    if sales:
        sb.insert_sales(sales)
        log.info("Recorded %d sale(s) to sales_history", len(sales))
    for (lid, st, fp) in finals:
        try: sb.finalize_lot(lid, st, fp)
        except Exception as e: log.warning("finalize %s failed: %s", lid, e)
    log.info("Finalized %d lot(s)", len(finals))


# ---------------------------------------------------------------------------
# offline self-test (no network) — proves the extraction + normalization
# ---------------------------------------------------------------------------
def selftest() -> None:
    print("· title normalizer")
    cases = [
        ("No Reserve: 1999 Ferrari 360 Modena 6-Speed", (1999, "Ferrari", "360 Modena 6-Speed", "no-reserve")),
        ("1992 Porsche 911 Carrera RS Lightweight",      (1992, "Porsche", "911 Carrera RS Lightweight", None)),
        ("1990 Mercedes-Benz 190E 2.5-16 Evolution II",  (1990, "Mercedes-Benz", "190E 2.5-16 Evolution II", None)),
        ("2000 Nissan Skyline GT-R R34 V-Spec II",       (2000, "Nissan", "Skyline GT-R R34 V-Spec II", None)),
    ]
    for title, exp in cases:
        got = normalize_title(title)
        assert got == exp, f"\n  title: {title}\n  got:   {got}\n  want:  {exp}"
        print(f"    ok  {title!r} -> {got}")

    print("· category heuristic")
    assert category_for(2023, "2023 Porsche 911 GT3 RS") == "Race"
    assert category_for(1991, "1991 Ferrari F40") == "Supercar"
    assert category_for(1963, "1963 Jaguar E-Type") == "Classic"
    assert category_for(1999, "1999 Ferrari 360 Modena") == "Modern"
    print("    ok")

    print("· JSON-LD listing extraction (synthetic fixture)")
    fixture = """<!doctype html><html><head>
      <meta property="og:title" content="1999 Ferrari 360 Modena 6-Speed">
      <meta property="og:image" content="https://img.example/360.jpg">
      <script type="application/ld+json">
      {"@context":"https://schema.org","@type":"Product",
       "name":"No Reserve: 1999 Ferrari 360 Modena 6-Speed",
       "image":["https://img.example/360-1.jpg"],
       "description":"Gated-manual 360 Modena finished in Rosso Corsa.",
       "vehicleTransmission":"6-speed manual",
       "mileageFromOdometer":{"@type":"QuantitativeValue","value":34000,"unitCode":"SMI"},
       "offers":{"@type":"Offer","price":"92000","priceCurrency":"USD",
                 "priceValidUntil":"2026-07-01T18:00:00Z","availability":"https://schema.org/InStock"}}
      </script></head><body>… No Reserve …</body></html>"""
    url = "https://bringatrailer.com/listing/1999-ferrari-360-modena-12/"
    lot = BringATrailerAdapter().parse_html(url, fixture)
    assert lot is not None, "parser returned None"
    assert lot.is_valid(), f"invalid lot: {lot}"
    row = lot.to_row()
    for k in ("year", "make", "model", "reserve_status", "current_bid", "currency",
              "auction_type", "external_lot_id", "category", "transmission", "mileage"):
        print(f"    {k:16} = {row.get(k)}")
    assert row["year"] == 1999 and row["make"] == "Ferrari"
    assert row["reserve_status"] == "no-reserve"
    assert row["current_bid"] == 92000.0 and row["currency"] == "USD"
    assert row["auction_type"] == "online"
    assert row["external_lot_id"] == "bat:1999-ferrari-360-modena-12"
    assert row["category"] == "Modern"
    assert row["transmission"] == "6-speed manual"
    assert row["mileage"] == "34,000 mi"
    assert row["image_url"] == "https://img.example/360-1.jpg"  # captured by default
    assert row["auction_end_date"].startswith("2026-07-01")
    print("· upsert payload shape (what POSTs to /rest/v1/auction_lots):")
    print("   ", json.dumps({k: row[k] for k in sorted(row)}, default=str)[:300], "…")
    print("· alert email rendering")
    sample = [
        {"query_id": 1, "label": "No-reserve Porsche \u2264 $300k", "email": "x@y.com",
         "lot_id": 11, "reason": "new", "year": 1992, "make": "Porsche", "model": "964 Carrera RS",
         "source_name": "Bring a Trailer", "source_url": "https://bringatrailer.com/listing/964/",
         "auction_type": "online", "current_bid": 285000, "estimate_low": None, "estimate_high": None,
         "currency": "USD", "reserve_status": "no-reserve", "location": "Online — USA",
         "closes_at": (dt.datetime.now(dt.timezone.utc) + dt.timedelta(hours=5)).isoformat()},
        {"query_id": 2, "label": "Le Mans cars", "email": "x@y.com",
         "lot_id": 22, "reason": "closing_soon", "year": 1970, "make": "Porsche", "model": "917K",
         "source_name": "Gooding Christie's", "source_url": "https://www.goodingco.com",
         "auction_type": "live", "current_bid": None, "estimate_low": 14000000, "estimate_high": 18000000,
         "currency": "USD", "reserve_status": "reserve", "location": "Pebble Beach, CA",
         "closes_at": (dt.datetime.now(dt.timezone.utc) + dt.timedelta(hours=20)).isoformat()},
    ]
    subj, html_body, text_body = render_email("x@y.com", sample)
    print("    subject:", subj)
    assert "2 cars" in subj
    assert "964 Carrera RS" in text_body and "917K" in text_body
    assert "Current bid $285,000" in text_body
    assert "Estimate $14,000,000\u2013$18,000,000" in text_body
    assert "bringatrailer.com/listing/964" in html_body
    assert fmt_money(92000, "GBP") == "\u00a392,000"
    assert closes_phrase((dt.datetime.now(dt.timezone.utc) + dt.timedelta(hours=5)).isoformat()).startswith("closes in")
    print("    ok")

    print("· adapter lookup by source name")
    assert ADAPTERS_BY_NAME.get("Bring a Trailer") is BringATrailerAdapter
    print("    ok")

    print("· Cars & Bids adapter (second source)")
    assert ADAPTERS_BY_NAME.get("Cars & Bids") is CarsAndBidsAdapter
    cab_url = "https://carsandbids.com/auctions/3xY7Qa9b/1998-bmw-m3-sedan"
    assert CarsAndBidsAdapter().make_external_id(cab_url + "/") == "cab:3xY7Qa9b"
    blob = ('<url><loc>https://carsandbids.com/auctions/3xY7Qa9b/1998-bmw-m3-sedan</loc></url>'
            '<url><loc>https://carsandbids.com/past-auctions</loc></url>')
    found = CarsAndBidsAdapter.LISTING_RE.findall(blob)
    assert found and found[0].endswith("1998-bmw-m3-sedan"), found
    cab_fixture = """<!doctype html><html><head>
      <meta property="og:title" content="No Reserve: 1998 BMW M3 Sedan 5-Speed">
      <meta property="og:image" content="https://img.example/m3.jpg">
      <script type="application/ld+json">
      {"@context":"https://schema.org","@type":"Product",
       "name":"1998 BMW M3 Sedan 5-Speed",
       "image":["https://img.example/m3-1.jpg"],
       "vehicleTransmission":"5-speed manual",
       "offers":{"@type":"Offer","price":"24500","priceCurrency":"USD",
                 "priceValidUntil":"2026-07-03T20:00:00Z"}}
      </script></head><body>No Reserve auction</body></html>"""
    clot = CarsAndBidsAdapter().parse_html(cab_url, cab_fixture)
    assert clot is not None and clot.is_valid(), clot
    crow = clot.to_row()
    assert crow["make"] == "BMW" and crow["year"] == 1998, crow
    assert crow["external_lot_id"] == "cab:3xY7Qa9b", crow
    assert crow["reserve_status"] == "no-reserve", crow
    assert crow["auction_type"] == "online" and crow["current_bid"] == 24500.0, crow
    print("    ok")

    print("· sold-result parse")
    sold = "<html><body>Sold for $92,000 on January 5, 2026 to bidder42.</body></html>"
    res = BringATrailerAdapter().parse_result("https://bringatrailer.com/listing/x/", sold)
    assert res.get("sold") is True, res
    assert res.get("sold_price") == 92000.0, res
    assert res.get("sold_date") == "2026-01-05", res
    notmet = "<html><body>Bid to $48,000 (Reserve Not Met)</body></html>"
    nm = BringATrailerAdapter().parse_result("u", notmet)
    assert nm.get("sold") is False and nm.get("final_bid") == 48000.0, nm
    print("    ok")

    print("· JSON-API helpers (_first / _to_iso / _abs_url)")
    assert _first({"a": "", "b": [], "c": "x"}, "a", "b", "c") == "x"
    assert _first({"flag": False}, "flag") is False          # False is a real value
    assert _first({}, "x") is None
    assert _to_iso("2026-07-04T10:00:00").startswith("2026-07-04")
    assert _to_iso("2026-07-04").startswith("2026-07-04")
    assert _to_iso("Saturday, 4 July 2026").startswith("2026-07-04")
    assert _to_iso("1783101600").startswith("2026-")          # epoch seconds
    assert _to_iso("not a date") is None
    assert _abs_url("https://rmsothebys.com", "/auctions/tc26/") == "https://rmsothebys.com/auctions/tc26/"
    assert _abs_url("https://rmsothebys.com", "//cdn.x/y.jpg") == "https://cdn.x/y.jpg"
    assert _abs_url("https://rmsothebys.com", "https://abs/z.jpg") == "https://abs/z.jpg"
    assert _parse_estimate_range("€450,000 - €550,000") == (450000.0, 550000.0, "EUR")
    assert _parse_estimate_range("$1,000,000 - $1,500,000") == (1000000.0, 1500000.0, "USD")
    assert _parse_estimate_range("£90,000 - £120,000")[2] == "GBP"
    assert _parse_estimate_range("Estimate available upon request") == (None, None, None)
    assert _parse_money("£1,200,000 GBP") == (1200000.0, "GBP")
    assert _parse_money("Sold for $2,500,000") == (2500000.0, "USD")
    assert _parse_money("Bid to €410,000") == (410000.0, "EUR")
    assert _parse_money("") == (None, None)
    print("    ok")

    print("· RM Sotheby's adapter (JSON API, third source)")
    assert ADAPTERS_BY_NAME.get("RM Sotheby's") is RMSothebysAdapter
    # an API source must override collect() (no discover/parse_html path)
    assert RMSothebysAdapter.collect is not SourceAdapter.collect
    rm = RMSothebysAdapter()
    rm_item = {
        "id": "a1b2c3", "lotNumber": "107",
        "publicName": "2006 Mercedes-Benz CLK DTM AMG Cabriolet",
        "subHeading": "One of just 80 convertibles",
        "lowEstimate": 450000, "highEstimate": 550000, "currency": "EUR",
        "withoutReserve": False,
        "auctionName": "The Tegernsee Auction", "auctionCode": "TC26",
        "auctionDate": "2026-07-04T10:00:00",
        "location": "Gmund am Tegernsee, Germany",
        "image": "https://img.rm/clk-1.jpg",
        "slug": "r0107-2006-mercedes-benz-clk-dtm-amg-cabriolet",
    }
    rr = rm._to_lot(rm_item, "tc26").to_row()
    for k in ("year", "make", "model", "auction_type", "currency",
              "estimate_low", "estimate_high", "lot_number", "auction_end_date"):
        print(f"    {k:16} = {rr.get(k)}")
    assert rr["year"] == 2006 and rr["make"] == "Mercedes-Benz", rr
    assert rr["auction_type"] == "live", rr
    assert rr["external_lot_id"] == "rm:a1b2c3", rr
    assert rr["estimate_low"] == 450000.0 and rr["estimate_high"] == 550000.0, rr
    assert rr["currency"] == "EUR", rr
    assert rr["lot_number"] == "107", rr
    assert rr["reserve_status"] == "reserve", rr
    assert rr["auction_event_name"] == "The Tegernsee Auction", rr
    assert rr["auction_end_date"].startswith("2026-07-04"), rr
    assert rr["image_url"] == "https://img.rm/clk-1.jpg", rr
    assert rr["source_url"].endswith(
        "/auctions/tc26/lots/r0107-2006-mercedes-benz-clk-dtm-amg-cabriolet/"), rr
    # robustness: nested estimate object, photos[] of dicts, relative lotUrl,
    # missing id (-> code+lot fallback), no-reserve flag
    rm_item2 = {
        "lotNumber": 22, "title": "1995 Ferrari F50",
        "estimate": {"low": 3200000, "high": 3800000, "currency": "USD"},
        "saleName": "The Monterey Auction", "date": "2026-08-15",
        "noReserve": True,
        "photos": [{"imageUrl": "https://img.rm/f50.jpg"}],
        "lotUrl": "/auctions/mo26/lots/f50/",
    }
    rr2 = rm._to_lot(rm_item2, "mo26").to_row()
    assert rr2["make"] == "Ferrari" and rr2["year"] == 1995, rr2
    assert rr2["estimate_low"] == 3200000.0 and rr2["currency"] == "USD", rr2
    assert rr2["external_lot_id"] == "rm:MO26-22", rr2
    assert rr2["reserve_status"] == "no-reserve", rr2
    assert rr2["image_url"] == "https://img.rm/f50.jpg", rr2
    assert rr2["source_url"].endswith("/auctions/mo26/lots/f50/"), rr2
    # non-car / memorabilia with no year -> dropped by is_valid()
    assert rm._to_lot({"publicName": "A Private Collection of Motoring Art"}, "tc26").is_valid() is False
    # --- the REAL RM JSON shape (verbatim from a live dump: the Senna NSX) ---
    # estimate in 'value' (preSaleEstimate empty) · sale name in 'header' ·
    # photo in 'crop' (a .webp) · country via 'locationFlag' path · blank 'lot'
    # falls back to 'referenceId'.
    rm_real = {
        "id": "7efde768-ce89-4588-b50c-46169ddd6153",
        "publicName": "1991 Honda NSX",
        "lot": "",
        "value": "\u00a3500,000 - \u00a3800,000 GBP",
        "valueType": "",
        "preSaleEstimate": "",
        "header": "THE LONDON AUCTION 2026",
        "auctionStyleName": "RM | SOTHEBY'S",
        "collection": "Ayrton Senna's personally allocated Honda NSX",
        "crop": "https://cdn.rmsothebys.com/f/c/c/a/a/3/fccaa35ea.webp",
        "locationFlag": "/media/General/Flags/241858/gb.png",
        "link": "/auctions/lf26/lots/r0002-1991-honda-nsx/",
        "referenceId": "r0002", "sold": False, "isStillForSale": True,
    }
    rr3 = rm._to_lot(rm_real, "lf26").to_row()
    assert rr3["year"] == 1991 and rr3["make"] == "Honda", rr3
    assert rr3["estimate_low"] == 500000.0 and rr3["estimate_high"] == 800000.0, rr3  # from 'value'
    assert rr3["currency"] == "GBP", rr3
    assert rr3["external_lot_id"] == "rm:7efde768-ce89-4588-b50c-46169ddd6153", rr3
    assert rr3["auction_event_name"] == "THE LONDON AUCTION 2026", rr3               # 'header', not styleName
    assert rr3["lot_number"] == "r0002", rr3                                          # blank lot -> referenceId
    assert rr3["location"] == "United Kingdom", rr3                                   # flag path -> country
    assert rr3["image_url"] == "https://cdn.rmsothebys.com/f/c/c/a/a/3/fccaa35ea.webp", rr3  # 'crop'
    assert rr3["description_short"].startswith("Ayrton Senna"), rr3
    assert rr3["source_url"].endswith("/auctions/lf26/lots/r0002-1991-honda-nsx/"), rr3
    # a SOLD lot's 'value' is a realized price: captured as current_bid +
    # status='sold' (so it drops off the active board), suppressed as estimate.
    sold_obj = rm._to_lot({"id": "z9", "publicName": "1965 Shelby Cobra",
                           "value": "$1,200,000 USD", "valueType": "Sold", "sold": True,
                           "crop": "https://cdn.x/c.webp"}, "mo26",
                          {"date": "2026-08-15T10:00:00"})
    sold_lot = sold_obj.to_row()
    assert sold_lot.get("estimate_low") is None and sold_lot.get("estimate_high") is None, sold_lot
    assert sold_lot.get("current_bid") == 1200000.0, sold_lot
    assert sold_lot.get("currency") == "USD", sold_lot
    assert sold_lot.get("status") == "sold", sold_lot
    # …and that sold lot becomes a sales_history comp at ingest
    comps = sold_sales_rows([sold_obj])
    assert len(comps) == 1, comps
    assert comps[0]["sold_price"] == 1200000.0 and comps[0]["currency"] == "USD", comps
    assert comps[0]["make"] == "Shelby" and comps[0]["sold_date"] == "2026-08-15", comps
    assert comps[0]["external_id"] == "rm:z9", comps
    # an unsold (estimate) lot is NOT a comp
    assert sold_sales_rows([rm._to_lot({"id": "e1", "publicName": "1991 Honda NSX",
                            "value": "£500,000 - £800,000 GBP"}, "lf26")]) == []
    # auction-level date: pulled from the response envelope and stamped on lots
    env_resp = {"options": {"auction": "TC26", "auctionDate": "2026-07-04T10:00:00",
                            "location": "Gmund am Tegernsee, Germany"},
                "items": [], "pager": {"totalItems": 0}}
    m = rm._meta_from_response(env_resp)
    assert m.get("date", "").startswith("2026-07-04"), m
    # multi-day sale -> earliest day wins
    m2 = rm._meta_from_response({"options": {"days": [{"date": "2026-08-16"},
                                                      {"date": "2026-08-15"}]}})
    assert m2.get("date", "").startswith("2026-08-15"), m2
    # a lot with no date inherits the auction date; flag-less location falls back to meta
    dated = rm._to_lot({"id": "d1", "publicName": "1991 Honda NSX",
                        "value": "£500,000 - £800,000 GBP"}, "lf26",
                       {"date": "2026-09-12T09:00:00", "location": "London, UK"}).to_row()
    assert dated["auction_end_date"].startswith("2026-09-12"), dated
    assert dated["location"] == "London, UK", dated
    # an explicit per-lot date still beats the auction meta
    own = rm._to_lot({"id": "d2", "publicName": "1991 Honda NSX", "date": "2026-10-01"},
                     "lf26", {"date": "2026-09-12"}).to_row()
    assert own["auction_end_date"].startswith("2026-10-01"), own
    # auction-code discovery: env override wins and is normalized
    os.environ["RADAR_RM_AUCTIONS"] = "TC26, mo26 ,Wp26"
    try:
        assert rm.discover_codes(Fetcher(respect_robots=False)) == ["tc26", "mo26", "wp26"]
    finally:
        del os.environ["RADAR_RM_AUCTIONS"]
    print("    ok")

    print("· upsert batch dedup (Postgres 21000 guard)")
    sb = Supabase("https://x.supabase.co", "k")          # enabled (url+key)
    captured: dict = {}
    class _Resp:
        status_code, text = 200, ""
        def raise_for_status(self): pass
    _orig_post = requests.post
    def _fake_post(url, headers=None, json=None, timeout=None):
        captured["rows"] = json
        return _Resp()
    requests.post = _fake_post
    try:
        n = sb.upsert_lots([
            {"source_name": "RM Sotheby's", "external_lot_id": "rm:dupe", "year": 1},
            {"source_name": "RM Sotheby's", "external_lot_id": "rm:dupe", "year": 2},
            {"source_name": "RM Sotheby's", "external_lot_id": "rm:other", "year": 3},
        ])
    finally:
        requests.post = _orig_post
    assert n == 2, n
    keys = {(r["source_name"], r["external_lot_id"]) for r in captured["rows"]}
    assert keys == {("RM Sotheby's", "rm:dupe"), ("RM Sotheby's", "rm:other")}, captured["rows"]
    dupe_row = next(r for r in captured["rows"] if r["external_lot_id"] == "rm:dupe")
    assert dupe_row["year"] == 2, dupe_row                 # last write wins
    print("    ok")

    print("· The Market by Bonhams adapter (Nuxt /api/listings JSON)")
    tm = TheMarketAdapter()
    # slug rule matches the site's own client-side route builder
    assert TheMarketAdapter._tm_slug("Rolls-Royce") == "rolls-royce"
    assert TheMarketAdapter._tm_slug("20/25 Doctors Coupé") == "2025-doctors-coup"
    assert TheMarketAdapter._tm_slug("20 HP Limousine de Ville by Thrupp & Maberley") == \
        "20-hp-limousine-de-ville-by-thrupp--maberley"
    # wall-clock close time + IANA tz -> UTC instant (London = BST/UTC+1 here)
    assert _to_iso_tz("2026-06-29 12:00:00", "Europe/London").startswith("2026-06-29T11:00:00"), \
        _to_iso_tz("2026-06-29 12:00:00", "Europe/London")
    # an already-absolute value is passed straight through
    assert _to_iso_tz("2026-06-22T08:00:00.000000Z", "Europe/London").startswith("2026-06-22T08:00:00")
    # a real live-feed record (decoded from window.__NUXT__)
    tm_live = {
        "id": "e7946edd-61a1-41f3-b7b6-b350ca4f5049",
        "end_date": "2026-06-29 12:00:00", "timezone": "Europe/London",
        "start_date": "2026-06-22T08:00:00.000000Z",
        "image": "e7946edd-61a1-41f3-b7b6-b350ca4f5049/5f0.jpg?optimizer=image&width=650&format=jpg",
        "lot_number": 5093, "location_country": "GB", "location_country_name": "United Kingdom",
        "location": "THE MARKET HQ", "make": "Rolls-Royce", "model": "20/25 Doctors Coupé",
        "highest_bid": 2800000, "highest_bid_formatted": "\u00a328,000",
        "status": 1, "year": "1931", "currency": "GBP",
        "reserve_status": "reserve-not-close", "visible": True, "bids_count": 6,
    }
    ll = tm._to_lot(tm_live, sold=False).to_row()
    assert ll["year"] == 1931 and ll["make"] == "Rolls-Royce" and ll["model"] == "20/25 Doctors Coupé", ll
    assert ll["auction_type"] == "online" and ll["status"] == "upcoming", ll
    assert ll["current_bid"] == 28000.0 and ll["currency"] == "GBP", ll          # pence -> pounds
    assert ll["reserve_status"] == "reserve", ll                                  # only no-reserve maps specially
    assert ll["external_lot_id"] == "tm:e7946edd-61a1-41f3-b7b6-b350ca4f5049", ll
    assert ll["lot_number"] == "5093", ll
    assert ll["location"] == "United Kingdom", ll
    assert ll["auction_end_date"].startswith("2026-06-29T11:00:00"), ll           # BST -> UTC
    assert ll["source_url"] == ("https://www.themarket.co.uk/listings/rolls-royce/"
                                "2025-doctors-coup/e7946edd-61a1-41f3-b7b6-b350ca4f5049"), ll
    assert ll["image_url"].startswith("https://cdn.themarket.co.uk/"), ll
    # no-reserve detection
    nr = tm._to_lot({**tm_live, "reserve_status": "no-reserve"}, sold=False).to_row()
    assert nr["reserve_status"] == "no-reserve", nr

    # collect(): live filter keeps status==1, skips buy-now/ended (5); /results
    # sold lots become comps via the normal run() path.
    class _R:
        status_code = 200
        def __init__(self, payload): self._p = payload
        def json(self): return self._p
    def _fake_get(url, headers=None):
        if "/api/listings/live" in url and "page=1" in url:
            return _R({"data": [tm_live, {**tm_live, "id": "dead", "status": 5}],
                       "meta": {"total_pages": 1, "per_page": 51, "total": 2}})
        if "/api/listings/results" in url and "page=1" in url:
            return _R({"data": [{"id": "sold-1", "make": "Ferrari", "model": "Dino 246 GT",
                                 "year": "1972", "currency": "GBP", "final_price": 35000000,
                                 "end_date": "2026-06-20 12:00:00", "timezone": "Europe/London",
                                 "lot_number": 4900, "reserve_status": "no-reserve",
                                 "image": "x/y.jpg", "tagline": "Beautiful"}],
                       "meta": {"total_pages": 1, "per_page": 51, "total": 1}})
        return _R({"data": [], "meta": {"total_pages": 1}})
    f = Fetcher(respect_robots=False)
    f.get = _fake_get                                            # type: ignore[assignment]
    got = {l.external_lot_id: l for l in tm.collect(f)}
    assert "tm:e7946edd-61a1-41f3-b7b6-b350ca4f5049" in got, sorted(got)
    assert "tm:dead" not in got, "status!=1 must be skipped"     # buy-now/ended filtered out
    assert "tm:sold-1" in got and got["tm:sold-1"].status == "sold", sorted(got)
    assert got["tm:sold-1"].current_bid == 350000.0, got["tm:sold-1"].current_bid  # 35000000 pence
    comps = sold_sales_rows(list(got.values()))
    assert any(c["external_id"] == "tm:sold-1" and c["sold_price"] == 350000.0 for c in comps), comps
    # hot-refresh parse() resolves a lot by its trailing UUID from the live feed
    tm2 = TheMarketAdapter()
    f2 = Fetcher(respect_robots=False)
    f2.get = _fake_get                                           # type: ignore[assignment]
    refreshed = tm2.parse("https://www.themarket.co.uk/listings/rolls-royce/2025-doctors-coup/"
                          "e7946edd-61a1-41f3-b7b6-b350ca4f5049", f2)
    assert refreshed and refreshed.external_lot_id == "tm:e7946edd-61a1-41f3-b7b6-b350ca4f5049", refreshed
    print("    ok")

    print("· Bonhams Cars adapter (__NEXT_DATA__ SSR, fourth source)")
    assert ADAPTERS_BY_NAME.get("Bonhams Cars") is BonhamsCarsAdapter
    assert BonhamsCarsAdapter.collect is not SourceAdapter.collect   # SSR source overrides collect()
    bh = BonhamsCarsAdapter()
    # helpers: YEAR/MAKE/MODEL from single-line titles AND multi-line comp names
    assert _parse_ymm("1936 Aston Martin 2-litre Speed competition two-seater Chassis no. L6/713/U") \
        == (1936, "Aston Martin", "2-litre Speed competition two-seater")     # two-word marque
    assert _parse_ymm("1953 Mercedes-Benz 300 S Roadster Chassis no. 188012 00071/53") \
        == (1953, "Mercedes-Benz", "300 S Roadster")                          # hyphenated = one token
    assert _parse_ymm("<I>prov</I><BR /><B>1929 Bentley 4½ Liter Tourer<BR />Coachwork by X</B>"
                      "<BR />Chassis no. FB 3320")[:2] == (1929, "Bentley")   # year line, not prov prefix
    assert _parse_chassis("X Chassis no. L6/713/U Engine no. L6/713/U") == "L6/713/U"
    assert _bonhams_img({"url": "https://img/x.jpg?src=a", "URLParams": "left=0.1&right=0.9"}) \
        == "https://img/x.jpg?src=a&left=0.1&right=0.9&width=640"
    assert _bonhams_date_from_img(
        "https://images2.bonhams.com/image?src=Images/live/2022-05/15/2.jpg") == "2022-05-15T00:00:00+00:00"

    # real upcoming-lot fixtures (values verbatim from the /cars/ __NEXT_DATA__ blob)
    hit_aston = {
        "id": "6172587", "lotUniqueId": "6172587", "auctionId": "31857", "auctionType": "PUBLIC",
        "slug": "1936-aston-martin-2-litre-speed-competition-two-seater-chassis-no-l6713u-engine-no-l6713u",
        "title": "1936 Aston Martin 2-litre Speed competition two-seater "
                 "Chassis no. L6/713/U Engine no. L6/713/U",
        "styledDescription": "<I>The Ex T.A.S.O Mathieson</I> 1936 Aston Martin 2-litre Speed "
                             "competition two-seater",
        "country": {"name": "United Kingdom"}, "currency": {"iso_code": "GBP"},
        "price": {"estimateLow": 500000, "estimateHigh": 600000, "hammerPremium": 0, "hammerPrice": 0},
        "biddableFrom": {"timestamp": 1789810200}, "auctionEndDate": {"timestamp": 1789858799},
        "flags": {"isWithoutReserve": False, "isPreview": True}, "lotNo": {"full": "0"},
        "image": {"url": "https://images1.bonhams.com/image?src=Images/live/2026-06/25/25873217-1-25.jpg",
                  "URLParams": "left=0.056666666666&right=0.946666666666"},
    }
    ra = bh._to_lot(hit_aston).to_row()
    for k in ("year", "make", "model", "currency", "estimate_low", "reserve_status", "auction_start_date"):
        print(f"    {k:18} = {ra.get(k)}")
    assert ra["year"] == 1936 and ra["make"] == "Aston Martin", ra
    assert ra["model"] == "2-litre Speed competition two-seater", ra
    assert ra["external_lot_id"] == "bonhams:6172587", ra
    assert ra["auction_type"] == "live" and ra["status"] == "upcoming", ra
    assert ra["currency"] == "GBP", ra
    assert ra["estimate_low"] == 500000.0 and ra["estimate_high"] == 600000.0, ra
    assert ra["reserve_status"] == "reserve", ra
    assert ra.get("lot_number") is None, ra                       # preview lots ship lotNo "0"
    assert ra["chassis"] == "L6/713/U", ra
    assert ra["location"] == "United Kingdom", ra
    assert ra.get("auction_event_name") is None, ra               # public sale name absent in /cars/ feed
    assert ra["auction_start_date"].startswith("2026-09-19"), ra  # trust epoch, not mislabeled datetime
    assert ra["auction_end_date"].startswith("2026-09-19"), ra
    assert ra["source_url"] == (
        "https://cars.bonhams.com/auction/31857/preview-lot/6172587/"
        "1936-aston-martin-2-litre-speed-competition-two-seater-chassis-no-l6713u-engine-no-l6713u/"), ra
    assert ra["image_url"].startswith("https://images1.bonhams.com/") \
        and ra["image_url"].endswith("&width=640"), ra

    # native per-lot currency: Belgian lot is EUR w/ EUR estimates, NOT the GBP-normalized fields
    hit_merc = {
        "id": "6156079", "auctionId": "32045", "auctionType": "PUBLIC",
        "slug": "1953-mercedes-benz-300-s-roadster",
        "title": "1953 Mercedes-Benz 300 S Roadster Chassis no. 188012 00071/53 Engine no. 188920 00073/53",
        "styledDescription": "", "country": {"name": "Belgium"}, "currency": {"iso_code": "EUR"},
        "price": {"estimateLow": 350000, "estimateHigh": 400000,
                  "GBPLowEstimate": 302813.48, "GBPHighEstimate": 346072.55},
        "biddableFrom": {"timestamp": 1791712800}, "auctionEndDate": {"timestamp": 1791755999},
        "flags": {"isWithoutReserve": False}, "lotNo": {"full": "0"},
        "image": {"url": "https://images1.bonhams.com/image?src=Images/live/2026-05/21/25863022-1-2.jpg"},
    }
    rmb = bh._to_lot(hit_merc).to_row()
    assert rmb["make"] == "Mercedes-Benz" and rmb["model"] == "300 S Roadster", rmb
    assert rmb["currency"] == "EUR", rmb
    assert rmb["estimate_low"] == 350000.0 and rmb["estimate_high"] == 400000.0, rmb   # native, not £302,813
    assert rmb["location"] == "Belgium" and rmb["external_lot_id"] == "bonhams:6156079", rmb

    # no-reserve flag mapping
    hit_bug = {
        "id": "6170829", "auctionId": "31857", "auctionType": "PUBLIC",
        "slug": "1929-bugatti-type-35c-grand-prix-two-seater-chassis-no-4930",
        "title": "1929 Bugatti Type 35C Grand Prix Two-Seater Chassis no. 4930",
        "styledDescription": "", "country": {"name": "United Kingdom"}, "currency": {"iso_code": "GBP"},
        "price": {"estimateLow": 500000, "estimateHigh": 700000},
        "biddableFrom": {"timestamp": 1789810200}, "auctionEndDate": {"timestamp": 1789858799},
        "flags": {"isWithoutReserve": True}, "lotNo": {"full": "0"},
        "image": {"url": "https://images1.bonhams.com/image?src=Images/live/2026-06/23/25829892-4-27.jpg"},
    }
    assert bh._to_lot(hit_bug).to_row()["reserve_status"] == "no-reserve"

    # 'Refer to department' -> 0/0 estimates collapse to None (lot still valid)
    hit_jag = {
        "id": "6170637", "auctionId": "31959", "auctionType": "PUBLIC",
        "slug": "1951-jaguar-xk120-roadster-chassis-no-670636",
        "title": "1951 Jaguar XK120 Roadster Chassis no. 670636", "styledDescription": "",
        "country": {"name": "United States"}, "currency": {"iso_code": "USD"},
        "price": {"estimateLow": 0, "estimateHigh": 0}, "lotNo": {"full": "0"},
        "biddableFrom": {"timestamp": 1786640400}, "auctionEndDate": {"timestamp": 1786690799},
        "flags": {"isWithoutReserve": True},
        "image": {"url": "https://images2.bonhams.com/image?src=Images/live/2026-06/22/x.jpg"},
    }
    rj = bh._to_lot(hit_jag).to_row()
    assert rj.get("estimate_low") is None and rj.get("estimate_high") is None, rj
    assert rj["currency"] == "USD" and rj["make"] == "Jaguar", rj

    # PRIAUC private sale: year-2100 'biddableFrom' sentinel -> no dates + "Private Sales" name
    hit_priv = {
        "id": "6148273", "auctionId": "26417", "auctionType": "PRIAUC",
        "slug": "1973-ferrari-365-gtb4-daytona-chassis-no-16309",
        "title": "1973 Ferrari 365 GTB/4 Daytona Chassis no. 16309", "styledDescription": "",
        "country": {"name": "United Kingdom"}, "currency": {"iso_code": "GBP"},
        "price": {"estimateLow": 0, "estimateHigh": 0}, "lotNo": {"full": "0"},
        "biddableFrom": {"timestamp": 4133941200}, "auctionEndDate": {"timestamp": 4133980799},
        "flags": {"isWithoutReserve": False},
        "image": {"url": "https://images1.bonhams.com/image?src=Images/live/2026-05/05/x.jpg"},
    }
    rp = bh._to_lot(hit_priv).to_row()
    assert rp["make"] == "Ferrari" and rp["model"] == "365 GTB/4 Daytona", rp
    assert rp["auction_event_name"] == "Private Sales", rp
    assert rp.get("auction_start_date") is None and rp.get("auction_end_date") is None, rp

    # exceptionalResults -> sold comps (hammerPremium = inc-premium realized price)
    ex_bentley = {
        "saleNo": 27656, "lotNo": "135", "saleLotNoUnique": 5562058,
        "lotName": "<I>Well-known car, extensively toured</I><BR /><B>1929 Bentley 4½ Liter Tourer<BR />"
                   "Coachwork in the style of Vanden Plas</B><BR />Chassis no. FB 3320<BR />Engine no. FB 3322",
        "imageURL": "https://images2.bonhams.com/image?src=Images/live/2022-05/15/25213302-1-1.jpg",
        "imageURLParams": "top=0.084444444444&left=0.136666666666",
        "hammerPrice": 545000, "hammerPremium": 604500, "currencySymbol": "US$",
    }
    ex_alfa = {                                                   # hammerPremium 0 -> unsold -> dropped
        "saleNo": 27509, "lotNo": "78", "saleLotNoUnique": 5570894,
        "lotName": "<b>1974 Alfa Romeo TIPO 33 TT 12 </b><br /> Chassis no. 11512.007",
        "imageURL": "https://images2.bonhams.com/image?src=Images/live/2022-06/09/x.jpg",
        "imageURLParams": "", "hammerPrice": 0, "hammerPremium": 0, "currencySymbol": "US$",
    }
    rc = bh._to_comp(ex_bentley).to_row()
    assert rc["external_lot_id"] == "bonhams:5562058", rc
    assert rc["year"] == 1929 and rc["make"] == "Bentley" and rc["model"] == "4½ Liter Tourer", rc
    assert rc["current_bid"] == 604500.0 and rc["currency"] == "USD", rc
    assert rc["status"] == "sold" and rc["chassis"] == "FB 3320", rc
    assert rc["auction_end_date"].startswith("2022-05-15"), rc   # date derived from image path
    assert rc["source_url"] == "https://cars.bonhams.com/auction/27656/lot/135/", rc
    assert bh._to_comp(ex_alfa) is None, "hammerPremium 0 must be filtered out"

    # end-to-end collect(): parse the blob, attach comps; run() routes sold->comps
    payload = {"props": {"pageProps": {
        "lots": {"found": 3, "nbPages": 1, "hits": [hit_aston, hit_merc, hit_bug]},
        "department": {"exceptionalResults": [ex_bentley, ex_alfa]},
    }}}
    class _BResp:
        status_code = 200
        def __init__(self, text): self.text = text
    def _bonhams_fake_get(url, headers=None):
        return _BResp('<!doctype html><html><body>'
                      '<script id="__NEXT_DATA__" type="application/json">'
                      + json.dumps(payload) + '</script></body></html>')
    fb = Fetcher(respect_robots=False)
    fb.get = _bonhams_fake_get                                    # type: ignore[assignment]
    out = bh.collect(fb)
    by_id = {l.external_lot_id: l for l in out}
    assert "bonhams:6172587" in by_id and "bonhams:6156079" in by_id, sorted(by_id)
    assert by_id["bonhams:6172587"].status == "upcoming", "preview lots stay on the board"
    assert "bonhams:5562058" in by_id and by_id["bonhams:5562058"].status == "sold", sorted(by_id)
    assert "bonhams:5570894" not in by_id, "unsold record (premium 0) must be dropped"
    comps = sold_sales_rows(out)
    assert any(c["external_id"] == "bonhams:5562058" and c["sold_price"] == 604500.0
               and c["make"] == "Bentley" and c["sold_date"] == "2022-05-15" for c in comps), comps
    # hot-refresh parse() resolves a lot by the numeric id in its preview-lot URL
    bh2 = BonhamsCarsAdapter()
    fb2 = Fetcher(respect_robots=False)
    fb2.get = _bonhams_fake_get                                   # type: ignore[assignment]
    ref = bh2.parse("https://cars.bonhams.com/auction/31857/preview-lot/6172587/1936-aston-martin/", fb2)
    assert ref and ref.external_lot_id == "bonhams:6172587", ref
    print("    ok")

    print("\nALL SELF-TESTS PASSED ✓")


def main() -> None:
    ap = argparse.ArgumentParser(description="Auction Radar ingestion + alerts worker")
    ap.add_argument("--source", default="bringatrailer", help="source key (see --list-sources)")
    ap.add_argument("--limit", type=int, default=None, help="max listings to process")
    ap.add_argument("--dry-run", action="store_true", help="print, don't write to DB / don't send")
    ap.add_argument("--no-robots", action="store_true",
                    help="(not recommended) skip robots.txt — only with explicit permission")
    ap.add_argument("--selftest", action="store_true", help="run offline tests and exit")
    ap.add_argument("--list-sources", action="store_true")
    # alerts
    ap.add_argument("--alerts", action="store_true", help="match saved searches and email digests")
    ap.add_argument("--soon-hours", type=int, default=24, help="'closing soon' window in hours")
    ap.add_argument("--new-within", type=int, default=48, help="treat lots added within N hours as 'new'")
    ap.add_argument("--bootstrap", action="store_true",
                    help="record current matches as already-sent without emailing (run once after deploy)")
    # hot refresh / loop
    ap.add_argument("--refresh-hot", action="store_true",
                    help="re-pull only lots closing soon (run on a tight cadence)")
    ap.add_argument("--harvest-results", action="store_true",
                    help="finalize closed lots: record sold prices to sales_history (comps)")
    ap.add_argument("--hot-hours", type=int, default=6, help="'hot' = online lots closing within N hours")
    ap.add_argument("--loop", action="store_true",
                    help="run continuously, interleaving full ingest, hot refresh, and alerts")
    ap.add_argument("--full-every", type=int, default=30, help="[loop] full ingest interval, minutes")
    ap.add_argument("--hot-every", type=int, default=120, help="[loop] hot refresh interval, seconds")
    ap.add_argument("--alert-every", type=int, default=10, help="[loop] alert pass interval, minutes")
    a = ap.parse_args()

    if a.list_sources:
        print("\n".join(sorted(ADAPTERS)))
        return
    if a.selftest:
        selftest()
        return
    if a.loop:
        run_loop(a.source, a.hot_hours, a.full_every, a.hot_every, a.alert_every, a.no_robots)
        return
    if a.refresh_hot:
        refresh_hot(a.hot_hours, a.dry_run, a.limit)
        return
    if a.harvest_results:
        harvest_results(a.dry_run, a.limit)
        return
    if a.alerts or a.bootstrap:
        run_alerts(a.soon_hours, a.new_within, a.dry_run, a.bootstrap)
        return
    if a.source not in ADAPTERS:
        ap.error(f"unknown source '{a.source}'. choices: {', '.join(sorted(ADAPTERS))}")
    run(a.source, a.dry_run, a.limit, a.no_robots)


if __name__ == "__main__":
    main()
