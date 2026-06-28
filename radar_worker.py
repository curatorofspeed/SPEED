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

    def get(self, url: str) -> Optional[requests.Response]:
        if not self._allowed(url):
            log.warning("robots.txt disallows %s — skipping", url)
            return None
        for attempt in range(1, MAX_RETRIES + 1):
            self._throttle()
            try:
                r = self.s.get(url, timeout=REQUEST_TIMEOUT)
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
        r = requests.post(
            f"{self.url}/rest/v1/auction_lots?on_conflict=source_name,external_lot_id",
            headers={**self.h, "Prefer": "resolution=merge-duplicates,return=minimal"},
            json=rows, timeout=REQUEST_TIMEOUT)
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
        Confirm the patterns against a real completed page for each source."""
        head = text[:40000]
        sold_m = re.search(r"sold\s+for[^0-9$£€]*([$£€])?\s*([\d][\d,]*)", head, re.I)
        if not sold_m:
            if re.search(r"reserve\s+not\s+met|did\s+not\s+sell|bid\s+to\b", head, re.I):
                return {"sold": False}
        if not sold_m:
            return {"sold": False}
        price = to_float(sold_m.group(2))
        sym = sold_m.group(1) or ""
        currency = {"£": "GBP", "€": "EUR", "$": "USD"}.get(sym, "USD")
        sold_date = None
        dm = re.search(r"sold\s+for[^.]*?on\s+([A-Z][a-z]+ \d{1,2},? \d{4})", head, re.I)
        if dm:
            try:
                sold_date = dt.datetime.strptime(dm.group(1).replace(",", ""), "%B %d %Y").date().isoformat()
            except ValueError:
                sold_date = None
        if price:
            return {"sold": True, "sold_price": price, "currency": currency, "sold_date": sold_date}
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


# register adapters here as you add them (Collecting Cars, PCARMARKET, …)
ADAPTERS: dict[str, type[SourceAdapter]] = {
    "bringatrailer": BringATrailerAdapter,
    "carsandbids": CarsAndBidsAdapter,
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
            finals.append((c["id"], "withdrawn", None))
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
    assert BringATrailerAdapter().parse_result("u", notmet).get("sold") is False
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
