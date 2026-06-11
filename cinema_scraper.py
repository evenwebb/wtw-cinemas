#!/usr/bin/env python3
"""WTW Cinemas Calendar Scraper.

Scrapes upcoming film releases from WTW Cinemas and generates per-cinema
iCalendar feeds plus an index page for GitHub Pages.
"""
from __future__ import annotations

import hashlib
import html as html_mod
import json
import logging
import os
import re
import sys
import threading
import time
import warnings
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime, timedelta, timezone
from itertools import groupby
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from zoneinfo import ZoneInfo

warnings.filterwarnings("ignore", message=".*OpenSSL.*", category=UserWarning)

import requests
from bs4 import BeautifulSoup

# ── Constants ──────────────────────────────────────────────────────────────────
HTTP_TIMEOUT = 60
HTTP_RETRIES = 3
HTTP_RETRY_DELAY = 1
HTTP_RETRY_MULTIPLIER = 2
USER_AGENT = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/131.0.0.0 Safari/537.36"
)
ICAL_LINE_LENGTH = 75
LONDON_TZ = ZoneInfo("Europe/London")


def format_london_timestamp(dt: Optional[datetime] = None) -> str:
    dt = dt or datetime.now(LONDON_TZ)
    return dt.astimezone(LONDON_TZ).strftime("%Y-%m-%d %H:%M %Z")
ICAL_NEWLINE = "\r\n"
CALENDAR_TIMEZONE = os.getenv("CALENDAR_TIMEZONE", "Europe/London")
OUTPUT_DIR = "docs"
WTW_BASE_URL = "https://wtwcinemas.co.uk"
RELEASE_HISTORY_PATH = ".release_history.json"
RELEASE_HISTORY_MAX_DAYS = 730
CACHE_FILE = ".film_cache.json"
CACHE_EXPIRY_DAYS = 7
TMDB_CACHE_FILE = ".tmdb_cache.json"
TMDB_CACHE_DAYS = 30
TMDB_DELAY_SEC = 0.2
POSTERS_DIR = "docs/posters"
CERTS_DIR = "docs/certs"
FINGERPRINT_FILE = ".scrape_fingerprint"
MIN_SYNOPSIS_LENGTH = 50
MAX_SYNOPSIS_LENGTH = 500
SYNOPSIS_SKIP_TERMS = ["cookie", "privacy", "terms", "wheelchair", "audio description"]
MAX_WORKERS = min(4, os.cpu_count() or 4)

DATE_PATTERN = re.compile(r"(?:Released|Showing)\s+(?:on\s+)?(\d{1,2})(?:st|nd|rd|th)?\s+([A-Za-z]+)", re.IGNORECASE)
ALT_DATE_PATTERN = re.compile(r"(\d{1,2})(?:st|nd|rd|th)?\s+([A-Za-z]+)", re.IGNORECASE)
RUNTIME_RE = re.compile(r"(\d+)\s*(?:minutes?|mins?)", re.IGNORECASE)
FILM_LINK_RE = re.compile(r"/film/")
TITLE_CLEAN_RE = re.compile(r"\s*\([^)]*\)$")

# Special screening suffixes - stripped before TMDb search
TITLE_CLEAN_PATTERNS = [
    (re.compile(r"\s+Toddler Cinema$", re.IGNORECASE), ""),
    (re.compile(r"\s+Double Bill$", re.IGNORECASE), ""),
    (re.compile(r"\s+Triple Bill$", re.IGNORECASE), ""),
    (re.compile(r"\s*[-–]\s*Toddler Cinema$", re.IGNORECASE), ""),
    (re.compile(r"\s*[-–]\s*Kids Club$", re.IGNORECASE), ""),
    (re.compile(r"\s*[-–]\s*Silver Screen$", re.IGNORECASE), ""),
    (re.compile(r"\s*[-–]\s*Mini Movie Deal$", re.IGNORECASE), ""),
    (re.compile(r"\s*[-–]\s*Parent & Baby$", re.IGNORECASE), ""),
    (re.compile(r"\s+Parent & Baby$", re.IGNORECASE), ""),
    (re.compile(r"\s+Parent And Baby$", re.IGNORECASE), ""),
    (re.compile(r"\s*[-–]\s*Autism Friendly$", re.IGNORECASE), ""),
    (re.compile(r"\s+Autism Friendly$", re.IGNORECASE), ""),
    (re.compile(r"\s*[-–]\s*Event Cinema$", re.IGNORECASE), ""),
    (re.compile(r"\s+Event Cinema$", re.IGNORECASE), ""),
    (re.compile(r"\s+with Q&A$", re.IGNORECASE), ""),
    (re.compile(r"\s+with Q and A$", re.IGNORECASE), ""),
    (re.compile(r"\s*[-–]\s*with Q&A$", re.IGNORECASE), ""),
    (re.compile(r"\s+Silver Screen$", re.IGNORECASE), ""),
    (re.compile(r"\s*[-–]\s*Super Saver$", re.IGNORECASE), ""),
    (re.compile(r"\s+Super Saver$", re.IGNORECASE), ""),
    (re.compile(r"^NT Live:\s*", re.IGNORECASE), ""),
    (re.compile(r"^RBO \d{4}-\d{2}:\s*", re.IGNORECASE), ""),
]

# Screening labels for display - derived from pattern names
_SCREENING_LABEL_MAP = {
    "Toddler Cinema": "Toddler Cinema", "Kids Club": "Kids Club",
    "Silver Screen": "Silver Screen", "Mini Movie Deal": "Mini Movie Deal",
    "Parent & Baby": "Parent & Baby", "Parent And Baby": "Parent & Baby",
    "Autism Friendly": "Autism Friendly", "Event Cinema": "Event Cinema",
    "Super Saver": "Super Saver", "Double Bill": "Double Bill",
    "Triple Bill": "Triple Bill",
    "with Q&A": "Q&A", "with Q and A": "Q&A",
}

def extract_screening_label(title: str):
    """Return (cleaned_title, screening_label) for a film title.
    Matches against screening suffix patterns and returns the
    corresponding friendly label for UI display."""
    for pattern, _ in TITLE_CLEAN_PATTERNS:
        m = pattern.search(title)
        if m:
            cleaned = pattern.sub("", title).strip()
            # Derive label from the pattern name
            for key, label in _SCREENING_LABEL_MAP.items():
                if key.lower() in m.group(0).lower():
                    return cleaned, label
            return cleaned, ""
    return title, ""

# Non-film events to skip TMDb enrichment entirely
SKIP_TMDB_TERMS = [
    "live nation", "tribute", "comedy club", "pantomime", "panto",
    "psychic", "candlelit", "on tour", "presented by", "choir", "orchestra",
    "theatre company", "pride", "adults only",
]

# Strip anniversary / special-edition suffixes before TMDb search so
# "Shrek - 25th Anniversary" resolves to the original film
TMDB_SEARCH_STRIP_RE = re.compile(
    r"\s*[-–]\s*\d+(?:st|nd|rd|th)?\s*[Aa]nniversary\b.*$"
)

CINEMAS: Dict[str, dict] = {
    "st-austell": {
        "enabled": True,
        "name": "St Austell",
        "url": "https://wtwcinemas.co.uk/st-austell/coming-soon/",
        "whats_on_url": "https://wtwcinemas.co.uk/st-austell/whats-on/",
    },
    "newquay": {
        "enabled": True,
        "name": "Newquay",
        "url": "https://wtwcinemas.co.uk/newquay/coming-soon/",
        "whats_on_url": "https://wtwcinemas.co.uk/newquay/whats-on/",
    },
    "wadebridge": {
        "enabled": True,
        "name": "Wadebridge",
        "url": "https://wtwcinemas.co.uk/wadebridge/coming-soon/",
        "whats_on_url": "https://wtwcinemas.co.uk/wadebridge/whats-on/",
    },
    "truro": {
        "enabled": True,
        "name": "Truro",
        "url": "https://wtwcinemas.co.uk/truro/coming-soon/",
        "whats_on_url": "https://wtwcinemas.co.uk/truro/whats-on/",
    },
}

NOTIFICATION_TIME = "09:00"
NOTIFICATIONS: Dict[str, Any] = {"enabled": False, "alarms": []}

# BBFC age rating: extracted from film titles like "Film Name (15)" or "Film Name (12A)"
BBFC_PATTERN = re.compile(r"\((\d{1,2}A?|U|PG|R18)\)", re.IGNORECASE)
CERT_IMAGES = {"U": "cert-u.png", "PG": "cert-pg.png", "12": "cert-12.png", "12A": "cert-12a.png", "15": "cert-15.png", "18": "cert-18.png"}
WTW_CERT_BASE = "https://wtwcinemas.co.uk/wp-content/themes/wtw-2017/dist/images"

# Cinema addresses for map links
CINEMA_ADDRESSES = {
    "st-austell": "White+River+Cinema+St+Austell",
    "newquay": "Lighthouse+Cinema+Newquay",
    "wadebridge": "Regal+Cinema+Wadebridge",
    "truro": "Plaza+Cinema+Truro",
}
# Cinema coordinates for geolocation
CINEMA_COORDS = {
    "st-austell": (50.338, -4.795),
    "newquay": (50.416, -5.075),
    "wadebridge": (50.517, -4.835),
    "truro": (50.263, -5.051),
}

# Health check minimums (env-configurable)
HEALTH_MIN_FILMS = int(os.getenv("HEALTH_MIN_FILMS", "1"))
HEALTH_MIN_CINEMAS = int(os.getenv("HEALTH_MIN_CINEMAS", "1"))

TMDB_GENRE_MAP = {
    28: "Action", 12: "Adventure", 16: "Animation", 35: "Comedy",
    80: "Crime", 99: "Documentary", 18: "Drama", 10751: "Family",
    14: "Fantasy", 36: "History", 27: "Horror", 10402: "Music",
    9648: "Mystery", 10749: "Romance", 878: "Science Fiction",
    10770: "TV Movie", 53: "Thriller", 10752: "War", 37: "Western",
}

# ── Logging ────────────────────────────────────────────────────────────────────
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)
err_handler = logging.FileHandler("cinema_log.txt")
err_handler.setLevel(logging.WARNING)
logger.addHandler(err_handler)
import atexit as _atexit
@_atexit.register
def _close_log_handler():
    err_handler.close()


# ── HTTP ───────────────────────────────────────────────────────────────────────
def _session() -> requests.Session:
    """Return a requests Session with retry-compatible settings."""
    s = requests.Session()
    s.headers.update({"User-Agent": USER_AGENT})
    return s


def fetch_with_retries(
    url: str,
    retries: int = HTTP_RETRIES,
    timeout: int = HTTP_TIMEOUT,
    session: Optional[requests.Session] = None,
) -> requests.Response:
    """Return HTTP response with exponential-backoff retries."""
    s = session or _session()
    delay = HTTP_RETRY_DELAY
    for attempt in range(retries):
        try:
            resp = s.get(url, timeout=timeout)
            resp.raise_for_status()
            return resp
        except requests.RequestException as exc:
            logger.warning("Attempt %d/%d failed for %s: %s", attempt + 1, retries, url, exc)
            if attempt == retries - 1:
                raise
            time.sleep(delay)
            delay *= HTTP_RETRY_MULTIPLIER


def get_base_film_url(url: str) -> str:
    """Strip query string, return canonical film URL."""
    return url.split("?")[0] if "?" in url else url


# ── Caches ─────────────────────────────────────────────────────────────────────
def _cutoff(expiry_days: int) -> str:
    return (datetime.now(timezone.utc) - timedelta(days=expiry_days)).isoformat()


def _load_json_cache(path: str, ttl_days: int, label: str = "") -> Dict[str, dict]:
    if not os.path.exists(path):
        return {}
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
        limit = _cutoff(ttl_days)
        fresh = {k: v for k, v in data.items() if v.get("cached_at", "") > limit}
        logger.info("Loaded %s: %d entries (%d expired)", label, len(fresh), len(data) - len(fresh))
        return fresh
    except (json.JSONDecodeError, OSError) as e:
        logger.warning("%s load failed: %s", label, e)
        return {}


def _save_json_cache(path: str, cache: Dict[str, dict], label: str = "") -> None:
    try:
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(cache, f, indent=2, ensure_ascii=False)
        os.replace(tmp, path)
        logger.info("Saved %s: %d entries", label, len(cache))
    except OSError as e:
        logger.warning("%s save failed: %s", label, e)


def load_cache() -> Dict[str, dict]:
    return _load_json_cache(CACHE_FILE, CACHE_EXPIRY_DAYS, "film cache")


def save_cache(cache: Dict[str, dict]) -> None:
    _save_json_cache(CACHE_FILE, cache, "film cache")


def load_tmdb_cache() -> Dict[str, dict]:
    return _load_json_cache(TMDB_CACHE_FILE, TMDB_CACHE_DAYS, "TMDb cache")


def save_tmdb_cache(cache: Dict[str, dict]) -> None:
    _save_json_cache(TMDB_CACHE_FILE, cache, "TMDb cache")


def load_release_history() -> set:
    path = Path(RELEASE_HISTORY_PATH)
    if not path.is_file():
        return set()
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        out = set()
        for item in data:
            if not (isinstance(item, (list, tuple)) and len(item) >= 2):
                continue
            try:
                out.add((date.fromisoformat(item[0]), item[1]))
            except (ValueError, TypeError):
                pass
        return out
    except (json.JSONDecodeError, OSError) as e:
        logger.warning("Release history load failed: %s", e)
        return set()


def save_release_history(releases: set) -> None:
    today = date.today()
    cutoff = today - timedelta(days=RELEASE_HISTORY_MAX_DAYS)
    kept = [(d.isoformat(), t) for (d, t) in releases if d >= cutoff]
    try:
        Path(RELEASE_HISTORY_PATH).write_text(
            json.dumps(kept, ensure_ascii=False), encoding="utf-8"
        )
        logger.info("Saved release history: %d entries", len(kept))
    except OSError as e:
        logger.warning("Release history save failed: %s", e)


def _tmdb_cache_key(film_title: str) -> str:
    t = TITLE_CLEAN_RE.sub("", film_title).strip()
    t = re.sub(r"[\s\-:]+", " ", t.lower()).strip()
    return re.sub(r"[^a-z0-9]+", "-", t).strip("-") or "unknown"


# ── Date parsing ───────────────────────────────────────────────────────────────
def parse_date(text: str) -> Optional[date]:
    """Parse release date: "Expected: DD Month YYYY" or "Expected at WTW ... DDth Month"."""
    m = DATE_PATTERN.search(text)
    if m:
        day, month_str = int(m.group(1)), m.group(2)
        year = date.today().year
    else:
        m = ALT_DATE_PATTERN.search(text)
        if not m:
            return None
        day, month_str = int(m.group(1)), m.group(2)
        year = date.today().year

    try:
        month = datetime.strptime(month_str, "%B").month
    except ValueError:
        logger.warning("Unrecognised month '%s' in: %s", month_str, text)
        return None

    try:
        parsed = date(year, month, day)
    except ValueError:
        logger.warning("Invalid date: day=%d month=%d year=%d in: %s", day, month, year, text)
        return None

    # Auto-advance into next year if parsed date is in the past
    if parsed < date.today():
        for advance in range(1, 5):
            try:
                parsed = date(year + advance, month, day)
                break
            except ValueError:
                continue
    return parsed


def parse_uk_date(text: str, scrape_date: date) -> Optional[date]:
    """Parse UK showtime dates: 'Today 8 February', 'Tomorrow 9 February', 'Tuesday 10 February 2026'."""
    text = text.strip()
    today = scrape_date
    if "today" in text.lower():
        return today
    if "tomorrow" in text.lower():
        return today + timedelta(days=1)
    m = re.search(r"(\d{1,2})\s+([A-Za-z]+)\s+(\d{4})", text)
    if m:
        day, month_str, year = int(m.group(1)), m.group(2), int(m.group(3))
        try:
            return datetime.strptime(f"{day} {month_str} {year}", "%d %B %Y").date()
        except ValueError:
            pass
    m = re.search(r"(\d{1,2})\s+([A-Za-z]+)(?:\s|$)", text)
    if m:
        day, month_str = int(m.group(1)), m.group(2)
        year = scrape_date.year
        try:
            dt = datetime.strptime(f"{day} {month_str} {year}", "%d %B %Y").date()
            if dt < today:
                dt = datetime.strptime(f"{day} {month_str} {year + 1}", "%d %B %Y").date()
            return dt
        except ValueError:
            pass
    return None


# ── Film detail scraping ───────────────────────────────────────────────────────
_film_cache_lock = threading.Lock()
_tmdb_cache_lock = threading.Lock()


def fetch_film_details(
    film_url: str, cache: Dict[str, dict], session: Optional[requests.Session] = None
) -> Dict[str, str]:
    """Fetch runtime, cast, synopsis from a film page. Uses cache when available."""
    details: Dict[str, str] = {"runtime": "", "cast": "", "synopsis": "", "director": ""}
    if not film_url:
        return details

    base_url = get_base_film_url(film_url)

    # Thread-safe cache check
    with _film_cache_lock:
        if base_url in cache:
            c = cache[base_url].copy()
            c.pop("cached_at", None)
            return c

    try:
        logger.info("Fetching film: %s", film_url)
        resp = fetch_with_retries(film_url, session=session)
        soup = BeautifulSoup(resp.text, "html.parser")

        # Runtime: match "119 minutes" etc.
        for text in soup.stripped_strings:
            m = RUNTIME_RE.search(text)
            if m:
                details["runtime"] = f"{m.group(1)} min"
                break

        # Cast: find text after "Starring:"
        for text in soup.stripped_strings:
            if "starring" in text.lower():
                rest = text.split(":", 1)[-1].strip()
                if len(rest) > 3:
                    details["cast"] = rest
                break

        # Synopsis
        for p in soup.find_all("p"):
            text = p.get_text(strip=True)
            if len(text) > MIN_SYNOPSIS_LENGTH and not any(
                t in text.lower() for t in SYNOPSIS_SKIP_TERMS
            ):
                details["synopsis"] = text
                break

        if not details["synopsis"]:
            for div in soup.find_all("div"):
                text = div.get_text(strip=True)
                if MIN_SYNOPSIS_LENGTH < len(text) < MAX_SYNOPSIS_LENGTH and not any(
                    t in text.lower() for t in SYNOPSIS_SKIP_TERMS
                ):
                    details["synopsis"] = text
                    break

        logger.info(
            "Film details: runtime=%s cast=%s synopsis_len=%d",
            details["runtime"],
            bool(details["cast"]),
            len(details["synopsis"]),
        )

        with _film_cache_lock:
            cache[base_url] = {**details, "cached_at": datetime.now().isoformat()}

    except requests.RequestException as e:
        logger.warning("Network error for %s: %s", film_url, e)
    except Exception as e:
        logger.warning("Error fetching %s: %s", film_url, e)

    return details


def extract_films(
    url: str,
    cinema_name: str,
    cache: Dict[str, dict],
    session: Optional[requests.Session] = None,
) -> List[Tuple[date, str, str, str, Dict[str, str]]]:
    """Scrape film listing from a cinema's coming-soon page."""
    logger.info("Scraping: %s (%s)", url, cinema_name)
    resp = fetch_with_retries(url, session=session)
    soup = BeautifulSoup(resp.text, "html.parser")

    films: List[Tuple[date, str, str, str, Dict[str, str]]] = []
    seen: set = set()

    for td in soup.find_all("div", class_="times"):
        li = td.parent
        if not li:
            continue

        h2 = li.find("h2")
        if not h2:
            continue

        raw_title = h2.get_text(strip=True)
        # Extract BBFC from cert span (e.g., <span class="cert cert--12A">)
        cert_span = li.select_one(".cert")
        bbfc_rating = ""
        if cert_span:
            for cls in cert_span.get("class", []):
                if cls.startswith("cert--"):
                    bbfc_rating = cls.replace("cert--", "").upper()
                    if bbfc_rating == "TBC":
                        bbfc_rating = ""
                    break
        title = TITLE_CLEAN_RE.sub("", raw_title)

        p = td.find("p")
        if not p:
            continue

        release_date = parse_date(p.get_text(strip=True))

        film_url = ""
        a = li.find("a", href=FILM_LINK_RE)
        if a:
            film_url = a.get("href", "")

        if release_date and title:
            key = (release_date, title, cinema_name, film_url)
            if key not in seen:
                clean_title, screening = extract_screening_label(title)
                film_details = fetch_film_details(film_url, cache, session)
                film_details["bbfc"] = bbfc_rating
                film_details["screening"] = screening
                films.append((release_date, clean_title or title, cinema_name, film_url, film_details))
                seen.add(key)
                logger.info("  %s - %s (%s)", title, release_date, cinema_name)

    return films


def scrape_cinema_whats_on(
    cinema_id: str,
    cinema_name: str,
    session: Optional[requests.Session] = None,
) -> List[Dict[str, Any]]:
    """Scrape a cinema's whats-on page for films with full multi-date showtime schedules."""
    url = CINEMAS[cinema_id]["whats_on_url"]
    logger.info("Scraping whats-on: %s (%s)", url, cinema_name)
    resp = fetch_with_retries(url, session=session)
    soup = BeautifulSoup(resp.text, "html.parser")

    films: List[Dict[str, Any]] = []
    film_items = soup.select("li.js-film") or soup.select("div[data-film]")
    if not film_items:
        logger.warning("No js-film nodes on whats-on page for %s", cinema_name)
        return films

    today_scrape = date.today()
    tag_names = ("Audio Description", "Subtitles", "Wheelchair access", "Silver Screen", "2D", "3D",
                 "Event cinema", "Strobe Light warning", "Parent & Baby", "Autism Friendly", "Kids Club")

    for li in film_items:
        film_a = li.find("a", href=lambda h: h and "/film/" in h)
        if not film_a:
            continue
        href = film_a.get("href", "")
        film_url = href if href.startswith("http") else WTW_BASE_URL + href

        title_elem = li.find("h2")
        title = (title_elem.get_text(strip=True) if title_elem else film_a.get_text(strip=True) or "").replace("–", "-")
        title = TITLE_CLEAN_RE.sub("", title)
        if not title:
            continue
        if any(skip in title.lower() for skip in ("looking ahead", "gaming", "private cinema", "onscreen magazine", "book the cinema")):
            continue

        showtimes: List[Dict[str, Any]] = []
        dates_ul = li.find("ul", class_="dates")
        if dates_ul:
            for date_li in dates_ul.find_all("li", class_="js-performance-date"):
                date_text = date_li.get_text(separator=" ", strip=True)
                parsed_date = parse_uk_date(date_text, today_scrape)
                if not parsed_date:
                    continue
                for perf in date_li.find_all("li", class_="js-performance"):
                    perf_text = perf.get_text(separator=" ", strip=True)
                    time_m = re.search(r"(\d{1,2}:\d{2})", perf_text)
                    time_str = time_m.group(1) if time_m else ""
                    if not time_str:
                        continue
                    screen = 1
                    sm = re.search(r"Screen:\s*(\d+)", perf_text, re.IGNORECASE)
                    if sm:
                        screen = int(sm.group(1))
                    tags = [t for t in tag_names if t.lower() in perf_text.lower()]
                    if not tags and "2D" in perf_text:
                        tags = ["2D"]
                    book_a = perf.find("a", href=lambda h: h and "performance=" in (h or ""))
                    booking_url = ""
                    if book_a:
                        raw_href = book_a.get("href", "").replace("&#038;", "&")
                        booking_url = raw_href if raw_href.startswith("http") else WTW_BASE_URL + raw_href

                    showtimes.append({
                        "date": parsed_date,
                        "time": time_str,
                        "screen": screen,
                        "booking_url": booking_url,
                        "tags": tags or ["2D"],
                        "cinema_name": cinema_name,
                    })

        if showtimes:
            # Deduplicate by (date, time, screen)
            seen_st = set()
            unique_st = []
            for st in showtimes:
                key = (st["date"], st["time"], st["screen"])
                if key not in seen_st:
                    seen_st.add(key)
                    unique_st.append(st)
            unique_st.sort(key=lambda s: (s["date"], s["time"]))
            films.append({
                "title": title,
                "film_url": film_url,
                "cinema_id": cinema_id,
                "cinema_name": cinema_name,
                "showtimes": unique_st,
            })

    logger.info("  whats-on %s: %d films with showtimes", cinema_name, len(films))
    return films


# ── TMDb enrichment ────────────────────────────────────────────────────────────
def _normalize_title_for_match(title: str) -> str:
    if not title:
        return ""
    return re.sub(r"[\s\-:]+", " ", title.lower()).strip()


def _pick_best_tmdb_result(results: List[Dict], search_title: str, release_year: Optional[int] = None) -> Optional[Dict]:
    if not results or not search_title:
        return results[0] if results else None
    norm_search = _normalize_title_for_match(search_title)
    if not norm_search:
        return results[0]

    # Exact match on normalized title
    for r in results:
        norm = _normalize_title_for_match(r.get("title") or "")
        if norm == norm_search:
            # Prefer result matching the expected release year
            if release_year and (r.get("release_date") or "").startswith(str(release_year)):
                return r
            return r

    # No exact match - score by substring + release year proximity
    best, best_score = None, -1
    for r in results:
        title = (r.get("title") or "").strip()
        norm = _normalize_title_for_match(title)
        # Substring match
        score = 90 if norm_search in norm else (50 if norm in norm_search else 0)
        # Bonus for matching release year
        if release_year and (r.get("release_date") or "").startswith(str(release_year)):
            score += 30
        if score == 0:
            try:
                y = int((r.get("release_date") or "")[:4] or 0)
                score = 60 if y >= 2024 else (40 if y >= 2020 else 10)
            except ValueError:
                score = 10
        if score > best_score:
            best_score, best = score, r
    return best if best_score >= 30 else None


def enrich_film_tmdb(
    film_title: str,
    film_url: str,
    api_key: str,
    cache: Dict[str, dict],
    session: Optional[requests.Session] = None,
) -> Dict[str, Any]:
    """Fetch TMDb metadata for a film. Returns genres, rating, director, cast, poster_url, trailer_url."""
    search_title = TMDB_SEARCH_STRIP_RE.sub("", TITLE_CLEAN_RE.sub("", film_title)).strip()
    # Apply screening-suffix title cleaning
    for pattern, replacement in TITLE_CLEAN_PATTERNS:
        search_title = pattern.sub(replacement, search_title).strip()
    if not search_title:
        return {}
    # Skip TMDb enrichment for non-film live events
    tl = search_title.lower()
    if any(skip in tl for skip in SKIP_TMDB_TERMS):
        return {}
    key = _tmdb_cache_key(film_title)

    with _tmdb_cache_lock:
        if key in cache:
            entry = cache[key]
            va = entry.get("vote_average")
            if va is not None and float(va) == 0.0:
                va = None
            return {
                "overview": entry.get("overview") or "",
                "genres": entry.get("genres") or [],
                "vote_average": va,
                "director": entry.get("director") or "",
                "cast": entry.get("cast") or "",
                "poster_url": entry.get("poster_url") or "",
                "trailer_url": entry.get("trailer_url") or "",
                "imdb_id": entry.get("imdb_id") or "",
            }

    s = session or _session()
    time.sleep(TMDB_DELAY_SEC)
    # Rate-limit-aware GET helper for TMDb
    def _tmdb_get(url: str, params: dict, max_tries: int = 3) -> dict:
        for attempt in range(max_tries):
            resp = s.get(url, params=params, timeout=10)
            if resp.status_code == 429:
                retry_after = float(resp.headers.get("Retry-After", 2))
                logger.warning("TMDb rate-limited, waiting %.1fs", retry_after)
                time.sleep(retry_after)
                continue
            if 500 <= resp.status_code < 600 and attempt < max_tries - 1:
                time.sleep(2 ** attempt)
                continue
            resp.raise_for_status()
            return resp.json()
        safe_url = re.sub(r"api_key=[^&]+", "api_key=***", url)
        raise RuntimeError(f"TMDb request failed: {safe_url}")
    empty_result = {
        "overview": "", "genres": [], "vote_average": None,
        "director": "", "cast": "",
        "poster_url": "", "poster_large_url": "", "backdrop_url": "",
        "runtime": "", "trailer_url": "", "imdb_id": "",
        "cached_at": datetime.now().isoformat(),
    }

    try:
        sr = _tmdb_get(
            "https://api.themoviedb.org/3/search/movie",
            {"api_key": api_key, "query": search_title, "language": "en-GB"},
        )
        results = (sr.get("results") or [])

        chosen = _pick_best_tmdb_result(results, search_title)

        # Progressive fallback: strip unknown screening suffixes word by word.
        # Cinema site may add "Toddler Cinema", "Kids Club", "Special Event" etc.
        # that our known-pattern list doesn't catch. Drop up to 3 trailing
        # words and re-search until TMDb gives a solid match.
        if not chosen:
            words = search_title.split()
            max_drop = min(6, len(words) - 1)
            for drop in range(1, max_drop + 1):
                shorter = " ".join(words[:-drop]).rstrip(":,-.&")
                if not shorter or len(shorter) < 2:
                    continue
                logger.info("TMDb fallback: trying %r → %r", search_title, shorter)
                time.sleep(TMDB_DELAY_SEC)
                sr2 = _tmdb_get(
                    "https://api.themoviedb.org/3/search/movie",
                    {"api_key": api_key, "query": shorter, "language": "en-GB"},
                )
                r2 = (sr2.get("results") or [])
                candidate = _pick_best_tmdb_result(r2, shorter)
                if candidate and candidate.get("id"):
                    chosen = candidate
                    break

        if not chosen or not chosen.get("id"):
            with _tmdb_cache_lock:
                cache[key] = empty_result
            return {}

        time.sleep(TMDB_DELAY_SEC)
        movie = _tmdb_get(
            f"https://api.themoviedb.org/3/movie/{chosen['id']}",
            {"api_key": api_key, "append_to_response": "videos,credits", "language": "en-GB"},
        )

        genres = [g["name"].strip() for g in (movie.get("genres") or []) if g.get("name")]
        if not genres:
            gids = chosen.get("genre_ids") or []
            genres = [TMDB_GENRE_MAP[g] for g in gids if g in TMDB_GENRE_MAP]

        overview = (movie.get("overview") or "").strip()
        vote_average = movie.get("vote_average")
        vote_count = movie.get("vote_count") or 0

        credits = movie.get("credits") or {}
        directors = [
            c["name"].strip()
            for c in (credits.get("crew") or [])
            if (c.get("job") or "").strip() == "Director"
        ]
        director_str = ", ".join(list(dict.fromkeys(directors))[:3])
        cast_names = [
            c["name"].strip()
            for c in (credits.get("cast") or [])[:6]
            if c.get("name")
        ]
        cast_str = ", ".join(cast_names)

        poster_path = (movie.get("poster_path") or "").lstrip("/")
        poster_url = f"https://image.tmdb.org/t/p/w500/{poster_path}" if poster_path else ""
        poster_large_url = f"https://image.tmdb.org/t/p/w780/{poster_path}" if poster_path else ""

        backdrop_path = (movie.get("backdrop_path") or "").lstrip("/")
        backdrop_url = f"https://image.tmdb.org/t/p/w780/{backdrop_path}" if backdrop_path else ""

        runtime_tmdb = movie.get("runtime") or 0

        trailer_key = None
        for v in (movie.get("videos", {}).get("results") or []):
            if v.get("site") == "YouTube":
                vtype = v.get("type", "").lower()
                yt_key = v.get("key")
                if not yt_key:
                    continue
                if vtype == "trailer":
                    trailer_key = yt_key
                    break
                if vtype == "teaser" and trailer_key is None:
                    trailer_key = yt_key
        trailer_url = f"https://www.youtube.com/watch?v={trailer_key}" if trailer_key else ""

        imdb_id = movie.get("imdb_id") or ""

        result = {
            "overview": overview,
            "genres": genres,
            "vote_average": vote_average if vote_count > 0 else None,
            "director": director_str,
            "cast": cast_str,
            "poster_url": poster_url,
            "poster_large_url": poster_large_url,
            "backdrop_url": backdrop_url,
            "runtime": f"{runtime_tmdb} min" if runtime_tmdb > 1 else "",
            "trailer_url": trailer_url,
            "imdb_id": imdb_id,
        }
        with _tmdb_cache_lock:
            cache[key] = {**result, "cached_at": datetime.now().isoformat()}
        return result
    except Exception as e:
        logger.warning("TMDb enrich failed for '%s': %s", search_title, e)
        with _tmdb_cache_lock:
            cache[key] = empty_result
        return {}


# ── iCalendar output ───────────────────────────────────────────────────────────
def _format_runtime_display(runtime_str: str) -> str:
    """'119 min' -> '2h 1min'; '45 min' -> '45 min'; skip known placeholders."""
    if not runtime_str or not isinstance(runtime_str, str):
        return ""
    m = re.search(r"(\d+)", runtime_str)
    if not m:
        return runtime_str.strip()
    minutes = int(m.group(1))
    # Skip obvious placeholders (1 min is not a real runtime)
    if minutes <= 1:
        return ""
    if minutes >= 60:
        h, mins = divmod(minutes, 60)
        return f"{h}h {mins}min" if mins else f"{h}h"
    return f"{minutes} min"


def _stars_from_rating(vote_average: Any) -> str:
    """Convert 0–10 TMDb rating to 5-star unicode string."""
    if vote_average is None:
        return ""
    try:
        v = float(vote_average)
    except (TypeError, ValueError):
        return ""
    if v <= 0 or v > 10:
        return ""
    full = min(5, round(v * 0.5))
    return "★" * full + "☆" * (5 - full)


def _cast_clean(cast_str: str) -> str:
    """Reduce cast string to comma-separated names, max 6."""
    if not cast_str or not isinstance(cast_str, str):
        return ""
    # If it's already clean TMDb format (just names, no parens), return as-is
    if "(" not in cast_str:
        return cast_str if cast_str.count(",") < 6 else ", ".join(cast_str.split(",")[:6])

    names = []
    for part in cast_str.split(","):
        part = part.strip()
        if not part:
            continue
        m = re.match(r"^([^(]+)(?:\s*\([^)]*\))?\s*$", part)
        if m:
            name = m.group(1).strip()
            if name and name not in names:
                names.append(name)
        elif part not in names:
            names.append(part)
        if len(names) >= 6:
            break
    return ", ".join(names[:6])


def escape_and_fold_ical_text(text: str, prefix: str = "") -> str:
    """Escape and RFC 5545 line-fold iCalendar text values."""
    escaped = text.replace("\\", "\\\\").replace(";", "\\;").replace(",", "\\,").replace("\n", "\\n")
    line = prefix + escaped
    if len(line) <= ICAL_LINE_LENGTH:
        return line
    parts = [line[:ICAL_LINE_LENGTH]]
    remain = line[ICAL_LINE_LENGTH:]
    while remain:
        parts.append(" " + remain[:ICAL_LINE_LENGTH - 1])
        remain = remain[ICAL_LINE_LENGTH - 1:]
    return ICAL_NEWLINE.join(parts)


def _make_alarm(alarm: Dict[str, Any], release_date: date) -> str:
    """Generate a VALARM component. Supports days_before (absolute) and hours_before (relative)."""
    if "hours_before" in alarm:
        hours = alarm["hours_before"]
        trigger = f"PT{abs(hours)}H" if hours < 0 else f"-PT{hours}H"
        trigger_line = f"TRIGGER:{trigger}"
    else:
        t = alarm.get("time", NOTIFICATION_TIME)
        try:
            hh, mm = map(int, t.split(":"))
        except (ValueError, AttributeError):
            hh, mm = 9, 0
        days = alarm.get("days_before", 1)
        trigger_dt = datetime.combine(release_date, datetime.min.time().replace(hour=hh, minute=mm))
        trigger_dt -= timedelta(days=days)
        trigger = trigger_dt.strftime("%Y%m%dT%H%M%S")
        trigger_line = f"TRIGGER;VALUE=DATE-TIME:{trigger}"
    return ICAL_NEWLINE.join([
        "BEGIN:VALARM",
        "ACTION:DISPLAY",
        f"DESCRIPTION:{alarm.get('description', 'Film Release Reminder')}",
        trigger_line,
        "END:VALARM",
        "",
    ])


def make_ics_event(
    release_date: date,
    film_title: str,
    cinema_name: str,
    film_url: str = "",
    film_details: Optional[Dict[str, Any]] = None,
) -> str:
    """Build a single VEVENT iCalendar block."""
    dtend = release_date + timedelta(days=1)
    uid_seed = f"{release_date.isoformat()}|{film_title}|{cinema_name}|{film_url or ''}"
    uid = f"{hashlib.sha1(uid_seed.encode()).hexdigest()}@wtw-cinemas"
    dtstamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    details = film_details or {}

    runtime_display = _format_runtime_display(details.get("runtime") or "")

    # Layout B if TMDb data present
    v = details.get("vote_average")
    has_tmdb = bool(
        details.get("genres") or details.get("overview")
        or (v is not None and isinstance(v, (int, float)))
    )

    parts = [f"{film_title} ({runtime_display})" if runtime_display else film_title]

    if has_tmdb:
        stars = _stars_from_rating(v) if v is not None else ""
        if stars:
            parts.append(stars)
        genres = details.get("genres")
        if genres:
            gs = ", ".join(str(g).strip() for g in (genres if isinstance(genres, list) else [genres]) if g)
            if gs:
                parts.append(gs)

    # Synopsis / overview
    desc_text = (details.get("overview") or details.get("synopsis") or "").strip()
    if desc_text:
        parts.append(f"\n{desc_text}")

    # Cast
    cast_raw = details.get("cast") or ""
    cast_line = _cast_clean(cast_raw)
    if cast_line:
        parts.append(f"\nStarring: {cast_line}")

    parts.append(f"\nFilm release at WTW Cinemas {cinema_name}")
    if film_url:
        parts.append("Book tickets: " + film_url)
    film_slug = _tmdb_cache_key(film_title)
    parts.append(f"\nFilm details: https://evenwebb.github.io/wtw-cinemas/films/{film_slug}.html")

    description = "\n".join(parts)

    lines = [
        "BEGIN:VEVENT",
        f"UID:{uid}",
        f"DTSTAMP:{dtstamp}",
        f"DTSTART;VALUE=DATE:{release_date.strftime('%Y%m%d')}",
        f"DTEND;VALUE=DATE:{dtend.strftime('%Y%m%d')}",
        escape_and_fold_ical_text(f"{film_title} @ WTW {cinema_name}", "SUMMARY:"),
        escape_and_fold_ical_text(description, "DESCRIPTION:"),
        escape_and_fold_ical_text(f"WTW Cinemas {cinema_name}", "LOCATION:"),
    ]
    if film_url:
        lines.append(escape_and_fold_ical_text(film_url, "URL:"))
    if NOTIFICATIONS.get("enabled") and NOTIFICATIONS.get("alarms"):
        for alarm in NOTIFICATIONS["alarms"]:
            lines.append(_make_alarm(alarm, release_date).rstrip(ICAL_NEWLINE))
    sequence = _get_ics_sequence(film_title, cinema_name, release_date, film_url)
    lines.append(f"SEQUENCE:{sequence}")
    lines.append("END:VEVENT")
    return ICAL_NEWLINE.join(lines) + ICAL_NEWLINE


# ── Dynamic SEQUENCE management (#3) ──────────────────────────────────────────
_SEQ_STATE_FILE = ".ics_sequence.json"
_seq_state_cache: Optional[Dict[str, dict]] = None


def _load_sequence_state() -> Dict[str, dict]:
    global _seq_state_cache
    if _seq_state_cache is not None:
        return _seq_state_cache
    if os.path.exists(_SEQ_STATE_FILE):
        try:
            with open(_SEQ_STATE_FILE, "r") as f:
                _seq_state_cache = json.load(f)
            return _seq_state_cache
        except (json.JSONDecodeError, OSError):
            pass
    _seq_state_cache = {}
    return _seq_state_cache


def _save_sequence_state() -> None:
    if _seq_state_cache is not None:
        Path(_SEQ_STATE_FILE).parent.mkdir(parents=True, exist_ok=True)
        with open(_SEQ_STATE_FILE, "w") as f:
            json.dump(_seq_state_cache, f, indent=2)


def _get_ics_sequence(title: str, cinema: str, release_date: date, url: str = "") -> int:
    """Return SEQUENCE number. Increments when event data changes."""
    fp = hashlib.sha256(f"{title}|{cinema}|{release_date}|{url}".encode()).hexdigest()[:16]
    state = _load_sequence_state()
    key = f"{title}|{cinema}"
    prev = state.get(key)
    if prev and prev.get("fp") == fp:
        return prev.get("seq", 0)
    seq = (prev.get("seq", 0) + 1) if prev else 0
    state[key] = {"fp": fp, "seq": seq}
    _seq_state_cache = state
    return seq


# ── Shared base CSS ─────────────────────────────────────────────────────────────
_SHARED_CSS = """
:root{--bg:#09090d;--surface:#13131c;--surface-2:#1a1a26;--border:rgba(192,132,252,0.18);--text:#e8edf2;--text-muted:#8b9db5;--cyan:#22d3ee;--purple:#c084fc;--accent:#22d3ee;--accent-dim:rgba(34,211,238,0.12);--accent-glow:rgba(34,211,238,0.2);--amber:#f59e0b;--radius:16px;--radius-sm:10px;--transition:0.2s ease}
*,::before,::after{box-sizing:border-box;margin:0;padding:0}
html{scroll-behavior:smooth;scroll-padding-top:2rem}
body{padding-top:42px;font-family:'Space Grotesk',system-ui,sans-serif;background:var(--bg);color:var(--text);line-height:1.7;min-height:100vh;-webkit-font-smoothing:antialiased}
@keyframes pageIn{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:translateY(0)}}
.page{animation:pageIn 0.4s ease-out}
.bg-mesh{position:fixed;inset:0;overflow:hidden;background:radial-gradient(ellipse 80% 60% at 50% -20%,var(--accent-dim) 0%,transparent 50%),radial-gradient(ellipse 50% 40% at 80% 90%,rgba(192,132,252,0.06) 0%,transparent 50%);pointer-events:none;z-index:0}
footer{text-align:center;padding:2.5rem 2rem;color:var(--text-muted);font-size:0.85rem;border-top:1px solid rgba(255,255,255,0.05);margin-top:4rem}
footer a{color:var(--accent);text-decoration:none;font-weight:500}
footer a:hover{color:var(--purple)}
.footer-updated{font-size:0.75rem;opacity:0.4;margin-top:0.75rem}
@media print{body{background:#fff!important;color:#111!important}.bg-mesh,.skip-link,.quick-nav,.map-link,.book-btn{display:none!important}.card,.stat-pill,.featured-film,.now-film,.cinema-table td{background:#fff!important;border:1px solid #ddd!important;box-shadow:none!important;break-inside:avoid}.hero h1{color:#111!important;-webkit-text-fill-color:#111!important;background:none!important}footer{border-top:1px solid #ddd!important}a{color:#111!important}}
"""

# ── HTML index page ────────────────────────────────────────────────────────────
CSS = _SHARED_CSS + """
.skip-link{position:absolute;top:-100px;left:1rem;z-index:100;background:var(--accent);color:var(--bg);padding:0.5rem 1.25rem;border-radius:100px;font-weight:600;text-decoration:none;font-size:0.9rem}
.skip-link:focus{top:1.25rem}
.page{position:relative;z-index:1;max-width:1100px;margin:0 auto;padding:2rem 1rem 4rem}
@media(min-width:640px){.page{padding:3rem 2rem 5rem}}
.quick-nav{display:flex;flex-wrap:wrap;gap:0.5rem;justify-content:center;margin-bottom:2.5rem;padding-bottom:2rem;border-bottom:1px solid var(--border)}
.quick-nav a{padding:0.65rem 1.5rem;border-radius:100px;font-size:0.9rem;font-weight:600;text-decoration:none;color:var(--text);background:var(--surface);border:1px solid var(--border);transition:all var(--transition)}
.quick-nav a:hover,.quick-nav a:focus{color:var(--accent);border-color:var(--accent);background:var(--accent-dim);transform:translateY(-1px);box-shadow:0 4px 12px var(--accent-glow)}
.hero{text-align:center;padding:1.5rem 0 2rem}
@media(min-width:640px){.hero{padding:3rem 0 3.5rem}}
.hero .badge{display:inline-flex;align-items:center;gap:0.5rem;font-size:0.7rem;font-weight:600;letter-spacing:0.15em;text-transform:uppercase;color:var(--accent);background:var(--accent-dim);padding:0.35rem 0.85rem;border-radius:100px;margin-bottom:1rem}
@media(min-width:640px){.hero .badge{font-size:0.75rem;padding:0.4rem 1rem;margin-bottom:1.5rem}}
.hero .badge::before{content:'';width:7px;height:7px;background:var(--accent);border-radius:50%}
@media(prefers-reduced-motion:no-preference){.hero .badge::before{animation:pulse 2s infinite}}
@keyframes pulse{0%,100%{opacity:1}50%{opacity:0.4}}
.hero h1{font-size:clamp(2rem,5.5vw,3.25rem);font-weight:800;letter-spacing:-0.03em;line-height:1.15;margin-bottom:1rem;background:linear-gradient(135deg,var(--cyan) 0%,var(--purple) 100%);-webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text}
.hero .tagline{font-size:1.05rem;color:var(--text-muted);max-width:38rem;margin:0 auto 1.5rem;line-height:1.65}
.hero .hero-stat{display:inline-block;font-family:'JetBrains Mono',monospace;font-size:0.85rem;color:var(--accent);background:var(--accent-dim);padding:0.3rem 0.9rem;border-radius:100px}
.hero-updated{font-size:0.7rem;color:var(--text-muted);margin-top:0.5rem}
.section-label{font-size:0.75rem;font-weight:700;letter-spacing:0.15em;text-transform:uppercase;color:var(--text-muted);margin-bottom:1.25rem;display:flex;align-items:center;gap:0.75rem}
.section-label::after{content:'';flex:1;height:1px;background:var(--border)}
.cinemas{list-style:none;display:grid;grid-template-columns:repeat(2,1fr);gap:0.75rem;margin-bottom:4rem}
@media(min-width:640px){.cinemas{gap:1rem}}
@media(min-width:960px){.cinemas{grid-template-columns:repeat(4,1fr);gap:1.25rem}}
.card{background:var(--surface);border:1px solid var(--border);border-radius:20px;padding:1.75rem;position:relative;overflow:hidden;box-shadow:0 1px 3px rgba(0,0,0,0.3)}
@media(prefers-reduced-motion:no-preference){.card{transition:transform var(--transition),border-color var(--transition),box-shadow var(--transition)}}
.card:hover{border-color:rgba(34,211,238,0.35);transform:translateY(-3px);box-shadow:0 12px 30px rgba(0,0,0,0.5),0 0 0 1px rgba(34,211,238,0.08)}
.card-icon{width:52px;height:52px;background:var(--accent-dim);border-radius:14px;display:flex;align-items:center;justify-content:center;margin:0 auto 1rem;font-size:1.5rem}
.card h2{font-size:1.15rem;font-weight:700;margin-bottom:0.25rem;text-align:center}
.card .meta{font-size:0.85rem;color:var(--text-muted);margin-bottom:1.25rem;text-align:center}
.card .btn{display:inline-flex;align-items:center;justify-content:center;gap:0.5rem;width:100%;padding:0.75rem 1.25rem;background:linear-gradient(135deg,var(--cyan),var(--purple));color:#0a0a10;font-weight:600;font-size:0.9rem;border-radius:12px;text-decoration:none}
@media(prefers-reduced-motion:no-preference){.card .btn{transition:transform var(--transition),box-shadow var(--transition),opacity var(--transition)}}
.card .btn:hover{transform:scale(1.02);box-shadow:0 6px 25px var(--accent-glow)}
.card .btn:active{transform:scale(0.98)}
@media(max-width:579px){.card .btn .btn-text-short{display:inline}.card .btn .btn-text-full{display:none}.card{padding:1.25rem}.card-icon{width:40px;height:40px;font-size:1.25rem;margin-bottom:0.75rem}.card h2{font-size:1rem}.card .meta{font-size:0.8rem;margin-bottom:1rem}.card .btn{padding:0.65rem 1rem;font-size:0.85rem}}
@media(min-width:580px){.card .btn .btn-text-short{display:none}.card .btn .btn-text-full{display:inline}}
.map-link{display:block;text-align:center;margin-top:0.6rem;font-size:0.78rem;color:var(--text-muted);text-decoration:none;transition:color var(--transition)}
.map-link:hover{color:var(--accent)}
.stats-section{margin-bottom:4rem}
.stats-section h2{font-size:1.15rem;font-weight:700;margin-bottom:0.75rem}
.stats-intro{font-size:0.9rem;color:var(--text-muted);margin-bottom:1.5rem;max-width:40rem}
.stats-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:0.75rem}
.stats-group-title{font-size:0.8rem;font-weight:700;color:var(--text-muted);text-transform:uppercase;letter-spacing:0.08em;margin:1.75rem 0 0.75rem}
.stat-pill{background:var(--surface);border:1px solid var(--border);border-radius:14px;padding:1.15rem;text-align:center}
@media(prefers-reduced-motion:no-preference){.stat-pill{transition:border-color var(--transition),background var(--transition)}}
.stat-pill:hover{border-color:rgba(34,211,238,0.25);background:var(--surface-2)}
.stat-pill .value{font-size:1.75rem;font-weight:800;color:var(--accent);letter-spacing:-0.02em;line-height:1.2;font-family:'JetBrains Mono',monospace}
.stat-pill .label{font-size:0.75rem;color:var(--text-muted);margin-top:0.4rem;display:block}
.howto-section{margin-bottom:3rem}
.howto-section h2{font-size:1.15rem;font-weight:700;margin-bottom:1rem}
.accordion{border:1px solid var(--border);border-radius:14px;overflow:hidden}
.accordion-item{border-bottom:1px solid var(--border)}
.accordion-item:last-child{border-bottom:none}
.accordion-trigger{width:100%;display:flex;align-items:center;justify-content:space-between;padding:1rem 1.25rem;background:var(--surface);border:none;color:var(--text);font-family:inherit;font-size:0.95rem;font-weight:600;cursor:pointer;text-align:left;-webkit-tap-highlight-color:transparent;min-height:48px}
.accordion-trigger:hover{background:var(--surface-2)}
.accordion-trigger:active{background:var(--accent-dim)}
.accordion-trigger::after{content:'+';font-size:1.35rem;font-weight:300;color:var(--accent);line-height:1}
@media(prefers-reduced-motion:no-preference){.accordion-trigger::after{transition:transform 0.25s ease}}
.accordion-item.open .accordion-trigger::after{transform:rotate(45deg)}
.accordion-panel{overflow:hidden;max-height:0}
@media(prefers-reduced-motion:no-preference){.accordion-panel{transition:max-height 0.3s ease}}
.accordion-content{padding:1rem 1.25rem 1.25rem;background:var(--surface);font-size:0.9rem;color:var(--text-muted);line-height:1.7}
.now-showing{margin-bottom:3.5rem}
.now-showing .section-header{display:flex;align-items:center;justify-content:space-between;margin-bottom:1rem;flex-wrap:wrap;gap:0.5rem}
.now-showing h2{font-size:1.15rem;font-weight:700;color:var(--accent)}
.now-showing .new-badge{font-size:0.7rem;font-weight:700;text-transform:uppercase;letter-spacing:0.1em;background:var(--accent-dim);color:var(--accent);padding:0.25rem 0.65rem;border-radius:100px}
.now-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(170px,1fr));gap:0.75rem}
.now-film{background:var(--surface);border:1px solid var(--border);border-radius:12px;padding:0.9rem 1rem;transition:border-color var(--transition)}
.now-film:hover{border-color:rgba(34,211,238,0.3)}
.now-film .date{font-size:0.7rem;color:var(--accent);font-weight:600;margin-bottom:0.2rem;display:block;text-transform:uppercase;letter-spacing:0.05em}
.now-film a{color:var(--text);text-decoration:none;font-weight:600;font-size:0.9rem;line-height:1.35}
.now-film a:hover{color:var(--accent)}
.film-section{margin-bottom:3.5rem}
.film-section .section-header{display:flex;align-items:center;justify-content:space-between;margin-bottom:1.25rem;flex-wrap:wrap;gap:0.75rem}
.film-section .section-header h2{font-size:1.2rem;font-weight:700;color:var(--accent)}
.film-section .section-header .count{font-size:0.85rem;color:var(--text-muted);background:var(--surface);padding:0.3rem 0.8rem;border-radius:100px;font-weight:500}
.film-browse-grid{display:flex;flex-direction:column;gap:1.25rem}
/* Now Showing poster grid */
.ns-poster-grid{display:grid;grid-template-columns:repeat(2,1fr);gap:0.75rem}
@media(min-width:480px){.ns-poster-grid{grid-template-columns:repeat(3,1fr);gap:1rem}}
@media(min-width:768px){.ns-poster-grid{grid-template-columns:repeat(4,1fr);gap:1.25rem}}
@media(min-width:1024px){.ns-poster-grid{grid-template-columns:repeat(5,1fr);gap:1.5rem}}
.ns-poster-card{display:block;text-decoration:none;border-radius:12px;overflow:hidden;transition:transform 0.2s,box-shadow 0.2s;background:var(--surface);border:1px solid var(--border)}
.ns-poster-card:hover{transform:translateY(-4px);box-shadow:0 8px 25px rgba(0,0,0,0.4);border-color:var(--accent)}
.ns-poster-wrap{position:relative;aspect-ratio:2/3;overflow:hidden;background:var(--surface-2)}
.ns-poster-wrap img{width:100%;height:100%;object-fit:cover;display:block}
.ns-poster-wrap .ns-no-poster{width:100%;height:100%;display:flex;align-items:center;justify-content:center;text-align:center;font-size:0.75rem;color:var(--text-muted);padding:0.5rem;background:linear-gradient(135deg,var(--accent-dim),rgba(192,132,252,0.06))}
.ns-title{display:block;padding:0.5rem 0.6rem;font-size:0.78rem;font-weight:600;color:var(--text);line-height:1.3;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.ns-event-tag{display:block;font-size:0.62rem;font-weight:700;text-transform:uppercase;letter-spacing:0.06em;padding:0.1rem 0.6rem 0.4rem;text-align:center}
.ns-event-tag.rbo{color:#f87171}.ns-event-tag.nt-live{color:var(--accent)}.ns-event-tag.toddler-cinema{color:var(--amber)}.ns-event-tag.double-bill{color:var(--purple)}.ns-event-tag.q-a{color:#fb923c}
@media(max-width:479px){.ns-title{padding:0.4rem;font-size:0.72rem}}
.film-card-full{display:grid;grid-template-columns:90px 1fr;gap:1rem;background:var(--surface);border:1px solid var(--border);border-radius:14px;padding:1.25rem;transition:border-color var(--transition),transform var(--transition)}
@media(min-width:480px){.film-card-full{grid-template-columns:130px 1fr;gap:1.5rem;padding:1.5rem}}
@media(min-width:768px){.film-card-full{grid-template-columns:170px 1fr;gap:1.75rem;padding:1.75rem}}
.film-card-full:hover{border-color:rgba(34,211,238,0.35);transform:translateY(-2px);box-shadow:0 8px 25px rgba(0,0,0,0.3)}
.film-card-full .fc-poster{width:90px;height:135px;flex-shrink:0;border-radius:10px;overflow:hidden;background:var(--surface-2)}
@media(min-width:480px){.film-card-full .fc-poster{width:130px;height:195px}}
@media(min-width:768px){.film-card-full .fc-poster{width:170px;height:255px}}
.film-card-full .fc-poster img{width:100%;height:100%;object-fit:cover;display:block}
.film-card-full .fc-poster .no-poster-sm{width:100%;height:100%;display:flex;align-items:center;justify-content:center;background:linear-gradient(135deg,var(--accent-dim),rgba(192,132,252,0.08));border-radius:10px;font-size:2.5rem}
.film-card-full .fc-info{display:flex;flex-direction:column;gap:0.5rem;min-width:0}
.film-card-full .fc-info h3{font-size:1.1rem;font-weight:700;line-height:1.3;margin:0;display:flex;align-items:center;gap:0.5rem;flex-wrap:wrap}
@media(min-width:768px){.film-card-full .fc-info h3{font-size:1.2rem}}
.film-card-full .fc-info h3 a{color:var(--text);text-decoration:none}
.film-card-full .fc-info h3 a:hover{color:var(--accent)}
.new-badge{display:inline-block;font-size:0.62rem;font-weight:700;text-transform:uppercase;letter-spacing:0.06em;padding:0.15rem 0.45rem;border-radius:100px;background:linear-gradient(135deg,var(--amber),#f59e0b);color:#0a0a10;vertical-align:middle;margin-left:0.3rem}
.screening-badge{display:inline-block;font-size:0.62rem;font-weight:600;text-transform:uppercase;letter-spacing:0.04em;padding:0.15rem 0.5rem;border-radius:100px;background:rgba(192,132,252,0.15);color:var(--purple);vertical-align:middle;margin-left:0.3rem}
.fc-screening-banner{font-size:0.7rem;font-weight:700;text-transform:uppercase;letter-spacing:0.08em;padding:0.35rem 1rem;margin:-1.25rem -1.25rem 0.75rem -1.25rem;border-radius:12px 12px 0 0;text-align:center}
.fc-screening-banner.rbo{background:linear-gradient(135deg,rgba(248,113,113,0.2),rgba(248,113,113,0.06));color:#f87171;border-bottom:1px solid rgba(248,113,113,0.2)}
.fc-screening-banner.nt-live{background:linear-gradient(135deg,rgba(34,211,238,0.15),rgba(34,211,238,0.04));color:var(--accent);border-bottom:1px solid rgba(34,211,238,0.2)}
.fc-screening-banner.toddler-cinema{background:linear-gradient(135deg,rgba(251,191,36,0.18),rgba(251,191,36,0.05));color:var(--amber);border-bottom:1px solid rgba(251,191,36,0.2)}
.fc-screening-banner.double-bill{background:linear-gradient(135deg,rgba(192,132,252,0.18),rgba(192,132,252,0.05));color:var(--purple);border-bottom:1px solid rgba(192,132,252,0.2)}
.fc-screening-banner.q-a{background:linear-gradient(135deg,rgba(251,146,60,0.2),rgba(251,146,60,0.06));color:#fb923c;border-bottom:1px solid rgba(251,146,60,0.2)}
@media(min-width:480px){.fc-screening-banner{margin:-1.5rem -1.5rem 0.75rem -1.5rem}}
@media(min-width:768px){.fc-screening-banner{margin:-1.75rem -1.75rem 0.75rem -1.75rem}}
.film-card-full .fc-meta{display:flex;flex-wrap:wrap;gap:0.35rem 0.85rem;font-size:0.82rem;color:var(--text-muted);align-items:center}
.film-card-full .fc-meta .stars{color:var(--amber);font-size:0.82rem;letter-spacing:0.05em}
.film-card-full .fc-meta .genres{color:var(--purple);font-weight:500}
.film-card-full .fc-meta .cert-badge{display:inline-block;font-size:0.7rem;font-weight:700;padding:0.1rem 0.4rem;border-radius:3px;background:rgba(34,211,238,0.12);color:var(--accent)}
.film-card-full .fc-meta .showing-date{color:var(--accent);font-weight:600}
.film-card-full .fc-synopsis{font-size:0.88rem;color:var(--text-muted);line-height:1.6;margin-top:0.25rem}
@media(max-width:479px){.film-card-full .fc-synopsis{-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden;display:-webkit-box}}
.film-card-full .fc-synopsis a{color:var(--accent);text-decoration:none;font-weight:500;white-space:nowrap}
.film-card-full .fc-showings{display:flex;flex-direction:column;gap:0.35rem;padding-top:0.6rem;border-top:1px solid var(--border);margin-top:0.25rem}
@media(min-width:768px){.film-card-full .fc-showings{padding-top:0.75rem;margin-top:0.5rem}}
.film-card-full .showing-row{display:flex;align-items:baseline;gap:0.6rem;flex-wrap:wrap}
.film-card-full .showing-date{font-size:0.75rem;font-weight:700;color:var(--accent);white-space:nowrap;min-width:5.5rem;text-transform:uppercase;letter-spacing:0.04em}
.film-card-full .showing-cinemas{display:flex;flex-wrap:wrap;gap:0.25rem 0.1rem}
.film-card-full .showing-cinema-link{font-size:0.78rem;font-weight:500;color:var(--text-muted);text-decoration:none;padding:0.2rem 0.5rem;border-radius:6px;transition:all var(--transition)}
.film-card-full .showing-cinema-link:hover{color:var(--accent);background:var(--accent-dim)}
.film-card-full .showing-cinema-link::after{content:" ·";color:var(--border);margin-left:0.25rem}
.film-card-full .showing-cinema-link:last-child::after{content:""}
.cinema-filter{display:flex;flex-wrap:wrap;gap:0.4rem;justify-content:center;margin-bottom:2.5rem}
.cinema-filter button{font-family:inherit;font-size:0.82rem;font-weight:500;padding:0.45rem 1rem;border-radius:100px;border:1px solid var(--border);background:var(--surface);color:var(--text-muted);cursor:pointer;transition:all var(--transition)}
.cinema-filter button:hover{color:var(--accent);border-color:var(--accent)}
.cinema-filter button.active{background:var(--accent-dim);color:var(--accent);border-color:var(--accent)}
.cinema-filter button.nearest{border-color:var(--amber);color:var(--amber);background:rgba(251,191,36,0.1)}
.cinema-filter button.nearest::after{content:" ★"}
.view-toggle-btn{font-family:inherit;font-size:0.78rem;font-weight:500;padding:0.35rem 0.85rem;border-radius:100px;border:1px solid var(--border);background:var(--surface);color:var(--text-muted);cursor:pointer;transition:all var(--transition)}
.view-toggle-btn:hover{color:var(--accent);border-color:var(--accent)}
/* Now Showing card/list toggle */
#now-showing-live.poster-view .ns-poster-grid{display:grid}
#now-showing-live.poster-view .ns-list-grid{display:none}
#now-showing-live:not(.poster-view) .ns-poster-grid{display:none}
#now-showing-live:not(.poster-view) .ns-list-grid{display:flex;flex-direction:column;gap:0.5rem}
.ns-list-card{display:flex;align-items:center;gap:0.75rem;flex-wrap:wrap;padding:0.85rem 1rem;background:var(--surface);border:1px solid var(--border);border-radius:12px;text-decoration:none;transition:border-color var(--transition)}
.ns-list-card:hover{border-color:var(--accent)}
.ns-list-title{font-weight:600;color:var(--text);font-size:0.92rem;flex:1;min-width:140px}
.ns-list-cinemas{font-size:0.78rem;color:var(--text-muted)}
.ns-list-next{font-size:0.78rem;color:var(--accent);font-weight:500;margin-left:auto}
/* Coming Soon poster toggle */
#coming-soon.poster-view .film-browse-grid{display:grid;grid-template-columns:repeat(2,1fr);gap:0.75rem}
@media(min-width:480px){#coming-soon.poster-view .film-browse-grid{grid-template-columns:repeat(3,1fr);gap:1rem}}
@media(min-width:768px){#coming-soon.poster-view .film-browse-grid{grid-template-columns:repeat(4,1fr);gap:1.25rem}}
#coming-soon.poster-view .film-card-full{display:block;padding:0;border:none;background:none}
#coming-soon.poster-view .film-card-full:hover{transform:none;box-shadow:none}
#coming-soon.poster-view .fc-poster{width:100%;height:auto;aspect-ratio:2/3;border-radius:12px}
#coming-soon.poster-view .fc-info{display:none}
#coming-soon.poster-view .fc-poster img{border-radius:12px}
/* Calendar promo banner */
.calendar-promo{display:flex;align-items:center;justify-content:center;gap:0.5rem;padding:0.55rem 1rem;background:linear-gradient(135deg,rgba(34,211,238,0.18),rgba(192,132,252,0.14));border-bottom:1px solid rgba(34,211,238,0.25);text-decoration:none;margin:0;position:fixed;top:0;left:0;right:0;z-index:50;backdrop-filter:blur(12px);-webkit-backdrop-filter:blur(12px);border-radius:0}
.calendar-promo:hover{border-bottom-color:var(--accent);box-shadow:0 2px 15px var(--accent-glow)}
.promo-icon{font-size:1.2rem;flex-shrink:0}
.promo-text{font-weight:500;color:var(--text);flex:1;text-align:center}
.promo-text-full{font-size:0.88rem}
.promo-text-short{font-size:0.82rem;display:none}
.promo-cta{font-size:0.72rem;font-weight:600;color:#0a0a10;background:linear-gradient(135deg,var(--cyan),var(--purple));padding:0.35rem 0.85rem;border-radius:100px;white-space:nowrap;animation:bounce-down 1.5s infinite;flex-shrink:0}
@keyframes bounce-down{0%,100%{transform:translateY(0)}50%{transform:translateY(3px)}}
@media(max-width:600px){.calendar-promo{padding:0.45rem 0.75rem;gap:0.4rem}.promo-text-full{display:none}.promo-text-short{display:inline}.promo-cta{font-size:0.68rem;padding:0.3rem 0.7rem}}
/* Calendar CTA section */
.calendar-cta{background:linear-gradient(160deg,rgba(34,211,238,0.08) 0%,rgba(192,132,252,0.1) 50%,rgba(34,211,238,0.04) 100%);border:1px solid rgba(34,211,238,0.2);border-radius:18px;padding:1.5rem;text-align:center;margin:3rem 0 2rem;position:relative;overflow:hidden}
.calendar-cta::before{content:'';position:absolute;top:0;left:0;right:0;height:2px;background:linear-gradient(90deg,transparent,var(--accent),var(--purple),var(--accent),transparent)}
@media(min-width:640px){.calendar-cta{padding:2.5rem;margin:4rem 0 3rem}}
.cta-header{display:flex;align-items:center;gap:1rem;margin-bottom:1.5rem;text-align:left;justify-content:center;flex-wrap:wrap}
@media(min-width:640px){.cta-header{margin-bottom:2rem}}
.cta-icon{font-size:2.5rem;flex-shrink:0}
@media(min-width:640px){.cta-icon{font-size:3rem}}
.calendar-cta h2{font-size:1.15rem;font-weight:800;margin:0 0 0.2rem;background:linear-gradient(135deg,var(--cyan),var(--purple));-webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text}
@media(min-width:640px){.calendar-cta h2{font-size:1.35rem}}
.calendar-cta .cta-header p{font-size:0.82rem;color:var(--text-muted);margin:0;line-height:1.5}
@media(min-width:640px){.calendar-cta .cta-header p{font-size:0.88rem}}
.calendar-cta .cta-buttons{display:grid;grid-template-columns:repeat(2,1fr);gap:0.75rem;max-width:640px;margin:0 auto}
@media(max-width:600px){.calendar-cta .cta-buttons{grid-template-columns:1fr}}
.calendar-cta .cta-cinema-row{display:flex;flex-direction:column;align-items:center;gap:0.5rem;padding:0.75rem;background:var(--surface);border:1px solid var(--border);border-radius:12px}
.cta-cinema-name{font-size:0.85rem;font-weight:600;color:var(--text)}
.cta-url{margin-top:0.25rem;width:100%}
.cta-url-input{width:100%;box-sizing:border-box;padding:0.35rem 0.5rem;font-size:0.7rem;font-family:monospace;background:var(--bg);color:var(--text-muted);border:1px solid var(--border);border-radius:6px;text-align:center}
.cta-url-input:focus{outline:none;border-color:var(--accent)}
.calendar-cta .cta-btn-group{display:flex;gap:0;border-radius:8px;overflow:hidden;border:1px solid var(--border)}
.calendar-cta .cta-btn-group .cta-btn,.calendar-cta .cta-btn-group .google-btn,.calendar-cta .cta-btn-group .ios-btn,.calendar-cta .cta-btn-group .copy-btn{display:inline-flex;align-items:center;justify-content:center;padding:0.45rem 0.75rem;font-weight:600;font-size:0.75rem;text-decoration:none;transition:filter 0.2s,background 0.2s;border:none;border-radius:0;cursor:pointer;font-family:inherit;min-width:48px}
.calendar-cta .cta-btn-group .ios-btn{background:#1a1a2e;color:#fff}
.calendar-cta .cta-btn-group .ios-btn:hover{background:#2a2a4e}
.calendar-cta .cta-btn-group .google-btn{background:#1a1a2e;color:#fff}
.calendar-cta .cta-btn-group .google-btn:hover{background:#2a2a4e}
.calendar-cta .cta-btn-group .copy-btn{background:var(--surface);color:var(--text-muted)}
.calendar-cta .cta-btn-group .copy-btn:hover{color:var(--accent);background:var(--accent-dim)}
.calendar-cta .cta-btn-group .copy-btn.copied{color:#4ade80;background:rgba(74,222,128,0.12)}
.calendar-cta .cta-btn-group .show-btn{background:var(--surface);color:var(--text-muted)}
.calendar-cta .cta-btn-group .show-btn:hover{color:var(--accent);background:var(--accent-dim)}
.cta-howto{margin-top:1.5rem;padding-top:1.25rem;border-top:1px solid var(--border);text-align:left;max-width:500px;margin-left:auto;margin-right:auto}
.cta-howto-title{font-size:0.82rem;font-weight:600;color:var(--text-muted);padding:0.25rem 0;text-align:center}
.cta-howto-content{display:flex;flex-direction:column;gap:0.6rem;padding:0.5rem 0 0}
.cta-howto-item{background:var(--surface);border:1px solid var(--border);border-radius:10px;padding:0.6rem 0.85rem}
.cta-howto-item p{font-size:0.78rem;color:var(--text-muted);margin:0.15rem 0 0;line-height:1.55}
.cta-howto-item p strong{color:var(--text);font-weight:600}
.footer-disclaimer{font-size:0.85rem;margin:0 auto 0.5rem;max-width:36rem;line-height:1.6}
.footer-links{display:flex;flex-wrap:wrap;justify-content:center;gap:0.5rem 1.25rem;margin-bottom:0.75rem;align-items:center}
"""


def _esc(text: Any) -> str:
    """HTML-escape a string for safe insertion into HTML."""
    return html_mod.escape(str(text or ""), quote=True)


def build_index_html(
    enabled_cinemas: Dict[str, dict],
    films_by_cinema: Dict[str, List],
    stats: Optional[Dict[str, int]] = None,
    now_showing_live: Optional[List[Dict[str, Any]]] = None,
    special_events: Optional[List[Dict[str, Any]]] = None,
    new_slugs: Optional[set] = None,
) -> str:
    """Generate the GitHub Pages index.html - film-discovery-first layout."""
    # ── Aggregate film data ──────────────────────────────────────────────────
    # Build rich film entries: deduplicate by title, collect per-cinema info
    film_entries: Dict[str, Dict[str, Any]] = {}
    for cf in films_by_cinema.values():
        for rd, title, cname, furl, fdetails, cid in cf:
            slug = _tmdb_cache_key(title)
            if slug not in film_entries:
                film_entries[slug] = {
                    "title": title, "release_date": rd, "slug": slug,
                    "details": fdetails, "cinemas": {},  # cname -> (furl, rd)
                }
            # Keep the earliest release date as primary, accumulate all cinema showings
            if cname not in film_entries[slug]["cinemas"] or rd < film_entries[slug]["cinemas"][cname][1]:
                film_entries[slug]["cinemas"][cname] = (furl, rd)
            if rd < film_entries[slug]["release_date"]:
                film_entries[slug]["release_date"] = rd

    all_films_list = sorted(film_entries.values(), key=lambda f: f["release_date"])

    today = date.today()
    cutoff = today - timedelta(days=14)
    now_showing = [f for f in all_films_list if cutoff <= f["release_date"] <= today]
    now_showing.sort(key=lambda f: f["release_date"], reverse=True)
    coming_soon = [f for f in all_films_list if f["release_date"] > today]

    cinema_slugs = list(enabled_cinemas.keys())
    cinema_names = list(enabled_cinemas.values())

    # ── Cinema filter pills ──────────────────────────────────────────────────
    filter_html = '<button type="button" class="active" data-cinema="all">All</button>\n'
    for cid, info in enabled_cinemas.items():
        filter_html += f'        <button type="button" data-cinema="{cid}">{info["name"]}</button>\n'

    # ── Film card builder ────────────────────────────────────────────────────
    def _film_card(f: Dict[str, Any]) -> str:
        d = f["details"]
        poster = d.get("poster_url") or ""
        runtime = _format_runtime_display(d.get("runtime") or "")
        rating = d.get("vote_average")
        genres = sorted(set(d.get("genres") or []))
        overview = d.get("overview") or d.get("synopsis") or ""
        bbfc = d.get("bbfc") or _extract_bbfc(f["title"])
        slug = f["slug"]
        cinemas_dict = f.get("cinemas", {})  # cname -> (furl, rd)
        cinema_names = sorted(cinemas_dict.keys())
        # Map cinema display names to the IDs used in filter buttons
        _name_to_id = {v["name"]: k for k, v in enabled_cinemas.items()}
        cinema_slugs = [_name_to_id.get(cn, cn.lower().replace(" ", "-")) for cn in cinema_names]
        cinemas_data = ",".join(cinema_slugs)

        stars = _stars_from_rating(rating) if rating is not None else ""
        meta_parts = []
        screening = d.get("screening") or ""
        if screening:
            meta_parts.append(f'<span class="screening-badge">{_esc(screening)}</span>')
        if bbfc:
            meta_parts.append(f'<span class="cert cert--{bbfc.lower()}" title="{_esc(bbfc)}"></span>')
        if runtime:
            meta_parts.append(f"<span>{runtime}</span>")
        if stars:
            meta_parts.append(f'<span class="stars">{stars}</span>')
        if genres:
            meta_parts.append(f'<span class="genres">{", ".join(genres[:3])}</span>')

        poster_html = (
            f'<a href="films/{slug}.html"><img src="{_esc(poster)}" alt="" loading="lazy" decoding="async"></a>'
            if poster else f'<a href="films/{slug}.html"><div class="no-poster-sm">🎬</div></a>'
        )
        scrn_badge = f' <span class="screening-badge">{_esc(d.get("screening",""))}</span>' if d.get("screening") else ""
        banner_class = d.get("screening","").lower().replace(" ","-").replace("&","") if d.get("screening") else ""
        scrn_banner = f'<div class="fc-screening-banner {_esc(banner_class)}">{_esc(d.get("screening",""))}</div>\n' if d.get("screening") else ""

        # Group cinemas by date for grid style display
        showings_by_date: Dict[date, List[tuple]] = {}
        for cname, (furl, rd) in cinemas_dict.items():
            showings_by_date.setdefault(rd, []).append((cname, furl))
        showing_lines = []
        for rd in sorted(showings_by_date.keys()):
            cinemas_on_date = sorted(showings_by_date[rd])
            rd_str = rd.strftime("%a %d %b")
            cinema_spans = " ".join(
                f'<a href="{f"https://wtwcinemas.co.uk{furl}" if furl.startswith("/") else furl}" class="showing-cinema-link" target="_blank" rel="noopener">{cname}</a>'
                for cname, furl in cinemas_on_date
            )
            showing_lines.append(
                f'      <div class="showing-row"><span class="showing-date">{rd_str}</span><span class="showing-cinemas">{cinema_spans}</span></div>'
            )
        showings_html = "\n".join(showing_lines)

        meta_html = "".join(f"      {p}\n" for p in meta_parts)
        synopsis_html = f'    <p class="fc-synopsis">{_esc(overview[:280])} <a href="films/{slug}.html">More →</a></p>\n' if overview else ''

        return (
            f'<article class="film-card-full" data-date="{f["release_date"].isoformat()}" data-cinemas="{_esc(cinemas_data)}">\n'
            + scrn_banner +
            f'  <div class="fc-poster">{poster_html}</div>\n'
            f'  <div class="fc-info">\n'
            f'    <h3><a href="films/{slug}.html">{_esc(f["title"])}{" <span class=\"new-badge\">New</span>" if new_slugs and slug in new_slugs else ""}{scrn_badge}</a></h3>\n'
            f'    <div class="fc-meta">\n'
            + meta_html +
            f'    </div>\n'
            + synopsis_html +
            f'    <div class="fc-showings">\n'
            + showings_html +
            f'    </div>\n'
            f'  </div>\n'
            f'</article>'
        )

    now_cards = "\n".join(_film_card(f) for f in now_showing)
    coming_cards = "\n".join(_film_card(f) for f in coming_soon)

    # ── Now Showing poster grid (from whats-on data) ──────────────────────────
    # ── Special Events section ────────────────────────────────────────────
    special_events_html = ""
    if special_events:
        se_cards = []
        for se in special_events:
            poster = se.get("poster") or ""
            slug = se["slug"]
            title = se["title"]
            screening = se.get("screening", "")
            banner_class = screening.lower().replace(" ", "-").replace("&", "")
            se_cards.append(
                f'<a href="films/{slug}.html" class="ns-poster-card">\n'
                f'  <div class="ns-poster-wrap">{f"<img src=\"{_esc(poster)}\">" if poster else f"<div class=\"ns-no-poster\">{_esc(title[:30])}</div>"}</div>\n'
                f'  <span class="ns-title">{_esc(title)}</span>\n'
                f'  <span class="ns-event-tag {_esc(banner_class)}">{_esc(screening)}</span>\n'
                f'</a>'
            )
        special_events_html = (
            f'    <section class="film-section" id="special-events">\n'
            f'      <div class="section-header"><h2>Special Events</h2><span class="count">{len(se_cards)} events</span></div>\n'
            f'      <div class="ns-poster-grid">\n' + "\n".join(se_cards) + f'\n      </div>\n'
            f'    </section>\n\n'
        )

    now_showing_grid = ""
    if now_showing_live:
        poster_cards = []
        list_cards = []
        seen_slugs = set(f["slug"] for f in (special_events or []))
        for nf in now_showing_live[:60]:  # cap at 60 for performance
            poster = nf.get("poster") or ""
            slug = nf["slug"]
            title = nf["title"]
            cinemas_str = ", ".join(nf.get("cinemas", [])[:3])
            poster_html = (
                f'<img src="{_esc(poster)}" alt="{_esc(title)}" loading="lazy" decoding="async">'
                if poster
                else f'<div class="ns-no-poster">{_esc(title)[:30]}</div>'
            )
            poster_cards.append(
                f'<a href="films/{slug}.html" class="ns-poster-card" title="{_esc(title)} - {_esc(cinemas_str)}">\n'
                f'  <div class="ns-poster-wrap">{poster_html}</div>\n'
                f'  <span class="ns-title">{_esc(title)}</span>\n'
                f'</a>'
            )
            # Simple list card for card view
            st_list = nf.get("showtimes", [])
            next_time = ""
            if st_list:
                today = date.today()
                upcoming = [s for s in st_list if s["date"] >= today]
                if upcoming:
                    nxt = upcoming[0]
                    next_time = f'{nxt["date"].strftime("%a %d %b")} {nxt["time"]}'
            list_cards.append(
                f'<a href="films/{slug}.html" class="ns-list-card">\n'
                f'  <span class="ns-list-title">{_esc(title)}</span>\n'
                f'  <span class="ns-list-cinemas">{_esc(cinemas_str)}</span>\n'
                + (f'  <span class="ns-list-next">{_esc(next_time)}</span>\n' if next_time else '')
                + f'</a>'
            )
        now_showing_grid = (
            f'    <section class="film-section poster-view" id="now-showing-live">\n'
            f'      <div class="section-header"><h2>Now Showing</h2><div style="display:flex;align-items:center;gap:0.75rem"><span class="count">{len(now_showing_live)} films</span><button type="button" id="ns-view-toggle" class="view-toggle-btn">☰ List</button></div></div>\n'
            f'      <div class="ns-poster-grid">\n' + "\n".join(poster_cards) + f'\n      </div>\n'
            f'      <div class="ns-list-grid" style="display:none">\n' + "\n".join(list_cards) + f'\n      </div>\n'
            f'    </section>\n\n'
        )

    now_html = (
        f'    <section class="film-section" id="now-showing">\n'
        f'      <div class="section-header"><h2>Now Showing</h2><span class="count">{len(now_showing)} films</span></div>\n'
        f'      <div class="film-browse-grid">\n{now_cards}\n      </div>\n'
        f'    </section>\n\n'
    ) if now_showing else ""

    coming_html = (
        f'    <section class="film-section" id="coming-soon">\n'
        f'      <div class="section-header"><h2>Coming Soon</h2><div style="display:flex;align-items:center;gap:0.75rem"><span class="count">{len(coming_soon)} films</span><button type="button" id="view-toggle" class="view-toggle-btn">▦ Posters</button></div></div>\n'
        f'      <div class="film-browse-grid">\n{coming_cards}\n      </div>\n'
        f'    </section>\n\n'
    ) if coming_soon else ""

    empty_html = (
        f'    <div style="text-align:center;padding:4rem 2rem;color:var(--text-muted)">\n'
        f'      <h2 style="font-size:1.5rem;margin-bottom:0.5rem;color:var(--text)">No films found</h2>\n'
        f'      <p>Check back soon for new premieres at WTW Cinemas.</p>\n'
        f'    </div>\n\n'
    ) if not all_films_list else ""

    # ── Calendar CTA section ─────────────────────────────────────────────────
    calendar_cta = ""
    calendar_promo = ""
    if cinema_slugs:
        cta_buttons = ""
        for cid, info in enabled_cinemas.items():
            ics_url = f"wtw-{cid}.ics"
            webcal_url = f"webcal://evenwebb.github.io/wtw-cinemas/{ics_url}"
            gcal_url = f"https://calendar.google.com/calendar/render?cid=webcal://evenwebb.github.io/wtw-cinemas/{ics_url}"
            https_url = f"https://evenwebb.github.io/wtw-cinemas/{ics_url}"
            cta_buttons += (
                f'          <div class="cta-cinema-row">\n'
                f'            <span class="cta-cinema-name">{info["name"]}</span>\n'
                f'            <div class="cta-btn-group">\n'
                f'              <a href="{_esc(webcal_url)}" class="cta-btn ios-btn" title="Add to Apple Calendar">iOS</a>\n'
                f'              <a href="{_esc(gcal_url)}" class="cta-btn google-btn" target="_blank" rel="noopener" title="Add to Google Calendar">Google</a>\n'
                f'              <button type="button" class="cta-btn copy-btn" data-copy="{_esc(webcal_url)}" title="Copy link">Copy</button>\n'
                f'              <button type="button" class="cta-btn show-btn" title="Show URL">Show</button>\n'
                f'            </div>\n'
                f'            <div class="cta-url" hidden><input type="text" value="{_esc(https_url)}" readonly class="cta-url-input" onclick="this.select()"></div>\n'
                f'          </div>\n'
            )
        calendar_cta = (
            f'    <section class="calendar-cta" id="subscribe" aria-labelledby="cta-heading">\n'
            f'      <div class="cta-header">\n'
            f'        <span class="cta-icon">📅</span>\n'
            f'        <div>\n'
            f'          <h2 id="cta-heading">Never miss a premiere</h2>\n'
            f'          <p>Subscribe to get new film releases added to your calendar automatically. Choose your cinema, pick your platform.</p>\n'
            f'        </div>\n'
            f'      </div>\n'
            f'      <div class="cta-buttons">\n'
            f'{cta_buttons}\n'
            f'      </div>\n'
            f'      <div class="cta-howto">\n'
            f'        <div class="cta-howto-title">How to add a calendar on your device</div>\n'
            f'        <div class="cta-howto-content">\n'
            f'          <div class="cta-howto-item">\n'
            f'            <p><strong>iPhone / iPad:</strong> Tap the <strong>iOS</strong> button above, then tap <strong>Subscribe</strong> in the popup. Or go to Settings → Calendar → Accounts → Add Account → Other → Add Subscribed Calendar.</p>\n'
            f'          </div>\n'
            f'          <div class="cta-howto-item">\n'
            f'            <p><strong>Google Calendar:</strong> Tap <strong>Google</strong> above to add directly. Or go to <strong>Add other calendars</strong> → <strong>From URL</strong>, paste the link, and click <strong>Add calendar</strong>.</p>\n'
            f'          </div>\n'
            f'          <div class="cta-howto-item">\n'
            f'            <p><strong>Outlook / Other:</strong> Copy the calendar link above, then go to <strong>Add calendar</strong> → <strong>Subscribe from web</strong> and paste it.</p>\n'
            f'          </div>\n'
            f'        </div>\n'
            f'      </div>\n'
            f'    </section>\n\n'
        )
        # Top promo banner
        calendar_promo = (
            '    <a href="#subscribe" class="calendar-promo">\n'
            '      <span class="promo-icon">📅</span>\n'
            '      <span class="promo-text promo-text-full">Get new film premieres added to your phone calendar automatically</span>\n'
            '      <span class="promo-text promo-text-short">Add premieres to your calendar</span>\n'
            '      <span class="promo-cta">Set up now ↓</span>\n'
            '    </a>\n\n'
        )

    now_london = format_london_timestamp()

    # ── Cinema filter JS ──────────────────────────────────────────────────────
    cinema_filter_js = (
        '<script>\n'
        'document.querySelectorAll(".cinema-filter button").forEach(function(btn){'
        'btn.addEventListener("click",function(){'
        'document.querySelectorAll(".cinema-filter button").forEach(function(b){b.classList.remove("active")});'
        'this.classList.add("active");'
        'var cinema=this.getAttribute("data-cinema");'
        'document.querySelectorAll(".film-card-full").forEach(function(card){'
        'if(cinema==="all"||(card.getAttribute("data-cinemas")||"").indexOf(cinema)!==-1){card.style.display=""}'
        'else{card.style.display="none"}'
        '})'
        '})'
        '});\n'
        '</script>\n'
    )

    return (
        '<!DOCTYPE html>\n<html lang="en">\n<head>\n'
        '  <meta charset="utf-8">\n'
        '  <meta name="viewport" content="width=device-width, initial-scale=1">\n'
        '  <title>What\'s on at WTW Cinemas - Film Premieres</title>\n'
        '  <meta name="description" content="Browse upcoming film premieres at WTW Cinemas in Cornwall. Discover new movies with ratings, trailers, and book tickets.">\n'
        '  <meta property="og:title" content="What\'s on at WTW Cinemas">\n'
        '  <meta property="og:description" content="Browse upcoming film premieres at WTW Cinemas in Cornwall. Ratings, trailers, and booking links.">\n'
        '  <meta property="og:type" content="website">\n'
        '  <link rel="canonical" href="https://evenwebb.github.io/wtw-cinemas/">\n'
        '  <meta name="twitter:card" content="summary">\n'
        '  <link rel="icon" href="data:image/svg+xml,<svg xmlns=\'http://www.w3.org/2000/svg\' viewBox=\'0 0 100 100\'><text y=\'.9em\' font-size=\'90\'>🎬</text></svg>">\n'
        '  <link rel="preconnect" href="https://fonts.googleapis.com">\n'
        '  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>\n'
        '  <link href="https://fonts.googleapis.com/css2?family=Space+Grotesk:wght@400;600;700&family=JetBrains+Mono:wght@400;500&display=swap" rel="stylesheet">\n'
        f'  <style>\n{CSS}\n  </style>\n'
        '</head>\n<body>\n'
        '  <a href="#main-content" class="skip-link">Skip to content</a>\n'
        '  <div class="bg-mesh" aria-hidden="true"></div>\n'
        '  <div class="page" id="main-content">\n'
        '    <header class="hero">\n'
        ''
        '      <h1>What\'s on at WTW Cinemas</h1>\n'
        '      <p class="tagline">Browse and discover upcoming film premieres across all WTW Cinemas. Ratings, trailers, and booking links - all in one place.</p>\n'
        f'      <span class="hero-stat">{len(all_films_list)} films across {len(enabled_cinemas)} cinemas</span>\n'
        f'      <div class="hero-updated">Last updated {now_london}</div>\n'
        '    </header>\n\n'
        + calendar_promo +
        (
            f'    <nav class="quick-nav" aria-label="Jump to section">\n'
            f'      <a href="#now-showing-live">Now Showing</a>\n'
            f'      <a href="#coming-soon">Coming Soon</a>\n'
            f'      <a href="#subscribe">Subscribe</a>\n'
            f'    </nav>\n\n'
        ) +
        '    <div class="cinema-filter" role="group" aria-label="Filter by cinema">\n'
        f'        {filter_html}'
        '    </div>\n\n'
        + now_showing_grid
        + special_events_html
        + coming_html
        + empty_html
        + calendar_cta +
        '    <footer role="contentinfo">\n'
        '      <p class="footer-disclaimer">An open source fan-made project. Calendars update when new premieres are added. Not affiliated with WTW Cinemas.</p>\n'
        '      <div class="footer-links">\n'
        '        <a href="https://wtwcinemas.co.uk/">WTW Cinemas</a>\n'
        '        <span aria-hidden="true">·</span>\n'
        '        <a href="https://github.com/evenwebb/wtw-cinemas">Source</a>\n'
        '        <span aria-hidden="true">·</span>\n'
        '        <a href="https://github.com/evenwebb/">evenwebb</a>\n'
        '      </div>\n'
        f'      <p class="footer-updated">Last updated: {now_london}</p>\n'
        '    </footer>\n'
        '  </div>\n'
        + cinema_filter_js +
        '  <script>\n'
        '  document.querySelectorAll(".copy-btn").forEach(function(btn){'
        'btn.addEventListener("click",function(){'
        'var url=this.getAttribute("data-copy");if(!url)return;'
        'navigator.clipboard.writeText(url).then(function(){'
        'this.textContent="Copied!";this.classList.add("copied");'
        'var self=this;setTimeout(function(){self.textContent="Copy";self.classList.remove("copied")},2000);'
        '}.bind(this)).catch(function(){'
        'this.textContent="Error";setTimeout(function(){this.textContent="Copy"}.bind(this),2000);'
        '}.bind(this));'
        '});'
        '});\n'
        'document.querySelectorAll(".show-btn").forEach(function(btn){'
        'btn.addEventListener("click",function(){'
        'var url=this.closest(".cta-cinema-row").querySelector(".cta-url");'
        'if(!url)return;'
        'var isHidden=url.hasAttribute("hidden");'
        'if(isHidden){url.removeAttribute("hidden");this.textContent="Hide"}'
        'else{url.setAttribute("hidden","");this.textContent="Show"}'
        '});'
        '});\n'
        '</script>\n'
        '  <script>\n'
        '  (function(){\n'
        '    var ua=navigator.userAgent||"";\n'
        '    var ios=/iPhone|iPod|iPad/.test(ua)||(navigator.maxTouchPoints>1&&/Macintosh|Mac OS X/.test(ua));\n'
        '    var mac=/Macintosh|Mac OS X/.test(ua)&&!ios;\n'
        '    var android=/Android/.test(ua);\n'
        '    var links=document.querySelectorAll(\'a[href$=".ics"]\');\n'
        '    for(var i=0;i<links.length;i++){(function(l){\n'
        '      var h=l.getAttribute("href");\n'
        '      if(!h)return;\n'
        '      try{\n'
        '        var u=new URL(h,window.location.href);\n'
        '        if(ios||mac){u.protocol="webcal:";l.href=u.href}\n'
        '        else if(android){l.href="https://www.google.com/calendar/render?cid="+encodeURIComponent(u.href)}\n'
        '        else{l.href="https://www.google.com/calendar/render?cid="+encodeURIComponent(u.href)}\n'
        '      }catch(e){}\n'
        '    })(links[i])}\n'
        '    var items=document.querySelectorAll(".accordion-item");\n'
        '    var triggers=document.querySelectorAll(".accordion-trigger");\n'
        '    var panels=document.querySelectorAll(".accordion-panel");\n'
        '    if(items.length){\n'
        '      var p0=panels[0];p0.style.maxHeight=p0.scrollHeight+"px";\n'
        '      items[0].classList.add("open");\n'
        '      triggers[0].setAttribute("aria-expanded","true");\n'
        '      p0.setAttribute("aria-hidden","false")\n'
        '    }\n'
        '    for(var k=0;k<triggers.length;k++){(function(btn,idx){\n'
        '      btn.addEventListener("click",function(){\n'
        '        var item=items[idx];\n'
        '        var panel=panels[idx];\n'
        '        var wasOpen=item.classList.contains("open");\n'
        '        for(var m=0;m<items.length;m++){\n'
        '          items[m].classList.remove("open");\n'
        '          panels[m].style.maxHeight="";\n'
        '          triggers[m].setAttribute("aria-expanded","false");\n'
        '          panels[m].setAttribute("aria-hidden","true")\n'
        '        }\n'
        '        if(!wasOpen){\n'
        '          item.classList.add("open");\n'
        '          panel.style.maxHeight=panel.scrollHeight+"px";\n'
        '          btn.setAttribute("aria-expanded","true");\n'
        '          panel.setAttribute("aria-hidden","false")\n'
        '        }\n'
        '      })\n'
        '    })(triggers[k],k)}\n'
        '  })();\n'
        '  </script>\n'
        '  <script>\n'
        '  // Nearest cinema highlight\n'
        '  (function(){\n'
        '    var cinemas={'
        + ",".join(f'"{c["name"]}":{{lat:{c["lat"]},lng:{c["lng"]}}}' for c in [{"name":"bodmin","lat":50.466,"lng":-4.718},{"name":"helston","lat":50.102,"lng":-5.274},{"name":"falmouth","lat":50.155,"lng":-5.067},{"name":"redruth","lat":50.233,"lng":-5.226},{"name":"st-ives","lat":50.210,"lng":-5.490},{"name":"penzance-savoy","lat":50.118,"lng":-5.538},{"name":"penzance-ritz","lat":50.118,"lng":-5.536}])
        + '};\n'
        '    if(!navigator.geolocation)return;\n'
        '    navigator.geolocation.getCurrentPosition(function(pos){\n'
        '      var best=null,bestDist=Infinity;\n'
        '      for(var cn in cinemas){\n'
        '        var c=cinemas[cn];\n'
        '        var d=Math.sqrt(Math.pow(c.lat-pos.coords.latitude,2)+Math.pow(c.lng-pos.coords.longitude,2));\n'
        '        if(d<bestDist){bestDist=d;best=cn;}\n'
        '      }\n'
        '      if(best){\n'
        '        var btns=document.querySelectorAll(".cinema-filter button");\n'
        '        var slug=best.toLowerCase().replace(/\\s+/g,"-");\n'
        '        for(var i=0;i<btns.length;i++){\n'
        '          if(btns[i].getAttribute("data-cinema")===slug){\n'
        '            btns[i].classList.add("nearest");\n'
        '            btns[i].setAttribute("title","Nearest cinema: "+best);\n'
        '            break;\n'
        '          }\n'
        '        }\n'
        '      }\n'
        '    },function(){},{timeout:5000,maximumAge:3600000});\n'
        '  })();\n'
        '  // View toggle for Now Showing and Coming Soon\n'
        '  function setupViewToggle(toggleId,sectionId,defaultPoster){\n'
        '    var toggle=document.getElementById(toggleId);\n'
        '    var section=document.getElementById(sectionId);\n'
        '    if(!toggle||!section)return;\n'
        '    var storageKey="wtw-view-"+sectionId;\n'
        '    var isPoster=section.classList.contains("poster-view");\n'
        '    if(localStorage.getItem(storageKey)==="cards"){\n'
        '      section.classList.remove("poster-view");\n'
        '      toggle.textContent=defaultPoster?"▦ Posters":"☰ Cards";\n'
        '    }\n'
        '    toggle.addEventListener("click",function(){\n'
        '      var nowPoster=section.classList.toggle("poster-view");\n'
        '      toggle.textContent=nowPoster?(defaultPoster?"☰ List":"☰ Cards"):(defaultPoster?"▦ Posters":"▦ Posters");\n'
        '      localStorage.setItem(storageKey,nowPoster?"posters":"cards");\n'
        '    });\n'
        '  }\n'
        '  setupViewToggle("ns-view-toggle","now-showing-live",true);\n'
        '  setupViewToggle("view-toggle","coming-soon",false);\n'
        '  </script>\n'
        '  <noscript>\n'
        '    <style>.accordion-panel{max-height:none!important}.accordion-trigger{cursor:default}.accordion-trigger::after{display:none}</style>\n'
        '  </noscript>\n'
        '</body>\n</html>'
    )


# ── Cinema pages ────────────────────────────────────────────────────────────────
def build_cinema_page(
    cinema_id: str,
    cinema_info: dict,
    now_showing_films: List[Dict[str, Any]],
    coming_soon_films: List[Dict[str, Any]],
) -> str:
    """Generate a dedicated page for a single cinema."""
    address = CINEMA_ADDRESSES.get(cinema_id, cinema_info["name"].replace(" ", "+"))
    maps_url = f"https://www.google.com/maps/search/{address}"

    # Now Showing poster cards
    ns_cards = []
    for nf in now_showing_films[:40]:
        cinemas = nf.get("cinemas", [])
        if cinema_info["name"] not in cinemas:
            continue
        poster = nf.get("poster") or ""
        slug = nf["slug"]
        title = nf["title"]
        poster_html = (
            f'<img src="../posters/{slug}.jpg" alt="{_esc(title)}" loading="lazy" decoding="async">'
            if poster
            else f'<div class="ns-no-poster">{_esc(title)[:30]}</div>'
        )
        ns_cards.append(
            f'<a href="films/{slug}.html" class="ns-poster-card">\n'
            f'  <div class="ns-poster-wrap">{poster_html}</div>\n'
            f'  <span class="ns-title">{_esc(title)}</span>\n'
            f'</a>'
        )

    ns_grid = (
        f'  <section class="film-section" id="now-showing">\n'
        f'    <div class="section-header"><h2>Now Showing</h2><span class="count">{len(ns_cards)} films</span></div>\n'
        f'    <div class="ns-poster-grid">\n' + "\n".join(ns_cards) + f'\n    </div>\n'
        f'  </section>\n'
    ) if ns_cards else ''

    # Coming Soon simple list
    cs_items = []
    for f in coming_soon_films:
        cs_items.append(
            f'<li><a href="films/{f["slug"]}.html">{_esc(f["title"])}</a>'
            f' - {f["release_date"].strftime("%a %d %b %Y")}</li>'
        )

    cs_section = (
        f'  <section class="film-section" id="coming-soon">\n'
        f'    <div class="section-header"><h2>Coming Soon</h2><span class="count">{len(cs_items)} films</span></div>\n'
        f'    <ul class="cs-list">\n' + "\n".join(cs_items) + f'\n    </ul>\n'
        f'  </section>\n'
    ) if cs_items else ''

    now_london = format_london_timestamp()

    return (
        '<!DOCTYPE html>\n<html lang="en">\n<head>\n'
        '  <meta charset="utf-8">\n'
        '  <meta name="viewport" content="width=device-width, initial-scale=1">\n'
        f'  <title>What\'s on at WTW {cinema_info["name"]}</title>\n'
        f'  <meta name="description" content="Now showing and coming soon at WTW Cinemas {cinema_info["name"]}.">\n'
        '  <link rel="canonical" href="https://evenwebb.github.io/wtw-cinemas/">\n'
        '  <link rel="icon" href="data:image/svg+xml,<svg xmlns=\'http://www.w3.org/2000/svg\' viewBox=\'0 0 100 100\'><text y=\'.9em\' font-size=\'90\'>🎬</text></svg>">\n'
        '  <link rel="preconnect" href="https://fonts.googleapis.com">\n'
        '  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>\n'
        '  <link href="https://fonts.googleapis.com/css2?family=Space+Grotesk:wght@400;600;700&display=swap" rel="stylesheet">\n'
        f'  <style>\n{_SHARED_CSS}\n'
        '    .page{max-width:860px;margin:0 auto;padding:1.5rem 1rem 4rem}\n'
        '    .back-btn{display:inline-flex;align-items:center;gap:0.4rem;padding:0.5rem 1.1rem;background:var(--surface);border:1px solid var(--border);border-radius:100px;color:var(--text-muted);text-decoration:none;font-weight:500;font-size:0.85rem;margin-bottom:2rem;transition:all var(--transition)}\n'
        '    .back-btn:hover{color:var(--accent);border-color:var(--accent);background:var(--accent-dim)}\n'
        '    .cinema-hero{text-align:center;padding:2rem 0 3rem}\n'
        '    .cinema-hero h1{font-size:clamp(1.5rem,4vw,2rem);font-weight:800;background:linear-gradient(135deg,var(--cyan),var(--purple));-webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text}\n'
        '    .cinema-hero p{color:var(--text-muted);font-size:0.95rem;margin-top:0.5rem}\n'
        '    .cinema-hero .map-link{display:inline-block;margin-top:0.75rem;padding:0.4rem 1rem;border-radius:100px;font-size:0.82rem;color:var(--accent);text-decoration:none;border:1px solid var(--border);transition:all var(--transition)}\n'
        '    .cinema-hero .map-link:hover{background:var(--accent-dim);border-color:var(--accent)}\n'
        '    .cs-list{list-style:none;padding:0;display:flex;flex-direction:column;gap:0.5rem}\n'
        '    .cs-list li{font-size:0.92rem;padding:0.75rem 1rem;background:var(--surface);border:1px solid var(--border);border-radius:10px}\n'
        '    .cs-list li a{color:var(--text);text-decoration:none;font-weight:600}\n'
        '    .cs-list li a:hover{color:var(--accent)}\n'
        '  </style>\n'
        '</head>\n<body>\n'
        '  <div class="bg-mesh" aria-hidden="true"></div>\n'
        '  <div class="page">\n'
        '    <a href="./" class="back-btn">← All</a>\n'
        f'    <header class="cinema-hero">\n'
        f'      <h1>WTW {cinema_info["name"]}</h1>\n'
        f'      <p>Subscribe: <a href="wtw-{cinema_id}.ics" type="text/calendar" download>iCal feed</a></p>\n'
        f'      <a href="{maps_url}" class="map-link" target="_blank" rel="noopener">📍 View on map</a>\n'
        f'    </header>\n'
        + ns_grid + cs_section +
        f'    <footer style="text-align:center;padding:2rem 0;color:var(--text-muted);font-size:0.85rem;border-top:1px solid var(--border);margin-top:3rem">\n'
        f'      <p>An open source fan-made project. Not affiliated with WTW Cinemas.</p>\n'
        f'      <p class="footer-updated">Last updated: {now_london}</p>\n'
        f'    </footer>\n'
        '  </div>\n'
        '</body>\n</html>'
    )


def generate_sitemap(film_slugs: List[str], cinema_ids: List[str]) -> str:
    """Generate sitemap.xml for SEO."""
    base = "https://evenwebb.github.io/wtw-cinemas"
    urls = [f"  <url><loc>{base}/</loc></url>"]
    for slug in film_slugs:
        urls.append(f"  <url><loc>{base}/films/{slug}.html</loc></url>")
    for cid in cinema_ids:
        urls.append(f"  <url><loc>{base}/{cid}.html</loc></url>")
    return '<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n' + "\n".join(urls) + '\n</urlset>'


# ── Film detail pages ───────────────────────────────────────────────────────────
def _extract_bbfc(title: str) -> str:
    """Extract BBFC rating from title like 'Film Name (15)' -> '15'."""
    m = BBFC_PATTERN.search(title)
    return m.group(1).upper().replace("R18", "R18") if m else ""


def _download_cert_images(session: Optional[requests.Session] = None) -> None:
    """Download BBFC cert images to docs/certs/ for local serving."""
    if not WTW_CERT_BASE:
        return  # WTW uses inline cert images, no remote download needed
    s = session or _session()
    Path(CERTS_DIR).mkdir(parents=True, exist_ok=True)
    for rating, filename in CERT_IMAGES.items():
        path = Path(CERTS_DIR) / filename
        if path.exists():
            continue
        try:
            r = s.get(f"{WTW_CERT_BASE}/{filename}", headers={"Referer": WTW_BASE_URL + "/"}, timeout=10)
            r.raise_for_status()
            path.write_bytes(r.content)
        except Exception as e:
            logger.warning("Cert download failed %s: %s", filename, e)


def _download_poster(url: str, slug: str, session: Optional[requests.Session] = None) -> str:
    """Download TMDb poster, return relative path like 'posters/slug.jpg' or '' on failure."""
    if not url.startswith("http"):
        return ""
    s = session or _session()
    posters_dir = Path(POSTERS_DIR)
    posters_dir.mkdir(parents=True, exist_ok=True)
    slug_clean = re.sub(r"[^a-z0-9-]", "", slug.lower()) or "poster"
    existing = list(posters_dir.glob(f"{slug_clean}.*"))
    if existing:
        return f"posters/{existing[0].name}"
    ext = "webp" if ".webp" in url.lower() else ("png" if ".png" in url.lower() else "jpg")
    path = posters_dir / f"{slug_clean}.{ext}"
    try:
        r = s.get(url, timeout=15)
        r.raise_for_status()
        path.write_bytes(r.content)
        return f"posters/{slug_clean}.{ext}"
    except Exception as e:
        logger.warning("Poster download failed %s: %s", url[:50], e)
        return ""


def _compute_fingerprint(films: List[Tuple]) -> str:
    """SHA-256 hash of film titles + dates + cinemas for change detection."""
    parts = sorted(set(
        f"{f[0].isoformat()}|{f[1]}|{f[5]}" for f in films
    ))
    return hashlib.sha256("\n".join(parts).encode()).hexdigest()


def _load_fingerprint() -> str:
    try:
        return Path(FINGERPRINT_FILE).read_text(encoding="utf-8").strip()
    except Exception:
        return ""


def _save_fingerprint(fp: str) -> None:
    Path(FINGERPRINT_FILE).write_text(fp, encoding="utf-8")


def _health_check(films: List[Tuple], enabled_cinemas: Dict[str, dict]) -> bool:
    """Return True if health checks pass, False otherwise."""
    unique_films = len(set(f[1] for f in films))
    cinemas_with_films = len(set(f[5] for f in films))
    ok = True
    if unique_films < HEALTH_MIN_FILMS:
        logger.warning("Health: %d films below minimum %d", unique_films, HEALTH_MIN_FILMS)
        ok = False
    if cinemas_with_films < HEALTH_MIN_CINEMAS:
        logger.warning("Health: %d cinemas below minimum %d", cinemas_with_films, HEALTH_MIN_CINEMAS)
        ok = False
    return ok


def _cert_span(rating: str) -> str:
    """HTML span for BBFC cert badge using local image."""
    if not rating or rating.upper() not in CERT_IMAGES:
        return ""
    r = rating.lower().replace(" ", "")
    return f'<span class="cert cert--{r}" aria-label="Rated {rating.upper()}" title="Rated {rating.upper()}"></span>'


FILM_CSS = _SHARED_CSS + """
body{position:relative}
.page{position:relative;z-index:1;max-width:860px;margin:0 auto;padding:1.5rem 1rem 4rem}
@media(min-width:640px){.page{padding:2.5rem 2rem 5rem}}
.back-btn{display:inline-flex;align-items:center;gap:0.4rem;padding:0.5rem 1.1rem;background:var(--surface);border:1px solid var(--border);border-radius:100px;color:var(--text-muted);text-decoration:none;font-weight:500;font-size:0.85rem;margin-bottom:2rem;transition:all var(--transition)}
.back-btn:hover{color:var(--accent);border-color:var(--accent);background:var(--accent-dim)}
.film-layout{display:grid;grid-template-columns:1fr;gap:2rem;margin-bottom:2.5rem;position:relative;padding-top:42px}@media(min-width:600px){body{padding-top:48px}}
@media(min-width:680px){.film-layout{grid-template-columns:280px 1fr;align-items:start}}
.poster{width:100%;max-width:280px;margin:0 auto;position:relative;z-index:1}
@media(min-width:680px){.poster{margin:0}}
.poster img{width:100%;height:auto;border-radius:14px;box-shadow:0 8px 35px rgba(0,0,0,0.5);display:block}
.poster .no-poster{width:100%;aspect-ratio:2/3;background:var(--surface);border-radius:14px;display:flex;align-items:center;justify-content:center;color:var(--text-muted);font-size:0.85rem;text-align:center;padding:2rem;border:1px dashed var(--border)}
.film-info{position:relative;z-index:1}
.film-info h1{font-size:clamp(1.5rem,4vw,2rem);font-weight:800;letter-spacing:-0.03em;line-height:1.15;margin-bottom:0.6rem;background:linear-gradient(135deg,var(--cyan),var(--purple));-webkit-background-clip:text;-webkit-text-fill-color:transparent;background-clip:text}
.film-info .meta{display:flex;flex-wrap:wrap;align-items:center;gap:0.4rem 0.9rem;margin-bottom:1.25rem;font-size:0.88rem;color:var(--text-muted)}
.film-info .stars{color:var(--amber);letter-spacing:0.05em;font-size:0.9rem}
.film-info .genres{color:var(--purple);font-weight:500}
.film-info .rating-pill{background:var(--accent-dim);color:var(--accent);padding:0.2rem 0.65rem;border-radius:100px;font-weight:600;font-size:0.82rem}
.film-info .synopsis{font-size:0.95rem;line-height:1.75;color:var(--text-muted);margin-bottom:1.25rem;padding:1.25rem;background:var(--surface);border-radius:12px;border:1px solid var(--border)}
.screening-info{background:linear-gradient(135deg,rgba(34,211,238,0.08),rgba(192,132,252,0.06));border:1px solid rgba(34,211,238,0.2);border-radius:12px;padding:1rem 1.25rem;margin-bottom:1.25rem}
.screening-info-label{display:inline-block;font-size:0.7rem;font-weight:700;text-transform:uppercase;letter-spacing:0.1em;color:var(--accent);background:var(--accent-dim);padding:0.25rem 0.65rem;border-radius:100px;margin-bottom:0.6rem}
.screening-info p{font-size:0.88rem;color:var(--text);margin:0;line-height:1.6}
.film-info .crew{margin-bottom:1rem}
.film-info .crew p{font-size:0.88rem;color:var(--text-muted);padding:0.55rem 0;border-bottom:1px solid var(--border)}
.film-info .crew p:last-child{border-bottom:none}
.film-info .crew strong{color:var(--text);margin-right:0.5rem;font-weight:600}
.links{display:flex;flex-wrap:wrap;gap:0.5rem;margin-bottom:1.5rem}
.ext-link{display:inline-flex;align-items:center;padding:0.45rem 0.85rem;background:var(--surface);border:1px solid var(--border);border-radius:100px;color:var(--text-muted);text-decoration:none;font-size:0.82rem;font-weight:500;transition:all var(--transition)}
.ext-link:hover{border-color:var(--accent);color:var(--accent);background:var(--accent-dim)}
.trailer-section{margin-bottom:2.5rem}
.trailer-section h2{font-size:1.1rem;font-weight:700;margin-bottom:0.85rem;color:var(--accent)}
.trailer-wrap{position:relative;width:100%;aspect-ratio:16/9;background:#000;border-radius:14px;overflow:hidden;box-shadow:0 4px 25px rgba(0,0,0,0.5),0 0 0 1px rgba(34,211,238,0.1)}
.trailer-wrap iframe{position:absolute;top:0;left:0;width:100%;height:100%;border:none}
.trailer-wrap .no-trailer{display:flex;align-items:center;justify-content:center;height:100%;color:var(--text-muted);font-size:0.9rem}
.cinema-section{margin-bottom:2.5rem}
.cinema-section h2{font-size:1.1rem;font-weight:700;margin-bottom:0.85rem;color:var(--accent);display:flex;align-items:center;gap:0.5rem}
.tag-key-btn{display:inline-flex;align-items:center;justify-content:center;width:22px;height:22px;border-radius:50%;border:1px solid var(--border);background:var(--surface);color:var(--text-muted);font-size:0.75rem;cursor:pointer;transition:all var(--transition);padding:0;line-height:1}
.tag-key-btn:hover{color:var(--accent);border-color:var(--accent);background:var(--accent-dim)}
.tag-key-popup{position:fixed;inset:0;z-index:100;display:flex;align-items:center;justify-content:center}
.tag-key-popup[hidden]{display:none}
.tag-key-overlay{position:absolute;inset:0;background:rgba(0,0,0,0.6)}
.tag-key-dialog{position:relative;background:var(--surface);border:1px solid var(--border);border-radius:14px;padding:1.5rem;max-width:340px;width:92%;max-height:80vh;overflow-y:auto;box-shadow:0 20px 60px rgba(0,0,0,0.5)}
@media(min-width:480px){.tag-key-dialog{padding:2rem;max-width:380px}}
.tag-key-close{position:absolute;top:0.75rem;right:1rem;background:none;border:none;color:var(--text-muted);font-size:1.5rem;cursor:pointer;padding:0;line-height:1}
.tag-key-close:hover{color:var(--text)}
.tag-key-dialog h3{font-size:1rem;font-weight:700;margin-bottom:1rem;color:var(--text)}
.tag-key-dialog dl{display:grid;grid-template-columns:auto 1fr;gap:0.6rem 0.75rem;align-items:center}
.tag-key-dialog dt{margin:0}
.tag-key-dialog dd{font-size:0.85rem;color:var(--text-muted);margin:0}
.st-filter{display:flex;flex-wrap:wrap;gap:0.35rem;margin-bottom:0.85rem}
.st-filter-btn{font-family:inherit;font-size:0.72rem;font-weight:600;padding:0.3rem 0.75rem;border-radius:100px;border:1px solid var(--border);background:var(--surface);color:var(--text-muted);cursor:pointer;transition:all var(--transition)}
.st-filter-btn:hover{color:var(--accent);border-color:var(--accent)}
.st-filter-btn.active{background:var(--accent-dim);color:var(--accent);border-color:var(--accent)}
.cinema-table-wrap{overflow-x:auto;-webkit-overflow-scrolling:touch;margin:0 -0.5rem;padding:0 0.5rem}
@media(min-width:600px){.cinema-table-wrap{margin:0;padding:0;overflow-x:visible}}
.cinema-table{width:100%;border-collapse:collapse;font-size:0.82rem;min-width:480px}
@media(min-width:600px){.cinema-table{font-size:0.9rem;min-width:0}}
.cinema-table thead th{text-align:left;font-size:0.68rem;font-weight:600;text-transform:uppercase;letter-spacing:0.08em;color:var(--text-muted);padding:0.4rem 0.5rem;border-bottom:2px solid var(--border)}
@media(min-width:600px){.cinema-table thead th{font-size:0.72rem;padding:0.5rem 0.75rem}}
.cinema-table tbody td{padding:0.5rem 0.5rem;border-bottom:1px solid var(--border);vertical-align:middle}
@media(min-width:600px){.cinema-table tbody td{padding:0.6rem 0.75rem}}
.cinema-table tbody tr:hover{background:var(--accent-dim)}
tr.nearest-cinema-row{background:rgba(34,211,238,0.06)}
tr.nearest-cinema-row:first-child{border-top:2px solid var(--accent)}
tr.nearest-cinema-row:last-of-type{border-bottom:2px solid var(--accent)}
tr.nearest-cinema-row td:first-child{border-left:3px solid var(--accent)}
.nearest-cinema-label{font-size:0.78rem;font-weight:600;color:var(--accent);padding:0.4rem 0.6rem;margin-bottom:0.25rem;display:flex;align-items:center;gap:0.3rem;background:rgba(34,211,238,0.08);border-radius:8px}
.cinema-table .date-cell{font-weight:600;color:var(--accent);white-space:nowrap;font-size:0.78rem}
@media(min-width:600px){.cinema-table .date-cell{font-size:inherit}}
.cinema-table .time-cell{font-weight:500;color:var(--text);font-variant-numeric:tabular-nums}
.cinema-table .screen-badge{font-size:0.65rem;font-weight:600;color:var(--purple);background:rgba(192,132,252,0.12);padding:0.12rem 0.3rem;border-radius:4px;margin-left:0.2rem;white-space:nowrap}
@media(min-width:600px){.cinema-table .screen-badge{font-size:0.72rem;padding:0.15rem 0.4rem}}
.cinema-table .tag-badge{display:inline-block;font-size:0.6rem;font-weight:700;padding:0.1rem 0.25rem;border-radius:3px;margin-left:0.15rem;vertical-align:middle;line-height:1.4;cursor:help}
@media(min-width:600px){.cinema-table .tag-badge{font-size:0.65rem;padding:0.1rem 0.3rem;margin-left:0.2rem}}
.cinema-table .tag-badge[title*=\"Audio\"]{color:#22d3ee;background:rgba(34,211,238,0.12)}
.cinema-table .tag-badge[title*=\"Subtitles\"]{color:#facc15;background:rgba(250,204,21,0.12)}
.cinema-table .tag-badge[title*=\"Wheelchair\"]{color:#4ade80;background:rgba(74,222,128,0.12)}
.cinema-table .tag-badge[title*=\"Strobe\"]{color:#fb923c;background:rgba(251,146,60,0.12)}
.cinema-table .tag-badge[title*=\"Autism\"]{color:#c084fc;background:rgba(192,132,252,0.12)}
.cinema-table .tag-badge[title*=\"Baby\"],.cinema-table .tag-badge[title*=\"Parent\"]{color:#f472b6;background:rgba(244,114,182,0.12)}
.cinema-table .tag-badge[title*=\"Kids\"]{color:#fbbf24;background:rgba(251,191,36,0.12)}
.cinema-table .tag-badge[title*=\"Silver\"]{color:#94a3b8;background:rgba(148,163,184,0.12)}
.cinema-table .tag-badge[title*=\"Event\"]{color:#f87171;background:rgba(248,113,113,0.12)}
.cinema-table .cinema-cell{font-weight:500;color:var(--text)}
.cinema-table .book-cell{text-align:right;white-space:nowrap}
.cinema-table .table-book-btn{display:inline-block;padding:0.35rem 0.7rem;background:linear-gradient(135deg,var(--cyan),var(--purple));color:#0a0a10;font-weight:600;font-size:0.72rem;border-radius:8px;text-decoration:none;transition:transform var(--transition),box-shadow var(--transition)}
@media(min-width:600px){.cinema-table .table-book-btn{font-size:0.78rem;padding:0.4rem 0.9rem}}
.cinema-table .table-book-btn:hover{transform:scale(1.04);box-shadow:0 4px 15px var(--accent-glow)}
.cert{display:inline-block;width:28px;height:28px;background-position:center;background-repeat:no-repeat;background-size:contain;vertical-align:middle;margin-left:0.4rem}
.cert--u{background-image:url(../certs/cert-u.png)}
.cert--pg{background-image:url(../certs/cert-pg.png)}
.cert--12a{background-image:url(../certs/cert-12a.png)}
.cert--12{background-image:url(../certs/cert-12.png)}
.cert--15{background-image:url(../certs/cert-15.png)}
.cert--18{background-image:url(../certs/cert-18.png)}
.backdrop-wrap{position:absolute;top:0;left:0;width:100%;height:100%;z-index:0;overflow:hidden;opacity:0.15;pointer-events:none}
.backdrop-wrap::after{content:"";position:absolute;inset:0;background:linear-gradient(180deg,rgba(10,10,16,0.7) 0%,rgba(10,10,16,0.9) 100%)}
.backdrop-img{width:100%;height:100%;object-fit:cover}
@media(max-width:680px){.backdrop-wrap{position:relative;height:200px;opacity:0.2}}
.backdrop-wrap{position:absolute;top:0;left:0;width:100%;height:100%;z-index:0;overflow:hidden}
.backdrop-wrap::after{content:'';position:absolute;inset:0;background:linear-gradient(180deg,rgba(10,10,16,0.65) 0%,rgba(10,10,16,0.85) 100%)}
.backdrop-img{width:100%;height:100%;object-fit:cover}
@media(max-width:680px){.backdrop-wrap{height:280px}}
"""


def _youtube_embed_url(trailer_url: str) -> str:
    """Extract YouTube video ID and return nocookie embed URL, or empty string."""
    if not trailer_url:
        return ""
    m = re.search(r"(?:v=|youtu\.be/)([a-zA-Z0-9_-]{11})", trailer_url)
    return f"https://www.youtube-nocookie.com/embed/{m.group(1)}" if m else ""


def build_film_page(
    film_title: str,
    film_slug: str,
    film_details: Dict[str, Any],
    cinemas: List[Tuple[str, str, date, str]],
    showtimes: Optional[List[Dict[str, Any]]] = None,
) -> str:
    """Generate a dedicated HTML page for a single film."""
    poster = film_details.get("poster_url") or ""
    poster_large = film_details.get("poster_large_url") or poster
    backdrop_url = film_details.get("backdrop_url") or ""
    backdrop_html = f'<div class="backdrop-wrap"><img src="{_esc(backdrop_url)}" alt="" class="backdrop-img" loading="lazy" decoding="async"></div>\n' if backdrop_url else ""
    trailer = film_details.get("trailer_url") or ""
    embed_url = _youtube_embed_url(trailer)
    scr_html = f' <span class="screening-badge">{_esc(film_details.get("screening", ""))}</span>' if film_details.get("screening") else ""
    screening_label = film_details.get("screening") or ""
    feature_text = film_details.get("screening_feature") or ""
    overview = film_details.get("overview") or film_details.get("synopsis")
    if not overview:
        screening = film_details.get("screening", "")
        if screening == "RBO":
            overview = "Royal Ballet & Opera broadcast - a world-class production from the Royal Opera House, Covent Garden, screened live at this cinema."
        elif screening == "NT Live":
            overview = "National Theatre Live broadcast - exceptional British theatre captured live and screened at this cinema."
        elif screening:
            overview = f"A special {screening} event at WTW Cinemas. Check the showtimes below for dates and booking."
        else:
            # Check if this is a known non-film event (live band, tribute, comedy etc.)
            tl = film_title.lower()
            if any(s in tl for s in SKIP_TMDB_TERMS):
                overview = "A live event at WTW Cinemas. Check the showtimes below for dates, times, and booking."
            else:
                overview = "Synopsis coming soon."
    runtime = _format_runtime_display(film_details.get("runtime") or "")
    rating = film_details.get("vote_average")
    genres = sorted(set(film_details.get("genres") or []))
    director = film_details.get("director") or ""
    cast = film_details.get("cast") or ""
    bbfc = film_details.get("bbfc") or _extract_bbfc(film_title)
    imdb_id = film_details.get("imdb_id", "")

    stars = _stars_from_rating(rating) if rating is not None else ""
    rating_text = f"{rating:.1f}/10" if rating is not None else ""

    meta_parts = []
    if bbfc:
        meta_parts.append(f'<span class="cert cert--{bbfc.lower()}" title="{_esc(bbfc)}"></span>')
    if runtime:
        meta_parts.append(f"<span>{runtime}</span>")
    if stars:
        meta_parts.append(f'<span class="stars">{stars}</span>')
    if rating_text:
        meta_parts.append(f'<span class="rating-pill">{rating_text}</span>')
    if genres:
        meta_parts.append(f'<span class="genres">{", ".join(genres)}</span>')

    poster_large_src = f"../{poster_large}" if poster_large.startswith("posters/") else poster_large
    poster_src = f"../{poster}" if poster.startswith("posters/") else poster
    poster_large = film_details.get("poster_large_url") or poster
    poster_large_src = f"../{poster_large}" if poster_large.startswith("posters/") else poster_large
    poster_html = (
        f'<img src="{_esc(poster_src)}" alt="Poster for {_esc(film_title)}" loading="lazy">'
        if poster
        else f'<div class="no-poster">No poster available</div>'
    )

    # Backdrop image - placed behind poster in film-layout
    backdrop_url = film_details.get("backdrop_url") or ""
    backdrop_html = (
        f'<div class="backdrop-wrap">\n'
        f'  <img src="{_esc(backdrop_url)}" alt="" class="backdrop-img" loading="lazy" decoding="async">\n'
        f'</div>\n'
    ) if backdrop_url else ""

    trailer_html = (
        f'<div class="trailer-wrap"><iframe src="{_esc(embed_url)}" title="Trailer for {_esc(film_title)}" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen loading="lazy"></iframe></div>'
        if embed_url
        else '<div class="trailer-wrap"><div class="no-trailer">No trailer available</div></div>'
    )

    # Google Calendar "Add to Calendar" link (#5)
    from urllib.parse import quote as _url_quote
    first_rd = cinemas[0][2] if cinemas else date.today()
    gcal_dates = f"{first_rd.strftime('%Y%m%d')}/{first_rd.strftime('%Y%m%d')}"
    gcal_text = _url_quote(film_title)
    gcal_location = _url_quote(f"WTW Cinemas {cinemas[0][0]}" if cinemas else "WTW Cinemas")
    gcal_url = f"https://calendar.google.com/calendar/render?action=TEMPLATE&text={gcal_text}&dates={gcal_dates}&location={gcal_location}"
    gcal_html = f'<a href="{_esc(gcal_url)}" class="cta-btn google-btn" target="_blank" rel="noopener" title="Add to Google Calendar">📅 Add to Calendar</a>'

    # Build cinema showtime table - use whats-on showtimes if available, else coming-soon dates
    table_rows = []
    cinema_set: set = set()
    if showtimes:
        # Use full showtime data from whats-on pages
        for st in showtimes:
            rd = st["date"]
            rd_str = rd.strftime("%a %d %b")
            cinema_name = st['cinema_name']
            cinema_slug = cinema_name.lower().replace(" ", "-")
            cinema_set.add(cinema_name)
            cinema_label = f"WTW {cinema_name}"
            time_str = st.get("time", "")
            screen_num = st.get("screen", 1)
            booking_url = st.get("booking_url", "")
            stags = st.get("tags") or []
            screen_tag = f" <span class=\"screen-badge\">Screen {screen_num}</span>"
            # Accessibility tag badges
            tag_map = {
                "audio description": ("AD", "Audio Description"),
                "subtitles": ("CC", "Subtitles"),
                "wheelchair access": ("WA", "Wheelchair Accessible"),
                "strobe light warning": ("SL", "Strobe Lighting"),
                "autism friendly": ("AF", "Autism Friendly"),
                "parent & baby": ("PB", "Parent & Baby"),
                "kids club": ("KC", "Kids Club"),
                "silver screen": ("SS", "Silver Screen"),
                "event cinema": ("EV", "Event Cinema"),
            }
            tag_badges = ""
            for t in stags:
                tl = t.lower()
                if tl in tag_map:
                    abbr, title = tag_map[tl]
                    tag_badges += f'<span class="tag-badge" title="{_esc(title)}">{abbr}</span> '
            table_rows.append(
                f'<tr data-film-cinema="{_esc(cinema_slug)}"><td class="date-cell">{rd_str}</td>'
                f'<td class="time-cell">{_esc(time_str)}</td>'
                f'<td class="cinema-cell">{_esc(cinema_label)}{screen_tag}{tag_badges}</td>'
                f'<td class="book-cell">{f"<a href=\"{_esc(booking_url)}\" class=\"table-book-btn\" target=\"_blank\" rel=\"noopener\">Book →</a>" if booking_url else ""}</td></tr>'
            )
    else:
        # Fall back to coming-soon release dates
        showings_by_date: Dict[date, List[Tuple[str, str, str]]] = {}
        for cname, furl, rdate, cid in sorted(cinemas, key=lambda x: x[2]):
            showings_by_date.setdefault(rdate, []).append((cname, furl, cid))
        for rd in sorted(showings_by_date.keys()):
            cinemas_on_date = sorted(showings_by_date[rd])
            rd_short = rd.strftime("%a %d %b")
            for cname, furl, cid in cinemas_on_date:
                booking_url = WTW_BASE_URL + furl if furl.startswith("/") else furl
                table_rows.append(
                    f'<tr><td class="date-cell">{rd_short}</td>'
                    f'<td class="cinema-cell">WTW {cname}</td>'
                    f'<td class="book-cell"><a href="{_esc(booking_url)}" class="table-book-btn" target="_blank" rel="noopener">Book →</a></td></tr>'
                )

    now_london = format_london_timestamp()

    # Schema.org Movie structured data
    schema = {
        "@context": "https://schema.org",
        "@type": "Movie",
        "name": film_title,
        "description": overview[:500],
        "image": poster or None,
    }
    if director:
        schema["director"] = {"@type": "Person", "name": director}
    if rating is not None:
        schema["aggregateRating"] = {"@type": "AggregateRating", "ratingValue": rating, "bestRating": 10}
    if genres:
        schema["genre"] = genres
    schema_json = json.dumps(schema, ensure_ascii=False)
    schema_block = f'    <script type="application/ld+json">{schema_json}</script>\n'

    crew_html = (
        f'        <div class="crew">\n'
        + (f'          <p><strong>Director:</strong> {_esc(director)}</p>\n' if director else '')
        + (f'          <p><strong>Starring:</strong> {_esc(cast)}</p>\n' if cast else '')
        + f'        </div>\n'
    ) if (director or cast) else ''

    table_header = '<thead><tr><th>Date</th><th>Time</th><th>Cinema</th><th></th></tr></thead>' if showtimes else '<thead><tr><th>Date</th><th>Cinema</th><th></th></tr></thead>'
    # Cinema filter pills for showtime table
    showtime_filter = ""
    showtime_filter_js = ""
    if showtimes and len(cinema_set) > 1:
        filter_btns = '<button type="button" class="st-filter-btn active" data-st-cinema="all">All</button>\n'
        for cn in sorted(cinema_set):
            slug = cn.lower().replace(" ", "-")
            filter_btns += f'          <button type="button" class="st-filter-btn" data-st-cinema="{_esc(slug)}">{_esc(cn)}</button>\n'
        showtime_filter = (
            f'      <div class="st-filter" role="group" aria-label="Filter by cinema">\n'
            f'        {filter_btns}'
            f'      </div>\n'
        )
        showtime_filter_js = (
            '<script>\n'
            'document.querySelectorAll(".st-filter-btn").forEach(function(btn){'
            'btn.addEventListener("click",function(){'
            'document.querySelectorAll(".st-filter-btn").forEach(function(b){b.classList.remove("active")});'
            'this.classList.add("active");'
            'var cinema=this.getAttribute("data-st-cinema");'
            'document.querySelectorAll("tr[data-film-cinema]").forEach(function(row){'
            'row.style.display=(cinema==="all"||row.getAttribute("data-film-cinema")===cinema)?"":"none"'
            '})'
            '})'
            '});\n'
            '</script>\n'
        )
    # Accessibility key popup - shown inline when showtimes have tag badges
    tag_popup = ""
    tag_popup_js = ""
    if showtimes:
        tag_popup = (
            '<div class="tag-key-popup" id="tag-key-popup" hidden>\n'
            '  <div class="tag-key-overlay"></div>\n'
            '  <div class="tag-key-dialog" role="dialog" aria-label="Accessibility key">\n'
            '    <button type="button" class="tag-key-close" aria-label="Close">&times;</button>\n'
            '    <h3>Accessibility Key</h3>\n'
            '    <dl>\n'
            '      <dt><span class="tag-badge" style="color:#22d3ee;background:rgba(34,211,238,0.12)">AD</span></dt><dd>Audio Description</dd>\n'
            '      <dt><span class="tag-badge" style="color:#facc15;background:rgba(250,204,21,0.12)">CC</span></dt><dd>Subtitles / Closed Captions</dd>\n'
            '      <dt><span class="tag-badge" style="color:#4ade80;background:rgba(74,222,128,0.12)">WA</span></dt><dd>Wheelchair Accessible</dd>\n'
            '      <dt><span class="tag-badge" style="color:#fb923c;background:rgba(251,146,60,0.12)">SL</span></dt><dd>Strobe Lighting warning</dd>\n'
            '      <dt><span class="tag-badge" style="color:#c084fc;background:rgba(192,132,252,0.12)">AF</span></dt><dd>Autism Friendly screening</dd>\n'
            '      <dt><span class="tag-badge" style="color:#f472b6;background:rgba(244,114,182,0.12)">PB</span></dt><dd>Parent &amp; Baby screening</dd>\n'
            '      <dt><span class="tag-badge" style="color:#fbbf24;background:rgba(251,191,36,0.12)">KC</span></dt><dd>Kids Club</dd>\n'
            '      <dt><span class="tag-badge" style="color:#94a3b8;background:rgba(148,163,184,0.12)">SS</span></dt><dd>Silver Screen (over 60s)</dd>\n'
            '      <dt><span class="tag-badge" style="color:#f87171;background:rgba(248,113,113,0.12)">EV</span></dt><dd>Event Cinema</dd>\n'
            '    </dl>\n'
            '  </div>\n'
            '</div>\n'
        )
        tag_popup_js = (
            '<script>\n'
            'var tagPopup=document.getElementById("tag-key-popup");\n'
            'var tagBtn=document.getElementById("tag-key-btn");\n'
            'var tagClose=tagPopup.querySelector(".tag-key-close");\n'
            'var tagOverlay=tagPopup.querySelector(".tag-key-overlay");\n'
            'tagBtn.addEventListener("click",function(){tagPopup.hidden=false});\n'
            'tagClose.addEventListener("click",function(){tagPopup.hidden=true});\n'
            'tagOverlay.addEventListener("click",function(){tagPopup.hidden=true});\n'
            'document.addEventListener("keydown",function(e){if(e.key==="Escape")tagPopup.hidden=true});\n'
            '</script>\n'
            '<script>\n'
            '// Nearest cinema highlight - reorder showtime rows\n'
            '(function(){\n'
            'var coords={'
            + ",".join(f'"{s}":{{lat:{lat},lng:{lng}}}' for s, lat, lng in [("st-austell",50.338,-4.795),("newquay",50.414,-5.075),("wadebridge",50.517,-4.835),("truro",50.263,-5.051)])
            + '};\n'
            'if(!navigator.geolocation)return;\n'
            'navigator.geolocation.getCurrentPosition(function(pos){\n'
            'var best=null,bestDist=Infinity;\n'
            'for(var cn in coords){\n'
            'var c=coords[cn];\n'
            'var d=Math.sqrt(Math.pow(c.lat-pos.coords.latitude,2)+Math.pow(c.lng-pos.coords.longitude,2));\n'
            'if(d<bestDist){bestDist=d;best=cn;}\n'
            '}\n'
            'if(!best)return;\n'
            'var tbody=document.querySelector(".cinema-table tbody");\n'
            'var rows=document.querySelectorAll("tr[data-film-cinema]");\n'
            'var topRows=[],otherRows=[];\n'
            'for(var i=0;i<rows.length;i++){\n'
            'var r=rows[i];\n'
            'if(r.getAttribute("data-film-cinema")===best){\n'
            'r.classList.add("nearest-cinema-row");\n'
            'topRows.push(r);\n'
            '}else{otherRows.push(r);}\n'
            '}\n'
            'if(topRows.length){\n'
            'var frag=document.createDocumentFragment();\n'
            'for(var j=0;j<topRows.length;j++)frag.appendChild(topRows[j]);\n'
            'for(var k=0;k<otherRows.length;k++)frag.appendChild(otherRows[k]);\n'
            'tbody.appendChild(frag);\n'
            'var label=document.createElement("div");\n'
            'label.className="nearest-cinema-label";\n'
            'label.textContent="★ Nearest cinema: "+(best.charAt(0).toUpperCase()+best.slice(1).replace(/-/g," "));\n'
            'var table=document.querySelector(".cinema-table-wrap");\n'
            'table.parentNode.insertBefore(label,table);\n'
            '}\n'
            '},function(){},{timeout:5000,maximumAge:3600000});\n'
            '})();\n'
            '</script>\n'
        )
    cinema_html = (
        f'    <div class="cinema-section">\n'
        f'      <h2>Showtimes & Cinemas <button type="button" id="tag-key-btn" class="tag-key-btn" aria-label="Accessibility key" title="Accessibility key">ⓘ</button></h2>\n'
        + showtime_filter +
        f'      <div class="cinema-table-wrap">\n'
        f'        <table class="cinema-table">\n'
        f'          {table_header}\n'
        f'          <tbody>\n'
        + "\n".join(table_rows) +
        f'\n          </tbody>\n'
        f'        </table>\n'
        f'      </div>\n'
        + showtime_filter_js +
        tag_popup +
        tag_popup_js +
        f'    </div>\n'
    ) if table_rows else ''

    og_image = f'  <meta property="og:image" content="{_esc(poster)}">\n' if poster else ''
    twitter_card = 'summary_large_image' if poster else 'summary'

    return (
        '<!DOCTYPE html>\n<html lang="en">\n<head>\n'
        '  <meta charset="utf-8">\n'
        '  <meta name="viewport" content="width=device-width, initial-scale=1">\n'
        f'  <title>{_esc(film_title)} - WTW Cinemas</title>\n'
        f'  <meta name="description" content="{_esc(overview[:160])}">\n'
        f'  <meta property="og:title" content="{_esc(film_title)} - WTW Cinemas">\n'
        f'  <meta property="og:description" content="{_esc(overview[:200])}">\n'
        f'  <meta property="og:type" content="website">\n'
        f'  {og_image}'
        f'  <meta property="og:url" content="https://evenwebb.github.io/wtw-cinemas/films/{film_slug}.html">\n'
        f'  <meta name="twitter:card" content="{twitter_card}">\n'
        '  <link rel="icon" href="data:image/svg+xml,<svg xmlns=\'http://www.w3.org/2000/svg\' viewBox=\'0 0 100 100\'><text y=\'.9em\' font-size=\'90\'>🎬</text></svg>">\n'
        '  <link rel="preconnect" href="https://fonts.googleapis.com">\n'
        '  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>\n'
        '  <link href="https://fonts.googleapis.com/css2?family=Space+Grotesk:wght@400;600;700&display=swap" rel="stylesheet">\n'
        f'  <style>\n{FILM_CSS}\n  </style>\n'
        '</head>\n<body>\n'
        '  <div class="bg-mesh" aria-hidden="true"></div>\n'
        + backdrop_html +
        '  <div class="page">\n'
        '    <a href="../" class="back-btn">← Back to all premieres</a>\n'
        '    <div class="film-layout">\n'
        f'      <div class="poster">{poster_html}</div>\n'
        '      <div class="film-info">\n'
        f'        <h1>{_esc(film_title)} {_cert_span(bbfc)}{scr_html}</h1>\n'
        f'        <div class="meta">{"".join(meta_parts)}</div>\n'
        f'        <div class="synopsis">{_esc(overview)}</div>\n'
        f'        <div class="links">\n'
        + (f'          <a href="https://www.imdb.com/title/{imdb_id}/" class="ext-link" target="_blank" rel="noopener">IMDb</a>\n' if imdb_id else '')
        + (f'          <a href="https://www.rottentomatoes.com/search?search={_esc(film_title)}" class="ext-link" target="_blank" rel="noopener">Rotten Tomatoes</a>\n')
        + (f'          <a href="https://trakt.tv/search?query={_esc(film_title)}" class="ext-link" target="_blank" rel="noopener">Trakt</a>\n')
        + f'        </div>\n'
        + schema_block + crew_html +
        f'    </div>\n'
        f'  </div>\n'
        f'    <div class="trailer-section">\n'
        f'      <h2>Trailer</h2>\n'
        f'      {trailer_html}\n'
        f'    </div>\n'
        + cinema_html +
        f'    <div style="text-align:center;margin:1.5rem 0">{gcal_html}</div>\n'
        '    <footer>\n'
        '      <p>An open source fan-made project. Not affiliated with WTW Cinemas.</p>\n'
        '      <div style="margin-top:0.75rem">\n'
        '        <a href="https://wtwcinemas.co.uk/">WTW Cinemas</a>\n'
        '        <span aria-hidden="true"> · </span>\n'
        '        <a href="../">All premieres</a>\n'
        '      </div>\n'
        f'      <p class="footer-updated">Last updated: {now_london}</p>\n'
        '    </footer>\n'
        '  </div>\n'
        '</body>\n</html>'
    )


# ── Validation ─────────────────────────────────────────────────────────────────
def validate_configuration() -> None:
    if NOTIFICATIONS.get("enabled") and NOTIFICATIONS.get("alarms"):
        tp = re.compile(r"^([01]?\d|2[0-3]):[0-5]\d$")
        if not tp.match(NOTIFICATION_TIME):
            raise ValueError(
                f"Invalid NOTIFICATION_TIME '{NOTIFICATION_TIME}'. Must be HH:MM."
            )
        for alarm in NOTIFICATIONS["alarms"]:
            if "time" in alarm and not tp.match(alarm["time"]):
                raise ValueError(
                    f"Invalid alarm time '{alarm['time']}'. Must be HH:MM."
                )
            if "days_before" not in alarm and "hours_before" not in alarm:
                raise ValueError(
                    "Each alarm must have 'days_before' or 'hours_before'."
                )

    if CACHE_EXPIRY_DAYS < 1:
        raise ValueError(f"CACHE_EXPIRY_DAYS must be >= 1, got {CACHE_EXPIRY_DAYS}")
    if not any(c["enabled"] for c in CINEMAS.values()):
        raise ValueError("At least one cinema must be enabled.")


# ── Main ───────────────────────────────────────────────────────────────────────
def main() -> None:
    try:
        validate_configuration()
    except ValueError as e:
        logger.error("Config error: %s", e)
        print(f"Configuration Error: {e}")
        sys.exit(1)

    enabled_cinemas = {k: v for k, v in CINEMAS.items() if v["enabled"]}
    if not enabled_cinemas:
        print("Error: No cinemas enabled.")
        sys.exit(1)

    start_time = datetime.now(timezone.utc)
    print(f"Scraping {len(enabled_cinemas)} cinema(s): "
          f"{', '.join(c['name'] for c in enabled_cinemas.values())}\n")

    # Load film-detail cache (shared across threads)
    cache = load_cache()
    all_films: List[Tuple] = []

    # ── Parallel cinema scraping ──────────────────────────────────────────
    def scrape_cinema(cid: str, info: dict) -> List[Tuple]:
        sess = _session()
        results = []
        try:
            films = extract_films(info["url"], info["name"], cache, session=sess)
            for f in films:
                results.append((*f, cid))
        except Exception as e:
            logger.error("Error scraping %s: %s", info["name"], e)
            print(f"✗ {info['name']}: Error - {e}")
        finally:
            sess.close()
        return results

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as ex:
        futures = {ex.submit(scrape_cinema, cid, info): cid for cid, info in enabled_cinemas.items()}
        for fut in as_completed(futures, timeout=HTTP_TIMEOUT * 3):
            cid = futures[fut]
            try:
                films = fut.result(timeout=HTTP_TIMEOUT)
                all_films.extend(films)
                print(f"✓ {enabled_cinemas[cid]['name']}: Found {len(films)} film(s)")
            except Exception as e:
                logger.error("Thread failed for %s: %s", enabled_cinemas[cid]["name"], e)
                print(f"✗ {enabled_cinemas[cid]['name']}: Error - {e}")

    save_cache(cache)

    # ── Parallel whats-on scraping ──────────────────────────────────────────
    def scrape_whats_on(cid: str, info: dict) -> List[Dict]:
        sess = _session()
        try:
            return scrape_cinema_whats_on(cid, info["name"], session=sess)
        except Exception as e:
            logger.error("Error scraping whats-on %s: %s", info["name"], e)
            print(f"✗ {info['name']} whats-on: Error - {e}")
            return []
        finally:
            sess.close()

    whats_on_data: Dict[str, List[Dict]] = {}  # normalized_title -> [showtime dicts]
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as wex:
        wfutures = {wex.submit(scrape_whats_on, cid, info): cid for cid, info in enabled_cinemas.items()}
        for fut in as_completed(wfutures, timeout=HTTP_TIMEOUT * 3):
            cid = wfutures[fut]
            try:
                wfilms = fut.result(timeout=HTTP_TIMEOUT)
                for wf in wfilms:
                    key = _normalize_title_for_match(wf["title"])
                    if key not in whats_on_data:
                        whats_on_data[key] = []
                    whats_on_data[key].append(wf)
                print(f"✓ {enabled_cinemas[cid]['name']} whats-on: Found {len(wfilms)} film(s)")
            except Exception as e:
                logger.error("Whats-on thread failed for %s: %s", enabled_cinemas[cid]["name"], e)
                print(f"✗ {enabled_cinemas[cid]['name']} whats-on: Error - {e}")

    # ── TMDb enrichment ───────────────────────────────────────────────────
    api_key = (os.environ.get("TMDB_API_KEY") or "").strip()
    tmdb_cache: Dict[str, dict] = load_tmdb_cache()

    # Always enrich all_films from cache (covers runs without API key)
    _CACHE_FIELDS = (
        "overview", "genres", "vote_average", "director", "cast",
        "poster_url", "poster_large_url", "backdrop_url", "runtime",
        "trailer_url", "imdb_id",
    )
    for i, (rd, title, cname, furl, fdetails, cid) in enumerate(all_films):
        k = _tmdb_cache_key(title)
        if k in tmdb_cache:
            tc = tmdb_cache[k]
            fdetails = dict(fdetails)
            for field in _CACHE_FIELDS:
                val = tc.get(field)
                if val and not fdetails.get(field):
                    if field == "vote_average" and float(val) == 0.0:
                        continue
                    fdetails[field] = val
            all_films[i] = (rd, title, cname, furl, fdetails, cid)

    if api_key:
        sess = _session()
        unique_by_key: Dict[str, Tuple[str, str, List[int]]] = {}
        for i, (rd, title, cname, furl, fdetails, cid) in enumerate(all_films):
            k = _tmdb_cache_key(title)
            if k not in unique_by_key:
                unique_by_key[k] = (title, furl, [i])
            else:
                unique_by_key[k][2].append(i)

        # TMDb lookups in parallel for unique films
        def _tmdb_enrich(key: str, title: str, url: str) -> Dict[str, Any]:
            return enrich_film_tmdb(title, url, api_key, tmdb_cache, session=sess)

        enrich_futures: Dict[Any, str] = {}
        with ThreadPoolExecutor(max_workers=min(8, MAX_WORKERS * 2)) as tex:
            for k, (title, furl, indices) in unique_by_key.items():
                enrich_futures[tex.submit(_tmdb_enrich, k, title, furl)] = k
            for fut in as_completed(enrich_futures):
                k = enrich_futures[fut]
                try:
                    extra = fut.result()
                except Exception:
                    extra = {}
                if not extra:
                    continue
                _ENRICH_FIELDS = (
                    "overview", "genres", "vote_average", "director", "cast",
                    "poster_url", "poster_large_url", "backdrop_url", "runtime",
                    "trailer_url", "imdb_id",
                )
                for i in unique_by_key[k][2]:
                    rd, t, cname, furl, fdetails, cid = all_films[i]
                    fdetails = dict(fdetails)
                    for field in _ENRICH_FIELDS:
                        val = extra.get(field)
                        if val or (field == "vote_average" and val is not None):
                            fdetails[field] = val
                    all_films[i] = (rd, t, cname, furl, fdetails, cid)
        # Also enrich unique whats-on films not already in unique_by_key
        whats_on_unique: Dict[str, Tuple[str, str]] = {}
        for norm_title, wf_list in whats_on_data.items():
            for wf in wf_list:
                k = _tmdb_cache_key(wf["title"])
                if k not in unique_by_key and k not in whats_on_unique:
                    whats_on_unique[k] = (wf["title"], wf["film_url"])

        if whats_on_unique:
            wo_enrich_futures: Dict[Any, str] = {}
            with ThreadPoolExecutor(max_workers=min(8, MAX_WORKERS * 2)) as tex:
                for k, (title, furl) in whats_on_unique.items():
                    wo_enrich_futures[tex.submit(_tmdb_enrich, k, title, furl)] = k
                for fut in as_completed(wo_enrich_futures):
                    k = wo_enrich_futures[fut]
                    try:
                        extra = fut.result()
                    except Exception:
                        extra = {}
                    if extra:
                        tmdb_cache.setdefault(k, {}).update({**extra, "cached_at": datetime.now().isoformat()})
        sess.close()
        save_tmdb_cache(tmdb_cache)
        logger.info("TMDb enrichment done: %d coming-soon + %d whats-on unique films",
                     len(unique_by_key), len(whats_on_unique))
    else:
        logger.info("TMDB_API_KEY not set; scraping without TMDb enrichment")

    if not all_films:
        logger.warning("No films found across any cinema")
        print("\nWarning: No films found across any cinema")
        sys.exit(1)

    # ── Fingerprint check ────────────────────────────────────────────────────
    fp = _compute_fingerprint(all_films)
    prev_fp = _load_fingerprint()
    if fp == prev_fp and not os.environ.get("FORCE_REBUILD"):
        elapsed = (datetime.now(timezone.utc) - start_time).total_seconds()
        print(f"\nFingerprint unchanged - nothing new. ({elapsed:.1f}s)")
        return

    # ── Health check ─────────────────────────────────────────────────────────
    if not _health_check(all_films, enabled_cinemas):
        logger.error("Health check failed - exiting before generating output")
        print("Error: Health check failed. Check cinema_log.txt for details.")
        sys.exit(1)

    # Sort by date then cinema
    all_films.sort(key=lambda x: (x[0], x[2]))

    # Group by cinema
    films_by_cinema: Dict[str, List] = {}
    for f in all_films:
        films_by_cinema.setdefault(f[5], []).append(f)

    out_dir = Path(OUTPUT_DIR)
    out_dir.mkdir(parents=True, exist_ok=True)

    # Remove legacy .ics files without wtw- prefix
    for old in out_dir.glob("*.ics"):
        if not old.name.startswith("wtw-"):
            old.unlink()
            logger.info("Removed legacy %s", old.name)

    # Write per-cinema .ics files
    for cid in enabled_cinemas:
        cname = enabled_cinemas[cid]["name"]
        cf = films_by_cinema.get(cid, [])
        events = []
        for rd, title, cn, furl, fdetails, _ in cf:
            events.append(make_ics_event(rd, title, cn, furl, fdetails))
        header = [
            "BEGIN:VCALENDAR",
            "VERSION:2.0",
            "PRODID:-//WTW Cinemas//EN",
            "CALSCALE:GREGORIAN",
            "METHOD:PUBLISH",
            "REFRESH-INTERVAL;VALUE=DURATION:PT12H",
            "X-PUBLISHED-TTL:PT12H",
            f"X-WR-CALNAME:WTW {cname} Movie Premieres",
            f"X-WR-CALDESC:Upcoming movie premieres at WTW Cinemas {cname}",
        ]
        if CALENDAR_TIMEZONE.strip():
            header.append(f"X-WR-TIMEZONE:{CALENDAR_TIMEZONE.strip()}")
        ics = ICAL_NEWLINE.join(header) + ICAL_NEWLINE + "".join(events) + f"END:VCALENDAR{ICAL_NEWLINE}"
        (out_dir / f"wtw-{cid}.ics").write_text(ics, encoding="utf-8")
        logger.info("Wrote %s (%d events)", f"wtw-{cid}.ics", len(events))

    _save_sequence_state()

    # ── Release stats ─────────────────────────────────────────────────────
    today = date.today()
    unique_releases = set((f[0], f[1]) for f in all_films)
    prev_history = load_release_history()
    new_releases = unique_releases - prev_history
    # Films first seen in the last 7 days get a "New" badge
    week_ago = today - timedelta(days=7)
    new_slugs: set = set()
    for rd, title in new_releases:
        if rd >= week_ago:
            new_slugs.add(_tmdb_cache_key(title))
    release_history = prev_history | unique_releases
    save_release_history(release_history)

    past_30 = today - timedelta(days=30)
    stats = {
        "past_30_days": sum(1 for d, _ in release_history if past_30 <= d <= today),
        "ytd_past": sum(1 for d, _ in release_history if d.year == today.year and d < today),
        "this_month": sum(1 for d, _ in unique_releases if d.year == today.year and d.month == today.month and d >= today),
        "this_year": sum(1 for d, _ in unique_releases if d.year == today.year and d >= today),
        "total_upcoming": sum(1 for d, _ in unique_releases if d >= today),
    }

    # Build now-showing list from whats-on data for index page
    today = date.today()
    now_showing_films: List[Dict[str, Any]] = []
    for norm_title, wf_list in whats_on_data.items():
        all_st = []
        for wf in wf_list:
            all_st.extend(wf.get("showtimes", []))
        if not all_st:
            continue
        # Film is "now showing" if it has any showtimes this week
        min_date = min(st["date"] for st in all_st)
        max_date = max(st["date"] for st in all_st)
        has_screening = bool(wf_list[0].get("screening", ""))
        if min_date > today + timedelta(days=7) and not has_screening:
            continue
        cinemas_set = sorted(set(st.get("cinema_name", "") for st in all_st))
        slug = _tmdb_cache_key(wf_list[0]["title"])
        poster = ""
        # Check TMDb cache first (now includes whats-on enrichments)
        if slug in tmdb_cache:
            poster = tmdb_cache[slug].get("poster_url", "") or ""
        # Also check all_films detail
        if not poster:
            for rd, t, cname, furl, fdetails, cid in all_films:
                if _tmdb_cache_key(t) == slug:
                    poster = fdetails.get("poster_url", "")
                    if poster:
                        break
        # Fallback to cinema poster from whats-on data
        if not poster:
            poster = wf_list[0].get("poster_url", "") or ""
        now_showing_films.append({
            "title": wf_list[0]["title"],
            "slug": slug,
            "cinemas": cinemas_set,
            "showtimes": all_st,
            "min_date": min_date,
            "poster": poster,
            "screening": wf_list[0].get("screening", ""),
        })
    now_showing_films.sort(key=lambda f: (f["min_date"], f["title"]))

    # ── Special Events ─────────────────────────────────────────────────────
    special_events = [f for f in now_showing_films if f.get("screening")]
    special_events.sort(key=lambda f: (f.get("screening", ""), f["min_date"]))

    # Write index.html
    html = build_index_html(enabled_cinemas, films_by_cinema, stats=stats,
                            now_showing_live=now_showing_films,
                            special_events=special_events,
                            new_slugs=new_slugs)
    (out_dir / "index.html").write_text(html, encoding="utf-8")
    logger.info("Wrote %s/index.html", OUTPUT_DIR)

    # ── Per-film detail pages ────────────────────────────────────────────────
    films_dir = out_dir / "films"
    films_dir.mkdir(parents=True, exist_ok=True)
    # Deduplicate films by slug; collect cinemas showing each film
    film_pages: Dict[str, Dict[str, Any]] = {}
    for rd, title, cname, furl, fdetails, cid in all_films:
        slug = _tmdb_cache_key(title)
        if slug not in film_pages:
            # Copy to avoid mutating all_films entries
            merged = dict(fdetails)
            film_pages[slug] = {
                "title": title, "details": merged, "cinemas": [],
                "release_date": rd,
            }
        film_pages[slug]["cinemas"].append((cname, furl, rd, cid))
        # Merge details from entries with more data (operate on our copy)
        existing = film_pages[slug]["details"]
        for key in ("overview", "poster_url", "poster_large_url", "backdrop_url", "trailer_url", "director", "cast", "runtime"):
            if not existing.get(key) and fdetails.get(key):
                existing[key] = fdetails[key]

    # Merge whats-on films into film_pages (they have showtimes but not coming-soon details)
    now_showing_entries: Dict[str, Dict[str, Any]] = {}
    for norm_title, wf_list in whats_on_data.items():
        for wf in wf_list:
            slug = _tmdb_cache_key(wf["title"])
            if slug not in now_showing_entries:
                now_showing_entries[slug] = {
                    "title": wf["title"], "slug": slug,
                    "details": {
                        "screening": wf.get("screening", ""),
                        "screening_feature": wf.get("screening_feature", ""),
                        "poster_url": wf.get("poster_url", ""),
                    },
                    "cinemas": [],
                    "release_date": date.today(),
                }
            now_showing_entries[slug]["cinemas"].append(
                (wf["cinema_name"], wf["film_url"], date.today(), wf["cinema_id"])
            )
    # Deduplicate showtimes per slug for detail pages
    showtimes_by_slug: Dict[str, List[Dict]] = {}
    for norm_title, wf_list in whats_on_data.items():
        for wf in wf_list:
            slug = _tmdb_cache_key(wf["title"])
            if slug not in showtimes_by_slug:
                showtimes_by_slug[slug] = []
            showtimes_by_slug[slug].extend(wf.get("showtimes", []))

    # Add now-showing films not already in film_pages
    for slug, entry in now_showing_entries.items():
        if slug not in film_pages:
            film_pages[slug] = entry

    # Enrich whats-on films with TMDb data from cache
    for slug, page in film_pages.items():
        if slug in tmdb_cache and not page["details"].get("overview"):
            tc = tmdb_cache[slug]
            for field in ("overview", "genres", "vote_average", "director", "cast",
                          "poster_url", "poster_large_url", "backdrop_url", "runtime",
                          "trailer_url", "imdb_id"):
                val = tc.get(field)
                if val and not page["details"].get(field):
                    if field == "vote_average" and float(val) == 0.0:
                        continue
                    page["details"][field] = val

    for slug, page in film_pages.items():
        film_showtimes = sorted(
            showtimes_by_slug.get(slug, []),
            key=lambda s: (s["date"], s["time"], s.get("cinema_name", ""))
        )
        page_html = build_film_page(
            page["title"], slug, page["details"], page["cinemas"],
            showtimes=film_showtimes or None
        )
        (films_dir / f"{slug}.html").write_text(page_html, encoding="utf-8")
    logger.info("Wrote %d film detail pages to %s/films/", len(film_pages), OUTPUT_DIR)

    # ── Poster downloads ─────────────────────────────────────────────────────
    poster_sess = _session()
    try:
        # Build slug→pages map once for O(1) lookup
        slug_to_page: Dict[str, tuple] = {}
        for slug, page in film_pages.items():
            poster_url = page["details"].get("poster_url", "")
            if poster_url.startswith("http"):
                slug_to_page[slug] = (poster_url, page)
        if slug_to_page:
            with ThreadPoolExecutor(max_workers=min(4, MAX_WORKERS)) as pex:
                futures = {pex.submit(_download_poster, url, slug, poster_sess): slug for slug, (url, _) in slug_to_page.items()}
                updated_slugs: set = set()
                for fut in as_completed(futures):
                    slug = futures[fut]
                    try:
                        local = fut.result() or ""
                    except Exception:
                        local = ""
                    if local:
                        slug_to_page[slug][1]["details"]["poster_url"] = local
                        updated_slugs.add(slug)
            # Only rewrite film pages that got poster updates
            for slug in updated_slugs:
                page = film_pages[slug]
                film_showtimes = showtimes_by_slug.get(slug, [])
                page_html = build_film_page(page["title"], slug, page["details"], page["cinemas"],
                    showtimes=film_showtimes or None)
                (films_dir / f"{slug}.html").write_text(page_html, encoding="utf-8")
    finally:
        poster_sess.close()

    # ── Cert images ──────────────────────────────────────────────────────────
    _download_cert_images()

    # ── Cinema pages ─────────────────────────────────────────────────────────
    # Build all_films_list for cinema pages (same as in build_index_html)
    _all_films_list = []
    _film_entries: Dict[str, Dict[str, Any]] = {}
    for cf in films_by_cinema.values():
        for rd, title, cname, furl, fdetails, cid in cf:
            slug = _tmdb_cache_key(title)
            if slug not in _film_entries:
                _film_entries[slug] = {
                    "title": title, "release_date": rd, "slug": slug,
                    "details": fdetails, "cinemas": {},
                }
            _film_entries[slug]["cinemas"][cname] = (furl, rd)
            if rd < _film_entries[slug]["release_date"]:
                _film_entries[slug]["release_date"] = rd
    _all_films_list = sorted(_film_entries.values(), key=lambda f: f["release_date"])
    cs_films_sorted = sorted(
        [f for f in _all_films_list if f["release_date"] > today],
        key=lambda f: f["release_date"]
    )
    for cid, info in enabled_cinemas.items():
        page_html = build_cinema_page(cid, info, now_showing_films, cs_films_sorted)
        (out_dir / f"{cid}.html").write_text(page_html, encoding="utf-8")
    logger.info("Wrote %d cinema pages", len(enabled_cinemas))

    # ── Sitemap ───────────────────────────────────────────────────────────────
    film_slugs = sorted(film_pages.keys())
    sitemap = generate_sitemap(film_slugs, list(enabled_cinemas.keys()))
    (out_dir / "sitemap.xml").write_text(sitemap, encoding="utf-8")
    logger.info("Wrote sitemap.xml with %d URLs", len(film_slugs) + len(enabled_cinemas) + 1)

    # ── Save fingerprint ─────────────────────────────────────────────────────
    _save_fingerprint(fp)

    elapsed = (datetime.now(timezone.utc) - start_time).total_seconds()
    print(f"\n✓ Created {OUTPUT_DIR}/ with {len(films_by_cinema)} calendar(s), {len(film_pages)} film page(s), {len(enabled_cinemas)} cinema page(s), sitemap.xml, and index page ({elapsed:.1f}s)\n")

    for d, group in groupby(all_films, key=lambda x: x[0]):
        print(f"{d.strftime('%d %B %Y')}:")
        for _, title, cname, _, _, _ in group:
            print(f"  • {title} @ {cname}")


if __name__ == "__main__":
    main()
