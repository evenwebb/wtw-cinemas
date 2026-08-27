#!/usr/bin/env python3
"""WTW Cinemas Calendar Scraper.

Scrapes upcoming film releases from WTW Cinemas and generates per-cinema
iCalendar feeds plus an index page for GitHub Pages.
"""
from __future__ import annotations

import hashlib
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
import atexit as _atexit

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
# TMDb ratings from fewer votes swing wildly (a 3-vote film can show 10/10)
MIN_TMDB_VOTES = 30
MIN_SYNOPSIS_LENGTH = 50
MAX_SYNOPSIS_LENGTH = 500
SYNOPSIS_SKIP_TERMS = ["cookie", "privacy", "terms", "wheelchair", "audio description"]
MAX_WORKERS = min(4, os.cpu_count() or 4)

# Import shared constants from the split-out module
from shared_constants import (  # noqa: E402
    _tmdb_cache_key, BBFC_PATTERN, CERT_CDN_MAP, CERT_IMAGES, CERTS_DIR,
    CINEMA_ADDRESSES, FINGERPRINT_FILE, HEALTH_MIN_CINEMAS, HEALTH_MIN_FILMS,
    ICAL_LINE_LENGTH, NOTIFICATIONS, NOTIFICATION_TIME,
    POSTERS_DIR, SKIP_TMDB_TERMS, WTW_CERT_BASE,
)

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


# Screening labels that denote alternative/event content — the film *is* the
# event (opera, ballet, theatre, concert, Q&A) as opposed to a Hollywood film
# shown in a special format (Toddler Cinema, Silver Screen, Double Bill, etc.).
EVENT_CINEMA_SCREENINGS = {"NT Live", "RBO", "Event Cinema", "Q&A"}

# Extra title hints for alternative content that carries no screening label.
# Covers the RBO / NT Live / exhibition / concert patterns WTW actually lists,
# plus the shared Merlin-style hints. ("Music" TMDb genre is deliberately
# ignored: it also covers Hollywood musicals like La La Land, which must stay
# under Now Showing.)
EVENT_CINEMA_TITLE_HINTS = (
    "concert", "met opera", "royal opera", "royal ballet", "bolshoi",
    "glyndebourne", "encore", "rieu",
    "national theatre live", "nt live", "exhibition on screen",
    "the musical", "the play", "q&a",
)


def _is_event_cinema(title: str, screening: str = "", categories=None, showtimes=None) -> bool:
    """Classify a now-showing film as event cinema / special content vs a
    regular Hollywood release. Uses the screening label, WTW's own per-showtime
    "Event cinema" tag, then falls back to title hints."""
    if screening in EVENT_CINEMA_SCREENINGS:
        return True
    if "Event Cinema" in (categories or []):
        return True
    for st in (showtimes or []):
        for tag in (st.get("tags") or []):
            if "event cinema" in (tag or "").lower():
                return True
    tl = (title or "").lower()
    if any(hint in tl for hint in EVENT_CINEMA_TITLE_HINTS):
        return True
    return False

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

NOTIFICATIONS: Dict[str, Any] = {"enabled": False, "alarms": []}

# BBFC / cinema / health constants are in shared_constants.py

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
        tmp = RELEASE_HISTORY_PATH + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(kept, f, ensure_ascii=False)
        os.replace(tmp, RELEASE_HISTORY_PATH)
        logger.info("Saved release history: %d entries", len(kept))
    except OSError as e:
        logger.warning("Release history save failed: %s", e)


# _tmdb_cache_key is now in shared_constants.py

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

    # Auto-advance into next year if parsed date is in the past (cap at 1 year)
    if parsed < date.today():
        try:
            parsed = date(year + 1, month, day)
        except ValueError:
            pass
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


def _atomic_write_text(path: Path, content: str, encoding: str = "utf-8") -> None:
    """Write content atomically: temp file then rename. Logs and continues on error."""
    try:
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_text(content, encoding=encoding)
        tmp.replace(path)
    except OSError as e:
        logger.error("Failed to write %s: %s", path, e)


def _atomic_write_bytes(path: Path, content: bytes) -> None:
    """Write bytes atomically: temp file then rename. Logs and continues on error."""
    try:
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_bytes(content)
        tmp.replace(path)
    except OSError as e:
        logger.error("Failed to write %s: %s", path, e)


# ── Film detail scraping ───────────────────────────────────────────────────────
_film_cache_lock = threading.Lock()
_tmdb_cache_lock = threading.Lock()


def fetch_film_details(
    film_url: str, cache: Dict[str, dict], session: Optional[requests.Session] = None
) -> Dict[str, str]:
    """Fetch runtime, cast, synopsis from a film page. Uses cache when available."""
    details: Dict[str, str] = {"runtime": "", "cast": "", "synopsis": "", "director": "", "title": ""}
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

        # Title: from <title> tag or <h1>
        if soup.title:
            title_text = soup.title.get_text(strip=True)
            # Strip "Film Times and Tickets | WTW Cinemas" suffix
            for sep in (" Film Times", " | WTW", " | The WTW"):
                if sep in title_text:
                    title_text = title_text.split(sep)[0].strip()
            if title_text:
                details["title"] = title_text
        if not details.get("title"):
            h1 = soup.select_one("h1")
            if h1:
                details["title"] = h1.get_text(strip=True)

        # Runtime: match "119 minutes" etc.
        for text in soup.stripped_strings:
            m = RUNTIME_RE.search(text)
            if m:
                details["runtime"] = f"{m.group(1)} min"
                break

        # Cast & Director: find <li> elements with "Starring:" or "Directed by:"
        for li in soup.find_all("li"):
            li_text = li.get_text(" ", strip=True)
            if not details.get("cast") and "starring" in li_text.lower():
                rest = li_text.split(":", 1)[-1].strip()
                if len(rest) > 3:
                    details["cast"] = rest
            if not details.get("director") and "directed by" in li_text.lower():
                rest = li_text.split(":", 1)[-1].strip()
                if len(rest) > 1:
                    details["director"] = rest
        # Fallback: try stripped_strings for cast
        if not details.get("cast"):
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


def _extract_title_from_slug(slug: str) -> str:
    """Convert a URL slug to a readable title."""
    if not slug:
        return ""
    # Hyphens to spaces, title case
    title = slug.replace("-", " ").title()
    # Fix common words
    for word in ("The", "Of", "In", "On", "And", "At", "For", "To", "By", "A", "An", "Is", "It", "Or", "As", "Be", "No"):
        title = title.replace(f" {word} ", f" {word.lower()} ")
    # Fix first word lowercase
    parts = title.split()
    if parts and parts[0].lower() in ("the", "a", "an"):
        pass  # Keep first word title case
    return title.strip()


def extract_films(
    url: str,
    cinema_name: str,
    cache: Dict[str, dict],
    session: Optional[requests.Session] = None,
) -> List[Tuple[date, str, str, str, Dict[str, str]]]:
    """Scrape film listing from a cinema's coming-soon page.

    Current site structure (2026): div[class^='filmecatte'] cards with
    film links containing slug-based titles. Release dates in sibling
    .poster-film-content .running-time containers.
    """
    logger.info("Scraping: %s (%s)", url, cinema_name)
    resp = fetch_with_retries(url, session=session)
    soup = BeautifulSoup(resp.text, "html.parser")

    films: List[Tuple[date, str, str, str, Dict[str, str]]] = []
    seen: set = set()

    film_cards = soup.select("div[class^='filmecatte']")
    if not film_cards:
        logger.warning("No film cards found on coming-soon page for %s", cinema_name)
        return films

    for card in film_cards:
        # Find film link — could be in card or a parent
        film_url = ""
        for el in [card] + list(card.parents)[:5]:
            link = el.select_one("a[href*='/film/']")
            if link:
                film_url = link.get("href", "")
                break
        if film_url and not film_url.startswith("http"):
            film_url = WTW_BASE_URL + film_url

        # Extract slug from URL for title
        slug = film_url.rstrip("/").split("/")[-1] if film_url else ""
        title = _extract_title_from_slug(slug)

        if not title or title.lower() in ("coming soon", "film", "cinema", ""):
            continue

        # Release date from .running-time in parent chain
        release_date = None
        for el in [card] + list(card.parents)[:6]:
            rt = el.select_one(".running-time")
            if rt:
                rt_text = rt.get_text(strip=True).replace("Expected:", "").strip()
                release_date = parse_date(rt_text)
                if release_date:
                    break

        if not release_date:
            continue

        # BBFC cert
        bbfc_rating = ""
        for el in [card] + list(card.parents)[:6]:
            cert_img = el.select_one(".film-certificate img")
            if cert_img:
                cert_src = cert_img.get("src", "")
                for cert_name, cert_file in CERT_IMAGES.items():
                    if cert_file in cert_src or CERT_CDN_MAP.get(cert_file, "") in cert_src:
                        bbfc_rating = cert_name
                        break
                if bbfc_rating:
                    break

        # Genre from card class
        genre = ""
        for cls in card.get("class", []):
            if cls.startswith("filmecatte"):
                genre = cls.replace("filmecatte", "").strip()
                break

        # Poster image from card or parent
        poster_url = ""
        for el in [card] + list(card.parents)[:4]:
            for img in el.select("img"):
                src = img.get("src", "")
                alt = img.get("alt", "")
                # Skip cert icons, accessibility icons, format badges
                if any(skip in src.lower() for skip in (
                    "filmcerts", "cert-", "modifier", "icon", "2d.png",
                    "3d.png", "wheelchair", "ccap", "audio-des",
                    "closed-caption", "strobe",
                )):
                    continue
                if alt in ("2D", "3D", "Closed Caption Subtitle Glasses Available",
                           "Audio Description Headsets Available", "Wheelchair Access",
                           "Contains a sequence of flashing lights.", "Laser Projection",
                           "Autism Friendly Film", "background-image"):
                    continue
                if "cdn.taposapp.com" in src or "poster" in src.lower():
                    poster_url = src
                    break
            if poster_url:
                break

        # Synopsis from card text
        card_text = card.get_text(" ", strip=True)
        synopsis = card_text[:MAX_SYNOPSIS_LENGTH] if len(card_text) >= MIN_SYNOPSIS_LENGTH else ""

        # Screening label
        clean_title, screening = extract_screening_label(title)

        key = (release_date, clean_title or title, cinema_name, film_url)
        if key not in seen:
            film_details: Dict[str, str] = {
                "bbfc": bbfc_rating,
                "screening": screening,
                "synopsis": synopsis,
                "genre": genre,
                "poster_url": poster_url,
                "source": "coming_soon_card",
            }
            if film_url:
                page_details = fetch_film_details(film_url, cache, session)
                if page_details:
                    # Use the real title from film page if available
                    page_title = page_details.get("title", "")
                    if page_title:
                        clean_title = TITLE_CLEAN_RE.sub("", page_title)
                    film_details.update(page_details)
            films.append((release_date, clean_title or title, cinema_name, film_url, film_details))
            seen.add(key)
            logger.info("  %s - %s (%s)", clean_title or title, release_date, cinema_name)

    logger.info("  coming-soon %s: %d films", cinema_name, len(films))
    return films


def scrape_cinema_whats_on(
    cinema_id: str,
    cinema_name: str,
    session: Optional[requests.Session] = None,
) -> List[Dict[str, Any]]:
    """Scrape a cinema's whats-on page for films with full multi-date showtime schedules.

    Current site structure (2026): Hero slider (.row.blurb) contains film titles.
    Showtime blocks are in #film_section .poster-film-content with .singlefilmperfs.
    """
    url = CINEMAS[cinema_id]["whats_on_url"]
    logger.info("Scraping whats-on: %s (%s)", url, cinema_name)
    resp = fetch_with_retries(url, session=session)
    soup = BeautifulSoup(resp.text, "html.parser")

    films: List[Dict[str, Any]] = []
    today_scrape = date.today()

    # Step 1: Extract hero slider data — (title, film_url)
    hero_entries: List[Tuple[str, str]] = []  # (title, film_url)
    for blurb in soup.select(".row.blurb"):
        h1 = blurb.select_one("h1")
        film_link = blurb.select_one("a[href*='/film/']")
        if h1 and film_link:
            title = h1.get_text(strip=True)
            if title and not any(skip in title.lower() for skip in (
                "looking ahead", "gaming", "private cinema",
                "onscreen magazine", "book the cinema",
            )):
                furl = film_link.get("href", "")
                if furl and not furl.startswith("http"):
                    furl = WTW_BASE_URL + furl
                hero_entries.append((title, furl))

    # Step 2: Build hero runtime lookup by fetching film detail pages (cached)
    hero_runtimes: Dict[int, Tuple[str, str, Dict[str, str]]] = {}  # runtime → (title, film_url, details)
    local_cache = load_cache()
    for hero_title, hero_url in hero_entries:
        details = fetch_film_details(hero_url, local_cache, session=session)
        if details:
            rt_str = details.get("runtime", "")
            rt_match = re.search(r"(\d+)", str(rt_str))
            if rt_match:
                rt = int(rt_match.group(1))
                if rt > 1 and rt not in hero_runtimes:
                    hero_runtimes[rt] = (hero_title, hero_url, details)

    # Step 3: Get film items from #film_section
    film_items = soup.select("#film_section .poster-film-content")
    if not film_items:
        logger.warning("No .poster-film-content nodes on whats-on page for %s", cinema_name)
        return films

    for item in film_items:
        # Runtime and starring from film section
        runtime = 0
        starring = ""
        rt_div = item.select_one(".running-time")
        if rt_div:
            rt_text = rt_div.get_text(" ", strip=True)
            star_match = re.search(r"Starring:\s*(.+?)\s*(?:Running\s*Time:|$)", rt_text)
            if star_match:
                starring = star_match.group(1).strip()
            rt_match = re.search(r"Running\s*Time:\s*(\d+)\s*minutes?", rt_text, re.IGNORECASE)
            if rt_match:
                runtime = int(rt_match.group(1))

        # Match film section to hero slider by runtime
        title = ""
        film_url = ""
        page_synopsis = ""
        poster_url = ""
        if runtime > 1 and runtime in hero_runtimes:
            title, film_url, details = hero_runtimes[runtime]
            page_synopsis = details.get("synopsis", "")
            # Extract poster from the matching hero slider blurb
            for blurb in soup.select(".row.blurb"):
                h1 = blurb.select_one("h1")
                if h1 and h1.get_text(strip=True) == title:
                    poster_img = blurb.select_one(".movie-slide-pic img")
                    if poster_img:
                        poster_url = poster_img.get("src", "")
                    break
        elif starring:
            # Fallback: match by first actor name in hero blurb text
            first_actor = starring.split(",")[0].strip().lower()
            if len(first_actor) > 3:
                for blurb in soup.select(".row.blurb"):
                    blurb_text = blurb.get_text(" ", strip=True).lower()
                    if first_actor in blurb_text:
                        h1 = blurb.select_one("h1")
                        fl = blurb.select_one("a[href*='/film/']")
                        if h1:
                            title = h1.get_text(strip=True)
                        if fl:
                            film_url = fl.get("href", "")
                            if film_url and not film_url.startswith("http"):
                                film_url = WTW_BASE_URL + film_url
                        break

        if not title:
            continue

        title = TITLE_CLEAN_RE.sub("", title)
        title = title.replace("–", "-").replace("—", "-")

        if any(skip in title.lower() for skip in (
            "looking ahead", "gaming", "private cinema",
            "onscreen magazine", "book the cinema"
        )):
            continue

        # BBFC cert
        bbfc = ""
        cert_img = item.select_one(".film-certificate img")
        if cert_img:
            cert_src = cert_img.get("src", "")
            for cert_name, cert_file in CERT_IMAGES.items():
                if cert_file in cert_src or CERT_CDN_MAP.get(cert_file, "") in cert_src:
                    bbfc = cert_name
                    break

        # Film detail URL — try from poster link or find from page links
        film_url = ""
        film_link = item.select_one("a[href*='/film/']")
        if film_link:
            film_url = film_link.get("href", "")
        if film_url and not film_url.startswith("http"):
            film_url = WTW_BASE_URL + film_url

        # Showtimes: .singlefilmperfs blocks
        showtimes: List[Dict[str, Any]] = []

        for perf_block in item.select(".singlefilmperfs"):
            # Get the date from the parent chain
            date_span = None
            parent = perf_block
            for _ in range(10):
                if not parent:
                    break
                date_span = parent.select_one(".firstdateshow")
                if date_span:
                    break
                parent = parent.parent

            if not date_span:
                continue

            date_text = date_span.get_text(strip=True)
            if not date_text:
                continue

            parsed_date = parse_uk_date(date_text, today_scrape)
            if not parsed_date:
                continue

            # Time from .perfbtn
            time_btn = perf_block.select_one(".perfbtn")
            time_text = ""
            if time_btn:
                time_parts = []
                for child in time_btn.children:
                    if isinstance(child, str):
                        time_parts.append(child.strip())
                time_text = "".join(time_parts).strip()
                time_match = re.search(r"(\d{1,2}:\d{2})", time_text)
                time_text = time_match.group(1) if time_match else ""

            if not time_text:
                continue

            # Screen
            screen = 1
            for li in perf_block.select(".hiddenbox-items li"):
                li_text = li.get_text(strip=True)
                screen_match = re.search(r"Screen:\s*(\d+)", li_text)
                if screen_match:
                    screen = int(screen_match.group(1))
                    break

            # Booking URL — skip sold-out/disabled showings (javascript:void(0);)
            booking_url = ""
            book_link = perf_block.select_one("a.hiddenbox-wrapper-link")
            if book_link and "disabled" not in book_link.get("class", []):
                href = book_link.get("href", "")
                if href and not href.startswith("javascript:"):
                    booking_url = href
                    if not booking_url.startswith("http"):
                        booking_url = WTW_BASE_URL + booking_url

            # Accessibility tags from CSS classes
            cls_list = perf_block.get("class", [])
            tags = []
            if "icon-2d" in cls_list:
                tags.append("2D")
            elif "icon-3d" in cls_list:
                tags.append("3D")
            if "ccap" in cls_list:
                tags.append("Subtitles")
            if "audio-des" in cls_list:
                tags.append("Audio Description")
            if "wc" in cls_list:
                tags.append("Wheelchair access")
            if "strobe-lgt" in cls_list:
                tags.append("Strobe Light warning")
            if "autism-friendly" in cls_list:
                tags.append("Autism Friendly")
            if "laser" in cls_list:
                tags.append("Laser Projection")
            if "kids-club" in cls_list:
                tags.append("Kids Club")
            if "silver-screen" in cls_list:
                tags.append("Silver Screen")
            if "parent-baby" in cls_list:
                tags.append("Parent & Baby")
            if "event-cinema" in cls_list:
                tags.append("Event cinema")
            if "fls-period" in cls_list:
                tags.append("FLS")

            showtimes.append({
                "date": parsed_date,
                "time": time_text,
                "screen": screen,
                "booking_url": booking_url,
                "tags": tags or ["2D"],
                "cinema_name": cinema_name,
            })

        if showtimes:
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
                "runtime": runtime,
                "starring": starring,
                "bbfc": bbfc,
                "synopsis": page_synopsis,
                "poster_url": poster_url,
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


def _apply_poster_fallback(details: dict) -> None:
    """Prefer TMDb art for the display poster.

    When TMDb has no poster_path the site's event banner would otherwise
    serve as the poster. A TMDb backdrop is a still from the film itself,
    so it makes the better stand-in. Site banners are landscape promo
    graphics; they never fit the 2/3 portrait frames, so drop any
    remaining non-TMDb art and let templates render the title tile.
    """
    poster = (details.get("poster_url") or "").strip()
    backdrop = (details.get("backdrop_url") or "").strip()
    if not poster or "image.tmdb.org" not in poster:
        details["poster_url"] = backdrop
    large = (details.get("poster_large_url") or "").strip()
    if large.startswith("http") and "image.tmdb.org" not in large:
        details["poster_large_url"] = ""


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
            if va is None or float(va) == 0.0:
                va = None
            elif entry.get("vote_count", MIN_TMDB_VOTES) < MIN_TMDB_VOTES:
                va = None
            return {
                "overview": entry.get("overview") or "",
                "genres": entry.get("genres") or [],
                "vote_average": va,
                "director": entry.get("director") or "",
                "cast": entry.get("cast") or "",
                "poster_url": entry.get("poster_url") or "",
                "poster_large_url": entry.get("poster_large_url") or "",
                "backdrop_url": entry.get("backdrop_url") or "",
                "runtime": entry.get("runtime") or "",
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
        "overview": "", "genres": [], "vote_average": None, "vote_count": 0,
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
            "vote_average": vote_average if vote_count >= MIN_TMDB_VOTES else None,
            "vote_count": vote_count,
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


# ── HTML templates and CSS ─────────────────────────────────────────────────────
from html_templates import (
    _SHARED_CSS, CSS, FILM_CSS,
    _esc, _format_runtime_display, _stars_from_rating,
    build_index_html, build_cinema_page, build_film_page,
    _cert_span, _youtube_embed_url, _extract_bbfc,
    _compute_fingerprint, _load_fingerprint, _save_fingerprint,
    _download_cert_images, _download_poster, _health_check, _save_sequence_state,
    write_style_css, make_ics_event, ICAL_NEWLINE, generate_sitemap,
    write_robots_txt,
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


# ── Main helpers ─────────────────────────────────────────────────────────────────
def _scrape_one_cinema(cid: str, info: dict, cache: Dict[str, dict]) -> List[Tuple]:
    """Scrape a single cinema's coming-soon page (module-level for pickling)."""
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


def _scrape_whats_on_one(cid: str, info: dict) -> List[Dict]:
    """Scrape a single cinema's whats-on page (module-level for pickling)."""
    sess = _session()
    try:
        return scrape_cinema_whats_on(cid, info["name"], session=sess)
    except Exception as e:
        logger.error("Error scraping whats-on %s: %s", info["name"], e)
        print(f"✗ {info['name']} whats-on: Error - {e}")
        return []
    finally:
        sess.close()


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
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as ex:
        futures = {ex.submit(_scrape_one_cinema, cid, info, cache): cid for cid, info in enabled_cinemas.items()}
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
    whats_on_data: Dict[str, List[Dict]] = {}  # normalized_title -> [showtime dicts]
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as wex:
        wfutures = {wex.submit(_scrape_whats_on_one, cid, info): cid for cid, info in enabled_cinemas.items()}
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
                    if field == "vote_average":
                        if float(val) == 0.0 or tc.get("vote_count", MIN_TMDB_VOTES) < MIN_TMDB_VOTES:
                            continue
                    fdetails[field] = val
            _apply_poster_fallback(fdetails)
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
        from functools import partial as _partial
        _tmdb_enrich = _partial(enrich_film_tmdb, api_key=api_key, cache=tmdb_cache, session=sess)

        enrich_futures: Dict[Any, str] = {}
        with ThreadPoolExecutor(max_workers=min(8, MAX_WORKERS * 2)) as tex:
            for k, (title, furl, indices) in unique_by_key.items():
                enrich_futures[tex.submit(_tmdb_enrich, title, furl)] = k
            for fut in as_completed(enrich_futures):
                k = enrich_futures[fut]
                try:
                    extra = fut.result()
                except Exception as exc:
                    logger.warning("TMDb enrichment failed for %s: %s", unique_by_key[k][0], exc)
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
                    _apply_poster_fallback(fdetails)
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
                    wo_enrich_futures[tex.submit(_tmdb_enrich, title, furl)] = k
                for fut in as_completed(wo_enrich_futures):
                    k = wo_enrich_futures[fut]
                    try:
                        extra = fut.result()
                    except Exception as exc:
                        logger.warning("TMDb poster fetch failed: %s", exc)
                        extra = {}
                    if extra:
                        tmdb_cache.setdefault(k, {}).update({**extra, "cached_at": datetime.now().isoformat()})
        sess.close()
        logger.info("TMDb enrichment done: %d coming-soon + %d whats-on unique films",
                     len(unique_by_key), len(whats_on_unique))
    else:
        logger.info("TMDB_API_KEY not set; scraping without TMDb enrichment")

    save_tmdb_cache(tmdb_cache)

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

    # Write combined CSS file for external reference
    write_style_css(out_dir)

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
        _atomic_write_text(out_dir / f"wtw-{cid}.ics", ics)
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
        # Film is "now showing" if it has any showtimes this week; event
        # cinema (opera, ballet, theatre, concert, Q&A) is surfaced even
        # when its next date is further out so it can be split out below.
        min_date = min(st["date"] for st in all_st)
        max_date = max(st["date"] for st in all_st)
        screening = extract_screening_label(wf_list[0]["title"])[1]
        is_event = _is_event_cinema(wf_list[0]["title"], screening, None, all_st)
        if min_date > today + timedelta(days=7) and not is_event:
            continue
        cinemas_set = sorted(set(st.get("cinema_name", "") for st in all_st))
        slug = _tmdb_cache_key(wf_list[0]["title"])
        poster = ""
        # Check TMDb cache first (now includes whats-on enrichments)
        if slug in tmdb_cache:
            tc = tmdb_cache[slug]
            poster = tc.get("poster_url", "") or tc.get("backdrop_url", "") or ""
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
            "screening": screening,
            "is_event": is_event,
        })
    now_showing_films.sort(key=lambda f: (f["min_date"], f["title"]))

    # ── Special Events / Hollywood split ─────────────────────────────────────
    special_events = [f for f in now_showing_films if f.get("is_event")]
    special_events.sort(key=lambda f: (f.get("screening", ""), f["min_date"]))
    now_showing_hollywood = [f for f in now_showing_films if not f.get("is_event")]

    # ── Enrich now-showing films with TMDb posters ───────────────────────────
    for f in now_showing_films:
        slug = f["slug"]
        tc = tmdb_cache.get(slug) or {}
        # Only TMDb art is usable in the portrait poster frames
        f["poster"] = (tc.get("poster_url") or "").strip()

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
                # Use title from film cache if we have a matching entry
                best_title = wf["title"]
                details: Dict[str, Any] = {
                    "screening": wf.get("screening", ""),
                    "screening_feature": wf.get("screening_feature", ""),
                    "poster_url": wf.get("poster_url") or "",
                    "runtime": f"{wf['runtime']} min" if wf.get("runtime") else "",
                    "cast": wf.get("starring", ""),
                    "bbfc": wf.get("bbfc", ""),
                    "synopsis": wf.get("synopsis", ""),
                }
                now_showing_entries[slug] = {
                    "title": best_title, "slug": slug,
                    "details": details,
                    "cinemas": [],
                    "release_date": date.today(),
                }
            now_showing_entries[slug]["cinemas"].append(
                (wf["cinema_name"], wf["film_url"], date.today(), wf["cinema_id"])
            )
    # ── Cross-reference with coming-soon to enrich now-showing films ────────
    # Build a lookup of coming-soon film URLs by normalized title
    cs_urls: Dict[str, str] = {}
    for rd, title, cname, furl, fdetails, cid in all_films:
        key = _tmdb_cache_key(title)
        if key not in cs_urls and furl:
            cs_urls[key] = furl
    # Fetch WTW detail pages for now-showing films that have a coming-soon URL
    for slug, entry in now_showing_entries.items():
        if slug in cs_urls and slug not in film_pages:
            wf_url = cs_urls[slug]
            page_details = fetch_film_details(wf_url, cache)
            if page_details:
                for field in ("synopsis", "runtime", "cast", "title"):
                    val = page_details.get(field)
                    if val and not entry["details"].get(field):
                        entry["details"][field] = val
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
        if slug in tmdb_cache:
            tc = tmdb_cache[slug]
            for field in ("overview", "genres", "vote_average", "director", "cast",
                          "poster_url", "poster_large_url", "backdrop_url", "runtime",
                          "trailer_url", "imdb_id"):
                val = tc.get(field)
                if not val:
                    continue
                if field == "vote_average":
                    if float(val) == 0.0 or tc.get("vote_count", MIN_TMDB_VOTES) < MIN_TMDB_VOTES:
                        continue
                # Always prefer TMDb poster/backdrop over WTW CDN backdrops
                if field in ("poster_url", "poster_large_url", "backdrop_url"):
                    page["details"][field] = val
                elif not page["details"].get(field):
                    page["details"][field] = val

    # One normalization pass covers every detail page (coming-soon + whats-on)
    for slug, page in film_pages.items():
        _apply_poster_fallback(page["details"])

    for slug, page in film_pages.items():
        film_showtimes = sorted(
            showtimes_by_slug.get(slug, []),
            key=lambda s: (s["date"], s["time"], s.get("cinema_name", ""))
        )
        page_html = build_film_page(
            page["title"], slug, page["details"], page["cinemas"],
            showtimes=film_showtimes or None
        )
        _atomic_write_text(films_dir / f"{slug}.html", page_html)
    current_film_slugs = set(film_pages.keys())
    for stale_page in films_dir.glob("*.html"):
        if stale_page.stem not in current_film_slugs:
            stale_page.unlink()
    logger.info("Wrote %d film detail pages to %s/films/", len(film_pages), OUTPUT_DIR)

    # ── Rebuild index with TMDb-enriched film_pages data ──────────────────────
    # build_index_html expects Dict[str, List[6-tuple]] format
    enriched_by_cinema: Dict[str, List] = {}
    for slug, page in film_pages.items():
        for cname, furl, rd, cid in page.get("cinemas", []):
            if cid:
                enriched_by_cinema.setdefault(cid, []).append(
                    (rd, page["title"], cname, furl, page["details"], cid)
                )
    enriched_all_films = []
    _seen = set()
    for cf in enriched_by_cinema.values():
        for rd, title, cname, furl, fdetails, cid in cf:
            slug = _tmdb_cache_key(title)
            if slug not in _seen:
                _seen.add(slug)
                cinemas_dict = {}
                for cname2, furl2, rd2, _cid2 in [(cname, furl, rd, cid)]:
                    cinemas_dict[cname2] = (furl2, rd2)
                enriched_all_films.append({
                    "title": title, "slug": slug,
                    "details": fdetails, "cinemas": cinemas_dict,
                    "release_date": rd,
                })
    enriched_all_films.sort(key=lambda f: (f["release_date"], f["title"]))

    # ── Special Events from the full coming-soon list ───────────────────────
    # wtw's event cinema (opera, ballet, theatre, concert, exhibition, NT Live,
    # RBO) films only appear in the full film list scraped for Coming Soon, not
    # in the current-week whats-on feed. Classify them here so they surface in
    # their own Special Events section below Now Showing instead of being
    # buried in Coming Soon.
    _today = date.today()
    _se_slugs = {f["slug"] for f in special_events}
    for f in enriched_all_films:
        if f["release_date"] < _today:
            continue
        if f["slug"] in _se_slugs:
            continue
        d = f.get("details", {})
        screening = d.get("screening", "")
        if not _is_event_cinema(f["title"], screening, d.get("categories"), None):
            continue
        special_events.append({
            "title": f["title"],
            "slug": f["slug"],
            "poster": d.get("poster_url"),
            "screening": screening or "Event Cinema",
            "min_date": f["release_date"],
        })
        _se_slugs.add(f["slug"])
    special_events.sort(key=lambda f: (f.get("screening", ""), f.get("min_date", date.min)))

    html = build_index_html(enabled_cinemas, enriched_by_cinema, stats=stats,
                            now_showing_live=now_showing_hollywood,
                            special_events=special_events,
                            new_slugs=new_slugs)
    _atomic_write_text(out_dir / "index.html", html)
    logger.info("Wrote %s/index.html (enriched)", OUTPUT_DIR)

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
                    except Exception as exc:
                        logger.warning("Poster download failed for %s: %s", slug, exc)
                        local = ""
                    if local:
                        slug_to_page[slug][1]["details"]["poster_url"] = local
                        updated_slugs.add(slug)
            # Only rewrite film pages that got poster updates
            for slug in updated_slugs:
                page = film_pages[slug]
                film_showtimes = sorted(
                    showtimes_by_slug.get(slug, []),
                    key=lambda s: (s["date"], s["time"], s.get("cinema_name", ""))
                )
                page_html = build_film_page(page["title"], slug, page["details"], page["cinemas"],
                    showtimes=film_showtimes or None)
                _atomic_write_text(films_dir / f"{slug}.html", page_html)
    finally:
        poster_sess.close()

    # Drop posters for films whose art was dropped this run
    if Path(POSTERS_DIR).is_dir():
        wanted = {slug for slug, page in film_pages.items() if page["details"].get("poster_url")}
        for orphan in Path(POSTERS_DIR).glob("*.jpg"):
            if orphan.stem not in wanted:
                orphan.unlink()

    # ── Cert images ──────────────────────────────────────────────────────────
    _download_cert_images()

    # ── Cinema pages ─────────────────────────────────────────────────────────
    # Use enriched film_pages data
    cs_films_sorted = sorted(
        [f for f in enriched_all_films if f["release_date"] > today],
        key=lambda f: f["release_date"]
    )
    for cid, info in enabled_cinemas.items():
        page_html = build_cinema_page(cid, info, now_showing_films, cs_films_sorted)
        _atomic_write_text(out_dir / f"{cid}.html", page_html)
    logger.info("Wrote %d cinema pages", len(enabled_cinemas))

    # ── Sitemap ───────────────────────────────────────────────────────────────
    film_slugs = sorted(film_pages.keys())
    sitemap = generate_sitemap(film_slugs, list(enabled_cinemas.keys()))
    _atomic_write_text(out_dir / "sitemap.xml", sitemap)
    logger.info("Wrote sitemap.xml with %d URLs", len(film_slugs) + len(enabled_cinemas) + 1)
    write_robots_txt(out_dir)

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
