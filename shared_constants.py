"""
Shared constants and helpers used by both cinema_scraper.py and html_templates.py.

This module breaks the circular import between those two files.
"""
from __future__ import annotations

import logging
import os as _os
import re
from typing import Any, Dict, List

# ── Output paths ────────────────────────────────────────────────────────────────
ICAL_LINE_LENGTH = 75
POSTERS_DIR = "docs/posters"
CERTS_DIR = "docs/certs"
FINGERPRINT_FILE = ".scrape_fingerprint"

# ── Site URL (used for canonical links, sitemap, iCal, calendar feeds) ──────────
SITE_BASE_URL = _os.environ.get("SITE_URL", "https://evenwebb.github.io/wtw-cinemas")

# ── WTW site constants ──────────────────────────────────────────────────────────
WTW_BASE_URL = "https://wtwcinemas.co.uk"
WTW_CERT_BASE = "https://websales-django-static-uk.taposapp.com/static/sales/images/filmcerts_uk"

# ── BBFC cert patterns and images ───────────────────────────────────────────────
BBFC_PATTERN = re.compile(r"\((\d{1,2}A?|U|PG|R18)\)", re.IGNORECASE)
CERT_IMAGES = {
    "U": "cert-u.png", "PG": "cert-pg.png", "12": "cert-12.png",
    "12A": "cert-12a.png", "15": "cert-15.png", "18": "cert-18.png",
}

# Mapping from CDN cert filenames to local filenames
CERT_CDN_MAP = {
    "cert-u.png": "u.png", "cert-pg.png": "pg.png", "cert-12.png": "12.png",
    "cert-12a.png": "12a.png", "cert-15.png": "15.png", "cert-18.png": "18.png",
}

# ── Cinema addresses for map links ──────────────────────────────────────────────
CINEMA_ADDRESSES = {
    "st-austell": "White+River+Cinema+St+Austell",
    "newquay": "Lighthouse+Cinema+Newquay",
    "wadebridge": "Regal+Cinema+Wadebridge",
    "truro": "Plaza+Cinema+Truro",
}

# ── Health check minimums ───────────────────────────────────────────────────────
HEALTH_MIN_FILMS = int(_os.getenv("HEALTH_MIN_FILMS", "1"))
HEALTH_MIN_CINEMAS = int(_os.getenv("HEALTH_MIN_CINEMAS", "1"))

# ── Notifications defaults ──────────────────────────────────────────────────────
NOTIFICATION_TIME = "09:00"
NOTIFICATIONS: Dict[str, Any] = {"enabled": False, "alarms": []}

# ── Terms to skip TMDb enrichment for ───────────────────────────────────────────
SKIP_TMDB_TERMS: List[str] = [
    "live nation", "tribute", "comedy club", "pantomime", "panto",
    "psychic", "candlelit", "on tour", "presented by", "choir", "orchestra",
    "theatre company", "pride", "adults only",
]

# ── Logger ──────────────────────────────────────────────────────────────────────
logger = logging.getLogger(__name__)


# ── Helpers ─────────────────────────────────────────────────────────────────────
_TITLE_CLEAN_RE = re.compile(r"\s*\([^)]*\)$")


def _tmdb_cache_key(film_title: str) -> str:
    """Derive a canonical cache key from a film title."""
    t = _TITLE_CLEAN_RE.sub("", film_title).strip()
    t = re.sub(r"[\s\-:]+", " ", t.lower()).strip()
    return re.sub(r"[^a-z0-9]+", "-", t).strip("-") or "unknown"
