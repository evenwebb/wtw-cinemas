# WTW Cinemas — Project Audit Report

**Date**: 2026-07-31 | **Auditor**: Claude Code  
**Scope**: Full repository audit, read-only  
**Stack**: Python 3.12, requests + BeautifulSoup4, GitHub Pages, GitHub Actions — 3,724 LOC

---

## Detected Stack (High Confidence)

| Layer | Technology | Evidence |
|-------|-----------|----------|
| Language | Python 3.12 | `.github/workflows/scrape.yml:30`, `python3 --version` |
| HTTP | requests 2.31+ | `requirements.txt:1` |
| HTML parsing | beautifulsoup4 4.12+ | `requirements.txt:2` |
| Deployment | GitHub Pages (`/docs`) | `README.md:191-194`, `.github/workflows/scrape.yml:84-103` |
| Scheduling | GitHub Actions (daily 10 UTC) | `.github/workflows/scrape.yml:4-5` |
| Package mgmt | pip + uv (CI) | `requirements.txt`, workflow uses `astral-sh/setup-uv@v4` |
| CSS | Inline generated | `html_templates.py` CSS constants |
| Tests | None | No test framework, no test files |
| DB | None (JSON file caches) | `.film_cache.json`, `.tmdb_cache.json` |

---

## Findings

### FINDING-01 | HIGH | Confirmed
**Broad `except Exception` swallows critical errors in TMDb enrichment loop**

- **File**: `cinema_scraper.py:1194`
- **Evidence**: `except Exception: pass` inside a loop processing all films, silently skipping TMDb enrichment failures.
- **Impact**: If TMDb returns malformed data or a transient error, the film is silently left unenriched with no log. The next run may re-attempt or skip depending on cache state, leading to inconsistent data.
- **Fix**: Log the specific error with film title; consider separate retry logic for transient vs permanent TMDb failures.
- **Risk**: Medium — non-critical data loss, but makes debugging enrichment gaps difficult.

### FINDING-02 | HIGH | Confirmed
**Hardcoded GitHub Pages URL in 11 locations across 2 files**

- **Files**: `html_templates.py:219,736-738,817,1050,1078,1605`
- **Evidence**: Literal string `"evenwebb.github.io/wtw-cinemas"` hardcoded in iCal descriptions, calendar subscription links, canonical URLs, og:url meta tags, and sitemap generation.
- **Impact**: Forking or renaming the repo requires search-and-replace across 11 lines. Easy to miss one, resulting in broken links or wrong canonical URLs.
- **Fix**: Extract to a single `SITE_BASE_URL` constant in `shared_constants.py`, default to env var `SITE_URL`.
- **Risk**: Low for current deployment, medium for portability.

### FINDING-03 | MEDIUM | Confirmed
**What's-on scraper captures only today's showtimes, matching by index position**

- **File**: `cinema_scraper.py:596-608`
- **Evidence**: Film titles are extracted from `.row.blurb h1` hero slider and matched to `#film_section .poster-film-content` showtime blocks by array index. The page has a JS-driven date selector with multiple date options that cannot be scraped statically.
- **Impact**: Only captures 5-6 films showing today, missing films showing on other days. iCal feeds won't include tomorrow's showtimes.
- **Fix**: Investigate the AJAX endpoint the date selector calls (likely returns JSON), or use the booking links to derive additional showtimes.
- **Risk**: Medium — functional gap compared to potential data available.

### FINDING-04 | MEDIUM | Confirmed
**No disk-full or write-failure handling for output generation**

- **File**: `cinema_scraper.py:1299-1524` (all `.write_text()` calls)
- **Evidence**: 11 `write_text()` / `write_bytes()` calls without try/except. An `OSError` (disk full, permission denied) will crash the entire run after scraping is complete.
- **Impact**: All scraped data is lost; cache files may be corrupted; GitHub Pages deployment will fail silently.
- **Fix**: Wrap output writes in a try/except that logs the error and exits cleanly; use atomic writes (write to temp file, then rename) for cache files.
- **Risk**: Low probability, high impact.

### FINDING-05 | MEDIUM | Confirmed
**`time` module imported but unused**

- **File**: `cinema_scraper.py:16`
- **Evidence**: `import time` at line 16; no usage of `time.sleep()` or `time.time()` anywhere in the file (search: zero hits outside the import).
- **Impact**: Dead import, minor code smell.
- **Fix**: Remove `import time`.
- **Risk**: Negligible.

### FINDING-06 | MEDIUM | Confirmed
**`groupby` from itertools imported but unused**

- **File**: `cinema_scraper.py:20`
- **Evidence**: `from itertools import groupby` — zero usages of `groupby` in the entire codebase.
- **Impact**: Dead import.
- **Fix**: Remove from import.
- **Risk**: Negligible.

### FINDING-07 | LOW | Confirmed
**Atomic writes used for some cache files but not all**

- **File**: `cinema_scraper.py:243` vs `cinema_scraper.py:1299`
- **Evidence**: Cache files use atomic write (temp file + rename): `save_cache()` writes to `.tmp` then `os.replace()`. But ICS files, HTML pages, and sitemap use direct `write_text()` — no atomicity.
- **Impact**: A crash during output write could leave partially-written HTML files in `docs/`, which would be deployed to GitHub Pages.
- **Fix**: Apply the same atomic write pattern to all output files.
- **Risk**: Low — crashes during output writes are rare.

### FINDING-08 | LOW | Confirmed
**`ZoneInfo` imported but unused in `cinema_scraper.py`**

- **File**: `cinema_scraper.py:23`
- **Evidence**: `from zoneinfo import ZoneInfo` — no usage of `ZoneInfo` anywhere in the file. The timezone is only used in `html_templates.py` for iCal generation.
- **Impact**: Dead import.
- **Fix**: Remove.
- **Risk**: Negligible.

### FINDING-09 | LOW | Unverified
**Film cache uses thread lock but TMDb cache may have a race condition**

- **File**: `cinema_scraper.py:946-948` vs `cinema_scraper.py:870-872`
- **Evidence**: TMDb cache reads use `with _tmdb_cache_lock` but the cache is also written at line 946 inside a lock. However, the `load_tmdb_cache()` call in `main()` is outside any lock, and the cache dict is shared across threads. If the dict is modified during iteration by another thread, Python may raise `RuntimeError: dictionary changed size during iteration`.
- **Impact**: Rare race condition could crash the enrichment phase.
- **Fix**: Use `threading.RLock()` or copy the cache dict before iteration.
- **Risk**: Low — unlikely with small cache sizes and low thread counts.

### FINDING-10 | LOW | Confirmed
**Coming-soon title extraction from slugs loses special characters**

- **File**: `cinema_scraper.py:461-471`
- **Evidence**: `_extract_title_from_slug()` converts URL slugs like `andr-rieus-2026-summer-concert-viva-maastricht` to `Andr Rieus 2026 Summer Concert Viva Maastricht` — loses the accented `é` in "André Rieu's". Fixed when the film detail page is fetched (real title extracted from `<title>` tag), but the initial slug-derived title is used for deduplication keys.
- **Impact**: Minor — subsequent enrichment from film detail pages corrects this. Only matters if film detail page fetch fails.
- **Fix**: None needed; film detail page correction is adequate.
- **Risk**: Negligible.

---

## Positive Findings (No Issues)

| Area | Assessment |
|------|-----------|
| **XSS Prevention** | ✓ All HTML output passes through `_esc()` which uses `html.escape(text, quote=True)`. No raw string interpolation into HTML. |
| **Secrets Management** | ✓ `TMDB_API_KEY` read from env var only, never hardcoded or logged. API key redacted in error messages (`api_key=***`). |
| **Thread Safety** | ✓ Cache reads/writes protected by `threading.Lock()`. Sessions properly closed in `finally` blocks. |
| **Error Recovery** | ✓ HTTP layer has exponential backoff (3 retries, 1s→2s→4s). Individual cinema failures don't block others. TMDb failures allow cache-only continuation. |
| **Input Validation** | ✓ Config validated at startup (`validate_configuration()`). Cache TTLs enforced. Date parsing handles edge cases (past dates, month rollover). |
| **Atomic Cache Writes** | ✓ JSON caches written to temp files then `os.replace()` — prevents corruption from partial writes. |
| **Fingerprint Change Detection** | ✓ SHA-256 content fingerprint skips rebuild when nothing changed. `FORCE_REBUILD` env override available. |
| **iCal Compliance** | ✓ RFC 5545 compliant with correct line folding at 75 octets, stable SHA-1 UIDs, VALARM support, REFRESH-INTERVAL header. |
| **Health Checks** | ✓ Minimum film/cinema thresholds prevent deploying empty output. Configurable via env vars. |
| **Concurrency Control** | ✓ GitHub Actions workflow has `cancel-in-progress: true`, preventing overlapping runs. |
| **Failure Auto-Issue** | ✓ Workflow creates/updates GitHub issues on failure with deduplication by error signature. Auto-closes after 2 successful runs. |
| **Accessibility** | ✓ Skip-to-content link, ARIA labels, `prefers-reduced-motion`, keyboard-dismissible popups, 44px+ touch targets. |
| **Cache TTLs** | ✓ Film cache 7 days, TMDb cache 30 days, release history 730 days. All configurable. |

---

## Coverage Gaps

| Gap | Risk |
|-----|------|
| **No automated tests** | Zero test framework, zero test files. All validation is manual. Regression risk on every change. |
| **No type checking** | No mypy/pyright configuration. Type annotations present but unverified. |
| **No linting configuration** | No `.flake8`, `pyproject.toml`, or `setup.cfg` with lint rules. |
| **What's-on date pagination** | Can't scrape beyond today's showtimes without JS execution or AJAX endpoint discovery. |
| **No monitoring/alerting** | No health check endpoint, no uptime monitoring. Relying solely on GitHub issue auto-creation. |

---

## Summary

| Severity | Count | Key Issues |
|----------|-------|-----------|
| HIGH | 2 | Broad exception swallowing TMDb errors; hardcoded site URL in 11 places |
| MEDIUM | 4 | Today-only what's-on; no disk-full handling; 2 dead imports |
| LOW | 4 | Incomplete atomic writes; unused ZoneInfo import; title slug approximation; potential cache race |
| **TOTAL** | **10** | All non-critical; scraper functional and safe |

**Overall**: Codebase is well-structured, secure, and production-functional. The 2 HIGH findings are code quality/portability issues, not production blockers. The main functional gap is the what's-on date pagination limitation.
