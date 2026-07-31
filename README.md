<div align="center">

<img src="data:image/svg+xml,<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 100 100'><text y='.9em' font-size='90'>🎬</text></svg>" width="80" height="80" alt="">

# WTW Cinemas

**All-in-one cinema tracker for Cornwall - now showing, coming soon, and calendar feeds.**

[Live page](https://evenwebb.github.io/wtw-cinemas/) · [Repository](https://github.com/evenwebb/wtw-cinemas)

</div>

---

## What it does

A single Python file scrapes all four WTW Cinemas (St Austell, Newquay, Wadebridge, Truro) and generates a complete static site with no server, no database, just GitHub Pages.

**Index page**: Now Showing poster grid with list/card toggle, Coming Soon cards with synopses, cinema filter pills, nearest cinema geolocation, calendar promo banner, quick-jump nav, and a subscribe section with iOS / Google Calendar / copy-to-clipboard per cinema.

**59+ film detail pages**: Full showtime tables with Date / Time / Cinema / Screen columns, per-cinema filter pills, accessibility badges (AD, CC, WA, SL, AF, PB, KC, SS, EV) with popup key, nearest cinema row reordering, TMDb backdrop behind the poster, trailer embed, synopsis, director, cast, star rating, IMDb / Rotten Tomatoes / Trakt links, and BBFC age rating certs.

**4 cinema pages**: Per-venue Now Showing poster grid and Coming Soon list with map link and calendar feed.

**4 iCalendar feeds**: RFC 5545 compliant `.ics` files, one per cinema, with `REFRESH-INTERVAL:PT12H`, Google Calendar redirect links, and configurable alarms.

**SEO**: sitemap.xml, canonical URLs, Open Graph / Twitter Card meta tags, Schema.org Movie structured data.

---

## Quick Start

```bash
git clone https://github.com/evenwebb/wtw-cinemas.git
cd wtw-cinemas
python3 -m venv .venv && source .venv/bin/activate
pip install -r requirements.txt
python3 cinema_scraper.py
```

For TMDb enrichment (posters, ratings, cast, trailers, backdrops):

```bash
TMDB_API_KEY=your_key_here python3 cinema_scraper.py
```

Runs offline from cache once populated:

```bash
FORCE_REBUILD=1 python3 cinema_scraper.py
```

Output lands in `docs/`:

```
docs/
  index.html                  ← Main film discovery page
  films/                      ← 59+ per-film detail pages
  posters/                    ← Downloaded TMDb posters
  certs/                      ← BBFC age rating images
  newquay.html                ← Cinema-specific page
  st-austell.html
  truro.html
  wadebridge.html
  wtw-newquay.ics             ← iCal feed
  wtw-st-austell.ics
  wtw-truro.ics
  wtw-wadebridge.ics
  sitemap.xml
```

---

## Features

- **Dark mode** with automatic OS preference detection and themed favicon
- **Modular architecture**:  and  with 

### Scraping
| Area | Details |
|---|---|
| **Dual-source** | Scrapes `/coming-soon/` (future release dates) and `/whats-on/` (full multi-date showtime schedules) for all 4 cinemas in parallel |
| **Showtimes** | Date, time, screen number, accessibility tags (Audio Description, Subtitles, Wheelchair, Strobe, Autism Friendly, Parent & Baby, Kids Club, Silver Screen, Event Cinema), booking links |
| **Film details** | Extracts runtime, cast, synopsis from individual WTW film pages with 7-day cache |
| **Parallel** | `ThreadPoolExecutor` for cinema scraping and TMDb lookups with `requests.Session` reuse |

### Enrichment
| Area | Details |
|---|---|
| **TMDb** | Posters (w500), large posters (w780), backdrops (w780), synopses, star ratings, genres, director, cast, trailers, IMDb IDs. Cached 30 days |
| **Cache-only mode** | Runs without `TMDB_API_KEY` by loading existing cache from disk |
| **Anniversary handling** | Strips "25th Anniversary" suffixes to match the original film on TMDb |
| **BBFC** | Age rating extracted from film titles, cert images downloaded locally |
| **Film naming** | Normalised title matching with year-aware fallback scoring |

### Index page
| Area | Details |
|---|---|
| **Now Showing** | Poster grid (default) with list view toggle. 2-wide on mobile, 5-wide on desktop. Pulled from live whats-on data |
| **Coming Soon** | Rich cards with poster, synopsis, runtime, star rating, genres, cinema showings, and booking links. Cards / posters toggle |
| **Cinema filter** | Pill buttons to show films from all cinemas or a specific one |
| **Nearest cinema** | Geolocation highlights the closest cinema's filter button |
| **Quick-nav** | Pill links to jump to Now Showing, Coming Soon, or Subscribe |
| **Calendar promo** | CTA banner with "Set up now" button linking to the subscribe section |
| **Subscribe section** | Per-cinema iOS / Google / Copy / Show URL buttons, inline how-to for iPhone, Google Calendar, and Outlook |
| **Just added badge** | "New" badge on films first seen in the last 7 days |
| **View toggle** | Cards / posters toggle for Coming Soon, preference saved in localStorage |

### Film detail pages
| Area | Details |
|---|---|
| **Showtime table** | Date / Time / Cinema / Screen columns with cinema filter pills |
| **Accessibility badges** | Color-coded AD, CC, WA, SL, AF, PB, KC, SS, EV badges with popup key |
| **Nearest cinema** | Geolocation reorders rows to put the closest cinema first with a highlight border |
| **Backdrop** | Full-width TMDb backdrop behind the page with gradient dark overlay |
| **Trailer** | YouTube embed with nocookie domain, prioritises "Trailer" over "Teaser" |
| **Meta** | Runtime, star rating, genres, synopsis, director, cast, IMDb / Rotten Tomatoes / Trakt links, BBFC cert |
| **Booking** | Direct WTW booking links for every showtime row |

### Cinema pages
| Area | Details |
|---|---|
| **Now Showing** | Poster grid filtered to that cinema only |
| **Coming Soon** | List with dates and links to film detail pages |
| **Map** | Google Maps link for the cinema location |
| **Calendar** | Direct iCal feed download link |

### iCalendar feeds
| Area | Details |
|---|---|
| **RFC 5545** | `VEVENT` with stable SHA-1 UIDs, line folding at 75 octets |
| **Refresh** | `REFRESH-INTERVAL:PT12H` for calendar clients |
| **Rich events** | Runtime display, film URL, cinema name, TMDb synopsis when available |
| **Alarms** | Configurable `VALARM` with `days_before` and `hours_before` |

### UI / UX
| Area | Details |
|---|---|
| **Dark theme** | CSS custom properties, cyan/purple accent gradient |
| **Mobile responsive** | Scrollable showtime tables, adaptive grids, breakpoints at 480/600/640/680/768/1024px |
| **Accessibility** | Skip-to-content link, ARIA labels, `prefers-reduced-motion`, keyboard-dismissible popups, touch-friendly 44px+ tap targets |
| **Print styles** | `@media print` hides backgrounds, nav, buttons |
| **Performance** | `loading="lazy"` and `decoding="async"` on all images, fingerprint-based change detection skips rebuilds, cache-based enrichment without API key |

---

## Configuration

Edit `cinema_scraper.py` - constants at the top:

| Setting | Default | Purpose |
|---|---|---|
| `CINEMAS` | All 4 enabled | Toggle individual venues on/off |
| `MAX_WORKERS` | `min(4, cpu_count)` | Thread pool size |
| `HTTP_RETRIES` | 3 | Retry attempts per request |
| `HTTP_TIMEOUT` | 60s | Per-request timeout |
| `CACHE_EXPIRY_DAYS` | 7 | Film detail cache TTL |
| `TMDB_CACHE_DAYS` | 30 | TMDb cache TTL |
| `CALENDAR_TIMEZONE` (env) | `Europe/London` | iCal timezone |
| `HEALTH_MIN_FILMS` (env) | 1 | Minimum films before health check fails |
| `HEALTH_MIN_CINEMAS` (env) | 1 | Minimum cinemas before health check fails |
| `TMDB_API_KEY` (env) | - | Enables live TMDb enrichment |

---

## GitHub Actions

Workflow at `.github/workflows/scrape.yml`:

- **Schedule**: Daily at 09:00 UTC
- **Manual**: `workflow_dispatch` trigger
- **Concurrency**: Prevents overlapping runs
- **Timeout**: 15 minutes
- **Retries**: Up to 2 attempts with escalating delays (30s/60s)
- **Caching**: Restores film cache, TMDb cache, release history, and fingerprint between runs
- **Commit**: Auto-commits changes with premiere count, film page count, and cinema page count
- **Failure alert**: Optional issue creation on repeated failures via `CREATE_FAILURE_ISSUE` variable

Repository secrets/variables:

| Name | Type | Purpose |
|---|---|---|
| `TMDB_API_KEY` | Secret | TMDb API key |
| `SCRAPER_RUN_ATTEMPTS` | Variable | Retry count (default 2) |
| `CREATE_FAILURE_ISSUE` | Variable | `true` to open issues on failure |

---

## GitHub Pages

1. **Settings → Pages**
2. Source: **Deploy from a branch**
3. Branch: `main`, folder: `/docs`
4. Published at `https://evenwebb.github.io/wtw-cinemas/`

---

## Architecture

```
cinema_scraper.py            # Single-file application (~2650 lines, 43 functions)
├── Constants / Config       # Cinemas, patterns, TMDb genre map, health minimums
├── HTTP layer               # requests.Session + exponential-backoff retries
├── Cache layer              # Thread-safe JSON file caches with TTL expiry
├── Date parsing             # UK date formats, relative dates (Today/Tomorrow)
├── Coming-soon scraping     # Release dates from /coming-soon/ listing pages
├── What's-on scraping       # Full multi-date showtime schedules from /whats-on/
├── Film detail extraction   # Runtime, cast, synopsis from individual film pages
├── TMDb enrichment          # Search + movie details with videos, credits, poster sizes
├── iCalendar output         # RFC 5545 VEVENT + VALARM generation with line folding
├── HTML builders            # Index page, film detail pages, cinema pages
├── CSS (inline)             # Shared CSS + index CSS + film page CSS + cinema page CSS
├── JavaScript (inline)      # Cinema filters, view toggles, geolocation, popups, clipboard
├── Poster/cert downloads    # TMDb posters + BBFC cert images saved locally
├── Sitemap generator        # Auto-generated sitemap.xml with all film + cinema URLs
├── Health checks            # Minimum film/cinema thresholds before output generation
├── Fingerprint              # SHA-256 change detection to skip unchanged rebuilds
├── Validation               # Config sanity checks, env var validation
└── Main orchestrator        # Thread pools → dual-source scrape → enrich → generate
```

## Dependencies

```
requests>=2.31,<3
beautifulsoup4>=4.12,<5
```

No frameworks, no build step, no JavaScript dependencies. Static HTML/CSS/JS output.

---

## License

MIT
