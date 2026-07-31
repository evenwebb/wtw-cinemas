# WTW Cinemas — Current Site Structure (July 2026)

## Page Types

### 1. What's On (`/st-austell/whats-on/`)
- Film section: `#film_section`
- Film items: `.poster-film-content` (currently 5 films for "Today")
- Film title: `img[alt]` in poster area (e.g. `<img alt="Toy Story 5">`)
- Runtime/Starring: `.poster_film_header > .running-time` (text: "Starring:X Running Time:X minutes")
- Certificate: `.film-certificate img` (src contains cert filename)
- Showtime blocks: `.singlefilmperfs` (multiple per film = multiple showtimes)
  - Date: parent `.wtw-performance-day-item span.firstdateshow` (text: "Today 31 July 2026")
  - Time: `.perfbtn` text content (e.g. "12:00")
  - Booking link: `a.hiddenbox-wrapper-link` href
  - Screen: `.hiddenbox-items li` containing "Screen:X"
  - Accessibility classes on `.singlefilmperfs`: `ccap`, `audio-des`, `wc`, `strobe-lgt`, `laser`, `autism-friendly`, `icon-2d`, `icon-3d`, `kids-club`, `silver-screen`, `parent-baby`, `event-cinema`
  - Performance type: class `percatestandardscreening` or `percatetoddler cinema` etc

### 2. Coming Soon (`/st-austell/coming-soon/`)
- Film listings use h1 tags (NOT within poster-film-content)
- Film cards: `div.filmecatte{GENRE} percatestandardscreening poster-img result_{TYPE}`
  - Title: inline text after poster
  - Synopsis: inline text after title
  - Release date: `.poster_film_header > .running-time` → "Expected: X Month Year"
  - Certificate: `.film-certificate img`
  - Film link: `a[href*="/film/"]`
- Genre from class: `filmecattedrama`, `filmecattecomedy`, `filmecatteaction`, `filmecatteevent cinema`, etc.

### 3. Film Detail (`/st-austell/film/{id}/{slug}`)
- Title: `<title>` tag + `<h1>` 
- Starring: `<li>` containing "Starring:"
- Running time: `<li>` containing "Running time:"
- Description: page `<p>` text
- Certificate: same cert image pattern

### 4. Hero Slider (both pages)
- `.row.blurb` sections at top
- Contains: backdrop image, h1 title, synopsis, cert, trailer URL
- Not used for scraping — these overlap with the listing data
