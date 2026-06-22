# CouchDB Obsidian Viewer (Flask)

Simple Flask app that reads Markdown notes from CouchDB and renders them as HTML.

At server startup, it caches all readable markdown notes into a local folder and then serves
home, note, and tag pages from this cache (instead of re-fetching notes on each request).

It also converts:
- Obsidian wiki-links `[[My Note]]` or `[[My Note|Alias]]` into clickable note links
- Hashtags like `#trading` into clickable tag pages
- Obsidian heading links such as `[[#Section Name]]` and `[[My Note#Section Name]]`
- Nested tags like `#desk/alpha` into grouped tag pages

## 1) Setup

```bash
cd couchdb_obsidian_viewer
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
cp .env.example .env
```

Edit `.env` with your CouchDB values.
You can optionally set `LOCAL_CACHE_DIR` to choose where startup cache files are written.

## 2) Run

```bash
python app.py
```

Skip cache regeneration and use existing local cache files:

```bash
python app.py --skip-cache-regeneration
```

Open:
- http://127.0.0.1:5000/
- http://127.0.0.1:5000/note/your-doc-id
- http://127.0.0.1:5000/tag/yourtag
- http://127.0.0.1:5000/tag/desk/alpha
- http://127.0.0.1:5000/debug/your-doc-id

## 3) LiveSync encryption notes

Supported encrypted chunk formats:
- `%$` (HKDF with embedded PBKDF2 salt)
- `%=` (HKDF with external PBKDF2 salt)
- legacy `%` hex format

If your chunks start with `%=` and do not decrypt, set `LIVESYNC_PBKDF2_SALT` in `.env`.
This value can be hex or base64.

## 4) Expected CouchDB document

A note doc can keep markdown in any one of these fields:
- `content`
- `markdown`
- `body`
- `text`

Example:

```json
{
  "_id": "My Note",
  "title": "My Note",
  "content": "# Hello\nLinks: [[Another Note]] and #trading"
}
```
