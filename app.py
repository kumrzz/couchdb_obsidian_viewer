import base64
import argparse
import datetime
import json
import os
import re
import shutil
import sys
import time
from urllib.parse import quote, unquote

import hashlib

from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC

import bleach
import markdown
import requests
from requests.packages.urllib3.exceptions import InsecureRequestWarning
requests.packages.urllib3.disable_warnings(InsecureRequestWarning)

from dotenv import load_dotenv
from flask import Flask, abort, redirect, render_template_string, request, url_for

load_dotenv()

app = Flask(__name__)

COUCHDB_URL = os.getenv("COUCHDB_URL", "http://127.0.0.1:5984").rstrip("/")
COUCHDB_DB = os.getenv("COUCHDB_DB", "obsidian_notes")
COUCHDB_USER = os.getenv("COUCHDB_USER", "")
COUCHDB_PASSWORD = os.getenv("COUCHDB_PASSWORD", "")

AUTH = (COUCHDB_USER, COUCHDB_PASSWORD) if COUCHDB_USER else None

LIVESYNC_PASSPHRASE = os.getenv("LIVESYNC_PASSPHRASE", "")

_ssl_env = os.getenv("COUCHDB_VERIFY_SSL", "true").strip()
if _ssl_env.lower() in ("0", "false", "no"):
    SSL_VERIFY: bool | str = False
else:
    # Treat any other non-empty value as a CA bundle path; "true" means default verification
    SSL_VERIFY = True if _ssl_env.lower() in ("1", "true", "yes") else _ssl_env

WIKI_LINK_PATTERN = re.compile(r"\[\[([^\]|]+)(?:\|([^\]]+))?\]\]")
TAG_PATTERN = re.compile(r"(?<![\w/])#([A-Za-z][\w/-]*)")
URL_PATTERN = re.compile(r"(?P<url>https?://[^\s<]+)")

BASE_TEMPLATE = """
<!doctype html>
<html lang=\"en\">
  <head>
    <meta charset=\"utf-8\" />
    <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />
    <title>{{ title }}</title>
    <style>
      :root {
        --bg: #f7f4ef;
        --card: #fffdfa;
        --ink: #1e1e1e;
        --accent: #0f766e;
        --muted: #6b7280;
      }
      body {
        margin: 0;
        background: radial-gradient(circle at 20% 0%, #e7efe8 0%, var(--bg) 45%);
        color: var(--ink);
        font-family: Georgia, Cambria, Times New Roman, serif;
        line-height: 1.65;
      }
      .wrap {
        max-width: 900px;
        margin: 2rem auto;
        padding: 0 1rem;
      }
      .card {
        background: var(--card);
        border: 1px solid #e8dfd3;
        border-radius: 14px;
        padding: 1.5rem;
        box-shadow: 0 8px 30px rgba(0, 0, 0, 0.04);
      }
      a {
        color: var(--accent);
      }
      pre {
        background: #f3efe8;
        padding: 0.8rem;
        border-radius: 8px;
        overflow-x: auto;
      }
      code {
        background: #f3efe8;
        padding: 0.1rem 0.25rem;
        border-radius: 4px;
      }
      .meta {
        color: var(--muted);
        margin-bottom: 1rem;
      }
            .topnav {
                margin-bottom: 1rem;
            }
            .bottomnav {
                margin-top: 1.25rem;
            }
            .topnav a,
            .bottomnav a {
                margin-right: 0.8rem;
            }
      .error {
        color: #991b1b;
      }
    </style>
  </head>
  <body>
    <main class=\"wrap\">
      <section class=\"card\">
                <div class="topnav"><a href="/">Home</a><a href="/all_files">All Files</a></div>
        {{ body | safe }}
                <div class="bottomnav"><a href="/">Home</a><a href="/all_files">All Files</a></div>
      </section>
    </main>
  </body>
</html>
"""


def couch_get(path: str):
    url = f"{COUCHDB_URL}/{COUCHDB_DB}/{path.lstrip('/')}"
    response = requests.get(url, auth=AUTH, timeout=12, verify=SSL_VERIFY)
    return response


def fetch_doc(doc_id: str) -> dict:
    # Request inline attachments so we can read LiveSync content stored as _attachments
    url = f"{COUCHDB_URL}/{COUCHDB_DB}/{doc_id.lstrip('/')}?attachments=true"
    response = requests.get(url, auth=AUTH, timeout=12, verify=SSL_VERIFY)
    if response.status_code == 404:
        abort(404, description=f"Document '{doc_id}' not found")
    if not response.ok:
        abort(response.status_code, description=response.text)
    return response.json()


_PREFERRED_KEYS = ("content", "markdown", "body", "text", "note", "data", "raw")
# CouchDB internal / Obsidian metadata fields to skip when auto-detecting
_SKIP_KEYS = frozenset({"_id", "_rev", "_attachments", "title", "name", "type",
                        "id", "created", "updated", "mtime", "ctime", "tags",
                        "aliases", "path", "stat", "frontmatter", "children", "eden", "size"})


# LiveSync encryption prefixes
_LIVESYNC_ENC_PREFIX = "%"
_HKDF_ENCRYPTED_PREFIX = "%="
_HKDF_SALTED_ENCRYPTED_PREFIX = "%$"
_PBKDF2_ITERATIONS = 310_000
_LIVESYNC_PBKDF2_SALT = os.getenv("LIVESYNC_PBKDF2_SALT", "").strip()
_SYNC_PARAMS_DOC_ID = "_local/obsidian_livesync_sync_parameters"
_PBKDF2_SALT_CACHE: bytes | None = None

LOCAL_CACHE_DIR = os.getenv("LOCAL_CACHE_DIR", "./local_markdown_cache")
LOCAL_CACHE_INDEX = os.path.join(LOCAL_CACHE_DIR, "index.json")
LOCAL_CACHE_NOTES_DIR = os.path.join(LOCAL_CACHE_DIR, "notes")
_CACHE_READY = False
_CACHED_NOTES: dict[str, dict] = {}
_REBUILD_CACHE = False
_BLOCKED_CACHE_PREFIXES = ("h%3A%2B",)
TAG_EXCLUSIONS_CONFIG = os.getenv("TAG_EXCLUSIONS_CONFIG", "./tag_exclusions.conf")


def _livesync_iterations(passphrase: str) -> int:
    """Mirror LiveSync autoCalculateIterations=true formula from octagonal-wheels/encryption.ts."""
    passphrase_len = 15 - len(passphrase)
    if passphrase_len > 0:
        return passphrase_len * 1000 + 121 - passphrase_len  # = passphrase_len * 999 + 121
    return 121 - passphrase_len  # = 121 + (len - 15)


def _decode_b64_loose(data: str) -> bytes:
    padded = data + ("=" * (-len(data) % 4))
    return base64.b64decode(padded)


def _parse_pbkdf2_salt(value: str) -> bytes:
    if not value:
        return b""
    # Accept hex, then base64, then raw utf-8 bytes.
    try:
        return bytes.fromhex(value)
    except Exception:
        pass
    try:
        return _decode_b64_loose(value)
    except Exception:
        pass
    return value.encode("utf-8")


def _fetch_sync_params_doc() -> dict:
    url = f"{COUCHDB_URL}/{COUCHDB_DB}/{_SYNC_PARAMS_DOC_ID}"
    response = requests.get(url, auth=AUTH, timeout=12, verify=SSL_VERIFY)
    if not response.ok:
        return {}
    payload = response.json()
    return payload if isinstance(payload, dict) else {}


def _discover_pbkdf2_salt() -> bytes:
    global _PBKDF2_SALT_CACHE

    if _PBKDF2_SALT_CACHE is not None:
        return _PBKDF2_SALT_CACHE

    if _LIVESYNC_PBKDF2_SALT:
        parsed = _parse_pbkdf2_salt(_LIVESYNC_PBKDF2_SALT)
        if parsed:
            _PBKDF2_SALT_CACHE = parsed
            return parsed

    params = _fetch_sync_params_doc()
    for key in ("pbkdf2salt", "pbkdf2Salt"):
        raw = params.get(key)
        if isinstance(raw, str) and raw.strip():
            parsed = _parse_pbkdf2_salt(raw.strip())
            if parsed:
                _PBKDF2_SALT_CACHE = parsed
                return parsed

    _PBKDF2_SALT_CACHE = b""
    return _PBKDF2_SALT_CACHE


def _derive_key_v2(passphrase: str, salt_bytes: bytes, iterations: int) -> bytes:
    """
    LiveSync key derivation (V2):
      1. SHA-256 hash the passphrase → use as PBKDF2 key material
      2. PBKDF2-SHA256 with the given salt and iterations → 32-byte AES-GCM key
    """
    passphrase_hash = hashlib.sha256(passphrase.encode("utf-8")).digest()
    kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt_bytes, iterations=iterations)
    return kdf.derive(passphrase_hash)


def _derive_hkdf_aes_key(passphrase: str, pbkdf2_salt: bytes, hkdf_salt: bytes) -> bytes:
    # Matches octagonal-wheels hkdf.ts:
    # 1) PBKDF2(passphrase utf8, pbkdf2Salt, 310000, SHA-256, 32)
    # 2) HKDF(masterKey, hkdfSalt, SHA-256, 32)
    master_key = hashlib.pbkdf2_hmac(
        "sha256",
        passphrase.encode("utf-8"),
        pbkdf2_salt,
        _PBKDF2_ITERATIONS,
        dklen=32,
    )
    hkdf = HKDF(algorithm=hashes.SHA256(), length=32, salt=hkdf_salt, info=b"")
    return hkdf.derive(master_key)


def _decrypt_hkdf_prefixed(data: str, passphrase: str) -> tuple[str, str]:
    if data.startswith(_HKDF_ENCRYPTED_PREFIX):
        payload = _decode_b64_loose(data[len(_HKDF_ENCRYPTED_PREFIX):])
        if len(payload) < 44:
            return data, "hkdf(%=): payload too short"
        iv = payload[0:12]
        hkdf_salt = payload[12:44]
        ciphertext = payload[44:]
        pbkdf2_salt = _discover_pbkdf2_salt()
        if not pbkdf2_salt:
            return data, "hkdf(%=): missing pbkdf2 salt (env or sync-params)"
        key = _derive_hkdf_aes_key(passphrase, pbkdf2_salt, hkdf_salt)
        plaintext = AESGCM(key).decrypt(iv, ciphertext, None)
        return plaintext.decode("utf-8"), "hkdf(%=): ok"

    if data.startswith(_HKDF_SALTED_ENCRYPTED_PREFIX):
        payload = _decode_b64_loose(data[len(_HKDF_SALTED_ENCRYPTED_PREFIX):])
        if len(payload) < 76:
            return data, "hkdf(%$): payload too short"
        pbkdf2_salt = payload[0:32]
        iv = payload[32:44]
        hkdf_salt = payload[44:76]
        ciphertext = payload[76:]
        key = _derive_hkdf_aes_key(passphrase, pbkdf2_salt, hkdf_salt)
        plaintext = AESGCM(key).decrypt(iv, ciphertext, None)
        return plaintext.decode("utf-8"), "hkdf(%$): ok"

    return data, "hkdf: not prefixed"


def _decrypt_legacy_percent_v2(data: str, passphrase: str) -> tuple[str, str]:
    # Legacy LiveSync V2 format:
    # % + hex(iv 16 bytes) + hex(salt 16 bytes) + base64(ciphertext)
    if not data.startswith("%") or len(data) < 66:
        return data, "legacy(%): not matched"
    if data.startswith(_HKDF_ENCRYPTED_PREFIX) or data.startswith(_HKDF_SALTED_ENCRYPTED_PREFIX):
        return data, "legacy(%): skipped hkdf"

    iv_hex = data[1:33]
    salt_hex = data[33:65]
    ciphertext = _decode_b64_loose(data[65:])
    iv = bytes.fromhex(iv_hex)
    salt = bytes.fromhex(salt_hex)

    for iterations in [_livesync_iterations(passphrase), 100000]:
        try:
            key = _derive_key_v2(passphrase, salt, iterations)
            plaintext = AESGCM(key).decrypt(iv, ciphertext, None)
            return plaintext.decode("utf-8"), f"legacy(%): ok (iterations={iterations})"
        except Exception:
            continue
    return data, "legacy(%): decrypt failed"


def decrypt_livesync_chunk(data: str, passphrase: str) -> str:
    """
    Decrypt a LiveSync encrypted chunk.
    Supports HKDF formats (%=, %$) and legacy % format.
    """
    if not passphrase:
        return data

    if data.startswith("%~"):
        # Keep explicit behavior for unknown/newer format markers.
        return data

    try:
        text, status = _decrypt_hkdf_prefixed(data, passphrase)
        if status.endswith(": ok"):
            return text

        text, status = _decrypt_legacy_percent_v2(data, passphrase)
        if status.startswith("legacy(%): ok"):
            return text
    except Exception:
        pass

    return data  # decryption failed — return raw so caller can surface it


def _resolve_chunk_data(raw: str) -> str:
    """Decrypt if encrypted, otherwise return as-is."""
    if raw.startswith(_LIVESYNC_ENC_PREFIX) and LIVESYNC_PASSPHRASE:
        return decrypt_livesync_chunk(raw, LIVESYNC_PASSPHRASE)
    return raw


def fetch_chunks(chunk_ids: list) -> str:
    """Fetch LiveSync chunk documents in bulk and return joined content."""
    if not chunk_ids:
        return ""
    response = requests.post(
        f"{COUCHDB_URL}/{COUCHDB_DB}/_bulk_get",
        json={"docs": [{"id": cid} for cid in chunk_ids]},
        auth=AUTH,
        timeout=20,
        verify=SSL_VERIFY,
    )
    if not response.ok:
        return ""
    parts = []
    for result in response.json().get("results", []):
        for item in result.get("docs", []):
            doc = item.get("ok", {})
            chunk_data = doc.get("data", "")
            if isinstance(chunk_data, str):
                parts.append(_resolve_chunk_data(chunk_data))
            elif isinstance(chunk_data, list):
                parts.extend(_resolve_chunk_data(c) for c in chunk_data if isinstance(c, str))
    return "".join(parts)


def _decode_attachment(att: dict) -> str:
    """Decode a CouchDB inline attachment to a UTF-8 string."""
    raw = att.get("data", "")
    content_type = att.get("content_type", "")
    if not raw:
        return ""
    try:
        decoded = base64.b64decode(raw).decode("utf-8", errors="replace")
        return decoded
    except Exception:
        return ""


def extract_markdown(doc: dict) -> str:
    # 0. LiveSync chunked format: content split across child chunk documents
    children = doc.get("children")
    if isinstance(children, list) and children:
        joined = fetch_chunks(children)
        if joined.strip():
            return joined

    # 1. Obsidian LiveSync stores chunks in a 'data' array field
    data_field = doc.get("data")
    if isinstance(data_field, list):
        joined = "".join(chunk for chunk in data_field if isinstance(chunk, str))
        if joined.strip():
            return joined

    # 2. Try preferred plain-string field names
    for key in _PREFERRED_KEYS:
        value = doc.get(key)
        if isinstance(value, str) and value.strip():
            return value

    # 3. Try _attachments (LiveSync may store the .md file as an attachment)
    attachments = doc.get("_attachments", {})
    for att_name, att_meta in attachments.items():
        if att_name.endswith(".md") or att_meta.get("content_type", "").startswith("text/"):
            decoded = _decode_attachment(att_meta)
            if decoded.strip():
                return decoded
    # Fall back to any attachment
    for att_meta in attachments.values():
        decoded = _decode_attachment(att_meta)
        if decoded.strip():
            return decoded

    # 4. Last resort: pick the longest string field that isn't metadata
    best_val = ""
    for key, value in doc.items():
        if key in _SKIP_KEYS or key.startswith("_"):
            continue
        if isinstance(value, str) and len(value) > len(best_val):
            best_val = value

    return best_val


def heading_to_anchor(heading: str) -> str:
        normalized = heading.strip().lower()
        normalized = normalized.replace("_", " ")
        normalized = re.sub(r"[^\w\s-]", "", normalized)
        normalized = re.sub(r"\s+", "-", normalized)
        normalized = re.sub(r"-+", "-", normalized).strip("-")
        return normalized or "section"


def split_wikilink_target(target: str) -> tuple[str, str | None]:
        if "#" in target:
                note_part, heading_part = target.split("#", 1)
                return note_part.strip(), heading_part.strip() or None
        return target.strip(), None


def convert_wikilinks(text: str) -> str:
    def repl(match: re.Match) -> str:
        target = match.group(1).strip()
        alias = (match.group(2) or target).strip()
        note_target, heading = split_wikilink_target(target)
        anchor = f"#{heading_to_anchor(heading)}" if heading else ""

        if note_target:
            resolved_target = _resolve_doc_id(note_target)
            href = f"/note/{quote(resolved_target, safe='')}{anchor}"
        else:
            href = anchor or "#"

        return f"[{alias}]({href})"

    return WIKI_LINK_PATTERN.sub(repl, text)


def convert_hashtags(text: str) -> str:
    def repl(match: re.Match) -> str:
        tag = match.group(1)
        href = f"/tag/{quote(tag, safe='')}"
        return f"[#{tag}]({href})"

    return TAG_PATTERN.sub(repl, text)


def convert_bare_urls(text: str) -> str:
    def repl(match: re.Match) -> str:
        url = match.group("url")

        # Skip if already inside markdown link syntax: [label](url)
        start = match.start()
        prefix = text[max(0, start - 2):start]
        if prefix == "](":
            return url

        # Trim common trailing punctuation not part of URL.
        trailing = ""
        while url and url[-1] in ".,;:!?)]":
            trailing = url[-1] + trailing
            url = url[:-1]

        return f"[{url}]({url}){trailing}"

    return URL_PATTERN.sub(repl, text)


def markdown_to_safe_html(md_text: str) -> str:
    transformed = convert_hashtags(convert_wikilinks(convert_bare_urls(md_text)))
    html = markdown.markdown(
        transformed,
        extensions=["extra", "sane_lists", "tables", "toc"],
        extension_configs={"toc": {"slugify": heading_to_anchor}},
    )

    allowed_tags = set(bleach.sanitizer.ALLOWED_TAGS).union(
        {
            "p",
            "pre",
            "code",
            "h1",
            "h2",
            "h3",
            "h4",
            "h5",
            "h6",
            "table",
            "thead",
            "tbody",
            "tr",
            "th",
            "td",
            "hr",
            "br",
            "blockquote",
            "ul",
            "ol",
            "li",
            "a",
            "img",
        }
    )
    allowed_attrs = {
        "*": ["class", "id"],
        "a": ["href", "title", "target", "rel"],
        "img": ["src", "alt", "title"],
    }

    return bleach.clean(html, tags=allowed_tags, attributes=allowed_attrs)


def page(title: str, body: str):
    return render_template_string(
        BASE_TEMPLATE,
        title=title,
        body=body,
    )


def extract_all_tags(doc: dict) -> set[str]:
    tags: set[str] = set()

    raw_tags = doc.get("tags")
    if isinstance(raw_tags, list):
        for value in raw_tags:
            if isinstance(value, str):
                clean = value.strip().lstrip("#")
                if clean:
                    tags.add(clean)

    for key in ("content", "markdown", "body", "text"):
        value = doc.get(key)
        if isinstance(value, str) and value:
            for found in TAG_PATTERN.findall(value):
                tags.add(found)

    return tags


def _load_excluded_tags() -> set[str]:
    excluded: set[str] = set()
    try:
        with open(TAG_EXCLUSIONS_CONFIG, "r", encoding="utf-8") as fh:
            lines = fh.readlines()
    except Exception:
        return excluded

    for line in lines:
        stripped = line.strip()
        if not stripped or stripped.startswith("//") or stripped.startswith("# "):
            continue
        for token in re.split(r"\s+", stripped):
            cleaned = token.strip()
            if not cleaned:
                continue
            if cleaned.startswith("#"):
                cleaned = cleaned[1:]
            cleaned = cleaned.strip()
            if cleaned:
                excluded.add(cleaned.lower())
    return excluded


def _parse_time_value(raw: object) -> float:
    """Parse time value from int, float, or ISO datetime string to unix timestamp."""
    if isinstance(raw, (int, float)):
        return float(raw)
    if isinstance(raw, str):
        cleaned = raw.strip()
        if not cleaned:
            return 0.0
        try:
            return float(cleaned)
        except Exception:
            pass
        try:
            iso = cleaned.replace("Z", "+00:00") if cleaned.endswith("Z") else cleaned
            return datetime.datetime.fromisoformat(iso).timestamp()
        except Exception:
            return 0.0
    return 0.0


def _note_last_modified_value(note_record: dict) -> float:
    """Get last-modified timestamp for a note: mtime > ctime > updated (legacy)."""
    mtime = _parse_time_value(note_record.get("mtime"))
    if mtime > 0:
        return mtime
    ctime = _parse_time_value(note_record.get("ctime"))
    if ctime > 0:
        return ctime
    return _parse_time_value(note_record.get("updated"))


def _last_cache_refresh_text() -> str:
    try:
        modified_ts = os.path.getmtime(LOCAL_CACHE_INDEX)
    except Exception:
        return "Last refresh: never"

    return "Last refresh: " + time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(modified_ts))


def _normalize_note_key(value: str) -> str:
    cleaned = value.strip().strip("/")
    cleaned = re.sub(r"(?i)\.md$", "", cleaned)
    return cleaned.lower()


def _canonical_note_key(doc_id: str) -> str:
    base = os.path.basename(str(doc_id).strip())
    return _normalize_note_key(base or doc_id)


def _doc_id_priority(doc_id: str) -> tuple[int, int]:
    # Prefer deeper paths over basenames, then longer IDs.
    return (doc_id.count("/"), len(doc_id))


def _cache_filename(doc_id: str) -> str:
    # Safe stable filename derived from doc id.
    encoded = quote(doc_id, safe="")
    return re.sub(r"(?i)(\.md)+$", "", encoded)


def _is_blocked_cache_doc_id(doc_id: str) -> bool:
    encoded = quote(doc_id, safe="")
    return any(encoded.startswith(prefix) for prefix in _BLOCKED_CACHE_PREFIXES)


def _blocked_id_regex() -> str:
    """Build a CouchDB _id regex from blocked URL-encoded prefixes."""
    parts = []
    for prefix in _BLOCKED_CACHE_PREFIXES:
        if not prefix:
            continue
        parts.append(re.escape(unquote(prefix)))
    if not parts:
        return ""
    return r"^(?:" + "|".join(parts) + r")"


def _load_cache_index() -> None:
    global _CACHED_NOTES
    if not os.path.exists(LOCAL_CACHE_INDEX):
        _CACHED_NOTES = {}
        return

    try:
        with open(LOCAL_CACHE_INDEX, "r", encoding="utf-8") as fh:
            records = json.load(fh)
    except Exception:
        _CACHED_NOTES = {}
        return

    notes: dict[str, dict] = {}
    selected_doc_id_by_key: dict[str, str] = {}
    if isinstance(records, list):
        for item in records:
            if not isinstance(item, dict):
                continue
            doc_id = str(item.get("id", "")).strip()
            if not doc_id:
                continue
            if _is_blocked_cache_doc_id(doc_id):
                continue

            dedupe_key = _canonical_note_key(doc_id)
            previous_id = selected_doc_id_by_key.get(dedupe_key)
            if not previous_id:
                notes[doc_id] = item
                selected_doc_id_by_key[dedupe_key] = doc_id
                continue

            winner = sorted([previous_id, doc_id], key=_doc_id_priority, reverse=True)[0]
            if winner == doc_id:
                notes.pop(previous_id, None)
                notes[doc_id] = item
                selected_doc_id_by_key[dedupe_key] = doc_id
    
    # Filter out deleted notes by checking CouchDB
    _CACHED_NOTES = _filter_deleted_notes(notes)


def _filter_deleted_notes(notes: dict[str, dict]) -> dict[str, dict]:
    if not notes:
        return notes
    
    # remove notes whose markdown files don't exist
    orphaned_ids: set[str] = set()
    for doc_id, note in notes.items():
        file_path = os.path.join(LOCAL_CACHE_NOTES_DIR, note.get("file", ""))
        if not os.path.exists(file_path):
            orphaned_ids.add(doc_id)
    
    all_removed = orphaned_ids
    if all_removed:
        # Re-save index without deleted notes
        remaining = {doc_id: note for doc_id, note in notes.items() if doc_id not in all_removed}
        try:
            records = list(remaining.values())
            with open(LOCAL_CACHE_INDEX, "w", encoding="utf-8") as fh:
                json.dump(records, fh, ensure_ascii=True, indent=2)
        except Exception:
            pass
        return remaining
    
    return notes




def _clear_local_cache() -> None:
    """Delete local cache artifacts so each run rebuilds from scratch."""
    try:
        if os.path.exists(LOCAL_CACHE_INDEX):
            os.remove(LOCAL_CACHE_INDEX)
    except Exception:
        pass

    try:
        if os.path.isdir(LOCAL_CACHE_NOTES_DIR):
            shutil.rmtree(LOCAL_CACHE_NOTES_DIR)
    except Exception:
        pass


def _get_total_docs_count() -> int:
    """Best-effort total row count for CLI progress display."""
    try:
        response = requests.get(
            f"{COUCHDB_URL}/{COUCHDB_DB}/_all_docs?limit=0",
            auth=AUTH,
            timeout=12,
            verify=SSL_VERIFY,
        )
        if not response.ok:
            return 0
        payload = response.json()
        return int(payload.get("total_rows", 0))
    except Exception:
        return 0


def _print_cache_progress(scanned: int, total: int, cached: int, elapsed: float = 0.0) -> None:
    width = 30
    mins, secs = divmod(int(elapsed), 60)
    time_str = f"{mins}m{secs:02d}s"
    if total > 0:
        ratio = min(1.0, max(0.0, scanned / total))
        filled = int(width * ratio)
        bar = "#" * filled + "-" * (width - filled)
        line = f"\rLoading notes [{bar}] {scanned}/{total} scanned | {cached} cached | {time_str}"
    else:
        pulse = scanned % (width + 1)
        bar = "#" * pulse + "-" * (width - pulse)
        line = f"\rLoading notes [{bar}] {scanned} scanned | {cached} cached | {time_str}"

    sys.stdout.write(line)
    sys.stdout.flush()


def build_markdown_cache() -> tuple[int, int]:
    """Fetch markdown notes once from CouchDB and write cache files + index."""
    global _CACHED_NOTES

    _clear_local_cache()
    _CACHED_NOTES = {}
    os.makedirs(LOCAL_CACHE_NOTES_DIR, exist_ok=True)

    selected_notes: dict[str, dict] = {}
    bookmark = None
    scanned = 0
    total_docs = _get_total_docs_count()
    _start_time = time.monotonic()

    _print_cache_progress(scanned=0, total=total_docs, cached=0, elapsed=0.0)

    while True:
        payload = {
            "selector": {"_id": {"$gt": None}},
            "fields": ["_id", "title", "name", "mtime", "ctime", "tags", "content", "markdown", "body", "text", "data", "children","deleted"],
            "limit": 500,
            "sort": [{"_id": "asc"}],
        }
        if bookmark:
            payload["bookmark"] = bookmark

        response = requests.post(
            f"{COUCHDB_URL}/{COUCHDB_DB}/_find",
            json=payload,
            auth=AUTH,
            timeout=20,
            verify=SSL_VERIFY,
        )
        if not response.ok:
            break

        body = response.json()
        docs = body.get("docs", [])
        scanned += len(docs)

        for d in docs:
            doc_id = str(d.get("_id", "")).strip()
            if not doc_id:
                continue
            if d.get("deleted"):
                continue
            if _is_blocked_cache_doc_id(doc_id):
                continue

            md_text = extract_markdown(d)
            if not isinstance(md_text, str) or not md_text.strip():
                continue

            title = str(d.get("title") or d.get("name") or doc_id)
            tags = extract_all_tags(d)
            tags.update(TAG_PATTERN.findall(md_text))

            dedupe_key = _canonical_note_key(doc_id)
            current = {
                "id": doc_id,
                "title": title,
                "mtime": d.get("mtime"),
                "ctime": d.get("ctime"),
                "tags": set(tags),
                "md_text": md_text,
            }
            existing = selected_notes.get(dedupe_key)
            if not existing:
                selected_notes[dedupe_key] = current
            else:
                existing_id = str(existing.get("id", ""))
                winner = sorted([existing_id, doc_id], key=_doc_id_priority, reverse=True)[0]
                if winner == doc_id:
                    current_tags = current.get("tags", set())
                    if isinstance(current_tags, set):
                        current_tags.update(existing.get("tags", set()))
                    selected_notes[dedupe_key] = current
                else:
                    existing_tags = existing.get("tags", set())
                    if isinstance(existing_tags, set):
                        existing_tags.update(tags)

        _print_cache_progress(scanned=scanned, total=total_docs, cached=len(selected_notes), elapsed=time.monotonic() - _start_time)

        new_bookmark = body.get("bookmark")
        if not docs or not new_bookmark or new_bookmark == bookmark:
            break
        bookmark = new_bookmark

    records: list[dict] = []
    for dedupe_key in sorted(selected_notes.keys()):
        note = selected_notes[dedupe_key]
        doc_id = str(note.get("id", "")).strip()
        md_text = str(note.get("md_text", ""))
        if not doc_id or not md_text.strip():
            continue

        filename = _cache_filename(doc_id)
        file_path = os.path.join(LOCAL_CACHE_NOTES_DIR, filename)
        try:
            with open(file_path, "w", encoding="utf-8") as fh:
                fh.write(md_text)
        except Exception:
            continue

        tags_val = note.get("tags", set())
        if not isinstance(tags_val, set):
            tags_val = set()

        records.append(
            {
                "id": doc_id,
                "title": str(note.get("title") or doc_id),
                "mtime": note.get("mtime"),
                "ctime": note.get("ctime"),
                "tags": sorted(tags_val, key=lambda t: t.lower()),
                "file": filename,
            }
        )

    if records:
        try:
            with open(LOCAL_CACHE_INDEX, "w", encoding="utf-8") as fh:
                json.dump(records, fh, ensure_ascii=True, indent=2)
        except Exception:
            pass

    _load_cache_index()
    elapsed_total = time.monotonic() - _start_time
    _print_cache_progress(scanned=scanned, total=total_docs, cached=len(records), elapsed=elapsed_total)
    mins, secs = divmod(int(elapsed_total), 60)
    sys.stdout.write(f"\nDone. {len(records)} notes cached in {mins}m{secs:02d}s.\n")
    sys.stdout.flush()
    return scanned, len(records)


def ensure_cache_loaded() -> None:
    global _CACHE_READY
    global _REBUILD_CACHE
    if _CACHE_READY:
        return

    if not _REBUILD_CACHE:
        _load_cache_index()
        app.logger.info(
            "Loaded existing cache by default; cached notes=%s",
            len(_CACHED_NOTES),
        )
        _CACHE_READY = True
        return

    scanned, cached = build_markdown_cache()
    app.logger.info("Markdown cache ready: scanned=%s cached=%s", scanned, cached)
    _CACHE_READY = True


def _read_cached_markdown(doc_id: str) -> str:
    note = _CACHED_NOTES.get(doc_id)
    if not note:
        return ""
    filename = note.get("file", "")
    if not isinstance(filename, str) or not filename:
        return ""
    path = os.path.join(LOCAL_CACHE_NOTES_DIR, filename)
    try:
        with open(path, "r", encoding="utf-8") as fh:
            return fh.read()
    except Exception:
        return ""


def _resolve_doc_id(doc_id: str) -> str:
    raw = str(doc_id).strip()
    if not raw:
        return raw
    if raw in _CACHED_NOTES:
        return raw

    target_key = _normalize_note_key(raw)
    if not target_key:
        return raw

    candidates: list[str] = []
    for cached_id in _CACHED_NOTES.keys():
        cid = str(cached_id).strip()
        if not cid:
            continue
        if target_key == _normalize_note_key(cid) or target_key == _normalize_note_key(os.path.basename(cid)):
            candidates.append(cid)

    if not candidates:
        return raw

    return sorted(set(candidates), key=_doc_id_priority, reverse=True)[0]


def _note_match_keys(doc_id: str, title: str) -> set[str]:
    keys: set[str] = set()
    candidates = [
        doc_id,
        title,
        os.path.basename(doc_id),
        os.path.basename(title),
    ]
    for candidate in candidates:
        if not candidate:
            continue
        key = _normalize_note_key(candidate)
        if key:
            keys.add(key)
    return keys


def _wikilink_targets(md_text: str) -> set[str]:
    targets: set[str] = set()
    for match in WIKI_LINK_PATTERN.finditer(md_text):
        target = match.group(1).strip()
        note_target, _heading = split_wikilink_target(target)
        if not note_target:
            continue
        normalized = _normalize_note_key(note_target)
        if normalized:
            targets.add(normalized)
            targets.add(_normalize_note_key(os.path.basename(note_target)))
    return targets


def _find_backlinks(doc_id: str, title: str) -> list[tuple[str, str]]:
    resolved_target_id = _resolve_doc_id(doc_id)
    target_keys = _note_match_keys(resolved_target_id, title)
    if not target_keys:
        return []

    links: list[tuple[str, str]] = []
    seen_source_ids: set[str] = set()
    docs = sorted(_CACHED_NOTES.values(), key=lambda d: str(d.get("id", "")).lower())
    for d in docs:
        source_id = str(d.get("id", "")).strip()
        if not source_id:
            continue

        resolved_source_id = _resolve_doc_id(source_id)
        if not resolved_source_id or resolved_source_id == resolved_target_id:
            continue
        if resolved_source_id in seen_source_ids:
            continue

        source_md = _read_cached_markdown(source_id)
        if not source_md:
            continue

        if target_keys.intersection(_wikilink_targets(source_md)):
            resolved_note = _CACHED_NOTES.get(resolved_source_id, d)
            source_title = str(resolved_note.get("title") or resolved_source_id)
            links.append((resolved_source_id, source_title))
            seen_source_ids.add(resolved_source_id)

    return links


@app.route("/")
def home():
    ensure_cache_loaded()

    docs = sorted(_CACHED_NOTES.values(), key=lambda d: str(d.get("id", "")).lower())
    cache_status = request.args.get("cache_status", "").strip()
    safe_status = bleach.clean(cache_status)
    last_refresh = bleach.clean(_last_cache_refresh_text())

    excluded_tags = _load_excluded_tags()
    if docs:
        tag_counts: dict[str, int] = {}
        for d in docs:
            for tag in d.get("tags", []):
                if isinstance(tag, str) and tag and tag.lower() not in excluded_tags:
                    tag_counts[tag] = tag_counts.get(tag, 0) + 1

        if tag_counts:
            tag_items = []
            sorted_tags = sorted(tag_counts.items(), key=lambda item: (-item[1], item[0].lower()))
            for tag, count in sorted_tags:
                href = f"/tag/{quote(tag, safe='')}"
                tag_items.append(
                    f"<li><a href='{href}'>#{bleach.clean(tag)}</a> ({count})</li>"
                )
            tag_list = f"<h2>All Tags</h2><ul>{''.join(tag_items)}</ul>"
        else:
            tag_list = "<h2>All Tags</h2><p class='meta'>No tags found.</p>"
    else:
        tag_list = "<h2>All Tags</h2><p class='meta'>No tags found.</p>"

    rebuild_controls = (
        "<form method='post' action='/rebuild_cache' "
        "style='margin: 0 0 1rem 0; display: flex; align-items: center; gap: 0.8rem;'>"
        "<button type='submit'>Fetch and Rebuild Cache</button>"
        f"<span class='meta' style='margin: 0;'>{last_refresh}</span>"
        "</form>"
    )
    status_block = f"<p class='meta'>{safe_status}</p>" if safe_status else ""

    body = (
        "<h1>CouchDB Obsidian Viewer</h1>"
        f"<p class='meta'>{len(docs)} notes (local cache)</p>"
        f"{rebuild_controls}"
        f"{status_block}"
        f"{tag_list}"
    )
    return page("Home", body)


@app.route("/rebuild_cache", methods=["POST"])
def rebuild_cache():
    scanned, cached = build_markdown_cache()
    message = f"Cache rebuild complete: scanned={scanned}, cached={cached}."
    return redirect(url_for("home", cache_status=message))


@app.route("/all_files")
def all_files():
    ensure_cache_loaded()

    docs = sorted(
        _CACHED_NOTES.values(),
        key=lambda d: (-_note_last_modified_value(d), str(d.get("id", "")).lower()),
    )
    if not docs:
        body = "<h1>All Files</h1><p class='meta'>No cached notes found.</p>"
        return page("All Files", body)

    items = []
    seen_doc_ids: set[str] = set()
    for d in docs:
        doc_id = str(d.get("id", "")).strip()
        if not doc_id:
            continue
        resolved_id = _resolve_doc_id(doc_id)
        if not resolved_id or resolved_id in seen_doc_ids:
            continue
        resolved_note = _CACHED_NOTES.get(resolved_id, d)
        label = str(resolved_note.get("title") or resolved_id)
        href = f"/note/{quote(resolved_id, safe='')}"
        items.append(f"<li><a href='{href}'>{bleach.clean(label)}</a></li>")
        seen_doc_ids.add(resolved_id)

    body = (
        "<h1>All Files</h1>"
        f"<p class='meta'>{len(items)} notes</p>"
        f"<ul>{''.join(items)}</ul>"
    )
    return page("All Files", body)


@app.route("/note/<path:doc_id>")
def note(doc_id: str):
    ensure_cache_loaded()
    resolved_doc_id = _resolve_doc_id(doc_id)
    md_text = _read_cached_markdown(resolved_doc_id)
    if not md_text:
        abort(404, description=f"No cached markdown content found for '{doc_id}'.")

    note_info = _CACHED_NOTES.get(resolved_doc_id, {})
    title = str(note_info.get("title") or resolved_doc_id)
    content_html = markdown_to_safe_html(md_text)
    backlinks = _find_backlinks(resolved_doc_id, title)
    if backlinks:
        backlink_items = []
        for src_id, src_title in backlinks:
            href = f"/note/{quote(src_id, safe='')}"
            backlink_items.append(f"<li><a href='{href}'>{bleach.clean(src_title)}</a></li>")
        backlinks_block = f"<h2>Backlinks</h2><ul>{''.join(backlink_items)}</ul>"
    else:
        backlinks_block = "<h2>Backlinks</h2><p class='meta'>No backlinks found.</p>"

    body = (
        f"<h1>{bleach.clean(str(title))}</h1>"
        f"<div class=\"meta\">doc id: {bleach.clean(resolved_doc_id)}</div>"
        f"{content_html}"
        f"{backlinks_block}"
    )
    return page(str(title), body)


@app.route("/tag/<path:tag>")
def tag_view(tag: str):
    ensure_cache_loaded()
    safe_tag = tag.strip("/")
    if not safe_tag:
        abort(404, description="Tag not provided")

    docs = list(_CACHED_NOTES.values())
    if not docs:
        return page(f"Tag #{safe_tag}", f"<h1>#{bleach.clean(safe_tag)}</h1><p>No notes found for this tag.</p>")

    requested = safe_tag.lower()
    groups: dict[str, set[str]] = {}
    matching_doc_ids: set[str] = set()

    for d in docs:
        doc_id = str(d.get("id", ""))
        tags_for_doc = set(tag for tag in d.get("tags", []) if isinstance(tag, str))

        for doc_tag in tags_for_doc:
            lowered = doc_tag.lower()
            if lowered == requested or lowered.startswith(f"{requested}/"):
                matching_doc_ids.add(doc_id)

                if lowered == requested:
                    group_key = safe_tag
                else:
                    remainder = doc_tag[len(safe_tag):].lstrip("/")
                    first_child = remainder.split("/", 1)[0]
                    group_key = f"{safe_tag}/{first_child}" if first_child else safe_tag

                groups.setdefault(group_key, set()).add(doc_id)

    if not matching_doc_ids:
        return page(f"Tag #{safe_tag}", f"<h1>#{bleach.clean(safe_tag)}</h1><p>No notes found for this tag.</p>")

    docs_by_id = {str(d.get("id", "")): d for d in docs}
    items = []
    sorted_doc_ids = sorted(
        matching_doc_ids,
        key=lambda doc_id: (-_note_last_modified_value(docs_by_id.get(doc_id, {})), doc_id),
    )
    for doc_id in sorted_doc_ids:
        d = docs_by_id.get(doc_id, {})
        label = str(d.get("title") or doc_id)
        items.append(f"<li><a href='/note/{quote(doc_id, safe='')}'>{bleach.clean(label)}</a></li>")


    subgroup_items = []
    for group_tag in sorted(groups.keys()):
        count = len(groups[group_tag])
        subgroup_items.append(
            f"<li><a href='/tag/{quote(group_tag, safe='')}'>{bleach.clean(group_tag)}</a> ({count})</li>"
        )

    group_block = ""
    if subgroup_items:
        group_block = f"<h2>Tag Groups</h2><ul>{''.join(subgroup_items)}</ul>"

    body = (
        f"<h1>#{bleach.clean(safe_tag)}</h1>"
        f"<p class='meta'>Matching notes: {len(items)}</p>"
        f"{group_block}"
        f"<h2>Notes</h2><ul>{''.join(items)}</ul>"
    )
    return page(f"Tag #{safe_tag}", body)


@app.route("/debug/<path:doc_id>")
def debug_doc(doc_id: str):
    """Show raw field names and types for a document — useful for diagnosing missing content."""
    import json as _json
    doc = fetch_doc(doc_id)
    rows = []
    for k, v in doc.items():
        if k == "_attachments":
            for att_name, att_meta in (v or {}).items():
                att_info = {kk: vv for kk, vv in att_meta.items() if kk != "data"}
                rows.append(f"<tr><td><code>_attachments / {bleach.clean(att_name)}</code></td>"
                            f"<td>{bleach.clean(type(att_meta).__name__)}</td>"
                            f"<td><pre>{bleach.clean(_json.dumps(att_info, indent=2))}</pre></td></tr>")
        else:
            preview = ""
            if isinstance(v, str):
                preview = bleach.clean(v[:300])
            elif isinstance(v, (list, dict)):
                try:
                    preview = f"<pre>{bleach.clean(_json.dumps(v, indent=2)[:600])}</pre>"
                except Exception:
                    preview = bleach.clean(repr(v)[:300])
            else:
                preview = bleach.clean(str(v)[:300])
            rows.append(f"<tr><td><code>{bleach.clean(k)}</code></td>"
                        f"<td>{bleach.clean(type(v).__name__)}</td>"
                        f"<td>{preview}</td></tr>")

    table = (
        "<table style='width:100%;border-collapse:collapse'>"
        "<thead><tr><th style='text-align:left'>Field</th><th>Type</th><th>Preview</th></tr></thead>"
        f"<tbody>{''.join(rows)}</tbody></table>"
    )
    body = f"<h1>Debug: {bleach.clean(doc_id)}</h1>{table}"
    return page(f"Debug: {doc_id}", body)


@app.errorhandler(404)
def not_found(err):
    return page("Not found", f"<h1 class='error'>Not Found</h1><p>{bleach.clean(str(err))}</p>"), 404


@app.errorhandler(500)
def server_error(err):
    return page("Server error", f"<h1 class='error'>Server Error</h1><p>{bleach.clean(str(err))}</p>"), 500


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="CouchDB Obsidian Viewer")
    parser.add_argument(
        "--rebuild-cache",
        action="store_true",
        help="Regenerate local cache files from CouchDB on startup",
    )
    args = parser.parse_args()

    _REBUILD_CACHE = args.rebuild_cache

    if args.rebuild_cache:
        scanned, cached = build_markdown_cache()
        app.logger.info("Markdown cache rebuilt: scanned=%s cached=%s", scanned, cached)

        restart_argv = [arg for arg in sys.argv if arg != "--rebuild-cache"]
        try:
            os.execv(sys.executable, [sys.executable, *restart_argv])
        except Exception as exc:
            app.logger.error("Failed to restart without --rebuild-cache: %s", exc)
            _REBUILD_CACHE = False

    port = int(os.getenv("FLASK_PORT", "5000"))
    ensure_cache_loaded()
    app.run(host="0.0.0.0", port=port, debug=True)
