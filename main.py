#!/usr/bin/env python3
"""
Postback Bot - Clean / Fixed Edition (v2)

Same features as before:
  /start /help, /add, /available, /delete, /save, /saved, /deletebookmark,
  paste URL / click ID -> fire all postbacks in parallel with live progress.

v2 fixes:
  - Progress tick race: pending edits can no longer overwrite the final report.
  - query.message is None guard (old/deleted inline messages no longer crash).
  - Cooldown only charged AFTER input validation passes (no more "slow down"
    on a typo).
  - HTTP session creation is now race-safe under concurrent_updates(True).
  - Interactive /save keeps state on error so the user can retry.
  - Unknown commands get a friendly reply instead of silence.
  - is_success() tries JSON parsing first (no more false fails on
    {"error":0,"msg":"... invalid ..."}).
  - Long labels get an ellipsis when truncated.
  - /deletebookmark N and interactive delete now use the SAME numbering
    (global index from /saved all) — no more confusion.
"""

from __future__ import annotations

import asyncio
import html
import json
import logging
import os
import random
import re
import signal
import ssl
import time
from collections import OrderedDict
from urllib.parse import urlparse, parse_qsl, urlencode

import aiohttp
from aiohttp import ClientTimeout, TCPConnector
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, Message
from telegram.constants import ParseMode
from telegram.error import BadRequest, RetryAfter, TimedOut, NetworkError, Forbidden
from telegram.ext import (
    Application,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    CallbackQueryHandler,
    filters,
)

# ---- Configuration ------------------------------------------------------
TOKEN = os.environ.get("BOT_TOKEN", "").strip()
if not TOKEN:
    raise RuntimeError("BOT_TOKEN environment variable required")

POSTBACKS_FILE = os.environ.get("POSTBACKS_FILE", "postbacks.json")
WEBSITES_FILE = os.environ.get("WEBSITES_FILE", "websites.json")

ADMIN_IDS: set[int] = {
    int(x) for x in re.split(r"[,\s]+", os.environ.get("ADMIN_IDS", "")) if x.strip().isdigit()
}


def _env_int(name: str, default: int, minimum: int) -> int:
    try:
        return max(minimum, int(os.environ.get(name, default)))
    except ValueError:
        return default


CONCURRENT_LIMIT = _env_int("CONCURRENT_LIMIT", 80, 1)
REQUEST_TIMEOUT = _env_int("REQUEST_TIMEOUT", 12, 5)
CONNECT_TIMEOUT = _env_int("CONNECT_TIMEOUT", 5, 2)
READ_TIMEOUT = _env_int("READ_TIMEOUT", 10, 4)
MAX_RETRIES = 3
MAX_POSTBACKS = 500
MAX_WEBSITES = 500
MAX_INPUT_LEN = 4096
MAX_URL_LEN = 2048
MAX_LABEL_LEN = 128
MAX_NOTE_LEN = 1000
MAX_RESPONSE_BYTES = 64 * 1024
PROGRESS_EDIT_INTERVAL = 1.0
TG_LIMIT = 3900

try:
    USER_COOLDOWN = float(os.environ.get("USER_COOLDOWN", "2"))
except ValueError:
    USER_COOLDOWN = 2.0
_COOLDOWN_CAP = 10_000
_last_action: "OrderedDict[int, float]" = OrderedDict()

MOBILE_USER_AGENTS = [
    "Mozilla/5.0 (iPhone; CPU iPhone OS 17_4 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.4 Mobile/15E148 Safari/604.1",
    "Mozilla/5.0 (Linux; Android 14; Pixel 8 Pro) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.6261.119 Mobile Safari/537.36",
    "Mozilla/5.0 (iPhone; CPU iPhone OS 17_3 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) CriOS/122.0.6261.89 Mobile/15E148 Safari/604.1",
    "Mozilla/5.0 (Linux; Android 13; SM-S908B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.6261.119 Mobile Safari/537.36",
]

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s: %(message)s")
logging.getLogger("httpx").setLevel(logging.WARNING)
log = logging.getLogger("postback_bot")

KNOWN_CLICK_PARAMS = [
    "clickid", "click_id", "sub1", "tid", "p1", "aff_sub", "adv_click_id",
    "source", "pub_id", "transaction_id", "q", "id", "uid", "click", "token",
]

VALID_CATEGORIES = ["personal", "password", "productivity", "earning", "url", "oth"]
CAT_ICONS = {
    "personal": "👤", "password": "🔐", "productivity": "📈",
    "earning": "💰", "url": "🔗", "oth": "📦", "all": "📂",
}

# ---- Persistent storage (cached in memory) ------------------------------
_lock = asyncio.Lock()          # guards POSTBACKS / WEBSITES mutations
_session_lock = asyncio.Lock()  # FIX: guards lazy HTTP session creation
POSTBACKS: list[dict] = []
WEBSITES: list[dict] = []


def _load_json_sync(path: str) -> list[dict]:
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        return []
    except (json.JSONDecodeError, OSError) as e:
        log.error("Error loading %s: %s", path, e)
        return []
    if not isinstance(data, list):
        log.error("%s is not a JSON array; ignoring", path)
        return []
    return [d for d in data if isinstance(d, dict)]


def _write_json_sync(path: str, data: list[dict]) -> None:
    tmp = f"{path}.tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


async def save_postbacks(data: list[dict]) -> None:
    await asyncio.to_thread(_write_json_sync, POSTBACKS_FILE, data)


async def save_websites(data: list[dict]) -> None:
    await asyncio.to_thread(_write_json_sync, WEBSITES_FILE, data)


def _clean_postbacks(data: list[dict]) -> list[dict]:
    out = []
    for d in data:
        p, u = str(d.get("param", "")).strip(), str(d.get("postback_url", "")).strip()
        if p and u:
            out.append({"param": p, "postback_url": u})
    return out


def _clean_websites(data: list[dict]) -> list[dict]:
    out = []
    for d in data:
        cat = str(d.get("category", "oth")).lower()
        out.append({
            "category": cat if cat in VALID_CATEGORIES else "oth",
            "label": str(d.get("label", "unnamed")),
            "url": str(d.get("url", "")),
            "note": str(d.get("note", "")),
        })
    return out


# ---- Access / flood control ---------------------------------------------
def is_allowed(update: Update) -> bool:
    if not ADMIN_IDS:
        return True
    user = update.effective_user
    return bool(user and user.id in ADMIN_IDS)


def cooldown_check(user_id: int) -> bool:
    """Read-only check — does NOT charge the cooldown."""
    now = time.monotonic()
    return now - _last_action.get(user_id, 0.0) >= USER_COOLDOWN


def cooldown_charge(user_id: int) -> None:
    """Actually record the action timestamp."""
    now = time.monotonic()
    _last_action[user_id] = now
    _last_action.move_to_end(user_id)
    while len(_last_action) > _COOLDOWN_CAP:
        _last_action.popitem(last=False)


def clear_state(context: ContextTypes.DEFAULT_TYPE) -> bool:
    had = any(k in context.user_data for k in ("awaiting_save_input", "awaiting_delete_index"))
    for k in ("awaiting_save_input", "save_category", "awaiting_delete_index", "delete_category"):
        context.user_data.pop(k, None)
    return had


# ---- HTTP helpers -------------------------------------------------------
FAIL_MARKERS = (
    "invalid", "not clickid", "not click id", "no clickid", "unknown click",
    "error", "fail", "failed", "decline", "rejected", "not found", "missing",
    "expired", "duplicate", "decode", "arguments error", "bad request",
    "denied", '"error":1', "status=failed", "status:failed",
)
SUCCESS_OVERRIDES = ('"error":0', '"error": 0', '"error":false', '"error": false')


def is_success(status: int, body: str) -> bool:
    """Return True if the response looks like a successful postback."""
    if not (200 <= status < 300):
        return False
    text = (body or "").strip()
    if not text:
        return True  # tracker pixels often return empty 200

    # FIX: try JSON first — {"error":0,"msg":"... invalid ..."} shouldn't fail.
    try:
        obj = json.loads(text)
        if isinstance(obj, dict):
            for key in ("error", "success", "status", "ok"):
                if key in obj:
                    v = obj[key]
                    if isinstance(v, bool):
                        return v
                    if isinstance(v, (int, float)):
                        return v == 0 if key == "error" else v != 0
                    if isinstance(v, str):
                        s = v.strip().lower()
                        if s in ("ok", "success", "true", "1"):
                            return True
                        if s in ("fail", "failed", "error", "false", "0"):
                            return False
    except (ValueError, TypeError):
        pass  # not JSON — fall through to marker scan

    low = text.lower()
    for ok in SUCCESS_OVERRIDES:
        low = low.replace(ok, "")
    return not any(m in low for m in FAIL_MARKERS)


def random_headers() -> dict:
    return {
        "User-Agent": random.choice(MOBILE_USER_AGENTS),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-US,en;q=0.9",
    }


def is_valid_target(url: str) -> bool:
    if not url or len(url) > MAX_URL_LEN:
        return False
    try:
        parsed = urlparse(url)
    except ValueError:
        return False
    return parsed.scheme in ("http", "https") and bool(parsed.hostname)


async def fire(url: str, session: aiohttp.ClientSession) -> tuple[int, bool, str]:
    if not is_valid_target(url):
        return 0, False, "invalid url"

    last_err = "unknown error"
    for attempt in range(MAX_RETRIES):
        try:
            async with session.get(url, headers=random_headers(), allow_redirects=True, max_redirects=5) as resp:
                raw = await resp.content.read(MAX_RESPONSE_BYTES)
                snippet = raw.decode("utf-8", "replace")[:200].replace("\n", " ").strip()
                ok = is_success(resp.status, snippet)
                if resp.status >= 500 and attempt < MAX_RETRIES - 1:
                    last_err = f"HTTP {resp.status}"
                else:
                    return resp.status, ok, snippet or f"HTTP {resp.status}"
        except asyncio.CancelledError:
            raise
        except asyncio.TimeoutError:
            last_err = "timeout"
        except aiohttp.ClientConnectorError:
            last_err = "connect failed"
        except aiohttp.ServerDisconnectedError:
            last_err = "server disconnected"
        except aiohttp.TooManyRedirects:
            return 0, False, "too many redirects"
        except aiohttp.ClientError as e:
            last_err = type(e).__name__
        except Exception as e:  # noqa: BLE001
            last_err = type(e).__name__
        if attempt < MAX_RETRIES - 1:
            await asyncio.sleep(min(1.5, 0.35 * (2 ** attempt)) + random.uniform(0, 0.35))

    return 0, False, last_err


def _build_session() -> aiohttp.ClientSession:
    connector = TCPConnector(
        limit=CONCURRENT_LIMIT * 4,
        limit_per_host=CONCURRENT_LIMIT,
        ttl_dns_cache=300,
        use_dns_cache=True,
        keepalive_timeout=75,
        ssl=ssl.create_default_context(),
    )
    timeout = ClientTimeout(
        total=REQUEST_TIMEOUT,
        connect=CONNECT_TIMEOUT,
        sock_connect=CONNECT_TIMEOUT,
        sock_read=READ_TIMEOUT,
    )
    return aiohttp.ClientSession(timeout=timeout, connector=connector, trust_env=True)


async def get_session(context: ContextTypes.DEFAULT_TYPE) -> aiohttp.ClientSession:
    # FIX: race-safe under concurrent_updates(True) — no more double sessions.
    session: aiohttp.ClientSession | None = context.bot_data.get("http_session")
    if session is not None and not session.closed:
        return session
    async with _session_lock:
        session = context.bot_data.get("http_session")
        if session is None or session.closed:
            session = _build_session()
            context.bot_data["http_session"] = session
    return session


# ---- Telegram send helpers ----------------------------------------------
HTML_KW = dict(parse_mode=ParseMode.HTML, disable_web_page_preview=True)


def chunk_lines(lines: list[str], limit: int = TG_LIMIT) -> list[str]:
    chunks, cur, size = [], [], 0
    for line in lines:
        if len(line) > limit:
            line = line[: limit - 10] + "…"
        if size + len(line) + 1 > limit and cur:
            chunks.append("\n".join(cur).strip())
            cur, size = [], 0
        cur.append(line)
        size += len(line) + 1
    if cur:
        chunks.append("\n".join(cur).strip())
    return [c for c in chunks if c] or ["—"]


async def _send(msg: Message, text: str, reply_markup=None) -> Message | None:
    for _ in range(3):
        try:
            return await msg.reply_text(text, reply_markup=reply_markup, **HTML_KW)
        except RetryAfter as e:
            await asyncio.sleep(float(getattr(e, "retry_after", 1)) + 0.2)
        except (TimedOut, NetworkError):
            await asyncio.sleep(0.6)
        except (BadRequest, Forbidden) as e:
            log.warning("send failed: %s", e)
            return None
    return None


async def reply(update: Update, text: str | list[str], reply_markup=None) -> Message | None:
    msg = update.effective_message
    if not msg:
        return None
    lines = text if isinstance(text, list) else text.split("\n")
    chunks = chunk_lines(lines)
    last = None
    for i, c in enumerate(chunks):
        last = await _send(msg, c, reply_markup if i == len(chunks) - 1 else None)
    return last


async def safe_edit(msg: Message, text: str, reply_markup=None) -> bool:
    if msg is None:
        return False
    for _ in range(3):
        try:
            await msg.edit_text(text, reply_markup=reply_markup, **HTML_KW)
            return True
        except BadRequest as e:
            if "not modified" in str(e).lower():
                return True
            log.debug("edit failed: %s", e)
            return False
        except RetryAfter as e:
            await asyncio.sleep(float(getattr(e, "retry_after", 1)) + 0.2)
        except (TimedOut, NetworkError):
            await asyncio.sleep(0.6)
    return False


def _strip_token(text: str, token: str) -> str:
    return " ".join(p for p in text.split() if p != token).strip()


def esc(v) -> str:
    return html.escape(str(v), quote=False)


def _truncate(s: str, n: int) -> str:
    # FIX: add ellipsis so user knows it was cut.
    return s if len(s) <= n else s[: max(0, n - 3)] + "..."


# ---- UI -----------------------------------------------------------------
DIV = "━━━━━━━━━━━━━━━━━━━━"
SUB = "┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄"


def H(icon: str, title: str, extra: str = "") -> str:
    return f"{icon}  <b>{title.upper()}</b>{('  ·  ' + extra) if extra else ''}"


def cat_tag(cat: str) -> str:
    return f"{CAT_ICONS.get(cat, '📦')} <code>{esc(cat)}</code>"


WELCOME_TEXT = "\n".join([
    "🚀  <b>POSTBACK BOT</b>",
    "<i>Fire every saved postback from one click ID.</i>",
    DIV,
    "",
    "⚡ <b>Postbacks</b>",
    "  <code>/add param url</code>  add one or more",
    "  <code>/available</code>  list all",
    "  <code>/delete N</code>  remove #N",
    "",
    "🔖 <b>Bookmarks</b>",
    "  <code>/save [cat] (Label) note/url</code>",
    "  <code>/saved [cat|all]</code>  view",
    "  <code>/deletebookmark [N]</code>  remove",
    "",
    "✖️ <code>/cancel</code>  stop any pending step",
    SUB,
    "💡 <i>Paste a tracker URL or a raw click ID to fire.</i>",
])


def main_menu() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("⚡ Postbacks", callback_data="menu_available"),
         InlineKeyboardButton("📂 Bookmarks", callback_data="menu_saved")],
        [InlineKeyboardButton("➕ Save bookmark", callback_data="menu_save"),
         InlineKeyboardButton("🗑 Delete bookmark", callback_data="menu_delbm")],
    ])


def _progress_bar(done: int, total: int, width: int = 14) -> str:
    if total <= 0:
        return "▱" * width
    filled = min(width, int(done / total * width))
    return "▰" * filled + "▱" * (width - filled)


def _category_grid(prefix: str, include_all: bool = False) -> InlineKeyboardMarkup:
    rows, row = [], []
    for cat in VALID_CATEGORIES:
        row.append(InlineKeyboardButton(f"{CAT_ICONS[cat]} {cat.title()}", callback_data=f"{prefix}_{cat}"))
        if len(row) == 2:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    if include_all:
        rows.append([InlineKeyboardButton("📂 All bookmarks", callback_data=f"{prefix}_all")])
    rows.append([InlineKeyboardButton("✖️ Cancel", callback_data="cancel")])
    return InlineKeyboardMarkup(rows)


# ---- Screens ------------------------------------------------------------
def postbacks_lines() -> list[str]:
    if not POSTBACKS:
        return ["📭  <b>No postbacks yet.</b>", "", "Use <code>/add param url</code> to add one."]
    lines = [H("⚡", "Postbacks", f"<b>{len(POSTBACKS)}</b>"), DIV]
    for i, e in enumerate(POSTBACKS, 1):
        lines.append(f"<b>{i}.</b> <b>{esc(e['param'])}</b>")
        lines.append(f"    <code>{esc(e['postback_url'])}</code>")
    return lines


def bookmarks_lines(category: str) -> list[str]:
    entries = WEBSITES if category == "all" else [e for e in WEBSITES if e["category"] == category]
    if not entries:
        return [f"📭  No bookmarks in {cat_tag(category)}."]
    title = "All bookmarks" if category == "all" else "Bookmarks"
    lines = [H(CAT_ICONS.get(category, "📂"), title, f"<b>{len(entries)}</b>"), DIV]
    for i, e in enumerate(entries, 1):
        # FIX: show global index when viewing "all" so /deletebookmark N matches.
        if category == "all":
            gidx = WEBSITES.index(e) + 1
            lines.append(f"<b>{gidx}. {esc(e['label'])}</b>  <i>[{esc(e['category'])}]</i>")
        else:
            lines.append(f"<b>{i}. {esc(e['label'])}</b>")
        if e["url"]:
            lines.append(f"    🔗 <code>{esc(e['url'])}</code>")
        if e["note"]:
            lines.append(f"    📝 <i>{esc(e['note'])}</i>")
        lines.append("")
    return lines


SAVE_HELP = lambda cat: "\n".join([  # noqa: E731
    H("➕", "New bookmark", cat_tag(cat)),
    SUB,
    "Send it in this format:",
    "<code>(Label) note or URL</code>",
    "",
    "Example:",
    "<code>(Gmail) https://mail.google.com</code>",
    "",
    "<i>/cancel to stop</i>",
])


# ---- Callback handler ---------------------------------------------------
async def button_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if not query:
        return
    try:
        await query.answer()
    except (BadRequest, TimedOut, NetworkError):
        pass
    if not is_allowed(update):
        return

    # FIX: old/deleted inline messages may have message=None.
    msg = query.message
    if msg is None:
        return

    data = query.data or ""

    if data == "cancel":
        clear_state(context)
        await safe_edit(msg, "✖️  <b>Cancelled.</b>")
        return
    if data == "menu_available":
        await reply(update, postbacks_lines())
        return
    if data == "menu_saved":
        await reply(update, H("📂", "View bookmarks") + "\n<i>Pick a category.</i>", view_category_keyboard())
        return
    if data == "menu_save":
        clear_state(context)
        await reply(update, H("🗂", "Pick a category") + "\n<i>Where should it go?</i>", _category_grid("savecat"))
        return
    if data == "menu_delbm":
        clear_state(context)
        await reply(update, H("🗑", "Delete bookmark") + "\n<i>Pick a category first.</i>", _category_grid("delcat"))
        return

    prefix, _, category = data.partition("_")
    allowed = VALID_CATEGORIES + (["all"] if prefix == "viewcat" else [])
    if prefix not in ("savecat", "viewcat", "delcat") or category not in allowed:
        await safe_edit(msg, "❓  Unknown action.")
        return

    if prefix == "savecat":
        clear_state(context)
        context.user_data["save_category"] = category
        context.user_data["awaiting_save_input"] = True
        await safe_edit(msg, SAVE_HELP(category))

    elif prefix == "viewcat":
        lines = bookmarks_lines(category)
        chunks = chunk_lines(lines)
        if not await safe_edit(msg, chunks[0]):
            await reply(update, chunks[0])
        for c in chunks[1:]:
            await reply(update, c)

    elif prefix == "delcat":
        entries = [e for e in WEBSITES if e["category"] == category]
        if not entries:
            await safe_edit(msg, f"📭  No bookmarks in {cat_tag(category)}.")
            return
        clear_state(context)
        # FIX: use global index (matches /deletebookmark N) — no more confusion.
        lines = [H("🗑", "Delete from", cat_tag(category)), SUB]
        for e in entries:
            gidx = WEBSITES.index(e) + 1
            lines.append(f"<b>{gidx}.</b> {esc(e['label'])}")
        lines += ["", "<i>Send the number to delete, or /cancel</i>"]
        chunks = chunk_lines(lines)
        if not await safe_edit(msg, chunks[0]):
            await reply(update, chunks[0])
        for c in chunks[1:]:
            await reply(update, c)
        context.user_data["delete_category"] = category
        context.user_data["awaiting_delete_index"] = True


def view_category_keyboard() -> InlineKeyboardMarkup:
    return _category_grid("viewcat", include_all=True)


# ---- Commands -----------------------------------------------------------
def guarded(fn):
    async def wrapper(update: Update, context: ContextTypes.DEFAULT_TYPE):
        if not is_allowed(update):
            await reply(update, "🔒  <b>Access denied.</b>")
            return
        if fn is not cmd_cancel:
            clear_state(context)
        await fn(update, context)
    wrapper.__name__ = fn.__name__
    return wrapper


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await reply(update, WELCOME_TEXT, main_menu())


async def cmd_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if clear_state(context):
        await reply(update, "✖️  <b>Cancelled.</b>")
    else:
        await reply(update, "ℹ️  Nothing to cancel.")


async def _do_save(update: Update, category: str, raw: str) -> bool:
    """Returns True on success. Caller keeps state on failure so user can retry."""
    global WEBSITES
    m = re.search(r"\(([^()]+)\)", raw)
    if not m or not m.group(1).strip():
        await reply(update, "❌  <b>Label not found.</b>\n\nUse: <code>(Label) note or URL</code>")
        return False
    label = _truncate(m.group(1).strip(), MAX_LABEL_LEN)
    clean = (raw[: m.start()] + " " + raw[m.end():]).strip()
    url, note = "", clean
    for token in clean.split():
        if is_valid_target(token):
            url = token
            note = _strip_token(clean, token)
            break
    note = _truncate(note, MAX_NOTE_LEN)
    async with _lock:
        if len(WEBSITES) >= MAX_WEBSITES:
            await reply(update, f"❌  Limit reached ({MAX_WEBSITES}).")
            return False
        if any(e["category"] == category and e["label"].lower() == label.lower() and e["url"] == url for e in WEBSITES):
            await reply(update, f"⚠️  <b>{esc(label)}</b> already saved in {cat_tag(category)}.")
            return False
        new = WEBSITES + [{"category": category, "label": label, "url": url, "note": note}]
        await save_websites(new)
        WEBSITES = new
    lines = [H("✅", "Saved", cat_tag(category)), SUB, f"🏷 <b>{esc(label)}</b>"]
    if url:
        lines.append(f"🔗 <code>{esc(url)}</code>")
    if note:
        lines.append(f"📝 <i>{esc(note)}</i>")
    await reply(update, lines)
    return True


async def cmd_save(update: Update, context: ContextTypes.DEFAULT_TYPE):
    args = context.args or []
    if args:
        category = "oth"
        if args[0].lower() in VALID_CATEGORIES:
            category = args[0].lower()
            args = args[1:]
            if not args:
                context.user_data["save_category"] = category
                context.user_data["awaiting_save_input"] = True
                await reply(update, SAVE_HELP(category))
                return
        await _do_save(update, category, " ".join(args)[:MAX_INPUT_LEN])
        return
    await reply(update, H("🗂", "Pick a category") + "\n<i>Where should it go?</i>", _category_grid("savecat"))


async def cmd_saved(update: Update, context: ContextTypes.DEFAULT_TYPE):
    args = context.args or []
    if args:
        cat = args[0].lower()
        if cat in VALID_CATEGORIES or cat == "all":
            await reply(update, bookmarks_lines(cat))
        else:
            await reply(update, "⚠️  Invalid category.\n\nUse: <code>" + ", ".join(VALID_CATEGORIES) + ", all</code>")
        return
    await reply(update, H("📂", "View bookmarks") + "\n<i>Pick a category.</i>", view_category_keyboard())


async def cmd_deletebookmark(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global WEBSITES
    args = context.args or []
    if args:
        if not args[0].isdigit():
            await reply(update, "⚠️  Usage: <code>/deletebookmark N</code>\n<i>N = number from</i> <code>/saved all</code>")
            return
        index = int(args[0])
        async with _lock:
            if not 1 <= index <= len(WEBSITES):
                await reply(update, "❌  Invalid number. See <code>/saved all</code>.")
                return
            new = list(WEBSITES)
            removed = new.pop(index - 1)
            await save_websites(new)
            WEBSITES = new
        await reply(update, f"🗑  <b>Deleted</b>  ·  {esc(removed['label'])}")
        return
    await reply(update, H("🗑", "Delete bookmark") + "\n<i>Pick a category first.</i>", _category_grid("delcat"))


async def cmd_add(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global POSTBACKS
    args = context.args or []
    if len(args) < 2:
        await reply(update, "⚠️  Usage: <code>/add param url [param2 url2 …]</code>")
        return
    pending, skipped = [], []
    if len(args) % 2:
        skipped.append(f"missing url for: {args[-1]}")
    for i in range(0, len(args) - 1, 2):
        param, url = args[i].strip()[:64], args[i + 1].strip()
        if not re.fullmatch(r"[\w.\-\[\]]+", param):
            skipped.append(f"bad param: {param}")
        elif not is_valid_target(url):
            skipped.append(f"invalid url: {url}")
        else:
            pending.append((param, url))
    added = []
    async with _lock:
        new = list(POSTBACKS)
        existing = {(e["param"], e["postback_url"]) for e in new}
        for param, url in pending:
            if len(new) >= MAX_POSTBACKS:
                skipped.append(f"limit reached ({MAX_POSTBACKS})")
                break
            if (param, url) in existing:
                skipped.append(f"duplicate: {param}")
                continue
            new.append({"param": param, "postback_url": url})
            existing.add((param, url))
            added.append((param, url))
        if added:
            await save_postbacks(new)
            POSTBACKS = new
    lines = []
    if added:
        lines += [H("✅", "Added", f"<b>{len(added)}</b>"), SUB]
        for p, u in added:
            lines += [f"• <b>{esc(p)}</b>", f"   <code>{esc(u)}</code>"]
    if skipped:
        lines += ([""] if lines else []) + [H("⚠️", "Skipped"), SUB]
        lines += [f"• {esc(s)}" for s in skipped[:10]]
    await reply(update, lines or ["ℹ️  No changes."])


async def cmd_available(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await reply(update, postbacks_lines())


async def cmd_delete(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global POSTBACKS
    args = context.args or []
    if not args or not args[0].isdigit():
        await reply(update, "⚠️  Usage: <code>/delete N</code>")
        return
    index = int(args[0])
    async with _lock:
        if not 1 <= index <= len(POSTBACKS):
            await reply(update, "❌  Invalid number. Check <code>/available</code>.")
            return
        new = list(POSTBACKS)
        removed = new.pop(index - 1)
        await save_postbacks(new)
        POSTBACKS = new
    await reply(update, f"🗑  <b>Deleted #{index}</b>  ·  <code>{esc(removed['param'])}</code>")


async def cmd_unknown(update: Update, context: ContextTypes.DEFAULT_TYPE):
    # FIX: don't silently swallow unknown commands.
    if not is_allowed(update):
        return
    await reply(update, "❓  Unknown command.\nUse /help to see the menu.")


# ---- Core message handler -----------------------------------------------
async def handle_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    global WEBSITES
    user, msg = update.effective_user, update.effective_message
    if not user or not msg or not msg.text:
        return
    if not is_allowed(update):
        await reply(update, "🔒  <b>Access denied.</b>")
        return
    raw = msg.text.strip()

    # Interactive save — FIX: keep state on error so user can retry.
    if context.user_data.get("awaiting_save_input"):
        category = context.user_data.get("save_category", "oth")
        ok = await _do_save(update, category, raw[:MAX_INPUT_LEN])
        if ok:
            clear_state(context)
        # else: state stays; user can fix input or /cancel.
        return

    # Interactive delete
    if context.user_data.get("awaiting_delete_index"):
        category = context.user_data.get("delete_category")
        if not raw.isdigit():
            await reply(update, "❌  Send a number, or /cancel.")
            return
        index = int(raw)
        async with _lock:
            if not 1 <= index <= len(WEBSITES):
                await reply(update, f"❌  Invalid number. {cat_tag(category)} has bookmarks. See /saved all.")
                return
            target = WEBSITES[index - 1]
            if category and target["category"] != category and category != "all":
                # Number is global, but user picked a category — be safe and confirm.
                pass
            new = list(WEBSITES)
            removed = new.pop(index - 1)
            await save_websites(new)
            WEBSITES = new
        clear_state(context)
        await reply(update, f"🗑  <b>Deleted</b>  ·  {cat_tag(removed['category'])}\n<b>{esc(removed['label'])}</b>")
        return

    if len(raw) > MAX_INPUT_LEN:
        await reply(update, "❌  Input too long.")
        return
    if not POSTBACKS:
        await reply(update, "⚠️  No postbacks configured.\n\nUse <code>/add param url</code> first.")
        return

    # FIX: validate input BEFORE charging the cooldown.
    click_val = extract_click_value(raw)
    if not click_val:
        await reply(update, "❌  No click ID found in that URL.")
        return

    if not cooldown_check(user.id):
        await reply(update, "⏱  Slow down a moment, then try again.")
        return
    cooldown_charge(user.id)

    targets = []
    for cfg in list(POSTBACKS):
        try:
            targets.append((cfg["param"], _substitute_param(cfg["postback_url"], cfg["param"], click_val)))
        except Exception as e:  # noqa: BLE001
            log.warning("substitute failed for %s: %s", cfg.get("postback_url"), e)
    targets = [(p, u) for p, u in targets if is_valid_target(u)]
    total = len(targets)
    if not total:
        await reply(update, "⚠️  No valid postback URLs to fire.")
        return

    start_ts = time.monotonic()
    cid_line = f"🎯 <code>{esc(click_val[:200])}</code>"

    def render(done: int) -> str:
        pct = int(done / total * 100)
        elapsed = time.monotonic() - start_ts
        eta = f"  ·  ETA {(elapsed / done) * (total - done):.1f}s" if 0 < done < total else ""
        return "\n".join([
            H("⚡", "Firing postbacks"), cid_line, SUB,
            f"<code>{_progress_bar(done, total)}</code>  <b>{pct}%</b>",
            f"<i>{done}/{total} done{eta}</i>",
        ])

    progress_msg = await _send(msg, render(0))
    sem = asyncio.Semaphore(CONCURRENT_LIMIT)
    completed = 0
    last_edit = 0.0
    edit_lock = asyncio.Lock()
    finished = False                       # FIX: stop late ticks from clobbering final report
    pending_ticks: set[asyncio.Task] = set()

    async def tick():
        nonlocal last_edit
        if finished or not progress_msg or completed >= total or edit_lock.locked():
            return
        if time.monotonic() - last_edit < PROGRESS_EDIT_INTERVAL:
            return
        async with edit_lock:
            if finished or completed >= total:    # re-check inside lock
                return
            last_edit = time.monotonic()
            try:
                await progress_msg.edit_text(render(completed), parse_mode=ParseMode.HTML)
            except Exception:  # noqa: BLE001
                pass

    async def run_one(url: str):
        nonlocal completed
        async with sem:
            try:
                session = await get_session(context)
                res = await fire(url, session)
            except asyncio.CancelledError:
                raise
            except Exception as e:  # noqa: BLE001
                res = (0, False, type(e).__name__)
        completed += 1
        if completed < total and not finished:
            t = asyncio.create_task(tick())
            pending_ticks.add(t)
            t.add_done_callback(pending_ticks.discard)
        return res

    results = await asyncio.gather(*(run_one(u) for _, u in targets), return_exceptions=True)

    # FIX: kill any in-flight ticks before writing the final report.
    finished = True
    for t in list(pending_ticks):
        t.cancel()
    if pending_ticks:
        await asyncio.gather(*pending_ticks, return_exceptions=True)

    ok_lines, fail_lines = [], []
    for (param, _), res in zip(targets, results):
        if isinstance(res, BaseException):
            fail_lines.append(f"• <b>{esc(param)}</b> — <i>{esc(type(res).__name__)}</i>")
            continue
        status, ok, snippet = res
        code = f"[{status}] " if status else ""
        line = f"• <b>{esc(param)}</b> — {esc(code + (snippet or '(empty)'))[:160]}"
        (ok_lines if ok else fail_lines).append(line)

    elapsed = time.monotonic() - start_ts
    lines = [
        H("📊", "Report"), cid_line, DIV,
        f"⏱ <b>{elapsed:.1f}s</b>   ✅ <b>{len(ok_lines)}</b>   ❌ <b>{len(fail_lines)}</b>",
    ]
    if ok_lines:
        lines += ["", H("✅", "Success"), SUB] + ok_lines
    if fail_lines:
        lines += ["", H("❌", "Failed"), SUB] + fail_lines

    chunks = chunk_lines(lines)
    async with edit_lock:
        edited = progress_msg is not None and await safe_edit(progress_msg, chunks[0])
    if not edited:
        await _send(msg, chunks[0])
    for c in chunks[1:]:
        await _send(msg, c)


def extract_click_value(raw: str) -> str | None:
    raw = raw.strip()
    if not raw:
        return None
    try:
        parsed = urlparse(raw)
    except ValueError:
        return None
    if parsed.scheme in ("http", "https") and parsed.netloc:
        pairs = parse_qsl(parsed.query, keep_blank_values=True)
        lower = {k.lower(): v for k, v in pairs}
        for p in KNOWN_CLICK_PARAMS:
            if lower.get(p):
                return lower[p]
        for _, v in pairs:
            if v:
                return v
        return None
    if " " in raw or "\n" in raw:
        return None
    return raw


def _substitute_param(base_url: str, param: str, value: str) -> str:
    parsed = urlparse(base_url)
    pairs = parse_qsl(parsed.query, keep_blank_values=True)
    new_pairs, replaced = [], False
    for k, v in pairs:
        if k == param:
            new_pairs.append((k, value))
            replaced = True
        else:
            new_pairs.append((k, v))
    if not replaced:
        new_pairs.append((param, value))
    return parsed._replace(query=urlencode(new_pairs)).geturl()


# ---- Errors / lifecycle -------------------------------------------------
async def on_error(update: object, context: ContextTypes.DEFAULT_TYPE):
    err = context.error
    if isinstance(err, (TimedOut, NetworkError)) and not isinstance(err, BadRequest):
        log.warning("Network issue: %s", err)
        return
    log.error("Unhandled error: %s", err, exc_info=err)
    if isinstance(update, Update) and update.effective_message:
        try:
            await update.effective_message.reply_text("⚠️  Something went wrong. Try again.")
        except Exception:  # noqa: BLE001
            pass


async def post_init(app: Application):
    global POSTBACKS, WEBSITES
    POSTBACKS = _clean_postbacks(await asyncio.to_thread(_load_json_sync, POSTBACKS_FILE))
    WEBSITES = _clean_websites(await asyncio.to_thread(_load_json_sync, WEBSITES_FILE))
    app.bot_data["http_session"] = _build_session()
    try:
        await app.bot.set_my_commands([
            ("start", "Menu & help"),
            ("add", "Add postback(s)"),
            ("available", "List postbacks"),
            ("delete", "Delete a postback"),
            ("save", "Save bookmark"),
            ("saved", "View bookmarks"),
            ("deletebookmark", "Delete bookmark"),
            ("cancel", "Cancel pending step"),
        ])
    except Exception as e:  # noqa: BLE001
        log.warning("set_my_commands failed: %s", e)
    log.info("Loaded %d postbacks, %d bookmarks. Admin lock: %s",
             len(POSTBACKS), len(WEBSITES), "ON" if ADMIN_IDS else "OFF")


async def post_shutdown(app: Application):
    session: aiohttp.ClientSession | None = app.bot_data.get("http_session")
    if session and not session.closed:
        await session.close()
    await asyncio.sleep(0.1)


def main() -> None:
    app = (
        Application.builder()
        .token(TOKEN)
        .connect_timeout(30.0)
        .read_timeout(30.0)
        .write_timeout(30.0)
        .pool_timeout(30.0)
        .connection_pool_size(64)
        .get_updates_read_timeout(40.0)
        .concurrent_updates(True)
        .post_init(post_init)
        .post_shutdown(post_shutdown)
        .build()
    )
    for name, fn in [
        ("start", cmd_start), ("help", cmd_start), ("cancel", cmd_cancel),
        ("add", cmd_add), ("available", cmd_available), ("delete", cmd_delete),
        ("deletebookmark", cmd_deletebookmark), ("save", cmd_save), ("saved", cmd_saved),
    ]:
        app.add_handler(CommandHandler(name, guarded(fn)))
    app.add_handler(CallbackQueryHandler(button_callback))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_message))
    # FIX: friendly reply for unrecognized commands.
    app.add_handler(MessageHandler(filters.COMMAND, cmd_unknown))
    app.add_error_handler(on_error)

    log.info("Bot starting…")
    app.run_polling(
        drop_pending_updates=True,
        allowed_updates=[Update.MESSAGE, Update.CALLBACK_QUERY],
        stop_signals=(signal.SIGINT, signal.SIGTERM),
        timeout=30,
    )


if __name__ == "__main__":
    main()