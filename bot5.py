#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
=====================================================================
 Telegram Remote-URL Video Uploader Bot — ADVANCED EDITION
=====================================================================
 Send the bot a video.txt file formatted as (one entry per line):

     name,https://example.com/path/to/video.mp4

 The bot downloads all URLs SIMULTANEOUSLY, renames each file to the
 name given in the txt and uploads them to the chat as streamable
 videos with a LIVE progress message.

 ── Advanced features ─────────────────────────────────────────────
 ⏸ SOURCE-RATE-LIMIT BRAIN (fixes "410 Gone" after long batches):
     * HTTP 403 / 410 / 429 from a video source no longer kills files.
       The bot waits (escalating pauses) and retries automatically.
     * If several files get blocked at once (= the source banned the
       server IP / quota hit), the WHOLE batch pauses, shows the
       countdown in the status message and resumes by itself.
     * 410-specific hint: links are usually signed & expire — just
       re-send a fresh video.txt and finished files are skipped.

 🧠 UPLOAD MEMORY (resumable batches):
     * Every successfully uploaded name is remembered in
       uploaded_history.json. Re-send the same/refreshed txt and
       already-uploaded files are SKIPPED instantly.
     * /forget clears the memory, /clean sweeps disk.

 ⚡ SPEED (leech-bot techniques):
     * aria2c-style segmented downloads (MAX_SEGMENTS Range conns/file)
     * fasttelethon parallel part uploads (UPLOAD_WORKERS × 512 KB in
       flight per file) + multiple Telegram sessions (round-robin)
     * cryptg native MTProto crypto (auto-detected)
     * optional global download speed cap: DL_SPEED_LIMIT_MBPS

 🧹 STORAGE MANAGEMENT:
     * every file deleted right after its upload, batch dir + txt temp
       removed at batch end, crash leftovers swept at startup / after
       each batch / via /clean. Disk usage reported in every summary.

 Commands:  /start /help · /cancel · /clean (/storage) · /forget
 Config via env vars — see README.md
=====================================================================
"""

import os
import re
import sys
import math
import time
import json
import glob
import random
import hashlib
import asyncio
import logging
import tempfile
import shutil
from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from urllib.parse import urlsplit

import aiohttp
from tqdm import tqdm

from telethon import TelegramClient, events
from telethon.errors import FloodWaitError, MessageNotModifiedError, RPCError
from telethon.tl.functions.upload import SaveFilePartRequest, SaveBigFilePartRequest
from telethon.tl.types import InputFile, InputFileBig

# ----------------------------------------------------------------------
# CONFIG  (override with environment variables if you want)
# ----------------------------------------------------------------------
API_ID        = int(os.environ.get("API_ID", "17074961"))
API_HASH      = os.environ.get("API_HASH", "f0077a7fb095171c22b0172dc9856b9a")
BOT_TOKEN     = os.environ.get("BOT_TOKEN", "5395615159:AAEGnlpyJxtWtpOKYw4IV9IyF_CXvFuyDbI")
OWNER_ID      = int(os.environ.get("OWNER_ID", "1081431445"))   # only this user may use the bot

# ---- speed tuning -----------------------------------------------------
MAX_DOWNLOADS   = int(os.environ.get("MAX_DOWNLOADS", "20"))     # files downloading at once
MAX_UPLOADS     = int(os.environ.get("MAX_UPLOADS", "10"))       # files uploading at once
UPLOAD_SESSIONS = int(os.environ.get("UPLOAD_SESSIONS", "100"))   # parallel Telegram connections
MAX_SEGMENTS    = int(os.environ.get("MAX_SEGMENTS", "100"))      # parallel Range connections per file
SEG_MIN_BYTES   = 16 * 1024 * 1024                              # only segment files bigger than 16 MB
SEG_MIN_PART    = 4 * 1024 * 1024                               # each segment at least 4 MB
UPLOAD_WORKERS  = int(os.environ.get("UPLOAD_WORKERS", "500"))    # parallel 512 KB parts per file upload
PARALLEL_UPLOAD_MIN = int(os.environ.get("PARALLEL_UPLOAD_MIN", str(10 * 1024 * 1024)))
BIG_FILE_MIN    = 10 * 1024 * 1024                              # Telegram rule: >=10 MB → saveBigFilePart
DL_SPEED_LIMIT_MBPS = float(os.environ.get("DL_SPEED_LIMIT_MBPS", "0"))   # 0 = unlimited

# ---- 💾 storage guard (small-disk hosts: queue waits instead of failing) ----
MIN_FREE_GB      = float(os.environ.get("MIN_FREE_GB", "2.0"))    # keep at least this much disk free
MIN_FREE_BYTES   = int(MIN_FREE_GB * 1024 ** 3)                   # ALL downloads pause below this
MAX_DISK_USE_PCT = float(os.environ.get("MAX_DISK_USE_PCT", "98"))  # …or at this % of disk used
STORAGE_CHECK_EVERY = 16 * 1024 * 1024                            # re-check disk every 16 MB written
HARD_FLOOR_BYTES = 32 * 1024 * 1024                               # even the escape download stops below this

# ---- 🌊 wave processing & 🔁 upload retries ----
WAVE_SIZE        = int(os.environ.get("WAVE_SIZE", "100"))         # download+upload N files, then next N (0 = continuous)
UPLOAD_RETRIES   = int(os.environ.get("UPLOAD_RETRIES", "3"))     # failed uploads are retried this often
UPLOAD_RETRY_BASE = float(os.environ.get("UPLOAD_RETRY_BASE", "20"))  # seconds × attempt between retries
FAILED_REQUEUE   = int(os.environ.get("FAILED_REQUEUE", "2"))     # failed files re-join a later wave this often

# ---- source rate-limit handling (the "410 Gone" fix) ------------------
RATE_LIMIT_STATUSES = {403, 410, 429}                           # treated as source throttling
RATE_LIMIT_RETRIES  = int(os.environ.get("RATE_LIMIT_RETRIES", "3"))    # waits per file before giving up
RATE_LIMIT_BASE     = int(os.environ.get("RATE_LIMIT_BASE", "300"))     # first wait: 5 min (doubles)
GLOBAL_PAUSE_AFTER  = int(os.environ.get("GLOBAL_PAUSE_AFTER", "3"))    # N files throttled within window…
GLOBAL_PAUSE_WINDOW = int(os.environ.get("GLOBAL_PAUSE_WINDOW", "120")) # …seconds → pause whole batch
GLOBAL_PAUSE_BASE   = int(os.environ.get("GLOBAL_PAUSE_BASE", "600"))   # first global pause: 10 min
GLOBAL_PAUSE_MAX    = int(os.environ.get("GLOBAL_PAUSE_MAX", "3600"))   # max pause: 1 h

# ---- upload memory ----------------------------------------------------
SKIP_UPLOADED  = os.environ.get("SKIP_UPLOADED", "1") == "1"
HISTORY_FILE   = Path(os.environ.get("HISTORY_FILE", "uploaded_history.json"))

CHUNK_SIZE     = 1024 * 1024
MAX_RETRIES    = 3                                              # network attempts per file / segment
RETRY_BACKOFF  = 5
MAX_UPLOAD     = 2000 * 1024 * 1024                             # Telegram bot upload limit (~2 GB)
STATUS_EVERY   = 2.5

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")

VIDEO_EXTS = {".mp4", ".mkv", ".webm", ".mov", ".avi", ".ts", ".m4v",
              ".flv", ".wmv", ".3gp", ".mpg", ".mpeg", ".m2ts", ".ogv"}

logging.basicConfig(level=logging.INFO, format="%(asctime)s  %(message)s", datefmt="%H:%M:%S")
log = logging.getLogger("url-uploader")

current_batch = None  # the Tracker of the batch currently running (or None)


# ----------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------
class JobError(Exception):
    pass


class BatchCancelled(Exception):
    pass


class SegmentFallback(Exception):
    """Server does not really support Range requests."""


class SourceLimited(Exception):
    """Source returned 403/410/429 — throttling / expired link."""
    def __init__(self, status, retry_after=None):
        super().__init__(f"HTTP {status}")
        self.status = status
        self.retry_after = retry_after


def fmt_bytes(n: float) -> str:
    if n is None:
        return "?"
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{n:.1f} {unit}" if unit != "B" else f"{int(n)} B"
        n /= 1024


def fmt_eta(seconds) -> str:
    if seconds is None or seconds < 0 or seconds != seconds:
        return "--:--"
    seconds = int(seconds)
    h, r = divmod(seconds, 3600)
    m, s = divmod(r, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


def bar(frac: float, width: int = 10) -> str:
    frac = 0.0 if frac is None else max(0.0, min(1.0, frac))
    n = int(round(frac * width))
    return "▓" * n + "░" * (width - n)


def sanitize_filename(name: str) -> str:
    name = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "_", name)
    name = name.strip(" .")
    return name[:180] or "video"


def decode_txt(raw: bytes) -> str:
    if raw.startswith((b"\xff\xfe", b"\xfe\xff")):
        return raw.decode("utf-16", errors="replace")
    if b"\x00" in raw[:200]:                      # UTF-16 saved WITHOUT BOM (Notepad)
        for enc in ("utf-16-le", "utf-16-be"):
            try:
                t = raw.decode(enc)
                if "http" in t.lower():
                    return t
            except UnicodeDecodeError:
                continue
    try:
        return raw.decode("utf-8-sig")
    except UnicodeDecodeError:
        return raw.decode("cp1252", errors="replace")


def looks_like_link_list(text: str) -> bool:
    return "http://" in text.lower() or "https://" in text.lower()


# ----------------------------------------------------------------------
# 🧹 Storage management
# ----------------------------------------------------------------------
TEMP_PREFIXES = ("tgupload_", "tglist_")


def sweep_temp_dirs(skip=None) -> int:
    removed = 0
    skip_abs = os.path.abspath(skip) if skip else None
    for root in {tempfile.gettempdir(), os.getcwd()}:
        for prefix in TEMP_PREFIXES:
            for p in glob.glob(os.path.join(root, prefix + "*")):
                if skip_abs and os.path.abspath(p) == skip_abs:
                    continue
                try:
                    if os.path.isdir(p):
                        shutil.rmtree(p, ignore_errors=True)
                    else:
                        os.remove(p)
                    removed += 1
                except OSError:
                    pass
    return removed


def disk_info(path: str = ".") -> str:
    try:
        st = shutil.disk_usage(path)
        pct = (st.free / st.total * 100) if st.total else 0
        return f"{fmt_bytes(st.used)} used / {fmt_bytes(st.total)} ({pct:.0f}% free)"
    except OSError:
        return "usage unknown"


def free_bytes(path: str = ".") -> int:
    try:
        return shutil.disk_usage(path).free
    except OSError:
        return 1 << 60


def disk_used_pct() -> float:
    try:
        du = shutil.disk_usage(".")
        return (du.total - du.free) * 100.0 / du.total if du.total else 0.0
    except OSError:
        return 0.0


def projected_free(tracker, job=None) -> int:
    """Free space that will remain AFTER the downloads already in flight
    have written everything they still owe. Used for the pre-download
    check: a new file may start only when its FULL size fits here."""
    free = free_bytes()
    admitted = getattr(tracker, "admitted", None)
    if admitted:
        free -= sum(max(0, (j.total or 0) - j.done) for j in admitted.values()
                    if j is not job and j.status == "downloading")
    return max(0, free)


def storage_paused(tracker=None, job=None, need=None) -> bool:
    """💾 need=None → basic limit: less than MIN_FREE_BYTES free or
    MAX_DISK_USE_PCT% used (≈7.5 GB used on an 8 GB server).
    need=N     → pre-download check: N bytes (the file's FULL size +
    headroom) must fit in the PROJECTED free space.
    Downloads pause then; uploads NEVER stop — every finished upload
    deletes its file, the space frees up and this flips back to False."""
    if need is not None:
        return projected_free(tracker, job) < need
    return free_bytes() < MIN_FREE_BYTES or disk_used_pct() >= MAX_DISK_USE_PCT


def _all_downloads_stalled(tracker, job) -> bool:
    """True when nothing can free space by itself: no upload is running and
    every other download is paused too."""
    jobs = getattr(tracker, "jobs", [])
    if any(j.status == "uploading" for j in jobs):
        return False
    others = [j for j in jobs if j.status == "downloading" and j is not job]
    return all(j.note.startswith(("⏸", "💾")) for j in others)


async def wait_for_storage(tracker, job=None, need=None):
    """💾 Storage guard: pause downloads until there is room.

    need=None → wait for basic headroom (MIN_FREE_BYTES / MAX_DISK_USE_PCT).
    need=N    → 🚦 pre-download check: wait until N bytes fit AFTER the
                downloads already in flight finish (projected free space).
                A file only ENTERS download when its full size fits.

    Uploads never pause; every finished upload deletes its file right away,
    so these waits end automatically and NO file is skipped for full disk.

    Deadlock breaker: if ALL downloads are stalled and no upload is running,
    ONE download may continue — but never below HARD_FLOOR_BYTES of real
    free space, so the disk can never actually be filled."""
    escape = False
    if job is not None:
        if getattr(tracker, "escape_job", None) is job:
            escape = True                          # slot already granted to me
        elif (getattr(tracker, "escape_job", None) is None
                and _all_downloads_stalled(tracker, job)):
            escape = True
            tracker.escape_job = job
            log.info("💾 Disk at limit and everything is stalled — letting %s "
                     "finish so its upload can free space", job.name)
    warned = False
    while True:
        if not storage_paused(tracker, job, need):
            break
        if tracker.cancelled:
            raise BatchCancelled
        if escape and free_bytes() > HARD_FLOOR_BYTES:
            if job is not None:
                job.note = "💾 disk full — finishing to free space"
            return                                 # continue downloading
        if not warned:
            if need is not None:
                log.info("🚦 %s: needs %s but only %s will be available — "
                         "waiting for uploads to free space",
                         job.name if job else "file", fmt_bytes(need),
                         fmt_bytes(projected_free(tracker, job)))
            else:
                log.info("💾 Disk at limit (%.0f%% used, %s free) — downloads "
                         "paused; uploads keep running and will free space",
                         disk_used_pct(), fmt_bytes(free_bytes()))
            warned = True
        if job is not None:
            if need is not None:
                job.note = (f"🚦 waiting for space: needs {fmt_bytes(need)}, "
                            f"{fmt_bytes(projected_free(tracker, job))} available")
            else:
                job.note = f"⏸ disk full — paused ({fmt_bytes(free_bytes())} free)"
        await asyncio.sleep(3)
    if job is not None:
        job.note = ""


# ----------------------------------------------------------------------
# 🧠 Upload memory (skip already-uploaded files)
# ----------------------------------------------------------------------
HISTORY = {}


def load_history():
    global HISTORY
    try:
        HISTORY = json.loads(HISTORY_FILE.read_text()) if HISTORY_FILE.exists() else {}
    except Exception:
        HISTORY = {}
    return len(HISTORY)


def save_history():
    try:
        HISTORY_FILE.write_text(json.dumps(HISTORY))
    except OSError as e:
        log.warning("could not save history: %s", e)


def mark_uploaded(name: str):
    HISTORY[name] = int(time.time())
    save_history()


# ----------------------------------------------------------------------
# ⏸ Source rate-limit brain  (the "410 Gone" fix)
# ----------------------------------------------------------------------
class RateLimitState:
    def __init__(self):
        self.global_until = 0.0     # monotonic time until which downloads pause
        self.global_count = 0       # escalation level of the global pause
        self.recent = deque()       # timestamps of recent per-file throttles


rl = RateLimitState()


def rate_limit_hint(status: int) -> str:
    if status == 410:
        return ("HTTP 410 Gone — the link expired or the source blocked this "
                "server's IP. Send a FRESH video.txt — already-uploaded files "
                "are skipped automatically.")
    if status == 429:
        return f"HTTP 429 — source rate limit persisted after {RATE_LIMIT_RETRIES} waits."
    return f"HTTP {status} — source refused the download after {RATE_LIMIT_RETRIES} waits."


def parse_retry_after(headers) -> int:
    try:
        return max(0, int(headers.get("Retry-After", "0")))
    except (TypeError, ValueError):
        return 0


def note_rate_limit(status: int, retry_after: int = 0):
    """Register a throttle event; escalate to a global batch pause when
    several files are throttled inside a short window (= IP-level ban)."""
    now = time.monotonic()
    rl.recent.append(now)
    while rl.recent and now - rl.recent[0] > GLOBAL_PAUSE_WINDOW:
        rl.recent.popleft()
    if len(rl.recent) >= GLOBAL_PAUSE_AFTER:
        rl.global_count += 1
        dur = min(GLOBAL_PAUSE_BASE * (2 ** (rl.global_count - 1)), GLOBAL_PAUSE_MAX)
        dur = max(dur, retry_after)
        rl.global_until = max(rl.global_until, now + dur)
        rl.recent.clear()
        log.info("⏸ Source is throttling many files — pausing ALL downloads for %s",
                 fmt_eta(dur))


async def wait_global(tracker):
    while time.monotonic() < rl.global_until:
        if tracker.cancelled:
            raise BatchCancelled
        await asyncio.sleep(3)


async def wait_out(status: int, retry_after: int, attempt: int, tracker, job):
    """Per-file escalating wait after a 403/410/429."""
    note_rate_limit(status, retry_after)
    await wait_global(tracker)
    d = min(max(RATE_LIMIT_BASE * (2 ** (attempt - 1)), retry_after), GLOBAL_PAUSE_MAX)
    job.note = f"⏸ HTTP {status} — retry in {fmt_eta(d)}"
    log.info("⏸ %s: HTTP %d — waiting %s before retry %d/%d",
             job.name, status, fmt_eta(d), attempt, RATE_LIMIT_RETRIES)
    end = time.monotonic() + d
    while time.monotonic() < end:
        if tracker.cancelled:
            raise BatchCancelled
        await asyncio.sleep(min(5, max(0.1, end - time.monotonic())))
    job.note = ""


# ----------------------------------------------------------------------
# 🐢 Optional global download speed cap
# ----------------------------------------------------------------------
class GlobalThrottle:
    def __init__(self, mbps: float):
        self.limit = int(mbps * 1024 * 1024) if mbps else 0
        self.window = deque()

    async def consume(self, n: int):
        if not self.limit:
            return
        now = time.monotonic()
        while self.window and now - self.window[0][0] >= 1.0:
            self.window.popleft()
        total = sum(b for _, b in self.window)
        if total + n > self.limit:
            await asyncio.sleep(min(5.0, (total + n - self.limit) / self.limit))
        self.window.append((time.monotonic(), n))


THROTTLE = GlobalThrottle(DL_SPEED_LIMIT_MBPS)


# ----------------------------------------------------------------------
# Parsing the txt  (line format:  name,URL   — split on FIRST comma only)
# ----------------------------------------------------------------------
@dataclass
class Job:
    index: int
    name: str
    caption: str
    url: str
    path: Path
    status: str = "queued"     # queued|downloading|uploading|done|failed|cancelled|skipped
    phase: str = "download"
    done: int = 0
    total: int = 0
    error: str = ""
    note: str = ""             # e.g. rate-limit countdown, shown in status
    downloaded: int = 0
    requeues: int = 0            # 🔁 how often this file was re-queued after a failure
    speed: float = None
    bar: object = None
    samples: deque = field(default_factory=deque)


URL_START = re.compile(r"https?://", re.I)
FILE_NAMEY = re.compile(r"[\w\-.%]+\.\w{2,4}")


def _clean(s: str) -> str:
    return (s.replace("\u00a0", " ").replace("\u200b", "").replace("\ufeff", "")
            .strip().strip("\"'<>").strip())


def split_name_url(line: str):
    """Parse one line of ANY real-world link list → (name, url).
    url == '' when no URL can be found. Accepts:
        name,URL   •   URL,name   •   name<TAB>URL   •   name URL
        name | URL •   name ; URL •   bare URL       •   "name","URL"
        1. name, URL (numbered)  — URLs may contain commas."""
    line = _clean(line)
    if not line:
        return "", ""
    # A) name,URL — split on FIRST comma (the URL keeps its own commas)
    head, sep, tail = line.partition(",")
    if sep and _clean(tail).lower().startswith(("http://", "https://")):
        return _clean(head), _clean(tail)
    # B) line STARTS with the URL → "URL,name" or bare URL or "URL name"
    if line.lower().startswith(("http://", "https://")):
        if "," in line:
            pos = line.rfind(",")
            maybe_name, maybe_url = _clean(line[pos + 1:]), _clean(line[:pos])
            if (maybe_name and "/" not in maybe_name and "://" not in maybe_name
                    and len(maybe_name) <= 120
                    and not FILE_NAMEY.fullmatch(maybe_name)):
                return maybe_name, maybe_url          # URL,name
        parts = line.split(None, 1)                   # URLs never contain spaces
        if len(parts) == 2:
            return _clean(parts[1]), parts[0]         # URL name
        return "", line                               # bare URL (commas kept)
    # C) URL anywhere else on the line (tab / space / | / ; / : separated)
    m = URL_START.search(line)
    if m:
        name = _clean(line[:m.start()])
        name = re.sub(r"[\s|;:=\-–—]+$", "", name).strip()
        return name, _clean(line[m.start():])
    return "", ""


def parse_jobs(text: str, batch_dir: Path):
    jobs = []
    used = {}
    text = text.lstrip("\ufeff")
    for raw in text.splitlines():
        line = _clean(raw)
        if not line or line.startswith("#"):
            continue

        name, url = split_name_url(line)
        if not url:
            jobs.append(Job(len(jobs), sanitize_filename(name or line)[:60], name or line,
                            "", batch_dir / "invalid", status="failed",
                            error="Invalid line (no URL found)"))
            continue

        if not name:
            base = os.path.basename(urlsplit(url).path) or "video"
            name = os.path.splitext(base)[0]
        # strip leading numbering like "12." / "12)" / "3 -"
        name = re.sub(r"^\s*\d+\s*[\).\-\u2013]\s*", "", name).strip() or "video"
        name = sanitize_filename(name)

        stem, ext = os.path.splitext(name)
        if ext.lower() not in VIDEO_EXTS:
            url_ext = os.path.splitext(urlsplit(url).path)[1].lower()
            if re.fullmatch(r"\.[a-z0-9]{1,5}", url_ext or ""):
                name = stem + url_ext
            else:
                name = name + ".mp4"

        stem, ext = os.path.splitext(name)
        base_stem, k = stem, 2
        while stem.lower() in used:
            stem = f"{base_stem} ({k})"
            k += 1
        used[stem.lower()] = True
        name = stem + ext

        jobs.append(Job(len(jobs), name, os.path.splitext(name)[0], url, batch_dir / name))
    return jobs


# ----------------------------------------------------------------------
# ⚡ HIGH-SPEED download pipeline (rate-limit aware)
# ----------------------------------------------------------------------
async def probe_file(session, job):
    """1-byte Range GET → returns (size, range_supported)."""
    try:
        async with session.get(job.url,
                               headers={"User-Agent": UA, "Range": "bytes=0-0"}) as resp:
            if resp.status in RATE_LIMIT_STATUSES:
                raise SourceLimited(resp.status, parse_retry_after(resp.headers))
            if resp.status == 206:
                cr = resp.headers.get("Content-Range", "")
                size = 0
                if "/" in cr:
                    tail = cr.split("/")[-1].strip()
                    size = int(tail) if tail.isdigit() else 0
                await resp.content.read(8)
                return size, True
            if resp.status == 200:
                return int(resp.headers.get("Content-Length") or 0), False
            raise JobError(f"HTTP {resp.status} {resp.reason}")
    except (JobError, SourceLimited):
        raise
    except Exception as e:
        raise JobError(f"Server unreachable: {type(e).__name__}: {e}")


async def _download_segment(session, job, tracker, start, end):
    net_attempt = 0
    rl_attempt = 0
    while True:
        if tracker.cancelled:
            raise BatchCancelled
        try:
            await wait_global(tracker)
            headers = {"User-Agent": UA, "Range": f"bytes={start}-{end}"}
            async with session.get(job.url, headers=headers) as resp:
                if resp.status in RATE_LIMIT_STATUSES:
                    raise SourceLimited(resp.status, parse_retry_after(resp.headers))
                if resp.status != 206:
                    raise SegmentFallback(f"server answered {resp.status} to Range request")
                ce = (resp.headers.get("Content-Encoding") or "identity").lower()
                if ce != "identity":
                    raise SegmentFallback(f"compressed response ({ce})")
                since_check = 0
                with job.path.open("r+b") as f:
                    f.seek(start)
                    async for chunk in resp.content.iter_chunked(CHUNK_SIZE):
                        if tracker.cancelled:
                            raise BatchCancelled
                        await THROTTLE.consume(len(chunk))
                        f.write(chunk)
                        job.done += len(chunk)
                        since_check += len(chunk)
                        if since_check >= STORAGE_CHECK_EVERY:
                            since_check = 0
                            if storage_paused():        # 💾 disk at limit → pause too
                                await wait_for_storage(tracker, job)
                        if job.bar:
                            job.bar.update(len(chunk))
                return
        except SourceLimited as sl:
            rl_attempt += 1
            if rl_attempt > RATE_LIMIT_RETRIES:
                raise JobError(rate_limit_hint(sl.status))
            await wait_out(sl.status, sl.retry_after, rl_attempt, tracker, job)
        except (SegmentFallback, BatchCancelled):
            raise
        except asyncio.CancelledError:
            raise
        except Exception as e:
            net_attempt += 1
            if net_attempt > MAX_RETRIES:
                raise JobError(f"Segment failed after {MAX_RETRIES} attempts: "
                               f"{type(e).__name__}: {e}")
            await asyncio.sleep(RETRY_BACKOFF * net_attempt)


async def _download_single(job, session, tracker):
    net_attempt = 0
    rl_attempt = 0
    while True:
        if tracker.cancelled:
            raise BatchCancelled
        resume = job.path.stat().st_size if job.path.exists() else 0
        headers = {"User-Agent": UA}
        if resume > 0:
            headers["Range"] = f"bytes={resume}-"
        try:
            await wait_global(tracker)
            async with session.get(job.url, headers=headers) as resp:
                if resp.status in RATE_LIMIT_STATUSES:
                    raise SourceLimited(resp.status, parse_retry_after(resp.headers))
                if resp.status == 416:
                    job.done = job.total = resume
                    return
                if resp.status == 206:
                    mode = "ab"
                    cr = resp.headers.get("Content-Range", "")
                    if "/" in cr and cr.split("/")[-1].strip().isdigit():
                        job.total = int(cr.split("/")[-1])
                elif resp.status == 200:
                    mode, resume = "wb", 0
                    job.total = int(resp.headers.get("Content-Length") or 0)
                else:
                    raise JobError(f"HTTP {resp.status} {resp.reason}")

                if not job.total:
                    job.total = int(resp.headers.get("Content-Length") or 0)
                if job.bar:
                    job.bar.reset(resume)
                    job.bar.total = job.total or None
                    job.bar.refresh()

                got = resume
                job.done = got
                since_check = 0
                with job.path.open(mode) as f:
                    async for chunk in resp.content.iter_chunked(CHUNK_SIZE):
                        if tracker.cancelled:
                            raise BatchCancelled
                        await THROTTLE.consume(len(chunk))
                        f.write(chunk)
                        got += len(chunk)
                        job.done = got
                        since_check += len(chunk)
                        if since_check >= STORAGE_CHECK_EVERY:
                            since_check = 0
                            if storage_paused():        # 💾 disk at limit → pause too
                                await wait_for_storage(tracker, job)
                        if job.bar:
                            job.bar.update(len(chunk))
                job.done = got
                return
        except SourceLimited as sl:
            rl_attempt += 1
            if rl_attempt > RATE_LIMIT_RETRIES:
                raise JobError(rate_limit_hint(sl.status))
            await wait_out(sl.status, sl.retry_after, rl_attempt, tracker, job)
        except (BatchCancelled, JobError, SegmentFallback):
            raise
        except asyncio.CancelledError:
            raise
        except Exception as e:
            net_attempt += 1
            log.warning("download error (%s) attempt %d/%d for %s: %s",
                        type(e).__name__, net_attempt, MAX_RETRIES, job.name, e)
            if net_attempt > MAX_RETRIES:
                raise JobError(f"Download failed after {MAX_RETRIES} attempts: "
                               f"{type(e).__name__}: {e}")
            await asyncio.sleep(RETRY_BACKOFF * net_attempt)


async def _download_file_once(job, session, tracker):
    size, range_ok = await probe_file(session, job)
    job.total = size

    if size:
        du = shutil.disk_usage(".")
        if size > du.total - MIN_FREE_BYTES:
            raise JobError(f"File is {fmt_bytes(size)} — larger than this server's usable "
                           f"disk ({fmt_bytes(du.total)} total). Cannot download it here.")
        # 🚦 pre-download storage check: ENTER download only when the file's
        # FULL size fits (after in-flight downloads finish). Uploads keep
        # running and deleting files, so this wait ends by itself.
        await wait_for_storage(tracker, job, size + MIN_FREE_BYTES)
        ad = getattr(tracker, "admitted", None)
        if ad is not None:
            ad[id(job)] = job

    nseg = 1
    if range_ok and size > SEG_MIN_BYTES and MAX_SEGMENTS > 1:
        nseg = max(1, min(MAX_SEGMENTS, size // SEG_MIN_PART))

    job.bar = tqdm(total=size or None, unit="B", unit_scale=True, unit_divisor=1024,
                   desc=f"⬇ {job.name[:40]}" + (f" ×{nseg}" if nseg > 1 else ""),
                   leave=False)
    try:
        if nseg > 1:
            log.info("⬇ %s: %d parallel connections (%s)", job.name, nseg, fmt_bytes(size))
            with job.path.open("wb") as f:
                f.truncate(size)
            step = math.ceil(size / nseg)
            bounds = [(i * step, min((i + 1) * step - 1, size - 1))
                      for i in range(nseg) if i * step < size]
            tasks = [asyncio.create_task(_download_segment(session, job, tracker, s, e))
                     for s, e in bounds]
            try:
                await asyncio.gather(*tasks)
            except SegmentFallback as sf:
                for t in tasks:
                    t.cancel()
                await asyncio.gather(*tasks, return_exceptions=True)
                log.info("⬇ %s: falling back to single stream (%s)", job.name, sf)
                job.done = 0
                if job.bar:
                    job.bar.reset(0)
                await _download_single(job, session, tracker)
            except BaseException:
                for t in tasks:
                    t.cancel()
                await asyncio.gather(*tasks, return_exceptions=True)
                raise
            actual = job.path.stat().st_size if job.path.exists() else 0
            if size and actual != size:
                raise JobError(f"Size mismatch after download ({actual} != {size} bytes)")
        else:
            await _download_single(job, session, tracker)
    finally:
        if job.bar:
            job.bar.close()
            job.bar = None


async def download_file(job, session, tracker):
    """⏸ Rate-limit-aware wrapper: on 403/410/429 the file waits it out
    (escalating) and the attempt is repeated — up to RATE_LIMIT_RETRIES."""
    attempt = 0
    while True:
        try:
            await wait_global(tracker)
            await _download_file_once(job, session, tracker)
            return
        except SourceLimited as sl:
            attempt += 1
            if attempt > RATE_LIMIT_RETRIES:
                raise JobError(rate_limit_hint(sl.status))
            await wait_out(sl.status, sl.retry_after, attempt, tracker, job)


# ----------------------------------------------------------------------
# ⚡ HIGH-SPEED upload pipeline
# ----------------------------------------------------------------------
def _file_md5(path: Path) -> str:
    h = hashlib.md5()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


async def parallel_upload(job, client, chat_id, tracker):
    """fasttelethon technique: UPLOAD_WORKERS concurrent 512 KB parts."""
    size = job.total or job.path.stat().st_size
    part_size = 512 * 1024
    part_count = math.ceil(size / part_size)
    big = size >= BIG_FILE_MIN
    file_id = random.randint(-2**63, 2**63 - 1)

    tb = tqdm(total=size, unit="B", unit_scale=True, unit_divisor=1024,
              desc=f"⬆ {job.name[:40]} ×{UPLOAD_WORKERS}", leave=False)
    md5_hex = None if big else await asyncio.to_thread(_file_md5, job.path)
    fd = os.open(str(job.path), os.O_RDONLY)
    sem = asyncio.Semaphore(UPLOAD_WORKERS)
    sender = client._sender

    async def send_part(i):
        async with sem:
            for attempt in range(1, MAX_RETRIES + 1):
                if tracker.cancelled:
                    raise BatchCancelled
                data = await asyncio.to_thread(os.pread, fd, part_size, i * part_size)
                if not data:
                    return
                req = (SaveBigFilePartRequest(file_id=file_id, file_part=i,
                                              file_total_parts=part_count, bytes=data)
                       if big else
                       SaveFilePartRequest(file_id=file_id, file_part=i, bytes=data))
                try:
                    await sender.send(req)
                    job.done += len(data)
                    tb.update(len(data))
                    return
                except (BatchCancelled, asyncio.CancelledError):
                    raise
                except FloodWaitError as e:
                    log.info("FloodWait %ss during part upload — sleeping it out", e.seconds)
                    await asyncio.sleep(e.seconds + 1)
                except Exception as e:
                    if attempt == MAX_RETRIES:
                        raise JobError(f"Part {i + 1}/{part_count} failed after "
                                       f"{MAX_RETRIES} attempts: {type(e).__name__}: {e}")
                    await asyncio.sleep(RETRY_BACKOFF * attempt)

    try:
        tasks = [asyncio.create_task(send_part(i)) for i in range(part_count)]
        try:
            await asyncio.gather(*tasks)
        except BaseException:
            for t in tasks:
                t.cancel()
            await asyncio.gather(*tasks, return_exceptions=True)
            raise
    finally:
        os.close(fd)
        tb.close()

    if tracker.cancelled:
        raise BatchCancelled

    input_file = (InputFileBig(id=file_id, parts=part_count, name=job.name) if big
                  else InputFile(id=file_id, parts=part_count, name=job.name,
                                 md5_checksum=md5_hex))
    log.info("⬆ %s: %d parts uploaded in parallel (%s), sending message…",
             job.name, part_count, "big" if big else "small")
    for attempt in range(1, 4):
        try:
            await client.send_file(chat_id, file=input_file,
                                   caption=job.caption[:1000],
                                   supports_streaming=True)
            return
        except FloodWaitError as e:
            await asyncio.sleep(e.seconds + 1)
        except RPCError as e:
            if attempt == 3:
                raise JobError(f"send_file failed: {e}")
            await asyncio.sleep(3)


async def upload_file(job, client, chat_id, tracker):
    if UPLOAD_WORKERS > 1 and (job.total or 0) >= PARALLEL_UPLOAD_MIN:
        return await parallel_upload(job, client, chat_id, tracker)

    tb = tqdm(total=job.total, unit="B", unit_scale=True, unit_divisor=1024,
              desc=f"⬆ {job.name[:40]}", leave=False)

    def cb(current, total):
        job.done = current
        if total:
            job.total = total
        tb.update(max(0, current - tb.n))
        if tracker.cancelled:
            raise BatchCancelled

    try:
        await client.send_file(
            chat_id,
            file=str(job.path),
            caption=job.caption[:1000],
            supports_streaming=True,
            progress_callback=cb,
            part_size_kb=512,
        )
    finally:
        tb.close()


async def process_job(job, session, chat_id, tracker) -> None:
    if job.status in ("failed", "skipped"):
        return
    try:
        async with tracker.dl_sem:
            if tracker.cancelled:
                raise BatchCancelled
            await wait_for_storage(tracker, job)   # 💾 never start on a full disk
            job.phase, job.status, job.done, job.total = "download", "downloading", 0, 0
            await download_file(job, session, tracker)

        if tracker.escape_job is job:              # 💾 escape slot has done its duty
            tracker.escape_job = None

        if tracker.cancelled:
            raise BatchCancelled
        size = job.path.stat().st_size if job.path.exists() else 0
        job.downloaded = size
        if size == 0:
            raise JobError("Downloaded file is empty (0 bytes)")
        if size > MAX_UPLOAD:
            raise JobError(f"File is {fmt_bytes(size)} — bigger than the "
                           f"2000 MB bot upload limit")

        async with tracker.up_sem:
            if tracker.cancelled:
                raise BatchCancelled
            up_client = tracker.upload_clients[job.index % len(tracker.upload_clients)]
            job.phase, job.status, job.done, job.total = "upload", "uploading", 0, size
            # 🔁 a failed upload is NOT final — retry it (rotating sessions)
            attempt, last_err = 0, None
            while True:
                try:
                    await upload_file(job, up_client, chat_id, tracker)
                    break
                except (BatchCancelled, asyncio.CancelledError):
                    raise
                except Exception as e:
                    last_err = e
                    attempt += 1
                    if attempt > UPLOAD_RETRIES:
                        raise JobError(f"Upload failed after {UPLOAD_RETRIES + 1} "
                                       f"attempts: {type(e).__name__}: {e}") from e
                    secs = min(UPLOAD_RETRY_BASE * attempt, 300)
                    fw = getattr(e, "seconds", 0)          # FloodWaitError
                    if fw:
                        secs = max(secs, min(int(fw) + 5, 600))
                    log.warning("🔁 %s: upload failed (%s: %s) — retry %d/%d in %ss",
                                job.name, type(e).__name__, e, attempt,
                                UPLOAD_RETRIES, int(secs))
                    job.note = f"🔁 upload retry {attempt}/{UPLOAD_RETRIES} in {int(secs)}s"
                    await asyncio.sleep(secs)
                    job.note = ""
                    job.done = 0
                    up_client = tracker.upload_clients[
                        (job.index + attempt) % len(tracker.upload_clients)]

        job.status = "done"
        if SKIP_UPLOADED:
            mark_uploaded(job.name)          # 🧠 remember for future batches
        log.info("✔ %s uploaded", job.name)
    except BatchCancelled:
        job.status = "cancelled"
    except asyncio.CancelledError:
        job.status = "cancelled"
        raise
    except Exception as e:
        job.status = "failed"
        job.error = str(e)[:300]
        log.error("✖ %s failed: %s", job.name, e)
    finally:
        if getattr(tracker, "escape_job", None) is job:
            tracker.escape_job = None
        ad = getattr(tracker, "admitted", None)
        if ad is not None:
            ad.pop(id(job), None)
        job.note = ""
        try:
            job.path.unlink(missing_ok=True)   # 🗑 delete the INSTANT upload ends
        except OSError:
            pass


# ----------------------------------------------------------------------
# Live progress message
# ----------------------------------------------------------------------
def speed_of(samples: deque, now_done: float):
    samples.append((time.monotonic(), now_done))
    while samples and now_done - samples[0][1] > 0 and time.monotonic() - samples[0][0] > 15:
        samples.popleft()
    if len(samples) < 2:
        return None
    t0, b0 = samples[0]
    dt = time.monotonic() - t0
    if dt <= 0.1:
        return None
    return (now_done - b0) / dt


def render_status(tracker) -> str:
    jobs = tracker.jobs
    n_done = sum(j.status == "done" for j in jobs)
    n_fail = sum(j.status == "failed" for j in jobs)
    n_canc = sum(j.status == "cancelled" for j in jobs)
    n_skip = sum(j.status == "skipped" for j in jobs)
    n_dl   = sum(j.status == "downloading" for j in jobs)
    n_up   = sum(j.status == "uploading" for j in jobs)
    n_wait = sum(j.status == "queued" for j in jobs)

    total = sum(j.total for j in jobs if j.total > 0)
    done = sum(j.done for j in jobs if j.status in ("downloading", "uploading", "done"))
    frac = done / total if total else None
    speed = tracker.overall_speed
    eta = ((total - done) / speed) if (speed and total and frac is not None and frac < 1) else None

    stats = f"📊 {fmt_bytes(done)} / {fmt_bytes(total) if total else '?'}"
    if frac is not None:
        stats += f"  ({frac*100:.1f}%)"
    if speed:
        stats += f"  •  {fmt_bytes(speed)}/s"
    if eta:
        stats += f"  •  ETA {fmt_eta(eta)}"

    head = [
        f"📦 Batch: {tracker.label} — {len(jobs)} file(s)   "
        f"⚙ {MAX_DOWNLOADS}⬇/{MAX_UPLOADS}⬆ ×{MAX_SEGMENTS}dl ×{UPLOAD_WORKERS}up "
        f"{len(tracker.upload_clients)}tx",
        stats,
        f"✅ {n_done}   ⬇ {n_dl}   ⬆ {n_up}   ⏳ {n_wait}   ⏭ {n_skip}   ❌ {n_fail}"
        + (f"   ⛔ {n_canc}" if n_canc else "")
        + f"   ⏱ {fmt_eta(time.monotonic() - tracker.t0)}"
        + f"   💾 {fmt_bytes(free_bytes())} free ({disk_used_pct():.0f}% used)"
        + ("   ⏸ DL PAUSED" if storage_paused() else ""),
    ]

    paused_for = rl.global_until - time.monotonic()
    if paused_for > 0:
        head.append(f"⏸ Source cooldown — downloads resume in {fmt_eta(paused_for)}")

    lines = []
    active = [j for j in jobs if j.status in ("downloading", "uploading")]
    for j in sorted(active, key=lambda x: x.index)[:8]:
        f = j.done / j.total if j.total else None
        icon = "⬇" if j.phase == "download" else "⬆"
        pct = f" {f*100:5.1f}%" if f is not None else "     ?"
        label = j.name[:30] + (f"  {j.note}" if j.note else "")
        lines.append(f"{icon} {bar(f)}{pct} {fmt_bytes(j.done)}/{fmt_bytes(j.total) if j.total else '?'}"
                     f"  {fmt_bytes(j.speed)}/s  {label}")
    if len(active) > 8:
        lines.append(f"… and {len(active) - 8} more active file(s)")
    return "\n".join(head + lines)


async def progress_updater(client, tracker) -> None:
    last_text = None
    while not tracker.finished:
        await asyncio.sleep(STATUS_EVERY)
        done_now = sum(j.done for j in tracker.jobs
                       if j.status in ("downloading", "uploading", "done"))
        tracker.overall_speed = speed_of(tracker.samples, done_now)
        for j in tracker.jobs:
            j.speed = speed_of(j.samples, j.done) if j.status in ("downloading", "uploading") else None
        text = render_status(tracker)
        if text != last_text:
            try:
                await tracker.message.edit(text)
                last_text = text
            except MessageNotModifiedError:
                pass
            except FloodWaitError as e:
                await asyncio.sleep(e.seconds)
            except RPCError as e:
                log.warning("status edit failed: %s", e)


# ----------------------------------------------------------------------
# Batch runner
# ----------------------------------------------------------------------
class Tracker:
    def __init__(self, label, message, upload_clients):
        self.jobs = []                      # grows when links are added mid-run
        self.label = label
        self.message = message
        self.upload_clients = upload_clients
        self.dl_sem = asyncio.Semaphore(MAX_DOWNLOADS)
        self.up_sem = asyncio.Semaphore(MAX_UPLOADS)
        self.batch_dir = None
        self.session = None
        self.cancelled = False
        self.finished = False
        self.t0 = time.monotonic()
        self.samples = deque()
        self.overall_speed = None
        self.outstanding = 0                # jobs started but not finished
        self.tasks = set()
        self.pending = deque()              # 🌊 queued jobs waiting for their wave
        self.admitted = {}                  # 🚦 id(job)→job: downloads that passed the full-fit check
        self.escape_job = None              # 💾 the one download allowed to finish on a full disk

    def enqueue(self, jobs):
        """Register jobs with this batch — they wait in `pending` until
        their wave starts (works for the initial list AND mid-run additions)."""
        for j in jobs:
            j.path = self.batch_dir / j.name
            self.jobs.append(j)
            self.pending.append(j)

    def start_jobs(self, jobs, session, chat_id):
        """Actually start one wave's worth of jobs."""
        for j in jobs:
            self.outstanding += 1
            t = asyncio.create_task(self._run_job(j, session, chat_id))
            self.tasks.add(t)
            t.add_done_callback(self.tasks.discard)

    async def _run_job(self, job, session, chat_id):
        try:
            await process_job(job, session, chat_id, self)
        finally:
            self.outstanding -= 1


def apply_skip_memory(jobs) -> int:
    """Mark jobs already uploaded in earlier batches as skipped."""
    n = 0
    if SKIP_UPLOADED:
        for j in jobs:
            if j.status != "failed" and j.name in HISTORY:
                j.status = "skipped"
                n += 1
    return n


async def add_to_running_batch(event, jobs, source_label) -> bool:
    """➕ Add newly entered links to the RUNNING batch's queue (one batch,
    never a second batch, never a rejection)."""
    b = current_batch
    if not b or b.finished or b.cancelled:
        return False
    n_skipped = apply_skip_memory(jobs)
    n_add = sum(1 for j in jobs if j.status == "queued")
    b.enqueue(jobs)
    log.info("➕ Added %d file(s) from %s to running batch (queue total: %d)",
             n_add, source_label, len(b.jobs))
    await event.respond(
        f"➕ Added {n_add} file(s) from {source_label} to the RUNNING batch"
        + (f" • ⏭ {n_skipped} already uploaded" if n_skipped else "")
        + f"\nQueue total: {len(b.jobs)} file(s) • in progress now: "
          f"{sum(1 for j in b.jobs if j.status in ('downloading', 'uploading'))}")
    return True


async def wave_feeder(tracker, chat_id):
    """🌊 Feed the queue in waves of WAVE_SIZE: fully download AND upload
    each wave (files are deleted as their uploads finish) before the next
    WAVE_SIZE files start. WAVE_SIZE=0 falls back to a continuous pipeline."""
    while True:
        if tracker.cancelled:
            for j in tracker.pending:
                j.status = "cancelled"
            tracker.pending.clear()
            return
        if not tracker.pending:
            if tracker.outstanding == 0:
                return                          # queue fully drained
            await asyncio.sleep(0.5)
            continue
        n = len(tracker.pending) if WAVE_SIZE <= 0 else min(WAVE_SIZE,
                                                            len(tracker.pending))
        wave = [tracker.pending.popleft() for _ in range(n)]
        log.info("🌊 Wave: starting %d file(s) • %d still queued",
                 len(wave), len(tracker.pending))
        tracker.start_jobs(wave, tracker.session, chat_id)
        await asyncio.gather(*list(tracker.tasks), return_exceptions=True)

        # 🔁 failed files immediately re-join the queue and run in the NEXT
        # wave together with the fresh serial links — waves never exceed
        # WAVE_SIZE. Invalid lines are not retried; every file gets at most
        # FAILED_REQUEUE extra attempts so dead links cannot loop forever.
        retry = []
        for j in wave:
            if j.status == "failed" and j.url and j.requeues < FAILED_REQUEUE:
                j.requeues += 1
                j.status = "queued"
                j.error = ""
                j.done = j.total = j.downloaded = 0
                retry.append(j)
        if retry:
            log.info("🔁 %d failed file(s) re-queued for the next wave "
                     "(attempt %d of max %d extra)",
                     len(retry), retry[0].requeues, FAILED_REQUEUE)
            tracker.pending.extendleft(reversed(retry))


async def run_batch(client, chat_id, jobs, label, upload_clients=None) -> None:
    global current_batch
    if not jobs:
        await client.send_message(chat_id, "❌ No valid lines found in the file.")
        return

    n_skipped = apply_skip_memory(jobs)
    upload_clients = upload_clients or [client]
    n_queued = sum(1 for j in jobs if j.status == "queued")
    wave_txt = f" — wave of {WAVE_SIZE} at a time" if WAVE_SIZE > 0 else ""
    status = await client.send_message(
        chat_id, f"📦 Queued {n_queued} file(s) from {label} — processed in order{wave_txt}"
                 + (f" • ⏭ {n_skipped} already uploaded (skipped)" if n_skipped else "")
                 + f"\n⚙ per wave: {MAX_DOWNLOADS} parallel downloads (×{MAX_SEGMENTS} "
                   f"connections each) • {MAX_UPLOADS} parallel uploads over "
                   f"{len(upload_clients)} sessions • {UPLOAD_WORKERS} parts per file "
                   f"• failed uploads retried {UPLOAD_RETRIES}×"
                 + (f"\n🌊 next {WAVE_SIZE} files start when the current wave finishes"
                    f" • failed files re-join the next wave (up to {FAILED_REQUEUE}×)"
                    if WAVE_SIZE > 0 else "")
                 + f"\n💾 Storage guard ON: every file checks the disk BEFORE entering "
                   f"download — it starts only when its FULL size fits (keeping "
                   f"{fmt_bytes(MIN_FREE_BYTES)} free). Uploads NEVER stop, each file is "
                   f"deleted the INSTANT its upload finishes, and the freed space lets "
                   f"the next file start"
                 + "\n➕ Send more links or another txt ANYTIME — they join this SAME queue.")
    tracker = Tracker(label, status, upload_clients)
    current_batch = tracker
    rl.global_until = 0.0
    rl.global_count = 0
    rl.recent.clear()

    tracker.batch_dir = Path(tempfile.mkdtemp(prefix="tgupload_"))
    timeout = aiohttp.ClientTimeout(total=None, connect=30, sock_read=120)
    tracker.session = aiohttp.ClientSession(timeout=timeout,
                                            connector=aiohttp.TCPConnector(limit=0))
    updater = None
    feeder = None
    try:
        updater = asyncio.create_task(progress_updater(client, tracker))
        tracker.enqueue(jobs)
        feeder = asyncio.create_task(wave_feeder(tracker, chat_id))
        # monitor: the batch stays alive until the whole queue — including
        # links added later — is completely processed, wave by wave
        while (tracker.outstanding > 0 or tracker.tasks or tracker.pending
               or not feeder.done()):
            await asyncio.sleep(0.5)
    finally:
        tracker.finished = True
        if current_batch is tracker:
            current_batch = None
        for tsk in (updater, feeder):
            if tsk:
                tsk.cancel()
                try:
                    await tsk
                except (asyncio.CancelledError, Exception):
                    pass
        await tracker.session.close()
        shutil.rmtree(tracker.batch_dir, ignore_errors=True)

    # ---- final summary (covers every job ever added to this batch) -------
    all_jobs = tracker.jobs
    n_done = [j for j in all_jobs if j.status == "done"]
    n_fail = [j for j in all_jobs if j.status == "failed"]
    n_canc = [j for j in all_jobs if j.status == "cancelled"]
    n_skip = [j for j in all_jobs if j.status == "skipped"]
    summary = (f"{'✅' if not n_fail and not n_canc else '⚠️'} Batch finished: {label}\n"
               f"✅ {len(n_done)} uploaded • ⏭ {len(n_skip)} skipped (already uploaded) • "
               f"❌ {len(n_fail)} failed • ⛔ {len(n_canc)} cancelled\n"
               f"⏱ Total time: {fmt_eta(time.monotonic() - tracker.t0)}")

    # ---- 🧹 storage management report ----------------------------------
    freed = sum(j.downloaded for j in all_jobs)
    n_files = sum(1 for j in all_jobs if j.downloaded)
    n_swept = sweep_temp_dirs()
    summary += (f"\n🧹 Server cleaned: {n_files} downloaded file(s) deleted "
                f"(~{fmt_bytes(freed)})"
                + (f" + {n_swept} leftover temp item(s) swept" if n_swept else "")
                + f"\n💾 Disk now: {disk_info()}")
    log.info("🧹 Cleanup: freed ~%s (%d files), swept %d leftover(s) • disk: %s",
             fmt_bytes(freed), n_files, n_swept, disk_info())

    if n_fail:
        summary += "\n\nFailures:"
        for j in n_fail[:20]:
            summary += f"\n❌ {j.name[:60]} — {j.error[:160]}"
        if any("410" in j.error for j in n_fail):
            summary += ("\n\n💡 410 Gone = expired/blocked links. Re-send a fresh "
                        "video.txt — finished files are skipped automatically. "
                        "Or set DL_SPEED_LIMIT_MBPS to slow down and stay under "
                        "the source's quota.")
    try:
        await tracker.message.edit(render_status(tracker) + "\n\n✔ Finished")
    except (RPCError, MessageNotModifiedError, FloodWaitError):
        pass
    await client.send_message(chat_id, summary)


# ----------------------------------------------------------------------
# Telegram event handlers
# ----------------------------------------------------------------------
HELP_TEXT = (
    "👋 Remote URL → Telegram video uploader (v9.1 — waves, retries, storage guard)\n\n"
    "📄 Send me a .txt file — one entry per line. All of these work:\n"
    "     name,https://example.com/video.mp4\n"
    "     https://example.com/video.mp4,name\n"
    "     name<TAB>https://…  •  bare URL  •  numbered lines\n"
    "     (UTF-8 / UTF-16 / ANSI encodings all work, commas in URLs are fine)\n\n"
    f"🌊 Files are processed in order, {WAVE_SIZE} at a time: each wave "
    f"downloads → uploads → deletes its files, then the next wave starts.\n"
    f"🔁 A failed upload is retried automatically {UPLOAD_RETRIES}× — and a "
    f"file that still fails re-joins the NEXT wave together with the fresh "
    f"links (up to {FAILED_REQUEUE} extra attempts), so failures never stop "
    f"the serial.\n\n"
    f"⚡ {MAX_DOWNLOADS} parallel downloads (×{MAX_SEGMENTS} connections each), "
    f"{MAX_UPLOADS} parallel uploads over {UPLOAD_SESSIONS} sessions, "
    f"{UPLOAD_WORKERS} concurrent parts per file + cryptg crypto.\n\n"
    "⏸ If a source throttles us (HTTP 403/410/429) the bot waits it out and "
    "retries automatically; if the source blocks the whole server the batch "
    "pauses and resumes by itself.\n"
    "🧠 Uploaded files are remembered — re-send the same/refreshed txt and "
    "finished files are skipped (batches are resumable). /forget clears it.\n"
    "💾 Storage guard: before a file ENTERS download, the bot checks the "
    "disk — it starts only when the file's FULL size fits (~7.5 GB used is "
    "the limit on an 8 GB server). Uploads NEVER stop; every file is "
    "deleted the INSTANT its upload finishes, and the freed space lets the "
    "next file start. Huge lists (100–200+ links) complete on any disk.\n"
    "➕ ONE queue: links or txt files sent while a batch is running are ADDED "
    "to it automatically — never rejected, never split into separate batches.\n\n"
    "Commands:\n"
    "/start — this help\n"
    "/cancel — stop the running batch\n"
    "/clean — delete leftover temp data + show disk usage\n"
    "/forget — clear the uploaded-files memory\n\n"
    "You can also send a single line 'name,url' as a plain text message."
)


async def cmd_start(event):
    if event.sender_id != OWNER_ID:
        await event.respond("⛔ You are not authorized to use this bot.")
        return
    await event.respond(HELP_TEXT)


async def cmd_cancel(event):
    global current_batch
    if event.sender_id != OWNER_ID:
        return
    if current_batch and not current_batch.finished:
        current_batch.cancelled = True
        await event.respond("⛔ Cancelling the current batch…")
    else:
        await event.respond("No batch is running.")


async def cmd_clean(event):
    if event.sender_id != OWNER_ID:
        return
    active = None
    if current_batch and not current_batch.finished:
        active = current_batch.batch_dir
    n = sweep_temp_dirs(skip=active)
    await event.respond(f"🧹 Removed {n} leftover temp item(s)."
                        + (" (kept the running batch's folder)" if active and n == 0 else "")
                        + f"\n💾 Disk: {disk_info()}"
                        + f"\n🚦 A file enters download only when its full size fits "
                          f"(keeps {fmt_bytes(MIN_FREE_BYTES)} free / below "
                          f"{MAX_DISK_USE_PCT:.0f}% used) — uploads never stop")


async def cmd_forget(event):
    """🧠 Clear the uploaded-files memory so nothing gets skipped."""
    if event.sender_id != OWNER_ID:
        return
    n = len(HISTORY)
    HISTORY.clear()
    save_history()
    await event.respond(f"🧠 Forgot {n} uploaded file name(s). "
                        f"The next batch will re-upload everything.")


def document_name(doc) -> str:
    """The filename Telegram attached to a document. Telethon's Document has
    NO 'original_name' attribute — the name lives in a
    DocumentAttributeFilename inside doc.attributes."""
    try:
        for attr in (doc.attributes if doc else None) or []:
            name = getattr(attr, "file_name", None)
            if name:
                return name
    except Exception:
        pass
    return ""


async def on_document(event):
    """Handles uploaded link-list files (.txt). Never fails silently."""
    doc = event.message.document
    log.info("📩 Incoming message from %s • document=%r mime=%s size=%s • text=%r",
             event.sender_id,
             document_name(doc) or None,
             getattr(doc, "mime_type", None),
             getattr(doc, "size", None),
             (event.message.text or "")[:60])
    if event.sender_id != OWNER_ID:
        log.warning("⛔ Rejected sender %s — this bot only accepts OWNER_ID=%d "
                    "(set the OWNER_ID env var to your Telegram user id)",
                    event.sender_id, OWNER_ID)
        await event.respond("⛔ You are not authorized to use this bot.")
        return
    if not doc:
        return
    fname = document_name(doc).lower()
    mime = (doc.mime_type or "").lower()
    small = bool(doc.size and doc.size < 512 * 1024)
    is_list = (fname.endswith((".txt", ".text", ".list", ".csv"))
               or mime.startswith("text/")
               or small)
    if not is_list:
        await event.respond("Please upload a .txt file (format: name,URL per line).")
        return
    if current_batch and not current_batch.finished and current_batch.cancelled:
        await event.respond("⏳ The previous batch is cancelling — wait a few seconds "
                            "and send it again.")
        return

    await event.respond(f"📄 Received {document_name(doc) or 'file'} — reading link list…")

    tmpdir = tempfile.mkdtemp(prefix="tglist_")
    try:
        try:
            path = await event.client.download_media(event.message, file=tmpdir + os.sep)
            if not path:
                raise JobError("Telegram returned no file for this message")
            raw = Path(path).read_bytes()
        except Exception as e:
            log.exception("txt download failed")
            await event.respond(f"❌ Could not download the txt from Telegram: "
                                f"{type(e).__name__}: {e}")
            return

        text = decode_txt(raw)
        log.info("📄 txt decoded: %d bytes → %d chars, %d non-empty line(s)",
                 len(raw), len(text),
                 sum(1 for l in text.splitlines() if l.strip()))
        jobs = parse_jobs(text, Path(tempfile.gettempdir()) / "placeholder")
        valid = [j for j in jobs if j.status != "failed"]
        log.info("Parsed %d job(s) (%d valid) from %s",
                 len(jobs), len(valid), document_name(doc))

        if not valid:
            sample = "\n".join(repr(l.strip())[:90]
                               for l in text.splitlines() if l.strip())
            sample = "\n".join(sample.splitlines()[:3])
            if looks_like_link_list(text):
                await event.respond(
                    "❌ I found URLs but could not parse any valid line.\n"
                    "Expected format — one entry per line:\n"
                    "     name,https://example.com/video.mp4\n"
                    f"First line(s) I saw:\n{sample}")
            else:
                await event.respond(
                    "❌ This file contains no http/https links.\n"
                    "Expected format — one entry per line:\n"
                    "     name,https://example.com/video.mp4\n"
                    "(save as plain text — UTF-8/UTF-16/ANSI all work)\n"
                    f"First line(s) I saw:\n{sample}")
            return

        # ➕ a batch is already running? these links JOIN its queue
        if current_batch and not current_batch.finished and not current_batch.cancelled:
            await add_to_running_batch(event, jobs, document_name(doc) or "video.txt")
            return

        try:
            await run_batch(event.client, event.chat_id, jobs,
                            document_name(doc) or "video.txt",
                            upload_clients=getattr(event.client, "_upload_clients", None))
        except Exception as e:
            log.exception("run_batch crashed")
            await event.respond(f"❌ Batch crashed: {type(e).__name__}: {e}")
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


async def on_text(event):
    """Bonus: a plain-text 'name,url' message uploads a single video."""
    if event.sender_id != OWNER_ID or event.message.document:
        return
    txt = (event.message.text or "").strip()
    if not txt or txt.startswith("/"):
        return
    if "http://" not in txt and "https://" not in txt:
        await event.respond(HELP_TEXT)
        return
    if current_batch and not current_batch.finished and current_batch.cancelled:
        await event.respond("⏳ The previous batch is cancelling — wait a few seconds "
                            "and send it again.")
        return
    try:
        jobs = parse_jobs(txt, Path(tempfile.gettempdir()) / "placeholder")
        # ➕ batch already running? these links JOIN its queue (one batch for all)
        if current_batch and not current_batch.finished:
            await add_to_running_batch(event, jobs, "message")
            return
        await run_batch(event.client, event.chat_id, jobs, "direct-link",
                        upload_clients=getattr(event.client, "_upload_clients", None))
    except Exception as e:
        log.exception("text-path batch crashed")
        await event.respond(f"❌ Batch crashed: {type(e).__name__}: {e}")


# ----------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------
async def main_async():
    try:
        import cryptg  # noqa: F401
        crypto = "⚡ cryptg ACTIVE — fast native MTProto encryption"
    except ImportError:
        crypto = "⚠ cryptg NOT installed — slower pure-Python crypto (pip install cryptg)"

    client = TelegramClient("uploader_bot", API_ID, API_HASH, flood_sleep_threshold=2400)
    await client.start(bot_token=BOT_TOKEN)
    client.parse_mode = None

    me = await client.get_me()
    log.info("✔ Logged in as %s (@%s)", me.first_name, me.username)
    log.info("  Connected to Telegram DC %s (closer server = faster uploads)",
             client.session.dc_id)
    log.info("  %s", crypto)

    upload_clients = [client]
    for i in range(2, UPLOAD_SESSIONS + 1):
        try:
            c = TelegramClient(f"uploader_bot_{i}", API_ID, API_HASH,
                               flood_sleep_threshold=600)
            await c.start(bot_token=BOT_TOKEN)
            c.parse_mode = None
            upload_clients.append(c)
        except Exception as e:
            log.warning("Extra upload session %d failed (%s) — continuing with %d",
                        i, e, len(upload_clients))
            break
    client._upload_clients = upload_clients

    n_hist = load_history()
    n_swept = sweep_temp_dirs()
    log.info("  🤖 Bot code version v9.1")
    log.info("  🧠 Upload memory: %d file name(s) remembered (SKIP_UPLOADED=%s)",
             n_hist, SKIP_UPLOADED)
    log.info("  🧹 Startup cleanup: removed %d leftover temp item(s) • disk: %s",
             n_swept, disk_info())
    log.info("  Owner ID: %d • waves of %d • downloads: %d (×%d seg) • uploads: %d over"
             " %d sessions (retried %d×) • rate-limit waits: %d × %ds base"
             " • storage guard: pre-download full-fit check, keeps %s free (limit %.0f%%)",
             OWNER_ID, WAVE_SIZE or "∞", MAX_DOWNLOADS, MAX_SEGMENTS, MAX_UPLOADS,
             len(upload_clients), UPLOAD_RETRIES, RATE_LIMIT_RETRIES, RATE_LIMIT_BASE,
             fmt_bytes(MIN_FREE_BYTES), MAX_DISK_USE_PCT)
    log.info("Send /start to @%s, then upload your video.txt.", me.username)

    client.add_event_handler(cmd_start, events.NewMessage(pattern=r"^/(start|help)(@\w+)?$"))
    client.add_event_handler(cmd_cancel, events.NewMessage(pattern=r"^/cancel(@\w+)?$"))
    client.add_event_handler(cmd_clean, events.NewMessage(pattern=r"^/(clean|storage)(@\w+)?$"))
    client.add_event_handler(cmd_forget, events.NewMessage(pattern=r"^/(forget|reset)(@\w+)?$"))
    client.add_event_handler(on_document, events.NewMessage(incoming=True))
    client.add_event_handler(on_text, events.NewMessage(incoming=True))

    try:
        await client.run_until_disconnected()
    finally:
        for c in upload_clients[1:]:
            try:
                await c.disconnect()
            except Exception:
                pass


def main():
    # debug helper:  python bot.py --parse video.txt
    if "--parse" in sys.argv:
        p = Path(sys.argv[sys.argv.index("--parse") + 1])
        jobs = parse_jobs(p.read_text(errors="replace"), Path("/tmp/parse-test"))
        print(f"{len(jobs)} job(s):")
        for j in jobs:
            print(f"  [{j.index}] name={j.name!r}  url={j.url[:90]}"
                  + (f"  ERROR={j.error}" if j.error else ""))
        return
    asyncio.run(main_async())


if __name__ == "__main__":
    main()
