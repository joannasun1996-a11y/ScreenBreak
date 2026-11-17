import cv2
import mediapipe as mp
import math
import json
import os
import re
import smtplib
import sys
import threading
import time
import traceback
import webbrowser
import tkinter as tk
from datetime import datetime, timedelta
from email.message import EmailMessage
from tkinter import messagebox, ttk
from PIL import Image, ImageTk
from pathlib import Path

# ScreenBreak v2.8 (2026-11-17): local webcam gaze estimate +
# accumulated screen-looking time.
# Webcam frames are processed locally and are never recorded or uploaded.
#
# v2.8 — understandable with no explanation (see CHANGES.txt):
#  a first-run "How ScreenBreak works" window explains the app in
#  plain words (reopenable any time from the "How it works"
#  button), the subtitle says what the app does, the live bar has
#  a colour legend underneath it, and a batch of small clarity
#  fixes (plain preset name, unit note, 2-Step Verification note,
#  Cancel button, a camera hint that says exactly where to look
#  in Windows, a clearer break popup, and the "App was off" colour
#  in the report legend).
#
# v2.7 — full audit + simpler and friendlier (see CHANGES.txt):
#  7 bugs fixed (sleep misread after a freeze, multi-day gaps
#  painted as "away", "Send report now" demanding an email when
#  email was off, the old name in a sent report, a failed email
#  never retrying, a break in progress shown as finished, and a
#  duplicated helper). The daily report now has ONE checkbox
#  instead of two, every status message is in plain words (no
#  shouting capitals, no "strike" jargon — "peek" instead), the
#  screen-time bar shows the goal, and the camera preview no
#  longer opens on its own at startup.
#
# v2.6 — the daily report is live and easier to read (see CHANGES.txt):
#  the report page reloads itself every 30 seconds while the app
#  rewrites it, a live timeline bar in the main window shows the
#  colours as they happen, and the report opens with a plain-English
#  summary and a "Right now" line.
#
# v2.5.2 — the report timeline is smoothed for display, so rapid
# looking/away flicker draws as solid blocks instead of hundreds
# of thin stripes (see CHANGES.txt).
#
# v2.5.1 — daily report timeline now looks like Joanna's sketch:
#  an hour label and tick at every hour, covering the day's
#  activity instead of midnight to midnight (see CHANGES.txt).
#
# v2.5 — auto-start, daily report, nicer UI (see CHANGES.txt):
#  Starts automatically when you sign in (toggle in Settings),
#  tracks the day as green screen time / red distracted / blue
#  break segments, and sends a daily timeline report by Gmail
#  (app password) at the time you choose. Closing the computer
#  counts as looking away.
#
# v2.4 — time units + audit fixes (see CHANGES.txt):
#  Screen time and break time can now be set in seconds, minutes or
#  hours (e.g. every 20 min, 20 sec eye break). Settings are stored
#  in seconds internally; old minute-based data files are migrated
#  automatically. Also fixes the audit findings below.
#
# v2.3-Reset-Confirmation (kept in this version, see CHANGES.txt):
#  Popups use pop_to_front(): non-transient, centred, always-on-top,
#  so they appear even when the main window is minimized. Plus a
#  "Reset screen time" button that asks for confirmation first.
#
# v2.2 — 3-strike anti-spam for breaks (see CHANGES.txt):
#  A short peek (<3s) used to only pause the break timer, so you could
#  spam look 2s / away 10s / look 2s / away 10s and still finish a break
#  without really resting your eyes. Now:
#  - A glance = 1s of continuous looking during a break = 1 strike.
#  - Strike 1: warning only. Strike 2: break timer resets to 0.
#  - Strike 3: timer resets to 0 AND the required break grows by
#    2x the time you looked at the screen during this break
#    (penalty = 2 * looking time since the last penalty, so total
#    penalty across a break is exactly 2x total looking time).
#    Strikes then reset to 0 for the next set of 3.
#  - After any glance, you need 10s away in a row before the timer
#    counts again (settle time), so spamming look/away wastes time.
#  - Staring for 3s straight still resets immediately, as in v2.1.
#
# v2.1 fixes (kept in this version, see CHANGES.txt):
#  1. Saving was completely broken: state had no "settings" key, so
#     save_data() always raised KeyError and silently did nothing.
#     Settings, screen time and break progress never persisted.
#     Fixed by adding "settings" to state, making save_data() fall back
#     to DEFAULTS, writing atomically, and reporting errors instead of
#     swallowing them. Startup sleep-gap handling now saves immediately
#     so the gap is not double-counted on the next restart.
#  2. One bad frame killed the timer forever: update() scheduled the
#     next tick only at the end, so any exception stopped all future
#     ticks. Fixed with try/finally in update() so the next tick is
#     always scheduled, and per-frame errors are logged, not fatal.
#  3. One glance wiped a whole break. Fixed with a 3-second
#     continuous-looking debounce: away time only resets after 3s of
#     uninterrupted looking. A flicker no longer loses 9m59s.
#  4. Camera never retried. Fixed: if the camera is missing or a read
#     fails repeatedly, ScreenBreak retries opening it every 5s.
#  5. Sleep while the app was running did not count as a break:
#     wall_elapsed was computed but never used. Fixed: a wall-clock
#     gap >5s (monotonic time barely advanced) is treated as away
#     time during a required break, even if the camera is unavailable.
#  6. Gaze check was too loose vertically (0.22-0.78 almost always
#     passed). Tightened to 0.30-0.70.
#  7. Smaller fixes: save every SAVE_EVERY_SECONDS (10s) instead of
#     every 1s; preview thumbnail now fits its 680x420 window
#     (640x360, was 900x650); Settings and Break Complete popups can
#     no longer stack; initial camera button matches actual state;
#     corrupt data files are backed up instead of silently discarded.

# Time units for the Settings screen. Settings are stored in seconds
# internally; the unit is only how the value is shown and entered.
UNIT_MULTIPLIERS = {"seconds": 1, "minutes": 60, "hours": 3600}
UNIT_CHOICES = ["seconds", "minutes", "hours"]
# Valid ranges, in seconds (screen: 1s-24h, break: 1s-4h).
SCREEN_LIMIT_MIN_SECONDS = 1
SCREEN_LIMIT_MAX_SECONDS = 24 * 3600
BREAK_MIN_SECONDS = 1
BREAK_MAX_SECONDS = 4 * 3600
# Eye-openness: eyelid distance / eye width. Below this in BOTH eyes
# the eyes are treated as closed (looking away), so shutting your eyes
# no longer counts as screen time.
EYE_OPEN_MIN = 0.12

# --- Daily report: green = looking at screen, red = looking away
# while NOT on a break (distracted), blue = on a break, grey = not
# tracked (camera off / face detection failed). ---
STATE_COLORS = {
    "screen": "#2E9E5B",
    "away": "#D64541",
    "break": "#2F7ED8",
    "unknown": "#9AA5B1",
}
STATE_LABELS = {
    "screen": "Looking at screen",
    "away": "Looking away (distracted)",
    "break": "On a break",
    "unknown": "Not tracked",
}
REPORT_STATE_ORDER = ["screen", "away", "break", "unknown"]

_EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")


def is_valid_email(addr):
    return bool(addr and _EMAIL_RE.match(str(addr).strip()))


def parse_report_time(text):
    """Parse a report time like '18:00', '6:30pm' or '6pm'.
    Returns (hour, minute) in 24h form, or None."""
    text = (text or "").strip().lower()
    m = re.match(r"^(\d{1,2}):(\d{2})\s*([ap]m)?$", text)
    if m:
        hour, minute, ampm = int(m.group(1)), int(m.group(2)), m.group(3)
        if ampm:
            if hour < 1 or hour > 12 or minute > 59:
                return None
            if ampm == "pm" and hour != 12:
                hour += 12
            if ampm == "am" and hour == 12:
                hour = 0
        elif hour > 23 or minute > 59:
            return None
        return hour, minute
    m = re.match(r"^(\d{1,2})\s*([ap]m)$", text)
    if m:
        hour = int(m.group(1))
        if hour < 1 or hour > 12:
            return None
        if m.group(2) == "pm" and hour != 12:
            hour += 12
        if m.group(2) == "am" and hour == 12:
            hour = 0
        return hour, 0
    return None

CAMERA_INDEX = 0
FRAME_WIDTH = 960
FRAME_HEIGHT = 540
SAVE_EVERY_SECONDS = 10
# Continuous looking required before a break timer is reset.
BREAK_RESET_LOOKING_SECONDS = 3.0
# Continuous looking that counts as one glance / strike.
GLANCE_SECONDS = 1.0
# Strikes before a penalty is added.
STRIKES_TO_PENALTY = 3
# Penalty multiplier: on the 3rd strike, add this many times the
# looking time since the last penalty to the required break.
PENALTY_MULTIPLIER = 2.0
# Continuous away time needed after a glance before the away timer
# counts again.
SETTLE_SECONDS = 10.0
# How often to retry opening the camera after a failure.
CAMERA_RETRY_SECONDS = 5.0
# A wall-clock gap larger than this, with almost no monotonic time
# passing, is treated as sleep / suspension.
SLEEP_GAP_MIN_SECONDS = 5.0
# Consecutive failed frame reads before the camera is reopened.
CAMERA_MAX_CONSECUTIVE_FAILURES = 25

LEFT_EYE_CORNERS = (33, 133)
RIGHT_EYE_CORNERS = (362, 263)
LEFT_IRIS = (468, 469, 470, 471, 472)
RIGHT_IRIS = (473, 474, 475, 476, 477)
CENTER_MIN = 0.34
CENTER_MAX = 0.66
VERTICAL_MIN = 0.30
VERTICAL_MAX = 0.70


def distance(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


def point(landmarks, idx, width, height):
    p = landmarks[idx]
    return (p.x * width, p.y * height)


def eye_ratio(landmarks, corners, iris_indices, width, height):
    a = point(landmarks, corners[0], width, height)
    b = point(landmarks, corners[1], width, height)
    iris_pts = [point(landmarks, i, width, height) for i in iris_indices]
    iris = (sum(p[0] for p in iris_pts) / len(iris_pts),
            sum(p[1] for p in iris_pts) / len(iris_pts))
    dx, dy = b[0] - a[0], b[1] - a[1]
    length2 = dx * dx + dy * dy
    if length2 < 1:
        return 0.5, 0.5
    horizontal = ((iris[0] - a[0]) * dx + (iris[1] - a[1]) * dy) / length2
    vertical = ((iris[0] - a[0]) * (-dy) + (iris[1] - a[1]) * dx) / max(math.sqrt(length2), 1)
    vertical = vertical / max(distance(a, b), 1) + 0.5
    return horizontal, vertical


def eye_open_ratio(landmarks, upper_idx, lower_idx, corners, width, height):
    """Eyelid opening as a fraction of eye width. ~0.25 open, ~0.05 shut."""
    upper = point(landmarks, upper_idx, width, height)
    lower = point(landmarks, lower_idx, width, height)
    a = point(landmarks, corners[0], width, height)
    b = point(landmarks, corners[1], width, height)
    return distance(upper, lower) / max(distance(a, b), 1)


def classify(face_landmarks, w, h):
    lm = face_landmarks.landmark
    lrx, lry = eye_ratio(lm, LEFT_EYE_CORNERS, LEFT_IRIS, w, h)
    rrx, rry = eye_ratio(lm, RIGHT_EYE_CORNERS, RIGHT_IRIS, w, h)
    x, y = (lrx + rrx) / 2, (lry + rry) / 2
    nose = point(lm, 1, w, h)
    left_face = point(lm, 234, w, h)
    right_face = point(lm, 454, w, h)
    face_left, face_right = sorted((left_face[0], right_face[0]))
    face_width = max(face_right - face_left, 1)
    nose_x = (nose[0] - face_left) / face_width
    eyes_centered = CENTER_MIN <= x <= CENTER_MAX and VERTICAL_MIN <= y <= VERTICAL_MAX
    head_centered = 0.34 <= nose_x <= 0.66
    # FIX (v2.4 audit): iris landmarks exist even with eyes shut, so
    # closed eyes used to count as looking. Require at least one eye
    # open (a wink still counts; both shut does not).
    left_open = eye_open_ratio(lm, 159, 145, LEFT_EYE_CORNERS, w, h)
    right_open = eye_open_ratio(lm, 386, 374, RIGHT_EYE_CORNERS, w, h)
    eyes_open = left_open >= EYE_OPEN_MIN or right_open >= EYE_OPEN_MIN
    return eyes_centered and head_centered and eyes_open, x, y, nose_x


def pop_to_front(win, width, height, keep_on_top_ms=None):
    """Make a popup appear on top of everything, even when the main
    ScreenBreak window is minimized or another app is full screen.
    The popup is NOT transient to the main window (a transient child
    is hidden along with a minimized parent on Windows) and is marked
    always-on-top so Windows' focus-stealing rules can't bury it.
    keep_on_top_ms: drop always-on-top after this many ms (None = keep
    it on top until the popup is closed)."""
    try:
        win.update_idletasks()
        x = max(0, (win.winfo_screenwidth() - width) // 2)
        y = max(0, (win.winfo_screenheight() - height) // 3)
        win.geometry(f"{width}x{height}+{x}+{y}")
        win.deiconify()
        win.attributes("-topmost", True)
        win.lift()
        try:
            win.focus_force()
        except tk.TclError:
            pass
        if keep_on_top_ms is not None:
            win.after(keep_on_top_ms, lambda: _drop_topmost(win))
    except tk.TclError:
        pass


def _drop_topmost(win):
    try:
        if win.winfo_exists():
            win.attributes("-topmost", False)
    except tk.TclError:
        pass


def is_minimized(win):
    try:
        return win.state() == "iconic"
    except tk.TclError:
        return False


def format_time(seconds):
    # FIX (v2.4 audit): 20s used to show as "0 min 20 sec" and 0 as
    # "0 min 00 sec". Short times now read naturally.
    seconds = max(0, int(seconds))
    hours, remainder = divmod(seconds, 3600)
    minutes, secs = divmod(remainder, 60)
    if hours:
        return f"{hours} hr {minutes:02d} min"
    if minutes:
        return f"{minutes} min {secs:02d} sec"
    return f"{secs} sec"


def format_duration(seconds):
    """Human words for a setting, e.g. 20 -> '20 seconds',
    1200 -> '20 minutes', 5400 -> '1 hour 30 minutes'."""
    seconds = max(0, int(round(seconds)))
    if seconds < 60:
        return f"{seconds} second" + ("s" if seconds != 1 else "")
    if seconds < 3600:
        minutes, secs = divmod(seconds, 60)
        text = f"{minutes} minute" + ("s" if minutes != 1 else "")
        if secs:
            text += f" {secs} second" + ("s" if secs != 1 else "")
        return text
    hours, remainder = divmod(seconds, 3600)
    minutes = remainder // 60
    text = f"{hours} hour" + ("s" if hours != 1 else "")
    if minutes:
        text += f" {minutes} minute" + ("s" if minutes != 1 else "")
    return text


def display_value(total_seconds, unit):
    """How many `unit`s a duration is, as a tidy string for an Entry:
    whole numbers stay whole ('120'), otherwise up to 2 decimals."""
    value = total_seconds / UNIT_MULTIPLIERS[unit]
    if abs(value - round(value)) < 1e-9:
        return str(int(round(value)))
    return f"{value:.2f}".rstrip("0").rstrip(".")


APP_DIR = Path(os.environ.get("LOCALAPPDATA", str(Path.home()))) / "ScreenBreak"
APP_DIR.mkdir(parents=True, exist_ok=True)
# Single source of truth for the data file. The earlier top-level
# DATA_FILE = Path(__file__).with_name(...) was overwritten here and
# only confused things, so it was removed.
DATA_FILE = APP_DIR / "screenbreak_data.json"
LOG_FILE = APP_DIR / "screenbreak.log"
REPORT_DIR = APP_DIR / "reports"
DAILY_DIR = APP_DIR / "daily"


def log_error(message):
    """Log an error to screenbreak.log as well as stderr. When the app
    starts automatically at sign-in there is no console window, so
    the log file is the only place startup errors can be seen."""
    try:
        line = f"{datetime.now().isoformat(timespec='seconds')} {message}\n"
        with open(LOG_FILE, "a", encoding="utf-8") as f:
            f.write(line)
    except Exception:
        pass
    print(f"ScreenBreak: {message}", file=sys.stderr)
# Settings are stored in seconds internally, plus the display unit
# the user picked for each one. Legacy minute keys are kept in the
# saved file too, so an older ScreenBreak can still read it (it will
# see sub-minute values rounded to whole minutes — see CHANGES.txt).
DEFAULTS = {"screen_limit_seconds": 120 * 60, "break_seconds": 10 * 60,
            "screen_limit_unit": "minutes", "break_unit": "minutes",
            "screen_limit_minutes": 120, "break_minutes": 10,
            # Daily report (v2.5). The report is generated on this
            # computer; email needs a Gmail address + app password.
            "report_enabled": False,
            "report_name": "",
            "report_email": "",
            "report_time": "18:00",
            "report_email_enabled": False,
            "report_sender_email": "",
            "report_smtp_password": ""}


LOCK_FILE = APP_DIR / "screenbreak.lock"


def try_acquire_lock():
    """Best-effort single-instance guard. Returns (status, handle):
    ("acquired", handle) — this instance owns the lock, keep `handle`
    open until exit; ("locked", None) — another ScreenBreak is already
    running; ("unavailable", None) — locking failed for some other
    reason, so continue anyway rather than refusing to start.
    FIX (v2.4 audit): two copies used to fight over the camera and the
    data file, with the last one to save winning and progress lost.
    The OS releases the lock if the app crashes, so there is no stale
    lock to get stuck on."""
    import errno
    try:
        handle = open(LOCK_FILE, "a+b")
    except Exception:
        return "unavailable", None
    try:
        handle.write(b"\n")
        handle.flush()
        handle.seek(0)
        try:
            import msvcrt
            msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
        except ImportError:
            import fcntl
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        return "acquired", handle
    except (BlockingIOError, OSError, ImportError) as exc:
        try:
            handle.close()
        except Exception:
            pass
        if isinstance(exc, BlockingIOError) or getattr(exc, "errno", None) in (errno.EACCES, errno.EAGAIN):
            return "locked", None
        return "unavailable", None


def release_lock(handle):
    if handle is None:
        return
    try:
        try:
            import msvcrt
            msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
        except ImportError:
            import fcntl
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
        except Exception:
            pass
        handle.close()
    except Exception:
        pass
    try:
        LOCK_FILE.unlink()
    except Exception:
        pass


def _safe_int(value, default):
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _safe_float(value, default):
    # FIX (v2.4 audit): load_data used float() directly on saved
    # fields, so one bad value (e.g. last_saved: "oops") threw and
    # the whole file was treated as corrupt, losing all progress.
    # Bad values now fall back to the default instead.
    try:
        result = float(value)
    except (TypeError, ValueError):
        return default
    if result != result or result in (float("inf"), float("-inf")):
        return default
    return result


def _normalize_settings(raw):
    """Turn a saved settings dict into the v2.4 seconds-based form.
    Accepts the new seconds keys, or migrates the old minute keys
    (v2.1-v2.3 files), or falls back to DEFAULTS."""
    if not isinstance(raw, dict):
        raw = {}
    if "screen_limit_seconds" in raw or "break_seconds" in raw:
        screen_sec = _safe_float(raw.get("screen_limit_seconds",
                                         DEFAULTS["screen_limit_seconds"]),
                                 DEFAULTS["screen_limit_seconds"])
        break_sec = _safe_float(raw.get("break_seconds",
                                        DEFAULTS["break_seconds"]),
                                DEFAULTS["break_seconds"])
    else:
        # Old file: minutes only. 120 min -> 7200s, 10 min -> 600s.
        screen_sec = _safe_float(raw.get("screen_limit_minutes", 120), 120) * 60
        break_sec = _safe_float(raw.get("break_minutes", 10), 10) * 60
    screen_sec = max(SCREEN_LIMIT_MIN_SECONDS,
                     min(SCREEN_LIMIT_MAX_SECONDS, int(round(screen_sec))))
    break_sec = max(BREAK_MIN_SECONDS,
                    min(BREAK_MAX_SECONDS, int(round(break_sec))))
    screen_unit = raw.get("screen_limit_unit", "minutes")
    if screen_unit not in UNIT_MULTIPLIERS:
        screen_unit = "minutes"
    break_unit = raw.get("break_unit", "minutes")
    if break_unit not in UNIT_MULTIPLIERS:
        break_unit = "minutes"
    report_time = str(raw.get("report_time", "18:00") or "").strip()[:20]
    if parse_report_time(report_time) is None:
        report_time = "18:00"
    return {
        "screen_limit_seconds": screen_sec,
        "break_seconds": break_sec,
        "screen_limit_unit": screen_unit,
        "break_unit": break_unit,
        # Legacy keys, kept so older versions can still read the file.
        "screen_limit_minutes": screen_sec / 60,
        "break_minutes": break_sec / 60,
        # v2.7: the two checkboxes became one. report_enabled is
        # kept only for old files and now mirrors the email switch.
        "report_enabled": bool(raw.get("report_email_enabled", raw.get("report_enabled", False))),
        "report_name": str(raw.get("report_name", "") or "").strip()[:100],
        "report_email": str(raw.get("report_email", "") or "").strip()[:200],
        "report_time": report_time,
        "report_email_enabled": bool(raw.get("report_email_enabled", False)),
        "report_sender_email": str(raw.get("report_sender_email", "") or "").strip()[:200],
        "report_smtp_password": str(raw.get("report_smtp_password", "") or ""),
    }


def load_data():
    try:
        raw = DATA_FILE.read_text(encoding="utf-8")
    except FileNotFoundError:
        return {
            "looking_seconds": 0.0, "break_required": False, "away_seconds": 0.0,
            "last_saved": time.time(), "settings": DEFAULTS.copy(),
            "break_extension_seconds": 0.0, "break_looking_seconds": 0.0,
            "strikes": 0, "penalized_looking_seconds": 0.0,
            # v2.5: True here means "no unclean gap to explain". Old
            # files have no such key, so they default to True.
            "clean_exit": True, "last_report_date": "",
            # v2.8: has the first-run explanation been shown?
            "welcomed": False,
        }
    except Exception as exc:
        print(f"ScreenBreak: could not read data file: {exc}", file=sys.stderr)
        return {
            "looking_seconds": 0.0, "break_required": False, "away_seconds": 0.0,
            "last_saved": time.time(), "settings": DEFAULTS.copy(),
            "break_extension_seconds": 0.0, "break_looking_seconds": 0.0,
            "strikes": 0, "penalized_looking_seconds": 0.0,
            # v2.5: True here means "no unclean gap to explain". Old
            # files have no such key, so they default to True.
            "clean_exit": True, "last_report_date": "",
            # v2.8: has the first-run explanation been shown?
            "welcomed": False,
        }
    try:
        data = json.loads(raw)
        if not isinstance(data, dict):
            raise ValueError("data file is not a JSON object")
        settings = data.get("settings", {}) or {}
        if not isinstance(settings, dict):
            settings = {}
        return {
            "looking_seconds": max(0.0, min(24 * 3600.0, _safe_float(data.get("looking_seconds", 0), 0.0))),
            "break_required": bool(data.get("break_required", False)),
            "away_seconds": max(0.0, min(24 * 3600.0, _safe_float(data.get("away_seconds", 0), 0.0))),
            "last_saved": _safe_float(data.get("last_saved", time.time()), time.time()),
            "break_extension_seconds": max(0.0, _safe_float(data.get("break_extension_seconds", 0), 0.0)),
            "break_looking_seconds": max(0.0, _safe_float(data.get("break_looking_seconds", 0), 0.0)),
            "strikes": max(0, min(2, _safe_int(data.get("strikes", 0), 0))),
            "penalized_looking_seconds": max(0.0, _safe_float(data.get("penalized_looking_seconds", 0), 0.0)),
            "settings": _normalize_settings(settings),
            "clean_exit": bool(data.get("clean_exit", True)),
            "last_report_date": str(data.get("last_report_date", "") or ""),
            "welcomed": bool(data.get("welcomed", False)),
        }
    except Exception as exc:
        # Back the corrupt file up instead of silently discarding it,
        # so progress is not lost without a trace.
        try:
            backup = DATA_FILE.with_name(
                f"screenbreak_data.corrupt-{int(time.time())}.json")
            backup.write_text(raw, encoding="utf-8")
            print(f"ScreenBreak: corrupt data file backed up to {backup}: {exc}",
                  file=sys.stderr)
        except Exception:
            print(f"ScreenBreak: corrupt data file, could not back up: {exc}",
                  file=sys.stderr)
        return {
            "looking_seconds": 0.0, "break_required": False, "away_seconds": 0.0,
            "last_saved": time.time(), "settings": DEFAULTS.copy(),
            "break_extension_seconds": 0.0, "break_looking_seconds": 0.0,
            "strikes": 0, "penalized_looking_seconds": 0.0,
            # v2.5: True here means "no unclean gap to explain". Old
            # files have no such key, so they default to True.
            "clean_exit": True, "last_report_date": "",
            # v2.8: has the first-run explanation been shown?
            "welcomed": False,
        }


def save_data(state):
    # FIX 1: state now always carries "settings", but fall back to
    # DEFAULTS anyway so a missing key can never silently kill saving.
    settings = state.get("settings", DEFAULTS)
    payload = {
        "looking_seconds": round(float(state.get("looking_seconds", 0.0)), 1),
        "break_required": bool(state.get("break_required", False)),
        "away_seconds": round(float(state.get("away_seconds", 0.0)), 1),
        "last_saved": time.time(),
        "settings": settings,
        "break_extension_seconds": round(float(state.get("break_extension_seconds", 0.0)), 1),
        "break_looking_seconds": round(float(state.get("break_looking_seconds", 0.0)), 1),
        "strikes": int(state.get("strikes", 0)),
        "penalized_looking_seconds": round(float(state.get("penalized_looking_seconds", 0.0)), 1),
        # v2.5: False while the app is running, True only when it is
        # closed properly. Lets startup tell sleep/shutdown apart
        # from simply having been closed.
        "clean_exit": bool(state.get("clean_exit", False)),
        "last_report_date": str(state.get("last_report_date", "") or ""),
        "welcomed": bool(state.get("welcomed", False)),
    }
    try:
        APP_DIR.mkdir(parents=True, exist_ok=True)
        # Atomic write: write to a temp file, then replace. A crash
        # mid-write can no longer leave a half-written JSON file.
        tmp = DATA_FILE.with_suffix(".tmp")
        tmp.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        os.replace(tmp, DATA_FILE)
    except Exception as exc:
        # Never swallow this silently again — the original bug hid
        # for exactly this reason.
        print(f"ScreenBreak: could not save data to {DATA_FILE}: {exc}",
              file=sys.stderr)
        traceback.print_exc()


def day_key(timestamp=None):
    """Local date string 'YYYY-MM-DD' for a timestamp (default: now)."""
    return datetime.fromtimestamp(
        timestamp if timestamp is not None else time.time()).strftime("%Y-%m-%d")


def _end_of_day(timestamp):
    """Midnight at the end of the day containing `timestamp`."""
    dt = datetime.fromtimestamp(timestamp)
    return (datetime(dt.year, dt.month, dt.day) + timedelta(days=1)).timestamp()


def _day_file(date_str):
    return DAILY_DIR / f"{date_str}.json"


def load_day(date_str):
    """Load one day's tracking: segments + counters. Never raises."""
    try:
        data = json.loads(_day_file(date_str).read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            raise ValueError("daily file is not a JSON object")
        segments = data.get("segments", [])
        if not isinstance(segments, list):
            segments = []
        clean = []
        for seg in segments:
            if not isinstance(seg, dict):
                continue
            try:
                s = float(seg["start"])
                e = float(seg["end"])
                st = str(seg["state"])
            except (KeyError, TypeError, ValueError):
                continue
            if st not in STATE_COLORS or e <= s:
                continue
            clean.append({"start": s, "end": e, "state": st})
        return {
            "segments": clean,
            "breaks_completed": max(0, _safe_int(data.get("breaks_completed", 0), 0)),
            "strikes": max(0, _safe_int(data.get("strikes", 0), 0)),
        }
    except FileNotFoundError:
        return {"segments": [], "breaks_completed": 0, "strikes": 0}
    except Exception as exc:
        log_error(f"could not read daily file {date_str}: {exc}")
        return {"segments": [], "breaks_completed": 0, "strikes": 0}


def save_day(date_str, day_data):
    try:
        DAILY_DIR.mkdir(parents=True, exist_ok=True)
        tmp = _day_file(date_str).with_suffix(".tmp")
        tmp.write_text(json.dumps(day_data, indent=2), encoding="utf-8")
        os.replace(tmp, _day_file(date_str))
    except Exception as exc:
        log_error(f"could not save daily file {date_str}: {exc}")


def append_segment(date_str, start, end, state):
    """Add one closed segment to a day, merging with the previous
    segment when it is the same state and touches this one."""
    if end <= start or state not in STATE_COLORS:
        return
    day = load_day(date_str)
    segments = day["segments"]
    if segments and segments[-1]["state"] == state and abs(segments[-1]["end"] - start) < 1.0:
        segments[-1]["end"] = end
    else:
        segments.append({"start": start, "end": end, "state": state})
    day["segments"] = segments
    save_day(date_str, day)


def split_across_midnight(start, end):
    """Split [start, end) into (date_str, start, end) pieces at midnight."""
    pieces = []
    cursor = start
    while cursor < end:
        dt = datetime.fromtimestamp(cursor)
        boundary = (datetime(dt.year, dt.month, dt.day) + timedelta(days=1)).timestamp()
        piece_end = min(end, boundary)
        pieces.append((dt.strftime("%Y-%m-%d"), cursor, piece_end))
        cursor = piece_end
    return pieces


def append_segment_spanning(start, end, state):
    for date_str, s, e in split_across_midnight(start, end):
        append_segment(date_str, s, e, state)


def bump_day_counter(date_str, key, amount=1):
    day = load_day(date_str)
    day[key] = max(0, int(day.get(key, 0)) + amount)
    save_day(date_str, day)


def daily_totals(date_str, open_segment=None):
    """(totals by state in seconds, day data). open_segment is
    (start_epoch, state) for the segment still in progress."""
    day = load_day(date_str)
    totals = {state: 0.0 for state in STATE_COLORS}
    for seg in day["segments"]:
        totals[seg["state"]] += seg["end"] - seg["start"]
    if open_segment is not None:
        start, state = open_segment
        if state in totals:
            totals[state] += max(0.0, time.time() - start)
    return totals, day


def _clock(timestamp):
    return datetime.fromtimestamp(timestamp).strftime("%H:%M")


def _hour_label(timestamp, long_form=True):
    """'1:00 PM' / '1 PM'. Built by hand because strftime's %-I
    works on Linux but not on Windows (%#I there)."""
    dt = datetime.fromtimestamp(timestamp)
    hour12 = dt.hour % 12 or 12
    ampm = "AM" if dt.hour < 12 else "PM"
    return f"{hour12}:00 {ampm}" if long_form else f"{hour12} {ampm}"


def _longest_stretch(segments, state):
    best = 0.0
    for seg in segments:
        if seg["state"] == state:
            best = max(best, seg["end"] - seg["start"])
    return best


def _smooth_timeline(segments, range_start, range_end):
    """Turn flickery segments into clean solid blocks FOR DISPLAY
    ONLY (the totals and the stored data are untouched).
    The camera can flip between looking and away every few seconds,
    which used to draw the timeline as hundreds of thin red/green
    stripes. This groups the day into 1-minute buckets, colours
    each bucket by whichever state fills most of it, then runs a
    5-bucket median filter, so anything shorter than about 3
    minutes collapses into its neighbours while a real break of
    several minutes still shows as its own solid block."""
    if not segments or range_end <= range_start:
        return []
    range_seconds = range_end - range_start
    bucket = 60.0 if range_seconds >= 600 else max(10.0, range_seconds / 10.0)
    n_buckets = int((range_seconds + bucket - 1) // bucket)
    if n_buckets > 2880:  # safety net: never more than 48h of buckets
        bucket = range_seconds / 2880.0
        n_buckets = 2880
    # Bucket states by majority overlap. Segments are sorted, so
    # walk them once with a pointer instead of rescanning per bucket.
    states = []
    seg_i = 0
    n_seg = len(segments)
    for b in range(n_buckets):
        b_start = range_start + b * bucket
        b_end = min(range_end, b_start + bucket)
        while seg_i < n_seg and segments[seg_i]["end"] <= b_start:
            seg_i += 1
        overlap = {}
        j = seg_i
        while j < n_seg and segments[j]["start"] < b_end:
            s = max(b_start, segments[j]["start"])
            e = min(b_end, segments[j]["end"])
            if e > s:
                overlap[segments[j]["state"]] = overlap.get(segments[j]["state"], 0.0) + (e - s)
            j += 1
        if overlap:
            top = max(overlap.values())
            tied = [st for st, v in overlap.items() if v == top]
            if len(tied) > 1 and states:
                best = states[-1] if states[-1] in tied else tied[0]
            else:
                best = tied[0]
            states.append(best)
        else:
            states.append("off")
    # Median filter, 5 buckets wide: each bucket takes the most
    # common colour among itself and its two neighbours each side.
    # A 1-2 minute blip is outvoted and disappears; a run of 3 or
    # more minutes survives.
    filtered = list(states)
    for i in range(n_buckets):
        window = states[max(0, i - 2):min(n_buckets, i + 3)]
        counts = {}
        for st in window:
            counts[st] = counts.get(st, 0) + 1
        top = max(counts.values())
        winners = [st for st, c in counts.items() if c == top]
        filtered[i] = states[i] if states[i] in winners else winners[0]
    # Merge neighbouring buckets of the same colour into blocks.
    blocks = []
    for b in range(n_buckets):
        b_start = range_start + b * bucket
        b_end = min(range_end, b_start + bucket)
        if blocks and blocks[-1]["state"] == filtered[b]:
            blocks[-1]["end"] = b_end
        else:
            blocks.append({"start": b_start, "end": b_end, "state": filtered[b]})
    return blocks


def _timeline_range(date_str, segments, now):
    """The timeline's (start, end, seconds) for a day: from the first
    hour with activity to the last (today: up to now), never outside
    the day itself. Shared by the HTML report and the live bar in
    the main window so they always agree."""
    midnight = datetime.strptime(date_str, "%Y-%m-%d").timestamp()
    day_end = midnight + 86400
    if segments:
        first = min(s["start"] for s in segments)
        last = max(s["end"] for s in segments)
        range_start = datetime.fromtimestamp(first).replace(
            minute=0, second=0, microsecond=0).timestamp()
        if date_str == day_key(now):
            range_end = max(now, last)
        else:
            # Round up to the next hour — unless the last activity
            # already ends exactly on the hour (e.g. 11:00 PM), in
            # which case the bar ends there, like Joanna's sketch.
            floor_last = datetime.fromtimestamp(last).replace(
                minute=0, second=0, microsecond=0)
            if last == floor_last.timestamp():
                range_end = floor_last.timestamp()
            else:
                range_end = (floor_last + timedelta(hours=1)).timestamp()
        range_end = min(range_end, day_end)
        if range_end - range_start < 3600:
            range_end = min(range_start + 3600, day_end)
    else:
        range_start = midnight
        range_end = min(now, day_end) if date_str == day_key(now) else day_end
    # Never let the range leave the day (a stale segment with an old
    # timestamp once stretched it over years and hung the report).
    range_start = max(range_start, midnight)
    range_end = min(range_end, day_end)
    return range_start, range_end, max(1.0, range_end - range_start)


def build_report_html(date_str, settings, totals, day, open_segment=None):
    """Daily report as a self-contained HTML page: a timeline bar
    (green screen / red distracted / blue break / grey not tracked),
    totals, and the list of breaks."""
    name = (settings.get("report_name") or "").strip() or "Student"
    now = time.time()
    midnight = datetime.strptime(date_str, "%Y-%m-%d").timestamp()
    day_end = midnight + 86400
    is_today = date_str == day_key(now)
    segments = list(day["segments"])
    if open_segment is not None:
        start, state = open_segment
        if state in STATE_COLORS:
            # The segment in progress ends now (today) or at midnight
            # (a past day's report is only built after the fact).
            end = min(now, day_end) if is_today else day_end
            segments.append({"start": start, "end": end, "state": state})
    segments.sort(key=lambda s: s["start"])
    range_start, range_end, range_seconds = _timeline_range(date_str, segments, now)
    # v2.5.2: the bar is drawn from smoothed blocks, not the raw
    # segments — the camera can flip looking/away every few seconds,
    # which drew hundreds of thin stripes. Totals and the breaks
    # list below still use the raw segments, so the numbers are exact.
    blocks = _smooth_timeline(segments, range_start, range_end)
    if not blocks and range_end > range_start:
        blocks = [{"start": range_start, "end": range_end, "state": "off"}]
    bar_parts = []
    for b in blocks:
        width = max(0.0, (b["end"] - b["start"]) / range_seconds * 100.0)
        if width <= 0:
            continue
        colour = STATE_COLORS.get(b["state"], "#E5EAF0")
        label = STATE_LABELS.get(b["state"], "App off")
        bar_parts.append(
            f'<div title="{label}: {_clock(b["start"])}–{_clock(b["end"])}" '
            f'style="flex:{max(0.01, b["end"] - b["start"]):.1f} 1 0;min-width:2px;'
            f'background:{colour};"></div>')
    bar_html = "".join(bar_parts) if bar_parts else (
        '<div style="flex:1;background:#E5EAF0;"></div>')
    # Hour axis above the bar: a label and a tick at every hour,
    # like Joanna's sketch. Labels are spaced out when the day is
    # long, and use the short form ("1 PM") so they cannot overlap.
    span_hours = (range_end - range_start) / 3600.0
    label_every = 1 if span_hours <= 14 else (2 if span_hours <= 20 else 3)
    use_long_label = span_hours <= 12
    axis_parts = []
    hour = range_start
    while hour <= range_end + 0.5:
        pct = (hour - range_start) / range_seconds * 100.0
        if 0.0 <= pct <= 100.0:
            if pct <= 0.0:
                pos = "left:0;transform:translateX(0);"
            elif pct >= 100.0:
                pos = "left:100%;transform:translateX(-100%);"
            else:
                pos = f"left:{pct:.2f}%;transform:translateX(-50%);"
            axis_parts.append(
                f'<div class="tick" style="{pos}"></div>')
            hour_index = int(round((hour - range_start) / 3600.0))
            if hour_index % label_every == 0:
                label = _hour_label(hour, long_form=use_long_label)
                axis_parts.append(
                    f'<div class="lbl" style="{pos}">{label}</div>')
        hour += 3600
    axis_html = '<div class="axis">' + "".join(axis_parts) + "</div>"
    # FIX (v2.7 audit): a break still in progress used to show
    # here as if it had finished. Closed breaks come from the saved
    # segments; the open one is listed separately, marked as such.
    breaks = [s for s in day["segments"] if s["state"] == "break"]
    breaks_html = ""
    for b in breaks:
        breaks_html += (f"<li>{_clock(b['start'])}–{_clock(b['end'])} — "
                        f"{format_duration(b['end'] - b['start'])}</li>")
    if open_segment is not None and open_segment[1] == "break":
        breaks_html += (f"<li>{_clock(open_segment[0])}–now — "
                        f"{format_duration(now - open_segment[0])} (in progress)</li>")
    if not breaks_html:
        breaks_html = "<li>No breaks yet today.</li>"
    generated = datetime.fromtimestamp(now).strftime("%Y-%m-%d %H:%M")
    generated_clock = datetime.fromtimestamp(now).strftime("%H:%M:%S")
    # v2.6: a plain-English summary so the report reads at a glance.
    total_tracked = totals["screen"] + totals["away"] + totals["break"]
    if total_tracked <= 0:
        summary = ("No activity recorded yet today." if is_today
                   else "No activity was recorded on this day.")
    else:
        when = "So far today" if is_today else f"On {date_str}"
        summary = (f"{when}, you spent {format_duration(totals['screen'])} looking at the screen, "
                   f"{format_duration(totals['away'])} looking away, and "
                   f"{format_duration(totals['break'])} on a break.")
        if day["breaks_completed"]:
            n = day["breaks_completed"]
            summary += f" You finished {n} break{'s' if n != 1 else ''}."
    # v2.6: what is happening right now (only when the report is live).
    right_now_html = ""
    if is_today and open_segment is not None:
        cur_start, cur_state = open_segment
        cur_label = {"screen": "looking at the screen", "away": "looking away",
                     "break": "on a break",
                     "unknown": "not tracked (camera off)"}.get(cur_state, cur_state)
        right_now_html = (f'<div class="rightnow">Right now: {cur_label} '
                          f'since {_clock(cur_start)}.</div>')
    # v2.6: live refresh (today only). The app rewrites this file
    # every 30 seconds while it runs, and the page reloads itself
    # every 30 seconds, so what you see stays current with no
    # refresh button and no need to close and reopen it. The meta
    # refresh works even with JavaScript off; the countdown is just
    # a display.
    if is_today:
        live_head = '<meta http-equiv="refresh" content="30">'
        live_badge = ('<span class="live">\u25cf LIVE</span> '
                      '<span class="live-note">updates every 30 seconds &bull; '
                      f'last updated {generated_clock} &bull; next update in '
                      '<span id="countdown">30</span>s</span>')
        live_script = ('<script>var s=30;function tick(){s--;var el='
                       'document.getElementById("countdown");if(el){el.textContent=s;}'
                       'if(s>0){setTimeout(tick,1000);}}setTimeout(tick,1000);</script>')
    else:
        live_head = ""
        live_badge = '<span class="live-note">Final report for this day.</span>'
        live_script = ""
    return f"""<!DOCTYPE html>
<html><head><meta charset="utf-8">{live_head}<title>ScreenBreak daily report — {name} — {date_str}</title>
<style>
body{{font-family:Segoe UI,Arial,sans-serif;background:#F4F7FB;color:#172B4D;margin:0;padding:24px;}}
.card{{background:#fff;border-radius:12px;padding:20px 24px;margin:0 auto 16px;max-width:760px;box-shadow:0 1px 4px rgba(0,0,0,.08);}}
h1{{font-size:22px;margin:0 0 4px;}} .sub{{color:#62748A;font-size:13px;}}
.live{{color:#1E7B34;font-weight:700;font-size:13px;}} .live-note{{color:#62748A;font-size:12px;}}
.summary{{font-size:15px;margin:10px 0 2px;}} .rightnow{{font-size:13px;color:#287D55;font-weight:600;margin:2px 0 0;}}
.explain{{font-size:11px;color:#8291A3;display:block;margin-top:2px;}}
.axis{{position:relative;height:32px;margin:16px 0 0;}}
.axis .lbl{{position:absolute;top:0;font-size:11px;font-weight:600;color:#172B4D;white-space:nowrap;}}
.axis .tick{{position:absolute;bottom:0;width:2px;height:10px;background:#172B4D;}}
.bar{{display:flex;height:44px;border-radius:8px;overflow:hidden;margin:0 0 8px;}}
.legend{{font-size:13px;color:#52657A;}}
.legend span{{display:inline-block;width:12px;height:12px;border-radius:3px;margin:0 4px 0 12px;vertical-align:-1px;}}
.totals{{display:flex;gap:12px;flex-wrap:wrap;}}
.total{{flex:1;min-width:140px;background:#F4F7FB;border-radius:8px;padding:12px;}}
.total b{{font-size:18px;display:block;}} .total span{{font-size:12px;color:#62748A;}}
ul{{margin:8px 0 0;padding-left:20px;}} li{{margin:2px 0;}}
</style></head><body>
<div class="card"><h1>ScreenBreak daily report — {name}</h1>
<div class="sub">{date_str} &bull; generated {generated} &bull; green = looking at screen, red = looking away (distracted), blue = on a break, grey = not tracked, pale grey = app was off</div>
<div style="margin-top:6px;">{live_badge}</div>
<div class="summary">{summary}</div>
{right_now_html}
{axis_html}
<div class="bar">{bar_html}</div>
<div class="legend"><span style="background:#2E9E5B"></span>Screen<span style="background:#D64541"></span>Distracted<span style="background:#2F7ED8"></span>Break<span style="background:#9AA5B1"></span>Not tracked<span style="background:#E5EAF0;border:1px solid #CBD5E1"></span>App was off</div></div>
<div class="card"><div class="totals">
<div class="total"><b>{format_duration(totals["screen"])}</b><span>🟢 Looking at screen</span><span class="explain">Time looking at the screen.</span></div>
<div class="total"><b>{format_duration(totals["away"])}</b><span>🔴 Distracted (looking away)</span><span class="explain">Time looking away while not on a break.</span></div>
<div class="total"><b>{format_duration(totals["break"])}</b><span>🔵 On a break</span><span class="explain">Time on a break.</span></div>
<div class="total"><b>{day["breaks_completed"]}</b><span>Breaks finished</span><span class="explain">Breaks you finished.</span></div>
<div class="total"><b>{day["strikes"]}</b><span>Peeks during breaks</span><span class="explain">Times you looked at the screen during a break.</span></div>
</div>
<p style="color:#62748A;font-size:13px;">Longest time looking at the screen without a break: {format_duration(_longest_stretch(segments, "screen"))}. Longest single break: {format_duration(_longest_stretch(segments, "break"))}.</p></div>
<div class="card"><h2 style="font-size:16px;margin:0 0 4px;">Breaks today</h2><ul>{breaks_html}</ul></div>
{live_script}
</body></html>"""


def build_report_text(date_str, settings, totals, day):
    name = (settings.get("report_name") or "").strip() or "Student"
    return (f"ScreenBreak daily report — {name} — {date_str}\n"
            f"Looking at screen: {format_duration(totals['screen'])}\n"
            f"Distracted (looking away): {format_duration(totals['away'])}\n"
            f"On a break: {format_duration(totals['break'])}\n"
            f"Breaks finished: {day['breaks_completed']}\n"
            f"Peeks during breaks: {day['strikes']}\n"
            f"The full timeline is in the attached HTML report.")


def send_report_email(settings, date_str, html, plain):
    """Send the daily report through Gmail (SMTP, app password).
    Returns (True, '') or (False, error message)."""
    sender = (settings.get("report_sender_email") or "").strip()
    password = (settings.get("report_smtp_password") or "").replace(" ", "")
    recipient = (settings.get("report_email") or "").strip()
    name = (settings.get("report_name") or "").strip() or "Student"
    if not sender or not password or not recipient:
        return False, "Gmail address, app password and recipient are all needed."
    msg = EmailMessage()
    msg["From"] = sender
    msg["To"] = recipient
    msg["Subject"] = f"ScreenBreak daily report — {name} — {date_str}"
    msg.set_content(plain)
    msg.add_alternative(html, subtype="html")
    try:
        with smtplib.SMTP("smtp.gmail.com", 587, timeout=30) as server:
            server.ehlo()
            server.starttls()
            server.ehlo()
            server.login(sender, password)
            server.send_message(msg)
        return True, ""
    except Exception as exc:
        log_error(f"report email failed: {exc}")
        return False, str(exc)


def autostart_command():
    """Command Windows should run at sign-in: pythonw (no console
    window) + this script, starting minimized."""
    script = os.path.abspath(__file__)
    exe = sys.executable or "pythonw.exe"
    if exe.lower().endswith("python.exe"):
        candidate = exe[: -len("python.exe")] + "pythonw.exe"
        if os.path.exists(candidate):
            exe = candidate
    return f'"{exe}" "{script}" --minimized'


def get_autostart_enabled():
    """True if the Windows Run key currently starts ScreenBreak."""
    if os.name != "nt":
        return False
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                            r"Software\Microsoft\Windows\CurrentVersion\Run",
                            0, winreg.KEY_READ) as key:
            value, _ = winreg.QueryValueEx(key, "ScreenBreak")
            return bool(value)
    except Exception:
        return False


def set_autostart_enabled(enabled):
    """Turn the Windows Run-key auto-start on/off.
    Returns (True, '') or (False, error message)."""
    if os.name != "nt":
        return False, "Auto-start is only available on Windows."
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                            r"Software\Microsoft\Windows\CurrentVersion\Run",
                            0, winreg.KEY_SET_VALUE) as key:
            if enabled:
                winreg.SetValueEx(key, "ScreenBreak", 0, winreg.REG_SZ,
                                  autostart_command())
            else:
                try:
                    winreg.DeleteValue(key, "ScreenBreak")
                except FileNotFoundError:
                    pass
        return True, ""
    except Exception as exc:
        log_error(f"auto-start change failed: {exc}")
        return False, str(exc)


def main():
    # FIX (v2.4 audit): refuse to start a second copy, which used to
    # fight the first one over the camera and the data file.
    lock_status, lock_handle = try_acquire_lock()
    if lock_status == "locked":
        # v2.5: if this copy was launched automatically at sign-in,
        # the first copy is already running — just exit quietly
        # instead of popping up "already running" at every login.
        if "--minimized" in sys.argv or "--startup" in sys.argv:
            return
        notice = tk.Tk()
        notice.withdraw()
        try:
            messagebox.showinfo(
                "ScreenBreak is already running",
                "ScreenBreak is already running.\n\n"
                "Check the taskbar or the minimized window —\n"
                "only one copy can run at a time.",
                parent=notice)
        finally:
            try:
                notice.destroy()
            except tk.TclError:
                pass
        return
    saved = load_data()
    settings = saved["settings"]
    # v2.5: True means the last session ended with a proper close;
    # False means it ended while running (sleep, shutdown, crash).
    was_clean_exit = saved.get("clean_exit", True)
    state = {
        "running": True,
        # FIX 1: "settings" was missing here, which made every
        # save_data(state) raise KeyError.
        "settings": settings,
        "looking_seconds": saved["looking_seconds"],
        "break_required": saved["break_required"],
        "away_seconds": saved["away_seconds"],
        "last_tick": time.monotonic(),
        "last_wall": time.time(),
        "last_save": time.monotonic(),
        "looking": False,
        "looking_streak": 0.0,
        "glance_counted": False,
        "long_look_reset_done": False,
        "continuous_away": 0.0,
        "strikes": saved.get("strikes", 0),
        "break_looking_seconds": saved.get("break_looking_seconds", 0.0),
        "break_extension_seconds": saved.get("break_extension_seconds", 0.0),
        "penalized_looking_seconds": saved.get("penalized_looking_seconds", 0.0),
        "last_penalty_seconds": 0.0,
        "camera_visible": True,
        "camera_available": False,
        "camera_fail_count": 0,
        "last_camera_retry": 0.0,
        "cap": None,
        "popup": None,
        "break_window": None,
        "settings_window": None,
        "camera_window": None,
        "camera_image": None,
        "camera_preview_label": None,
        "lock_handle": lock_handle,
        # v2.5: False while running; set True only by close_app().
        "clean_exit": False,
        "last_report_date": saved.get("last_report_date", ""),
        "welcomed": saved.get("welcomed", False),
        "welcome_window": None,
        "last_report_check": 0.0,
        # v2.7: retry a failed report email (see _maybe_send_daily_report).
        "report_sending": False,
        "last_report_attempt": 0.0,
        # v2.6: live report + live bar timing.
        "last_live_regen": 0.0,
        "last_bar_draw": 0.0,
        # Daily timeline tracking (v2.5).
        "current_segment_state": None,
        "current_segment_start": None,
        "segments_date": day_key(),
        "today_totals": daily_totals(day_key())[0],
    }

    root = tk.Tk()
    root.title("ScreenBreak")
    # v2.5: taller again, for the progress bars, the Today summary
    # and the View report button.
    root.geometry("470x545")
    root.minsize(440, 480)
    # v2.5: start minimized when launched automatically at sign-in.
    if "--minimized" in sys.argv or "--startup" in sys.argv:
        try:
            root.iconify()
        except tk.TclError:
            pass
    root.configure(bg="#F4F7FB")

    title = tk.Label(root, text="ScreenBreak", font=("Segoe UI", 23, "bold"),
                     fg="#172B4D", bg="#F4F7FB")
    title.pack(pady=(20, 4))
    subtitle = tk.Label(root, text="Counts your screen time with the camera\nand reminds you to take a break.",
                        font=("Segoe UI", 10), fg="#62748A", bg="#F4F7FB", justify="center")
    subtitle.pack()

    status = tk.Label(root, text="Starting camera…", font=("Segoe UI", 14, "bold"),
                      fg="#B7791F", bg="#F4F7FB", wraplength=400, justify="center")
    status.pack(pady=(20, 8))
    screen_label = tk.Label(root, text="", font=("Segoe UI", 17, "bold"),
                            fg="#172B4D", bg="#F4F7FB")
    screen_label.pack(pady=3)
    # v2.5: how close you are to the screen-time limit.
    screen_progress = ttk.Progressbar(root, orient="horizontal", length=380,
                                      mode="determinate", maximum=100)
    screen_progress.pack(pady=(0, 2))
    break_label = tk.Label(root, text="", font=("Segoe UI", 12),
                           fg="#287D55", bg="#F4F7FB", wraplength=410, justify="center")
    break_label.pack(pady=3)
    # v2.5: break progress (only fills while you are on a break).
    break_progress = ttk.Progressbar(root, orient="horizontal", length=380,
                                     mode="determinate", maximum=100)
    break_progress.pack(pady=(0, 2))
    # v2.5: Today at a glance — green screen, red distracted, blue break.
    today_frame = tk.Frame(root, bg="#F4F7FB")
    today_frame.pack(pady=(4, 2))
    screen_today_label = tk.Label(today_frame, text="", font=("Segoe UI", 10, "bold"),
                                  fg="#2E9E5B", bg="#F4F7FB")
    screen_today_label.pack(side="left", padx=8)
    away_today_label = tk.Label(today_frame, text="", font=("Segoe UI", 10, "bold"),
                                fg="#D64541", bg="#F4F7FB")
    away_today_label.pack(side="left", padx=8)
    break_today_label = tk.Label(today_frame, text="", font=("Segoe UI", 10, "bold"),
                                 fg="#2F7ED8", bg="#F4F7FB")
    break_today_label.pack(side="left", padx=8)
    # v2.6: a live timeline bar — the same colours as the daily
    # report, redrawn every second. The dark line is right now.
    tk.Label(root, text="Today's timeline — live  (the dark line is now)",
             font=("Segoe UI", 10, "bold"), fg="#172B4D", bg="#F4F7FB").pack(pady=(6, 0))
    today_canvas = tk.Canvas(root, height=48, bg="#F4F7FB", highlightthickness=0)
    today_canvas.pack(fill="x", padx=20, pady=(0, 2))
    # v2.8: the live bar means nothing without a legend. Say what
    # each colour is, in words, right underneath it.
    tk.Label(root, text="Green = looking at the screen  •  Red = looking away  •  Blue = on a break  •  Grey = camera can't see you",
             font=("Segoe UI", 9), fg="#62748A", bg="#F4F7FB",
             wraplength=430, justify="center").pack(pady=(0, 2))
    hint = tk.Label(root, text="ScreenBreak runs quietly while this window is open.",
                    font=("Segoe UI", 9), fg="#62748A", bg="#F4F7FB", wraplength=380)
    hint.pack(pady=8)

    controls = tk.Frame(root, bg="#F4F7FB")
    controls.pack(pady=8)
    camera_button = tk.Button(controls, text="Show camera", width=13,
                              command=lambda: toggle_camera(), relief="flat",
                              bg="#DCE7F5", fg="#172B4D", padx=8, pady=7)
    camera_button.grid(row=0, column=0, padx=4)
    settings_button = tk.Button(controls, text="Settings", width=10,
                                command=lambda: open_settings(), relief="flat",
                                bg="#DCE7F5", fg="#172B4D", padx=8, pady=7)
    settings_button.grid(row=0, column=1, padx=4)
    # v2.5: open today's report in the browser.
    report_button = tk.Button(controls, text="Today's report", width=14,
                              command=lambda: view_today_report(), relief="flat",
                              bg="#DCE7F5", fg="#172B4D", padx=8, pady=7)
    report_button.grid(row=0, column=2, padx=4)
    # v2.8: reopen the first-run explanation any time.
    how_button = tk.Button(controls, text="How it works", width=12,
                           command=lambda: show_welcome_window(), relief="flat",
                           bg="#DCE7F5", fg="#172B4D", padx=8, pady=7)
    how_button.grid(row=0, column=3, padx=4)
    reset_button = tk.Button(root, text="Reset screen time", command=lambda: reset_with_confirmation(),
                             relief="flat", bg="#FCE8E6", fg="#A12B24",
                             padx=14, pady=7)
    reset_button.pack(pady=(2, 4))
    tk.Label(root, text="Your camera is processed on this computer. No video is saved.",
             font=("Segoe UI", 8), fg="#8291A3", bg="#F4F7FB").pack(side="bottom", pady=12)

    def open_camera():
        """Try to open the webcam. Returns a VideoCapture or None.
        FIX (v2.5 audit): VideoCapture can return None (and a bad
        backend can raise), which used to crash startup here with
        AttributeError. A camera failure must never kill the app."""
        cap = None
        try:
            cap = cv2.VideoCapture(CAMERA_INDEX, cv2.CAP_DSHOW)
        except Exception:
            cap = None
        if cap is None or not cap.isOpened():
            try:
                if cap is not None:
                    cap.release()
            except Exception:
                pass
            try:
                cap = cv2.VideoCapture(CAMERA_INDEX)
            except Exception:
                cap = None
        if cap is not None and cap.isOpened():
            cap.set(cv2.CAP_PROP_FRAME_WIDTH, FRAME_WIDTH)
            cap.set(cv2.CAP_PROP_FRAME_HEIGHT, FRAME_HEIGHT)
            state["camera_available"] = True
            state["camera_fail_count"] = 0
            return cap
        try:
            if cap is not None:
                cap.release()
        except Exception:
            pass
        state["camera_available"] = False
        return None

    def close_camera():
        cap = state.get("cap")
        state["cap"] = None
        state["camera_available"] = False
        if cap is not None:
            try:
                cap.release()
            except Exception:
                pass

    # FIX (v2.5 audit): the first camera open is also guarded, so
    # no camera failure can ever stop the app from starting.
    try:
        state["cap"] = open_camera()
    except Exception as exc:
        log_error(f"camera open failed at startup: {exc}")
        state["cap"] = None
        state["camera_available"] = False
    state["last_camera_retry"] = time.monotonic()

    try:
        face_mesh = mp.solutions.face_mesh.FaceMesh(
            max_num_faces=1, refine_landmarks=True,
            min_detection_confidence=0.55, min_tracking_confidence=0.55)
    except Exception as exc:
        print(f"ScreenBreak: could not start face detection: {exc}", file=sys.stderr)
        traceback.print_exc()
        face_mesh = None

    # When Windows was asleep or shut down during a required break, that elapsed
    # wall-clock time counts as away time. It never adds screen-looking time.
    # FIX 1: save immediately here, so last_saved advances and the same
    # gap is not added again on the next restart.
    # v2.5: closing the computer counts as looking away. If the app
    # was running when the computer slept or shut down (not a clean
    # exit), the gap since it last saved was time not looking at the
    # screen — log it as away time in the daily report.
    startup_gap = max(0.0, time.time() - saved["last_saved"])
    if startup_gap > 0 and not was_clean_exit:
        # FIX (v2.7 audit): cap at the end of the day the gap started
        # in, so a crash on Monday reopened on Wednesday does not
        # paint Tuesday as 24 hours of "away".
        gap_end = min(time.time(), _end_of_day(saved["last_saved"]))
        if gap_end > saved["last_saved"]:
            append_segment_spanning(saved["last_saved"], gap_end, "away")
        state["today_totals"], _ = daily_totals(state["segments_date"])
    if state["break_required"]:
        gap = max(0.0, time.time() - saved["last_saved"])
        if gap > 0:
            state["away_seconds"] += gap
            state["continuous_away"] = SETTLE_SECONDS
        # FIX (v2.4 audit): this used break_minutes * 60 and reset
        # only some tracking fields, leaving stale strike/glance
        # state behind. Use the seconds-based required time and
        # clear every per-break field.
        if state["away_seconds"] >= settings["break_seconds"] + state["break_extension_seconds"]:
            state["break_required"] = False
            state["away_seconds"] = 0.0
            state["looking_seconds"] = 0.0
            state["strikes"] = 0
            state["break_looking_seconds"] = 0.0
            state["break_extension_seconds"] = 0.0
            state["penalized_looking_seconds"] = 0.0
            state["last_penalty_seconds"] = 0.0
            state["looking_streak"] = 0.0
            state["glance_counted"] = False
            state["long_look_reset_done"] = False
            state["continuous_away"] = 0.0
        save_data(state)

    def target_seconds():
        # v2.4: settings are stored in seconds now.
        return int(settings["screen_limit_seconds"])

    def required_break_seconds():
        # v2.2: base break + any penalty extension from 3rd strikes.
        return int(settings["break_seconds"]) + state["break_extension_seconds"]

    def reset_break_tracking():
        """Clear all per-break strike/penalty tracking (fresh break)."""
        state["strikes"] = 0
        state["break_looking_seconds"] = 0.0
        state["break_extension_seconds"] = 0.0
        state["penalized_looking_seconds"] = 0.0
        state["last_penalty_seconds"] = 0.0
        state["looking_streak"] = 0.0
        state["glance_counted"] = False
        state["long_look_reset_done"] = False
        state["continuous_away"] = 0.0

    def apply_strike():
        """Handle one glance (1s continuous looking) during a break.
        Returns a short status message, or None. Strike 1 = warning,
        strike 2 = reset away to 0, strike 3 = reset + penalty of
        2x the looking time since the last penalty, then strikes reset.
        """
        # v2.5: count the glance in today's report.
        bump_day_counter(day_key(), "strikes", 1)
        state["strikes"] += 1
        if state["strikes"] >= STRIKES_TO_PENALTY:
            new_looking = max(0.0, state["break_looking_seconds"] - state["penalized_looking_seconds"])
            penalty = PENALTY_MULTIPLIER * new_looking
            state["break_extension_seconds"] += penalty
            state["penalized_looking_seconds"] = state["break_looking_seconds"]
            state["last_penalty_seconds"] = penalty
            state["away_seconds"] = 0.0
            state["continuous_away"] = 0.0
            state["strikes"] = 0
            save_data(state)
            return (f"You peeked 3 times, so your break is {format_time(penalty)} longer. "
                    f"Look away to start again.")
        if state["strikes"] == 2:
            state["away_seconds"] = 0.0
            state["continuous_away"] = 0.0
            save_data(state)
            return "You peeked again (2 of 3). The break started over."
        return "You peeked at the screen (1 of 3). Look away."

    def show_threshold_popup():
        try:
            if state["popup"] is not None and state["popup"].winfo_exists():
                # If the user minimized the popup itself, bring it back.
                if is_minimized(state["popup"]):
                    pop_to_front(state["popup"], 390, 205)
                return
        except tk.TclError:
            state["popup"] = None
        popup = tk.Toplevel(root)
        state["popup"] = popup
        popup.title("Time for a break")
        popup.resizable(False, False)
        popup.configure(bg="#F4F7FB")
        tk.Label(popup, text="Time for a break!", font=("Segoe UI", 20, "bold"),
                 fg="#172B4D", bg="#F4F7FB").pack(pady=(24, 8))
        # FIX (v2.4 audit): this hard-coded "minutes", so a 20-second
        # break would have read as "20 minutes". Use real durations.
        tk.Label(popup, text=f"You've reached {format_duration(target_seconds())} of screen time.\n"
                 f"Take a break for {format_duration(required_break_seconds())} or more.\n"
                 f"Look away from the screen — that is what counts toward the break.",
                 font=("Segoe UI", 11), fg="#52657A", bg="#F4F7FB").pack(pady=5)

        def begin():
            state["break_required"] = True
            state["away_seconds"] = 0.0
            reset_break_tracking()
            state["last_wall"] = time.time()
            state["last_tick"] = time.monotonic()
            try:
                popup.grab_release()
            except tk.TclError:
                pass
            try:
                popup.destroy()
            except tk.TclError:
                pass
            state["popup"] = None
            status.config(text="Time for a break!", fg="#287D55")
            hint.config(text="Look away from the screen. Peeking at the screen pauses the break, and 3 peeks make it longer.")
            save_data(state)

        tk.Button(popup, text="OK — start my break", command=begin,
                  font=("Segoe UI", 11, "bold"), relief="flat",
                  bg="#287D55", fg="white", padx=18, pady=9).pack(pady=13)
        popup.protocol("WM_DELETE_WINDOW", begin)
        # Show above everything, even if ScreenBreak is minimized.
        pop_to_front(popup, 390, 205)
        # FIX (v2.4 audit): the v2.3-Reset-Confirmation change dropped
        # grab_set, so while this popup was open you could still click
        # Settings or Reset in the main window and change the very
        # counters the popup is about. Modal again — after popping to
        # front, so the grab works even when the main window is
        # minimized. If the grab fails, the popup still shows.
        try:
            popup.grab_set()
        except tk.TclError:
            pass

    def finish_break_popup():
        # FIX 7: don't stack Break Complete popups.
        try:
            if state.get("break_window") is not None and state["break_window"].winfo_exists():
                pop_to_front(state["break_window"], 350, 170, keep_on_top_ms=8000)
                return
        except tk.TclError:
            state["break_window"] = None
        popup = tk.Toplevel(root)
        state["break_window"] = popup
        popup.title("Break complete")
        popup.resizable(False, False)
        popup.configure(bg="#F4F7FB")
        tk.Label(popup, text="Break complete!", font=("Segoe UI", 20, "bold"),
                 fg="#287D55", bg="#F4F7FB").pack(pady=(25, 8))
        tk.Label(popup, text="Your screen time starts over now.",
                 font=("Segoe UI", 10), fg="#52657A", bg="#F4F7FB").pack(pady=5)

        def done():
            # The counters were reset at the exact moment the required break
            # completed. This button only dismisses the confirmation window.
            state["break_window"] = None
            try:
                popup.destroy()
            except tk.TclError:
                pass
        tk.Button(popup, text="OK", command=done, relief="flat",
                  bg="#287D55", fg="white", padx=24, pady=8).pack(pady=12)
        popup.protocol("WM_DELETE_WINDOW", done)
        # Show above everything, even if ScreenBreak is minimized.
        pop_to_front(popup, 350, 170, keep_on_top_ms=8000)

    def reset_with_confirmation():
        """Ask before clearing the current screen-time and break progress."""
        # FIX (v2.4 audit): messagebox with parent=root is hidden
        # when the main window is minimized. Restore it first so
        # the confirmation is actually visible.
        try:
            if is_minimized(root):
                root.deiconify()
                root.lift()
                root.update_idletasks()
        except tk.TclError:
            pass
        # FIX (v2.4 audit): the message below was double-escaped
        # (\\n), so the dialog showed literal "\n\n" text instead
        # of a line break. Fixed to a real newline.
        confirmed = messagebox.askyesno(
            "Start over?",
            "This clears your screen time, break progress, peeks, "
            "and any extra break time.",
            parent=root,
            icon="warning",
        )
        if not confirmed:
            return

        # FIX (v2.4 audit): Reset left any open popups on screen. A
        # stale "Time for a break" popup could then start a break
        # right after the reset, and a stale "Break complete" popup
        # described a cycle that no longer exists. Dismiss both.
        for key in ("popup", "break_window"):
            win = state.get(key)
            if win is not None:
                try:
                    if win.winfo_exists():
                        try:
                            win.grab_release()
                        except tk.TclError:
                            pass
                        win.destroy()
                except tk.TclError:
                    pass
                state[key] = None
        state["looking_seconds"] = 0.0
        state["break_required"] = False
        state["away_seconds"] = 0.0
        # reset_break_tracking() clears strikes, looking totals,
        # penalty extension, penalized total, streak/flags and settle.
        reset_break_tracking()
        state["last_tick"] = time.monotonic()
        state["last_wall"] = time.time()
        state["last_save"] = time.monotonic()
        status.config(text="Screen time reset.", fg="#287D55")
        hint.config(text="Your screen time and break progress are reset.")
        save_data(state)
        refresh_labels()

    def complete_break():
        """Reset the next screen-time cycle immediately. Shared by the
        normal tick path and the sleep-gap path so they cannot drift."""
        # v2.5: count the finished break in today's report.
        bump_day_counter(day_key(), "breaks_completed", 1)
        state["break_required"] = False
        state["away_seconds"] = 0.0
        state["looking_seconds"] = 0.0
        reset_break_tracking()
        state["last_tick"] = time.monotonic()
        state["last_wall"] = time.time()
        status.config(text="Break done — your screen time starts over now.", fg="#287D55")
        hint.config(text="Nice break! Your screen time starts over now.")
        save_data(state)
        finish_break_popup()

    def close_camera_preview():
        win = state.get("camera_window")
        state["camera_visible"] = False
        state["camera_image"] = None
        state["camera_preview_label"] = None
        if win is not None:
            try:
                if win.winfo_exists():
                    win.destroy()
            except tk.TclError:
                pass
        state["camera_window"] = None
        camera_button.config(text="Show camera")

    def open_camera_preview():
        if state.get("camera_window") is not None:
            try:
                if state["camera_window"].winfo_exists():
                    state["camera_window"].lift()
                    return
            except tk.TclError:
                pass
        win = tk.Toplevel(root)
        state["camera_window"] = win
        state["camera_visible"] = True
        win.title("ScreenBreak Camera")
        win.geometry("680x420")
        win.configure(bg="#172B4D")
        preview = tk.Label(win, text="Starting camera preview…",
                           bg="#172B4D", fg="white",
                           font=("Segoe UI", 12))
        preview.pack(fill="both", expand=True, padx=8, pady=8)
        tk.Label(win, text="Closing this window only hides the preview. ScreenBreak keeps running.",
                 bg="#172B4D", fg="#DCE7F5",
                 font=("Segoe UI", 9)).pack(pady=(0, 8))
        state["camera_preview_label"] = preview
        win.protocol("WM_DELETE_WINDOW", close_camera_preview)
        camera_button.config(text="Hide camera")

    def toggle_camera():
        if state["camera_visible"]:
            close_camera_preview()
        elif state.get("cap") is not None and state["cap"].isOpened():
            open_camera_preview()
        else:
            status.config(text="Camera not available.", fg="#B42318")
            hint.config(text="Connect a webcam. In Windows Settings, go to Privacy & security, then Camera, and make sure apps can use it.")

    # v2.7: the preview no longer opens on its own at startup —
    # one window, not two. Open it with the button when you want to
    # see what the camera sees. Its X button closes only the preview.
    state["camera_visible"] = False
    camera_button.config(text="Show camera")

    def _generate_report(date_str, report_settings=None):
        """Build today's (or a given day's) report HTML + text and save
        the HTML file. Returns (html_path, html, plain).
        report_settings: use these settings instead of the saved ones.
        FIX (v2.7 audit): 'Send report now' used to build the report
        from the old saved settings, so a name just typed in Settings
        did not appear in the report that was sent."""
        use_settings = report_settings if report_settings is not None else settings
        open_seg = None
        if (state.get("current_segment_state") is not None
                and date_str == state["segments_date"]):
            open_seg = (state["current_segment_start"], state["current_segment_state"])
        totals, day = daily_totals(date_str, open_segment=open_seg)
        html = build_report_html(date_str, use_settings, totals, day, open_segment=open_seg)
        plain = build_report_text(date_str, use_settings, totals, day)
        try:
            REPORT_DIR.mkdir(parents=True, exist_ok=True)
            path = REPORT_DIR / f"report-{date_str}.html"
            # v2.6: atomic write (temp + replace). The browser reloads
            # this file every 30 seconds for the live view, so it must
            # never catch a half-written page.
            tmp = path.with_suffix(".tmp")
            tmp.write_text(html, encoding="utf-8")
            os.replace(tmp, path)
        except Exception as exc:
            log_error(f"could not save report {date_str}: {exc}")
            path = None
        return path, html, plain

    def view_today_report():
        """Generate today's report and open it in the browser."""
        path, _, _ = _generate_report(day_key())
        if path is not None:
            try:
                webbrowser.open(path.as_uri())
            except Exception as exc:
                log_error(f"could not open report: {exc}")
                status.config(text="Report saved, but the browser couldn't open it.", fg="#B7791F")
        else:
            status.config(text="Couldn't save today's report.", fg="#B42318")

    def show_welcome_window():
        """First-run explanation, in plain words. Shows once (until
        dismissed with 'Got it'), and any time from the 'How it
        works' button. A person forced to use ScreenBreak should
        understand it from this window alone — no one needs to
        explain it to them."""
        try:
            if state.get("welcome_window") is not None and state["welcome_window"].winfo_exists():
                win = state["welcome_window"]
                win.update_idletasks()
                pop_to_front(win, win.winfo_reqwidth(), win.winfo_reqheight())
                return
        except tk.TclError:
            state["welcome_window"] = None
        win = tk.Toplevel(root)
        state["welcome_window"] = win
        win.title("How ScreenBreak works")
        win.configure(bg="#F4F7FB")
        tk.Label(win, text="How ScreenBreak works", font=("Segoe UI", 20, "bold"),
                 fg="#172B4D", bg="#F4F7FB").pack(pady=(22, 6))
        points = [
            ("1. It watches with your camera.",
             "It only counts the time you are actually looking at the screen. Looking away pauses the count."),
            ("2. After " + format_duration(target_seconds()) + " of looking, it asks for a break.",
             "Take a break of " + format_duration(int(settings["break_seconds"])) + " or more. Look away from the screen — that is what counts."),
            ("3. Peeking pauses the break.",
             "If you look at the screen during a break, the break pauses. Peek 3 times and the break gets longer."),
            ("4. The colours.",
             "Green = looking at the screen. Red = looking away. Blue = on a break. Grey = the camera can't see you."),
            ("5. Your camera video never leaves this computer.",
             "Nothing is recorded or uploaded."),
        ]
        for title_text, body_text in points:
            tk.Label(win, text=title_text, font=("Segoe UI", 11, "bold"),
                     fg="#172B4D", bg="#F4F7FB", anchor="w").pack(fill="x", padx=24, pady=(8, 0))
            tk.Label(win, text=body_text, font=("Segoe UI", 11),
                     fg="#52657A", bg="#F4F7FB", anchor="w",
                     wraplength=410, justify="left").pack(fill="x", padx=24)
        tk.Label(win, text="You can change the times in Settings, and see today in Today's report.",
                 font=("Segoe UI", 11), fg="#52657A", bg="#F4F7FB",
                 wraplength=410, justify="left").pack(fill="x", padx=24, pady=(10, 4))
        show_every_var = tk.BooleanVar(value=False)
        tk.Checkbutton(win, text="Show this every time I open ScreenBreak",
                       variable=show_every_var, bg="#F4F7FB", fg="#172B4D",
                       font=("Segoe UI", 10), anchor="w").pack(fill="x", padx=24, pady=(2, 6))

        def _got_it():
            if not show_every_var.get():
                state["welcomed"] = True
                save_data(state)
            state["welcome_window"] = None
            try:
                win.destroy()
            except tk.TclError:
                pass

        tk.Button(win, text="Got it", command=_got_it,
                  font=("Segoe UI", 11, "bold"), relief="flat",
                  bg="#287D55", fg="white", padx=24, pady=9).pack(pady=(4, 18))
        win.protocol("WM_DELETE_WINDOW", _got_it)
        # Size to the content, then centre it on screen.
        win.update_idletasks()
        pop_to_front(win, win.winfo_reqwidth(), win.winfo_reqheight())

    def open_settings():
        # FIX 7: don't open a stack of Settings windows.
        try:
            if state.get("settings_window") is not None and state["settings_window"].winfo_exists():
                state["settings_window"].lift()
                return
        except tk.TclError:
            state["settings_window"] = None
        win = tk.Toplevel(root)
        state["settings_window"] = win
        win.title("ScreenBreak settings")
        # v2.5: tabbed Settings — Break rules, Auto-start, Daily report.
        win.geometry("480x580")
        win.minsize(460, 520)
        win.configure(bg="#F4F7FB")
        notebook = ttk.Notebook(win)
        notebook.pack(fill="both", expand=True, padx=10, pady=(10, 4))

        def _make_unit_row(parent, label_text, total_seconds, saved_unit):
            """One setting: a number Entry plus a seconds/minutes/hours
            dropdown. Changing the unit converts the number shown, so
            120 minutes becomes 2 hours, not 120 hours."""
            tk.Label(parent, text=label_text, bg="#F4F7FB",
                     fg="#52657A", anchor="w").pack(fill="x", padx=16)
            row = tk.Frame(parent, bg="#F4F7FB")
            row.pack(fill="x", padx=16, pady=(3, 10))
            value_var = tk.StringVar(value=display_value(total_seconds, saved_unit))
            tk.Entry(row, textvariable=value_var, font=("Segoe UI", 12),
                     justify="center", width=12).pack(side="left", fill="x", expand=True)
            unit_var = tk.StringVar(value=saved_unit)
            menu = tk.OptionMenu(row, unit_var, *UNIT_CHOICES)
            menu.config(font=("Segoe UI", 11), bg="#DCE7F5", fg="#172B4D",
                        relief="flat", padx=6, pady=4)
            menu.pack(side="left", padx=(8, 0))
            prev = {"unit": saved_unit}

            def _on_unit_change(*args):
                old_unit = prev["unit"]
                new_unit = unit_var.get()
                if old_unit == new_unit or new_unit not in UNIT_MULTIPLIERS:
                    prev["unit"] = new_unit
                    return
                try:
                    number = float(value_var.get())
                except ValueError:
                    prev["unit"] = new_unit
                    return
                converted = number * UNIT_MULTIPLIERS[old_unit] / UNIT_MULTIPLIERS[new_unit]
                value_var.set(display_value(converted * UNIT_MULTIPLIERS[new_unit], new_unit))
                prev["unit"] = new_unit

            unit_var.trace_add("write", _on_unit_change)
            return value_var, unit_var

        # ---- Tab 1: Break rules ----
        break_tab = tk.Frame(notebook, bg="#F4F7FB")
        notebook.add(break_tab, text="Break rules")
        tk.Label(break_tab, text="When do I need a break?", font=("Segoe UI", 14, "bold"),
                 fg="#172B4D", bg="#F4F7FB").pack(pady=(14, 6), anchor="w", padx=16)
        screen_var, screen_unit_var = _make_unit_row(
            break_tab, "How long can I look at the screen before a break?",
            int(settings["screen_limit_seconds"]),
            settings.get("screen_limit_unit", "minutes"))
        break_var, break_unit_var = _make_unit_row(
            break_tab, "How long must the break be?",
            int(settings["break_seconds"]),
            settings.get("break_unit", "minutes"))
        tk.Label(break_tab, text="Your break only counts while you look away from the screen. "
                 "Peeking at the screen pauses it, and 3 peeks make the break longer. "
                 "Changing seconds / minutes / hours keeps the same length of time — 120 minutes becomes 2 hours.",
                 bg="#F4F7FB", fg="#62748A", font=("Segoe UI", 9),
                 wraplength=420, justify="left").pack(fill="x", padx=16, pady=(0, 10))
        tk.Label(break_tab, text="Try one of these:", bg="#F4F7FB",
                 fg="#52657A", anchor="w").pack(fill="x", padx=16)
        preset_frame = tk.Frame(break_tab, bg="#F4F7FB")
        preset_frame.pack(fill="x", padx=16, pady=(4, 8))

        def _apply_preset(screen_num, screen_unit, break_num, break_unit):
            # Set the unit first, then the number: the unit change
            # converts the old number, and the number then overwrites
            # it with the preset value.
            screen_unit_var.set(screen_unit)
            screen_var.set(str(screen_num))
            break_unit_var.set(break_unit)
            break_var.set(str(break_num))

        tk.Button(preset_frame, text="Rest your eyes\n20 min / 20 sec",
                  command=lambda: _apply_preset(20, "minutes", 20, "seconds"),
                  relief="flat", bg="#DCE7F5", fg="#172B4D", padx=8, pady=6).pack(side="left", padx=(0, 6))
        tk.Button(preset_frame, text="2 hours / 10 min",
                  command=lambda: _apply_preset(2, "hours", 10, "minutes"),
                  relief="flat", bg="#DCE7F5", fg="#172B4D", padx=8, pady=6).pack(side="left", padx=6)
        tk.Button(preset_frame, text="50 min / 10 min",
                  command=lambda: _apply_preset(50, "minutes", 10, "minutes"),
                  relief="flat", bg="#DCE7F5", fg="#172B4D", padx=8, pady=6).pack(side="left", padx=6)

        # ---- Tab 2: Auto-start ----
        start_tab = tk.Frame(notebook, bg="#F4F7FB")
        notebook.add(start_tab, text="Auto-start")
        tk.Label(start_tab, text="Start automatically", font=("Segoe UI", 14, "bold"),
                 fg="#172B4D", bg="#F4F7FB").pack(pady=(14, 6), anchor="w", padx=16)
        autostart_var = tk.BooleanVar(value=get_autostart_enabled())
        autostart_check = tk.Checkbutton(
            start_tab, text="Start ScreenBreak when I sign in to Windows",
            variable=autostart_var, bg="#F4F7FB", fg="#172B4D",
            font=("Segoe UI", 11), anchor="w", wraplength=420, justify="left")
        autostart_check.pack(fill="x", padx=16, pady=(0, 8))
        autostart_status = tk.Label(
            start_tab,
            text="Auto-start is currently ON." if get_autostart_enabled() else "Auto-start is currently OFF.",
            bg="#F4F7FB", fg="#62748A", font=("Segoe UI", 10), anchor="w")
        autostart_status.pack(fill="x", padx=16, pady=(0, 8))
        if os.name != "nt":
            autostart_check.config(state="disabled")
            tk.Label(start_tab, text="Auto-start is only available on Windows.",
                     bg="#F4F7FB", fg="#B42318", font=("Segoe UI", 10),
                     anchor="w").pack(fill="x", padx=16)
        tk.Label(start_tab, text="It opens in the background (minimized). The camera keeps running "
                 "and break popups still appear. Turn it off here any time.",
                 bg="#F4F7FB", fg="#62748A", font=("Segoe UI", 9),
                 wraplength=420, justify="left").pack(fill="x", padx=16)

        # ---- Tab 3: Daily report ----
        # v2.7: one checkbox instead of two. The old "Send me a daily
        # report" + "Email the report" pair was confusing: the daily
        # save only ran when the first was on, but "Send report now"
        # emailed even when it was off. Now the report is always
        # saved on this computer, and this one checkbox only controls
        # whether it is also emailed.
        report_tab = tk.Frame(notebook, bg="#F4F7FB")
        notebook.add(report_tab, text="Daily report")
        tk.Label(report_tab, text="Daily report", font=("Segoe UI", 14, "bold"),
                 fg="#172B4D", bg="#F4F7FB").pack(pady=(14, 6), anchor="w", padx=16)
        tk.Label(report_tab, text="A report is always saved on this computer — open it any time with Today's report.",
                 bg="#F4F7FB", fg="#62748A", font=("Segoe UI", 9),
                 wraplength=420, justify="left").pack(fill="x", padx=16, pady=(0, 6))
        tk.Label(report_tab, text="Name for the report (optional)", bg="#F4F7FB",
                 fg="#52657A", anchor="w").pack(fill="x", padx=16, pady=(8, 2))
        name_var = tk.StringVar(value=settings.get("report_name", ""))
        tk.Entry(report_tab, textvariable=name_var, font=("Segoe UI", 12)).pack(fill="x", padx=16, pady=(0, 6))
        email_enabled_var = tk.BooleanVar(value=bool(settings.get("report_email_enabled", False)))
        tk.Checkbutton(report_tab, text="Email me the daily report",
                       variable=email_enabled_var, bg="#F4F7FB", fg="#172B4D",
                       font=("Segoe UI", 11), anchor="w").pack(fill="x", padx=16)
        tk.Label(report_tab, text="Send the report to (email)", bg="#F4F7FB",
                 fg="#52657A", anchor="w").pack(fill="x", padx=16, pady=(8, 2))
        email_var = tk.StringVar(value=settings.get("report_email", ""))
        email_entry = tk.Entry(report_tab, textvariable=email_var, font=("Segoe UI", 12))
        email_entry.pack(fill="x", padx=16, pady=(0, 6))
        tk.Label(report_tab, text="Time to send it (e.g. 6pm)", bg="#F4F7FB",
                 fg="#52657A", anchor="w").pack(fill="x", padx=16, pady=(0, 2))
        time_var = tk.StringVar(value=settings.get("report_time", "18:00"))
        time_entry = tk.Entry(report_tab, textvariable=time_var, font=("Segoe UI", 12))
        time_entry.pack(fill="x", padx=16, pady=(0, 8))
        tk.Label(report_tab, text="Your Gmail address", bg="#F4F7FB",
                 fg="#52657A", anchor="w").pack(fill="x", padx=16, pady=(8, 2))
        sender_var = tk.StringVar(value=settings.get("report_sender_email", ""))
        sender_entry = tk.Entry(report_tab, textvariable=sender_var, font=("Segoe UI", 12))
        sender_entry.pack(fill="x", padx=16, pady=(0, 6))
        tk.Label(report_tab, text="Gmail app password", bg="#F4F7FB",
                 fg="#52657A", anchor="w").pack(fill="x", padx=16, pady=(0, 2))
        pw_frame = tk.Frame(report_tab, bg="#F4F7FB")
        pw_frame.pack(fill="x", padx=16, pady=(0, 4))
        password_var = tk.StringVar(value=settings.get("report_smtp_password", ""))
        password_entry = tk.Entry(pw_frame, textvariable=password_var, font=("Segoe UI", 12), show="*")
        password_entry.pack(side="left", fill="x", expand=True)
        show_pw_var = tk.BooleanVar(value=False)

        def _toggle_password():
            password_entry.config(show="" if show_pw_var.get() else "*")

        show_pw_check = tk.Checkbutton(pw_frame, text="Show", variable=show_pw_var,
                       command=_toggle_password, bg="#F4F7FB", fg="#172B4D",
                       font=("Segoe UI", 10))
        show_pw_check.pack(side="left", padx=(6, 0))
        tk.Label(report_tab, text="An app password is not your normal Gmail password. In your Google Account, go to Security, then 2-Step Verification, then App passwords. Turn on 2-Step Verification first if it is off — app passwords only work with it on. It is stored only on this computer.",
                 bg="#F4F7FB", fg="#62748A", font=("Segoe UI", 9),
                 wraplength=420, justify="left").pack(fill="x", padx=16, pady=(0, 8))
        report_btn_frame = tk.Frame(report_tab, bg="#F4F7FB")
        report_btn_frame.pack(fill="x", padx=16, pady=(0, 6))

        # v2.7: the email fields are only editable when email is on,
        # so it is obvious what the checkbox controls.
        def _toggle_email_fields(*args):
            entry_state = "normal" if email_enabled_var.get() else "disabled"
            for widget in (email_entry, time_entry, sender_entry, password_entry, show_pw_check):
                try:
                    widget.config(state=entry_state)
                except tk.TclError:
                    pass

        email_enabled_var.trace_add("write", _toggle_email_fields)
        _toggle_email_fields()

        def _report_settings_from_entries():
            """Settings as typed in this window (for Send now / View)."""
            trial = dict(settings)
            trial["report_name"] = name_var.get().strip()
            trial["report_email"] = email_var.get().strip()
            trial["report_time"] = time_var.get().strip()
            trial["report_email_enabled"] = bool(email_enabled_var.get())
            trial["report_sender_email"] = sender_var.get().strip()
            trial["report_smtp_password"] = password_var.get()
            # FIX (v2.7 audit): an email address is only needed when
            # the report will actually be emailed. With email off,
            # "Send report now" just saves and opens the report, and
            # the old code wrongly refused it when the email field
            # was empty.
            if trial["report_email_enabled"]:
                if not is_valid_email(trial["report_email"]):
                    return None, "Enter a valid email to send the report to."
                if not is_valid_email(trial["report_sender_email"]):
                    return None, "Enter a valid Gmail address to send from."
                if not trial["report_smtp_password"]:
                    return None, "Enter your Gmail app password to send the report."
            return trial, None

        def _send_report_now():
            trial, err = _report_settings_from_entries()
            if err:
                msg.config(text=err, fg="#B42318")
                return
            today = day_key()
            # FIX (v2.7 audit): build the report from the settings
            # just typed, so the name shows up in the report sent.
            path, html, plain = _generate_report(today, trial)
            if trial["report_email_enabled"]:
                msg.config(text="Sending report…", fg="#62748A")

                def _bg():
                    ok, send_err = send_report_email(trial, today, html, plain)

                    def _done():
                        try:
                            if ok:
                                msg.config(text=f"Report sent to {trial['report_email']}.", fg="#287D55")
                            else:
                                msg.config(text=f"Could not send it: {send_err} The report was saved as a file instead.", fg="#B42318")
                        except tk.TclError:
                            pass
                    try:
                        win.after(0, _done)
                    except tk.TclError:
                        pass

                threading.Thread(target=_bg, daemon=True).start()
            else:
                msg.config(text="Report saved — opening it now.", fg="#287D55")
                if path is not None:
                    try:
                        webbrowser.open(path.as_uri())
                    except Exception:
                        pass

        tk.Button(report_btn_frame, text="Send report now",
                  command=_send_report_now, relief="flat",
                  bg="#287D55", fg="white", padx=12, pady=6).pack(side="left", padx=(0, 6))
        tk.Button(report_btn_frame, text="View today's report",
                  command=lambda: view_today_report(), relief="flat",
                  bg="#DCE7F5", fg="#172B4D", padx=12, pady=6).pack(side="left", padx=6)

        msg = tk.Label(win, text="", font=("Segoe UI", 9), fg="#B42318",
                       bg="#F4F7FB", wraplength=430, justify="center")
        msg.pack(fill="x", padx=16)

        def _clear_settings_window():
            state["settings_window"] = None

        def save_settings():
            try:
                screen_number = float(screen_var.get())
                break_number = float(break_var.get())
                new_screen = int(round(screen_number * UNIT_MULTIPLIERS[screen_unit_var.get()]))
                new_break = int(round(break_number * UNIT_MULTIPLIERS[break_unit_var.get()]))
                if not (SCREEN_LIMIT_MIN_SECONDS <= new_screen <= SCREEN_LIMIT_MAX_SECONDS
                        and BREAK_MIN_SECONDS <= new_break <= BREAK_MAX_SECONDS):
                    raise ValueError
            except (ValueError, KeyError, TypeError, OverflowError):
                msg.config(text="Enter a number: screen 1 second – 24 hours, break 1 second – 4 hours.", fg="#B42318")
                return
            # Daily report validation (only when email is on).
            if email_enabled_var.get():
                if not is_valid_email(email_var.get()):
                    msg.config(text="Enter a valid email to send the daily report to.", fg="#B42318")
                    return
                if parse_report_time(time_var.get()) is None:
                    msg.config(text="Enter a report time like 18:00 or 6pm.", fg="#B42318")
                    return
                if not is_valid_email(sender_var.get()):
                    msg.config(text="Enter a valid Gmail address to send the report from.", fg="#B42318")
                    return
                if not password_var.get():
                    msg.config(text="Enter your Gmail app password to email the report.", fg="#B42318")
                    return
            # Auto-start first: if it fails, nothing is saved, so the
            # window stays open and the error is visible.
            if os.name == "nt":
                ok, err = set_autostart_enabled(bool(autostart_var.get()))
                if not ok:
                    msg.config(text=f"Could not change auto-start: {err}", fg="#B42318")
                    return
            settings["screen_limit_seconds"] = new_screen
            settings["break_seconds"] = new_break
            settings["screen_limit_unit"] = screen_unit_var.get()
            settings["break_unit"] = break_unit_var.get()
            settings["screen_limit_minutes"] = new_screen / 60
            settings["break_minutes"] = new_break / 60
            # v2.7: one checkbox now. report_enabled is kept in the
            # file only so old versions can still read it; it mirrors
            # the email switch.
            settings["report_enabled"] = bool(email_enabled_var.get())
            settings["report_name"] = name_var.get().strip()
            settings["report_email"] = email_var.get().strip()
            settings["report_time"] = time_var.get().strip()
            settings["report_email_enabled"] = bool(email_enabled_var.get())
            settings["report_sender_email"] = sender_var.get().strip()
            settings["report_smtp_password"] = password_var.get()
            save_data(state)
            state["settings_window"] = None
            try:
                win.destroy()
            except tk.TclError:
                pass
            refresh_labels()
        # v2.8: a Cancel button, so it is obvious that closing
        # without saving changes nothing.
        save_frame = tk.Frame(win, bg="#F4F7FB")
        save_frame.pack(pady=(6, 10))
        tk.Button(save_frame, text="Save settings", command=save_settings, relief="flat",
                  bg="#287D55", fg="white", padx=18, pady=8).pack(side="left", padx=(0, 6))
        tk.Button(save_frame, text="Cancel", command=lambda: (_clear_settings_window(), win.destroy()),
                  relief="flat", bg="#DCE7F5", fg="#172B4D", padx=18, pady=8).pack(side="left", padx=6)
        win.protocol("WM_DELETE_WINDOW", lambda: (_clear_settings_window(), win.destroy()))

    def refresh_labels():
        screen_label.config(text=f"Screen time: {format_time(state['looking_seconds'])} of {format_time(target_seconds())}")
        # v2.5: progress bars.
        try:
            screen_progress["value"] = min(100.0, state["looking_seconds"] / max(1, target_seconds()) * 100.0)
        except tk.TclError:
            pass
        if state["break_required"]:
            req = required_break_seconds()
            extra = f" (+{format_time(state['break_extension_seconds'])} penalty)" if state["break_extension_seconds"] > 0 else ""
            break_label.config(text=f"Break: {format_time(state['away_seconds'])} of {format_time(req)}{extra} • Peeks {state['strikes']} of 3")
            try:
                break_progress["value"] = min(100.0, state["away_seconds"] / max(1.0, req) * 100.0)
            except tk.TclError:
                pass
        else:
            left = max(0, target_seconds() - state["looking_seconds"])
            break_label.config(text=f"Break in: {format_time(left)}")
            try:
                break_progress["value"] = 0
            except tk.TclError:
                pass
        # v2.5: Today at a glance, including the segment in progress.
        totals = dict(state["today_totals"])
        if state.get("current_segment_state") in totals and state.get("current_segment_start") is not None:
            totals[state["current_segment_state"]] += max(0.0, time.time() - state["current_segment_start"])
        try:
            screen_today_label.config(text=f"● Screen {format_time(totals['screen'])}")
            away_today_label.config(text=f"● Looking away {format_time(totals['away'])}")
            break_today_label.config(text=f"● Break {format_time(totals['break'])}")
        except tk.TclError:
            pass

    def _close_segment(end_time):
        """Close the segment in progress at end_time (midnight splits
        it across days). Does nothing when no segment is open."""
        start = state.get("current_segment_start")
        seg_state = state.get("current_segment_state")
        if start is None or seg_state is None:
            return
        state["current_segment_state"] = None
        state["current_segment_start"] = None
        if end_time <= start:
            return
        append_segment_spanning(start, end_time, seg_state)

    def _start_segment(seg_state, start_time):
        state["current_segment_state"] = seg_state
        state["current_segment_start"] = start_time

    def _current_display_state():
        """Green screen / red distracted / blue break / grey unknown."""
        if face_mesh is None or not state.get("camera_available", False):
            return "unknown"
        if state["break_required"]:
            return "break"
        if state.get("looking"):
            return "screen"
        return "away"

    def _track_segment():
        """Keep one open segment for the current state; close it and
        start a new one whenever the state changes or the day rolls
        over at midnight."""
        now = time.time()
        today = day_key(now)
        if today != state["segments_date"]:
            # Midnight: close the old day's segment at midnight, then
            # start fresh for the new day.
            midnight = datetime.strptime(today, "%Y-%m-%d").timestamp()
            _close_segment(midnight)
            state["segments_date"] = today
            state["today_totals"], _ = daily_totals(today)
        display = _current_display_state()
        if display != state.get("current_segment_state"):
            if state.get("current_segment_state") is not None:
                prev_start = state["current_segment_start"]
                prev_state = state["current_segment_state"]
                _close_segment(now)
                if prev_start is not None:
                    state["today_totals"][prev_state] = state["today_totals"].get(prev_state, 0.0) + max(0.0, now - prev_start)
            _start_segment(display, now)

    def _record_sleep_gap(now_wall, sleep_gap):
        """A sleep gap is time the computer was closed: close whatever
        segment was open when it went to sleep, log the gap as away,
        and leave no segment open (tracking restarts fresh).
        FIX (v2.7 audit): the gap is capped at the end of the day it
        started in. A computer asleep over the weekend used to log
        "away" for every day in between, making those days look like
        24 hours of red; days with no activity now stay blank."""
        sleep_start = now_wall - sleep_gap
        gap_end = min(now_wall, _end_of_day(sleep_start))
        if gap_end <= sleep_start:
            return
        _close_segment(sleep_start)
        append_segment_spanning(sleep_start, gap_end, "away")
        state["today_totals"], _ = daily_totals(state["segments_date"])

    def _maybe_send_daily_report():
        """Once a second at most: when the report time comes, save
        today's report file. If email is on, email it too.
        FIX (v2.7 audit): the old code marked the report sent BEFORE
        sending it, so a failed send never retried. Now it is marked
        sent only when the email actually goes through, and a failed
        send is tried again in 5 minutes (at most one attempt every
        5 minutes, so a down mail server is not hammered)."""
        now_mono = time.monotonic()
        if now_mono - state["last_report_check"] < 1.0:
            return
        state["last_report_check"] = now_mono
        if state.get("report_sending"):
            return
        parsed = parse_report_time(settings.get("report_time", ""))
        if parsed is None:
            return
        today = day_key()
        if state.get("last_report_date") == today:
            return
        hour, minute = parsed
        now_local = datetime.now()
        if (now_local.hour, now_local.minute) < (hour, minute):
            return
        if now_mono - state.get("last_report_attempt", 0.0) < 300.0:
            return
        path, html, plain = _generate_report(today)
        if not settings.get("report_email_enabled"):
            # No email: the saved file IS the report for today.
            state["last_report_date"] = today
            save_data(state)
            status.config(text="Today's report is ready.", fg="#287D55")
            return
        # FIX (v2.5 audit): sending email can take up to 30s on a bad
        # connection. Doing it here would freeze the whole window, so
        # it runs in a background thread and only the status update
        # comes back to the main thread.
        state["report_sending"] = True
        state["last_report_attempt"] = now_mono
        email_settings = dict(settings)

        def _send_in_background():
            ok, err = send_report_email(email_settings, today, html, plain)
            if not ok:
                log_error(f"daily report email failed: {err}")

            def _done():
                state["report_sending"] = False
                try:
                    if ok:
                        state["last_report_date"] = today
                        save_data(state)
                        status.config(text=f"Daily report sent to {email_settings.get('report_email', '')}.", fg="#287D55")
                    else:
                        status.config(text="Couldn't email the report — it's saved on this computer instead. Will try again in 5 minutes.", fg="#B42318")
                except tk.TclError:
                    pass
            try:
                root.after(0, _done)
            except tk.TclError:
                state["report_sending"] = False

        threading.Thread(target=_send_in_background, daemon=True).start()

    def _maybe_regenerate_live_report():
        """Keep today's report file fresh for the live browser view.
        If the file exists (the user opened it, or it was emailed),
        rewrite it every 30 seconds so the page's auto-reload picks
        up the new colours. Cheap, and harmless when nobody has the
        page open."""
        now_mono = time.monotonic()
        if now_mono - state["last_live_regen"] < 30.0:
            return
        state["last_live_regen"] = now_mono
        today = day_key()
        path = REPORT_DIR / f"report-{today}.html"
        if path.exists():
            try:
                _generate_report(today)
            except Exception:
                traceback.print_exc()

    def _draw_today_bar(force=False):
        """Redraw the live timeline bar in the main window (at most
        once a second, or immediately when forced, e.g. on resize)."""
        now_mono = time.monotonic()
        if not force and now_mono - state["last_bar_draw"] < 1.0:
            return
        state["last_bar_draw"] = now_mono
        try:
            width = today_canvas.winfo_width()
            if width <= 1:
                return
            today = state["segments_date"]
            day = load_day(today)
            segments = list(day["segments"])
            if state.get("current_segment_state") is not None:
                segments.append({"start": state["current_segment_start"],
                                 "end": time.time(),
                                 "state": state["current_segment_state"]})
            segments.sort(key=lambda s: s["start"])
            now = time.time()
            rs, re_, rsec = _timeline_range(today, segments, now)
            blocks = _smooth_timeline(segments, rs, re_)
            today_canvas.delete("all")
            # Hour ticks + labels (every hour on a short day, every
            # 2 hours on a long one so they cannot overlap).
            span_hours = (re_ - rs) / 3600.0
            label_every = 1 if span_hours <= 6 else 2
            hour = rs
            while hour <= re_ + 0.5:
                x = (hour - rs) / rsec * width
                if 0.0 <= x <= width:
                    today_canvas.create_line(x, 16, x, 20, fill="#172B4D", width=2)
                    hi = int(round((hour - rs) / 3600.0))
                    if hi % label_every == 0:
                        label = _hour_label(hour, long_form=False)
                        if x <= 2:
                            today_canvas.create_text(2, 8, text=label,
                                                     font=("Segoe UI", 8), fill="#172B4D", anchor="w")
                        elif x >= width - 2:
                            today_canvas.create_text(width - 2, 8, text=label,
                                                     font=("Segoe UI", 8), fill="#172B4D", anchor="e")
                        else:
                            today_canvas.create_text(x, 8, text=label,
                                                     font=("Segoe UI", 8), fill="#172B4D")
                hour += 3600
            for b in blocks:
                x0 = max(0.0, (b["start"] - rs) / rsec * width)
                x1 = min(float(width), (b["end"] - rs) / rsec * width)
                if x1 <= x0:
                    continue
                colour = STATE_COLORS.get(b["state"], "#E5EAF0")
                today_canvas.create_rectangle(x0, 20, x1, 46, fill=colour, outline="")
            # "Now" marker: a dark line at the current time.
            nx = (now - rs) / rsec * width
            if 0.0 <= nx <= width:
                today_canvas.create_line(nx, 16, nx, 48, fill="#172B4D", width=2)
        except Exception:
            traceback.print_exc()

    def _update_tick():
        now_mono = time.monotonic()
        now_wall = time.time()
        # FIX (v2.7 audit): sleep is detected from the UNCLAMPED
        # monotonic delta. A UI freeze advances monotonic time (only
        # the event loop is stuck), while real sleep freezes it. The
        # old code used the elapsed time clamped to 1s, so any freeze
        # over 5s was misread as sleep and logged fake "away" time.
        raw_elapsed = max(0.0, now_mono - state["last_tick"])
        elapsed = min(raw_elapsed, 1.0)
        wall_elapsed = max(0.0, now_wall - state["last_wall"])
        state["last_tick"] = now_mono
        state["last_wall"] = now_wall

        # FIX 5: sleep / suspension while the app is running.
        # If the wall clock advanced a lot but monotonic time barely
        # did, the computer was asleep. That time counts as away
        # time during a required break, even with no camera evidence
        # — the user could not have been looking while asleep.
        # It never adds screen-looking time.
        sleep_gap = 0.0
        if wall_elapsed > SLEEP_GAP_MIN_SECONDS and (wall_elapsed - raw_elapsed) > SLEEP_GAP_MIN_SECONDS:
            sleep_gap = wall_elapsed - raw_elapsed
            # v2.5: the computer was closed/asleep — that whole gap
            # was time not looking at the screen. Log it as away.
            _record_sleep_gap(now_wall, sleep_gap)
            if state["break_required"]:
                state["away_seconds"] += sleep_gap
                state["continuous_away"] = SETTLE_SECONDS
                if state["away_seconds"] >= required_break_seconds():
                    complete_break()
                    refresh_labels()
                    return
            # Don't double-count this tick's normal elapsed time:
            # the gap already covers the whole suspended interval.
            elapsed = 0.0

        # FIX (v2.5 audit): if face detection failed to start, say
        # so before trying the camera. Retrying the camera is
        # pointless when the model itself never loaded, and the old
        # order hid this behind "CAMERA NOT AVAILABLE" whenever the
        # camera was also missing. Pause both timers instead of
        # counting a break with no evidence.
        if face_mesh is None:
            state["camera_available"] = False
            state["looking"] = False
            status.config(text="Face detection couldn't start — please close and reopen ScreenBreak.", fg="#B42318")
            hint.config(text="Face detection could not start. Close and reopen ScreenBreak.")
            refresh_labels()
            if now_mono - state["last_save"] >= SAVE_EVERY_SECONDS:
                save_data(state)
                state["last_save"] = now_mono
            return

        # FIX 4: retry the camera every CAMERA_RETRY_SECONDS if it is
        # missing or has failed. Previously it was opened once at
        # startup and never tried again.
        cap = state.get("cap")
        if cap is None or not cap.isOpened():
            if now_mono - state["last_camera_retry"] >= CAMERA_RETRY_SECONDS:
                state["last_camera_retry"] = now_mono
                state["cap"] = open_camera()
                cap = state.get("cap")
            if cap is None or not cap.isOpened():
                state["camera_available"] = False
                state["looking"] = False
                state["looking_streak"] = 0.0
                state["glance_counted"] = False
                state["long_look_reset_done"] = False
                status.config(text="Camera not available — trying again…", fg="#B42318")
                hint.config(text="Connect a webcam. In Windows Settings, go to Privacy & security, then Camera, and make sure apps can use it.")
                refresh_labels()
                if now_mono - state["last_save"] >= SAVE_EVERY_SECONDS:
                    save_data(state)
                    state["last_save"] = now_mono
                return

        looking = False
        ok, frame = cap.read()
        # FIX (v2.4 audit): a read can succeed with an empty frame
        # (size 0), which used to crash frame.shape below.
        if not ok or frame is None or getattr(frame, "size", 1) == 0:
            state["camera_fail_count"] += 1
            state["camera_available"] = False
            state["looking"] = False
            # FIX 4: after repeated failures, drop the handle so the
            # retry logic above reopens it instead of spinning forever.
            if state["camera_fail_count"] >= CAMERA_MAX_CONSECUTIVE_FAILURES:
                close_camera()
                state["last_camera_retry"] = now_mono
            status.config(text="Camera not available — trying again…", fg="#B42318")
            refresh_labels()
            return
        state["camera_fail_count"] = 0

        frame = cv2.flip(frame, 1)
        h, w = frame.shape[:2]
        if face_mesh is not None:
            try:
                results = face_mesh.process(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB))
                if results.multi_face_landmarks:
                    looking, gx, gy, hx = classify(results.multi_face_landmarks[0], w, h)
            except Exception as exc:
                # A single bad frame must not kill the timer (see update()).
                print(f"ScreenBreak: face detection error: {exc}", file=sys.stderr)
                looking = False
        # Render the preview in its own Tk window. Its X button destroys
        # only this preview; the main ScreenBreak status window remains open.
        if state["camera_visible"]:
            cam_win = state.get("camera_window")
            try:
                if cam_win is not None and cam_win.winfo_exists():
                    preview = state.get("camera_preview_label")
                    if preview is not None and preview.winfo_exists():
                        # Convert OpenCV's BGR frame to RGB, then use Pillow's
                        # ImageTk bridge. Tkinter PhotoImage does not reliably
                        # decode JPEG data, which caused the preview to disappear.
                        rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                        pil_image = Image.fromarray(rgb)
                        # FIX 7: was (900, 650) in a 680x420 window.
                        pil_image.thumbnail((640, 360))
                        photo = ImageTk.PhotoImage(pil_image)
                        preview.configure(image=photo, text="")
                        state["camera_image"] = photo
            except Exception as exc:
                print(f"ScreenBreak: preview error: {exc}", file=sys.stderr)
                try:
                    close_camera_preview()
                except Exception:
                    pass
        # (v2.5: face_mesh is None is handled at the top of the tick,
        # before the camera retry, so it can never be None here.)
        state["camera_available"] = True

        state["looking"] = looking
        if state["break_required"]:
            if looking:
                # v2.2: track total looking during this break (for the
                # 2x penalty) and the current continuous streak.
                state["break_looking_seconds"] += elapsed
                state["looking_streak"] += elapsed
                state["continuous_away"] = 0.0
                # One glance = 1s continuous looking. Count it once
                # per looking episode, not once per frame.
                strike_msg = None
                if not state["glance_counted"] and state["looking_streak"] >= GLANCE_SECONDS:
                    state["glance_counted"] = True
                    strike_msg = apply_strike()
                # Staring 3s straight still resets immediately, as in
                # v2.1. Only fire once per episode.
                long_reset = False
                if state["looking_streak"] >= BREAK_RESET_LOOKING_SECONDS and not state["long_look_reset_done"]:
                    state["long_look_reset_done"] = True
                    state["away_seconds"] = 0.0
                    state["continuous_away"] = 0.0
                    long_reset = True
                # v2.7: plain words, no shouting capitals, no jargon.
                # A 3rd peek resets strikes to 0, so strikes == 0 here
                # means the penalty was just applied.
                if strike_msg is not None and state["strikes"] == 0:
                    status.config(text=strike_msg, fg="#B42318")
                    hint.config(text=f"You looked at the screen for {format_time(state['break_looking_seconds'])} in total during this break, so {format_time(state['last_penalty_seconds'])} was added. Look away to start again.")
                elif long_reset:
                    status.config(text="You looked at the screen for 3 seconds, so the break started over.", fg="#B7791F")
                elif strike_msg is not None:
                    status.config(text=strike_msg, fg="#B7791F")
                else:
                    status.config(text="Break paused — you're looking at the screen.", fg="#B7791F")
            else:
                state["looking_streak"] = 0.0
                state["glance_counted"] = False
                state["long_look_reset_done"] = False
                if state["camera_available"]:
                    # v2.2 settle: after any glance, away time only
                    # counts after 10s away in a row. Spamming
                    # look 2s / away 5s / look 2s can never reach 10s
                    # in a row, so it earns no break progress at all.
                    prev_away = state["continuous_away"]
                    state["continuous_away"] += elapsed
                    countable = (max(0.0, state["continuous_away"] - SETTLE_SECONDS)
                                 - max(0.0, prev_away - SETTLE_SECONDS))
                    if countable > 0:
                        state["away_seconds"] += countable
                        status.config(text="On a break — keep looking away.", fg="#287D55")
                    else:
                        status.config(text="Break paused — keep looking away and the timer starts again in a few seconds.", fg="#B7791F")
                else:
                    status.config(text="Camera not available.", fg="#B42318")
            if state["away_seconds"] >= required_break_seconds():
                # Complete the break and reset the next screen-time cycle
                # immediately; do not wait for the user to dismiss the popup.
                complete_break()
        else:
            state["looking_streak"] = 0.0
            state["glance_counted"] = False
            state["long_look_reset_done"] = False
            state["continuous_away"] = 0.0
            if looking:
                state["looking_seconds"] += elapsed
                status.config(text="Looking at the screen — counting your screen time.", fg="#287D55")
            elif state["camera_available"]:
                status.config(text="Looking away — screen time paused.", fg="#B7791F")
            else:
                status.config(text="Camera not available.", fg="#B42318")
            if state["looking_seconds"] >= target_seconds():
                state["looking_seconds"] = target_seconds()
                show_threshold_popup()

        refresh_labels()
        # FIX 7: was >= 1 (every second). Use the intended 10s interval.
        if now_mono - state["last_save"] >= SAVE_EVERY_SECONDS:
            save_data(state)
            state["last_save"] = now_mono

    def update():
        # FIX 2: always schedule the next tick, even if this tick
        # throws. Previously the root.after() was at the end of the
        # tick, so one exception stopped the timer forever while the
        # window still looked alive.
        if not state["running"]:
            return
        try:
            _update_tick()
            # v2.5: timeline tracking + daily-report check. Errors
            # here are caught below, so they can never stop the timer.
            _track_segment()
            _maybe_send_daily_report()
            # v2.6: keep the report file and the live bar current.
            _maybe_regenerate_live_report()
            _draw_today_bar()
        except Exception:
            traceback.print_exc()
        finally:
            if state["running"]:
                try:
                    root.after(40, update)
                except tk.TclError:
                    pass

    def close_app():
        if not state["running"]:
            return
        state["running"] = False
        # v2.5: finish today's timeline and mark a clean exit, so the
        # next launch knows the gap was just "app was closed".
        try:
            _close_segment(time.time())
        except Exception:
            traceback.print_exc()
        state["clean_exit"] = True
        save_data(state)
        try:
            close_camera()
            if face_mesh is not None:
                face_mesh.close()
        except Exception:
            pass
        try:
            release_lock(state.get("lock_handle"))
        except Exception:
            pass
        try:
            root.destroy()
        except tk.TclError:
            pass

    root.protocol("WM_DELETE_WINDOW", close_app)
    if state.get("cap") is None or not state["cap"].isOpened():
        status.config(text="Camera not available.", fg="#B42318")
        hint.config(text="Connect a webcam. In Windows Settings, go to Privacy & security, then Camera, and make sure apps can use it.")
    root.after(100, update)
    # v2.8: first run — explain the app in plain words, so a person
    # forced to use it understands it with no one telling them.
    if not state.get("welcomed", False):
        show_welcome_window()
    # v2.6: redraw the live bar when the window is resized. Bound
    # here (not at widget creation) because _draw_today_bar is only
    # defined further up in main().
    today_canvas.bind("<Configure>", lambda e: _draw_today_bar(force=True))
    root.mainloop()


if __name__ == "__main__":
    main()
