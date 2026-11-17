import cv2
import mediapipe as mp
import math
import json
import os
import sys
import time
import traceback
import tkinter as tk
from tkinter import messagebox
from PIL import Image, ImageTk
from pathlib import Path

# ScreenBreak v2.2 (2026-11-16): local webcam gaze estimate +
# accumulated screen-looking time.
# Webcam frames are processed locally and are never recorded or uploaded.
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
    return eyes_centered and head_centered, x, y, nose_x


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
    seconds = max(0, int(seconds))
    hours, remainder = divmod(seconds, 3600)
    minutes, secs = divmod(remainder, 60)
    if hours:
        return f"{hours} hr {minutes:02d} min"
    return f"{minutes} min {secs:02d} sec"


APP_DIR = Path(os.environ.get("LOCALAPPDATA", str(Path.home()))) / "ScreenBreak"
APP_DIR.mkdir(parents=True, exist_ok=True)
# Single source of truth for the data file. The earlier top-level
# DATA_FILE = Path(__file__).with_name(...) was overwritten here and
# only confused things, so it was removed.
DATA_FILE = APP_DIR / "screenbreak_data.json"
DEFAULTS = {"screen_limit_minutes": 120, "break_minutes": 10}


def _safe_int(value, default):
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def load_data():
    try:
        raw = DATA_FILE.read_text(encoding="utf-8")
    except FileNotFoundError:
        return {
            "looking_seconds": 0.0, "break_required": False, "away_seconds": 0.0,
            "last_saved": time.time(), "settings": DEFAULTS.copy(),
            "break_extension_seconds": 0.0, "break_looking_seconds": 0.0,
            "strikes": 0, "penalized_looking_seconds": 0.0,
        }
    except Exception as exc:
        print(f"ScreenBreak: could not read data file: {exc}", file=sys.stderr)
        return {
            "looking_seconds": 0.0, "break_required": False, "away_seconds": 0.0,
            "last_saved": time.time(), "settings": DEFAULTS.copy(),
            "break_extension_seconds": 0.0, "break_looking_seconds": 0.0,
            "strikes": 0, "penalized_looking_seconds": 0.0,
        }
    try:
        data = json.loads(raw)
        if not isinstance(data, dict):
            raise ValueError("data file is not a JSON object")
        settings = data.get("settings", {}) or {}
        if not isinstance(settings, dict):
            settings = {}
        return {
            "looking_seconds": max(0.0, min(24 * 3600.0, float(data.get("looking_seconds", 0)))),
            "break_required": bool(data.get("break_required", False)),
            "away_seconds": max(0.0, min(24 * 3600.0, float(data.get("away_seconds", 0)))),
            "last_saved": float(data.get("last_saved", time.time())),
            "break_extension_seconds": max(0.0, float(data.get("break_extension_seconds", 0))),
            "break_looking_seconds": max(0.0, float(data.get("break_looking_seconds", 0))),
            "strikes": max(0, min(2, _safe_int(data.get("strikes", 0), 0))),
            "penalized_looking_seconds": max(0.0, float(data.get("penalized_looking_seconds", 0))),
            "settings": {
                "screen_limit_minutes": max(1, min(1440, _safe_int(
                    settings.get("screen_limit_minutes", DEFAULTS["screen_limit_minutes"]),
                    DEFAULTS["screen_limit_minutes"]))),
                "break_minutes": max(1, min(240, _safe_int(
                    settings.get("break_minutes", DEFAULTS["break_minutes"]),
                    DEFAULTS["break_minutes"]))),
            },
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


def main():
    saved = load_data()
    settings = saved["settings"]
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
    }

    root = tk.Tk()
    root.title("ScreenBreak")
    root.geometry("430x330")
    root.minsize(400, 300)
    root.configure(bg="#F4F7FB")

    title = tk.Label(root, text="ScreenBreak", font=("Segoe UI", 23, "bold"),
                     fg="#172B4D", bg="#F4F7FB")
    title.pack(pady=(20, 4))
    subtitle = tk.Label(root, text="A little break helps you feel refreshed.",
                        font=("Segoe UI", 10), fg="#62748A", bg="#F4F7FB")
    subtitle.pack()

    status = tk.Label(root, text="Starting camera…", font=("Segoe UI", 14, "bold"),
                      fg="#B7791F", bg="#F4F7FB")
    status.pack(pady=(20, 8))
    screen_label = tk.Label(root, text="", font=("Segoe UI", 17, "bold"),
                            fg="#172B4D", bg="#F4F7FB")
    screen_label.pack(pady=3)
    break_label = tk.Label(root, text="", font=("Segoe UI", 12),
                           fg="#287D55", bg="#F4F7FB")
    break_label.pack(pady=3)
    hint = tk.Label(root, text="ScreenBreak runs quietly while this window is open.",
                    font=("Segoe UI", 9), fg="#62748A", bg="#F4F7FB", wraplength=380)
    hint.pack(pady=8)

    controls = tk.Frame(root, bg="#F4F7FB")
    controls.pack(pady=8)
    camera_button = tk.Button(controls, text="Hide camera preview", width=18,
                              command=lambda: toggle_camera(), relief="flat",
                              bg="#DCE7F5", fg="#172B4D", padx=8, pady=7)
    camera_button.grid(row=0, column=0, padx=5)
    settings_button = tk.Button(controls, text="Settings", width=12,
                                command=lambda: open_settings(), relief="flat",
                                bg="#DCE7F5", fg="#172B4D", padx=8, pady=7)
    settings_button.grid(row=0, column=1, padx=5)
    reset_button = tk.Button(root, text="Reset screen time", command=lambda: reset_with_confirmation(),
                             relief="flat", bg="#FCE8E6", fg="#A12B24",
                             padx=14, pady=7)
    reset_button.pack(pady=(2, 4))
    tk.Label(root, text="Your camera is processed on this computer. No video is saved.",
             font=("Segoe UI", 8), fg="#8291A3", bg="#F4F7FB").pack(side="bottom", pady=12)

    def open_camera():
        """Try to open the webcam. Returns a VideoCapture or None."""
        cap = cv2.VideoCapture(CAMERA_INDEX, cv2.CAP_DSHOW)
        if not cap.isOpened():
            try:
                cap.release()
            except Exception:
                pass
            cap = cv2.VideoCapture(CAMERA_INDEX)
        if cap.isOpened():
            cap.set(cv2.CAP_PROP_FRAME_WIDTH, FRAME_WIDTH)
            cap.set(cv2.CAP_PROP_FRAME_HEIGHT, FRAME_HEIGHT)
            state["camera_available"] = True
            state["camera_fail_count"] = 0
            return cap
        try:
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

    state["cap"] = open_camera()
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
    if state["break_required"]:
        gap = max(0.0, time.time() - saved["last_saved"])
        if gap > 0:
            state["away_seconds"] += gap
            state["continuous_away"] = SETTLE_SECONDS
        if state["away_seconds"] >= settings["break_minutes"] * 60 + state["break_extension_seconds"]:
            state["break_required"] = False
            state["away_seconds"] = 0.0
            state["looking_seconds"] = 0.0
            state["strikes"] = 0
            state["break_looking_seconds"] = 0.0
            state["break_extension_seconds"] = 0.0
            state["penalized_looking_seconds"] = 0.0
        save_data(state)

    def target_seconds():
        return settings["screen_limit_minutes"] * 60

    def required_break_seconds():
        # v2.2: base break + any penalty extension from 3rd strikes.
        return settings["break_minutes"] * 60 + state["break_extension_seconds"]

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
            return (f"3RD STRIKE — +{format_time(penalty)} BREAK TIME "
                    f"(looked {format_time(new_looking)} since last penalty)")
        if state["strikes"] == 2:
            state["away_seconds"] = 0.0
            state["continuous_away"] = 0.0
            save_data(state)
            return "2ND GLANCE — BREAK RESET TO ZERO"
        return "1ST GLANCE — WARNING, LOOK AWAY"

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
        tk.Label(popup, text=f"You've reached {settings['screen_limit_minutes']} minutes of screen time.\n"
                 f"Take a break for at least {settings['break_minutes']} minutes.",
                 font=("Segoe UI", 11), fg="#52657A", bg="#F4F7FB").pack(pady=5)

        def begin():
            state["break_required"] = True
            state["away_seconds"] = 0.0
            reset_break_tracking()
            state["last_wall"] = time.time()
            state["last_tick"] = time.monotonic()
            try:
                popup.destroy()
            except tk.TclError:
                pass
            state["popup"] = None
            status.config(text="BREAK TIME", fg="#287D55")
            hint.config(text="Look away or step away. 1s glance = 1 strike: 1st warns, 2nd resets, 3rd resets + adds 2x your looking time.")
            save_data(state)

        tk.Button(popup, text="OK — start my break", command=begin,
                  font=("Segoe UI", 11, "bold"), relief="flat",
                  bg="#287D55", fg="white", padx=18, pady=9).pack(pady=13)
        popup.protocol("WM_DELETE_WINDOW", begin)
        # Show above everything, even if ScreenBreak is minimized.
        pop_to_front(popup, 390, 205)

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
        tk.Label(popup, text="Your screen-time counter has restarted.",
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
        confirmed = messagebox.askyesno(
            "Confirm reset",
            "Are you sure you want to reset ScreenBreak?\\n\\n"
            "This will clear your accumulated screen time, break progress, "
            "glance strikes, and any extra break time.",
            parent=root,
            icon="warning",
        )
        if not confirmed:
            return

        state["looking_seconds"] = 0.0
        state["break_required"] = False
        state["away_seconds"] = 0.0
        state["break_looking_seconds"] = 0.0
        state["break_extension_seconds"] = 0.0
        state["strikes"] = 0
        state["penalized_looking_seconds"] = 0.0
        reset_break_tracking()
        state["last_tick"] = time.monotonic()
        state["last_wall"] = time.time()
        state["last_save"] = time.monotonic()
        status.config(text="SCREEN TIME RESET", fg="#287D55")
        hint.config(text="Your screen-time counter and break progress have been reset.")
        save_data(state)
        refresh_labels()

    def complete_break():
        """Reset the next screen-time cycle immediately. Shared by the
        normal tick path and the sleep-gap path so they cannot drift."""
        state["break_required"] = False
        state["away_seconds"] = 0.0
        state["looking_seconds"] = 0.0
        reset_break_tracking()
        state["last_tick"] = time.monotonic()
        state["last_wall"] = time.time()
        status.config(text="BREAK COMPLETE — NEW CYCLE STARTED", fg="#287D55")
        hint.config(text="Your screen-time counter has restarted from zero.")
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
        camera_button.config(text="Show camera preview")

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
        camera_button.config(text="Hide camera preview")

    def toggle_camera():
        if state["camera_visible"]:
            close_camera_preview()
        elif state.get("cap") is not None and state["cap"].isOpened():
            open_camera_preview()
        else:
            status.config(text="CAMERA NOT AVAILABLE", fg="#B42318")
            hint.config(text="Connect a webcam and check Windows camera permissions.")

    # The preview is a separate Toplevel. Its X button closes only this window.
    if state.get("cap") is not None and state["cap"].isOpened():
        open_camera_preview()
    else:
        # FIX 7: don't claim a preview is open when there is no camera.
        state["camera_visible"] = False
        camera_button.config(text="Show camera preview")

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
        win.geometry("370x245")
        win.resizable(False, False)
        win.configure(bg="#F4F7FB")
        tk.Label(win, text="Your break settings", font=("Segoe UI", 17, "bold"),
                 fg="#172B4D", bg="#F4F7FB").pack(pady=(18, 12))
        frame = tk.Frame(win, bg="#F4F7FB")
        frame.pack(padx=20, fill="x")
        tk.Label(frame, text="Screen time before a break (minutes)", bg="#F4F7FB",
                 fg="#52657A", anchor="w").pack(fill="x")
        screen_var = tk.StringVar(value=str(settings["screen_limit_minutes"]))
        tk.Entry(frame, textvariable=screen_var, font=("Segoe UI", 12), justify="center").pack(fill="x", pady=(3, 10))
        tk.Label(frame, text="Minimum continuous break (minutes)", bg="#F4F7FB",
                 fg="#52657A", anchor="w").pack(fill="x")
        break_var = tk.StringVar(value=str(settings["break_minutes"]))
        tk.Entry(frame, textvariable=break_var, font=("Segoe UI", 12), justify="center").pack(fill="x", pady=(3, 8))
        msg = tk.Label(win, text="", font=("Segoe UI", 9), fg="#B42318", bg="#F4F7FB")
        msg.pack()

        def _clear_settings_window():
            state["settings_window"] = None

        def save_settings():
            try:
                new_screen = int(screen_var.get())
                new_break = int(break_var.get())
                if not (1 <= new_screen <= 1440 and 1 <= new_break <= 240):
                    raise ValueError
            except ValueError:
                msg.config(text="Enter whole minutes (screen: 1–1440, break: 1–240).")
                return
            settings["screen_limit_minutes"] = new_screen
            settings["break_minutes"] = new_break
            save_data(state)
            state["settings_window"] = None
            try:
                win.destroy()
            except tk.TclError:
                pass
            refresh_labels()
        tk.Button(win, text="Save settings", command=save_settings, relief="flat",
                  bg="#287D55", fg="white", padx=18, pady=8).pack(pady=7)
        win.protocol("WM_DELETE_WINDOW", lambda: (_clear_settings_window(), win.destroy()))

    def refresh_labels():
        screen_label.config(text=f"Screen time: {format_time(state['looking_seconds'])}")
        if state["break_required"]:
            req = required_break_seconds()
            extra = f" (+{format_time(state['break_extension_seconds'])} penalty)" if state["break_extension_seconds"] > 0 else ""
            break_label.config(text=f"Break progress: {format_time(state['away_seconds'])} / {format_time(req)}{extra} • Strikes {state['strikes']}/3 • Looked {format_time(state['break_looking_seconds'])}")
        else:
            left = max(0, target_seconds() - state["looking_seconds"])
            break_label.config(text=f"Break reminder in: {format_time(left)}")

    def _update_tick():
        now_mono = time.monotonic()
        now_wall = time.time()
        elapsed = max(0.0, min(now_mono - state["last_tick"], 1.0))
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
        if wall_elapsed > SLEEP_GAP_MIN_SECONDS and (wall_elapsed - elapsed) > SLEEP_GAP_MIN_SECONDS:
            sleep_gap = wall_elapsed - elapsed
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
                status.config(text="CAMERA NOT AVAILABLE — RETRYING…", fg="#B42318")
                hint.config(text="Connect a webcam and check Windows camera permissions.")
                refresh_labels()
                if now_mono - state["last_save"] >= SAVE_EVERY_SECONDS:
                    save_data(state)
                    state["last_save"] = now_mono
                return

        looking = False
        ok, frame = cap.read()
        if not ok or frame is None:
            state["camera_fail_count"] += 1
            state["camera_available"] = False
            state["looking"] = False
            # FIX 4: after repeated failures, drop the handle so the
            # retry logic above reopens it instead of spinning forever.
            if state["camera_fail_count"] >= CAMERA_MAX_CONSECUTIVE_FAILURES:
                close_camera()
                state["last_camera_retry"] = now_mono
            status.config(text="CAMERA NOT AVAILABLE — RETRYING…", fg="#B42318")
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
                if strike_msg is not None and "3RD STRIKE" in strike_msg:
                    status.config(text=strike_msg, fg="#B42318")
                    hint.config(text=f"You looked {format_time(state['break_looking_seconds'])} total during this break, so {format_time(state['last_penalty_seconds'])} was added. Look away to restart.")
                elif long_reset:
                    status.config(text="LOOKING 3s — BREAK RESET", fg="#B7791F")
                elif strike_msg is not None:
                    status.config(text=strike_msg, fg="#B7791F")
                else:
                    remaining = BREAK_RESET_LOOKING_SECONDS - state["looking_streak"]
                    status.config(
                        text=f"BREAK PAUSED — LOOKING ({remaining:.0f}s TO RESET) • STRIKE {state['strikes']}/3",
                        fg="#B7791F")
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
                        status.config(text="BREAK IN PROGRESS", fg="#287D55")
                    else:
                        left_settle = SETTLE_SECONDS - state["continuous_away"]
                        status.config(text=f"SETTLING — {left_settle:.0f}s BEFORE TIMER RESUMES", fg="#B7791F")
                else:
                    status.config(text="CAMERA NOT AVAILABLE", fg="#B42318")
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
                status.config(text="SCREEN TIME COUNTING", fg="#287D55")
            elif state["camera_available"]:
                status.config(text="AWAY — SCREEN TIME PAUSED", fg="#B7791F")
            else:
                status.config(text="CAMERA NOT AVAILABLE", fg="#B42318")
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
        save_data(state)
        try:
            close_camera()
            if face_mesh is not None:
                face_mesh.close()
        except Exception:
            pass
        try:
            root.destroy()
        except tk.TclError:
            pass

    root.protocol("WM_DELETE_WINDOW", close_app)
    if state.get("cap") is None or not state["cap"].isOpened():
        status.config(text="CAMERA NOT AVAILABLE", fg="#B42318")
        hint.config(text="Connect a webcam and check Windows camera permissions.")
    root.after(100, update)
    root.mainloop()


if __name__ == "__main__":
    main()
