import cv2
import mediapipe as mp
import math
import json
import base64
import os
import time
import tkinter as tk
from pathlib import Path

# ScreenBreak v2: local webcam gaze estimate + accumulated screen-looking time.
# Webcam frames are processed locally and are never recorded or uploaded.

CAMERA_INDEX = 0
FRAME_WIDTH = 960
FRAME_HEIGHT = 540
TARGET_SECONDS = 2 * 60 * 60
BREAK_SECONDS = 10 * 60
SAVE_EVERY_SECONDS = 10
DATA_FILE = Path(__file__).with_name("screenbreak_data.json")

LEFT_EYE_CORNERS = (33, 133)
RIGHT_EYE_CORNERS = (362, 263)
LEFT_IRIS = (468, 469, 470, 471, 472)
RIGHT_IRIS = (473, 474, 475, 476, 477)
CENTER_MIN = 0.34
CENTER_MAX = 0.66
VERTICAL_MIN = 0.22
VERTICAL_MAX = 0.78


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



def format_time(seconds):
    seconds = max(0, int(seconds))
    hours, remainder = divmod(seconds, 3600)
    minutes, secs = divmod(remainder, 60)
    if hours:
        return f"{hours} hr {minutes:02d} min"
    return f"{minutes} min {secs:02d} sec"


APP_DIR = Path(os.environ.get("LOCALAPPDATA", str(Path.home()))) / "ScreenBreak"
APP_DIR.mkdir(parents=True, exist_ok=True)
DATA_FILE = APP_DIR / "screenbreak_data.json"
DEFAULTS = {"screen_limit_minutes": 120, "break_minutes": 10}


def load_data():
    try:
        data = json.loads(DATA_FILE.read_text(encoding="utf-8"))
        settings = data.get("settings", {})
        return {
            "looking_seconds": max(0.0, float(data.get("looking_seconds", 0))),
            "break_required": bool(data.get("break_required", False)),
            "away_seconds": max(0.0, float(data.get("away_seconds", 0))),
            "last_saved": float(data.get("last_saved", time.time())),
            "settings": {
                "screen_limit_minutes": max(1, int(settings.get("screen_limit_minutes", DEFAULTS["screen_limit_minutes"]))),
                "break_minutes": max(1, int(settings.get("break_minutes", DEFAULTS["break_minutes"]))),
            },
        }
    except Exception:
        return {
            "looking_seconds": 0.0, "break_required": False, "away_seconds": 0.0,
            "last_saved": time.time(), "settings": DEFAULTS.copy()
        }


def save_data(state):
    try:
        DATA_FILE.write_text(json.dumps({
            "looking_seconds": round(state["looking_seconds"], 1),
            "break_required": state["break_required"],
            "away_seconds": round(state["away_seconds"], 1),
            "last_saved": time.time(),
            "settings": state["settings"],
        }, indent=2), encoding="utf-8")
    except Exception:
        pass


def main():
    saved = load_data()
    settings = saved["settings"]
    state = {
        "running": True,
        "looking_seconds": saved["looking_seconds"],
        "break_required": saved["break_required"],
        "away_seconds": saved["away_seconds"],
        "last_tick": time.monotonic(),
        "last_wall": time.time(),
        "last_save": time.monotonic(),
        "looking": False,
        "camera_visible": True,
        "camera_available": False,
        "popup": None,
        "break_window": None,
        "camera_window": None,
        "camera_image": None,
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
    tk.Label(root, text="Your camera is processed on this computer. No video is saved.",
             font=("Segoe UI", 8), fg="#8291A3", bg="#F4F7FB").pack(side="bottom", pady=12)

    cap = cv2.VideoCapture(CAMERA_INDEX, cv2.CAP_DSHOW)
    if not cap.isOpened():
        cap = cv2.VideoCapture(CAMERA_INDEX)
    if cap.isOpened():
        cap.set(cv2.CAP_PROP_FRAME_WIDTH, FRAME_WIDTH)
        cap.set(cv2.CAP_PROP_FRAME_HEIGHT, FRAME_HEIGHT)
        state["camera_available"] = True

    face_mesh = mp.solutions.face_mesh.FaceMesh(
        max_num_faces=1, refine_landmarks=True,
        min_detection_confidence=0.55, min_tracking_confidence=0.55)

    # When Windows was asleep or shut down during a required break, that elapsed
    # wall-clock time counts as away time. It never adds screen-looking time.
    if state["break_required"]:
        gap = max(0.0, time.time() - saved["last_saved"])
        state["away_seconds"] += gap
        if state["away_seconds"] >= settings["break_minutes"] * 60:
            state["break_required"] = False
            state["away_seconds"] = 0.0
            state["looking_seconds"] = 0.0
            save_data(state)

    def target_seconds():
        return settings["screen_limit_minutes"] * 60

    def required_break_seconds():
        return settings["break_minutes"] * 60

    def show_threshold_popup():
        if state["popup"] is not None and state["popup"].winfo_exists():
            return
        popup = tk.Toplevel(root)
        state["popup"] = popup
        popup.title("Time for a break")
        popup.geometry("390x205")
        popup.resizable(False, False)
        popup.configure(bg="#F4F7FB")
        popup.transient(root)
        popup.grab_set()
        tk.Label(popup, text="Time for a break!", font=("Segoe UI", 20, "bold"),
                 fg="#172B4D", bg="#F4F7FB").pack(pady=(24, 8))
        tk.Label(popup, text=f"You've reached {settings['screen_limit_minutes']} minutes of screen time.\n"
                 f"Take a break for at least {settings['break_minutes']} minutes.",
                 font=("Segoe UI", 11), fg="#52657A", bg="#F4F7FB").pack(pady=5)

        def begin():
            state["break_required"] = True
            state["away_seconds"] = 0.0
            state["last_wall"] = time.time()
            popup.destroy()
            state["popup"] = None
            status.config(text="BREAK TIME", fg="#287D55")
            hint.config(text="Look away or step away. Looking at the screen resets your break timer.")
            save_data(state)

        tk.Button(popup, text="OK — start my break", command=begin,
                  font=("Segoe UI", 11, "bold"), relief="flat",
                  bg="#287D55", fg="white", padx=18, pady=9).pack(pady=13)
        popup.protocol("WM_DELETE_WINDOW", begin)

    def finish_break_popup():
        popup = tk.Toplevel(root)
        state["break_window"] = popup
        popup.title("Break complete")
        popup.geometry("350x170")
        popup.resizable(False, False)
        popup.configure(bg="#F4F7FB")
        tk.Label(popup, text="Break complete!", font=("Segoe UI", 20, "bold"),
                 fg="#287D55", bg="#F4F7FB").pack(pady=(25, 8))
        tk.Label(popup, text="Your screen-time counter has restarted.",
                 font=("Segoe UI", 10), fg="#52657A", bg="#F4F7FB").pack(pady=5)
        def done():
            state["break_required"] = False
            state["away_seconds"] = 0.0
            state["looking_seconds"] = 0.0
            state["break_window"] = None
            popup.destroy()
            status.config(text="READY", fg="#287D55")
            hint.config(text="Your next screen-time session has started.")
            save_data(state)
        tk.Button(popup, text="OK", command=done, relief="flat",
                  bg="#287D55", fg="white", padx=24, pady=8).pack(pady=12)
        popup.protocol("WM_DELETE_WINDOW", done)

    def close_camera_preview():
        win = state.get("camera_window")
        state["camera_visible"] = False
        state["camera_image"] = None
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
        elif cap.isOpened():
            open_camera_preview()
        else:
            status.config(text="CAMERA NOT AVAILABLE", fg="#B42318")
            hint.config(text="Connect a webcam and check Windows camera permissions.")

    # The preview is a separate Toplevel. Its X button closes only this window.
    if cap.isOpened():
        open_camera_preview()

    def open_settings():
        win = tk.Toplevel(root)
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
            win.destroy()
            refresh_labels()
        tk.Button(win, text="Save settings", command=save_settings, relief="flat",
                  bg="#287D55", fg="white", padx=18, pady=8).pack(pady=7)

    def refresh_labels():
        screen_label.config(text=f"Screen time: {format_time(state['looking_seconds'])}")
        if state["break_required"]:
            break_label.config(text=f"Break progress: {format_time(state['away_seconds'])} / {settings['break_minutes']} min")
        else:
            left = max(0, target_seconds() - state["looking_seconds"])
            break_label.config(text=f"Break reminder in: {format_time(left)}")
    def update():
        if not state["running"]:
            return
        now_mono = time.monotonic()
        now_wall = time.time()
        elapsed = max(0.0, min(now_mono - state["last_tick"], 1.0))
        wall_elapsed = max(0.0, now_wall - state["last_wall"])
        state["last_tick"] = now_mono
        state["last_wall"] = now_wall

        looking = False
        ok, frame = cap.read() if cap.isOpened() else (False, None)
        if ok:
            frame = cv2.flip(frame, 1)
            h, w = frame.shape[:2]
            results = face_mesh.process(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB))
            if results.multi_face_landmarks:
                looking, gx, gy, hx = classify(results.multi_face_landmarks[0], w, h)
            # Render the preview in its own Tk window. Its X button destroys
            # only this preview; the main ScreenBreak status window remains open.
            if state["camera_visible"]:
                cam_win = state.get("camera_window")
                try:
                    if cam_win is not None and cam_win.winfo_exists():
                        preview = state.get("camera_preview_label")
                        if preview is not None and preview.winfo_exists():
                            ok_jpg, encoded = cv2.imencode(".jpg", frame)
                            if ok_jpg:
                                photo = tk.PhotoImage(data=base64.b64encode(encoded.tobytes()))
                                preview.configure(image=photo, text="")
                                state["camera_image"] = photo
                except tk.TclError:
                    close_camera_preview()
            state["camera_available"] = True
        else:
            state["camera_available"] = False

        state["looking"] = looking
        if state["break_required"]:
            if looking:
                state["away_seconds"] = 0.0
                status.config(text="BREAK PAUSED — YOU'RE AT THE SCREEN", fg="#B7791F")
            elif state["camera_available"]:
                state["away_seconds"] += elapsed
                status.config(text="BREAK IN PROGRESS", fg="#287D55")
            else:
                status.config(text="CAMERA NOT AVAILABLE", fg="#B42318")
            if state["away_seconds"] >= required_break_seconds():
                state["away_seconds"] = required_break_seconds()
                save_data(state)
                state["break_required"] = False
                finish_break_popup()
        else:
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
        if now_mono - state["last_save"] >= 1:
            save_data(state)
            state["last_save"] = now_mono
        root.after(40, update)

    def close_app():
        if not state["running"]:
            return
        state["running"] = False
        save_data(state)
        try:
            cap.release()
            face_mesh.close()
        except Exception:
            pass
        root.destroy()

    root.protocol("WM_DELETE_WINDOW", close_app)
    if not cap.isOpened():
        status.config(text="CAMERA NOT AVAILABLE", fg="#B42318")
        hint.config(text="Connect a webcam and check Windows camera permissions.")
    root.after(100, update)
    root.mainloop()


if __name__ == "__main__":
    main()
