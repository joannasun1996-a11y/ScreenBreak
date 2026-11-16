import cv2
import mediapipe as mp
import math
import json
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
DATA_DIR = Path(os.environ.get("LOCALAPPDATA", str(Path.home()))) / "ScreenBreak"\nDATA_DIR.mkdir(parents=True, exist_ok=True)\nDATA_FILE = DATA_DIR / "screenbreak_data.json"

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
    return f"{hours:02d}:{minutes:02d}:{secs:02d}"


def load_saved_seconds():
    try:
        data = json.loads(DATA_FILE.read_text(encoding="utf-8"))
        return max(0.0, min(float(data.get("looking_seconds", 0)), TARGET_SECONDS))
    except Exception:
        return 0.0


def save_seconds(seconds):
    try:
        DATA_FILE.write_text(json.dumps({"looking_seconds": round(seconds, 1)}), encoding="utf-8")
    except Exception:
        pass


def main():
    cap = cv2.VideoCapture(CAMERA_INDEX, cv2.CAP_DSHOW)
    if not cap.isOpened():
        cap = cv2.VideoCapture(CAMERA_INDEX)
    if not cap.isOpened():
        raise RuntimeError("Could not open the webcam. Close other camera apps and check Windows camera permissions.")
    cap.set(cv2.CAP_PROP_FRAME_WIDTH, FRAME_WIDTH)
    cap.set(cv2.CAP_PROP_FRAME_HEIGHT, FRAME_HEIGHT)

    root = tk.Tk()
    root.title("ScreenBreak")
    root.geometry("470x310")
    root.resizable(False, False)
    root.configure(bg="#101820")

    tk.Label(root, text="ScreenBreak", font=("Segoe UI", 22, "bold"),
             fg="white", bg="#101820").pack(pady=(18, 3))
    status = tk.Label(root, text="Starting camera…", font=("Segoe UI", 17, "bold"),
                      fg="#f5c542", bg="#101820")
    status.pack(pady=(8, 3))
    timer_label = tk.Label(root, text="Screen time: 00:00:00", font=("Segoe UI", 16),
                           fg="white", bg="#101820")
    timer_label.pack(pady=5)
    remaining_label = tk.Label(root, text="2 hours of looking at the screen triggers a break",
                               font=("Segoe UI", 9), fg="#c5d0d8", bg="#101820")
    remaining_label.pack(pady=3)
    detail = tk.Label(root, text="Keep your face visible and look naturally at your monitor.",
                      font=("Segoe UI", 9), fg="#c5d0d8", bg="#101820", wraplength=430)
    detail.pack(pady=5)
    tk.Label(root, text="Local processing • No video is saved", font=("Segoe UI", 9),
             fg="#8fa3b5", bg="#101820").pack(pady=(10, 0))

    state = {
        "running": True,
        "looking_seconds": load_saved_seconds(),
        "last_tick": time.monotonic(),
        "last_save": time.monotonic(),
        "on_break": False,
        "break_end": None,
        "break_window": None,
        "face_mesh": None,
    }

    face_mesh = mp.solutions.face_mesh.FaceMesh(
        max_num_faces=1, refine_landmarks=True,
        min_detection_confidence=0.55, min_tracking_confidence=0.55)
    state["face_mesh"] = face_mesh

    def start_break():
        if state["on_break"] or not state["running"]:
            return
        state["on_break"] = True
        state["break_end"] = time.monotonic() + BREAK_SECONDS
        save_seconds(0)
        state["looking_seconds"] = 0
        status.config(text="BREAK TIME", fg="#35d07f")
        detail.config(text="Your 2 hours of screen-looking time are complete. Enjoy some fresh air!")

        popup = tk.Toplevel(root)
        state["break_window"] = popup
        popup.title("ScreenBreak — Outdoor break")
        popup.geometry("420x245")
        popup.resizable(False, False)
        popup.configure(bg="#101820")
        popup.attributes("-topmost", True)
        popup.protocol("WM_DELETE_WINDOW", lambda: None)
        tk.Label(popup, text="Time to go outside!", font=("Segoe UI", 21, "bold"),
                 fg="white", bg="#101820").pack(pady=(22, 8))
        tk.Label(popup, text="Take a 10-minute outdoor break.", font=("Segoe UI", 13),
                 fg="#c5d0d8", bg="#101820").pack(pady=3)
        countdown = tk.Label(popup, text="10:00 remaining", font=("Segoe UI", 25, "bold"),
                             fg="#35d07f", bg="#101820")
        countdown.pack(pady=12)
        done_button = tk.Button(popup, text="Done — start again", font=("Segoe UI", 11, "bold"),
                                state="disabled", command=finish_break,
                                bg="#35d07f", fg="#101820", activebackground="#55e092",
                                relief="flat", padx=18, pady=9, disabledforeground="#607080")
        done_button.pack(pady=4)

        def tick_break():
            if not state["on_break"] or not popup.winfo_exists():
                return
            left = max(0, int(state["break_end"] - time.monotonic() + 0.999))
            countdown.config(text=f"{left // 60:02d}:{left % 60:02d} remaining")
            if left <= 0:
                countdown.config(text="Break complete!", fg="#35d07f")
                done_button.config(state="normal")
            else:
                popup.after(250, tick_break)
        tick_break()

    def finish_break():
        if not state["on_break"]:
            return
        popup = state["break_window"]
        state["on_break"] = False
        state["break_window"] = None
        state["break_end"] = None
        state["looking_seconds"] = 0
        state["last_tick"] = time.monotonic()
        save_seconds(0)
        if popup and popup.winfo_exists():
            popup.destroy()
        status.config(text="WAITING FOR YOUR FACE…", fg="#f5c542")
        detail.config(text="Your screen-time counter has restarted.")

    def update():
        if not state["running"]:
            return
        now = time.monotonic()
        elapsed = max(0.0, min(now - state["last_tick"], 0.25))
        state["last_tick"] = now
        ok, frame = cap.read()
        looking = False
        if ok:
            frame = cv2.flip(frame, 1)
            h, w = frame.shape[:2]
            results = face_mesh.process(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB))
            if results.multi_face_landmarks:
                looking, gx, gy, hx = classify(results.multi_face_landmarks[0], w, h)
                if looking:
                    status.config(text="LOOKING AT SCREEN", fg="#35d07f")
                else:
                    status.config(text="LOOKING AWAY", fg="#ffb454")
                detail.config(text=f"Gaze estimate: horizontal {gx:.2f}, vertical {gy:.2f} • head {hx:.2f}")
            else:
                status.config(text="FACE NOT DETECTED", fg="#f5c542")
                detail.config(text="Move into view of the webcam. Screen time pauses when your face isn't detected.")
            cv2.putText(frame, "ScreenBreak camera preview - press Q to close", (15, 28),
                        cv2.FONT_HERSHEY_SIMPLEX, 0.55, (255, 255, 255), 1)
            cv2.imshow("ScreenBreak Camera", frame)
            if cv2.waitKey(1) & 0xFF == ord('q'):
                close()
                return
        else:
            status.config(text="CAMERA UNAVAILABLE", fg="#f5c542")

        if looking and not state["on_break"]:
            state["looking_seconds"] += elapsed

        current = state["looking_seconds"]
        timer_label.config(text=f"Screen time: {format_time(current)}")
        if not state["on_break"]:
            left = max(0, TARGET_SECONDS - current)
            remaining_label.config(text=f"{format_time(left)} of looking time until your 10-minute outdoor break")
            if current >= TARGET_SECONDS:
                start_break()
        if now - state["last_save"] >= SAVE_EVERY_SECONDS:
            save_seconds(current)
            state["last_save"] = now
        root.after(30, update)

    def close():
        if not state["running"]:
            return
        state["running"] = False
        save_seconds(state["looking_seconds"])
        try:
            cap.release()
            face_mesh.close()
            cv2.destroyAllWindows()
        finally:
            if root.winfo_exists():
                root.destroy()

    root.protocol("WM_DELETE_WINDOW", close)
    root.after(100, update)
    root.mainloop()
    if state["running"]:
        close()


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        print("\nScreenBreak could not start:")
        print(exc)
        input("\nPress Enter to close...")
