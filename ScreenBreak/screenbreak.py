import bisect
import cv2
import mediapipe as mp
import math
import json
import html as html_lib
import os
import re
import sys
import threading
import time
import traceback
import urllib.request
import urllib.error
import webbrowser
import tkinter as tk
from datetime import datetime, timedelta
from tkinter import messagebox, ttk
from PIL import Image, ImageTk
from pathlib import Path

# v2.32 (2026-11-19): report email is manual only; send now uses the
#  saved Google service connection and requires only a recipient email.
# v2.30 (2026-11-18): HTML-escape the user-editable report name
#  before inserting it into generated reports.
#
# v2.29 (2026-11-18): settings save is transactional, failed writes
#  roll back in-memory values and auto-start, and report cadence
#  rejects fractional day/week values instead of truncating them.
#
# v2.28 (2026-11-18): inference failures are unknown (not away),
#  restart gaps respect the 2-second/report-break thresholds and
#  can complete the automatic away reset, and sleep report colors
#  honor penalty-extended breaks. See AUDIT-REPORT.txt.
#
# v2.27 (2026-11-18): missing camera/model pauses auto-away timing;
#  only a working camera frame with no face counts as away. Also
#  settings saving now receives a real True/False
#  result from save_data(), fixing the Save settings button falsely
#  reporting failure after a successful write. See AUDIT-REPORT.txt.
#
# v2.22 (2026-11-18): the emailed report stays under Gmail's
#  ~102KB clip limit, so the previous days show without expanding
#  the message — compact email strips, today skipped in All reports
#  (it is already the main report), strips for the newest previous
#  days only while they fit a 55KB budget, every day still listed.
#  See CHANGES.txt.
#
# v2.21 (2026-11-18): the emailed All reports section works in
#  Gmail — no JavaScript search box (Gmail strips it, so it did
#  nothing) and no <details> rows (Gmail cannot open them, so
#  yesterday's report never showed). The newest days' timelines
#  are shown directly. See CHANGES.txt.
#
# v2.20 (2026-11-18): the All reports window shows the selected
#  day's report right there in the window — one hour at a time,
#  scrolling sideways — instead of only opening it in the browser.
#  See CHANGES.txt.
#
# v2.19 (2026-11-18): the emailed strip shows ONE hour at a time
#  (600px hour blocks), scrolling sideways, built from inline-block
#  blocks and tables — the layout Gmail renders most reliably. The
#  v2.18 flex version bunched the labels and squeezed the bars.
#  See CHANGES.txt.
#
# v2.18 (2026-11-18): the emailed strip is one bar that fills the
#  email width (no absolute positioning, no sideways scroll), so it
#  looks in Gmail like the live bar; the live bar shows 1 hour at a
#  time. See CHANGES.txt.
#
# v2.17 (2026-11-18): the report shows ONE hour at a time again,
#  like the screenshot, and every bar is drawn at its true width
#  (short ones floored at 1 pixel so they stay visible). The live
#  bar keeps 3 hours at a time. See CHANGES.txt.
#
# v2.16 (2026-11-18): more of the bar at once (3 hours, still
#  scrolling sideways), the reset rule fixed so look-away AND face-not-
#  detected both reset the screen timer, every window fits on screen
#  with all its buttons visible, and a bug audit (see CHANGES.txt).
#
# v2.15 (2026-11-18): the emailed report looks like the app, and the
#  buttons feel like they work (see CHANGES.txt). The email now carries
#  today's full report as a scrollable strip — every hour with a tall
#  line, every 30 minutes with a short line, same green/red/blue/grey
#  as the app — plus an All reports list (search it, click a day to
#  see that day) and an attached all-reports.html that does the same
#  in your browser. Hovering or clicking any coloured bar shows how
#  long that bar lasted. "Send report now" and "Save schedule" now
#  show, in plain words and on the button itself, that they worked.
#
# v2.14 (2026-11-18): the emailed report now has a schedule: pick how
#  often (every N days or weeks) and the time of day. Several-day
#  reports email a totals table plus each day's timeline attached.
#
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

# --- Daily report: green = looking at screen, red = looked away for
# LESS than the break time, blue = away (or not there) for the full
# break time (screen time reset to 0), grey = not tracked (camera off / face detection failed). ---
STATE_COLORS = {
    "screen": "#2E9E5B",
    "away": "#D64541",
    "break": "#2F7ED8",
    "unknown": "#9AA5B1",
}
STATE_LABELS = {
    "screen": "Looking at screen",
    "away": "Looked away (shorter than a break)",
    "break": "Away for a full break",
    "unknown": "Not tracked",
}
# Short labels for the emailed strips (v2.22): a full tooltip
# ("Looking at screen: 08:20:00-08:55:00 (35 min 0 sec)") costs
# ~100 bytes per bar, and a flickery day has ~90 bars. The short
# form keeps what it is and how long it lasted.
_SHORT_LABELS = {
    "screen": "Looking",
    "away": "Looked away",
    "break": "Full break",
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

# --- v2.14: how often the report is emailed ---------------------------
REPORT_EVERY_UNITS = {"days": 1, "weeks": 7}
REPORT_MAX_DAYS = 31          # longest period one email may cover


def clean_report_every(value, unit):
    """(number, unit) made safe: unit days/weeks, whole number >= 1,
    and never more than REPORT_MAX_DAYS days in total."""
    unit = unit if unit in REPORT_EVERY_UNITS else "days"
    try:
        number = int(float(str(value).strip()))
    except (ValueError, TypeError, OverflowError):
        number = 1
    number = max(1, min(number, REPORT_MAX_DAYS // REPORT_EVERY_UNITS[unit]))
    return number, unit


def report_period_days(settings):
    number, unit = clean_report_every(settings.get("report_every", 1),
                                      settings.get("report_every_unit", "days"))
    return number * REPORT_EVERY_UNITS[unit]


def report_period_name(n_days):
    """'daily', 'weekly', or '3-day' for report titles."""
    if n_days == 1:
        return "daily"
    if n_days == 7:
        return "weekly"
    return f"{n_days}-day"


def report_every_text(settings):
    """'every day', 'every 2 days', 'every week', 'every 3 weeks'."""
    number, unit = clean_report_every(settings.get("report_every", 1),
                                      settings.get("report_every_unit", "days"))
    singular = unit[:-1]
    return f"every {singular}" if number == 1 else f"every {number} {unit}"


def next_report_due(settings, last_report_date, now=None):
    """The datetime the next report is due: the day `period` days after
    the last one was sent, at the chosen time. With nothing sent yet it
    is due today. Returns None if the time is not valid."""
    parsed = parse_report_time(settings.get("report_time", ""))
    if parsed is None:
        return None
    now = now or datetime.now()
    period = report_period_days(settings)
    try:
        last = datetime.strptime(str(last_report_date), "%Y-%m-%d").date()
    except (ValueError, TypeError):
        last = None
    today = now.date()
    if last is None or last > today:
        due_day = today
    else:
        due_day = last + timedelta(days=period)
    return datetime(due_day.year, due_day.month, due_day.day, parsed[0], parsed[1])


def build_period_report_html(dates, per_day, settings):
    """Summary email for a report that covers several days: a totals
    table (one row per day, plus a total row). Inline styles only, so
    mail apps show it properly. Each day's full timeline is attached."""
    name = (settings.get("report_name") or "").strip() or "Student"
    name = html_lib.escape(name)
    period = report_period_name(len(dates))
    sums = {"screen": 0.0, "away": 0.0, "break": 0.0}
    breaks_total = strikes_total = 0
    cell = "padding:6px 10px;border-bottom:1px solid #E5EAF0;text-align:right;"
    head = "padding:6px 10px;background:#F4F7FB;text-align:right;font-weight:600;"
    rows = ""
    for d in dates:
        totals, day = per_day[d]
        tracked = totals["screen"] + totals["away"] + totals["break"]
        label = datetime.strptime(d, "%Y-%m-%d").strftime("%a %b %d")
        if tracked <= 0:
            rows += (f'<tr><td style="{cell}text-align:left;">{label}</td>'
                     f'<td colspan="5" style="{cell}color:#8291A3;text-align:left;">'
                     f'No activity recorded</td></tr>')
            continue
        for k in sums:
            sums[k] += totals[k]
        breaks_total += day["breaks_completed"]
        strikes_total += day["strikes"]
        rows += (f'<tr><td style="{cell}text-align:left;">{label}</td>'
                 f'<td style="{cell}">{format_duration(totals["screen"])}</td>'
                 f'<td style="{cell}">{format_duration(totals["away"])}</td>'
                 f'<td style="{cell}">{format_duration(totals["break"])}</td>'
                 f'<td style="{cell}">{day["breaks_completed"]}</td>'
                 f'<td style="{cell}">{day["strikes"]}</td></tr>')
    rows += (f'<tr style="font-weight:700;"><td style="{cell}text-align:left;">Total</td>'
             f'<td style="{cell}">{format_duration(sums["screen"])}</td>'
             f'<td style="{cell}">{format_duration(sums["away"])}</td>'
             f'<td style="{cell}">{format_duration(sums["break"])}</td>'
             f'<td style="{cell}">{breaks_total}</td><td style="{cell}">{strikes_total}</td></tr>')
    first = datetime.strptime(dates[0], "%Y-%m-%d").strftime("%B %d")
    last = datetime.strptime(dates[-1], "%Y-%m-%d").strftime("%B %d, %Y")
    return (f'<div style="font-family:Segoe UI,Arial,sans-serif;color:#172B4D;max-width:680px;">'
            f'<h2 style="margin:0 0 4px;">ScreenBreak {period} report \u2014 {name}</h2>'
            f'<div style="color:#62748A;font-size:13px;margin-bottom:12px;">{first} \u2013 {last}</div>'
            f'<table style="border-collapse:collapse;width:100%;font-size:14px;">'
            f'<tr><th style="{head}text-align:left;">Day</th>'
            f'<th style="{head}">\U0001F7E2 Screen</th><th style="{head}">\U0001F534 Short away</th>'
            f'<th style="{head}">\U0001F535 Break</th><th style="{head}">Breaks</th>'
            f'<th style="{head}">Peeks</th></tr>{rows}</table>'
            f'<p style="color:#62748A;font-size:12px;">Each day\u2019s full timeline is attached '
            f'as an HTML file \u2014 open it in your browser.</p></div>')


def _clock_12(dt):
    """'6:00 PM' for a datetime."""
    hour12 = dt.hour % 12 or 12
    return f"{hour12}:{dt.minute:02d} {'AM' if dt.hour < 12 else 'PM'}"


def sent_confirmation_text(email, when, period_name, dates):
    """Plain words for a successful send. Pure, so it can be tested."""
    when_text = when.strftime("%a %b %d at ") + _clock_12(when)
    if len(dates) <= 1:
        what = f"today's {period_name} report"
    else:
        what = f"the {period_name} report for {dates[0]} to {dates[-1]}"
    return (f"\u2713 Sent to {email} at {when_text} \u2014 {what}. "
            f"Check your inbox (and spam if you don't see it).")


def saved_schedule_text(next_due, every_text):
    """Plain words for a saved schedule. Pure, so it can be tested."""
    if next_due is None:
        return "\u2713 Saved."
    when = next_due.strftime("%a %b %d") + " at " + _clock_12(next_due)
    return f"\u2713 Saved \u2014 sends {every_text}, next report: {when}."


def list_report_days():
    """Every day with saved tracking, newest first. Never raises."""
    try:
        dates = []
        for file_path in DAILY_DIR.glob("*.json"):
            date_text = file_path.stem
            try:
                datetime.strptime(date_text, "%Y-%m-%d")
            except ValueError:
                continue
            dates.append(date_text)
        today = day_key()
        if today not in dates and _day_file(today).exists():
            dates.append(today)
        return sorted(set(dates), reverse=True)
    except Exception as exc:
        log_error(f"could not list report days: {exc}")
        return []


def all_days_data(open_segment=None, today_str=None, limit=31):
    """All saved days, newest first, each with totals and segments.
    Capped at `limit` days so an email never gets enormous."""
    today_str = today_str or day_key()
    out = []
    for d in list_report_days()[:limit]:
        open_seg = open_segment if d == today_str else None
        totals, day = daily_totals(d, open_segment=open_seg)
        segments = list(day["segments"])
        if open_seg is not None:
            start, state = open_seg
            if state in STATE_COLORS:
                segments.append({"start": start, "end": time.time(), "state": state})
        segments.sort(key=lambda sg: sg["start"])
        out.append({
            "date": d,
            "label": datetime.strptime(d, "%Y-%m-%d").strftime("%a %b %d, %Y"),
            "totals": totals,
            "breaks_completed": day["breaks_completed"],
            "strikes": day["strikes"],
            "segments": segments,
        })
    return out


def seg_title(state, start, end):
    """Hover text for one coloured bar: what it is, when, and — the
    point — how long it lasted."""
    label = STATE_LABELS.get(state, state)
    return (f"{label}: {_clock_s(start)}\u2013{_clock_s(end)} "
            f"({format_duration(end - start)})")


def build_email_timeline_html(date_str, segments, range_start, range_end, now, is_today):
    """Today's timeline for EMAIL: one hour at a time, scrolling
    sideways — one hour fills the width of the email, like the
    on-computer report. Built from plain inline-block hour blocks
    and tables, because that is the layout Gmail renders most
    reliably: the v2.15 absolute-positioned strip only showed a
    sliver in Gmail, and the v2.18 flex version bunched the hour
    labels together at the left and squeezed the bars. Every hour
    has a tall line and label, every 30 minutes a short line and
    label; segments are drawn at their true width, floored at about
    1 pixel so a 2-second look-away is still a thin line. Hovering
    a bar shows a short tooltip (what it is and how long it
    lasted). The cells carry no click handler and no long tooltip
    text: Gmail strips onclick anyway, and a flickery day has ~90
    bars, so the long text alone added ~10KB per day — part of why
    Gmail clipped the email. v2.22."""
    segments = sorted(segments or [], key=lambda sg: sg["start"])
    starts = _hour_starts(range_start, range_end)
    seg_starts = [sg["start"] for sg in segments]
    # One hour per block, 600px wide (about one email width), so one
    # hour fills the view and the rest scroll sideways.
    hour_w = 600
    blocks = []
    for hs in starts:
        he = hs + 3600
        pieces = []
        cursor = hs
        for seg_s, seg_e, seg_state in _clip_segments(segments, seg_starts, hs, he):
            if seg_s < cursor:
                seg_s = cursor
            if seg_e <= seg_s:
                continue
            if seg_s > cursor:
                pieces.append((cursor, seg_s, None))
            pieces.append((seg_s, seg_e, seg_state))
            cursor = max(cursor, seg_e)
        if cursor < he:
            pieces.append((cursor, he, None))
        cells = []
        for s0, e0, st in pieces:
            pct = (e0 - s0) / 3600.0 * 100.0
            if st is None:
                if pct < 0.05:
                    continue
                cells.append(
                    f'<td width="{pct:.3f}%" style="width:{pct:.3f}%;height:44px;background:#E5EAF0;">&nbsp;</td>')
            else:
                # Floor at ~1 pixel (0.17% of an hour) so a 2-second
                # look-away is still a thin visible line.
                pct = max(pct, 0.17)
                colour = STATE_COLORS[st]
                title = f"{_SHORT_LABELS.get(st, st)}: {format_duration(e0 - s0)}".replace('"', "'")
                cells.append(
                    f'<td width="{pct:.3f}%" style="width:{pct:.3f}%;height:44px;background:{colour};" '
                    f'class="seg" title="{title}">&nbsp;</td>')
        bar = ('<div style="border-radius:6px;overflow:hidden;">'
               '<table width="100%" cellpadding="0" cellspacing="0" style="table-layout:fixed;height:44px;'
               'border-collapse:collapse;font-size:0;line-height:0;"><tr>' + "".join(cells) + "</tr></table></div>")
        blocks.append(
            f'<div style="display:inline-block;width:{hour_w}px;vertical-align:top;white-space:normal;">'
            f'<div style="font-size:12px;font-weight:700;color:#172B4D;">{_hour_label(hs)}</div>'
            f'<div style="font-size:10px;color:#8291A3;text-align:center;">{_half_label(hs + 1800)}</div>'
            f'<div style="height:12px;">'
            f'<span style="display:inline-block;width:2px;height:12px;background:#172B4D;vertical-align:bottom;"></span>'
            f'<span style="display:inline-block;width:298px;height:12px;vertical-align:bottom;"></span>'
            f'<span style="display:inline-block;width:1px;height:6px;background:#62748A;vertical-align:bottom;"></span>'
            f'</div>'
            f'{bar}</div>')
    return (
        f'<div class="stripwrap"><div style="overflow-x:auto;border:1px solid #E5EAF0;border-radius:8px;background:#fff;padding:8px;white-space:nowrap;">'
        + "".join(blocks) + "</div>"
        f'<div class="seginfo" style="font-size:13px;color:#287D55;font-weight:600;margin:6px 0 0;">'
        f'Hover over a coloured bar to see how long it lasted.</div>'
        f'<div style="font-size:11px;color:#8291A3;margin:2px 0 0;">Showing one hour at a time. Scroll sideways for earlier hours. '
        f'Tall line = each hour, short line = each 30 minutes. Green = looking, red = looked away for less '
        f'than the break time, blue = away for a full break, grey = not tracked.</div>')


def build_all_reports_section_html(all_days, max_detail_days=7, skip_date=None,
                                   strip_budget=55000):
    """'All reports' for inside an email: every saved day with its
    totals, and the newest previous days with their timeline shown
    directly underneath. Plain visible rows only — no JavaScript
    search box and no <details> rows, because Gmail strips
    JavaScript and cannot open a <details> row. v2.22: the section
    skips `skip_date` (that day is already the main report above),
    and shows a day's timeline only while the timelines together
    stay inside `strip_budget` bytes — a realistic email was ~300KB
    and Gmail clips messages over ~102KB, so showing every day's
    timeline meant the previous days hid behind "Message clipped".
    Every saved day is still listed, so any date is findable with
    Find (Ctrl+F or Cmd+F). Searching and clicking still work in
    the attached all-reports.html, opened in a browser, where
    JavaScript runs."""
    if not all_days:
        return ('<div style="font-size:13px;color:#62748A;">No earlier reports yet.</div>')
    rows = []
    strips_bytes = 0
    shown = 0
    for i, d in enumerate(all_days):
        if skip_date is not None and d["date"] == skip_date:
            continue
        t = d["totals"]
        tracked = t["screen"] + t["away"] + t["break"]
        if tracked <= 0:
            summary_line = "No activity recorded"
        else:
            summary_line = (f"Screen {format_duration(t['screen'])} \u00b7 "
                            f"Short away {format_duration(t['away'])} \u00b7 "
                            f"Break {format_duration(t['break'])} \u00b7 "
                            f"{d['breaks_completed']} break{'s' if d['breaks_completed'] != 1 else ''} finished")
        strip = ""
        if shown < max_detail_days and tracked > 0:
            rs, re_ = _view_range(d["date"], d["segments"], time.time())
            candidate = build_email_timeline_html(d["date"], d["segments"], rs, re_, time.time(), False)
            if strips_bytes + len(candidate.encode("utf-8")) <= strip_budget:
                strip = candidate
                strips_bytes += len(candidate.encode("utf-8"))
                shown += 1
        if strip:
            rows.append(
                f'<div style="border-bottom:1px solid #E5EAF0;padding:8px 0;">'
                f'<div style="font-size:14px;"><b>{d["label"]}</b> '
                f'<span style="color:#62748A;">\u2014 {summary_line}</span></div>'
                f'<div style="padding:10px 0 4px;">{strip}</div></div>')
        else:
            rows.append(
                f'<div style="border-bottom:1px solid #E5EAF0;padding:8px 0;font-size:14px;">'
                f'<b>{d["label"]}</b> <span style="color:#62748A;">\u2014 {summary_line}</span></div>')
    return (
        '<div style="font-size:13px;color:#62748A;margin-bottom:8px;">'
        'The newest days are below, with their timelines. Every saved day is listed \u2014 '
        'use Find (Ctrl+F or Cmd+F) to jump to a date. To search or open any day, '
        'open the attached <b>all-reports.html</b> in your browser.</div>'
        + "".join(rows))


_ALL_BUNDLE_JS = '''<script>
var DAYS=__DATA__;
function fmt(s){s=Math.max(0,Math.round(s));var h=Math.floor(s/3600),m=Math.floor(s%3600/60),x=s%60;
if(h){return h+' hr '+String(m).padStart(2,'0')+' min';}if(m){return m+' min '+String(x).padStart(2,'0')+' sec';}return x+' sec';}
function clock(t){var d=new Date(t*1000);return String(d.getHours()).padStart(2,'0')+':'+String(d.getMinutes()).padStart(2,'0')+':'+String(d.getSeconds()).padStart(2,'0');}
function hourLabel(t){var d=new Date(t*1000);var h=d.getHours()%12||12;return h+':00 '+(d.getHours()<12?'AM':'PM');}
function strip(day){
var segs=day.segments.slice().sort(function(a,b){return a.start-b.start;});
if(!segs.length){return '<p style="color:#62748A;">No activity recorded on this day.</p>';}
var first=segs[0].start,last=segs[segs.length-1].start;
var rs=new Date(first*1000);rs.setMinutes(0,0,0);rs=rs.getTime()/1000;
var re=new Date(last*1000);re.setMinutes(0,0,0);re=re.getTime()/1000+3600;
var hours=[];for(var h=rs;h<re;h+=3600){hours.push(h);}
var W=260,totalW=hours.length*W,totalS=Math.max(1,re-rs);
var col={screen:'#2E9E5B',away:'#D64541',break:'#2F7ED8',unknown:'#9AA5B1'};
var lab={screen:'Looking at screen',away:'Looked away (shorter than a break)',break:'Away for a full break',unknown:'Not tracked'};
var out='<div style="overflow-x:auto;border:1px solid #E5EAF0;border-radius:8px;background:#fff;"><div style="position:relative;width:'+totalW+'px;height:80px;">';
hours.forEach(function(hs){
var x0=(hs-rs)/totalS*totalW;
out+='<div style="position:absolute;left:'+x0+'px;top:0;font-size:12px;font-weight:700;white-space:nowrap;">'+hourLabel(hs)+'</div>'
+'<div style="position:absolute;left:'+x0+'px;top:22px;width:2px;height:12px;background:#172B4D;"></div>'
+'<div style="position:absolute;left:'+(x0+W/2)+'px;top:8px;font-size:10px;color:#8291A3;transform:translateX(-50%);white-space:nowrap;">'+(new Date((hs+1800)*1000).getHours()%12||12)+':30</div>'
+'<div style="position:absolute;left:'+(x0+W/2)+'px;top:26px;width:1px;height:8px;background:#62748A;"></div>';
segs.forEach(function(sg){
if(sg.end<=hs||sg.start>=hs+3600){return;}
var a=Math.max(sg.start,hs),b=Math.min(sg.end,hs+3600);
var left=x0+(a-hs)/3600*W,wd=Math.max(2,(b-a)/3600*W);
var title=lab[sg.state]+': '+clock(a)+'\u2013'+clock(b)+' ('+fmt(b-a)+')';
out+='<div title="'+title+'" onclick="showSeg(this)" data-title="'+title+'" style="position:absolute;left:'+left.toFixed(1)+'px;top:34px;height:44px;width:'+wd.toFixed(1)+'px;background:'+col[sg.state]+';cursor:pointer;"></div>';});
});
out+='</div></div><div class="seginfo" style="font-size:13px;color:#287D55;font-weight:600;margin:6px 0 0;">Hover over a coloured bar to see how long it lasted \u2014 or click it to keep it shown here.</div>';
out='<div class="stripwrap">'+out+'</div>';
return out;}
function showDay(date){
var day=null;DAYS.forEach(function(d){if(d.date===date){day=d;}});
var el=document.getElementById('daydetail');if(!day||!el){return;}
var t=day.totals;
el.innerHTML='<h2 style="font-size:18px;margin:0 0 4px;">'+day.label+'</h2>'
+'<p style="margin:0 0 10px;">Screen <b>'+fmt(t.screen)+'</b> \u00b7 Short away <b>'+fmt(t.away)+'</b> \u00b7 Break <b>'+fmt(t.break)+'</b> \u00b7 '+day.breaks_completed+' breaks finished</p>'
+strip(day);
el.scrollIntoView();}
function filterDays(q){
q=(q||'').toLowerCase();var n=0;
document.querySelectorAll('.dayrow').forEach(function(r){
var ok=!q||(r.getAttribute('data-search')||'').indexOf(q)>=0;
r.style.display=ok?'':'none';if(ok){n++;}});
var nm=document.getElementById('nomatch');if(nm){nm.style.display=n?'none':'';}}
function showSeg(el){var w=el.closest('.stripwrap');var i=w?w.querySelector('.seginfo'):null;if(i&&el){i.textContent='\u25cf '+el.getAttribute('data-title');}}
</script>'''


def build_all_reports_bundle_html(all_days, settings):
    """Standalone all-reports.html, attached to every email: search
    any day, click it, and that day's full timeline opens — same
    hours, 30-minute lines and colours as the app, and clicking a
    bar shows how long it lasted. Works in any browser."""
    name = (settings.get("report_name") or "").strip() or "Student"
    name = html_lib.escape(name)
    rows = []
    for d in all_days:
        t = d["totals"]
        tracked = t["screen"] + t["away"] + t["break"]
        summary_line = ("No activity recorded" if tracked <= 0 else
                        f"Screen {format_duration(t['screen'])} \u00b7 "
                        f"Short away {format_duration(t['away'])} \u00b7 "
                        f"Break {format_duration(t['break'])}")
        rows.append(
            f'<div class="dayrow" data-search="{d["label"].lower()} {d["date"]}" '
            f'style="border-bottom:1px solid #E5EAF0;padding:10px 4px;cursor:pointer;" '
            f'onclick="showDay(\'{d["date"]}\')">'
            f'<b>{d["label"]}</b> <span style="color:#62748A;">\u2014 {summary_line}</span></div>')
    data = [{
        "date": d["date"], "label": d["label"],
        "totals": d["totals"], "breaks_completed": d["breaks_completed"],
        "strikes": d["strikes"],
        "segments": [{"start": sg["start"], "end": sg["end"], "state": sg["state"]}
                     for sg in d["segments"]],
    } for d in all_days]
    script = _ALL_BUNDLE_JS.replace("__DATA__", json.dumps(data))
    return f'''<!DOCTYPE html>
<html><head><meta charset="utf-8"><title>ScreenBreak — all reports — {name}</title>
<style>body{{font-family:Segoe UI,Arial,sans-serif;background:#F4F7FB;color:#172B4D;margin:0;padding:24px;}}
.card{{background:#fff;border-radius:12px;padding:20px 24px;margin:0 auto 16px;max-width:760px;box-shadow:0 1px 4px rgba(0,0,0,.08);}}
input{{width:100%;box-sizing:border-box;font-size:14px;padding:8px 10px;border:1px solid #CBD5E1;border-radius:8px;}}</style>
</head><body>
<div class="card"><h1 style="font-size:22px;margin:0 0 4px;">All reports — {name}</h1>
<div style="color:#62748A;font-size:13px;">Search for a date, then click it to open that day's timeline.</div>
<div style="margin:12px 0 6px;"><input id="allsearch" type="text" placeholder="Search a date, e.g. Nov 17 or 2026-11-17" oninput="filterDays(this.value)"></div>
<div id="alldays">{''.join(rows) if rows else '<div style="color:#62748A;">No reports saved yet.</div>'}</div>
<div id="nomatch" style="display:none;font-size:13px;color:#B42318;">No day matches that search.</div></div>
<div class="card" id="daydetail"><div style="color:#62748A;">Click a day above to see its timeline here.</div></div>
{script}
</body></html>'''


def build_period_report_text(dates, per_day, settings):
    name = (settings.get("report_name") or "").strip() or "Student"
    lines = [f"ScreenBreak {report_period_name(len(dates))} report \u2014 {name} \u2014 "
             f"{dates[0]} to {dates[-1]}", ""]
    sums = {"screen": 0.0, "away": 0.0, "break": 0.0}
    for d in dates:
        totals, day = per_day[d]
        if totals["screen"] + totals["away"] + totals["break"] <= 0:
            lines.append(f"{d}: no activity recorded")
            continue
        for k in sums:
            sums[k] += totals[k]
        lines.append(f"{d}: screen {format_duration(totals['screen'])}, "
                     f"looking away {format_duration(totals['away'])}, "
                     f"break {format_duration(totals['break'])}, "
                     f"{day['breaks_completed']} breaks finished")
    lines += ["", f"Total looking at screen: {format_duration(sums['screen'])}",
              f"Total looking away: {format_duration(sums['away'])}",
              f"Total on a break: {format_duration(sums['break'])}",
              "Each day's full timeline is attached as an HTML file."]
    return "\n".join(lines)

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
# Report only records a look-away after it lasts at least this long.
REPORT_AWAY_MIN_SECONDS = 2.0
# A return to looking must remain stable briefly to avoid splitting one
# genuine away interval because of a single noisy frame.
REPORT_RETURN_CONFIRM_SECONDS = 0.35
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
        # v2.16: never ask for a window bigger than the screen —
        # on a short screen the buttons used to fall off the bottom.
        width = max(200, min(int(width), win.winfo_screenwidth() - 20))
        height = max(200, min(int(height), win.winfo_screenheight() - 40))
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


def fit_window(win, width, height):
    """Size a window, clamped to the screen and centred, so every
    button is on screen even on a small laptop. Returns the size used."""
    try:
        sw = win.winfo_screenwidth()
        sh = win.winfo_screenheight()
        width = max(200, min(int(width), sw - 20))
        height = max(200, min(int(height), sh - 40))
        x = max(0, (sw - width) // 2)
        y = max(0, (sh - height) // 2)
        win.geometry(f"{width}x{height}+{x}+{y}")
        return width, height
    except tk.TclError:
        return width, height


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
SETTINGS_BACKUP_FILE = APP_DIR / "screenbreak_settings.json"
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
            # v2.14: how often the report is emailed (every N days/weeks).
            "report_every": 1,
            "report_every_unit": "days",
            "report_email_enabled": False,
            "report_sender_email": "",
            "report_smtp_password": "",
            "report_cloud_url": "",
            "report_cloud_token": "",
            "report_time_zone": "America/New_York"}


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
    every, every_unit = clean_report_every(raw.get("report_every", 1),
                                           raw.get("report_every_unit", "days"))
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
        "report_enabled": False,
        "report_name": str(raw.get("report_name", "") or "").strip()[:100],
        "report_email": str(raw.get("report_email", "") or "").strip()[:200],
        "report_time": report_time,
        "report_every": every,
        "report_every_unit": every_unit,
        "report_email_enabled": False,
        "report_sender_email": str(raw.get("report_sender_email", "") or "").strip()[:200],
        "report_smtp_password": str(raw.get("report_smtp_password", "") or ""),
        "report_cloud_url": str(raw.get("report_cloud_url", "") or "").strip()[:500],
        "report_cloud_token": str(raw.get("report_cloud_token", "") or "").strip()[:200],
        "report_time_zone": str(raw.get("report_time_zone", "America/New_York") or "America/New_York").strip()[:100],
    }


def _settings_with_backup(primary=None):
    """Restore settings omitted by a version that rewrote the main state."""
    merged = {}
    saved_settings = {}
    try:
        saved = json.loads(SETTINGS_BACKUP_FILE.read_text(encoding="utf-8"))
        if isinstance(saved, dict):
            saved_settings = saved
            merged.update(saved_settings)
    except FileNotFoundError:
        pass
    except Exception as exc:
        log_error(f"could not read saved settings backup: {exc}")
    if isinstance(primary, dict):
        # Values present in the main file reflect the most recently saved
        # preferences; the sidecar fills fields an older version omitted.
        merged.update(primary)
    # An older build may have written empty values for fields it did not
    # know about. Keep the saved cloud connection unless the current build
    # explicitly saves a replacement or clears it in the sidecar.
    for key in ("report_cloud_url", "report_cloud_token", "report_time_zone"):
        if saved_settings.get(key) and not merged.get(key):
            merged[key] = saved_settings[key]
    return _normalize_settings(merged)


def _write_settings_backup(settings):
    """Atomically save settings outside the version-specific app state file."""
    try:
        APP_DIR.mkdir(parents=True, exist_ok=True)
        tmp = SETTINGS_BACKUP_FILE.with_suffix(".tmp")
        tmp.write_text(json.dumps(settings, indent=2), encoding="utf-8")
        os.replace(tmp, SETTINGS_BACKUP_FILE)
        return True
    except Exception as exc:
        print(f"ScreenBreak: could not save settings backup to {SETTINGS_BACKUP_FILE}: {exc}",
              file=sys.stderr)
        traceback.print_exc()
        return False


def load_data():
    try:
        raw = DATA_FILE.read_text(encoding="utf-8")
    except FileNotFoundError:
        return {
            "looking_seconds": 0.0, "break_required": False, "away_seconds": 0.0,
            "last_saved": time.time(), "settings": _settings_with_backup(),
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
            "last_saved": time.time(), "settings": _settings_with_backup(),
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
            "settings": _settings_with_backup(settings),
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
            "last_saved": time.time(), "settings": _settings_with_backup(),
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
        if not _write_settings_backup(settings):
            return False
        # Atomic write: write to a temp file, then replace. A crash
        # mid-write can no longer leave a half-written JSON file.
        tmp = DATA_FILE.with_suffix(".tmp")
        tmp.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        os.replace(tmp, DATA_FILE)
        return True
    except Exception as exc:
        # Never swallow this silently again — the original bug hid
        # for exactly this reason.
        print(f"ScreenBreak: could not save data to {DATA_FILE}: {exc}",
              file=sys.stderr)
        traceback.print_exc()
        return False


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


_DRAW_ORDER = ["unknown", "screen", "away", "break"]   # red/blue are drawn on top
# v2.18: the live bar shows this many hours at a time (1 hour, like
# the report); scroll sideways one hour at a time for earlier hours.
BAR_HOURS_VISIBLE = 1


def _clock_s(timestamp):
    return datetime.fromtimestamp(timestamp).strftime("%H:%M:%S")


def _half_label(timestamp):
    dt = datetime.fromtimestamp(timestamp)
    return f"{dt.hour % 12 or 12}:{dt.minute:02d}"


def _hour_starts(range_start, range_end):
    """Start time of every one-hour block from range_start to range_end."""
    starts = []
    hs = range_start
    while hs < range_end and len(starts) < 30:
        starts.append(hs)
        hs += 3600
    return starts or [range_start]


def _clip_segments(segments, seg_starts, w_start, w_end):
    """The (start, end, state) pieces of the sorted segments that fall
    inside [w_start, w_end). Nothing is smoothed or dropped, so a
    1-second look-away is still there."""
    out = []
    n = len(segments)
    i = max(0, bisect.bisect_right(seg_starts, w_start) - 3)
    while i < n and segments[i]["start"] < w_end:
        seg = segments[i]
        if seg["end"] > w_start:
            out.append((max(seg["start"], w_start), min(seg["end"], w_end), seg["state"]))
        i += 1
    return out


def update_away_run(away_run, look_confirm, looking, elapsed,
                    confirm_seconds=REPORT_RETURN_CONFIRM_SECONDS):
    """The away timer, with flicker protection. Returns
    (away_run, look_confirm, looking_is_back). Looking only ends an
    away run after `confirm_seconds` of steady looking — one noisy
    frame (a poster, a pet, a flicker) must not wipe minutes of
    looking away. Not looking — away, face not detected, camera
    error — always adds to the run. Pure, so it can be tested."""
    if looking:
        look_confirm = look_confirm + elapsed
        if look_confirm >= confirm_seconds:
            return 0.0, 0.0, True
        return away_run, look_confirm, False
    return away_run + elapsed, 0.0, False


def should_reset_screen_time(away_run, break_seconds, break_required, away_reset_done):
    """Pure decision for the reset rule: away (or face not detected)
    for the whole break time, while not already on a required break
    and not already reset for this away stretch, resets the timer."""
    if break_required or away_reset_done:
        return False
    return away_run >= float(break_seconds)


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


def _view_range(date_str, segments, now):
    """(start, end) of the hour blocks to show. With no activity yet
    that is just one block (the current hour) instead of a whole
    empty day."""
    range_start, range_end, _ = _timeline_range(date_str, segments, now)
    if not segments:
        anchor = min(now, range_end - 1) if range_end > range_start else range_start
        range_start = datetime.fromtimestamp(anchor).replace(
            minute=0, second=0, microsecond=0).timestamp()
        range_end = range_start + 3600
    return range_start, range_end


_HOUR_CSS = """
.hourhead{display:flex;align-items:center;justify-content:space-between;gap:8px;margin:14px 0 6px;}
.hourhead button{font:inherit;font-size:12px;border:0;border-radius:6px;background:#DCE7F5;color:#172B4D;padding:6px 10px;cursor:pointer;}
.hourhead button:disabled{opacity:.4;cursor:default;}
.hourtitle{font-size:13px;font-weight:700;color:#172B4D;text-align:center;flex:1;}
.scroller{overflow-x:auto;scroll-snap-type:x mandatory;}
.track{display:flex;}
.hour{flex:0 0 auto;scroll-snap-align:start;box-sizing:border-box;}
.axis{position:relative;height:34px;}
.axis .lbl{position:absolute;white-space:nowrap;}
.axis .lbl.hr{top:0;font-size:12px;font-weight:700;color:#172B4D;}
.axis .lbl.half{top:10px;font-size:10px;color:#8291A3;transform:translateX(-50%);}
.axis .tick{position:absolute;bottom:0;background:#172B4D;}
.axis .tick.hr{width:2px;height:12px;}
.axis .tick.half{width:1px;height:6px;background:#62748A;}
.bar{position:relative;height:44px;border-radius:6px;overflow:hidden;background:#E5EAF0;margin:0 0 8px;}
.bar .s{position:absolute;top:0;bottom:0;min-width:1px;}
.bar .now{position:absolute;top:0;bottom:0;width:2px;background:#172B4D;}
.hint{font-size:11px;color:#8291A3;margin:0 0 6px;}
"""


# The report's styles, shared by the on-computer report and the
# emailed reports. v2.18: the multi-day email used to drop the whole
# <style> block, so its cards, totals and legend showed unstyled in
# Gmail (plain full-width text, no white cards).
_REPORT_CSS = """body{font-family:Segoe UI,Arial,sans-serif;background:#F4F7FB;color:#172B4D;margin:0;padding:24px;}
.card{background:#fff;border-radius:12px;padding:20px 24px;margin:0 auto 16px;max-width:760px;box-shadow:0 1px 4px rgba(0,0,0,.08);}
h1{font-size:22px;margin:0 0 4px;} .sub{color:#62748A;font-size:13px;}
.live{color:#1E7B34;font-weight:700;font-size:13px;} .live-note{color:#62748A;font-size:12px;}
.summary{font-size:15px;margin:10px 0 2px;} .rightnow{font-size:13px;color:#287D55;font-weight:600;margin:2px 0 0;}
.explain{font-size:11px;color:#8291A3;display:block;margin-top:2px;}
.legend{font-size:13px;color:#52657A;}
.legend span{display:inline-block;width:12px;height:12px;border-radius:3px;margin:0 4px 0 12px;vertical-align:-1px;}
.totals{display:flex;gap:12px;flex-wrap:wrap;}
.total{flex:1;min-width:140px;background:#F4F7FB;border-radius:8px;padding:12px;}
.total b{font-size:18px;display:block;} .total span{font-size:12px;color:#62748A;}
ul{margin:8px 0 0;padding-left:20px;} li{margin:2px 0;}
""" + _HOUR_CSS

_HOUR_JS = """<script>(function(){
var sc=document.getElementById('scroller');if(!sc){return;}
var titles=__TITLES__;var n=titles.length;var key='sbHour_'+'__DATE__';
var pb=document.getElementById('prevH'),nb=document.getElementById('nextH'),tt=document.getElementById('hourtitle');
function cw(){return sc.clientWidth||1;}
function idx(){return Math.max(0,Math.min(n-1,Math.round(sc.scrollLeft/cw())));}
function show(){var i=idx();tt.textContent=titles[i]+'  ('+(i+1)+' of '+n+')';pb.disabled=(i<=0);nb.disabled=(i>=n-1);}
function go(i,smooth){i=Math.max(0,Math.min(n-1,i));try{sc.scrollTo({left:i*cw(),behavior:smooth?'smooth':'auto'});}catch(e){sc.scrollLeft=i*cw();}}
function save(){try{sessionStorage.setItem(key,idx()>=n-1?'end':String(idx()));}catch(e){}}
pb.onclick=function(){go(idx()-1,true);};nb.onclick=function(){go(idx()+1,true);};
var start=n-1;try{var sv=sessionStorage.getItem(key);if(sv&&sv!=='end'){var k=parseInt(sv,10);if(k>=0&&k<n){start=k;}}}catch(e){}
go(start,false);show();
sc.addEventListener('scroll',function(){show();save();});
sc.addEventListener('click',function(e){var t=e.target.closest?e.target.closest('.s'):null;if(t){var el=document.getElementById('seginfo');if(el){el.textContent='\u25cf '+t.getAttribute('title');}}});
window.addEventListener('resize',function(){go(idx(),false);});
})();</script>"""


def html_body_fragment(full_html):
    """The <body>...</body> content of a report we generated, so a
    full report can be placed inside another email body. Pure."""
    try:
        return full_html.split("<body>", 1)[1].rsplit("</body>", 1)[0]
    except (IndexError, AttributeError):
        return full_html


def _build_hour_scroller_html(date_str, segments, range_start, range_end, now, is_today):
    """The report timeline: one block per hour, each as wide as the
    page, so you see one hour at a time and scroll sideways for the
    earlier ones — one wide bar with a tall line at the hour and a
    short line at 30 minutes, like the live bar. Every segment is
    drawn at its true width (a 10-minute block looks twice as wide
    as a 5-minute one), floored at 1 pixel so a 1-second look-away
    is still a visible red line."""
    starts = _hour_starts(range_start, range_end)
    seg_starts = [seg["start"] for seg in segments]
    blocks = []
    titles = []
    for hs in starts:
        he = hs + 3600
        layers = {}
        for seg_s, seg_e, seg_state in _clip_segments(segments, seg_starts, hs, he):
            layers.setdefault(seg_state, []).append((seg_s, seg_e))
        parts = []
        for st in _DRAW_ORDER:
            colour = STATE_COLORS[st]
            label = STATE_LABELS[st]
            for seg_s, seg_e in layers.get(st, []):
                left = (seg_s - hs) / 3600.0 * 100.0
                width = (seg_e - seg_s) / 3600.0 * 100.0
                parts.append(
                    f'<div class="s" title="{label}: {_clock_s(seg_s)}–{_clock_s(seg_e)} '
                    f'({format_duration(seg_e - seg_s)})" '
                    f'style="left:{left:.3f}%;width:{width:.3f}%;background:{colour};"></div>')
        now_html = ""
        if is_today and hs <= now < he:
            now_html = f'<div class="now" style="left:{(now - hs) / 3600.0 * 100.0:.3f}%;"></div>'
        axis = (f'<div class="tick hr" style="left:0"></div>'
                f'<div class="lbl hr" style="left:3px">{_hour_label(hs)}</div>'
                f'<div class="tick half" style="left:50%"></div>'
                f'<div class="lbl half" style="left:50%">{_half_label(hs + 1800)}</div>')
        # v2.17: one hour fills the whole page (the live bar still
        # shows 3 hours at a time; the report shows 1).
        blocks.append(f'<div class="hour" style="flex:0 0 100.000%"><div class="axis">{axis}</div>'
                      f'<div class="bar">{"".join(parts)}{now_html}</div></div>')
        titles.append(f"{_hour_label(hs)} – {_hour_label(he)}")
    html = ('<div class="hourhead"><button id="prevH" type="button">&#9664; Earlier hour</button>'
            '<span id="hourtitle" class="hourtitle"></span>'
            '<button id="nextH" type="button">Later hour &#9654;</button></div>'
            '<div class="scroller" id="scroller"><div class="track">' + "".join(blocks) +
            '</div></div>'
            '<div class="hint">Showing one hour at a time. Scroll sideways (or use the buttons) for earlier hours. '
            'Tall line = each hour, short line = each 30 minutes. Bars are drawn at their true width, so a '
            '10-minute bar looks twice as wide as a 5-minute one.</div>')
    script = (_HOUR_JS.replace("__TITLES__", json.dumps(titles))
              .replace("__DATE__", date_str))
    return html, script


def build_report_html(date_str, settings, totals, day, open_segment=None, email_mode=False, all_days=None):
    """Daily report as a self-contained HTML page: a timeline bar
    (green screen / red distracted / blue break / grey not tracked),
    totals, and the list of breaks."""
    name = (settings.get("report_name") or "").strip() or "Student"
    name = html_lib.escape(name)
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
    # v2.10/v2.17: the report shows ONE hour at a time (the newest);
    # scroll sideways for earlier hours. Nothing is smoothed: every
    # look-away is drawn at its true width, when it lasts at least
    # 2 seconds, floored at 1 pixel so it stays visible.
    # v2.19: the EMAILED report is different — Gmail strips the
    # JavaScript the hour buttons need, so the email version shows
    # one hour at a time in a sideways-scrolling strip (600px per
    # hour), with the same hours, 30-minute lines, colours and
    # segments as the app. It never auto-reloads.
    range_start, range_end = _view_range(date_str, segments, now)
    if email_mode:
        hour_html = build_email_timeline_html(
            date_str, segments, range_start, range_end, now, is_today)
        hour_script = ""
    else:
        hour_html, hour_script = _build_hour_scroller_html(
            date_str, segments, range_start, range_end, now, is_today)
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
    if email_mode:
        # An email must never reload itself. It carries no JavaScript
        # any more (v2.22): nothing in the email uses the click /
        # search script, and Gmail strips scripts out of emails
        # anyway — the attached all-reports.html is the fully
        # working copy there.
        live_head = ""
        live_badge = '<span class="live-note">Sent by email.</span>' 
        live_script = ""
    elif is_today:
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
    # v2.15: click a bar to keep its length shown (file mode), and the
    # All reports list (email mode only — the live file stays light).
    seginfo_html = ('<div id="seginfo" style="font-size:13px;color:#287D55;font-weight:600;margin:6px 0 0;">'
                    'Hover over a coloured bar to see how long it lasted \u2014 or click it to keep it shown here.</div>') if not email_mode else ""
    # Email contains only the selected report; the local All Reports
    # feature remains available inside ScreenBreak.
    all_reports_html = ""
    return f"""<!DOCTYPE html>
<html><head><meta charset="utf-8">{live_head}<title>ScreenBreak daily report — {name} — {date_str}</title>
<style>
{_REPORT_CSS}</style></head><body>
<div class="card"><h1>ScreenBreak daily report — {name}</h1>
<div class="sub">{date_str} &bull; generated {generated} &bull; green = looking at screen, red = looked away for less than the break time (when it lasts at least 2 seconds), blue = away for a full break (screen time reset to 0), grey = not tracked, pale grey = app was off</div>
<div style="margin-top:6px;">{live_badge}</div>
<div class="summary">{summary}</div>
{right_now_html}
{hour_html}
{seginfo_html}
<div class="legend"><span style="background:#2E9E5B"></span>Screen<span style="background:#D64541"></span>Short look-away<span style="background:#2F7ED8"></span>Full break<span style="background:#9AA5B1"></span>Not tracked<span style="background:#E5EAF0;border:1px solid #CBD5E1"></span>App was off</div></div>
<div class="card"><div class="totals">
<div class="total"><b>{format_duration(totals["screen"])}</b><span>🟢 Looking at screen</span><span class="explain">Time looking at the screen.</span></div>
<div class="total"><b>{format_duration(totals["away"])}</b><span>🔴 Looked away (short)</span><span class="explain">Time looking away in stretches shorter than the break time.</span></div>
<div class="total"><b>{format_duration(totals["break"])}</b><span>🔵 Away for a full break</span><span class="explain">Time away for at least the break time. Screen time went back to 0.</span></div>
<div class="total"><b>{day["breaks_completed"]}</b><span>Breaks finished</span><span class="explain">Breaks you finished.</span></div>
<div class="total"><b>{day["strikes"]}</b><span>Peeks during breaks</span><span class="explain">Times you looked at the screen during a break.</span></div>
</div>
<p style="color:#62748A;font-size:13px;">Longest time looking at the screen without a break: {format_duration(_longest_stretch(segments, "screen"))}. Longest single break: {format_duration(_longest_stretch(segments, "break"))}.</p></div>
{all_reports_html}
<div class="card"><h2 style="font-size:16px;margin:0 0 4px;">Breaks today</h2><ul>{breaks_html}</ul></div>
{live_script}
{hour_script}
</body></html>"""


def build_report_text(date_str, settings, totals, day):
    name = (settings.get("report_name") or "").strip() or "Student"
    return (f"ScreenBreak daily report — {name} — {date_str}\n"
            f"Looking at screen: {format_duration(totals['screen'])}\n"
            f"Distracted (looking away): {format_duration(totals['away'])}\n"
            f"On a break: {format_duration(totals['break'])}\n"
            f"Breaks finished: {day['breaks_completed']}\n"
            f"Peeks during breaks: {day['strikes']}\n"
            f"The full timeline is shown in the report above.")


def send_cloud_email_request(settings, payload, timeout=30):
    """Send a small authenticated HTTPS request to the user's Apps Script.
    Gmail authorization and scheduled sending happen in Google's service;
    no Gmail app password is sent or stored there."""
    endpoint = (settings.get("report_cloud_url") or "").strip()
    token = (settings.get("report_cloud_token") or "").strip()
    if not endpoint.startswith("https://script.google.com/"):
        return False, "Enter the HTTPS Google Apps Script web-app URL.", None
    if not token:
        return False, "Enter the access key shown by the Apps Script setup.", None
    body = dict(payload)
    body["token"] = token
    request = urllib.request.Request(
        endpoint,
        data=json.dumps(body, ensure_ascii=False).encode("utf-8"),
        headers={"Content-Type": "text/plain; charset=utf-8"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            result = json.loads(response.read().decode("utf-8"))
        if not result.get("ok"):
            return False, str(result.get("error") or "The online email service rejected the request."), result
        return True, "", result
    except urllib.error.HTTPError as exc:
        try:
            detail = exc.read().decode("utf-8", "replace")[:500]
        except Exception:
            detail = str(exc)
        return False, f"Google returned HTTP {exc.code}: {detail}", None
    except Exception as exc:
        return False, str(exc), None


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
        "face_detected": False,
        "looking_streak": 0.0,
        "glance_counted": False,
        "long_look_reset_done": False,
        "continuous_away": 0.0,
        # v2.9: continuous seconds the kid has been away (or not there)
        # with the camera working, and whether this away stretch already
        # reset the screen time.
        "away_run": 0.0,
        "away_reset_done": False,
        # v2.16: seconds of steady looking in a row — the away run
        # only ends once this reaches the confirm time (see
        # update_away_run), so one flicker frame cannot wipe it.
        "look_confirm": 0.0,
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
        "last_cloud_sync": 0.0,
        # v2.6: live report + live bar timing.
        "last_live_regen": 0.0,
        "last_bar_draw": 0.0,
        # Daily timeline tracking. Raw camera classifications must remain
        # stable briefly before they become report activity, preventing
        # one-frame flicker from creating false red slivers.
        "current_segment_state": None,
        "current_segment_start": None,
        "pending_segment_state": None,
        "pending_segment_start": None,
        "segments_date": day_key(),
        "today_totals": daily_totals(day_key())[0],
    }

    root = tk.Tk()
    root.title("ScreenBreak")
    # v2.5: taller again, for the progress bars, the Today summary
    # and the View report button.
    # v2.16: wider so all five buttons fit in one row (they used to
    # overflow the 470px window and the last ones were cut off), and
    # clamped to the screen, centred, so nothing falls off the edge.
    root.geometry("560x620")
    root.minsize(520, 560)
    fit_window(root, 560, 620)
    # v2.5: start minimized when launched automatically at sign-in.
    if "--minimized" in sys.argv or "--startup" in sys.argv:
        try:
            root.iconify()
        except tk.TclError:
            pass
    root.configure(bg="#F4F7FB")

    title = tk.Label(root, text="ScreenBreak", font=("Segoe UI", 23, "bold"),
                     fg="#172B4D", bg="#F4F7FB")
    title.pack(pady=(12, 2))
    subtitle = tk.Label(root, text="Counts your screen time with the camera\nand reminds you to take a break.",
                        font=("Segoe UI", 10), fg="#62748A", bg="#F4F7FB", justify="center")
    subtitle.pack()

    status = tk.Label(root, text="Starting camera…", font=("Segoe UI", 14, "bold"),
                      fg="#B7791F", bg="#F4F7FB", wraplength=400, justify="center")
    status.pack(pady=(12, 6))
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
    tk.Label(root, text="This hour — live  (dark line = now, scroll left for earlier hours)",
             font=("Segoe UI", 10, "bold"), fg="#172B4D", bg="#F4F7FB").pack(pady=(6, 0))
    today_canvas = tk.Canvas(root, height=48, bg="#F4F7FB", highlightthickness=0)
    today_canvas.pack(fill="x", padx=20, pady=(0, 0))
    today_scroll = ttk.Scrollbar(root, orient="horizontal", command=today_canvas.xview)
    today_scroll.pack(fill="x", padx=20, pady=(0, 2))
    today_canvas.configure(xscrollcommand=today_scroll.set)
    # v2.8: the live bar means nothing without a legend. Say what
    # each colour is, in words, right underneath it.
    tk.Label(root, text="Green = looking at the screen  •  Red = looked away for less than the break time (when it lasts at least 2 seconds)  •  Blue = away for the full break (screen time resets to 0)  •  Grey = camera can't see you",
             font=("Segoe UI", 9), fg="#62748A", bg="#F4F7FB",
             wraplength=430, justify="center").pack(pady=(0, 2))
    # v2.15: hovering or clicking a coloured bar shows how long it lasted.
    bar_info = tk.Label(root, text="Hover over a coloured bar to see how long it lasted \u2014 click it to keep it shown.",
                        font=("Segoe UI", 9), fg="#287D55", bg="#F4F7FB", wraplength=430, justify="center")
    bar_info.pack(pady=(0, 2))
    hint = tk.Label(root, text="ScreenBreak runs quietly while this window is open.",
                    font=("Segoe UI", 9), fg="#62748A", bg="#F4F7FB", wraplength=380)
    hint.pack(pady=8)

    controls = tk.Frame(root, bg="#F4F7FB")
    controls.pack(pady=6)
    camera_button = tk.Button(controls, text="Show camera", width=12,
                              command=lambda: toggle_camera(), relief="flat",
                              bg="#DCE7F5", fg="#172B4D", padx=8, pady=7)
    camera_button.grid(row=0, column=0, padx=3)
    settings_button = tk.Button(controls, text="Settings", width=9,
                                command=lambda: open_settings(), relief="flat",
                                bg="#DCE7F5", fg="#172B4D", padx=8, pady=7)
    settings_button.grid(row=0, column=1, padx=3)
    # v2.5: open today's report in the browser.
    report_button = tk.Button(controls, text="Today's report", width=12,
                              command=lambda: view_today_report(), relief="flat",
                              bg="#DCE7F5", fg="#172B4D", padx=8, pady=7)
    report_button.grid(row=0, column=2, padx=3)
    all_reports_button = tk.Button(controls, text="All reports", width=10,
                                   command=lambda: open_all_reports(), relief="flat",
                                   bg="#DCE7F5", fg="#172B4D", padx=8, pady=7)
    all_reports_button.grid(row=0, column=3, padx=3)
    # v2.8: reopen the first-run explanation any time.
    how_button = tk.Button(controls, text="How it works", width=11,
                           command=lambda: show_welcome_window(), relief="flat",
                           bg="#DCE7F5", fg="#172B4D", padx=8, pady=7)
    how_button.grid(row=0, column=4, padx=3)
    reset_button = tk.Button(root, text="Reset screen time", command=lambda: reset_with_confirmation(),
                             relief="flat", bg="#FCE8E6", fg="#A12B24",
                             padx=14, pady=7)
    reset_button.pack(pady=(2, 4))
    tk.Label(root, text="Your camera is processed on this computer. No video is saved.",
             font=("Segoe UI", 8), fg="#8291A3", bg="#F4F7FB").pack(side="bottom", pady=8)

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
        report_break_threshold = (
            float(settings["break_seconds"]) + state["break_extension_seconds"] + SETTLE_SECONDS
            if state["break_required"] else float(settings["break_seconds"])
        )
        if startup_gap >= report_break_threshold:
            gap_state = "break"
        elif startup_gap >= REPORT_AWAY_MIN_SECONDS:
            gap_state = "away"
        else:
            gap_state = None
        if gap_end > saved["last_saved"] and gap_state is not None:
            append_segment_spanning(saved["last_saved"], gap_end, gap_state)
        state["today_totals"], _ = daily_totals(state["segments_date"])
        # The app was not running during this interval. Carry that
        # confirmed-away time into the automatic reset rule as well.
        if not state["break_required"]:
            state["away_run"] = startup_gap
            if startup_gap >= float(settings["break_seconds"]):
                state["looking_seconds"] = 0.0
                state["away_reset_done"] = True
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
        state["look_confirm"] = 0.0

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

    def _maybe_reset_screen_time():
        """v2.9/v2.16: if the kid has been away — looking away OR face
        not detected — for the whole break length, screen time goes
        back to 0 and starts counting again. Works any time, not only
        after the screen limit. Returns True if it reset just now.
        If the timer was already at 0 there is nothing to reset, but
        the stretch is still marked done so the status line says so
        instead of counting down from 0."""
        if not should_reset_screen_time(state["away_run"], float(settings["break_seconds"]),
                                        state["break_required"], state["away_reset_done"]):
            return False
        state["away_reset_done"] = True
        had_screen_time = state["looking_seconds"] > 0
        state["looking_seconds"] = 0.0
        if had_screen_time:
            bump_day_counter(day_key(), "breaks_completed", 1)
        status.config(text="Break done — screen time is back at 0.", fg="#2F7ED8")
        hint.config(text="You were away for the whole break, so screen time started over.")
        save_data(state)
        return True

    def complete_break():
        """Reset the next screen-time cycle immediately. Shared by the
        normal tick path and the sleep-gap path so they cannot drift."""
        # v2.5: count the finished break in today's report.
        bump_day_counter(day_key(), "breaks_completed", 1)
        state["break_required"] = False
        state["away_seconds"] = 0.0
        state["looking_seconds"] = 0.0
        state["away_reset_done"] = True
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
        fit_window(win, 680, 420)
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

    def _generate_email_report(end_date_str, report_settings=None):
        """Build the emailed report without the local All reports
        history or its all-reports.html attachment.
        Returns (subject, html, plain, attachments)."""
        use_settings = report_settings if report_settings is not None else settings
        n_days = report_period_days(use_settings)
        name = (use_settings.get("report_name") or "").strip() or "Student"
        end_day = datetime.strptime(end_date_str, "%Y-%m-%d").date()
        open_seg = None
        if (state.get("current_segment_state") is not None
                and end_date_str == state["segments_date"]):
            open_seg = (state["current_segment_start"], state["current_segment_state"])
        totals, day = daily_totals(end_date_str, open_segment=open_seg)
        email_html = build_report_html(end_date_str, use_settings, totals, day,
                                       open_segment=open_seg, email_mode=True, all_days=[])
        plain = build_report_text(end_date_str, use_settings, totals, day)
        attachments = []
        if n_days == 1:
            subject = f"ScreenBreak daily report \u2014 {name} \u2014 {end_date_str}"
            return subject, email_html, plain, attachments
        dates = [(end_day - timedelta(days=i)).strftime("%Y-%m-%d")
                 for i in range(n_days - 1, -1, -1)]
        per_day, size = {}, 0
        for d in dates:
            o_seg = open_seg if d == end_date_str else None
            per_day[d] = daily_totals(d, open_segment=o_seg)
            if per_day[d][0]["screen"] + per_day[d][0]["away"] + per_day[d][0]["break"] > 0:
                _, day_html, _ = _generate_report(d, use_settings)
                if size + len(day_html) < 15 * 1024 * 1024:
                    attachments.append((f"report-{d}.html", day_html))
                    size += len(day_html)
        period_html = build_period_report_html(dates, per_day, use_settings)
        period_plain = build_period_report_text(dates, per_day, use_settings)
        subject = (f"ScreenBreak {report_period_name(n_days)} report \u2014 {name} \u2014 "
                   f"{dates[0]} to {dates[-1]}")
        # v2.18: the multi-day email used to leave the <style> out
        # entirely, so Gmail showed the report unstyled. Include it.
        html = ("<!DOCTYPE html><html><head><meta charset=\"utf-8\">"
                f"<title>{subject}</title><style>{_REPORT_CSS}</style></head><body>"
                + period_html + html_body_fragment(email_html)
                + "</body></html>")
        plain = period_plain + "\n\n" + plain
        return subject, html, plain, attachments

    def _generate_period_report(end_date_str, report_settings=None):
        """Kept for callers: the emailed report (see _generate_email_report)."""
        return _generate_email_report(end_date_str, report_settings)

    def _cloud_report_payload(use_settings, action="sync"):
        today = day_key()
        subject, report_html, plain, attachments = _generate_period_report(today, use_settings)
        return {
            "action": action,
            "settings": {
                "enabled": bool(use_settings.get("report_email_enabled")),
                "recipient": use_settings.get("report_email", ""),
                "report_name": use_settings.get("report_name", ""),
                "report_time": use_settings.get("report_time", "18:00"),
                "report_every": int(use_settings.get("report_every", 1)),
                "report_every_unit": use_settings.get("report_every_unit", "days"),
                "time_zone": use_settings.get("report_time_zone", "America/New_York"),
                "last_report_date": state.get("last_report_date", ""),
            },
            "report": {
                "date": today,
                "subject": subject,
                "html": report_html,
                "plain": plain,
                "attachments": [
                    {"filename": filename, "html": content}
                    for filename, content in attachments
                ],
            },
        }

    def _cloud_sync_async(use_settings, action="sync", callback=None):
        settings_copy = dict(use_settings)

        def _worker():
            try:
                payload = _cloud_report_payload(settings_copy, action)
                ok, err, response = send_cloud_email_request(settings_copy, payload)
            except Exception as exc:
                ok, err, response = False, str(exc), None
                log_error(f"cloud report sync failed: {exc}")

            def _finish():
                if ok and response:
                    sent_date = response.get("last_report_date", "")
                    if sent_date:
                        state["last_report_date"] = sent_date
                        save_data(state)
                elif not ok:
                    log_error(f"cloud report sync failed: {err}")
                if callback:
                    try:
                        callback(ok, err, response)
                    except tk.TclError:
                        pass

            try:
                root.after(0, _finish)
            except tk.TclError:
                pass

        threading.Thread(target=_worker, daemon=True).start()

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

    def open_all_reports():
        """Let the user search saved dates and open any day's visual bar report."""
        win = tk.Toplevel(root)
        win.title("All reports")
        win.geometry("700x560")
        fit_window(win, 700, 560)
        win.resizable(True, True)
        win.configure(bg="#F4F7FB")
        win.transient(root)

        tk.Label(win, text="All reports", font=("Segoe UI", 16, "bold"),
                 fg="#172B4D", bg="#F4F7FB").pack(pady=(16, 4))
        tk.Label(win, text="Search for a date or choose a saved report.",
                 font=("Segoe UI", 9), fg="#62748A", bg="#F4F7FB").pack(pady=(0, 10))

        search_var = tk.StringVar()
        search_entry = tk.Entry(win, textvariable=search_var, font=("Segoe UI", 11))
        search_entry.pack(fill="x", padx=18, pady=(0, 10))
        search_entry.insert(0, "")
        list_frame = tk.Frame(win, bg="#F4F7FB")
        list_frame.pack(fill="both", expand=True, padx=18, pady=(0, 10))
        scrollbar = ttk.Scrollbar(list_frame, orient="vertical")
        report_list = tk.Listbox(list_frame, font=("Segoe UI", 11),
                                 activestyle="dotbox", yscrollcommand=scrollbar.set,
                                 height=6, exportselection=False)
        scrollbar.config(command=report_list.yview)
        scrollbar.pack(side="right", fill="y")
        report_list.pack(side="left", fill="both", expand=True)

        def saved_dates():
            try:
                dates = []
                for file_path in DAILY_DIR.glob("*.json"):
                    date_text = file_path.stem
                    try:
                        datetime.strptime(date_text, "%Y-%m-%d")
                    except ValueError:
                        continue
                    dates.append(date_text)
                today = day_key()
                if today not in dates and _day_file(today).exists():
                    dates.append(today)
                return sorted(set(dates), reverse=True)
            except Exception as exc:
                log_error(f"could not list saved reports: {exc}")
                return []

        all_dates = saved_dates()

        def refresh_list(*_):
            query = search_var.get().strip().lower()
            report_list.delete(0, tk.END)
            matches = [d for d in all_dates if query in d or query in datetime.strptime(d, "%Y-%m-%d").strftime("%B %d, %Y").lower()]
            for date_text in matches:
                report_list.insert(tk.END, datetime.strptime(date_text, "%Y-%m-%d").strftime("%B %d, %Y"))
            if matches:
                report_list.selection_set(0)
            return matches

        visible_dates = refresh_list()
        sel_label = tk.Label(win, text="", font=("Segoe UI", 9), fg="#287D55",
                             bg="#F4F7FB", wraplength=640, justify="center")
        sel_label.pack(fill="x", padx=18, pady=(0, 4))

        # v2.20: the report for the selected day, right here in this
        # window — one hour at a time, scrolling sideways (scrollbar,
        # mouse wheel or drag), like the live bar in the main window
        # and the on-computer report. Clicking a date used to only
        # show its totals here and open the report in the browser.
        bar_hour_label = tk.Label(win, text="", font=("Segoe UI", 10, "bold"),
                                  fg="#172B4D", bg="#F4F7FB")
        bar_hour_label.pack(fill="x", padx=18, pady=(6, 0))
        bar_frame = tk.Frame(win, bg="#F4F7FB")
        bar_frame.pack(fill="x", padx=18, pady=(2, 0))
        report_canvas = tk.Canvas(bar_frame, height=48, bg="white",
                                  highlightthickness=1, highlightbackground="#CBD5E1")
        report_hbar = ttk.Scrollbar(bar_frame, orient="horizontal")
        report_canvas.pack(side="top", fill="x")
        report_hbar.pack(side="top", fill="x")
        bar_info = tk.Label(win, text="Hover over a coloured bar to see how long it lasted \u2014 click it to keep it shown.",
                            font=("Segoe UI", 9), fg="#62748A", bg="#F4F7FB", wraplength=640, justify="center")
        bar_info.pack(fill="x", padx=18, pady=(4, 0))
        bar = {"items": [], "hour_w": 0.0, "total_w": 0.0, "hours": [], "pinned": False, "press": None}

        def _report_visible_hour():
            try:
                total = bar["total_w"]
                hw = bar["hour_w"]
                hours = bar["hours"]
                if not hours or total <= 0 or hw <= 0:
                    return 0
                lo, _ = report_canvas.xview()
                idx = int(round(lo * total / float(hw)))
                return max(0, min(len(hours) - 1, idx))
            except Exception:
                return 0

        def _report_hour_text():
            hours = bar["hours"]
            if not hours:
                return ""
            idx = _report_visible_hour()
            label = _hour_label(hours[idx])
            if len(hours) > 1:
                return f"Showing {label} \u2014 scroll sideways for other hours"
            return f"Showing {label}"

        def _on_report_xscroll(first, last):
            report_hbar.set(first, last)
            bar_hour_label.config(text=_report_hour_text())

        report_canvas.configure(xscrollcommand=_on_report_xscroll)
        report_hbar.configure(command=report_canvas.xview)

        def _clear_report_bar():
            report_canvas.delete("all")
            bar["items"] = []
            bar["hour_w"] = 0.0
            bar["total_w"] = 0.0
            bar["hours"] = []
            bar["pinned"] = False
            bar_hour_label.config(text="")
            bar_info.config(text="Hover over a coloured bar to see how long it lasted \u2014 click it to keep it shown.")

        def _draw_report_bar(follow=False):
            """Draw the selected day's timeline: one hour fills the
            canvas, the rest scrolls sideways."""
            try:
                sel = report_list.curselection()
                if not sel:
                    _clear_report_bar()
                    return
                matches = [d for d in all_dates if search_var.get().strip().lower() in d or search_var.get().strip().lower() in datetime.strptime(d, "%Y-%m-%d").strftime("%B %d, %Y").lower()]
                if not matches or sel[0] >= len(matches):
                    _clear_report_bar()
                    return
                date_text = matches[sel[0]]
                vw = report_canvas.winfo_width()
                if vw <= 1:
                    return
                now = time.time()
                day = load_day(date_text)
                segments = list(day["segments"])
                if (state.get("current_segment_state") is not None
                        and date_text == state["segments_date"]):
                    segments.append({"start": state["current_segment_start"],
                                     "end": now,
                                     "state": state["current_segment_state"]})
                segments.sort(key=lambda s: s["start"])
                rs, re_ = _view_range(date_text, segments, now)
                hours = _hour_starts(rs, re_)
                n = len(hours)
                hour_w = float(vw)
                total_w = n * hour_w
                # Keep the hour the person was looking at, unless
                # following the newest hours (a new selection).
                lo, hi = report_canvas.xview()
                old_total = bar["total_w"]
                old_hw = bar["hour_w"]
                last_page = max(0, n - 1)
                keep_idx = int(round(lo * old_total / max(1.0, old_hw))) if old_total > 0 else last_page
                report_canvas.delete("all")
                bar["items"] = []
                report_canvas.configure(scrollregion=(0, 0, total_w, 48))
                target = last_page if follow else max(0, min(last_page, keep_idx))
                report_canvas.xview_moveto(target * hour_w / float(total_w))
                bar["total_w"] = total_w
                bar["hour_w"] = hour_w
                bar["hours"] = hours
                if not segments:
                    bar_info.config(text="No activity recorded on this day.")
                elif not bar["pinned"]:
                    bar_info.config(text="Hover over a coloured bar to see how long it lasted \u2014 click it to keep it shown.")
                bar["pinned"] = False
                seg_starts = [sg["start"] for sg in segments]
                for i, hs in enumerate(hours):
                    x0 = i * hour_w
                    he = hs + 3600
                    layers = {}
                    for seg_s, seg_e, seg_state in _clip_segments(segments, seg_starts, hs, he):
                        layers.setdefault(seg_state, []).append((seg_s, seg_e))
                    report_canvas.create_rectangle(x0, 20, x0 + hour_w, 46, fill="#E5EAF0", outline="")
                    for st in _DRAW_ORDER:
                        colour = STATE_COLORS[st]
                        for seg_s, seg_e in layers.get(st, []):
                            xa = x0 + (seg_s - hs) / 3600.0 * hour_w
                            xb = x0 + (seg_e - hs) / 3600.0 * hour_w
                            # True width, floored at 1 pixel so a
                            # 2-second look-away is a thin line.
                            if xb - xa < 1:
                                xb = xa + 1
                            report_canvas.create_rectangle(xa, 20, xb, 46, fill=colour, outline="")
                            bar["items"].append((max(x0, xa - 2.0),
                                               min(x0 + hour_w, xb + 2.0),
                                               seg_title(st, seg_s, seg_e)))
                    report_canvas.create_line(x0 + 1, 14, x0 + 1, 20, fill="#172B4D", width=2)
                    report_canvas.create_text(x0 + 4, 7, text=_hour_label(hs, long_form=False),
                                             font=("Segoe UI", 8, "bold"), fill="#172B4D", anchor="w")
                    xm = x0 + hour_w / 2.0
                    report_canvas.create_line(xm, 17, xm, 20, fill="#62748A", width=1)
                    report_canvas.create_text(xm, 8, text=_half_label(hs + 1800),
                                             font=("Segoe UI", 7), fill="#8291A3")
                    if date_text == day_key() and hs <= now < he:
                        nx = x0 + (now - hs) / 3600.0 * hour_w
                        report_canvas.create_line(nx, 16, nx, 48, fill="#172B4D", width=2)
                bar_hour_label.config(text=_report_hour_text())
            except Exception:
                traceback.print_exc()

        def _report_hover(event):
            try:
                if bar["pinned"]:
                    return
                cx = report_canvas.canvasx(event.x)
                if not (20 <= event.y <= 46):
                    bar_info.config(text="Hover over a coloured bar to see how long it lasted \u2014 click it to keep it shown.")
                    return
                for xa, xb, title in bar["items"]:
                    if xa <= cx < xb:
                        bar_info.config(text="\u25cf " + title)
                        return
                bar_info.config(text="Hover over a coloured bar to see how long it lasted \u2014 click it to keep it shown.")
            except Exception:
                pass

        def _report_press(event):
            bar["press"] = (event.x, event.y)
            bar["pinned"] = False
            try:
                report_canvas.scan_mark(event.x, 0)
            except Exception:
                pass

        def _report_drag(event):
            try:
                report_canvas.scan_dragto(event.x, 0, gain=1)
                bar_hour_label.config(text=_report_hour_text())
            except Exception:
                pass

        def _report_release(event):
            try:
                press = bar["press"]
                if press is None:
                    return
                if abs(event.x - press[0]) < 4 and abs(event.y - press[1]) < 4:
                    cx = report_canvas.canvasx(event.x)
                    if 20 <= event.y <= 46:
                        for xa, xb, title in bar["items"]:
                            if xa <= cx < xb:
                                bar["pinned"] = True
                                bar_info.config(text="\u25cf " + title)
                                return
            except Exception:
                pass

        def _report_wheel(event):
            """Mouse wheel over the bar moves one hour at a time."""
            try:
                total = bar["total_w"]
                hw = bar["hour_w"]
                if total <= 0 or hw <= 0:
                    return
                n = max(1, int(round(total / float(hw))))
                lo, _ = report_canvas.xview()
                idx = int(round(lo * total / float(hw))) + (-1 if event.delta > 0 else 1)
                idx = max(0, min(max(0, n - 1), idx))
                report_canvas.xview_moveto(idx * hw / float(total))
                bar_hour_label.config(text=_report_hour_text())
            except Exception:
                traceback.print_exc()

        report_canvas.bind("<Motion>", _report_hover)
        report_canvas.bind("<ButtonPress-1>", _report_press)
        report_canvas.bind("<B1-Motion>", _report_drag)
        report_canvas.bind("<ButtonRelease-1>", _report_release)
        report_canvas.bind("<MouseWheel>", _report_wheel)
        report_canvas.bind("<Configure>", lambda _e: _draw_report_bar())

        def _show_selected_totals(*_):
            sel = report_list.curselection()
            if not sel:
                sel_label.config(text="")
                _clear_report_bar()
                return
            query = search_var.get().strip().lower()
            matches = [d for d in all_dates if query in d or query in datetime.strptime(d, "%Y-%m-%d").strftime("%B %d, %Y").lower()]
            if sel[0] >= len(matches):
                return
            date_text = matches[sel[0]]
            totals, day = daily_totals(date_text)
            sel_label.config(text=f"{datetime.strptime(date_text, '%Y-%m-%d').strftime('%b %d, %Y')}: screen {format_duration(totals['screen'])} \u00b7 short away {format_duration(totals['away'])} \u00b7 break {format_duration(totals['break'])} \u00b7 {day['breaks_completed']} breaks finished")
            # v2.20: a new selection shows that day's report, newest hour first.
            _draw_report_bar(follow=True)

        report_list.bind("<<ListboxSelect>>", _show_selected_totals)
        _show_selected_totals()
        search_var.trace_add("write", lambda *_: _show_selected_totals())

        def open_selected():
            selection = report_list.curselection()
            if not selection:
                messagebox.showinfo("Choose a report", "Select a date first.", parent=win)
                return
            matches = [d for d in all_dates if search_var.get().strip().lower() in d or search_var.get().strip().lower() in datetime.strptime(d, "%Y-%m-%d").strftime("%B %d, %Y").lower()]
            if not matches:
                return
            date_text = matches[selection[0]]
            path, _, _ = _generate_report(date_text)
            if path is not None:
                try:
                    webbrowser.open(path.as_uri())
                except Exception as exc:
                    log_error(f"could not open report {date_text}: {exc}")
                    messagebox.showerror("Couldn't open report", "The report was saved, but your browser couldn't open it.", parent=win)
            else:
                messagebox.showerror("Couldn't open report", "ScreenBreak couldn't create that report.", parent=win)

        search_var.trace_add("write", refresh_list)
        report_list.bind("<Double-Button-1>", lambda _event: open_selected())
        tk.Button(win, text="Open selected report", command=open_selected,
                  relief="flat", bg="#DCE7F5", fg="#172B4D",
                  font=("Segoe UI", 10, "bold"), padx=12, pady=8).pack(pady=(0, 14))
        win.update_idletasks()
        _draw_report_bar(follow=True)
        search_entry.focus_set()

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
             "It only counts the time you are actually looking at the screen. Looking away pauses the count. Look away (or leave) for the whole break time and screen time goes back to 0 and starts again."),
            ("2. After " + format_duration(target_seconds()) + " of looking, it asks for a break.",
             "Take a break of " + format_duration(int(settings["break_seconds"])) + " or more. Look away from the screen — that is what counts."),
            ("3. Peeking pauses the break.",
             "If you look at the screen during a break, the break pauses. Peek 3 times and the break gets longer."),
            ("4. The colours.",
             "Green = looking at the screen. Red = looked away for less than the break time, even for 1 second. Blue = away for the full break time, so screen time went back to 0. Grey = the camera can't see you."),
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
        # v2.5: tabbed Settings — Break rules, Auto-start, Email report.
        # v2.16: the window fits the screen, and the whole thing
        # scrolls, so the Save/Cancel buttons are always reachable
        # even on a short laptop screen (at 720px tall they used to
        # fall off the bottom).
        win.minsize(460, 400)
        win.configure(bg="#F4F7FB")
        fit_window(win, 480, 720)
        _settings_scroll = ttk.Scrollbar(win, orient="vertical")
        _settings_canvas = tk.Canvas(win, bg="#F4F7FB", highlightthickness=0,
                                     yscrollcommand=_settings_scroll.set)
        _settings_scroll.config(command=_settings_canvas.yview)
        _settings_scroll.pack(side="right", fill="y")
        settings_footer = tk.Frame(win, bg="#F4F7FB", bd=0,
                                   highlightthickness=1, highlightbackground="#D7E0EA")
        settings_footer.pack(side="bottom", fill="x")
        _settings_canvas.pack(side="left", fill="both", expand=True)
        settings_body = tk.Frame(_settings_canvas, bg="#F4F7FB")
        _settings_win_id = _settings_canvas.create_window((0, 0), window=settings_body, anchor="nw")

        def _on_settings_body_configure(_event=None):
            try:
                _settings_canvas.configure(scrollregion=_settings_canvas.bbox("all"))
            except tk.TclError:
                pass

        def _on_settings_canvas_configure(event):
            try:
                _settings_canvas.itemconfig(_settings_win_id, width=event.width)
                _settings_canvas.configure(scrollregion=_settings_canvas.bbox("all"))
            except tk.TclError:
                pass

        settings_body.bind("<Configure>", _on_settings_body_configure)
        _settings_canvas.bind("<Configure>", _on_settings_canvas_configure)

        def _on_settings_wheel(event):
            try:
                _settings_canvas.yview_scroll(-1 if event.delta > 0 else 1, "units")
            except tk.TclError:
                pass

        _settings_canvas.bind("<MouseWheel>", _on_settings_wheel)
        settings_body.bind("<MouseWheel>", _on_settings_wheel)
        notebook = ttk.Notebook(settings_body)
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
        tk.Label(break_tab, text="Look away (or leave) for the whole break time at any point and screen time goes back to 0. "
                 "A required break only counts while you look away from the screen. "
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

        # ---- Tab 3: Manual report email ----
        report_tab = tk.Frame(notebook, bg="#F4F7FB")
        notebook.add(report_tab, text="Report email")
        tk.Label(report_tab, text="Send a report by email", font=("Segoe UI", 14, "bold"),
                 fg="#172B4D", bg="#F4F7FB").pack(pady=(14, 6), anchor="w", padx=16)
        tk.Label(report_tab, text="Enter the recipient email, then click Send report now.",
                 bg="#F4F7FB", fg="#62748A", font=("Segoe UI", 9),
                 wraplength=420, justify="left").pack(fill="x", padx=16, pady=(0, 10))
        tk.Label(report_tab, text="Send the report to (email)", bg="#F4F7FB",
                 fg="#52657A", anchor="w").pack(fill="x", padx=16, pady=(8, 2))
        email_var = tk.StringVar(value=settings.get("report_email", ""))
        email_entry = tk.Entry(report_tab, textvariable=email_var, font=("Segoe UI", 12))
        email_entry.pack(fill="x", padx=16, pady=(0, 10))
        report_btn_frame = tk.Frame(report_tab, bg="#F4F7FB")
        report_btn_frame.pack(fill="x", padx=16, pady=(4, 8))
        sent_label = tk.Label(report_tab, text="", font=("Segoe UI", 9), fg="#287D55",
                              bg="#F4F7FB", wraplength=420, justify="left")
        sent_label.pack(fill="x", padx=16, pady=(0, 4))
        if state.get("last_report_date"):
            sent_label.config(text=f"Last report saved: {state['last_report_date']}.")

        def _report_settings_from_entries():
            """Build a manual-only email request using the saved service connection."""
            trial = dict(settings)
            trial["report_email"] = email_var.get().strip()
            trial["report_name"] = str(settings.get("report_name", "") or "")
            trial["report_email_enabled"] = False
            trial["report_enabled"] = False
            trial["report_cloud_url"] = str(settings.get("report_cloud_url", "") or "").strip()
            trial["report_cloud_token"] = str(settings.get("report_cloud_token", "") or "").strip()
            trial["report_time_zone"] = str(settings.get("report_time_zone", "America/New_York") or "America/New_York")
            if not is_valid_email(trial["report_email"]):
                return None, "Enter a valid email to send the report to."
            if not trial["report_cloud_url"].startswith("https://script.google.com/") or not trial["report_cloud_token"]:
                return None, "The one-time email service is not connected on this copy of ScreenBreak."
            return trial, None

        def _restore_send_btn():
            try:
                send_now_btn.config(state="normal", text="Send report now", bg="#287D55", fg="white")
            except tk.TclError:
                pass

        def _send_report_now():
            trial, err = _report_settings_from_entries()
            if err:
                msg.config(text=err, fg="#B42318")
                return
            today = day_key()
            _generate_report(today)
            sent_at = datetime.now()
            settings["report_email"] = trial["report_email"]
            settings["report_email_enabled"] = False
            settings["report_enabled"] = False
            state["settings"] = settings
            save_data(state)
            send_now_btn.config(state="disabled", text="Sending…", bg="#8291A3")
            msg.config(text="Sending through Google…", fg="#62748A")
            sent_label.config(text="Sending…")

            def _done(ok, send_err, response):
                try:
                    if ok and response and response.get("sent_now"):
                        msg.config(text=f"Report sent to {trial['report_email']}.", fg="#287D55")
                        sent_label.config(text=f"✓ Sent at {_clock_12(sent_at)} through Google.")
                        send_now_btn.config(text="✓ Sent!", bg="#287D55", fg="white")
                        status.config(text=f"Report sent to {trial['report_email']}.", fg="#287D55")
                    else:
                        msg.config(text=f"Could not send the report: {send_err or 'Google did not confirm sending.'}", fg="#B42318")
                        sent_label.config(text="The report remains saved on this computer.")
                        send_now_btn.config(text="Try again", bg="#B42318", fg="white")
                except tk.TclError:
                    pass
                try:
                    win.after(4000, _restore_send_btn)
                except tk.TclError:
                    pass

            _cloud_sync_async(trial, "send_now", _done)

        send_now_btn = tk.Button(report_btn_frame, text="Send report now",
                  command=_send_report_now, relief="flat",
                  bg="#287D55", fg="white", padx=12, pady=6)
        send_now_btn.pack(side="left", padx=(0, 6))

        msg = tk.Label(settings_body, text="", font=("Segoe UI", 9), fg="#B42318",
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
            if email_var.get().strip() and not is_valid_email(email_var.get().strip()):
                msg.config(text="Enter a valid email address.", fg="#B42318")
                return
            # Keep a rollback copy. If writing the settings file fails,
            # the previous settings and startup behavior remain in effect.
            previous_settings = dict(settings)
            previous_autostart = get_autostart_enabled() if os.name == "nt" else False
            settings["screen_limit_seconds"] = new_screen
            settings["break_seconds"] = new_break
            settings["screen_limit_unit"] = screen_unit_var.get()
            settings["break_unit"] = break_unit_var.get()
            settings["screen_limit_minutes"] = new_screen / 60
            settings["break_minutes"] = new_break / 60
            # Email is manual only in this build. Keep old scheduled-send
            # flags off so older builds do not restart background delivery.
            settings["report_enabled"] = False
            settings["report_email"] = email_var.get().strip()
            settings["report_email_enabled"] = False
            settings["report_sender_email"] = ""
            settings["report_smtp_password"] = ""
            state["settings"] = settings
            if not save_data(state):
                settings.clear()
                settings.update(previous_settings)
                state["settings"] = settings
                if os.name == "nt":
                    set_autostart_enabled(previous_autostart)
                msg.config(text="Could not save settings. Your previous settings are still active.", fg="#B42318")
                save_btn.config(text="Save settings", state="normal", bg="#287D55")
                return
            # Change the Windows startup entry only after the settings
            # file is safely saved. If this fails, restore the old file.
            if os.name == "nt":
                ok, err = set_autostart_enabled(bool(autostart_var.get()))
                if not ok:
                    settings.clear()
                    settings.update(previous_settings)
                    state["settings"] = settings
                    save_data(state)
                    set_autostart_enabled(previous_autostart)
                    msg.config(text=f"Could not change auto-start: {err}. Previous settings restored.", fg="#B42318")
                    save_btn.config(text="Save settings", state="normal", bg="#287D55")
                    return
            refresh_labels()
            # v2.15: show that it saved BEFORE closing, so the button
            # does not feel hollow. The window closes a moment later.
            msg.config(text="\u2713 Settings saved.", fg="#287D55")
            status.config(text="Settings saved.", fg="#287D55")
            try:
                save_btn.config(text="\u2713 Saved!", bg="#287D55", fg="white")
            except tk.TclError:
                pass

            def _close_after_save():
                state["settings_window"] = None
                try:
                    win.destroy()
                except tk.TclError:
                    pass

            try:
                win.after(900, _close_after_save)
            except tk.TclError:
                _close_after_save()
        # v2.8: a Cancel button, so it is obvious that closing
        # without saving changes nothing.
        save_frame = tk.Frame(settings_footer, bg="#F4F7FB")
        save_frame.pack(pady=9)
        save_btn = tk.Button(save_frame, text="Save settings", command=save_settings, relief="flat",
                  bg="#287D55", fg="white", padx=22, pady=9,
                  font=("Segoe UI", 10, "bold"), cursor="hand2")
        save_btn.pack(side="left", padx=(0, 8))
        tk.Button(save_frame, text="Cancel", command=lambda: (_clear_settings_window(), win.destroy()),
                  relief="flat", bg="#DCE7F5", fg="#172B4D", padx=22, pady=9,
                  cursor="hand2").pack(side="left", padx=8)
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
            away_today_label.config(text=f"● Short away {format_time(totals['away'])}")
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

    def _blue_threshold():
        """Seconds of continuous looking away that count as a full break.
        Normally the break length from Settings. While a required break
        is running it is the (possibly penalty-extended) break plus the
        short settle time, so blue appears exactly when the break ends."""
        if state["break_required"]:
            return required_break_seconds() + SETTLE_SECONDS
        return float(settings["break_seconds"])

    def _current_display_state():
        """Green screen / red distracted / blue break / grey unknown."""
        if face_mesh is None or not state.get("camera_available", False):
            return "unknown"
        if state.get("looking"):
            return "screen"
        # v2.9: away long enough for a full break = blue, shorter = red.
        if state.get("away_run", 0.0) >= _blue_threshold():
            return "break"
        return "away"

    def _track_segment():
        """Record report activity using duration-confirmed transitions.

        Away is only recorded when it lasts at least 2 seconds. The start
        is backdated to the first away frame after confirmation, so a
        2-second-or-longer interval is represented accurately. Away that
        ends sooner is discarded and does not become red.

        Returning to looking is confirmed for 0.35 seconds to prevent a
        one-frame classification flicker from splitting a continuous
        away interval. If the away interval reaches the break threshold,
        its whole duration is promoted from red to blue.
        """
        now = time.time()
        today = day_key(now)
        if today != state["segments_date"]:
            midnight = datetime.strptime(today, "%Y-%m-%d").timestamp()
            _close_segment(midnight)
            state["segments_date"] = today
            state["today_totals"], _ = daily_totals(today)
            state["pending_segment_state"] = None
            state["pending_segment_start"] = None

        display = _current_display_state()
        current = state.get("current_segment_state")
        pending = state.get("pending_segment_state")
        pending_start = state.get("pending_segment_start")

        # Camera/model unavailable is not proof of looking away. Close
        # the current visible state immediately and leave an unknown gap.
        if display == "unknown":
            state["pending_segment_state"] = None
            state["pending_segment_start"] = None
            if current != "unknown":
                if current is not None:
                    prev_start = state.get("current_segment_start")
                    prev_state = current
                    _close_segment(now)
                    if prev_start is not None:
                        state["today_totals"][prev_state] = (
                            state["today_totals"].get(prev_state, 0.0)
                            + max(0.0, now - prev_start)
                        )
                _start_segment("unknown", now)
            return

        # A confirmed away segment becomes blue once its total continuous
        # duration reaches the break setting. This uses the recorder's
        # own onset time, not the per-frame away_run counter, so one noisy
        # looking frame cannot erase an otherwise continuous report break.
        if (current == "away"
                and state.get("current_segment_start") is not None
                and now - state["current_segment_start"] >= _blue_threshold()):
            state["current_segment_state"] = "break"
            current = "break"

        if display == current:
            state["pending_segment_state"] = None
            state["pending_segment_start"] = None
            return

        # If currently looking, a possible away interval starts a timer.
        # A later "break" display belongs to the same candidate away run;
        # do not restart its timer when the threshold changes away -> break.
        if current in (None, "screen") and display in ("away", "break"):
            if pending != "away" or pending_start is None:
                state["pending_segment_state"] = "away"
                state["pending_segment_start"] = now
                return
            candidate_duration = now - pending_start
            break_threshold = _blue_threshold()
            confirm_after = min(REPORT_AWAY_MIN_SECONDS, break_threshold)
            if candidate_duration < confirm_after:
                return
            confirmed_state = (
                "break" if candidate_duration >= break_threshold or display == "break"
                else "away"
            )
            state["pending_segment_state"] = None
            state["pending_segment_start"] = None
            if current is not None:
                prev_start = state.get("current_segment_start")
                prev_state = current
                _close_segment(pending_start)
                if prev_start is not None:
                    state["today_totals"][prev_state] = (
                        state["today_totals"].get(prev_state, 0.0)
                        + max(0.0, pending_start - prev_start)
                    )
            _start_segment(confirmed_state, pending_start)
            return

        # If currently away/break, confirm a return to looking before
        # ending the interval. A short return flicker is ignored.
        if current in ("away", "break") and display == "screen":
            if pending != "screen" or pending_start is None:
                state["pending_segment_state"] = "screen"
                state["pending_segment_start"] = now
                return
            if now - pending_start < REPORT_RETURN_CONFIRM_SECONDS:
                return
            transition_time = pending_start
            state["pending_segment_state"] = None
            state["pending_segment_start"] = None
            prev_start = state.get("current_segment_start")
            prev_state = current
            _close_segment(transition_time)
            if prev_start is not None:
                state["today_totals"][prev_state] = (
                    state["today_totals"].get(prev_state, 0.0)
                    + max(0.0, transition_time - prev_start)
                )
            _start_segment("screen", transition_time)
            return

        # Handle other legitimate transitions (for example unknown -> screen).
        state["pending_segment_state"] = display
        state["pending_segment_start"] = now
        if current is None or display == "screen":
            state["pending_segment_state"] = None
            state["pending_segment_start"] = None
            if current is not None:
                prev_start = state.get("current_segment_start")
                prev_state = current
                _close_segment(now)
                if prev_start is not None:
                    state["today_totals"][prev_state] = (
                        state["today_totals"].get(prev_state, 0.0)
                        + max(0.0, now - prev_start)
                    )
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
        report_break_threshold = (
            required_break_seconds() + SETTLE_SECONDS
            if state["break_required"] else float(settings["break_seconds"])
        )
        if sleep_gap >= report_break_threshold:
            gap_state = "break"
        elif sleep_gap >= REPORT_AWAY_MIN_SECONDS:
            gap_state = "away"
        else:
            # Ignore sub-2-second gaps in the report entirely.
            gap_state = None
        if gap_state is not None:
            append_segment_spanning(sleep_start, gap_end, gap_state)
        state["today_totals"], _ = daily_totals(state["segments_date"])

    def _maybe_send_daily_report():
        """Automatic email is disabled; reports are sent only on button press."""
        return

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
        """Redraw the live timeline in the main window (at most once a
        second, or at once when forced). v2.10: it shows ONE hour at a
        time — the current hour — and you scroll sideways (scrollbar,
        mouse wheel or drag) for earlier hours. A tall line marks each
        hour and a short line each 30 minutes. Nothing is smoothed away:
        every look-away is drawn at least 2 pixels wide."""
        now_mono = time.monotonic()
        if not force and now_mono - state["last_bar_draw"] < 1.0:
            return
        state["last_bar_draw"] = now_mono
        try:
            vw = today_canvas.winfo_width()
            if vw <= 1:
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
            rs, re_ = _view_range(today, segments, now)
            hours = _hour_starts(rs, re_)
            n = len(hours)
            # v2.18: one hour fills the window, the rest scroll
            # sideways one hour at a time.
            hour_w = vw / min(BAR_HOURS_VISIBLE, n)
            total_w = n * hour_w
            # Where was the person looking? Keep them there, unless they
            # were on the newest hours — then follow the live hour.
            lo, hi = today_canvas.xview()
            old_total = state.get("bar_total_w") or 0
            old_hw = state.get("bar_hour_w") or hour_w
            follow = hi >= 0.995 or old_total <= 0
            last_page = max(0, n - BAR_HOURS_VISIBLE)
            keep_idx = int(round(lo * old_total / max(1, old_hw))) if old_total > 0 else last_page
            today_canvas.delete("all")
            state["bar_items"] = []
            today_canvas.configure(scrollregion=(0, 0, total_w, 48))
            target = last_page if follow else max(0, min(last_page, keep_idx))
            today_canvas.xview_moveto(target * hour_w / float(total_w))
            state["bar_total_w"] = total_w
            state["bar_hour_w"] = hour_w
            seg_starts = [sg["start"] for sg in segments]
            for i, hs in enumerate(hours):
                x0 = i * hour_w
                he = hs + 3600
                layers = {}
                for seg_s, seg_e, seg_state in _clip_segments(segments, seg_starts, hs, he):
                    layers.setdefault(seg_state, []).append((seg_s, seg_e))
                # Pale base for the whole hour (gaps = app was off / not yet happened).
                today_canvas.create_rectangle(x0, 20, x0 + hour_w, 46, fill="#E5EAF0", outline="")
                for st in _DRAW_ORDER:
                    colour = STATE_COLORS[st]
                    for seg_s, seg_e in layers.get(st, []):
                        xa = x0 + (seg_s - hs) / 3600.0 * hour_w
                        xb = x0 + (seg_e - hs) / 3600.0 * hour_w
                        # v2.17: true width, floored at 1 pixel so a
                        # 2-second look-away is a thin line, not a
                        # 40-second-wide block (2 px at ~173 px/hour).
                        if xb - xa < 1:
                            xb = xa + 1
                        today_canvas.create_rectangle(xa, 20, xb, 46, fill=colour, outline="")
                        # v2.15/v2.17: remember this piece so hovering
                        # or clicking it can say how long it lasted.
                        # The target is widened 2 px each side so a
                        # 1-px line can still be hovered or clicked.
                        state["bar_items"].append((max(x0, xa - 2.0),
                                                  min(x0 + hour_w, xb + 2.0),
                                                  seg_title(st, seg_s, seg_e)))
                # Tall line + label at every hour, short line + label at :30.
                today_canvas.create_line(x0 + 1, 14, x0 + 1, 20, fill="#172B4D", width=2)
                today_canvas.create_text(x0 + 4, 7, text=_hour_label(hs, long_form=False),
                                         font=("Segoe UI", 8, "bold"), fill="#172B4D", anchor="w")
                xm = x0 + hour_w / 2.0
                today_canvas.create_line(xm, 17, xm, 20, fill="#62748A", width=1)
                today_canvas.create_text(xm, 8, text=_half_label(hs + 1800),
                                         font=("Segoe UI", 7), fill="#8291A3")
                if hs <= now < he:
                    nx = x0 + (now - hs) / 3600.0 * hour_w
                    today_canvas.create_line(nx, 16, nx, 48, fill="#172B4D", width=2)
        except Exception:
            traceback.print_exc()

    def _bar_hover(event):
        """Hovering a coloured bar says how long it lasted."""
        try:
            if state.get("bar_pinned"):
                return
            cx = today_canvas.canvasx(event.x)
            if not (20 <= event.y <= 46):
                bar_info.config(text="Hover over a coloured bar to see how long it lasted \u2014 click it to keep it shown.")
                return
            for xa, xb, title in state.get("bar_items", []):
                if xa <= cx < xb:
                    bar_info.config(text="\u25cf " + title)
                    return
            bar_info.config(text="Hover over a coloured bar to see how long it lasted \u2014 click it to keep it shown.")
        except Exception:
            pass

    def _bar_press(event):
        # A press starts a scroll-drag; remember where, so a plain
        # click (press and release in the same spot) can pin the bar.
        state["bar_press"] = (event.x, event.y)
        state["bar_pinned"] = False
        try:
            today_canvas.scan_mark(event.x, 0)
        except Exception:
            pass

    def _bar_release(event):
        try:
            press = state.get("bar_press")
            if press is None:
                return
            if abs(event.x - press[0]) < 4 and abs(event.y - press[1]) < 4:
                cx = today_canvas.canvasx(event.x)
                if 20 <= event.y <= 46:
                    for xa, xb, title in state.get("bar_items", []):
                        if xa <= cx < xb:
                            state["bar_pinned"] = True
                            bar_info.config(text="\u25cf " + title)
                            return
        except Exception:
            pass

    def _bar_wheel(event):
        """Mouse wheel over the bar moves one hour at a time."""
        try:
            total = state.get("bar_total_w") or 0
            hw = state.get("bar_hour_w") or 0
            if total <= 0 or hw <= 0:
                return
            n = max(1, int(round(total / float(hw))))
            lo, _ = today_canvas.xview()
            idx = int(round(lo * total / float(hw))) + (-1 if event.delta > 0 else 1)
            idx = max(0, min(max(0, n - BAR_HOURS_VISIBLE), idx))
            today_canvas.xview_moveto(idx * hw / float(total))
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
            state["away_run"] += sleep_gap
            state["look_confirm"] = 0.0
            if not state["break_required"]:
                _maybe_reset_screen_time()
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
            # No working face model means there is no reliable camera
            # evidence. Pause the away timer; do not treat a model failure
            # as proof that the user is away. A real frame with no face
            # detected is handled below and does count as away.
            state["look_confirm"] = 0.0
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
                # A missing camera is unknown, not evidence of being
                # away. Pause the away timer until frames resume.
                state["look_confirm"] = 0.0
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
        face_detected = False
        ok, frame = cap.read()
        # FIX (v2.4 audit): a read can succeed with an empty frame
        # (size 0), which used to crash frame.shape below.
        if not ok or frame is None or getattr(frame, "size", 1) == 0:
            state["camera_fail_count"] += 1
            state["camera_available"] = False
            state["looking"] = False
            # A failed camera read is unknown, not a confirmed
            # face-not-detected frame. Pause the away timer.
            state["look_confirm"] = 0.0
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
                    face_detected = True
                    looking, gx, gy, hx = classify(results.multi_face_landmarks[0], w, h)
            except Exception as exc:
                # A failed inference is unknown, not proof of looking away.
                # Pause this tick's away/reset logic; the next frame retries.
                print(f"ScreenBreak: face detection error: {exc}", file=sys.stderr)
                state["camera_available"] = False
                state["looking"] = False
                state["face_detected"] = False
                state["look_confirm"] = 0.0
                status.config(text="Face detection had a problem — trying again…", fg="#B42318")
                hint.config(text="The camera is connected, but this frame could not be checked.")
                refresh_labels()
                return
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
        state["face_detected"] = face_detected
        # v2.16: how long the kid has been continuously away / not
        # there — look-away AND face-not-detected both count. The run
        # only ends after steady looking (see update_away_run).
        state["away_run"], state["look_confirm"], _looking_back = update_away_run(
            state["away_run"], state.get("look_confirm", 0.0), looking, elapsed)
        if _looking_back:
            state["away_reset_done"] = False
        # Check the away-duration reset immediately after updating the
        # continuous-away clock. This is deliberately independent of
        # the screen-limit popup: a full configured break away resets
        # screen time even when a required break was never announced.
        # It also catches the exact tick that crosses the break duration.
        if not state["break_required"]:
            _maybe_reset_screen_time()
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
                        status.config(text=("Face not detected — break timer is running." if not state.get("face_detected", False) else "On a break — keep looking away."), fg="#287D55")
                    else:
                        status.config(text=("Face not detected — stay away for a few more seconds." if not state.get("face_detected", False) else "Break paused — keep looking away and the timer starts again in a few seconds."), fg="#B7791F")
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
                if _maybe_reset_screen_time():
                    pass
                elif state["away_reset_done"]:
                    status.config(text="Break done — screen time is back at 0. It starts counting when you look again.", fg="#2F7ED8")
                else:
                    left = max(0.0, float(settings["break_seconds"]) - state["away_run"])
                    if state.get("face_detected", False):
                        status.config(text=f"Looking away — screen time paused. Stay away {format_time(left)} more to reset it to 0.", fg="#B7791F")
                    else:
                        status.config(text=f"Face not detected — screen time paused. Stay away {format_time(left)} more to reset it to 0.", fg="#B7791F")
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
    today_canvas.bind("<MouseWheel>", _bar_wheel)
    today_canvas.bind("<ButtonPress-1>", _bar_press)
    today_canvas.bind("<B1-Motion>", lambda e: today_canvas.scan_dragto(e.x, 0, gain=1))
    today_canvas.bind("<ButtonRelease-1>", _bar_release)
    today_canvas.bind("<Motion>", _bar_hover)
    root.mainloop()


if __name__ == "__main__":
    main()
