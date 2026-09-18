#!/usr/bin/env python3
"""Supervise the single implementer. Run once a minute by warm_daemon.sh; no model is involved.

Rules:
  rotate   state/rotate exists (the implementer declared itself ready, or reached the hard threshold, or
           compaction was about to start) and the implementer is idle, or the flag has stood for
           ROTATE_MAX seconds whatever it is doing: run rotate.sh auto.
  gone     the implementer named in state/current-impl has not been listed for GONE_CHECKS runs (a crash, a
           kill): run rotate.sh auto, which starts the next one from HANDOFF.md.
  limit    the idle implementer's last reply is the synthetic usage-limit notice ("You've hit your session
           limit · resets 5:40pm") and the reset time has passed: wake it. Nothing else restarts a
           background session when the limit resets.
  stalled  the implementer has been idle for IDLE_MAX seconds without a declared wait and without rotation
           being due (an API error or an interrupted turn ends a turn without the stop hook): wake it.
Waking is `claude stop` plus a bare `claude --bg --resume <session> "<prompt>"`, which keeps the session's id,
name, saved options (settings and hooks included) and its prompt cache while that is alive (verified
2026-09-18). A session is woken at most once in BACKOFF seconds. Nothing is done while state/stopped exists
(stop.sh writes it, start.sh removes it). Every action is one line in state/watchdog.log.
"""
import datetime
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
PROJECT = os.path.dirname(os.path.dirname(HERE))
STATE = os.environ.get("ORCH_STATE_DIR") or os.path.join(HERE, "state")
TRANSCRIPTS = os.path.expanduser("~/.claude/projects/" + PROJECT.replace("/", "-").replace("_", "-"))
IDLE_MAX = int(os.environ.get("ORCH_IDLE_MAX", 600))
ROTATE_MAX = int(os.environ.get("ORCH_ROTATE_MAX", 120))
GONE_CHECKS = int(os.environ.get("ORCH_GONE_CHECKS", 3))
BACKOFF = int(os.environ.get("ORCH_WAKE_BACKOFF", 600))

IMPL_WAKE = ("You were stopped ({why}) and have been woken. Continue the work "
             "exactly where you stopped, following your system prompt. Background commands you had running did not survive the restart: check their "
             "outputs and relaunch what is still needed.")

def log(text):
    os.makedirs(STATE, exist_ok=True)
    with open(os.path.join(STATE, "watchdog.log"), "a") as f:
        f.write(f"{time.strftime('%Y-%m-%dT%H:%M:%S')} {text}\n")


def row(name):
    out = subprocess.run([os.path.join(HERE, "session_row.py"), name], capture_output=True, text=True).stdout.split()
    return dict(zip(("kind", "id", "activity", "sid", "state"), out)) if len(out) >= 4 else None


def last_reply(sid):
    """(model, text, epoch) of the last assistant entry, read from the transcript's tail."""
    path = f"{TRANSCRIPTS}/{sid}.jsonl"
    try:
        size = os.path.getsize(path)
        with open(path, "rb") as f:
            f.seek(max(0, size - 300_000))
            lines = f.read().decode(errors="ignore").splitlines()
    except OSError:
        return None, "", 0
    for line in reversed(lines):
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("type") == "assistant":
            m = d.get("message") or {}
            text = " ".join(c.get("text", "") for c in m.get("content") or [] if isinstance(c, dict))
            ts = d.get("timestamp", "")
            try:
                epoch = datetime.datetime.fromisoformat(ts.replace("Z", "+00:00")).timestamp()
            except ValueError:
                epoch = 0
            return m.get("model"), text, epoch
    return None, "", 0


def reset_epoch(text, said_at):
    """The local time the limit notice names, as an epoch at or after the moment it was said."""
    m = re.search(r"resets\s+(\d{1,2})(?::(\d{2}))?\s*(am|pm)", text, re.I)
    if not m:
        return said_at + 3600
    hour = int(m.group(1)) % 12 + (12 if m.group(3).lower() == "pm" else 0)
    said = datetime.datetime.fromtimestamp(said_at)
    when = said.replace(hour=hour, minute=int(m.group(2) or 0), second=0, microsecond=0)
    if when < said:
        when += datetime.timedelta(days=1)
    return when.timestamp()


def age(name):
    try:
        return time.time() - os.path.getmtime(os.path.join(STATE, name))
    except OSError:
        return None


def wake(name, r, why, prompt):
    mark = f"{name}.woken"
    if (age(mark) or BACKOFF + 1) < BACKOFF:
        return
    open(os.path.join(STATE, mark), "w").write(why + "\n")
    subprocess.run(["claude", "stop", r["id"]], capture_output=True, text=True, cwd=PROJECT)
    time.sleep(2)
    out = subprocess.run(["claude", "--bg", "--resume", r["sid"], prompt.format(why=why)],
                         capture_output=True, text=True, cwd=PROJECT)
    log(f"woke {name} ({why}): {(out.stdout + out.stderr).strip().splitlines()[0][:160] if (out.stdout + out.stderr).strip() else 'no output'}")


def rotate(why):
    mark = "rotated"
    if (age(mark) or BACKOFF + 1) < 120:
        return
    open(os.path.join(STATE, mark), "w").write(why + "\n")
    out = subprocess.run([os.path.join(HERE, "rotate.sh"), "auto"], capture_output=True, text=True, cwd=PROJECT)
    log(f"rotation ({why}): " + " | ".join((out.stdout + out.stderr).strip().splitlines())[:400])


def main():
    if os.path.exists(os.path.join(STATE, "stopped")):
        return
    now = time.time()
    try:
        impl = open(os.path.join(STATE, "current-impl")).read().strip() or None
    except OSError:
        impl = None
    if not impl:
        return
    r = row(impl)
    gone_file = os.path.join(STATE, "impl-gone-count")
    if r is None:
        n = int(open(gone_file).read() or 0) + 1 if os.path.exists(gone_file) else 1
        open(gone_file, "w").write(str(n))
        if n >= GONE_CHECKS:
            os.remove(gone_file)
            rotate(f"{impl} is no longer listed")
        return
    if os.path.exists(gone_file):
        os.remove(gone_file)
    if r["kind"] != "background":
        return
    flag_age = age("rotate")
    if flag_age is not None and (r["activity"] == "idle" or flag_age > ROTATE_MAX):
        rotate("the implementer is ready" if r["activity"] == "idle" else "the rotate flag has stood for minutes")
        return
    if r["activity"] != "idle":
        return
    model, text, said_at = last_reply(r["sid"])
    if model == "<synthetic>" and re.search(r"hit your .*limit", text, re.I):
        if now >= reset_epoch(text, said_at) + 90:
            wake(impl, r, "the account's usage limit, which has now reset", IMPL_WAKE)
        return
    idle_for = now - said_at if said_at else 0
    if age("waiting") is None:
        declared = age("waiting-declared") is not None  # a declared wait gets three times as long
        if idle_for > IDLE_MAX * (3 if declared else 1):
            wake(impl, r, "you have been idle for a long time" + (" waiting for the owner" if declared else
                 " without the goal being reached and without a declared wait"), IMPL_WAKE)


if __name__ == "__main__":
    try:
        main()
    except Exception as e:  # the daemon must survive anything here
        log(f"watchdog error: {e!r}")
        sys.exit(0)
