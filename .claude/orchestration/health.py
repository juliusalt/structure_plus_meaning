#!/usr/bin/env python3
"""One-screen health report of the orchestrated implementer. Lines that need someone start with ATTENTION."""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import watchdog as w  # noqa: E402

S = w.STATE


def read(name):
    try:
        return open(os.path.join(S, name)).read().strip()
    except OSError:
        return ""


def recent(name, seconds, pick=None):
    out = []
    for line in read(name).splitlines():
        try:
            t = time.mktime(time.strptime(line[:19], "%Y-%m-%dT%H:%M:%S"))
        except ValueError:
            continue
        if time.time() - t <= seconds and (pick is None or pick in line):
            out.append(line)
    return out


def main():
    now = time.time()
    print(time.strftime("health at %Y-%m-%d %H:%M:%S"))
    mem = {k: int(v.split()[0]) // 1024 for k, v in (ln.split(":") for ln in open("/proc/meminfo")) if k in ("MemTotal", "MemAvailable")}
    print(f"memory: {mem['MemAvailable'] // 1024} GiB available of {mem['MemTotal'] // 1024}")
    if read("stopped"):
        print(f"stopped by stop.sh at {read('stopped')}; start.sh resumes")
        return
    pid = read("warm.pid")
    print("daemon: alive" if pid and os.path.exists(f"/proc/{pid}") else "ATTENTION daemon is not running: start.sh starts it")
    impl = read("current-impl")
    r = w.row(impl) if impl else None
    if not r:
        print(f"ATTENTION {impl or 'no implementer'} is not listed (the watchdog starts the next one after three minutes)")
    else:
        ctx = subprocess.run([os.path.join(HERE, "ctx_gauge.py"), "measure", f"{w.TRANSCRIPTS}/{r['sid']}.jsonl"],
                             capture_output=True, text=True).stdout.strip()
        model, text, said = w.last_reply(r["sid"])
        idle = int(now - said) if said else -1
        line = f"{impl}: {r['activity']} ({r['state']}), context {int(ctx or 0) // 1000}K, last reply {idle // 60} min ago; open it with: claude attach {r['id']}"
        if model == "<synthetic>" and "limit" in text.lower():
            reset = w.reset_epoch(text, said)
            line += f"; stopped by the usage limit, resets {time.strftime('%H:%M', time.localtime(reset))}"
            if now > reset + 900:
                line = "ATTENTION " + line + " — the reset passed fifteen minutes ago and the watchdog has not woken it"
        elif r["activity"] == "idle" and idle > 1200 and w.age("rotate") is None:
            line = "ATTENTION " + line + " — idle for over twenty minutes"
        print(line)
    mode = read("impl-mode")
    print(f"mode: {mode or '-'}" + ("   (fork-cold: that fork paid a cold write and does not keep the base warm)" if "cold" in mode else ""))
    rot = w.age("rotate")
    if rot is not None:
        print(("ATTENTION " if rot > 600 else "") + f"rotation due for {int(rot) // 60} min: {read('rotate')}")
    a = w.age("impl-base.hit")
    print("base: none sealed" if a is None else f"base: last hit {int(a) // 60} min ago" + (" — ATTENTION over an hour: its cache entry has expired" if a > 3700 else ""))
    for line in recent("warm.log", 3600, "MISS"):
        print("ATTENTION keep-warm miss: " + line[:170])
    for line in recent("watchdog.log", 3600):
        print("watchdog: " + line[:220])


if __name__ == "__main__":
    main()
