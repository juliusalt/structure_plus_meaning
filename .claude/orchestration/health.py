#!/usr/bin/env python3
"""One-screen health report of the orchestration: the daemon, the knowledge base, each slot's session, the queue and
its stages, parked and finishing tasks, questions, what is held warm, the bases. Lines that need someone start with
ATTENTION."""
import calendar
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ctx_gauge  # noqa: E402
import v2  # noqa: E402
import watchdog as w  # noqa: E402

S = v2.STATE


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


def minutes(seconds):
    return f"{int(seconds) // 60} min"


def session(label, s, now):
    """One line on a live session: activity, context, last reply, how to open it."""
    if not s.get("sid"):
        return (("ATTENTION " if now - s.get("starting", now) > v2.START_MAX else "")
                + f"{label}: {s['name']} starting for {minutes(now - s.get('starting', now))}")
    r = v2.row(s["name"])
    if not r:
        return f"ATTENTION {label}: {s['name']} is not listed (the watchdog acts after {w.GONE_CHECKS} minutes)"
    ctx = ctx_gauge.context_tokens(f"{v2.TRANSCRIPTS}/{s['sid']}.jsonl")
    model, text, said = w.last_reply(s["sid"])
    idle = now - said if said else 0
    line = (f"{label}: {s['name']}" + (f" on task {s['task']}" if s.get("task") else "") + f", {r['activity']}, "
            f"context {ctx // 1000}K, last reply {minutes(idle)} ago; open it with: claude attach {r['id']}")
    if model == "<synthetic>" and "limit" in text.lower():
        reset = w.reset_epoch(text, said)
        line += f"; stopped by the usage limit, resets {time.strftime('%H:%M', time.localtime(reset))}"
        if now > reset + 900:
            line = "ATTENTION " + line + " — the reset passed fifteen minutes ago and it has not been resumed"
    elif r["activity"] == "idle" and idle > 1200:
        line = "ATTENTION " + line + " — idle for over twenty minutes"
    if os.path.exists(os.path.join(S, "flags", s["sid"] + ".hard")):
        line += "; at the end of its window"
    try:
        wst = json.load(open(os.path.join(S, f"work-{s['sid']}.json")))
        at = wst.get("production_at")
        if at:
            line += (f"\n  last production {minutes(now - calendar.timegm(time.strptime(at[:19], '%Y-%m-%dT%H:%M:%S')))} "
                     f"ago, {wst.get('read_tokens', 0) // 1000}K read since, {wst.get('productions', 0)} productions"
                     + (f", in step {wst['step']}" if wst.get("step") is not None else "")
                     + (f"; the same check failure {wst['repeats']} times" if wst.get("repeats") else ""))
    except (OSError, ValueError):
        pass
    return line


def main():
    now = time.time()
    print(time.strftime("health at %Y-%m-%d %H:%M:%S"))
    mem = {k: int(v.split()[0]) // 1024 for k, v in (ln.split(":") for ln in open("/proc/meminfo")) if k in ("MemTotal", "MemAvailable")}
    print(f"memory: {mem['MemAvailable'] // 1024} GiB available of {mem['MemTotal'] // 1024}")
    if read("stopped"):
        print(f"stopped by stop.sh at {read('stopped')}; start.sh resumes")
        return
    st = v2.peek()
    if not st["active"]:
        print("the orchestration is inactive; start.sh starts it")
        return
    pid = read("warm.pid")
    print("daemon: alive" if pid and os.path.exists(f"/proc/{pid}") else "ATTENTION daemon is not running: start.sh starts it")
    kb = st["sessions"].get(st["kb"] or "")
    if st.get("kb_building"):
        print(session("knowledge base (loading)", st["sessions"][st["kb_building"]], now))
    if kb:
        a = v2.hit_age(kb["name"])
        ctx = kb.get("context") or 0
        print(("ATTENTION " if a > v2.WARM_MAX else "") + f"knowledge base: {kb['name']}, {kb.get('kb_state')}, "
              f"{ctx // 1000}K of its {v2.KB_MAX // 1000}K limit (its forks' room: {(v2.SOFT - ctx) // 1000}K), last hit "
              f"{minutes(a)} ago"
              + (f", {len(st['notes'])} notes pending" if st["notes"] else ""))
        if kb.get("kb_state") == "sealed" and not st.get("kb_building") and ctx > v2.KB_MAX - v2.KB_MARGIN:
            print("ATTENTION the knowledge base loads near its limit even fresh: condensing HANDOFF.md is asked of the "
                  "planner, and a base rebuild (yours: base.sh max build, status, seal) takes in what the documents "
                  "hold; " + v2.stale("max"))
    elif not st.get("kb_building"):
        print("ATTENTION no knowledge base (the dispatch builds one)")
    for label, roles, fix in (("planner", {"planner"}, False), ("producing", v2.PRODUCING, False),
                              ("supporting", v2.SUPPORTING, False), ("quick fix", v2.PRODUCING, True),
                              ("consultation", {"consultant"}, False)):
        s = v2.slot(st, roles, fix)
        print(session(label, s, now) if s else f"{label}: -")
    stages = [f"{tid}:{(st['tasks'].get(tid) or {}).get('stage', '?')}" for tid in st["queue"]]
    print("queue: " + (" ".join(stages) or "empty"))
    if not v2.slot(st, v2.PRODUCING) and not any((st["tasks"].get(t) or {}).get("stage") in ("ready", "brief")
                                                  for t in st["queue"]):
        print("ATTENTION nothing is producing and nothing is ready or to be briefed: the planner queues the next tasks")
    for tid, t in st["tasks"].items():
        if t.get("stage") == "parked":
            p = t.get("parked") or {}
            print(f"parked: task {tid} for {minutes(now - p.get('since', now))} of {v2.HOLD_PARK // 3600} h, waits on "
                  f"{p.get('after') or 'the planner'}: {p.get('why', '')[:100]}")
        elif t.get("stage") in ("checking", "reviewing", "fixing", "committing", "planner"):
            print(f"task {tid}: {t['stage']}" + (f" (checks failed {t['checks_failed']})" if t.get("checks_failed") else "")
                  + (f" (rejected {t['rejections']})" if t.get("rejections") else ""))
    for qid, q in st["asks"].items():
        if q["state"] != "answered":
            print(("ATTENTION " if now - q["asked"] > 1800 else "") + f"question {qid} from {q['from']} to {q['target']}, "
                  f"{q['state']} for {minutes(now - q['asked'])}: {q['text'][:100]}")
    if st["events"]:
        print(f"events for the next planning episode: {len(st['events'])}, the oldest from {st['events'][0]['at']}")
    held = [(n, w.held(st, n, s)) for n, s in st["sessions"].items() if s["state"] not in v2.LIVE and not s.get("released")]
    for n, why in held:
        if why:
            a = v2.hit_age(n)
            print(("ATTENTION " if a > v2.WARM_MAX else "") + f"held: {n} ({why}), last hit {minutes(a)} ago")
    for who in v2.BASES:
        if os.path.exists(os.path.join(S, f"{who}-base.json")):
            a = w.age(f"{who}-base.hit")
            print(f"base {who}: " + ("never hit" if a is None else f"last hit {minutes(a)} ago"
                                      + (" — its cache entry has expired" if a > 3700 else "")))
    for line in recent("warm.log", 3600, "MISS"):
        print("ATTENTION keep-warm miss: " + line[:170])
    for line in recent("v2.log", 3600)[-12:]:
        print("log: " + line[:220])


if __name__ == "__main__":
    main()
