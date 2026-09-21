#!/usr/bin/env python3
"""One-screen health report of the orchestration: the daemon, the knowledge base, each slot's session, the queue and
its stages, parked and finishing tasks, questions, what is held warm, the bases. Lines that need someone start with
ATTENTION."""
import calendar
import json
import os
import subprocess
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


CACHE_LIFE = 3700   # an hour of prompt cache, with a minute's slack: past this nothing is left of an entry


def daemon_alive():
    """Whether the keep-warm daemon runs: its pid, and that the process holding that pid is the daemon. A pid file a
    dead daemon left behind names whatever took the number since, and `warm_daemon.sh --ensure` reads it the same
    way — so one stale number would have said "daemon: alive" for ever while nothing pinged (2026-09-21). A cmdline
    that cannot be read counts as alive: nothing here calls a live daemon dead.

    Inside Claude Code's sandbox, where the owner's session and every other runs this, only the command's own
    processes are visible, and the pid of the live daemon read as dead: there its heartbeat (warm_daemon.sh) says it."""
    if not v2.control():
        try:
            beat = time.time() - os.path.getmtime(os.path.join(S, "warm.beat"))
        except OSError:
            return False
        return beat <= 3 * int(os.environ.get("ORCH_BEAT_EVERY", 5)) + 5
    pid = read("warm.pid")
    if not pid or not os.path.exists(f"/proc/{pid}"):
        return False
    try:
        return "warm_daemon" in open(f"/proc/{pid}/cmdline").read()
    except OSError:
        return True


def minutes(seconds):
    return f"{int(seconds) // 60} min"


def session(label, s, now):
    """One line on a live session: activity, context, last reply, how to open it."""
    if not s.get("sid"):
        return (("ATTENTION " if now - s.get("starting", now) > v2.START_MAX else "")
                + f"{label}: {s['name']} starting for {minutes(now - s.get('starting', now))}")
    r = v2.row(s["name"])
    if not r and s.get("state") == "idle":  # the planner between its events is sealed, and a sealed session is not
        return (f"{label}: {s['name']} waits for its next event, sealed and held warm, last hit "  # listed: that is
                f"{minutes(v2.hit_age(s['name']))} ago")                                           # what idle means
    if not r:
        return f"ATTENTION {label}: {s['name']} is not listed (the watchdog acts after {w.GONE_CHECKS} minutes)"
    ctx = ctx_gauge.context_tokens(v2.transcript(s["sid"]))
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
                     f"ago, {wst.get('productions', 0)} productions, a reserve of {wst.get('reserve', '?')} reads"
                     + (f"; the same check failure {wst['repeats']} times" if wst.get("repeats") else ""))
    except (OSError, ValueError):
        pass
    return line


def bases_and_trees():
    """What is true whether or not the orchestration runs: whether each base was warm when it was last pinged (the
    mark is touched on a miss too, so it says only that it was pinged), and what stands in each task's own tree."""
    log = os.path.join(v2.STATE, "warm.log")
    lines = open(log).read().splitlines() if os.path.exists(log) else []
    for who in v2.BASES:
        last = [l for l in lines if f"warm {who}:" in l and (" OK" in l or "MISS" in l)]
        if not last:
            continue
        at = last[-1].split()[0]
        misses = os.path.join(v2.STATE, f"{who}-base.miss")
        n = len(open(misses).read().split()) if os.path.exists(misses) else 0
        # `base.sh WHO warm` forks the layer when there is one — what the roles fork is what must stay warm, and a
        # fork of a layer reads the stable base under it — so saying "base" of that ping named the wrong thing.
        what = f"layer {who} (with the base under it)" if v2.layer_record(who) else f"base {who}"
        # how long ago, and whether anything is left of it: "warm at 21:59:00" read at 01:17 says warm, and the entry
        # it names died at 22:59. A stopped run is read hours later, and this is the line that says what a restart
        # would find (2026-09-21).
        try:
            old = time.time() - time.mktime(time.strptime(at, "%Y-%m-%dT%H:%M:%S"))
        except ValueError:
            old = None
        print(("ATTENTION " if n >= 2 else "")
              + f"{what}: {'warm' if ' OK' in last[-1] else 'was COLD and was rewritten'} at {at[11:19]}"
              + (f" ({minutes(old)} ago" + ("; its cache entry has expired since" if old > CACHE_LIFE else "") + ")"
                 if old is not None else "")
              + (f", {n} miss(es); two stop its pings" if n else ""))
    for who in v2.BASES:
        path = os.path.join(v2.STATE, f"{who}-layer.json")
        if not os.path.exists(path):
            continue
        try:
            rec = json.load(open(path))
        except (OSError, ValueError):
            continue
        share = 0.0
        try:
            out = subprocess.run([sys.executable, os.path.join(v2.HERE, "manifest.py"), "stale-share", who],
                                 capture_output=True, text=True, timeout=120,
                                 env={k: v for k, v in os.environ.items() if k != "ORCH_LOAD_LIST"}).stdout
            share = float(out.strip() or 0)
        except (ValueError, OSError, subprocess.SubprocessError):
            pass
        if not v2.layer_record(who):
            print(f"ATTENTION layer {who}: it is a fork of the stable base {str(rec.get('base'))[:8]}, which has been "
                  "rebuilt under it — nothing forks it and nothing pings it; build it again (base.sh "
                  f"{who} layer)")
            continue
        due = share >= float(os.environ.get("ORCH_LAYER_STALE", 0.20))
        building = os.path.exists(os.path.join(v2.STATE, f"{who}-layer.building"))
        # the watchdog is the only thing that refreshes a layer, and it does nothing while the run is stopped or its
        # daemon is down: "— it is refreshed" said then names something nobody will do (2026-09-21)
        tended = daemon_alive() and not read("stopped")
        print(("ATTENTION " if due and not building else "")
              + f"layer {who}: {rec.get('context', 0) // 1000}K, sealed {rec.get('sealed', '?')[11:19]}, "
              + f"{share:.0%} of what it holds has changed"
              + (" — it is being built again" if building else "" if not due
                 else " — it is refreshed" if tended
                 else f" — it is due to be built again, and nothing runs to do it (start.sh, or base.sh {who} layer)"))
    graph = v2.graph_held()
    if graph:
        print(f"the graph is held: {graph}; the planner's `v2.py queue` releases it")
    hold = v2.held_back()
    if hold:
        print(f"ATTENTION nothing starts a session: the hold is on ({hold}). Keep-warm pings still go. "
              f"Take it off when you mean to begin: rm {os.path.join(v2.STATE, v2.NO_LAUNCH)}")
    size, biggest, its = v2.handoff_size()
    if size > v2.HANDOFF_MAX:
        print(f"ATTENTION HANDOFF.md is {size // 1000}K tokens of at most {v2.HANDOFF_MAX // 1000}K, `## {biggest}` "
              f"{its // 1000}K of it: every knowledge base holds it and every designer reads it whole. The planner "
              f"is told in its status; what was done and how belongs in {v2.PLANNER_LOG}, DECISIONS.md takes what "
              "the development decides, and a planning decision belongs to the task it governs.")
    risk = v2.base_at_risk()
    if risk:
        print("ATTENTION the accepted base stands in a task's own directory: "
              + ", ".join(os.path.relpath(x, v2.PROJECT) for x in risk)
              + " — dropping that task, re-planning it or sweeping its run output would take the base with it")
    if v2.TREES and os.path.exists(os.path.join(v2.STATE, "no-tree")):
        print("ATTENTION no task gets a tree of its own: " + open(os.path.join(v2.STATE, "no-tree")).read()
              + " — every task works in the one tree meanwhile, where one task's unfinished work holds every other out")
    elif not v2.TREES:
        print("trees: off (ORCH_TREES=0) — every task works in the one tree")
    trees = v2.trees_standing()
    if trees:
        print("trees: " + ", ".join(f"task {x['task']} ({x['changed']} changed, {x['commits']} commit(s))"
                                    for x in trees))


def standing(st, now):
    """What the state holds whoever is running: the queue and the tasks' stages, the questions, and the events
    waiting for the next planning episode. A stopped or an inactive run is the state a restart meets, so it is
    shown there too: health said "stopped at ..." and nothing more, and the parked tasks, the proposals nobody
    placed and the reviews left orphaned were visible nowhere while it stood still (2026-09-21)."""
    stages = [f"{tid}:{(st['tasks'].get(tid) or {}).get('stage', '?')}" for tid in st["queue"]]
    print("queue: " + (" ".join(stages) or "empty"))
    # a path is the task's until its finalizer commits it, which takes it out of the map. So a changed path owned by
    # a task the planner has completed is work the graph calls done and the repository does not have: on 2026-09-21
    # every uncommitted path in the tree was one, of tasks 22, 46, 48 and 50, and it was named nowhere.
    changed = set(v2.changed_paths())
    with v2.owners(write=False) as owners:
        stranded = {p: t for p, t in owners.items()
                    if p in changed and (v2.read_task(t) or {}).get("status") == "completed"}
    if stranded:
        print("ATTENTION uncommitted changes whose task is completed: "
              + ", ".join(f"{p} (task {t})" for p, t in sorted(stranded.items())[:6])
              + (f", and {len(stranded) - 6} more" if len(stranded) > 6 else "")
              + " — the graph calls that work done and the repository does not hold it: it is committed by the task "
                "that continues it, or discarded")
    with_planner = set(v2.with_the_planner(st))
    for tid, t in st["tasks"].items():
        if t.get("stage") == "parked":
            p = t.get("parked") or {}
            waits = {"run": "its own run", "tree": f"the working tree (task {p.get('holder')})",
                     "fix": f"its fix (task {p.get('after')})" if p.get("after") else "the planner to name its fix",
                     "answer": "the answer to its question"}.get(p.get("for"), p.get("after") or "the planner")
            print(f"parked: task {tid} for {minutes(now - p.get('since', now))} of {v2.HOLD_PARK // 3600} h, waits on "
                  f"{waits}" + (f": {p.get('why', '')[:100]}" if p.get("why") else ""))
        elif t.get("stage") == "proposed":
            print(f"ATTENTION task {tid}: {t.get('proposed', '?')} task(s) proposed and not placed — only the "
                  f"planner places them ({t.get('proposal')})")
        elif t.get("stage") in ("checking", "reviewing", "fixing", "committing", "planner"):
            # a stage of "planner" the graph does not agree with is the harness's own bookkeeping, which nothing
            # clears when a task is completed or dropped elsewhere: tasks 5, 9, 18 and 21 read as the planner's here
            # long after three were committed and the fourth dropped (2026-09-20)
            stale = t["stage"] == "planner" and tid not in with_planner
            print(f"task {tid}: {t['stage']}" + (f" (checks failed {t['checks_failed']})" if t.get("checks_failed") else "")
                  + (f" (rejected {t['rejections']})" if t.get("rejections") else "")
                  + (" — stale, and nothing is told of it: the list says "
                     + ((v2.read_task(tid) or {}).get("status") or "it is not there at all") if stale else ""))
    for qid, q in st["asks"].items():
        if q["state"] != "answered":
            print(("ATTENTION " if now - q["asked"] > 1800 else "") + f"question {qid} from {q['from']} to {q['target']}, "
                  f"{q['state']} for {minutes(now - q['asked'])}: {q['text'][:100]}")
    if st["events"]:
        print(f"events for the next planning episode: {len(st['events'])}, the oldest from {st['events'][0]['at']}")


def main():
    now = time.time()
    print(time.strftime("health at %Y-%m-%d %H:%M:%S"))
    mem = {k: int(v.split()[0]) // 1024 for k, v in (ln.split(":") for ln in open("/proc/meminfo")) if k in ("MemTotal", "MemAvailable")}
    print(f"memory: {mem['MemAvailable'] // 1024} GiB available of {mem['MemTotal'] // 1024}")
    bases_and_trees()
    st = v2.peek()
    if read("stopped"):
        print(f"stopped at {read('stopped')}; start.sh resumes")  # the marker says when, not who wrote it
        standing(st, now)
        return
    if not st["active"]:
        print("the orchestration is inactive; start.sh starts it")
        standing(st, now)
        return
    trouble = v2.tree_trouble()
    print(("ATTENTION the working tree refuses every check: " + "; ".join(trouble[:3])) if trouble
          else "working tree: consistent (every theory declared, every declaration present, no dangling import)")
    print("daemon: alive" if daemon_alive() else "ATTENTION daemon is not running: start.sh starts it")
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
        if not s and label == "planner":  # it is in no slot between its events, and it is alive there
            s = st["sessions"].get(v2.planner_live(st) or "")
        print(session(label, s, now) if s else f"{label}: -")
    standing(st, now)
    if not v2.slot(st, v2.PRODUCING) and not any((st["tasks"].get(t) or {}).get("stage") in ("ready", "brief")
                                                  for t in st["queue"]):
        print("ATTENTION nothing is producing and nothing is ready or to be briefed: the planner queues the next tasks")
    held = [(n, w.held(st, n, s)) for n, s in st["sessions"].items() if s["state"] not in v2.LIVE and not s.get("released")]
    for n, why in held:
        if why:
            a = v2.hit_age(n)
            print(("ATTENTION " if a > v2.WARM_MAX else "") + f"held: {n} ({why}), last hit {minutes(a)} ago")
    for who in v2.BASES:
        if os.path.exists(os.path.join(S, f"{who}-base.json")):
            a = w.age(f"{who}-base.hit")
            print(f"base {who}: " + ("never hit" if a is None else f"last hit {minutes(a)} ago"
                                      + (" — its cache entry has expired" if a > CACHE_LIFE else "")))
    for line in recent("warm.log", 3600, "MISS"):
        print("ATTENTION keep-warm miss: " + line[:170])
    for line in recent("v2.log", 3600)[-12:]:
        print("log: " + line[:220])


if __name__ == "__main__":
    main()
