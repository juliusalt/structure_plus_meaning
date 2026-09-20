#!/usr/bin/env python3
"""Supervise the sessions and keep what may be consulted warm. Run once a minute by warm_daemon.sh; no model is involved.

  live       a session gone for GONE_CHECKS runs is lost: its piece of work goes back (a producing session's task to the
             planner, a review or a brief to be started again, a planning episode's events to the next one, a question
             to be asked again, the knowledge base to be rebuilt). An idle session with mail is resumed with it; one
             stopped by the usage limit is resumed once the limit has reset; one at the end of its window is stopped
             and its piece of work goes back; one whose piece of work has ended, or that waits, is sealed (stopped:
             it can be resumed or forked while warm); the planner, which lives across its events, is sealed between
             them and held warm; one whose turn ended without any of that (an API error, a lost turn) is resumed to
             continue after IDLE_MAX seconds.
  held       a sealed session something may still consult or continue is pinged before its cache expires (v2.ping):
             the knowledge base and the planner always; a task's session while its task is being checked, reviewed,
             fixed or committed; its reviewer while a re-review may come; a waiting (parked) session for v2.HOLD_PARK seconds,
             after which it is resumed to record a partial result; a task designer or a designer while tasks it
             briefed or designed are open, for at most v2.HOLD_MAX seconds. Anything else is released.
  finishing  a quick fix past its budget and a grace is stopped, the task given to the planner; a check or commit whose
             finalizer has not reported within FINAL_MAX seconds counts as failed.
  dispatch   then v2.dispatch: the knowledge base, the producing slot, the supporting slot, a quick fix, a
             consultation, a planning episode.
Nothing is done while state/stopped exists or the orchestration is inactive. Every action is one line in state/v2.log.
"""
import contextlib
import datetime
import json
import os
import re
import signal
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import v2  # noqa: E402

STATE = v2.STATE
IDLE_MAX = int(os.environ.get("ORCH_IDLE_MAX", 300))
GONE_CHECKS = int(os.environ.get("ORCH_GONE_CHECKS", 3))
BACKOFF = int(os.environ.get("ORCH_WAKE_BACKOFF", 600))
# The finalizer waits for Isabelle at most ORCH_ISABELLE_WAIT and runs its check at most ORCH_FINAL_MAX; past both and a
# margin it is given up. A finalizer that is gone without having reported is given up after START_GRACE.
FINAL_MAX = int(os.environ.get("ORCH_ISABELLE_WAIT", 3600)) + int(os.environ.get("ORCH_FINAL_MAX", 3600)) + 600
START_GRACE = 120
GRACE = 180
OWNER_IDLE = int(os.environ.get("ORCH_OWNER_IDLE", 1800))  # an episode the owner left: asked to end


def last_reply(sid):
    """(model, text, epoch) of the last assistant entry, read from the transcript's tail."""
    path = f"{v2.TRANSCRIPTS}/{sid}.jsonl"
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
            try:
                epoch = datetime.datetime.fromisoformat(d.get("timestamp", "").replace("Z", "+00:00")).timestamp()
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


def gone(name):
    """Whether a session has been missing for GONE_CHECKS runs in a row (counted in state/gone-<name>)."""
    path = os.path.join(STATE, f"gone-{name}")
    n = int(open(path).read() or 0) + 1 if os.path.exists(path) else 1
    if n >= GONE_CHECKS:
        os.remove(path)
        return True
    open(path, "w").write(str(n))
    return False


def seen(name):
    try:
        os.remove(os.path.join(STATE, f"gone-{name}"))
    except OSError:
        pass


def hard(s):
    return os.path.exists(os.path.join(STATE, "flags", f"{s.get('sid')}.hard"))


# ---------------------------------------------------------------- a session's piece of work goes back

def lost(name, why):
    """A session that can no longer continue: its piece of work goes back, by its role."""
    if v2.has_mail(name):  # nothing will open its box again: said, and kept where it is
        box = os.path.join(v2.STATE, "mail", f"{name}.jsonl")
        held = open(box, errors="ignore").read() if os.path.exists(box) else ""
        v2.log(f"ATTENTION mail to {name} reached nobody ({why}); it is kept in state/mail/{name}.jsonl: "
               f"{held[:200]}")
    with v2.state() as st:
        s = st["sessions"][name]
        s["state"], tid = "lost", s.get("task")
        t = st["tasks"].get(tid or "") or {}
        role = s["role"]
        if role in v2.PRODUCING:
            t["stage"] = "planner"
            t["fixing"] = None
            v2.event(st, "the harness", f"{name} ({role}) on task {tid} {why}; what it wrote is on disk "
                     f"(.build/tasks/{tid}/ and its deliverables): split or re-plan the task over what exists.")
        elif role == "reviewer":  # its review task is taken up again by a new reviewer
            x = st["tasks"].get(s.get("reviews") or "") or {}
            t["reviewing"], x["reviewing"] = None, None
            if t.get("reviewed_by") == name:
                t["reviewed_by"] = None
                t.pop("round", None)
        elif role == "task-designer":  # its brief task is taken up again
            if t.get("stage") == "running":
                t["stage"] = "ready"
        elif role == "planner":
            st["events"] = (s.get("events") or []) + st["events"]
            v2.event(st, "the harness", f"The planner {name} {why} before it wrote its notes, so the knowledge base "
                     "holds nothing of what it settled and HANDOFF.md is all that carries over. What it was given and "
                     "had not handled is below; read HANDOFF.md as the state, and say in your own notes what that "
                     "costs if anything is missing from it.")
        elif role == "consultant" and s.get("qid") in st["asks"]:
            st["asks"][s["qid"]]["state"] = "queued"
        elif role == "kb" and st.get("kb_building") == name:
            st["kb_building"] = None
        elif role == "kb":
            s["kb_state"] = "lost"
    v2.log(f"{name} {why}")
    v2.release(name)
    if role in v2.PRODUCING and tid:  # stopped now: its changes leave the working tree
        aside = v2.leave(tid, "lost")
        if aside:
            with v2.state() as st:
                v2.event(st, "the harness", f"Task {tid}:{aside}")


def care(name, s):
    """One live session: gone, mail, usage limit, end of window, sealing, stalls."""
    if s["state"] == "starting":
        if time.time() - s.get("starting", 0) > v2.START_MAX:
            lost(name, "never started")
        return
    r = v2.row(name)
    if not r:
        if s["state"] in v2.LIVE and gone(name):
            lost(name, "is gone")
        elif s["state"] not in v2.LIVE:
            with v2.state() as st:
                st["sessions"][name]["sealed"] = True
        return
    seen(name)
    if r["activity"] != "idle":
        return
    if s["role"] == "kb":
        return  # v2.kb_care seals it when it has replied INTEGRATED
    model, said, at = last_reply(s["sid"])
    # the limit first: a session stopped by it is not idle by choice, and resuming it to hand over mail spends the
    # resume on a turn that hits the limit again while unread() has already emptied its box — the mail would be
    # read by nobody. It stays there, and the gauge hands it over at the session's first tool call after the reset.
    if model == "<synthetic>" and re.search(r"hit your .*limit", said, re.I):
        if time.time() >= reset_epoch(said, at) + 90 and (age(f"{name}.woken") or BACKOFF + 1) > BACKOFF:
            v2.resume(name, "You were stopped by the account's usage limit, which has now reset. Continue.")
        return
    if s["state"] in v2.LIVE and v2.has_mail(name) and not v2.running_jobs(name):
        messages = v2.unread(name)
        if messages and not v2.resume(name, v2.mail_text(messages)):
            v2.keep_mail(name, messages)  # kept, each with its own sender; a session gone cold cannot take it
            if not v2.warm(name):
                lost(name, "went cold before its mail reached it")
        return
    if hard(s) and s["state"] in v2.LIVE:
        lost(name, "reached the end of its window")
        return
    if v2.running_jobs(name):
        return  # stopping it would kill its jobs: their completion runs its turn
    if s.get("owner") and at and time.time() - at > OWNER_IDLE and (age(f"{name}.woken") or BACKOFF + 1) > BACKOFF:
        # the owner has gone; the planner is not ended by that — it goes back to its events with what it was told
        with v2.state() as st:
            st["sessions"][name]["owner"] = False
        v2.resume(name, "The owner has been silent for half an hour and has gone. Record every direction they gave in "
                        "the ledger, carry it into HANDOFF.md, the graph and the order, and then go on with your "
                        "events as before; end your turn when you have.")
        return
    waiting = s["role"] not in v2.PRODUCING and any(
        q["from"] == name and q["state"] != "answered" for q in v2.peek()["asks"].values())
    if waiting and s["state"] == "working":
        with v2.state() as st:
            st["sessions"][name]["state"] = "waiting"  # holds its slot; held warm until its answer wakes it
    if s["state"] in ("done", "parked") or waiting:
        v2.seal(name)
        return
    if s.get("owner"):
        return  # it waits for the owner
    if s["role"] == "planner" and s["state"] == "working":
        # The planner lives across its events. Its turn ends when it has handled what it was given (ctx_gauge.may_end
        # lets it, after its mail is taken); it is then sealed and held warm, and the next event wakes it. The events
        # it was given are cleared here because by that contract they are handled; what it is given and does not
        # handle is given again only if it is lost mid-turn.
        with v2.state() as st:
            st["sessions"][name].update(state="idle", events=[])
        v2.seal(name)
        v2.log(f"{name} has handled what it was given and waits for the next event")
        return
    if at and time.time() - at > IDLE_MAX and (age(f"{name}.woken") or BACKOFF + 1) > BACKOFF:
        # what it is told is the rule that holds for it: a producing session's turn is freed by a park and by
        # nothing else (ctx_gauge.may_end), so telling it that a question of its own would free it is false, and
        # false at the moment it is looking for a way out (2026-09-21)
        rule = ("your turn ends with your result recorded, or once you have parked (`v2.py park run|tree|fix|answer`): "
                "you hold the producing slot and never wait in a turn."
                if s["role"] in v2.PRODUCING else
                "your turn ends when your piece of work has ended, or while you wait on a question of your own.")
        if not v2.resume(name, "Your turn ended before your piece of work did. Continue; " + rule):
            lost(name, "stalled and went cold")


# ---------------------------------------------------------------- holding

def held(st, name, s):
    """Why a sealed session is kept warm, or None."""
    if s.get("released") or s["state"] == "lost" or not s.get("sid"):
        return None
    if name == st["kb"]:
        return "the knowledge base"
    if s["role"] == "planner" and s["state"] == "idle":
        return "the planner, between events"  # one planner lives across them; the next event wakes it
    tasks = st["tasks"]
    t = tasks.get(s.get("task") or "") or {}
    ended = s.get("ended") or s.get("started") or 0
    if s["state"] == "parked":
        return {"run": "waits on its own run", "tree": "waits on the working tree",
                "fix": "waits on its efficiency fix",
                "answer": "waits on the answer to its question"}.get((t.get("parked") or {}).get("for"), "parked")
    if s["state"] == "waiting":
        return "waits on the answer to its question"
    if s["role"] in v2.PRODUCING and t.get("session") == name and t.get("stage") in ("checking", "reviewing", "fixing",
                                                                                     "committing"):
        return f"its task is {t['stage']}"
    x = tasks.get(s.get("reviews") or "") or {}
    if s["role"] == "reviewer" and t.get("reviewed_by") == name and t.get("verdict") == "reject" \
            and x.get("stage") in ("fixing", "checking", "reviewing"):
        return "a re-review may come"
    if time.time() - ended > v2.HOLD_MAX:
        return None
    if s["role"] == "task-designer" and any(x.get("briefed_by") == name and x.get("stage") != "done" for x in tasks.values()):
        return "tasks it briefed are open"
    if s["role"] == "designer":
        for tid, x in tasks.items():
            if x.get("stage") != "done" and s.get("task") in ((v2.read_task(tid) or {}).get("blockedBy") or []):
                return "tasks built on its design are open"
    return None


def pinging(name):
    a = age(f"ping-{name}")
    return a is not None and a < 600


def planner_mail():
    """The planner between its events is sealed and `idle`, which is not LIVE, so care() is never reached for it and
    nothing opens its box. Mail can be left there two ways: plan() posts and, finding it busy, leaves its hooks to
    show it — and its hooks do not run again after its last tool call of the turn — or a resume fails and keep_mail
    puts it back. plan() then returns at once while no new event has come, so what was in the box waited for the next
    event, and with none it waited for ever. On 2026-09-20 the orchestrator worker's message about the worktrees was
    read only because a tool call happened to follow it by half a minute; nothing had made that so."""
    for name, s in v2.peek()["sessions"].items():
        if s["role"] != "planner" or s["state"] != "idle" or s.get("released"):
            continue
        if not v2.has_mail(name) or v2.running_jobs(name):
            continue
        v2.log(f"{name} has mail that its turn did not take; waking it")
        v2.wake_planner(name)  # cold, it cannot be woken: holds() loses it and its events go back


def holds():
    st = v2.peek()
    for name, s in st["sessions"].items():
        if (s["state"] in v2.LIVE and not (s["state"] == "waiting" and s.get("sealed"))) or s.get("released") or (
                s["role"] == "kb" and name != st["kb"]):
            continue
        why = held(st, name, s)
        if why is None:
            if not s.get("sealed") and v2.running_jobs(name):
                continue  # live with jobs of its own: stopping it would kill them
            if s.get("sealed") or s["state"] in ("done", "lost"):
                v2.release(name)
                v2.log(f"released {name}")
            continue
        if s["state"] in ("parked", "waiting") and not v2.warm(name):
            lost(name, "went cold while it waited")
            continue
        if s["state"] == "idle" and not v2.warm(name):
            # a planner whose cache is gone can no longer be resumed (v2.resume refuses a cold session), so an event
            # delivered to it would sit in its box and nothing would ever open it. It is lost here instead: what it
            # was given and had not handled goes back, and the next one forks from the knowledge base.
            lost(name, "went cold between its events")
            continue
        since = (((st["tasks"].get(s.get("task")) or {}).get("parked") or {}).get("since") if s["state"] == "parked" else
                 min((q["asked"] for q in st["asks"].values() if q["from"] == name and q["state"] != "answered"),
                     default=None))
        if s["state"] in ("parked", "waiting") and since and time.time() - since > v2.HOLD_PARK:
            what = "The fix you waited for has not landed" if s["state"] == "parked" else "No answer to your question came"
            if not v2.resume(name, f"{what} within {v2.HOLD_PARK // 3600} hours. Record a partial result now "
                                   f"(`v2.py result {s.get('task')}`): what exists, and what remains."):
                lost(name, "went cold while it waited")
            continue
        if v2.hit_age(name) > v2.PING_AGE and not pinging(name):
            open(os.path.join(STATE, f"ping-{name}"), "w").write(str(time.time()))
            subprocess.Popen([sys.executable, os.path.join(HERE, "v2.py"), "ping", name], stdout=subprocess.DEVNULL,
                             stderr=subprocess.DEVNULL, start_new_session=True)


# ---------------------------------------------------------------- finishing

def finalizer_pids(tid):
    """The finalizer's process and its check's process group (each started as its own session)."""
    try:
        return [int(x) for x in open(os.path.join(v2.BUILD, tid, "finalizer.pid")).read().split()]
    except (OSError, ValueError):
        return []


def finalizer_alive(tid):
    pids = finalizer_pids(tid)
    return bool(pids) and os.path.exists(f"/proc/{pids[0]}")


def end_finalizer(tid):
    """A finalizer given up: it and its check end before its task leaves the working tree."""
    for sig in (signal.SIGTERM, signal.SIGKILL):
        for pid in finalizer_pids(tid):
            try:
                os.killpg(pid, sig)
            except OSError:
                pass
        time.sleep(2)


def finishing():
    st = v2.peek()
    for tid, t in st["tasks"].items():
        stage = t.get("stage")
        if stage in ("checking", "committing"):
            since = t.get("finishing_since")
            if not since:
                with v2.state() as w:
                    w["tasks"][tid]["finishing_since"] = time.time()
                continue
            alive = finalizer_alive(tid)
            why = (f"has not reported within {FINAL_MAX // 60} minutes" if alive and time.time() - since > FINAL_MAX else
                   "ended without reporting" if not alive and time.time() - since > START_GRACE else None)
            if why:
                if alive:
                    end_finalizer(tid)
                with v2.state() as w:
                    w["tasks"][tid]["finishing_since"] = None
                    v2.to_planner(w, tid, "the harness", f"The finalizer of task {tid} {why} ({stage}); see "
                                  f".build/tasks/{tid}/finalize.log.")
        elif t.get("finishing_since"):
            with v2.state() as w:
                w["tasks"][tid]["finishing_since"] = None
    for name, s in st["sessions"].items():
        fix = s.get("fix")
        if fix and s["state"] in v2.LIVE and time.time() - fix["since"] > v2.FIX_MINUTES * 60 + GRACE:
            r = v2.row(name)
            if not r or r["activity"] == "idle":
                lost(name, "outgrew its quick fix's budget")


LAYER_STALE = float(os.environ.get("ORCH_LAYER_STALE", 0.20))
LAYER_EVERY = int(os.environ.get("ORCH_LAYER_EVERY", 900))  # how often the share is looked at


def layers():
    """Refresh a base's frontier layer when what it holds has moved: when the held files changed since the layer
    loaded reach ORCH_LAYER_STALE of its tokens, or when `state/<who>-layer.refresh` asks for one by hand —
    replaying the 30 commits of 2026-09-19 that came to 6 refreshes for the middle base and 7 for the implementation
    one in 15.5 hours, about every 2.5 to 3 hours of continuous work. The stable reference under it is the owner's to
    rebuild and is never touched here."""
    for who in v2.BASES:
        if not os.path.exists(os.path.join(STATE, f"{who}-layer.json")):
            continue
        asked = os.path.exists(os.path.join(STATE, f"{who}-layer.refresh"))
        if not asked and (age(f"{who}-layer.looked") or LAYER_EVERY + 1) < LAYER_EVERY:
            continue
        if os.path.exists(os.path.join(STATE, f"{who}-layer.building")):
            continue  # one refresh of a layer at a time; base.sh holds this while it builds and gives it up at the end
        open(os.path.join(STATE, f"{who}-layer.looked"), "w").write(str(time.time()))
        share = 1.0 if asked else stale_share(who)
        if share < LAYER_STALE:
            continue
        with contextlib.suppress(OSError):
            os.remove(os.path.join(STATE, f"{who}-layer.refresh"))
        v2.log(f"the {who} layer is refreshed: {share:.0%} of what it holds has changed since it loaded"
               if not asked else f"the {who} layer is refreshed, asked for by hand")
        subprocess.Popen(["sh", os.path.join(HERE, "base.sh"), who, "layer"], cwd=v2.PROJECT,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)


def stale_share(who):
    try:
        out = subprocess.run([sys.executable, os.path.join(HERE, "manifest.py"), "stale-share", who],
                             capture_output=True, text=True, timeout=120,
                             env={k: v for k, v in os.environ.items() if k != "ORCH_LOAD_LIST"}).stdout
        return float(out.strip() or 0)
    except (ValueError, OSError, subprocess.SubprocessError) as e:
        # 0.0 reads as "nothing has changed", so the layer is never refreshed and health.py says 0% of a layer that
        # may be wholly stale: the failure is said rather than shown as a measurement
        v2.log(f"ATTENTION the stale share of the {who} layer could not be measured ({e!r}); it reads as 0%")
        return 0.0


def watch():
    """The care of every live session, the finalizations, what is held warm, the archive: each part on its own, so that
    one that fails (logged) holds up nothing else."""
    for name, s in list(v2.peek()["sessions"].items()):
        if (s["state"] in v2.LIVE and not (s["state"] == "waiting" and s.get("sealed"))) or (
                s["role"] == "kb" and not s.get("sealed") and not s.get("released")):
            contained(f"care of {name}", care, name, s)
    for part in (planner_mail, finishing, holds, layers, v2.archive):
        contained(part.__name__, part)


def contained(what, fn, *args):
    try:
        fn(*args)
    except Exception as e:  # noqa: BLE001
        v2.log(f"watchdog error in {what}: {e!r}")


def main():
    if os.path.exists(os.path.join(STATE, "stopped")) or not v2.peek()["active"]:
        return
    v2.dispatch(pre=watch, wait=True)  # the care and the dispatch under one lock


if __name__ == "__main__":
    try:
        main()
    except Exception as e:  # the daemon must survive anything here
        v2.log(f"watchdog error: {e!r}")
        sys.exit(0)
