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
             fixed or committed; its reviewer while a re-review may come; a waiting (parked) session for v2.HOLD_PARK seconds
             (v2.HOLD_TREE when parked for the one tree: v2.hold_of), after which it is resumed to record a partial result; a task designer while
             its proposal waits on the planner (who may send it back to be
             revised: v2.revise_proposal), for at most v2.HOLD_MAX seconds. Anything else is released.
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
import train  # noqa: E402
import finalize  # noqa: E402

STATE = v2.STATE
IDLE_MAX = int(os.environ.get("ORCH_IDLE_MAX", 300))
GONE_CHECKS = int(os.environ.get("ORCH_GONE_CHECKS", 3))
API_RETRY_AFTER = int(os.environ.get("ORCH_API_RETRY_AFTER", 60))  # a turn the API broke off: redone after this
API_RETRIES = int(os.environ.get("ORCH_API_RETRIES", 3))  # in a row, before it is a stall like any other
BACKOFF = int(os.environ.get("ORCH_WAKE_BACKOFF", 600))
# The finalizer waits for Isabelle at most ORCH_ISABELLE_WAIT and runs its check at most ORCH_FINAL_MAX; past both and a
# margin it is given up. A finalizer that is gone without having reported is given up after START_GRACE.
FINAL_MAX = int(os.environ.get("ORCH_ISABELLE_WAIT", 3600)) + int(os.environ.get("ORCH_FINAL_MAX", 3600)) + 600
START_GRACE = 120
GRACE = 180
OWNER_IDLE = int(os.environ.get("ORCH_OWNER_IDLE", 1800))  # an episode the owner left: asked to end


def last_reply(sid):
    """(model, text, epoch) of the last assistant entry, read from the transcript's tail."""
    path = v2.transcript(sid)
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


def replied_between(sid, after, before):
    """Whether the session made a reply of its own (not the harness's synthetic one) between two moments."""
    path = v2.transcript(sid)
    try:
        size = os.path.getsize(path)
        with open(path, "rb") as f:
            f.seek(max(0, size - 2_000_000))
            lines = f.read().decode(errors="ignore").splitlines()
    except OSError:
        return False
    for line in reversed(lines):
        if '"assistant"' not in line:
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("type") != "assistant" or (d.get("message") or {}).get("model") == "<synthetic>":
            continue
        try:
            epoch = datetime.datetime.fromisoformat(d.get("timestamp", "").replace("Z", "+00:00")).timestamp()
        except ValueError:
            continue
        if epoch <= after:
            return False
        if epoch < before:
            return True
    return False


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


def api_failed(name, s):
    """Whether a session's turn ended on the API failing mid-response ("API Error: Server error mid-response…"), and
    is taken care of here: resumed after API_RETRY_AFTER to redo the step its cut reply was making, API_RETRIES times
    in a row at most. It waited for the stall's rule, IDLE_MAX and a ten-minute backoff meant for loops, and was told
    only that its turn had ended (investigate-82, 2026-09-22; the owner: resume it within a minute, and say so). A
    reply of its own since starts the count again."""
    model, said, at = last_reply(s["sid"])
    mark = os.path.join(STATE, f"api-errors-{name}")
    if model != "<synthetic>" or not said.startswith("API Error") or re.search(r"hit your .*limit", said, re.I):
        with contextlib.suppress(OSError):
            os.remove(mark)
        return False
    words = (open(mark).read().split() if os.path.exists(mark) else []) + ["0", "0"]
    n, handled = int(words[0] or 0), float(words[1] or 0)
    if handled and at <= handled:
        return True  # this failure was taken care of: its resume is under way
    if n and replied_between(s["sid"], handled, at):
        # a reply of its own came between: not in a row. plan-35, working again after one failure, was counted "2 of
        # 3 in a row" at its next — the count was reset only when a pass found it idle (2026-09-22 04:08)
        n = 0
    if n >= API_RETRIES:
        return False  # tried enough: the stall's own rule
    if time.time() - at < API_RETRY_AFTER or (age(f"{name}.woken") or API_RETRY_AFTER + 1) <= API_RETRY_AFTER:
        return True  # a moment first
    if not v2.resume(name, f"The API failed mid-response ({said[:160]}): your last reply may be incomplete, and what it "
                           "was about to do may not have been done. Redo that step, and continue."):
        return False
    open(mark, "w").write(f"{n + 1} {at}")
    v2.log(f"{name}: the API failed mid-response; resumed to redo its step ({n + 1} of {API_RETRIES} in a row)")
    return True


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
    # what is in its box is named by v2.release below, which this ends with: it said so here as well, and said the
    # box was kept, which release had just emptied (2026-09-21)
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
    # the listing gives `status` (busy or idle) while the supervisor holds the session; a row carrying only the
    # coarser `state` — `blocked`, a process it no longer runs — stays listed, and counting it as seen kept the
    # gone count from ever reaching GONE_CHECKS: a session in that state would hold its slot for ever with nothing
    # said, since `gone` is only consulted when there is no row at all (2026-09-21)
    if r["activity"] not in ("busy", "idle"):
        if s["role"] != "kb" and api_failed(name, s):
            return  # a turn the API broke off leaves its session blocked, which is not gone
        if s["state"] in v2.LIVE and gone(name):
            lost(name, f"is listed as {r['activity']} and no turn of it runs")
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
    if api_failed(name, s):
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
    run = v2.machine_wait(s)
    if run:  # its turn ended waiting for the machine, which refused its run: woken when one may start, not before
        if not v2.run_blocked((s.get("task"), s.get("reviews")), run) and (age(f"{name}.woken") or 61) > 60:
            if not v2.resume(name, "A run may start on the machine now: run your check and continue."):
                lost(name, "went cold while it waited for the machine")
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
                "answer": "waits on the answer to its question",
                "machine": "waits on a free run"}.get((t.get("parked") or {}).get("for"), "parked")
    if s["state"] == "waiting":
        return "waits on the answer to its question"
    if s["role"] in v2.PRODUCING and t.get("session") == name and t.get("stage") in ("checking", "reviewing", "fixing",
                                                                                     "committing"):
        return f"its task is {t['stage']}"
    if s["role"] in v2.PRODUCING and v2.may_come_back(st, name, s):
        return "its task may come back to it"  # resumed when the planner queues it again (v2.reusable)
    x = tasks.get(s.get("reviews") or "") or {}
    if s["role"] == "reviewer" and t.get("reviewed_by") == name and t.get("verdict") == "reject":
        if x.get("stage") in ("fixing", "checking", "reviewing"):
            return "a re-review may come"
        # and while the fix waits (parked, with the planner, queued again), within the hold's bound: held only in the
        # three stages above, review-23 was released when its task's fix parked for the tree and review-47 when its
        # task went back to the planner (2026-09-21), and each re-review then needs a reviewer that reads all again
        if x.get("stage") not in (None, "done", "deleted") and time.time() - ended <= v2.HOLD_MAX:
            return "a re-review may come once the fix continues"
    # One that accepted, while the task it accepted has not landed: its commit refused, its landing not merging or
    # failing, a partial result, sent back to the planner and worked on again — each came back to a fresh reviewer that
    # read it all again, 11 of them on 2026-09-21/22 (119 requests, 9.1M; start_review resumes this one instead)
    if s["role"] == "reviewer" and v2.accepted_by(t) == name and x.get("stage") not in ("done", "deleted") \
            and (v2.read_task(s.get("reviews") or "") or {}).get("status") not in ("completed", None) \
            and time.time() - ended <= v2.HOLD_MAX and not os.path.exists(os.path.join(STATE, "flags", f"{s.get('sid')}.soft")):
        return "the task it accepted has not landed"
    if time.time() - ended > v2.HOLD_MAX:
        return None
    # a proposal is not final until the planner places it, and the one moment a correction is likely is before: held
    # only while tasks it briefed were open, a task designer was released three seconds after its result, and the
    # planner's `v2.py tell` found no session — brief 13 was re-planned and briefed again whole (2026-09-21)
    if s["role"] == "task-designer" and t.get("session") == name and t.get("stage") == "proposed":
        return "its proposal waits on the planner"
    # Not held to be asked: a task designer while tasks it briefed were open, a designer while tasks built on its
    # design were, was pinged for questions none ever came — none in the whole run of 2026-09-21/22, against 26 pings
    # and 16.4M tokens read (design-66 still pinged an hour after it had landed), and a question to an author gone
    # cold is answered by the knowledge base (the owner: stop keeping alive what is never asked, 2026-09-22)
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
        hold = v2.hold_of(st["tasks"].get(s.get("task")) or {}) if s["state"] == "parked" else v2.HOLD_PARK
        if s["state"] in ("parked", "waiting") and since and time.time() - since > hold:
            kind = ((st["tasks"].get(s.get("task")) or {}).get("parked") or {}).get("for", "fix")
            what = {"fix": "The fix you waited for has not landed", "run": "Your run has not ended",
                    "tree": "The working tree has not come free for you", "answer": "No answer to your question came",
                    "machine": "No run could start on the machine"}.get(kind) if s["state"] == "parked" else \
                "No answer to your question came"
            if not v2.resume(name, f"{what} within {hold // 3600} hours. Record a partial result now "
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
    landers = checkers = False
    for tid, t in st["tasks"].items():
        stage = t.get("stage")
        if stage in ("checking", "committing"):
            if t.get("held_finalizer"):
                continue  # held with the graph (v2.reopen_unlanded): no finalizer is meant to run until it is released
            if stage == "checking" and t.get("check_again"):
                again = t["check_again"]
                if not finalizer_alive(tid) and (time.time() - again.get("at", 0) >= finalize.BASE_RETRY
                                                 or finalize.active_pointer() != again.get("pointer")):
                    with v2.state() as w:
                        w["tasks"][tid].pop("check_again", None)
                        w["tasks"][tid]["finishing_since"] = None
                    v2.log(f"task {tid}'s check, refused by the proof base, is run again")
                    v2.background("finalize.py", "check", tid)
                continue
            if stage == "checking" and train.CHECK_QUEUE.queued(tid):
                # its check waits in the check queue: the next batch checks it, whoever runs it (train.run_batcher)
                checkers = checkers or finalizer_alive(tid)
                continue
            if stage == "committing":
                d = train.decision(tid)
                if d and d.get("what") == "landed":
                    # landed, and its report is the lander's to make once it lets main go; one never made (the lander
                    # ended) is made here: task 151 landed at 15:30:23 and was taken for a finalizer that had ended
                    # without reporting, and sent to the planner (2026-09-22)
                    with v2.landing(time.time()) as free:
                        pass
                    if free and not train.lander_alive() and time.time() - d.get("decided", 0) > 60:
                        v2.log(f"task {tid} landed as {d.get('ref')}; its report was never made: it is made now")
                        v2.committed(tid, d.get("ref"), None)
                    continue
            if stage == "committing" and train.queued(tid):
                # committed on its branch and queued: the next train lands it, whoever lands it (train.run_lander)
                landers = landers or finalizer_alive(tid)
                continue
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
    asked = [tid for tid, e in train.CHECK_QUEUE.peek().items() if not e.get("decided")]
    if asked and not checkers and not train.batcher_alive():
        v2.log(f"the check queue holds task{'s' if len(asked) > 1 else ''} {train.listing(asked)} and nobody checks "
               "it: a batcher starts")
        v2.background("finalize.py", "check-batch")
    waiting = [tid for tid, e in train.peek().items() if not e.get("decided")]
    if waiting and not landers and not train.lander_alive():
        v2.log(f"the landing queue holds task{'s' if len(waiting) > 1 else ''} {train.listing(waiting)} and nobody "
               "lands it: a lander starts")
        v2.background("finalize.py", "land-queue")
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
    one in 15.5 hours, about every 2.5 to 3 hours of continuous work. The stable reference under it is not rebuilt
    here: a refresh that finds its stable base's own cache entry cold loads that base again first (base.sh restable,
    the owner, 2026-09-21), since a fork of it would write it whole and every refresh after would too."""
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
    for part in (planner_mail, finishing, holds, layers, v2.lands_when_free, v2.archive, isabelle_snapshot):
        contained(part.__name__, part)


def isabelle_snapshot():
    """The Isabelle processes on this machine and the run each is counted in (v2.isabelle_run_roots), written while
    there are any to state/isabelle-processes.json: the watchdog sees the machine's processes, and a session's sandbox
    does not. The count was in processes, the limit in runs (2026-09-21); this shows what one run is on the machine,
    and it is the count a sandboxed command reads (v2.isabelle_runs), so it is written every pass, no run too."""
    procs = v2.machine_processes()
    roots = v2.isabelle_run_roots(procs)  # written every pass, none too: a sandboxed command reads its count here

    def chain(pid, depth=12):
        out = []
        while pid in procs and len(out) < depth:
            out.append({"pid": pid, "name": procs[pid][1], "command": procs[pid][2][:240]})
            pid = procs[pid][0]
        return out
    def rss_mb(pid):  # its resident memory, to judge the probes' limit by (PROBE_MAX)
        with contextlib.suppress(OSError, ValueError, IndexError):
            for line in open(f"/proc/{pid}/status"):
                if line.startswith("VmRSS:"):
                    return int(line.split()[1]) // 1024
        return None
    kinds = {root: v2.run_kind(procs.get(root, (0, "", ""))[2]) for root in set(roots.values())}
    unseen = v2.unseen_finalizer_runs(procs)  # let start, preparing, no Isabelle yet: a sandbox counts them from here

    def in_sandbox(pid, depth=40):  # a session's run: under bwrap, the sandbox of a session's command
        while pid in procs and depth:
            if procs[pid][1] == "bwrap":
                return True
            pid, depth = procs[pid][0], depth - 1
        return False
    snapshot = {"at": v2.iso(), "memory_available_gb": v2.memory_available_gb(),
                "runs": len(kinds) + unseen, "heavy": list(kinds.values()).count("heavy") + unseen, "unseen": unseen,
                "roots": [{"pid": root, "kind": kind, "started": v2.process_started(root), "session": in_sandbox(root)}
                          for root, kind in kinds.items()],  # what a session's mark is matched with (v2.session_marks)
                "probes": list(kinds.values()).count("probe"),
                "processes": [{"pid": pid, "run": root, "kind": kinds[root], "rss_mb": rss_mb(pid),
                               "run_command": procs.get(root, (0, "", ""))[2][:240], "ancestors": chain(pid)}
                              for pid, root in sorted(roots.items())]}
    tmp = os.path.join(STATE, "isabelle-processes.json.tmp")
    with open(tmp, "w") as f:
        json.dump(snapshot, f, indent=1)
    os.replace(tmp, os.path.join(STATE, "isabelle-processes.json"))


def contained(what, fn, *args):
    """One part of a pass, on its own: its failure is logged and holds up nothing else, and one that takes longer
    than v2.SLOW_PART is named — a pass of 04:19:30–04:27:07 on 2026-09-22 held every resume and start for seven
    minutes, and nothing said which part."""
    began = time.time()
    try:
        fn(*args)
    except Exception as e:  # noqa: BLE001
        v2.log(f"watchdog error in {what}: {e!r}")
    took = time.time() - began
    if took > v2.SLOW_PART:
        v2.log(f"the watchdog's {what} took {took:.0f} s")


def main():
    v2.keep_pointer_links()  # stopped or not: the owner's own checks read the base's places too
    if os.path.exists(os.path.join(STATE, "stopped")) or not v2.peek()["active"]:
        return
    v2.dispatch(pre=watch, wait=True)  # the care and the dispatch under one lock


if __name__ == "__main__":
    try:
        main()
    except Exception as e:  # the daemon must survive anything here
        v2.log(f"watchdog error: {e!r}")
        sys.exit(0)
