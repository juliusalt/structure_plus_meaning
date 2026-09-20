#!/usr/bin/env python3
"""Orchestration v2: a knowledge base, planning episodes, and one session per piece of work
(notes/orchestration-v2-plan.md).

Every self-contained piece of work is a fork: of a sealed base, of the knowledge base, or of a sealed session that is
consulted. A resume only continues the same piece of work (a quick fix, a re-review, an implementer woken after the
efficiency fix it waited for). A session whose cache has expired is never woken or forked.

  knowledge base   kb-N: a fork of the planner's base that never works; its context is what has been integrated
                   into it (HANDOFF.md, the owner's words, the notes of every planning episode). Sealed between
                   integrations; questions to it are answered by forks of it.
  planner          plan-N: a planning episode, a fork of the knowledge base on a batch of events; it orders the
                   graph, decides, writes its notes for the knowledge base, and ends.
  producing        design-ID, investigate-ID, implement-ID, fix-ID: one at a time, by the task's kind.
  supporting       brief-ID (a task designer), review-ID (a reviewer): one at a time, beside the producing one.
  quick fix        the task's own session resumed (or a fixer) after a failed check or a rejected review, once.
  consultation     ask-N: a fork of the consulted session (the knowledge base, an author) answering one question.

Commands of the sessions (the caller is known from CLAUDE_CODE_SESSION_ID):
  v2.py step ID N SOURCE...      open step N: every source it needs printed at once, free of the reading limits
  v2.py ask --to WHOM TEXT       a question to kb, planner, designer, task-designer or reviewer
  v2.py reply QID TEXT|--file F [--decision]   answer a question (a consultation, the planner)
  v2.py tell ID TEXT             the planner (or the owner): tell the sessions working on task ID what changes their work
  v2.py escalate --efficiency TEXT   a performance problem, reported to the planner (its fix becomes a task); go on
  v2.py park run|fix|tree|answer   nothing productive left: park, the producing slot free for another worker, until
                                 the run ends, the fix lands, the working tree is free or the answer comes
  v2.py finalize ID --check CMD --files PATH... --message FILE   hand over the final check and the commit
  v2.py result ID                record the result written to .build/tasks/ID/result.md
  v2.py briefed ID [NEW...]      the task designer: the briefs are in the task list, in form
  v2.py verdict ID accept|reject --file FILE   the reviewer (or the planner, for design and investigation)
  v2.py queue ID...              the planner: the order in which tasks are to be done
  v2.py after ID TASK            the planner: the parked task ID continues when TASK has landed (`none`: now)
  v2.py drop ID                  the planner: stop whatever works on task ID
  v2.py planned --notes FILE     the planner: the episode ends; its notes go to the knowledge base
Harness:
  v2.py start | stop | status | graph | who ROLE | dispatch | talk | ping NAME
"""
import contextlib
import fcntl
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
PROJECT = os.environ.get("ORCH_PROJECT") or os.path.dirname(os.path.dirname(HERE))
STATE = os.environ.get("ORCH_STATE_DIR") or os.path.join(HERE, "state")
TRANSCRIPTS = os.environ.get("ORCH_TRANSCRIPTS") or os.path.expanduser(
    "~/.claude/projects/" + PROJECT.replace("/", "-").replace("_", "-"))
LIST = os.environ.get("ORCH_TASK_LIST", "orchestration-graph")
TASKS = os.path.expanduser(os.environ.get("ORCH_TASKS_DIR", "~/.claude/tasks"))
BUILD = os.path.join(PROJECT, ".build", "tasks")
PROTOCOLS = os.path.join(HERE, "protocols")

# The kinds of task: every piece of work beyond a consultation is a task of the graph, planned in the brief's form by the
# same machinery (the planner, the task designer): producing kinds, detailing (brief) and reviews.
PRODUCING_KINDS = ("design", "investigate", "build", "fix")
KINDS = PRODUCING_KINDS + ("brief", "review")
BRIEF_FIELDS = ("Kind", "Serves", "Deliverable", "Acceptance", "Inputs", "Plan", "Size")
# every field of the brief's form (protocols/_brief.md): a field's text runs to the next one
FORM_FIELDS = BRIEF_FIELDS + ("Reviews", "Decided", "Yours", "Planner's", "While checks run")

RESULT_SECTIONS = ("Produced", "Decisions", "Plan as followed", "Remains")
PLANNER_SECTIONS = ("Graph", "Decisions", "Delivered", "Open", "Now")

# Roles: what a session of the role forks (a base, "kb", or for a consultation the consulted session), its settings
# (a fork uses its origin's: the knowledge base's forks all take planner-settings.json), the prefix of its name,
# whether it reads statements only, and whether it may edit the task graph.
BASES = ("max", "xhigh", "high")  # the planner's base (max), the middle base (xhigh), the implementation base (high)
FALLBACK = {"xhigh": ("max",), "high": ("max",)}  # until the base topic builds them, their roles fork the present base
ROLES = {
    "kb": dict(origin="max", settings="planner-settings.json", prefix="kb", statements=True, graph=False),
    "planner": dict(origin="kb", settings="planner-settings.json", prefix="plan", statements=True, graph=True),
    "designer": dict(origin="xhigh", settings="worker-settings.json", prefix="design", statements=False, graph=False),
    "task-designer": dict(origin="xhigh", settings="planner-settings.json", prefix="brief", statements=True, graph=True),
    "investigator": dict(origin="xhigh", settings="worker-settings.json", prefix="investigate", statements=False, graph=False),
    "reviewer": dict(origin="xhigh", settings="worker-settings.json", prefix="review", statements=False, graph=False),
    "implementer": dict(origin="high", settings="worker-settings.json", prefix="implement", statements=False, graph=False),
    "fixer": dict(origin="high", settings="worker-settings.json", prefix="fix", statements=False, graph=False),
    "consultant": dict(origin=None, settings=None, prefix="ask", statements=None, graph=False),
}
PRODUCER = {"design": "designer", "investigate": "investigator", "build": "implementer", "fix": "fixer"}
PRODUCING, SUPPORTING = set(PRODUCER.values()), {"task-designer", "reviewer"}
LIVE = ("starting", "working", "waiting")  # a session in one of these holds its slot

JOB_STALE = int(os.environ.get("ORCH_JOB_STALE", 7200))  # a background job whose output stands still this long is dead
SPEC_ERRORS = int(os.environ.get("ORCH_SPEC_ERRORS", 2))  # tries at a check command that is not runnable
FIX_MINUTES = int(os.environ.get("ORCH_FIX_MINUTES", 15))
BRIEF_BACKLOG = int(os.environ.get("ORCH_BRIEF_BACKLOG", 6))  # open build and fix tasks past which no brief is detailed:
# a brief task is the graph's multiplier (one turned into 26 tasks on 2026-09-20), and the supporting slot detailing work while the builders are blocked makes the queue diverge from what they can consume (the owner, 2026-09-20)
WORKERS_MAX = int(os.environ.get("ORCH_WORKERS", 1))  # sessions working at once, over every slot: the owner's
# choice of 2026-09-20, to spend the usage window at a rate that outlasts it
CONSULT_MAX = int(os.environ.get("ORCH_CONSULT_MAX", 4))  # consultations at once: each a fork, answering one question
FIX_ROUNDS = int(os.environ.get("ORCH_FIX_ROUNDS", 8))
# Between two productions a session takes at most ROUNDS requests and reads at most READ_TOKENS tokens; the same failure
# after fixes CIRCLING times in a row stops its checks (work_meter.py enforces them; the protocols state them).
ROUNDS = int(os.environ.get("ORCH_ROUNDS", 3))  # the owner's choice of 2026-09-19: few rounds force batched reading
READ_TOKENS = int(os.environ.get("ORCH_READ_TOKENS", 20_000))
CIRCLING = int(os.environ.get("ORCH_CIRCLING", 3))
GATHER_CHARS = 120_000  # what one gather prints: within what a Bash result shows whole (bashOutputMaxChars 128,000 in
# every settings file; Claude Code saves a longer output to a file and shows a preview)
PAUSE = float(os.environ.get("ORCH_PAUSE", 2))  # between stopping a session and resuming it, and between listings
START_MAX = 120  # a start claimed this long ago that has no session yet is abandoned
RETRY = int(os.environ.get("ORCH_START_RETRY", 600))  # an unconfirmed start is tried again after this
# The prompt cache lives an hour past its last hit (promptCacheTtl 1h): a session is warm while its last hit is younger
# than WARM_MAX; a held session is pinged when its last hit is PING_AGE old.
WARM_MAX = int(os.environ.get("ORCH_WARM_MAX", 3300))
PING_AGE = int(os.environ.get("ORCH_PING_AGE", 2700))
HOLD_PARK = int(os.environ.get("ORCH_HOLD_PARK", 3 * 3600))  # the owner's choice: a waiting implementer, 3 hours
HOLD_MAX = int(os.environ.get("ORCH_HOLD_MAX", 3 * 3600))  # an author held for consultation, at most
EPISODE_GAP = int(os.environ.get("ORCH_EPISODE_GAP", 900))  # events arriving within this are batched into one
URGENT_GAP = int(os.environ.get("ORCH_URGENT_GAP", 300))  # and this is the floor when nothing can be produced
# 23 of the 48 sessions of 2026-09-20 were planning episodes, each a fork of the knowledge base at about 510K:
# the bypass fired on single events while the queue stood blocked, which is most of the time (the owner)
KB_MARGIN = 50_000  # a fresh knowledge base loading within this of its limit asks for condensing and a base rebuild  # events arriving within this are batched into one episode
# The window: the largest request the API has accepted (an implementer's, 972,479 tokens); the notice to end the
# piece of work comes at SOFT, the end mark at HARD (ctx_gauge.py).
CEILING = int(os.environ.get("ORCH_CEILING", 972_000))
SOFT = int(os.environ.get("ORCH_SOFT", CEILING - 65_000))
HARD = int(os.environ.get("ORCH_HARD", CEILING - 30_000))
# The room a fork of the knowledge base needs before its notice: a fork starts with the knowledge base's whole context.
# Planning episodes and consultations fork it, so it is rebuilt before it leaves them less than their room. Estimates,
# to be measured. A designer forks the middle base (xhigh), which holds the working frontier a design needs (the owner,
# 2026-09-19), and reads HANDOFF.md in its first gather; a design task has the room its base leaves, like every other
# (the owner, 2026-09-19: no separate cap).
ROOM = {"planner": int(os.environ.get("ORCH_ROOM_PLANNER", 150_000)),
        "consultant": int(os.environ.get("ORCH_ROOM_CONSULTANT", 60_000))}
KB_MAX = int(os.environ.get("ORCH_KB_MAX", SOFT - max(ROOM["planner"], ROOM["consultant"])))
PROTOCOL_ROOM = 20_000  # a session's first message (protocol and brief) and its first gather, within its room
# A background session does not take the launching shell's environment (README, verified 2026-09-18), but the
# `claude` command that launches it runs in it: from inside a session it would see that session's id, messaging
# socket and effort, and the planner's task list (planner-settings.json). Every launch runs without them.
INHERITED = {"CLAUDECODE", "CLAUDE_CODE_ENTRYPOINT", "CLAUDE_CODE_EXECPATH", "CLAUDE_CODE_SESSION_ID",
             "CLAUDE_CODE_CHILD_SESSION", "CLAUDE_CODE_SESSION_ATTENDED", "CLAUDE_CODE_MESSAGING_SOCKET",
             "CLAUDE_CODE_MESSAGING_TOKEN", "CLAUDE_CODE_TASK_LIST_ID", "CLAUDE_PID", "CLAUDE_EFFORT", "AI_AGENT"}


HARNESS = "[harness] "  # what the harness says to a session begins so: never the owner's words (extract_owner_directions)
LEDGER = os.environ.get("ORCH_LEDGER") or os.path.join(HERE, "owner-ledger.md")


# ---------------------------------------------------------------- state, under a lock

DEFAULTS = {"active": False, "kb": None, "counters": {}, "sessions": {}, "tasks": {}, "queue": [], "events": [],
            "notes": [], "asks": {}}


@contextlib.contextmanager
def state():
    """The orchestration's state, read and written under one lock."""
    os.makedirs(STATE, exist_ok=True)
    with open(os.path.join(STATE, "v2.lock"), "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        path = os.path.join(STATE, "v2.json")
        try:
            st = json.load(open(path))
        except (OSError, ValueError):
            st = {}
        for key, empty in DEFAULTS.items():
            st.setdefault(key, json.loads(json.dumps(empty)))
        yield st
        tmp = path + ".tmp"
        json.dump(st, open(tmp, "w"), indent=1)
        os.replace(tmp, path)


def peek():
    """The state without taking the lock (hooks read it on every tool call)."""
    try:
        st = json.load(open(os.path.join(STATE, "v2.json")))
    except (OSError, ValueError):
        st = {}
    for key, empty in DEFAULTS.items():
        st.setdefault(key, json.loads(json.dumps(empty)))
    return st


def count(st, key):
    st["counters"][key] = st["counters"].get(key, 0) + 1
    return st["counters"][key]


def role_of(session):
    """(role, record) of a session by its id, or (None, None)."""
    if not session:
        return None, None
    for rec in peek()["sessions"].values():
        if rec.get("sid") == session:
            return rec["role"], rec
    return None, None


def caller():
    """The record of the session running this command, or None (the owner, the harness)."""
    return role_of(os.environ.get("CLAUDE_CODE_SESSION_ID"))[1]


def log(text):
    os.makedirs(STATE, exist_ok=True)
    with open(os.path.join(STATE, "v2.log"), "a") as f:
        f.write(time.strftime("%Y-%m-%dT%H:%M:%S ") + text + "\n")


def iso(epoch=None):
    """A moment in the form of the transcripts' timestamps (UTC, milliseconds), so that the two compare as strings."""
    epoch = time.time() if epoch is None else epoch
    return time.strftime("%Y-%m-%dT%H:%M:%S", time.gmtime(epoch)) + f".{int(epoch * 1000) % 1000:03d}Z"


def event(st, sender, text):
    """Something for the next planning episode."""
    st["events"].append({"at": time.strftime("%Y-%m-%dT%H:%M:%S"), "from": sender, "text": text})


# ---------------------------------------------------------------- the owner's words

def owner_said(rec, text):
    """The owner typed to a session (its UserPromptSubmit hook, ctx_gauge.py owner): the words are recorded verbatim and
    dated in the owner ledger, and every session but a planning episode (which acts on them itself) turns them into an
    event for the next planning episode, so that they reach the graph and the knowledge base."""
    where = f"to {rec['name']} ({rec['role']}" + (f", task {rec['task']}" if rec.get("task") else "") + ")"
    entry = (f"**{time.strftime('%Y-%m-%d %H:%M')}** ({where}; recorded by the harness):\n\n"
             + "\n".join("> " + ln if ln.strip() else ">" for ln in text.splitlines()) + "\n\n")
    with open(LEDGER + ".lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            s = open(LEDGER).read()
        except OSError:
            s = "# Owner ledger\n\n## Owner directions\n\n## Open questions to the owner\n"
        at = s.find("## Open questions to the owner")
        s = s[:at] + entry + s[at:] if at >= 0 else s.rstrip("\n") + "\n\n" + entry
        open(LEDGER + ".tmp", "w").write(s)
        os.replace(LEDGER + ".tmp", LEDGER)
    if rec["role"] != "planner":
        with state() as st:
            event(st, "the owner", f"The owner said {where}: {text}")
    log(f"the owner spoke {where}")


# ---------------------------------------------------------------- mail

def mailbox(name):
    return os.path.join(STATE, "mail", name + ".jsonl")


def post(name, sender, text):
    os.makedirs(os.path.join(STATE, "mail"), exist_ok=True)
    with open(mailbox(name), "a") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        f.write(json.dumps({"from": sender, "text": text, "at": time.strftime("%Y-%m-%dT%H:%M:%S")}) + "\n")


def take_mail(name):
    """The unread messages for a session, as one text, and the mailbox emptied; "" when there are none."""
    try:
        with open(mailbox(name), "r+") as f:
            fcntl.flock(f, fcntl.LOCK_EX)
            lines = [json.loads(line) for line in f if line.strip()]
            f.seek(0)
            f.truncate()
    except (OSError, ValueError):
        return ""
    return "\n\n".join(f"Message from {m['from']} ({m['at']}):\n{m['text']}" for m in lines)


def has_mail(name):
    try:
        return os.path.getsize(mailbox(name)) > 0
    except OSError:
        return False


def deliver(name, sender, text):
    """Mail a session; one whose turn has ended while it still works on its piece of work (waiting on a question) is
    resumed with the mail when its cache is warm. A busy session receives its mail through its hooks. A session that
    is done, lost or released reads nothing ever again, and mail to it is said to have reached nobody rather than
    left in a box no one opens."""
    s = peek()["sessions"].get(name) or {}
    if s.get("state") in ("done", "lost") or s.get("released"):
        log(f"ATTENTION mail to {name} reached nobody ({s.get('state')}): {text[:160]}")
        return
    post(name, sender, text)
    if s.get("state") not in ("working", "waiting"):
        return
    r = row(name)
    if r and (r["activity"] == "busy" or running_jobs(name)):
        return
    mail = take_mail(name)
    if mail and not resume(name, mail):
        post(name, "the harness", mail)  # kept for when it runs again


# ---------------------------------------------------------------- sessions

def claude(*args, cwd=None):
    env = {k: v for k, v in os.environ.items() if k not in INHERITED}
    return subprocess.run(["claude", *args], capture_output=True, text=True, cwd=cwd or PROJECT, env=env)


def row(name):
    out = subprocess.run([os.path.join(HERE, "session_row.py"), name], capture_output=True, text=True).stdout.split()
    return dict(zip(("kind", "id", "activity", "sid", "state"), out)) if len(out) >= 4 else None


def base_record(who):
    """(name, record) of a sealed base, falling back to the present base while the base topic has not built it."""
    for name in (who,) + FALLBACK.get(who, ()):
        try:
            b = json.load(open(os.path.join(STATE, f"{name}-base.json")))
            return name, {"sid": b["sessionId"], "model": b["model"], "effort": b["effort"]}
        except (OSError, ValueError, KeyError):
            continue
    return None, None


def origin_of(origin):
    """(name, record) of what a fork starts from: a base by its name, "kb" for the knowledge base, or a session."""
    if origin in BASES:
        return base_record(origin)
    st = peek()
    name = st["kb"] if origin == "kb" else origin
    rec = st["sessions"].get(name or "")
    return (name, rec) if rec and rec.get("sid") else (None, None)


def hits(name):
    return os.path.join(STATE, "hits", name)


def hit(name):
    """A request read this session's (or base's) cache: its entry lives another TTL."""
    if name in BASES:
        for mark in ("hit", "used"):
            path = os.path.join(STATE, f"{name}-base.{mark}")
            open(path, "a").close()
            os.utime(path)
        return
    os.makedirs(os.path.join(STATE, "hits"), exist_ok=True)
    open(hits(name), "a").close()
    os.utime(hits(name))


def hit_chain(name):
    """A session's request reads its own prefix, and so its origin's: each is hit, down to the base."""
    seen = set()
    while name and name not in seen:
        seen.add(name)
        hit(name)
        name = None if name in BASES else (peek()["sessions"].get(name) or {}).get("origin")


def hit_age(name):
    path = os.path.join(STATE, f"{name}-base.hit") if name in BASES else hits(name)
    try:
        return time.time() - os.path.getmtime(path)
    except OSError:
        return float("inf")


def warm(name):
    return hit_age(name) < WARM_MAX


def stale(who):
    """The line naming the held files of that base that changed since it was loaded (manifest.py)."""
    out = subprocess.run([os.path.join(HERE, "manifest.py"), "changed", who], capture_output=True, text=True).stdout
    return out.strip() or "no held file has changed since the load"


def fork(org, name, settings, prompt, cwd=None):
    """A session-level fork, with the lean tool set every fork must share and its origin's model and effort; its row
    or None."""
    claude("--bg", "--resume", org["sid"], "--fork-session",
           *open(os.path.join(HERE, "session-flags")).read().split(), "--model", org["model"],
           "--effort", org["effort"], "--permission-mode", "auto", "--autocompact", "1M",
           "--settings", os.path.join(HERE, settings), "-n", name, prompt, cwd=cwd)
    for _ in range(15):
        r = row(name)
        if r:
            if os.environ.get("ORCH_CACHE_CHECK", "1") != "0":
                subprocess.Popen([sys.executable, os.path.join(HERE, "v2.py"), "cache-check", r["sid"], org["sid"], name],
                                 stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
            return r
        time.sleep(PAUSE)
    return None


def fresh_name(st, prefix, key):
    name, n = f"{prefix}-{key}", 1
    while name in st["sessions"]:
        n += 1
        name = f"{prefix}-{key}.{n}"
    return name


def launch(role, key, prompt_of, **fields):
    """Fork a session for a piece of work: claim it in the state, fork its origin (never a cold session), confirm it.
    prompt_of(name) gives its first message. Its name, or None."""
    spec = ROLES[role]
    origin = fields.pop("origin", None) or spec["origin"]
    who, org = origin_of(origin)
    if not org:
        log(f"no {role} started for {key}: its origin {origin} does not exist")
        return None
    if who not in BASES and not warm(who):
        log(f"no {role} started for {key}: {who} is cold")
        return None
    settings = fields.pop("settings", None) or spec["settings"] or org.get("settings")
    with state() as st:
        name = fresh_name(st, spec["prefix"], key)
        st["sessions"][name] = dict(name=name, role=role, origin=who, model=org["model"], effort=org["effort"],
                                    settings=settings, state="starting", starting=time.time(), **fields)
    hit_chain(who)
    tree = worktree(key) if TREES and role in PRODUCING and str(key).isdigit() and not in_main_tree(key) else None
    if tree:
        with state() as st:
            st["sessions"][name]["tree"] = os.path.relpath(tree, PROJECT)
    r = fork(org, name, settings, prompt_of(name), cwd=tree)
    with state() as st:
        s = st["sessions"][name]
        if not r:
            s["state"] = "lost"
            log(f"start of {name} not confirmed")
            return None
        s.update(sid=r["sid"], id=r["id"], state="working", started=time.time())
    hit(name)
    log(f"started {name} ({role}, from {who})")
    return name


def resume(name, text):
    """Continue a session's own piece of work with a message: only while its cache is warm. A live session is stopped
    first (a bare resume keeps its id, options, hooks and cache); `<name>.woken` tells attach.sh it was a wake."""
    s = peek()["sessions"].get(name) or {}
    if not s.get("sid") or not warm(name):
        return False
    r = row(name)
    if r and running_jobs(name):  # stopping it would kill its jobs: their completion runs its turn, and the mail with it
        post(name, "the harness", text)
        with state() as st:
            if st["sessions"][name]["state"] in ("done", "parked", "waiting"):
                st["sessions"][name]["state"] = "working"
        log(f"{name} has running jobs: its message waits as mail")
        return True
    with open(os.path.join(STATE, f"{name}.woken"), "a") as f:
        f.write(time.strftime("%Y-%m-%dT%H:%M:%S ") + text.split("\n", 1)[0][:100] + "\n")
    if r:
        claude("stop", r["id"])
        time.sleep(PAUSE)
    claude("--bg", "--resume", s["sid"], HARNESS + text, cwd=tree_of(s))
    with state() as st:
        rec = st["sessions"][name]
        rec["sealed"] = False
        if rec["state"] in ("done", "parked", "waiting"):
            rec["state"] = "working"
    hit(name)
    log(f"resumed {name}")
    return True


def job_stale(job, output):
    """A background job whose output file has stood still for JOB_STALE is dead: the session was stopped, or the job
    was, and no completion will come. Without the fallback a job that never reports holds its session's mail and its
    resume for ever (2026-09-20: a stopped job held one for eight hours)."""
    try:
        idle = time.time() - os.path.getmtime(output)
    except (OSError, TypeError):
        return False  # nothing to judge it by: it counts as running
    if idle > JOB_STALE:
        log(f"job {job}: its output has stood still for {int(idle) // 60} minutes; it counts as ended")
        return True
    return False


def running_jobs(name):
    """The background jobs a session started that have not completed (from its transcript): stopping the session, to
    seal or to resume it, would kill them."""
    s = peek()["sessions"].get(name) or {}
    try:
        path = f"{TRANSCRIPTS}/{s['sid']}.jsonl"
        size = os.path.getsize(path)
        with open(path, "rb") as f:
            f.seek(max(0, size - 4_000_000))
            text = f.read().decode(errors="ignore")
    except (OSError, KeyError):
        return []
    started = dict.fromkeys(re.findall(r"running in background with ID: (\w+)", text))
    out = {j: m.rstrip(".,;)") for j, m in  # the transcript is JSON: the path ends at a quote, a brace or the sentence
           re.findall(r"running in background with ID: (\w+)\. Output is being written to: ([^\s\"'\\]+)", text)}
    return [j for j in started
            if not re.search(rf"<task-id>{re.escape(j)}</task-id>.*?<status>", text, re.S)
            and not re.search(rf"Successfully stopped task: {re.escape(j)}\b", text)
            and not job_stale(j, out.get(j))]


def seal(name):
    """Stop a session whose turn has ended: it can still be resumed or forked while it is warm."""
    r = row(name)
    if r:
        claude("stop", r["id"])
    with state() as st:
        if name in st["sessions"]:
            st["sessions"][name]["sealed"] = True


def forget(sid):
    """What the hooks kept about a session: its guard state, its production snapshots, its window marks."""
    if not sid:
        return
    for path in (os.path.join(STATE, f"work-{sid}.json"), os.path.join(STATE, "flags", f"{sid}.soft"),
                 os.path.join(STATE, "flags", f"{sid}.hard")):
        with contextlib.suppress(OSError):
            os.remove(path)
    shutil.rmtree(os.path.join(STATE, f"work-{sid}.snap"), ignore_errors=True)


def release(name):
    """A session nothing refers to any more: stopped, its listing removed, its guard state forgotten."""
    s = peek()["sessions"].get(name) or {}
    r = row(name)
    if r:
        claude("stop", r["id"])
    if s.get("id"):
        claude("rm", s["id"])
    forget(s.get("sid"))
    with state() as st:
        if name in st["sessions"]:
            st["sessions"][name].update(sealed=True, released=True)
            if st["sessions"][name]["state"] in LIVE:
                st["sessions"][name]["state"] = "done"


ARCHIVE_AFTER = int(os.environ.get("ORCH_ARCHIVE_AFTER", 24 * 3600))


def archive():
    """Move what nothing refers to any more out of the state that every hook reads: sessions released a day ago whose
    task is done or gone, and questions answered a day ago; they are appended to state/v2-archive.jsonl."""
    now, out = time.time(), []
    with state() as st:
        referenced = set()
        for t in st["tasks"].values():
            if t.get("stage") != "done":
                referenced.update(t.get(k) for k in ("session", "reviewed_by", "reviewing", "briefing", "briefed_by", "fixing"))
        referenced.update((st["kb"], st.get("kb_building")))
        for name, s in list(st["sessions"].items()):
            if s.get("released") and name not in referenced and now - (s.get("ended") or s.get("started") or now) > ARCHIVE_AFTER:
                out.append({"session": s})
                del st["sessions"][name]
        for qid, q in list(st["asks"].items()):
            if q.get("state") == "answered" and now - (q.get("answered") or now) > ARCHIVE_AFTER:
                out.append({"ask": dict(q, qid=qid)})
                del st["asks"][qid]
        if out:
            with open(os.path.join(STATE, "v2-archive.jsonl"), "a") as f:
                f.write("".join(json.dumps(x) + "\n" for x in out))
    return len(out)


def finish(name, how="done"):
    """A session's piece of work has ended (its turn ends next; the watchdog seals it)."""
    with state() as st:
        if name in st["sessions"]:
            st["sessions"][name].update(state=how, ended=time.time())


FINISHING = ("checking", "reviewing", "fixing", "committing")
# A finalization held its files from its check through its review to its commit — minutes of checking, then a whole
# review — and an append to DECISIONS.md waited behind all of it (six refusals across two tasks, 2026-09-20). A
# review reads what was checked; it does not write, and nothing it reads changes if another task appends meanwhile.
# So the files are the finalization's while it checks, while a quick fix repairs them, and while it commits.
HOLDS_FILES = ("checking", "fixing", "committing")
COMMIT_WAIT = int(os.environ.get("ORCH_COMMIT_WAIT", 600))  # for another task's append to land before a commit
ISABELLE_MAX = int(os.environ.get("ORCH_ISABELLE_MAX", 2))  # concurrent Isabelle runs (three reached 59 of 60 GiB)
ADVANCES = re.compile(r"--advance-base\b|\badopt\b")  # a check that moves the base heap under every other run


def isabelle_runs():
    """The Isabelle processes (poly) running on this machine. ORCH_ISABELLE_RUNS states it instead where the machine's
    own processes are not the subject (the tests, which must not depend on what else the machine is doing)."""
    stated = os.environ.get("ORCH_ISABELLE_RUNS")
    if stated is not None:
        return int(stated)
    n = 0
    for pid in filter(str.isdigit, os.listdir("/proc")):
        with contextlib.suppress(OSError):
            n += open(f"/proc/{pid}/comm").read().strip() == "poly"
    return n


EXCLUSIVE = "isabelle-exclusive"
CLAIM_GRACE = float(os.environ.get("ORCH_CLAIM_GRACE", 180))  # to launch the run a session has claimed the machine for


def claim_exclusive(tid, why, pid=None, session=None):
    """Hold the machine for one task: its final check while it advances the base heap, or a session's run whose result
    is a timing, which a neighbour would distort as surely as it would exceed the memory."""
    json.dump({"task": tid, "why": why, "pid": pid, "session": session, "at": time.time()},
              open(os.path.join(STATE, EXCLUSIVE), "w"))


def exclusive_claim():
    """The claim on the machine, or None. A claim outlives neither the process nor the run that holds it: a check
    killed before its own cleanup left one behind and the next check waited an hour behind a holder that did not
    exist (2026-09-20), and a session's claim stands only while its run does, with CLAIM_GRACE to launch it."""
    path = os.path.join(STATE, EXCLUSIVE)
    try:
        claim = json.load(open(path))
    except (OSError, ValueError):
        claim = None
    if not isinstance(claim, dict):  # the forms before a claim said what holds it ("TASK" and "TASK PID")
        try:
            tid, _, pid = open(path).read().strip().partition(" ")
        except OSError:
            return None
        claim = {"task": tid, "why": "its final check advances the base heap",
                 "pid": pid if pid.isdigit() else None, "at": 0}
    alive = (claim.get("pid") and os.path.exists(f"/proc/{claim['pid']}")) or (
        claim.get("session") and (running_jobs(claim["session"]) or time.time() - claim.get("at", 0) < CLAIM_GRACE))
    if alive:
        return claim
    with contextlib.suppress(OSError):
        os.remove(path)
        log(f"cleared the machine's claim by task {claim.get('task')}: what held it is gone")
    return None


def exclusive_holder():
    claim = exclusive_claim()
    return claim["task"] if claim else None


def working(st):
    """The sessions doing work now, over every slot: producing, supporting, a quick fix, the planning episode and the
    consultations. The knowledge base is not one of them; a parked session is not working and does not count."""
    return [n for n, s in st["sessions"].items()
            if s.get("state") in LIVE and s.get("role") != "kb" and not s.get("released")]


def at_capacity(st):
    return len(working(st)) >= WORKERS_MAX


def slot(st, roles, fix=False):
    """The live session of a slot: the producing one, the supporting one, a quick fix, a planning episode, a
    consultation."""
    for s in st["sessions"].values():
        if s["role"] in roles and s["state"] in LIVE and bool(s.get("fix")) == fix:
            return s
    return None


# ---------------------------------------------------------------- the working tree
# The working tree has one owner at a time: the task whose finalization is in flight (its check, review, fix and
# commit), and otherwise the producing task. While a finalization is in flight every other session writes only under
# .build/ (the guard refuses the rest), so a check, a review's diff and a commit see that task's changes alone, and
# nothing is ever moved under a running session. The guard records which task wrote each path
# (state/tree-owners.json). A task that leaves unfinished (parked, back to the planner, lost, dropped, interrupted) has
# its installed work in the working tree, whole: a change here is a set of parts (a theory, the ROOT line declaring
# it, the import reaching it, its row, its entry) and a part taken out refuses every task's check, not only its own.
# While such work stands, the tree is that task's (tree_writer) and another session drafts under .build/tasks/ID/.

EXEMPT = (".build/", ".claude/", "HANDOFF.md")  # never an owned change: drafts, the harness's files, the planner's state


def exempt(path):
    return path.startswith(EXEMPT) or "__pycache__/" in path or path.endswith(".pyc")


def git_out(*args, binary=False, tree=None):
    r = subprocess.run(["git", "-C", tree or PROJECT, *args], capture_output=True, text=not binary)
    return r.stdout if r.returncode == 0 else None


def changed_paths(tree=None):
    """Every path of the working tree that differs from HEAD (modified, added, deleted, untracked), exempt ones left out."""
    out = git_out("status", "--porcelain=v1", "-z", "--untracked-files=all", tree=tree) or ""
    fields, paths, i = out.split("\0"), [], 0
    while i < len(fields):
        entry = fields[i]
        i += 1
        if len(entry) < 4:
            continue
        code, path = entry[:2], entry[3:]
        if code[0] in "RC":  # a rename is followed by its source
            paths.append(fields[i])
            i += 1
        paths.append(path)
    return sorted({p for p in paths if not exempt(p)})


@contextlib.contextmanager
def owners():
    """{path: task} of the changes in the working tree, read and written under a lock."""
    os.makedirs(STATE, exist_ok=True)
    path = os.path.join(STATE, "tree-owners.json")
    with open(path + ".lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            data = json.load(open(path))
        except (OSError, ValueError):
            data = {}
        yield data
        json.dump(data, open(path + ".tmp", "w"), indent=0)
        os.replace(path + ".tmp", path)


def own(task, paths):
    """The guard records that a task writes these paths (project-relative, exempt ones ignored)."""
    paths = [p for p in paths if p and not exempt(p)]
    if task and paths:
        with owners() as o:
            o.update({p: task for p in paths})


def unshelve(where):
    """Bring what `where` holds back into the working tree. Nothing makes a shelf since 2026-09-20 — the harness no
    longer takes a task's work out of the tree — so this serves a shelf made before that, by hand or by an older
    harness: as it was where nothing has changed the path since, merged
    (git merge-file) onto what has landed where something has. The paths that did not merge cleanly are returned; the
    shelved version of each stays beside it in `where`."""
    try:
        manifest = json.load(open(os.path.join(where, "manifest.json")))
    except (OSError, ValueError):
        return []
    read = lambda f: open(f, "rb").read() if os.path.lexists(f) else None
    conflicts = []
    for e in manifest:
        p, dst = e["path"], os.path.join(PROJECT, e["path"])
        base = read(os.path.join(where, "base", p)) if e["in_head"] else None
        mine = read(os.path.join(where, "files", p)) if e["exists"] else None
        current = read(dst)
        if current == base:  # untouched since: the shelved state comes back as it was
            if mine is None:
                with contextlib.suppress(OSError):
                    os.remove(dst)
            else:
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                open(dst, "wb").write(mine)
        elif mine is not None and base is not None and current is not None:
            r = subprocess.run(["git", "merge-file", "-p", dst, os.path.join(where, "base", p),
                                os.path.join(where, "files", p)], capture_output=True)
            open(dst, "wb").write(r.stdout)
            if r.returncode:
                conflicts.append(p)
        elif mine != current:
            conflicts.append(p)  # added, removed or rewritten on both sides: the working tree's version stays
    os.replace(os.path.join(where, "manifest.json"), os.path.join(where, "manifest.restored.json"))
    return conflicts


def tree_holder(st, rec=None):
    """The task whose finalization holds the working tree (checking, reviewing, fixing, committing), other than the
    session's own task; or None when the tree is free for the producing session."""
    own = {(rec or {}).get("task"), (rec or {}).get("reviews")}
    for tid, t in st["tasks"].items():
        if tid in own:
            continue
        if t.get("stage") == "checking" and os.path.exists(os.path.join(BUILD, tid, "finalize.json")):
            return tid  # its check is running and sees the working tree, which must hold its changes alone
        if t.get("stage") == "parked" and (t.get("parked") or {}).get("holds_tree"):
            return tid  # parked for its own run, which reads its changes in the working tree
    writer = tree_writer(st)  # its installed work stands in the tree until it commits: another task drafts meanwhile
    return writer if writer and writer not in own else None


def locked_files(st, rec):
    """{file: task} of the finalizations in flight that are not this session's own: their files are theirs until they
    are committed, while the rest of the working tree stays open (only a running check holds it whole)."""
    own = {rec.get("task"), rec.get("reviews")}
    out = {}
    for tid, t in st["tasks"].items():
        if t.get("stage") in HOLDS_FILES and tid not in own:
            try:
                for f in json.load(open(os.path.join(BUILD, tid, "finalize.json")))["files"]:
                    out[os.path.normpath(os.path.join(PROJECT, f))] = tid
            except (OSError, ValueError, KeyError):
                pass
    return out


def finalizing(st, rec=None):
    """The other task whose finalization is in flight (one runs at a time: a second task's check would see the first's
    uncommitted files), or None."""
    own = {(rec or {}).get("task"), (rec or {}).get("reviews")}
    return next((tid for tid, t in st["tasks"].items() if t.get("stage") in FINISHING and tid not in own
                 and os.path.exists(os.path.join(BUILD, tid, "finalize.json"))), None)


def check_isolation():
    """A check sees the working tree: while one runs, no other session writes it. A task whose session still works is
    parked — its work stays where it is — and resumed when the check's task has landed."""
    st = peek()
    checking = next((tid for tid, t in st["tasks"].items() if t.get("stage") == "checking"), None)
    if not checking:
        return
    with owners() as o:
        changed = {p: o.get(p) for p in changed_paths()}
    for tid, t in st["tasks"].items():
        if tid == checking or t.get("stage") not in ("running", "fixing") or tid not in changed.values():
            continue
        name = t.get("session")
        aside = leave(tid, f"task {checking}'s check")
        with state() as w:
            w["tasks"][tid].update(stage="parked", parked={"since": time.time(), "for": "tree", "why": "", "after": None,
                                                           "holds_tree": False, "questions": [], "holder": checking})
            if name in w["sessions"]:
                w["sessions"][name]["state"] = "parked"
        if name:
            deliver(name, "the harness", f"Task {checking}'s check is running and sees the working tree, so your changes "
                    f"left it and your task is parked.{aside} End your turn; you are resumed, your context intact, when "
                    "the check's task has landed and the producing slot is free.")
        log(f"parked {tid} while task {checking}'s check runs")


def mark_tree_wait(name, holder):
    """A session was refused the working tree while task holder holds it: it is told when the tree is free."""
    with state() as st:
        s = st["sessions"].get(name)
        if s:
            s.update(tree_wait=holder, tree_wait_since=s.get("tree_wait_since") or time.time())


def tree_care():
    """Tell every session that was refused the working tree, once it is free for it; and tell the producing session when
    a task's uncommitted changes, which its work may build on, have left the working tree."""
    st = peek()
    if st.get("withdrawn"):
        with state() as w:
            withdrawn, w["withdrawn"] = w.get("withdrawn", []), []
        for tid in withdrawn:
            for name, s in st["sessions"].items():
                if s["role"] in PRODUCING and s["state"] in LIVE and s.get("task") != tid:
                    deliver(name, "the harness", f"Task {tid} went back to the planner. Its uncommitted changes stay "
                            f"in the working tree, whole, until the planner says what becomes of them; the tree is "
                            "still its own, so draft under your own .build/tasks/ID/ and ask the planner "
                            "(`v2.py ask --to planner`) if your work builds on them.")
    for name, s in st["sessions"].items():
        if s.get("tree_wait") and s["state"] in LIVE and not tree_holder(st, s):
            held, tid = s["tree_wait"], s.get("task")
            with state() as w:
                w["sessions"][name].pop("tree_wait", None)
                w["sessions"][name].pop("tree_wait_since", None)
                back = (w["tasks"].get(tid) or {}).pop("take_up", False)
            deliver(name, "the harness", f"Task {held} has let the working tree go: it is yours. Install what "
                    f"you drafted under .build/tasks/{tid}/, make the edits you kept for now, and continue."
                    + (take_up(tid) if back else ""))


def leave(tid, why):
    """A task leaves the working tree unfinished (its session has stopped): its work stays in it, whole. Returns the
    text for the planner, or "". Never raises."""
    try:
        return _leave(tid, why)
    except Exception as e:  # noqa: BLE001  the orchestration must not stop over one task's files
        log(f"could not read what task {tid} leaves in the working tree: {e!r}")
        return f" What it leaves in the working tree could not be read ({e!r}); its changes are still there."


ACTIVE_CONTEXT = os.environ.get("ORCH_ACTIVE_CONTEXT", "/tmp/structural-active-context.json")


THEORY_LINE = re.compile(r"^\s{4}(\w+)\s*$", re.M)
IMPORTS = re.compile(r"\bimports\b(.*?)\bbegin\b", re.S)  # the header, one line or many
MARKERS = re.compile(r"^(?:<{7}|>{7}|={7})(?:\s|$)", re.M)


def _read(name, tree=None):
    try:
        return open(os.path.join(tree or PROJECT, name), errors="ignore").read()
    except OSError:
        return ""


def tree_trouble(tree=None):
    """What is wrong with the working tree as a whole, in the terms the checks refuse on. Each of these refuses every
    task's check and not only the one whose change caused it, so each is the orchestration's to notice rather than a
    task's to discover: a theory present and undeclared, a line declaring a theory that is not there, an import of a
    theory that is neither present nor in the history, and the markers of a merge that did not resolve."""
    out, tree = [], tree or PROJECT
    try:
        root = open(os.path.join(tree, "ROOT")).read()
        present = {f[:-4] for f in os.listdir(os.path.join(tree, "theories")) if f.endswith(".thy")}
    except OSError:
        return []  # no ROOT or no theories/: not a tree these terms are about, and nothing to say of it
    declared = THEORY_LINE.findall(root)
    listed = set(declared)
    for name in sorted({n for n in declared if declared.count(n) > 1}):
        out.append(f"ROOT declares {name} {declared.count(name)} times")
    headings = re.findall(r"^## (.+?)\s*$", _read("DECISIONS.md", tree), re.M)
    for head in sorted({h for h in headings if headings.count(h) > 1}):
        out.append(f"DECISIONS.md holds the entry \"{head}\" {headings.count(head)} times")
    rows = [r for r in re.findall(r"^\| ([A-Za-z_][\w]*) \|", _read("THEORY_MAP.md", tree), re.M) if r != "Theory"]
    for row in sorted({r for r in rows if rows.count(r) > 1}):
        out.append(f"THEORY_MAP.md holds the row of {row} {rows.count(row)} times")
    for name in sorted(present - listed):
        out.append(f"theories/{name}.thy is in the tree and no ROOT line declares it")
    for name in sorted(listed - present):
        out.append(f"ROOT declares {name}, which is not in theories/")
    known = present | {n[:-4] for n in (git_out("ls-tree", "--name-only", "HEAD", "theories/") or "").splitlines()
                       if n.endswith(".thy")}
    known = {n.rsplit("/", 1)[-1] for n in known}
    for name in sorted(present):
        try:
            text = open(os.path.join(tree, "theories", name + ".thy"), errors="ignore").read(4000)
        except OSError:
            continue
        m = IMPORTS.search(text)
        for imported in (m.group(1).split() if m else []):
            imported = imported.strip('"')
            if "." in imported or imported in known or imported == "Main":
                continue
            out.append(f"theories/{name}.thy imports {imported}, which is neither in the tree nor in the history")
    for path in changed_paths(tree):
        full = os.path.join(tree, path)
        if not os.path.isfile(full) or os.path.getsize(full) > 8_000_000:
            continue
        try:
            if MARKERS.search(open(full, errors="ignore").read()):
                out.append(f"{path} holds the markers of a merge that did not resolve")
        except OSError:
            continue
    return out


def tree_checked(who, what, tree=None):
    """Say at once when the tree has been left in a state every check refuses, naming what did it."""
    trouble = tree_trouble(tree)
    if trouble:
        log(f"ATTENTION the working tree is inconsistent after {what} ({who}): " + "; ".join(trouble[:4]))
        with state() as st:
            event(st, "the harness", f"The working tree is inconsistent after {what}: " + "; ".join(trouble)
                  + ". Every task's check refuses on this, not only the one whose change caused it, so nothing can "
                  "be checked until it is put right.")
    return trouble


def root_lines_back(where):
    """Put back the ROOT lines that went out with a task's theories, each after the line it followed."""
    mark = os.path.join(where, "root-lines.json")
    try:
        dropped = json.load(open(mark))
    except (OSError, ValueError):
        return []
    path = os.path.join(PROJECT, "ROOT")
    try:
        lines = open(path).read().splitlines(keepends=True)
    except OSError:
        return []
    back, lost = [], []
    for d in dropped:
        if any(l.strip() == d["name"] for l in lines):
            continue  # someone put it back already
        i = next((n for n, l in enumerate(lines) if l.strip() == d["after"]), None)
        if i is None:
            lost.append(d["name"])
            continue
        lines.insert(i + 1, d["line"])
        back.append(d["name"])
    open(path, "w").write("".join(lines))
    with contextlib.suppress(OSError):
        os.remove(mark)
    if back or lost:
        log(f"put {len(back)} line(s) back into ROOT" + (f"; {', '.join(lost)} found no place and must be listed by "
                                                         "hand" if lost else ""))
    return back


def _leave(tid, why):
    """What a task leaves in the working tree when it stops working — and it leaves all of it. Until 2026-09-20 the
    harness took a task's changes out and returned the files to HEAD, so that the next check saw one task's work
    alone. A change in this repository is not a set of files but a set of *parts* — a theory, the ROOT line that
    declares it, the import that reaches it, its row, its entry — and moving files moved parts: a theory went while
    its declaration stayed, a declaration went while its theory stayed, a boundary import stayed while the theory it
    named went. Each left a tree that every task's check refuses, not only the one that moved. Nothing is taken out
    now: while a task's installed work stands, the tree is that task's (tree_writer, tree_holder) and another session
    starts, drafts under its own .build/tasks/ID/ and installs when the tree is free; a task that cannot come back
    leaves its work for the planner to re-plan over, which is what it does with it anyway."""
    with owners() as o:
        mine = [p for p, t in o.items() if t == tid]
    paths = [p for p in changed_paths() if p in mine]
    if not paths:
        return ""
    log(f"task {tid} leaves {len(paths)} changed path(s) in the working tree ({why}): {', '.join(paths[:6])}"
        + (", …" if len(paths) > 6 else ""))
    return (f" Its uncommitted changes stay in the working tree ({len(paths)} paths: {', '.join(paths[:6])}"
            f"{', …' if len(paths) > 6 else ''}), whole: a check reads a tree, and a part of a change taken out of "
            "one refuses every task's check.")


def shelved_paths(tid):
    """The working-tree paths a task left set aside, as absolute paths."""
    try:
        manifest = json.load(open(os.path.join(BUILD, tid, "shelf", "manifest.json")))
    except (OSError, ValueError):
        return set()
    return {os.path.normpath(os.path.join(PROJECT, e["path"])) for e in manifest}


def take_up(tid, task=None):
    """Bring a task's set-aside changes back (for itself, or for the task continuing them); a text for its session.
    Only while no finalization is in flight. Never raises."""
    try:
        return _take_up(tid, task)
    except Exception as e:  # noqa: BLE001
        log(f"could not take up the changes of task {tid}: {e!r}")
        return f" The changes of task {tid} set aside could not be brought back ({e!r}): they are under .build/tasks/{tid}/shelf/."


def _take_up(tid, task=None):
    where = os.path.join(BUILD, tid, "shelf")
    if not os.path.exists(os.path.join(where, "manifest.json")):
        return ""
    paths = [e["path"] for e in json.load(open(os.path.join(where, "manifest.json")))]
    conflicts = unshelve(where)
    root_lines_back(where)
    own(task or tid, paths)
    return (f" The changes of task {tid} set aside are back in the working tree ({len(paths)} paths)"
            + (f"; these did not merge cleanly with what has landed since, and have conflict markers or keep the landed "
               f"version (the set-aside one is under .build/tasks/{tid}/shelf/files/): {', '.join(conflicts)}"
               if conflicts else "") + ".")


# ---------------------------------------------------------------- the task graph

def task_path(tid):
    return os.path.join(TASKS, LIST, f"{tid}.json")


@contextlib.contextmanager
def task_lock(tid):
    """Claude Code's own lock on a task file: proper-lockfile's directory `<file>.lock`, stale after 10 s (read from
    Claude Code 2.1.273's updateTask), so that the harness's writes and the sessions' TaskUpdate never interleave."""
    lock = task_path(tid) + ".lock"
    for _ in range(200):
        try:
            os.mkdir(lock)
            break
        except FileExistsError:
            with contextlib.suppress(OSError):
                if time.time() - os.stat(lock).st_mtime > 10:
                    os.rmdir(lock)
                    continue
            time.sleep(0.05)
        except FileNotFoundError:  # no task list
            yield False
            return
    else:
        raise TimeoutError(f"the lock of task {tid} is held")
    try:
        yield True
    finally:
        with contextlib.suppress(OSError):
            os.rmdir(lock)


def read_task(tid):
    for _ in range(3):  # a read can meet a write in progress
        try:
            return json.load(open(task_path(tid)))
        except ValueError:
            time.sleep(0.05)
        except OSError:
            return None
    return None


def update_task(tid, **fields):
    with task_lock(tid):
        t = read_task(tid)
        if not t:
            return
        t.update(fields)
        tmp = task_path(tid) + ".tmp"
        json.dump(t, open(tmp, "w"), indent=2)
        os.replace(tmp, task_path(tid))


def all_tasks():
    d = os.path.join(TASKS, LIST)
    names = sorted((f for f in os.listdir(d) if f.endswith(".json")), key=lambda n: (len(n), n)) if os.path.isdir(d) else []
    return [t for t in (read_task(f[:-5]) for f in names) if t]


def graph_text(full=False):
    """The graph as the planner and the task designer are shown it: every open task with its stage, dependencies,
    owner and why; the completed ones only counted (`v2.py graph --all` lists them too), so that the first message of
    an episode does not grow with the whole history."""
    st, lines, done = peek(), [], 0
    for t in all_tasks():
        if t.get("status") == "completed" and not full:
            done += 1
            continue
        meta = t.get("metadata") or {}
        kind = meta.get("kind") or field(t.get("description", ""), "Kind") or "?"
        after = ", ".join(t.get("blockedBy") or []) or "-"
        stage = (st["tasks"].get(t["id"]) or {}).get("stage")
        lines.append(f"- {t['id']} [{t.get('status')}{', ' + stage if stage else ''}] ({kind}) {t.get('subject', '')}; "
                     f"after {after}" + (f"; owner {t['owner']}" if t.get("owner") else "")
                     + (f"; why: {meta['why']}" if meta.get("why") else ""))
    if done:
        lines.append(f"- and {done} completed task{'s' if done > 1 else ''} (`v2.py graph --all` lists them)")
    return "\n".join(lines) or "(the task list is empty)"


def deps_done(tid):
    t = read_task(tid) or {}
    return all((read_task(d) or {}).get("status") == "completed" for d in t.get("blockedBy") or [])


# ---------------------------------------------------------------- forms

def head(name):
    """A field's line start: `Name:`, markup around the name allowed."""
    return rf"^[ \t]*[-*]?[ \t]*(?:\*\*)?{re.escape(name)}:(?:\*\*)?"


def field(text, name):
    """The text after `Name:` on its line, or ""."""
    m = re.search(head(name) + r"[ \t]*(.*)$", text, re.M | re.I)
    return m.group(1).strip() if m else ""


def section(text, name):
    """The whole text of a brief's field: from `Name:` to the next field of the form, lines below it included."""
    others = "|".join(head(f)[1:] for f in FORM_FIELDS if f != name)
    m = re.search(head(name) + rf"(.*?)(?=^(?:{others})|\Z)", text, re.M | re.S | re.I)
    return m.group(1).strip() if m else ""


def names_in(text):
    """The backticked names of a field (files, ranges stripped, and facts), in order."""
    out = []
    for n in re.findall(r"`([^`\s]+)`", text):
        n = re.sub(r":[\d,-]+$", "", n)
        if len(n) >= 3 and re.fullmatch(r"[\w./-]+", n) and n not in out:
            out.append(n)
    return out


def deliverables(text):
    return [p for p in names_in(section(text, "Deliverable")) if "/" in p or "." in p]


def inputs(text):
    return names_in(section(text, "Inputs"))


def size_of(text):
    """The brief's size estimate in tokens of work (`Size: about 150K ...`), or None."""
    m = re.search(r"(\d+(?:\.\d+)?)\s*([KkMm])\b", field(text, "Size") or section(text, "Size"))
    return int(float(m.group(1)) * (1_000_000 if m.group(2) in "Mm" else 1_000)) if m else None


def reviewed(text):
    """The task a review task reviews (its `Reviews:` line names it), or None."""
    m = re.search(r"`?([\w.-]+)`?", field(text, "Reviews"))
    return m.group(1) if m else None


def brief_problems(text):
    out = [f"the brief has no `{f}:` line" for f in BRIEF_FIELDS if not re.search(head(f), text, re.M | re.I)]
    kind = field(text, "Kind").split()[0].strip(".,").lower() if field(text, "Kind") else ""
    if kind and kind not in KINDS:
        out.append(f"Kind must be one of {', '.join(KINDS)}, not {kind}")
    if len(re.findall(r"^\s*\d+[.)]\s", section(text, "Plan"), re.M)) < 2:
        out.append("the plan must be the task's logical course: at least two numbered steps")
    if kind not in ("brief", "review"):
        files = deliverables(text)
        if not files:
            out.append("the Deliverable names no file in backticks")
        for p in files:
            if os.path.isdir(os.path.join(PROJECT, p)):
                out.append(f"the Deliverable names the directory `{p}`: name its files, which are what counts as production")
    if kind == "review" and not reviewed(text):
        out.append("a review task names the task it reviews on its `Reviews:` line")
    size, room = size_of(text), room_of(kind if kind in KINDS else "build")
    if re.search(head("Size"), text, re.M | re.I) and size is None:
        out.append("the Size is an estimate in tokens of work (for example `Size: about 150K`)")
    elif size and size > room:
        out.append(f"the Size ({size // 1000}K) is beyond what a {kind or 'build'} session has room for "
                   f"({room // 1000}K): split the task")
    return out


def room_of(kind):
    """The work a session of this kind has room for: what its base leaves before the notice, less its first message and
    gather."""
    who = ROLES[PRODUCER.get(kind) or {"brief": "task-designer", "review": "reviewer"}[kind]]["origin"]
    try:
        who = base_record(who)[0] or "max"
        context = json.load(open(os.path.join(STATE, f"{who}-base.json")))["context"]
    except (OSError, ValueError, KeyError, TypeError):
        context = 560_000  # the present base, measured 2026-09-19
    return max(0, SOFT - context - PROTOCOL_ROOM)


def brief_kind(text):
    k = field(text, "Kind")
    return k.split()[0].strip(".,").lower() if k else "build"


def result_problems(text):
    status = field(text, "Status").split()[0].strip(".,").lower() if field(text, "Status") else ""
    out = [] if status in ("done", "partial", "blocked") else ["the `Status:` line must say done, partial or blocked"]
    for s in RESULT_SECTIONS:
        if not re.search(rf"^\s*(?:#+\s*|[-*]\s*)?(?:\*\*)?{re.escape(s)}\b", text, re.M | re.I):
            out.append(f"the result has no `{s}` part")
    return out


def part(text, name):
    """The text of a `## Name` part of a document, up to the next part."""
    m = re.search(rf"^#+\s*{re.escape(name)}\b[^\n]*\n(.*?)(?=^#+\s|\Z)", text, re.M | re.S | re.I)
    return m.group(1).strip() if m else ""


def verdict_problems(text, verdict):
    out = [] if part(text, "Summary") else ["the verdict has no `## Summary` part (about 150 words, for the planner)"]
    if verdict == "reject" and not part(text, "Findings"):
        out.append("a rejection lists its blocking findings under `## Findings`")
    return out


def planner_state_problems(text):
    heads = {m.strip().lower() for m in re.findall(r"^##\s+(.+?)\s*$", text, re.M)}
    return [f"HANDOFF.md has no `## {s}` section" for s in PLANNER_SECTIONS if s.lower() not in heads]


# ---------------------------------------------------------------- what a session produces

def deliverables_of(rec):
    """{"deliverables": [...], "drafts": dir or "", "task_tools": bool}: what counts as a session's production."""
    role, tid = rec.get("role"), rec.get("task")
    if role in PRODUCING:
        try:
            b = json.load(open(os.path.join(BUILD, tid, "brief.json")))
        except (OSError, ValueError, TypeError):
            b = {"deliverables": []}
        return {"deliverables": b.get("deliverables", []), "drafts": f".build/tasks/{tid}/", "task_tools": False}
    if role == "task-designer":
        return {"deliverables": [], "drafts": f".build/tasks/{tid}/brief/", "task_tools": True}
    if role == "reviewer":
        return {"deliverables": [f".build/tasks/{tid}/review.md"], "drafts": "", "task_tools": False}
    if role == "planner":
        return {"deliverables": ["HANDOFF.md"], "drafts": f".build/plans/{rec.get('name')}/", "task_tools": True}
    if role == "consultant":
        return {"deliverables": [], "drafts": f".build/asks/{rec.get('qid')}/", "task_tools": False}
    return {"deliverables": [], "drafts": "", "task_tools": False}


def statements_only(rec):
    """Whether a session reads statements only: the planner, the task designer, the knowledge base, and a
    consultation of the knowledge base or of a planning episode."""
    if rec.get("role") == "consultant":
        return ROLES[(peek()["sessions"].get(rec.get("origin")) or {}).get("role", "kb")]["statements"] is not False
    return bool(ROLES.get(rec.get("role"), {}).get("statements"))


# ---------------------------------------------------------------- protocols

def render(role, **values):
    """A role's first message: protocols/<role>.md with its shared parts ({{part}} is protocols/_part.md) and values."""
    text = open(os.path.join(PROTOCOLS, f"{role}.md")).read()
    for _ in range(2):
        text = re.sub(r"\{\{([\w-]+)\}\}", lambda m: open(os.path.join(PROTOCOLS, f"_{m.group(1)}.md")).read().strip(), text)
    values = dict(ROUNDS=str(ROUNDS), READ=str(READ_TOKENS // 1000), CIRCLING=str(CIRCLING), FIX_MINUTES=str(FIX_MINUTES),
                  BRIEF_BACKLOG=str(BRIEF_BACKLOG),
                  FIX_ROUNDS=str(FIX_ROUNDS), HOLD_HOURS=str(HOLD_PARK // 3600), ROOM_DESIGN=str(room_of("design") // 1000),
                  ROOM_TASK=str(room_of("build") // 1000), **values)
    missing = [k for k in dict.fromkeys(re.findall(r"\{([A-Z][A-Z_]{2,})\}", text)) if k not in values]
    for k, v in values.items():
        text = text.replace("{" + k + "}", v)
    for left in missing:
        log(f"ATTENTION the {role} protocol has no value for {{{left}}}: it is left out of the message")
        text = text.replace("{" + left + "}", "")
    return text.strip()


def owner_words():
    """Collect the owner's words given since the curated ones, for the knowledge base to hold."""
    err = os.path.join(STATE, "owner-directions-new.err")
    ok = subprocess.run([os.path.join(HERE, "extract_owner_directions.py"), "--new"], stdout=subprocess.DEVNULL,
                        stderr=open(err, "w")).returncode == 0
    if not ok:
        open(os.path.join(STATE, "owner-directions-new.md"), "w").write(
            "# Owner directions given since the curated ones\n\nThey could not be collected for this start. Read the "
            "owner ledger, and ask the owner whether anything was said since.\n")


def handoff_parts():
    """HANDOFF.md's `## Now` and `## Open` as they are: what the last episode left unhandled and the open questions."""
    path = os.path.join(PROJECT, "HANDOFF.md")
    text = open(path, errors="ignore").read() if os.path.exists(path) else ""
    return "\n\n".join(f"### {p}\n{part(text, p) or '(empty)'}" for p in ("Now", "Open"))


def first_episode():
    """The first episode's part of its first message (protocols/_first.md), while there is no task graph and no episode
    has ended; "" afterwards."""
    if peek().get("plan_ended") or all_tasks():
        return ""
    with owners() as o:
        unowned = [p for p in changed_paths() if p not in o]
    listed = ", ".join(f"`{p}`" for p in unowned[:40]) + (f", and {len(unowned) - 40} more" if len(unowned) > 40 else "")
    return open(os.path.join(PROTOCOLS, "_first.md")).read().strip().replace("{UNOWNED}", listed or "none")


def events_text(events):
    return "\n\n".join(f"- {e['at']}, from {e['from']}: {e['text']}" for e in events) or "(none)"


def status_text():
    return cmd_status()


# ---------------------------------------------------------------- the knowledge base

def notes_path(kb):
    return os.path.join(STATE, f"{kb}-notes.md")


def kb_build():
    """A new knowledge base, forked from the planner's base: it reads what it is to hold and is sealed when it has."""
    if not base_record("max")[1]:
        log("no knowledge base started: there is no sealed base (base.sh max build, then seal)")
        return None
    owner_words()
    previous = peek()["kb"]
    with state() as st:
        n = count(st, "kb")
    key = str(n)

    def prompt(name):
        # HANDOFF.md holds what outlasts a knowledge base; the notes told only its predecessor what changed
        return render("kb", NAME=name, STALE=stale(base_record("max")[0] or "max"))
    name = launch("kb", key, prompt, kb_state="building", previous=previous)
    if name:
        with state() as st:
            st["kb_building"] = name
    return name


def kb_care():
    """Build the knowledge base when there is none (or it has grown too large, or gone cold), seal it when a load or
    an integration has ended, and integrate pending notes while it is sealed."""
    st = peek()
    kb, building = st["kb"], st.get("kb_building")
    if building:
        s = st["sessions"].get(building) or {}
        if s.get("state") == "lost":
            with state() as w:
                w["kb_building"] = None
            return
        if s.get("sid") and integrated(s, s.get("started", 0)):
            seal(building)
            ctx = context_of(s["sid"])
            with state() as w:
                w["sessions"][building].update(state="done", kb_state="sealed", context=ctx, built_context=ctx,
                                               base_sid=(base_record("max")[1] or {}).get("sid"))
                w["kb"], w["kb_building"] = building, None
                if ctx > KB_MAX - KB_MARGIN:
                    event(w, "the harness", f"The knowledge base {building} loads at {ctx // 1000}K, near its limit of "
                          f"{KB_MAX // 1000}K (its forks need their room): condense HANDOFF.md (settled decisions to "
                          "where they are written, with references; what was delivered, at the level later work needs), "
                          "so that the next knowledge base loads less. A base rebuild, which is the owner's, takes in "
                          "what the documents hold.")
            if kb and kb != building:
                release(kb)
            log(f"{building} holds the knowledge ({ctx} tokens)" + (" — near its limit: a base rebuild is due (the owner's)"
                                                                     if ctx > KB_MAX - KB_MARGIN else ""))
        return
    rec = st["sessions"].get(kb or "") or {}
    ctx, built = rec.get("context") or 0, rec.get("built_context") or 0
    # a successor is built while the present one still serves: once it has grown within KB_MARGIN of its limit (a fresh
    # one that loads that large is not rebuilt again), or when the owner has rebuilt the base it was forked from
    grown = ctx > KB_MAX - KB_MARGIN and ctx > built + KB_MARGIN
    rebased = rec.get("base_sid") and rec["base_sid"] != (base_record("max")[1] or {}).get("sid")
    if not kb or rec.get("state") == "lost" or (rec.get("kb_state") == "sealed" and not warm(kb)) or grown or rebased:
        kb_build()
        return
    if rec.get("kb_state") == "integrating":
        if integrated(rec, rec.get("integrating_since", 0)):
            seal(kb)
            ctx = context_of(rec["sid"])
            with state() as w:
                w["sessions"][kb].update(kb_state="sealed", context=ctx, state="done")
            log(f"{kb} integrated ({ctx} tokens)")
        return
    if st["notes"] and rec.get("kb_state") == "sealed":
        with state() as w:
            notes, w["notes"] = w["notes"], []
        with open(notes_path(kb), "a") as f:
            f.write("\n\n".join(notes) + "\n\n")
        text = ("Integrate these notes into what you hold, then reply INTEGRATED and end your turn; do nothing else.\n\n"
                + "\n\n".join(notes))
        with state() as w:
            w["sessions"][kb].update(kb_state="integrating", integrating_since=time.time())
        if not resume(kb, text):
            with state() as w:
                w["sessions"][kb]["kb_state"] = "sealed"
                w["notes"] = notes + w["notes"]


def integrated(rec, since):
    """Whether the knowledge base has replied INTEGRATED after a moment: its load or its integration has ended."""
    import watchdog
    _, text, at = watchdog.last_reply(rec["sid"])
    return at > since and "INTEGRATED" in text


def kb_context():
    st = peek()
    return (st["sessions"].get(st["kb"] or "") or {}).get("context") or 0


def kb_ready():
    """The knowledge base can be forked: sealed and warm, and not past its limit while its successor is being built
    (a fork of it would have less than its room)."""
    st = peek()
    rec = st["sessions"].get(st["kb"] or "") or {}
    past = (rec.get("context") or 0) > KB_MAX and st.get("kb_building")
    return rec.get("kb_state") == "sealed" and warm(st["kb"]) and not past


def context_of(sid):
    import ctx_gauge
    return ctx_gauge.context_tokens(f"{TRANSCRIPTS}/{sid}.jsonl")


# ---------------------------------------------------------------- dispatch

def task_state(st, tid):
    """A queued task's stage, read from its task when the harness has not taken it up: done when the graph says it is
    completed, ready when its description is a brief in form (dispatched by its kind), unformed otherwise, which the
    planner is told once."""
    t = st["tasks"].setdefault(tid, {})
    if t.get("stage") in (None, "unformed", "ready"):
        task = read_task(tid)
        if task and task.get("status") == "completed":
            t["stage"] = "done"
        elif task and t.get("stage") != "ready":
            problems = brief_problems(task.get("description", ""))
            if not problems:
                t["stage"], t["kind"] = "ready", brief_kind(task["description"])
            elif t.get("stage") != "unformed":
                t["stage"] = "unformed"
                event(st, "the harness", f"Task {tid} is queued but its brief is not in form, so nothing takes it up:\n- "
                      + "\n- ".join(problems))
    return t


PLANNED_FIX = ("Nothing failed: this task is a fix the planner planned, not a repair of a check or a review. What it "
               "must put right is its brief below.")


def start_producer(tid):
    task = read_task(tid)
    brief = task["description"]
    kind = brief_kind(brief)
    role = PRODUCER[kind]
    os.makedirs(os.path.join(BUILD, tid), exist_ok=True)
    json.dump({"task": tid, "deliverables": deliverables(brief), "drafts": f".build/tasks/{tid}/", "inputs": inputs(brief)},
              open(os.path.join(BUILD, tid, "brief.json"), "w"))
    base = base_record(ROLES[role]["origin"])[0] or "max"
    name = launch(role, tid, lambda name: render(role, NAME=name, ID=tid, KIND=kind, SUBJECT=task.get("subject", ""),
                                                 BRIEF=brief.strip(), STALE=stale(base), WHAT=PLANNED_FIX), task=tid)
    with state() as st:
        t = task_state(st, tid)
        if name:
            t.update(stage="running", session=name, role=role)
            st.pop("start_failed", None)
        else:
            first = (st.get("start_failed") or {}).get("task") != tid
            st["start_failed"] = {"task": tid, "at": time.time()}
            if first:
                event(st, "the harness", f"The start of the {role} on task {tid} was not confirmed; it is tried again "
                      f"every {RETRY // 60} minutes.")
    if name:
        update_task(tid, status="in_progress", owner=name)
    return name


def parked_ready(st, tid, p):
    """Whether what a parked task waits for has come: its fix landed, its run ended, the working tree free, its question
    answered."""
    kind = p.get("for", "fix")
    if kind == "fix":
        return bool(p.get("after")) and (p["after"] == "none" or (read_task(p["after"]) or {}).get("status") == "completed")
    if kind == "run":
        return not p.get("holds_tree")
    if kind == "tree":
        if tree_holder(st, {"task": tid}):
            return False  # a check is running and sees the working tree
        other = finalizing(st, {"task": tid})
        if not other:
            return True
        mine = shelved_paths(tid)  # its own files are back only where the finalization in flight holds none of them
        return not (mine & set(locked_files(st, {"task": tid})))
    if kind == "answer":
        return all((st["asks"].get(q) or {}).get("state") == "answered" for q in p.get("questions", []))
    return False


PARKED_TEXT = {"fix": "The fix of the performance problem you parked for has landed (task {after}). Continue task {tid}.",
               "run": "The run you parked for has ended; its completion is in your context. Continue task {tid}.",
               "tree": "The working tree is yours: install what you drafted and continue task {tid}.",
               "answer": "The answer you parked for is in the mail below. Continue task {tid}."}


def parking_care():
    """A task parked for its own run keeps the working tree while the run reads it; when the run has ended the tree is
    free for the producing session, and its work stays in it until it commits."""
    st = peek()
    for tid, t in st["tasks"].items():
        p = t.get("parked") or {}
        if t.get("stage") == "parked" and p.get("holds_tree") and not running_jobs(t.get("session") or ""):
            aside = leave(tid, "its run has ended")
            with state() as w:
                w["tasks"][tid]["parked"]["holds_tree"] = False
            log(f"the run task {tid} parked for has ended" + (f";{aside}" if aside else ""))


TREES = os.environ.get("ORCH_TREES", "1") == "1"  # a worktree per producing task (ORCH_TREES=0 for the one tree)
TREE_DIR = ".build/trees"


def in_main_tree(tid):
    """Whether this task's work already stands in the one tree. Such a task keeps working there: a tree of its own
    would be a checkout of HEAD without what it has installed, and carrying the work over would be the harness moving
    a change again. A task that starts fresh gets its own tree."""
    with owners() as o:
        mine = {p for p, t in o.items() if t == str(tid)}
    return bool(mine & set(changed_paths()))


def worktree(tid):
    """The working tree of a task, made if it is not there: a git worktree on the branch task/<tid>, from HEAD.
    Measured on 2026-09-20: a check inside one reused all 1,797 theories of the base in 172.88 s, so the heaps are
    bound to their session names and not to a path, and two tasks can hold their own trees. What that buys is the
    merge: a ROOT line, a DECISIONS entry and a THEORY_MAP row are lines, and git merges lines — which is the
    granularity every failure of that day lacked."""
    path = os.path.join(PROJECT, TREE_DIR, tid)
    if os.path.isdir(os.path.join(path, ".git")) or os.path.isfile(os.path.join(path, ".git")):
        return path
    os.makedirs(os.path.join(PROJECT, TREE_DIR), exist_ok=True)
    r = subprocess.run(["git", "-C", PROJECT, "worktree", "add", "-B", f"task/{tid}", path, "HEAD"],
                       capture_output=True, text=True)
    if r.returncode:
        log(f"could not make a working tree for task {tid}: {(r.stdout + r.stderr).strip()[-200:]}")
        return None
    common = (git_out("rev-parse", "--git-common-dir") or ".git").strip()  # relative to the project, as git prints it
    exclude = os.path.join(common if os.path.isabs(common) else os.path.join(PROJECT, common), "info", "exclude")
    os.makedirs(os.path.dirname(exclude), exist_ok=True)  # `.build/` in .gitignore matches a directory, and the link
    if ".build" not in (open(exclude).read() if os.path.exists(exclude) else ""):  # below is a file: it would be
        with open(exclude, "a") as f:                                              # committed, and merging it would
            f.write("\n# the one .build, linked into every task's tree\n.build\n")  # replace the real directory
    link = os.path.join(path, ".build")
    if not os.path.exists(link):
        os.symlink(os.path.join(PROJECT, ".build"), link)  # one .build: drafts, check outputs and their lineage
    log(f"task {tid} has its own working tree at {TREE_DIR}/{tid} (branch task/{tid})")
    return path


def worktree_of(tid):
    """The task's own working tree if it has one, else the one tree."""
    path = os.path.join(PROJECT, TREE_DIR, str(tid))
    return path if os.path.exists(path) else PROJECT


def tree_of(rec):
    """The working tree of the session this record is of: its task's, or the one tree."""
    return worktree_of((rec or {}).get("task")) if (rec or {}).get("task") else PROJECT


def worktree_gone(tid):
    """Take a task's working tree away once its work has landed; its branch goes with it."""
    path = os.path.join(PROJECT, TREE_DIR, str(tid))
    if not os.path.exists(path):
        return
    subprocess.run(["git", "-C", PROJECT, "worktree", "remove", "--force", path], capture_output=True, text=True)
    subprocess.run(["git", "-C", PROJECT, "branch", "-D", f"task/{tid}"], capture_output=True, text=True)
    log(f"the working tree of task {tid} is taken away")


def trees_standing():
    """The task trees that are still there, and what stands in each. A tree is taken away when its work has landed
    (committed and merged); one whose task was dropped or lost keeps its work — that is where the planner re-plans
    from — so it is named rather than removed, and an empty one is taken away at once."""
    root = os.path.join(PROJECT, TREE_DIR)
    out = []
    for tid in sorted(os.listdir(root)) if os.path.isdir(root) else []:
        tree = os.path.join(root, tid)
        changed = [p for p in (git_out("status", "--porcelain", tree=tree) or "").splitlines() if p.strip()]
        ahead = len([l for l in (git_out("log", "--format=%h", f"main..task/{tid}") or "").splitlines() if l])
        out.append({"task": tid, "changed": len(changed), "commits": ahead})
    return out


def trees_tidied():
    """Take away every tree that holds nothing: no uncommitted change and no commit of its own."""
    gone = []
    for x in trees_standing():
        if not x["changed"] and not x["commits"] and (peek()["tasks"].get(x["task"]) or {}).get("stage") != "running":
            worktree_gone(x["task"])
            gone.append(x["task"])
    return gone


def merged(tid):
    """Bring a task's branch into the one that is pushed. Its lines meet the lines that landed meanwhile, and git
    says which did not meet: a conflict is reported, never resolved behind the tasks."""
    r = subprocess.run(["git", "-C", PROJECT, "merge", "--no-ff", "-m", f"Take up the work of task {tid}",
                        f"task/{tid}"], capture_output=True, text=True)
    if r.returncode == 0:
        return None
    conflicts = [l.split("\t")[-1] for l in (subprocess.run(
        ["git", "-C", PROJECT, "diff", "--name-only", "--diff-filter=U"], capture_output=True,
        text=True).stdout or "").splitlines()]
    subprocess.run(["git", "-C", PROJECT, "merge", "--abort"], capture_output=True, text=True)
    log(f"the work of task {tid} does not merge: {', '.join(conflicts) or (r.stdout + r.stderr).strip()[-300:]}")
    return conflicts or ["(the merge failed without naming a file)"]


def tree_writer(st):
    """The unfinished task whose installed work stands in the working tree, or None. Since the harness no longer takes
    a task's work out (leave), the tree holds one task's uncommitted change at a time: a second would stand beside it
    and no check could say whose failure it was. Designs, briefs, reviews and consultations do not write the tree and
    are not bound by this."""
    with owners() as o:
        owned = {p: tid for p, tid in o.items() if p in set(changed_paths())}
    for tid in owned.values():
        if (st["tasks"].get(tid) or {}).get("stage") not in ("done", None) and (read_task(tid) or {}).get(
                "status") != "completed":
            return tid
    return None


def produce():
    """The producing slot: a parked task whose wait is over first (its changes come back into the free working tree),
    then the first ready task in the queue."""
    st = peek()
    if slot(st, PRODUCING):
        return
    if at_capacity(st):
        return  # one session works at a time (WORKERS_MAX)
    for tid, t in sorted(st["tasks"].items(), key=lambda kv: (kv[1].get("parked") or {}).get("since", 0)):
        p = t.get("parked") or {}
        if t.get("stage") == "parked" and parked_ready(st, tid, p):  # before any new task, the longest parked first
            text = (PARKED_TEXT.get(p.get("for", "fix"), PARKED_TEXT["fix"]).format(after=p.get("after"), tid=tid)
                    if p.get("after") != "none" else f"Continue task {tid} as it is; the planner's answer is in the mail.")
            holder = tree_holder(st, {"task": tid})
            with state() as w:
                w["tasks"][tid]["stage"] = "running"
                w["tasks"][tid].pop("parked", None)
                if holder and os.path.exists(os.path.join(BUILD, tid, "shelf", "manifest.json")):
                    w["tasks"][tid]["take_up"] = True  # its changes come back when the tree is free (tree_care)
            if holder:
                text += (f" Task {holder} holds the working tree now: draft under .build/tasks/{tid}/ meanwhile; you are "
                         "told when it is yours" + (", and your set-aside changes come back then." if os.path.exists(
                             os.path.join(BUILD, tid, "shelf", "manifest.json")) else "."))
                mark_tree_wait(t["session"], holder)
            else:
                text += take_up(tid)  # a shelf from before 2026-09-20, if one is still there; otherwise nothing
            if not resume(t["session"], text + ("\n\n" + take_mail(t["session"]) if has_mail(t["session"]) else "")):
                with state() as w:
                    w["tasks"][tid]["stage"] = "planner"
                    event(w, "the harness", f"{t['session']}, parked on task {tid}, went cold before its wait was over: "
                          "re-plan the task over what is on disk." + leave(tid, "cold"))
            return
    failed = st.get("start_failed") or {}
    for tid in st["queue"]:
        with state() as w:
            t = dict(task_state(w, tid))
        if t.get("stage") != "ready" or t.get("kind") not in PRODUCING_KINDS or not deps_done(tid):
            continue

        if failed.get("task") == tid and time.time() - failed["at"] < RETRY:
            return
        start_producer(tid)
        return


def start_review(rid, tid):
    """The review task rid of the finished task tid (rid is tid itself when no review task was briefed: a review
    planned by the harness from the task's brief). The one who judged it before is resumed while warm for a re-review;
    otherwise a new reviewer forks the middle base."""
    st = peek()
    t, r = st["tasks"][tid], st["tasks"].get(rid) or {}
    task, review = read_task(tid) or {}, read_task(rid) or {}
    before = r.get("reviewed_by")
    if before and r.get("verdict") == "reject":
        text = (f"The findings you listed on task {tid} are fixed and its check passes again. Judge those findings and "
                "whatever the fix itself broke; add nothing else. Write the verdict again and record it "
                f"(`v2.py verdict {rid} accept|reject --file .build/tasks/{rid}/review.md`).")
        if resume(before, text):
            return before
    own = rid != tid
    name = launch("reviewer", rid, lambda name: render(
        "reviewer", NAME=name, ID=rid, TASK=tid, SUBJECT=task.get("subject", ""),
        REVIEW=(review.get("description") or "").strip() if own else "(no review task was briefed: judge the task "
        "against its brief, step by step, then against the principles)",
        BRIEF=(task.get("description") or "").strip(), SESSION=t.get("session", "-"),
        STALE=stale(base_record("xhigh")[0] or "max"),
        BEFORE=f"A previous review rejected it; its findings are in .build/tasks/{rid}/review.md. Judge those findings "
               "and whatever the fix broke; add nothing else." if r.get("verdict") == "reject" else ""),
        task=rid, reviews=tid)
    if name:
        with state() as w:
            w["tasks"].setdefault(rid, {}).update(reviewed_by=name, reviewing=name)
            w["tasks"][tid]["reviewed_by"] = name
    return name


def start_brief(tid):
    """A task designer on a brief task: the planner's plan of the detailing is its brief."""
    task = read_task(tid) or {}
    name = launch("task-designer", tid, lambda name: render(
        "task-designer", NAME=name, ID=tid, SUBJECT=task.get("subject", ""), BRIEF=(task.get("description") or "").strip(),
        WHY=(task.get("metadata") or {}).get("why", "-"), GRAPH=graph_text(), LIST=LIST,
        STALE=stale(base_record("xhigh")[0] or "max")), task=tid)
    with state() as w:
        if name:
            w["tasks"][tid].update(stage="running", session=name, role="task-designer")
    if name:
        update_task(tid, status="in_progress", owner=name)
    return name


def pending_reviews(st):
    """(review task, reviewed task) pairs to start: every review task of a finished task in review that has no verdict
    this round (or rejected it last round), and a review planned by the harness for a build or fix nobody briefed one for."""
    out = []
    for tid, t in st["tasks"].items():
        if t.get("stage") != "reviewing" or t.get("kind", "build") not in ("build", "fix"):
            continue
        rids = t.get("review_tasks") or []
        if not rids:
            if not t.get("reviewing"):
                out.append((tid, tid))
            continue
        for rid in rids:
            r = st["tasks"].get(rid) or {}
            if r.get("verdict") in (None, "reject") and not r.get("reviewing") and r.get("round") != t.get("rejections", 0):
                out.append((rid, tid))
    return out


def age_of(name):
    """Seconds since a marker under STATE was written, or None."""
    try:
        return time.time() - os.path.getmtime(os.path.join(STATE, name))
    except OSError:
        return None


def build_backlog(st=None):
    """The build and fix tasks that are not completed: what the one producing slot has still to do."""
    return [x["id"] for x in all_tasks() if x.get("status") != "completed"
            and ((x.get("metadata") or {}).get("kind") or field(x.get("description", ""), "Kind")) in ("build", "fix")]


def support():
    """The one supporting slot: a review task of a finished build or fix, or a brief task; the brief first when nothing
    is ready for the producing slot."""
    st = peek()
    if slot(st, SUPPORTING):
        return
    if at_capacity(st):
        return  # one session works at a time (WORKERS_MAX)
    reviews = pending_reviews(st)
    briefs, ready = [], False
    for tid in st["queue"]:
        with state() as w:
            t = dict(task_state(w, tid))
        if t.get("stage") == "ready" and t.get("kind") == "brief" and deps_done(tid):
            briefs.append(tid)
        ready = ready or (t.get("stage") == "ready" and t.get("kind") in PRODUCING_KINDS and deps_done(tid))
    backlog = build_backlog()
    if briefs and len(backlog) >= BRIEF_BACKLOG:
        if age_of(f"brief-held") is None or age_of("brief-held") > 900:
            open(os.path.join(STATE, "brief-held"), "w").write(str(time.time()))
            log(f"no brief is detailed while {len(backlog)} build and fix tasks are open (at most {BRIEF_BACKLOG}): "
                f"{', '.join(briefs)} wait for the builders")
        briefs = []
    if briefs and (not ready or not reviews):
        start_brief(briefs[0])
    elif reviews:
        rid, tid = reviews[0]
        name = start_review(rid, tid)
        if name:
            with state() as w:
                w["tasks"][rid].update(reviewing=name, round=w["tasks"][tid].get("rejections", 0))
                w["tasks"][tid]["reviewing"] = name


def quick_fix():
    """The quick-fix slot: a task whose check failed or whose review rejected it, once: its own session resumed while
    warm, a fixer otherwise."""
    st = peek()
    if slot(st, PRODUCING, fix=True):
        return
    for tid, t in st["tasks"].items():
        if t.get("stage") != "fixing" or t.get("fixing"):
            continue
        what = t.get("fix_text", "")
        text = (f"{what}\nFix it as a quick fix: at most {FIX_MINUTES} minutes and {FIX_ROUNDS} rounds. Then hand over "
                f"the final job again (`v2.py finalize {tid} ...`) and record your result again (`v2.py result {tid}`).")
        own = t.get("session")
        with state() as w:
            if own in w["sessions"]:
                w["sessions"][own]["fix"] = {"since": time.time()}
        if own and resume(own, text):
            name = own
        else:
            with state() as w:
                if own in w["sessions"]:
                    w["sessions"][own].pop("fix", None)
            task = read_task(tid) or {}
            name = launch("fixer", tid, lambda name: render(
                "fixer", NAME=name, ID=tid, BRIEF=(task.get("description") or "").strip(), WHAT=text,
                STALE=stale(base_record("high")[0] or "max")), task=tid, fix={"since": time.time()})
        with state() as w:
            w["tasks"][tid]["fixing"] = name
            if name:
                w["tasks"][tid]["session"] = name
            else:
                to_planner(w, tid, "the harness", f"No quick fix could start on task {tid}: {what[:300]}")
        return


def consulted_base(origin):
    """The base a consulted session's fork inherits, for what changed since it was loaded."""
    who = (peek()["sessions"].get(origin) or {}).get("origin")
    return base_record(who if who in BASES else "max")[0] or "max"


def consult():
    """The consultations: every queued question, oldest first, up to CONSULT_MAX at once, each answered by a fork of the
    consulted session while it is warm, by a fork of the knowledge base otherwise. A question whose origin cannot be
    forked now (the knowledge base integrating) waits without holding up the others."""
    st = peek()
    if at_capacity(st):
        return  # one session works at a time (WORKERS_MAX); a question waits for the gap
    live = sum(1 for s in st["sessions"].values() if s["role"] == "consultant" and s["state"] in LIVE)
    for qid, q in sorted(st["asks"].items(), key=lambda kv: kv[1]["asked"]):
        if live >= CONSULT_MAX:
            return
        if q["state"] != "queued":
            continue
        target, note = q["target"], ""
        if target != "kb" and not warm(target):
            note = (f"The question was for {target}, whose cache has expired; answer from what you hold and from its "
                    f"written work ({q.get('artifacts') or 'its task directory under .build/tasks/'}).")
            target = "kb"
        if target == "kb" and not kb_ready():
            continue
        origin = peek()["kb"] if target == "kb" else target
        name = launch("consultant", qid, lambda name: render(
            "consultant", NAME=name, ID=qid, QID=qid, ASKER=q["from"], TARGET=origin, QUESTION=q["text"], NOTE=note,
            STALE=stale(consulted_base(origin))),
            origin=origin, qid=qid)
        with state() as w:
            w["asks"][qid].update(state="open", session=name) if name else None
        live += bool(name)


def plan():
    """A planning episode, a fork of the knowledge base on the events gathered since the last one; urgent (no gap)
    when nothing can be produced without it."""
    st = peek()
    if slot(st, {"planner"}) or not st["events"] or not kb_ready() or st["notes"]:
        return  # an episode starts from a knowledge base that holds every earlier episode's notes
    if at_capacity(st):
        return  # one session works at a time (WORKERS_MAX): the episode runs in the gap between them
    ready = any((st["tasks"].get(tid) or {}).get("stage") == "ready" for tid in st["queue"])
    urgent = not slot(st, PRODUCING) and not ready
    if time.time() - st.get("plan_ended", 0) < (URGENT_GAP if urgent else EPISODE_GAP):
        return
    if not urgent and time.time() - max(time.mktime(time.strptime(e["at"], "%Y-%m-%dT%H:%M:%S")) for e in st["events"]) < 30:
        return  # let a burst of events arrive together
    with state() as w:
        events, w["events"] = w["events"], []
        n = count(w, "plan")
    name = launch("planner", str(n), lambda name: render(
        "planner", NAME=name, ID="plan", EVENTS=events_text(events), HANDOFF=handoff_parts(), GRAPH=graph_text(), QUEUE=" ".join(peek()["queue"]) or "(empty)",
        STATUS=status_text(), LIST=LIST, OWNER="", FIRST=first_episode(),
        STALE=stale(base_record("max")[0] or "max")), events=events)
    if not name:
        with state() as w:
            w["events"] = events + w["events"]


def waits_on(tasks, tid, other, seen=None):
    """Whether task tid waits, through the graph, on task other (itself included); a completed blocker waits on nothing."""
    if tid == other:
        return True
    seen = seen if seen is not None else set()
    if tid in seen or (tasks.get(tid) or {}).get("status") == "completed":
        return False
    seen.add(tid)
    return any(waits_on(tasks, b, other, seen) for b in (tasks.get(tid) or {}).get("blockedBy") or [])


def fix_deadlock():
    """A task parked for a fix waits on a task that must therefore be able to run: a fix blocked, through the graph, by
    the task waiting for it can never land, and the park's timeout is then the only escape (2026-09-20: task 5 waited
    for task 12 while the work that remained of it was queued behind task 5's own review). Those blockers are dropped
    and the planner is told; nothing else of the graph is touched."""
    st = peek()
    tasks = {t["id"]: t for t in all_tasks()}
    for tid, rec in st["tasks"].items():
        fix = rec.get("efficiency_fix")
        if not fix or fix not in tasks or rec.get("stage") in ("done", None) or rec.get("fix_told"):
            continue
        if (tasks[fix].get("status") or "") == "completed":
            continue
        circle = [b for b in tasks[fix].get("blockedBy") or [] if waits_on(tasks, b, tid)]
        if not circle:
            continue
        update_task(fix, blockedBy=[b for b in tasks[fix].get("blockedBy") or [] if b not in circle])
        with state() as w:
            event(w, "the harness", f"Task {tid} waits for its fix, task {fix}, which was blocked by "
                  f"{', '.join(circle)} — each waiting, through the graph, on task {tid} itself. Those blockers are "
                  f"dropped so the fix can land; if {fix} truly needs one of them, the wait it answers must be ended "
                  f"another way (`v2.py after {tid} none`).")
        log(f"dropped the blockers {', '.join(circle)} of task {fix}: they waited on task {tid}, which waits for it")


def dispatch_once():
    st = peek()
    if not st["active"] or os.path.exists(os.path.join(STATE, "stopped")):
        return
    for part in (tree_care, check_isolation, parking_care, fix_deadlock, efficiency_care, kb_care, produce, support,
                 quick_fix,
                 consult, plan):
        try:  # one part that fails does not hold up the others; it is logged, and tried again at the next dispatch
            part()
        except Exception as e:  # noqa: BLE001
            log(f"dispatch: {part.__name__} failed: {e!r}")


def dispatch(pre=None, wait=False):
    """Run the dispatch, one at a time: a dispatch asked for while one runs makes that one run again. The watchdog runs
    its care of the sessions (pre) under the same lock and waits for it (wait), so that the two never act on one
    session at once."""
    again = os.path.join(STATE, "dispatch.again")
    os.makedirs(STATE, exist_ok=True)
    while True:
        with open(os.path.join(STATE, "dispatch.lock"), "w") as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | (0 if wait else fcntl.LOCK_NB))
            except BlockingIOError:
                open(again, "w").close()
                return
            if pre:
                pre()
                pre = None
            while True:
                with contextlib.suppress(OSError):
                    os.remove(again)
                dispatch_once()
                if not os.path.exists(again):
                    break
        if not os.path.exists(again):
            return


def background(script, *args):
    """Run one of the harness's scripts without holding up the command that asks for it (ORCH_SYNC=1: at once, for
    tests)."""
    cmd = [sys.executable, os.path.join(HERE, script), *args]
    if os.environ.get("ORCH_SYNC") == "1":
        subprocess.run(cmd, cwd=PROJECT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    else:
        subprocess.Popen(cmd, cwd=PROJECT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)


def kick():
    """Dispatch after a change."""
    if os.environ.get("ORCH_SYNC") == "1":
        dispatch()
    else:
        background("v2.py", "dispatch")


# ---------------------------------------------------------------- task transitions

def to_planner(st, tid, sender, text):
    """A task goes back to the planner; what it changed stays in the working tree (leave), and the producing session
    is told (tree_care)."""
    st["tasks"].setdefault(tid, {})["stage"] = "planner"
    aside = leave(tid, "back to the planner")
    if aside:
        st.setdefault("withdrawn", []).append(tid)
    event(st, sender, text + aside)


def checked(tid, ok, tail="", ran=True):
    """The finalizer's check of a task has ended. A check that never ran (a command that is not runnable as written)
    is not a failed check: it costs the task no round, and the session is told to correct the command it handed over
    (2026-09-20: a quick fix reused an output directory the tool refuses, and two one-second failures sent a task
    whose check had passed to the planner)."""
    with state() as st:
        t = st["tasks"].setdefault(tid, {})
        if t.get("stage") != "checking":  # the watchdog gave the task to the planner meanwhile
            event(st, "the finalizer", f"The check of task {tid} ended after the task had left its check "
                  f"({t.get('stage')}): it {'passed' if ok else 'failed'}; .build/tasks/{tid}/finalize.log.")
            ok = None
        elif ok:
            t["stage"] = "reviewing"
            t.pop("reviewing", None)
            if t.get("role") in ("designer", "investigator"):
                event(st, "the finalizer", f"Task {tid} ({t.get('role')}) is finished and its check passes: judge it "
                      f"(its result: .build/tasks/{tid}/result.md; `v2.py verdict {tid} accept|reject --file ...`).")
        elif ok is False and not ran:
            t["spec_errors"] = t.get("spec_errors", 0) + 1
            if t["spec_errors"] <= SPEC_ERRORS:
                t.update(stage="fixing", fixing=None, fix_text=(
                    f"The check of task {tid} did not run at all: the command handed over is not runnable as written. "
                    f"The end of .build/tasks/{tid}/finalize.log:\n{tail}\n\nCorrect the command (`v2.py finalize "
                    f"{tid} --check ... --files ... --message ...`, which replaces what you handed over) and record "
                    "your result again. This did not count as a failed check, and the work itself is untouched."))
            else:
                to_planner(st, tid, "the finalizer", f"The check of task {tid} has not run {t['spec_errors']} times: "
                           f"the command handed over is not runnable as written. The end of "
                           f".build/tasks/{tid}/finalize.log:\n{tail}")
        elif ok is False:
            t["checks_failed"] = t.get("checks_failed", 0) + 1
            if t["checks_failed"] == 1:
                t.update(stage="fixing", fixing=None, fix_text=f"The finalizer's check of task {tid} failed. The end of "
                         f"its log (.build/tasks/{tid}/finalize.log):\n{tail}")
            else:
                to_planner(st, tid, "the finalizer", f"Task {tid} failed its check again after a quick fix; it is yours "
                           f"to re-plan. The end of .build/tasks/{tid}/finalize.log:\n{tail}")
    kick()


def committed(tid, commit, error=None):
    """The finalizer's commit of an accepted task has ended."""
    with state() as st:
        t = st["tasks"].setdefault(tid, {})
        late = t.get("stage") != "committing"
        if late:
            event(st, "the finalizer", f"The commit of task {tid} ended after the task had left it ({t.get('stage')}): "
                  + (f"it is committed as {commit}." if commit else f"it failed: {error}"))
        if commit:
            t["stage"] = "done"
            summary = t.get("summary", "")
            event(st, "the finalizer", f"Task {tid} is committed as {commit}." + (f" {summary}" if summary else ""))
        elif not late:
            to_planner(st, tid, "the finalizer", f"Task {tid} was accepted, but its commit failed: {error}")
        sessions = [t.get("session")] + [n for n, x in st["sessions"].items() if x.get("reviews") == tid]
    if commit:
        for x in [tid, *(peek()["tasks"].get(tid) or {}).get("review_tasks", [])]:
            update_task(x, status="completed")
        for name in sessions:
            if name and (peek()["sessions"].get(name) or {}).get("role") != "designer":
                release(name)
    kick()


# ---------------------------------------------------------------- commands of the sessions

def own_task(tid):
    """Refuse a session acting on a task that is not its own (the owner and the harness may; a consultation has none)."""
    c = caller()
    if c and c["role"] in ("consultant", "kb"):
        return "refused: a consultation answers its question and acts on no task"
    if c and c.get("task") and tid not in (c["task"], c.get("reviews")) and c["role"] != "planner":
        return f"refused: you work on task {c['task']}, not {tid}"
    return None


def cmd_step(tid, n, sources):
    """Open step n: print every source it needs at once (the gather), outside the reading limits; allowed once the
    previous step has produced."""
    import work_meter
    c = caller()
    refused = own_task(tid)
    if refused:
        return refused
    wst = work_meter.load(c["sid"]) if c else {}
    if c and wst.get("step") is not None and wst.get("productions", 0) <= wst.get("step_productions", 0):
        return (f"refused: step {wst.get('step')} has not produced yet: write its part of a deliverable first; the next "
                "step's gather opens after that")
    statements = statements_only(c or {})
    out, shown = [], []
    for src in sources:
        text = gather_one(src, tid, statements, shown)
        out.append(f"== {src}\n{text.rstrip()}\n")
    body = "\n".join(out)
    if len(body) > GATHER_CHARS:
        body = body[:GATHER_CHARS] + (f"\n[the gather stops here, at {GATHER_CHARS} characters: what is cut was not shown; "
                                      "name narrower ranges in the next step]")
    if c:
        wst["step_at"], wst["step"], wst["step_productions"] = iso(), n, wst.get("productions", 0)
        for path, a, b in shown:
            seen = wst["reads"].setdefault(path, {"stamp": work_meter.stamp(path), "ranges": [], "at": ""})
            seen["ranges"].append([a, b])
            seen["at"] = time.strftime("%H:%M")
        work_meter.save(c["sid"], wst)
    return f"Step {n} of task {tid}: its gather.\n\n" + body


def gather_one(src, tid, statements, shown):
    """One source of a gather: a file or a range of it, the task's diff, result or check log, or a named fact."""
    import work_meter
    d = os.path.join(BUILD, tid)
    if src in ("diff", "result", "log"):
        if statements and src != "result":
            return "(refused: the statements of your task are your reading, not its diff or log)"
        if src == "result":
            p = os.path.join(d, "result.md")
            return open(p).read() if os.path.exists(p) else "(no result yet)"
        if src == "log":
            p = os.path.join(d, "finalize.log")
            return "\n".join(open(p, errors="ignore").read().splitlines()[-80:]) if os.path.exists(p) else "(no log)"
        try:
            files = json.load(open(os.path.join(d, "finalize.json")))["files"]
        except (OSError, ValueError, KeyError):
            files = []
        return subprocess.run(["git", "-C", PROJECT, "diff", "HEAD", "--", *files], capture_output=True, text=True).stdout \
            + "".join(f"\n(new file) {f}\n" + open(os.path.join(PROJECT, f), errors="ignore").read()
                      for f in files if subprocess.run(["git", "-C", PROJECT, "ls-files", "--error-unmatch", f],
                                                       capture_output=True).returncode)
    m = re.fullmatch(r"(.+?)(?::(\d+)-(\d+))?", src)
    path = os.path.join(PROJECT, m.group(1))
    if os.path.isfile(path):
        if statements and work_meter.BODY.search(os.path.relpath(path, PROJECT)):
            if path.endswith(".thy"):
                sys.path.insert(0, HERE)
                from digest import held_text
                return held_text(path, "statements")[0]
            return "(refused: code and logs are not your reading; the statements of theories are)"
        lines = open(path, errors="ignore").read().splitlines()
        a, b = (int(m.group(2)), int(m.group(3))) if m.group(2) else (1, len(lines))
        b = min(b, len(lines))
        shown.append((os.path.normpath(path), a, b))
        return "\n".join(f"{i:6}\t{lines[i - 1]}" for i in range(a, b + 1))
    args = ["--statement"] if statements else []
    return subprocess.run([sys.executable, os.path.join(HERE, "show.py"), *args, src], capture_output=True, text=True,
                          cwd=PROJECT, env=dict(os.environ, ORCH_PROJECT=PROJECT)).stdout


def cmd_ask(to, text):
    """A question from a session working on a task, or from a planning episode: to the knowledge base, the planner, or an
    author of the asker's task. A consultation asks nothing (it answers from what it holds), nor does the knowledge
    base; the owner speaks to a session instead (talk.sh, attach.sh)."""
    c = caller()
    if not c or c["role"] in ("consultant", "kb"):
        return ("refused: questions are asked by the sessions working on a task and by planning episodes; a consultation "
                "answers from what it holds, and the owner speaks to a session (talk.sh, attach.sh)")
    st = peek()
    asker = (c or {}).get("name", "the owner")
    tid = (c or {}).get("task")
    t = st["tasks"].get(tid or "", {})
    target = None
    if to == "kb":
        target = "kb"
    elif to == "planner":
        target = "planner"
    elif to == "task-designer":
        target = t.get("briefing")
    elif to == "reviewer":
        target = t.get("reviewed_by")
    elif to == "designer":
        designs = [s for s in st["sessions"].values() if s["role"] == "designer" and s.get("task") in
                   ((read_task(tid) or {}).get("blockedBy") or [])]
        target = designs[-1]["name"] if designs else None
    else:
        return "refused: ask --to kb|planner|designer|task-designer|reviewer TEXT"
    with state() as w:
        qid = f"q{count(w, 'ask')}"
        q = {"from": asker, "to": to, "text": text, "asked": time.time(), "state": "queued", "task": tid,
             "target": target or "kb", "artifacts": f".build/tasks/{(st['sessions'].get(target or '') or {}).get('task')}/"}
        if to == "planner":
            q["state"] = "open"
            event(w, asker, f"Question {qid} (answer with `v2.py reply {qid} TEXT`): {text}")
        w["asks"][qid] = q
    kick()
    who = {"kb": "the knowledge base"}.get(q["target"], q["target"])
    if c and c["role"] in PRODUCING:
        return (f"asked as {qid} ({who}); continue with what does not depend on the answer; when nothing productive is "
                "left, park for it (`v2.py park answer`): another worker produces meanwhile")
    return (f"asked as {qid} ({who}); continue with what does not depend on the answer, and end your turn only when "
            "nothing is left: the answer wakes you")


def cmd_tell(tid, text):
    """The planner (or the owner) tells the sessions working on a task something that changes their work: a review's
    finding, a decision. A busy session receives it at its next tool call, one waiting on a question is resumed with
    it, a parked one finds it when it is resumed."""
    c = caller()
    if c and c["role"] != "planner":
        return "refused: telling a working session is the planner's (and the owner's); ask its author instead"
    st = peek()
    names = [n for n, s in st["sessions"].items() if s.get("task") == tid and not s.get("released")
             and s["state"] in LIVE + ("parked",)]
    if not names:
        return f"refused: no session works on task {tid}"
    for n in names:
        deliver(n, (c or {}).get("name", "the owner"), text)
    return "told " + ", ".join(names)


def cmd_reply(qid, text, decision=False):
    c = caller()
    with state() as st:
        q = st["asks"].get(qid)
        if not q:
            return f"refused: no question {qid}"
        q.update(state="answered", answered=time.time(), answer=text)
        if decision:
            event(st, (c or {}).get("name", "the owner"), f"The answer to {qid} ({q['from']}: {q['text'][:200]}) decides "
                  f"something not decided before: {text}")
            st["notes"].append(f"Decided in answering {q['from']}: {text}")
    if c and c["role"] == "consultant":
        finish(c["name"])
    sender = (c or {}).get("name", "the owner")
    deliver(q["from"], sender, f"Answer to your question {qid} ({q['text'][:200]}):\n{text}")
    landed(qid, q, sender, text)
    kick()
    return "answered; end your turn" if c and c["role"] == "consultant" else "answered"


def landed(qid, q, sender, text):
    """Whether the answer reached its asker. A session that asks without blocking and finishes in the same turn is
    gone when the answer comes, and mail to it is read by nobody: the answer is written where its task's work will
    find it and the planner is told to put it where the work reads it. On 2026-09-20 four of twelve answers sat
    unread in the mailboxes of sessions that had ended, their substance surviving only because the planner had also
    written it into HANDOFF.md and the tasks."""
    s = peek()["sessions"].get(q["from"]) or {}
    if s.get("state") not in ("done", "lost") and not s.get("released"):
        with state() as w:  # parked, waiting, working or starting: it is alive, and its mail reaches it when it goes on
            w["asks"][qid]["delivered"] = True
        return True
    tid = s.get("task") or q.get("task")
    where = os.path.join(BUILD, str(tid), "answers") if tid else os.path.join(BUILD, "answers")
    os.makedirs(where, exist_ok=True)
    path = os.path.join(where, f"{qid}.md")
    open(path, "w").write(f"# {qid}, answered by {sender} after {q['from']} had ended\n\n"
                          f"## The question, from {q['from']}\n\n{q['text']}\n\n## The answer\n\n{text}\n")
    rel = os.path.relpath(path, PROJECT)
    with state() as w:
        w["asks"][qid]["delivered"] = False
        w["asks"][qid]["written"] = rel
        event(w, "the harness", f"The answer to {qid} reached nobody: {q['from']} had ended when it came, and a "
              f"session that has ended reads no mail. It is written to {rel}. Put what it decides where the work "
              f"reads it — the Planner's line of each task it bears on, or HANDOFF.md — because nothing else will "
              f"carry it: {text[:300]}")
    log(f"the answer to {qid} reached nobody ({q['from']} had ended); written to {rel}")
    return False


def cmd_carried(qid, text=""):
    """An answer that reached nobody is carried where the work reads it, and then stops being an open loose end. The
    planner (or the owner) says so, because only they can tell that what it decides is now in the tasks."""
    refused = planner_only("saying an answer is carried")
    if refused:
        return refused
    with state() as st:
        q = st["asks"].get(qid)
        if not q:
            return f"refused: no question {qid}"
        if q.get("delivered") is not False:
            return f"refused: the answer to {qid} reached its asker; nothing is loose"
        q.update(delivered=True, carried=text.strip() or "carried where the work reads it")
    log(f"the answer to {qid} is carried: {text.strip()[:120] or '-'}")
    return f"{qid} is no longer loose"


def jobs_refusal(c, what):
    jobs = running_jobs(c["name"]) if c else []
    return (f"refused: your background jobs {', '.join(jobs)} are still running; stop them (TaskStop) or let them finish "
            f"before you {what}: you are stopped once you have, which would kill them") if jobs else None


def cmd_escalate(text):
    """A performance problem met on the path, through its channel (the owner, 2026-09-19): reported, measured, to the
    planner, who makes its fix a task. The session does not fix it itself, and continues with whatever does not depend
    on the fix, the slow run going on meanwhile; with nothing productive left it parks (cmd_park) for whichever comes
    sooner, the run or the fix."""
    c = caller()
    if not c or c["role"] in ("kb", "consultant"):
        return "refused: a working session reports the performance problems it meets"
    tid = c.get("task")
    with state() as st:
        if tid:
            st["tasks"].setdefault(tid, {}).setdefault("efficiency", []).append({"at": time.time(), "what": text})
        event(st, c["name"], f"Performance problem met by {c['name']}" + (f" on task {tid}" if tid else "")
              + f", which continues with what does not depend on its fix: {text}\nMake the fix a task if it should be "
              "one, ordered by what it blocks" + (f", and name it for the task (`v2.py after {tid} FIXTASK`): the "
              "session is told when it lands, and a session that has come to wait for it is woken then." if tid else "."))
    kick()
    return ("reported: continue with whatever does not depend on the fix, the slow run going on meanwhile. When nothing "
            "productive is left, park (`v2.py park run` for your run, or `v2.py park fix` if the fix will come sooner "
            "than the run ends): another worker produces meanwhile.")


def cmd_measuring(text=""):
    """A run whose result is a timing holds the machine alone: another run beside it distorts the number as surely as
    it exceeds the memory, and the harness gave that hold only to a check advancing the base heap (the owner,
    2026-09-20). Claimed before the run is launched; it stands while the run does, and falls of itself after."""
    c = caller()
    if not c or not c.get("task"):
        return "refused: a session working on a task claims the machine for its measurement"
    holder = exclusive_claim()
    if holder and holder["task"] != c["task"]:
        return (f"refused: task {holder['task']} holds the machine ({holder['why']}). Measure when it has let go; "
                "meanwhile write, or run what is not a measurement.")
    runs = isabelle_runs()
    if runs and not holder:
        return (f"refused: {runs} Isabelle run(s) are going on this machine, and a timing taken beside them is not "
                "the timing of your work. Claim it when they have ended.")
    claim_exclusive(c["task"], text.strip() or "a measurement of its own work", session=c["name"])
    log(f"task {c['task']} holds the machine for a measurement: {text.strip() or '-'}")
    return (f"the machine is yours while your run goes: launch it within {int(CLAIM_GRACE) // 60} minutes. No other "
            "check or measurement starts meanwhile, and the hold ends with your run — record the numbers it gives "
            "before you park or produce.")


def cmd_park(kind, text=""):
    """A producing session with nothing productive left must wait: it parks, and the producing slot is free for another
    worker (the owner, 2026-09-19). It waits for its own run (which keeps the working tree while it reads the task's
    changes), a fix, the working tree, or the answer to its question; it is resumed, its context intact, when that has
    come and the slot and the working tree are free, before any new task starts."""
    c = caller()
    if not c or c["role"] not in PRODUCING:
        return "refused: a producing session parks its task"
    if kind not in ("run", "fix", "tree", "answer"):
        return "refused: v2.py park run|fix|tree|answer"
    tid, st = c["task"], peek()
    jobs = running_jobs(c["name"])
    if kind == "run" and not jobs:
        return "refused: no run of yours is going on: continue, record your result, or park for what you wait on"
    if kind != "run" and jobs:
        return (f"refused: your runs {', '.join(jobs)} are going on: park for them (`v2.py park run`), or stop them "
                "(TaskStop) first")
    holder = tree_holder(st, c) or finalizing(st, c)
    if kind == "tree" and not holder:
        return "the working tree is free: install what you drafted and continue"
    questions = [q for q, a in st["asks"].items() if a["from"] == c["name"] and a["state"] != "answered"]
    if kind == "answer" and not questions:
        return "refused: no question of yours is open"
    after = (st["tasks"].get(tid) or {}).get("efficiency_fix") if kind == "fix" else None
    aside = "" if kind == "run" else leave(tid, "parked")  # a run reads the task's changes: they stay while it runs
    with state() as w:
        w["tasks"].setdefault(tid, {}).update(stage="parked", parked={
            "since": time.time(), "for": kind, "why": text, "after": after, "holds_tree": kind == "run",
            "questions": questions, "holder": holder})
        w["sessions"][c["name"]]["state"] = "parked"
        if kind == "fix" and not after:
            event(w, c["name"], f"Task {tid} is parked for the fix of its performance problem: tell the harness which task "
                  f"fixes it (`v2.py after {tid} FIXTASK`, or `v2.py after {tid} none` to let it continue as it is).")
    kick()
    what = {"run": "your run has ended", "fix": "the fix has landed", "tree": f"task {holder} has let the working tree go",
            "answer": "the answer has come"}[kind]
    return (f"parked: end your turn now; another worker produces meanwhile. You are resumed here, your context intact, "
            f"when {what} and the producing slot is free; if not within {HOLD_PARK // 3600} hours, you are woken to record "
            "a partial result." + (f"{aside}" if aside else "")
            + (" Your run keeps going; its completion does not resume you by itself." if kind == "run" else ""))


def cmd_unshelve(tid):
    """A producing session continues another task's work: that task's set-aside changes come back into the working tree,
    as its own changes."""
    c = caller()
    if c and c["role"] not in PRODUCING:
        return "refused: a producing session takes up set-aside changes"
    holder = tree_holder(peek(), c)
    if holder:
        if c:
            mark_tree_wait(c["name"], holder)
        return (f"refused: task {holder}'s finalization holds the working tree; take them up when it has landed (you are "
                "told)")
    text = take_up(tid, (c or {}).get("task"))
    return text.strip() or f"nothing of task {tid} is set aside"


def cmd_finalize(tid, args):
    refused = own_task(tid)
    if refused:
        return refused
    holder = finalizing(peek(), caller())
    if holder:
        return (f"refused: task {holder}'s finalization is in flight and one runs at a time, since a check sees the "
                "working tree: yours begins when it has landed. Install what you drafted then; with nothing productive "
                "left meanwhile, park (`v2.py park tree`)")
    check, files, message = None, [], None
    while args:
        a = args.pop(0)
        if a == "--check" and args:
            check = args.pop(0)
        elif a == "--message" and args:
            message = args.pop(0)
        elif a == "--files":
            while args and not args[0].startswith("--"):
                files.append(args.pop(0))
    bad = [f for f in files if not os.path.lexists(os.path.join(PROJECT, f)) and git_out("ls-files", "--error-unmatch", "--", f) is None]
    outside = [f for f in files if os.path.isabs(f) or os.path.normpath(f).startswith("..") or exempt(os.path.normpath(f))
               or subprocess.run(["git", "-C", PROJECT, "check-ignore", "-q", "--", f]).returncode == 0]
    if outside:
        return ("refused: the finalizer commits files of the repository's working tree, not ignored, not under .build/ or "
                f".claude/, relative to the project: {', '.join(outside)}")
    if not check or not files or not message or bad or not os.path.exists(os.path.join(PROJECT, message)):
        return ("refused: v2.py finalize ID --check CMD --files PATH... --message FILE, every file existing (or a deletion "
                "of a tracked one)"
                + (f" (missing: {', '.join(bad)})" if bad else ""))
    os.makedirs(os.path.join(BUILD, tid), exist_ok=True)
    json.dump({"check": check, "files": files, "message": message}, open(os.path.join(BUILD, tid, "finalize.json"), "w"), indent=1)
    return "the final job is prepared; its check runs when you record your result"


def cmd_result(tid):
    refused = own_task(tid)
    if refused:
        return refused
    path = os.path.join(BUILD, tid, "result.md")
    text = open(path, errors="ignore").read() if os.path.exists(path) else ""
    problems = result_problems(text) if text else [f"write the result to .build/tasks/{tid}/result.md first"]
    if problems:
        return "refused: the result is not in form:\n- " + "\n- ".join(problems)
    status = field(text, "Status").split()[0].strip(".,").lower()
    final = os.path.join(BUILD, tid, "finalize.json")
    try:
        committed_files = [p for p in json.load(open(os.path.join(BUILD, tid, "brief.json")))["deliverables"]
                           if not p.startswith(".build/")]
    except (OSError, ValueError, KeyError):
        committed_files = []
    if status == "done" and committed_files and not os.path.exists(final):
        return ("refused: a done task's deliverables are committed by the finalizer: hand it the final job first "
                f"(`v2.py finalize {tid} --check ... --files ... --message .build/tasks/{tid}/commit.md`)")
    c = caller()
    refused = jobs_refusal(c, "record your result")
    if refused:
        return refused
    with state() as st:
        t = st["tasks"].setdefault(tid, {})
        name = (c or {}).get("name") or t.get("session")
        if name in st["sessions"]:
            st["sessions"][name].update(state="done", ended=time.time(), result=status)
            st["sessions"][name].pop("fix", None)
        t["fixing"] = None
        if status != "done":
            to_planner(st, tid, name or "the harness", f"Task {tid} ended {status}: .build/tasks/{tid}/result.md "
                       "(what exists, what remains). Split it into tasks over what exists, or re-plan it.")
        elif os.path.exists(final):
            t["stage"] = "checking"
        else:  # nothing to commit: judged as it is
            t["stage"] = "reviewing"
            if t.get("role") in ("designer", "investigator"):
                event(st, name or "the harness", f"Task {tid} ({t.get('role')}) is finished: judge it (its result: "
                      f".build/tasks/{tid}/result.md; `v2.py verdict {tid} accept|reject --file ...`).")
    log(f"result of task {tid}: {status}")
    if status == "done" and os.path.exists(final):
        background("finalize.py", "check", tid)  # its end dispatches
    else:
        kick()
    return "recorded. End your turn now."


def cmd_briefed(bid, new):
    """The task designer of brief task bid has put its tasks into the graph: each in form, every build or fix with a
    review task naming it; they are queued after the brief task, which is done."""
    c = caller()
    if c and (c["role"] != "task-designer" or c.get("task") != bid):
        return f"refused: brief task {bid} is recorded by its task designer"
    problems, briefs = [], {}
    for t in new:
        task = read_task(t)
        if not task:
            problems.append(f"task {t} is not in the task list")
            continue
        briefs[t] = task.get("description", "")
        problems += [f"task {t}: {p}" for p in brief_problems(briefs[t])]
    if not new:
        problems.append("name the tasks you briefed: `v2.py briefed ID NEW...`")
    reviews = {t: reviewed(b) for t, b in briefs.items() if brief_kind(b) == "review"}
    for t, b in briefs.items():
        if brief_kind(b) in ("build", "fix") and t not in reviews.values():
            problems.append(f"task {t} is a {brief_kind(b)} task without a review task (kind review, `Reviews:` naming it)")
    for r, t in reviews.items():
        if t not in briefs and not read_task(t):
            problems.append(f"review task {r} reviews {t}, which is not in the task list")
    if problems:
        return "refused: the briefs are not in form:\n- " + "\n- ".join(problems)
    by = (c or {}).get("name")
    with state() as st:
        for t, b in briefs.items():
            st["tasks"].setdefault(t, {}).update(stage="ready", kind=brief_kind(b), briefed_by=by, briefing=by,
                                                 queued_at=time.time(), brief_task=bid)
        for r, t in reviews.items():
            st["tasks"][r]["reviews"] = t
            rt = st["tasks"].setdefault(t, {}).setdefault("review_tasks", [])
            if r not in rt:
                rt.append(r)
        q = st["queue"]
        at = q.index(bid) + 1 if bid in q else len(q)
        st["queue"] = q[:at] + [t for t in new if t not in q] + q[at:]
        st["tasks"].setdefault(bid, {})["stage"] = "done"
        if c:
            st["sessions"][c["name"]].update(state="done", ended=time.time())
    update_task(bid, status="completed")
    kick()
    return "briefed. End your turn now."


def cmd_verdict(rid, verdict, path):
    """A verdict: of a review task on the task it reviews (the task moves once every one of its reviews has given one:
    all accepting, it is committed; any rejecting, it gets its one fix with every finding), or of the planner on a
    design or an investigation (or of a review the harness planned, on the task itself)."""
    c = caller()
    if c and c["role"] not in ("reviewer", "planner"):
        return "refused: a verdict is the reviewer's, or the planner's on a design or an investigation"
    if verdict not in ("accept", "reject"):
        return "refused: v2.py verdict ID accept|reject --file FILE"
    text = open(os.path.join(PROJECT, path), errors="ignore").read() if path and os.path.exists(os.path.join(PROJECT, path)) else ""
    problems = verdict_problems(text, verdict)
    if problems:
        return "refused: the verdict is not in form:\n- " + "\n- ".join(problems)
    if c and c["role"] == "reviewer" and c.get("task") != rid:
        return f"refused: you review for task {c.get('task')}, not {rid}"
    by = (c or {}).get("name", "the owner")
    commit = False
    with state() as st:
        r = st["tasks"].setdefault(rid, {})
        tid = r.get("reviews") or rid
        t = st["tasks"].setdefault(tid, {})
        if t.get("stage") != "reviewing":
            return f"refused: task {tid} is not awaiting a verdict (it is {t.get('stage')})"
        r.update(verdict=verdict, findings=part(text, "Findings"), summary=part(text, "Summary"),
                 followups=part(text, "Follow-ups"), reviewing=None, verdict_file=path)
        if c and c["role"] == "reviewer":
            st["sessions"][c["name"]].update(state="done", ended=time.time())
        rids = t.get("review_tasks") or [tid]
        judged = [st["tasks"].get(x) or {} for x in rids]
        waiting = any(j.get("verdict") is None or j.get("reviewing") for j in judged)
        if not waiting:
            t["reviewing"] = None
        follow = "; ".join(j["followups"] for j in judged if j.get("followups"))
        if waiting:
            pass
        elif all(j["verdict"] == "accept" for j in judged):
            t["summary"] = " ".join(j.get("summary", "") for j in judged) + (f" Follow-ups proposed: {follow}" if follow else "")
            for x in rids:
                if x != tid:
                    st["tasks"][x]["stage"] = "done"
            if os.path.exists(os.path.join(BUILD, tid, "finalize.json")):
                t["stage"], commit = "committing", True
            else:
                t["stage"] = "done"
                event(st, by, f"Task {tid} is accepted (nothing to commit). {t['summary']}")
        else:
            t["rejections"] = t.get("rejections", 0) + 1
            findings = "\n".join(f"From {x} ({(st['tasks'].get(x) or {}).get('verdict_file')}):\n{j['findings']}"
                                 for x, j in zip(rids, judged) if j["verdict"] == "reject")
            if t["rejections"] == 1:
                t.update(stage="fixing", fixing=None, fix_text=f"The review of task {tid} rejected it. Its blocking "
                         f"findings, all of them:\n{findings}")
            else:
                to_planner(st, tid, by, f"Task {tid} was rejected again after its fix round; it is yours to decide "
                           f"(accept with follow-ups, a fixer's task, or re-planning). The findings:\n{findings}"
                           + (f"\nFollow-ups proposed: {follow}" if follow else ""))
    if waiting:
        kick()
        return f"{verdict}ed task {tid} for review {rid}; its other reviews are pending" + (
            ". End your turn now." if c and c["role"] == "reviewer" else "")
    if t.get("stage") == "done":  # accepted with nothing to commit: the task and its reviews are completed
        for x in dict.fromkeys([tid, *rids]):
            update_task(x, status="completed")
    if commit:
        background("finalize.py", "commit", tid)  # its end dispatches
    else:
        kick()
    return f"{verdict}ed task {tid}" + (". End your turn now." if c and c["role"] == "reviewer" else "")


def cmd_queue(ids):
    """The planner's order. Tasks a task designer queued after this episode began, which the episode could not have
    seen, keep their place after the brief task that made them (or go last) unless the order names them."""
    c = caller()
    if c and c["role"] != "planner":
        return "refused: the queue is the planner's"
    since = (c or {}).get("started") or time.time()
    with state() as st:
        for tid in ids:
            t = st["tasks"].get(tid) or {}
            if t.get("stage") in ("planner", "unformed"):  # re-planned: its stage is read afresh from its brief
                st["tasks"][tid] = {k: v for k, v in t.items() if k in ("briefed_by", "briefing", "review_tasks", "reviews")}
        order = list(ids)
        kept = [tid for tid in st["queue"] if tid not in order and (st["tasks"].get(tid) or {}).get("queued_at", 0) > since
                and (st["tasks"].get(tid) or {}).get("stage") != "done"]
        for tid in kept:
            brief = (st["tasks"].get(tid) or {}).get("brief_task")
            at = order.index(brief) + 1 if brief in order else len(order)
            while at < len(order) and order[at] in kept:
                at += 1
            order.insert(at, tid)
        st["queue"] = order
    missing = [tid for tid in ids if not read_task(tid)]
    kick()
    return "queued" + (f"; kept, briefed since this episode began: {', '.join(kept)}" if kept else "") + (
        f"; not in the task list: {', '.join(missing)}" if missing else "")


def planner_only(what):
    c = caller()
    return f"refused: {what} is the planner's" if c and c["role"] != "planner" else None


def cmd_after(tid, other):
    """The planner names the task that fixes a task's performance problem: a parked task continues when it has landed;
    a task still working is told then (efficiency_care), and waits on it if it comes to wait."""
    refused = planner_only("naming a task's fix")
    if refused:
        return refused
    with state() as st:
        t = st["tasks"].get(tid)
        if t is None:
            return f"refused: task {tid} is not known"
        if other != "none":
            tasks = {x["id"]: x for x in all_tasks()}
            circle = [b for b in (tasks.get(other) or {}).get("blockedBy") or [] if waits_on(tasks, b, tid)]
            if circle:
                return (f"refused: task {other} is blocked by {', '.join(circle)}, which waits on task {tid} itself, so "
                        f"the fix could never land. Queue {other} ahead of that, or let {tid} continue as it is "
                        f"(`v2.py after {tid} none`).")
            t.update(efficiency_fix=other, fix_told=False)
        if t.get("stage") == "parked" and (t.get("parked") or {}).get("for", "fix") == "fix":
            t["parked"]["after"] = other
        elif other == "none":
            return f"refused: task {tid} is not parked for a fix"
    kick()
    if t.get("stage") == "parked" and (t.get("parked") or {}).get("for", "fix") == "fix":
        return f"task {tid} continues when {other} has landed" if other != "none" else f"task {tid} continues"
    return f"task {tid} is told when {other} has landed, and waits on it if it parks for its fix"


def efficiency_care():
    """A fix a working task's session reported the need for has landed: the session is told, and uses it from now on."""
    st = peek()
    for tid, t in st["tasks"].items():
        fix = t.get("efficiency_fix")
        if fix and not t.get("fix_told") and t.get("stage") == "running" and \
                (read_task(fix) or {}).get("status") == "completed":
            with state() as w:
                w["tasks"][tid]["fix_told"] = True
            if t.get("session"):
                deliver(t["session"], "the harness", f"Task {fix}, the fix of the performance problem you reported, has "
                        "landed: use it from now on.")


def cmd_drop(tid):
    refused = planner_only("dropping a task")
    if refused:
        return refused
    st = peek()
    names = [n for n, s in st["sessions"].items() if s.get("task") == tid and not s.get("released")]
    for n in names:
        release(n)
    aside = leave(tid, "dropped")
    with state() as w:
        w["tasks"].setdefault(tid, {})["stage"] = "planner"
        w["queue"] = [t for t in w["queue"] if t != tid]
    return "dropped " + (", ".join(names) or "nothing") + aside


def cmd_planned(notes):
    c = caller()
    if c and c["role"] != "planner":
        return "refused: ending a planning episode is the planner's"
    text = open(os.path.join(PROJECT, notes), errors="ignore").read().strip() if notes and os.path.exists(
        os.path.join(PROJECT, notes)) else ""
    handoff = os.path.join(PROJECT, "HANDOFF.md")
    problems = planner_state_problems(open(handoff, errors="ignore").read() if os.path.exists(handoff) else "")
    if problems:
        return "refused: HANDOFF.md is not in the form of the planner's state:\n- " + "\n- ".join(problems)
    if not text:
        return "refused: v2.py planned --notes FILE: the notes the knowledge base integrates (what it must now hold)"
    with state() as st:
        st["notes"].append(f"From {(c or {}).get('name', 'the owner')}:\n{text}")
        st["plan_ended"] = time.time()
        if c:
            st["sessions"][c["name"]].update(state="done", ended=time.time())
    kick()
    return "planned. End your turn now."


# ---------------------------------------------------------------- commands of the harness

def cmd_start():
    with state() as st:
        st["active"] = True
        first = not st["kb"] and not st.get("kb_building")
        if first and not st.get("plan_ended"):
            event(st, "the harness", "The orchestration starts, and there is no task graph yet: build it (the first "
                  "episode's part of this message says from what).")
        for i in st.pop("interrupted", []):
            event(st, "the harness", i)
    dispatch()
    st = peek()
    return f"active; knowledge base {st['kb'] or st.get('kb_building') or 'not started (see state/v2.log)'}"


def cmd_stop():
    """Every live session stopped; the orchestration inactive. What was interrupted is an event for the next episode."""
    at = time.strftime("%Y-%m-%dT%H:%M:%S")
    st = peek()
    live = [n for n, s in st["sessions"].items() if s["state"] in LIVE or row(n)]
    leaving = []
    with state() as w:
        w["active"] = False
        for n in live:
            s = w["sessions"][n]
            if s["state"] in LIVE and s.get("task"):
                w.setdefault("interrupted", []).append(
                    f"The orchestration was stopped at {at} while {n} ({s['role']}) worked on task {s['task']}; what it "
                    f"wrote is on disk (.build/tasks/{s['task']}/ and its deliverables).")
                t = w["tasks"].get(s["task"]) or {}
                if s["role"] in PRODUCING and t.get("stage") == "running":
                    t["stage"] = "planner"
                    leaving.append((len(w["interrupted"]) - 1, s["task"]))
                if s["role"] == "reviewer":
                    t["reviewing"] = None
                    t.pop("round", None)
                    (w["tasks"].get(s.get("reviews") or "") or {})["reviewing"] = None
                if s["role"] == "task-designer" and t.get("stage") == "running":
                    t["stage"] = "ready"
            if s["state"] in LIVE:
                s["state"] = "lost"
            if s["role"] == "planner" and s.get("events"):
                w["events"] = s["events"] + w["events"]
            if s["role"] == "consultant" and s.get("qid") in w["asks"]:
                w["asks"][s["qid"]]["state"] = "queued"
            if s["role"] == "kb":
                s["kb_state"] = "sealed" if s.get("kb_state") == "integrating" else s.get("kb_state")
        if w.get("kb_building"):
            w["kb_building"] = None
    for n in live:
        seal(n)
    for i, tid in leaving:  # the sessions have stopped; what they installed stays in the tree
        aside = leave(tid, "interrupted")
        if aside:
            with state() as w:
                w["interrupted"][i] += aside
    return "stopped " + (", ".join(live) or "nothing")


def cmd_talk():
    """A planning episode for the owner to speak to (talk.sh attaches to it), launched under the dispatch's lock so that
    the two never start two episodes."""
    with open(os.path.join(STATE, "dispatch.lock"), "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        return talk()


def talk():
    st = peek()
    s = slot(st, {"planner"})
    if s:
        return s["name"]
    if not kb_ready() or st["notes"]:
        return ""  # the knowledge base is not ready, or has not yet integrated the last episode's notes
    with state() as w:
        events, w["events"] = w["events"], []
        n = count(w, "plan")
    name = launch("planner", str(n), lambda name: render(
        "planner", NAME=name, ID="plan", EVENTS=events_text(events), HANDOFF=handoff_parts(), GRAPH=graph_text(), QUEUE=" ".join(peek()["queue"]) or "(empty)",
        STATUS=status_text(), LIST=LIST, OWNER="The owner opened this episode to speak with you: wait for the owner's "
        "words (the harness records them verbatim in the owner ledger), act on them in the graph, the order and the "
        "decisions, carry them into HANDOFF.md and your notes, and end the episode (`v2.py planned`) only when the "
        "owner is done.", FIRST=first_episode(), STALE=stale(base_record("max")[0] or "max")), events=events, owner=True)
    if not name:
        with state() as w:
            w["events"] = events + w["events"]
    return name or ""


def cmd_who(role):
    st = peek()
    roles = {"planner": {"planner"}, "producer": PRODUCING, "support": SUPPORTING, "kb": {"kb"},
             "consultant": {"consultant"}}.get(role)
    if role == "fix":
        s = slot(st, PRODUCING, fix=True)
    elif role == "kb":
        s = st["sessions"].get(st.get("kb_building") or st["kb"] or "")
    else:
        s = slot(st, roles or set())
    return s["name"] if s and s.get("sid") else ""


def cmd_status():
    st = peek()
    out = [f"orchestration: {'active' if st['active'] else 'inactive'}",
           f"knowledge base: {st['kb'] or '-'}" + (f" ({(st['sessions'].get(st['kb']) or {}).get('kb_state')})" if st['kb'] else "")
           + (f"; building {st['kb_building']}" if st.get("kb_building") else "")]
    for label, roles, fix in (("planner", {"planner"}, False), ("producing", PRODUCING, False),
                              ("supporting", SUPPORTING, False), ("quick fix", PRODUCING, True),
                              ("consultation", {"consultant"}, False)):
        s = slot(st, roles, fix)
        out.append(f"{label}: " + (f"{s['name']}" + (f" on {s['task']}" if s.get("task") else "") + f" ({s['state']})"
                                   if s else "-"))
    out.append("queue: " + (" ".join(f"{t}:{(st['tasks'].get(t) or {}).get('stage', '?')}" for t in st["queue"]) or "-"))
    busy = working(st)
    out.append(f"working: {len(busy)} of at most {WORKERS_MAX}" + (f" ({', '.join(busy)})" if busy else ""))
    backlog = build_backlog(st)
    out.append(f"build backlog: {len(backlog)} open build and fix tasks of at most {BRIEF_BACKLOG}"
               + ("; no brief is detailed until the builders have taken some" if len(backlog) >= BRIEF_BACKLOG else ""))
    parked = [f"{tid} ({int(time.time() - t['parked']['since']) // 60} min, after {t['parked'].get('after') or '?'})"
              for tid, t in st["tasks"].items() if t.get("stage") == "parked"]
    if parked:
        out.append("parked: " + ", ".join(parked))
    waiting = [tid for tid, t in st["tasks"].items() if t.get("stage") in ("checking", "reviewing", "fixing", "committing")]
    if waiting:
        out.append("finishing: " + ", ".join(f"{tid}:{st['tasks'][tid]['stage']}" for tid in waiting))
    if st["events"]:
        out.append(f"events for the next episode: {len(st['events'])}")
    undelivered = [f"{q} ({a['from']} had ended; {a.get('written')})" for q, a in st["asks"].items()
                   if a.get("delivered") is False]
    if undelivered:
        out.append("answers that reached nobody: " + ", ".join(undelivered))
    open_asks = [f"{q} to {a['target']}" for q, a in st["asks"].items() if a["state"] != "answered"]
    if open_asks:
        out.append("questions: " + ", ".join(open_asks))
    return "\n".join(out)


def ping(name):
    """Keep a sealed session's cache warm: a throwaway fork reads its whole prefix and is deleted (as base.sh warm)."""
    s = peek()["sessions"].get(name) or {}
    if not s.get("sid") or not warm(name):
        return f"{name}: not pinged ({'cold' if s.get('sid') else 'unknown'})"
    n = f"warm-{name}"
    claude("--bg", "--resume", s["sid"], "--fork-session", *open(os.path.join(HERE, "session-flags")).read().split(),
           "--model", s["model"], "--effort", s["effort"], "--permission-mode", "auto",
           "--settings", os.path.join(HERE, s["settings"]), "-n", n,
           f"Keep-warm ping {int(time.time())}. Use no tools. Reply with the single word WARM and end your turn.")
    r = None
    for _ in range(90):
        r = row(n)
        if r and r["activity"] == "idle" and os.environ.get("ORCH_PING_WAIT", "1") != "0":
            break
        if r and os.environ.get("ORCH_PING_WAIT", "1") == "0":
            break
        time.sleep(PAUSE)
    verdict = subprocess.run([os.path.join(HERE, "session_fork_check.py"), r["sid"], s["sid"]], capture_output=True,
                             text=True).stdout.strip() if r else "no ping session"
    if r:
        claude("stop", r["id"])
        claude("rm", r["id"])
        for p in (f"{TRANSCRIPTS}/{r['sid']}.jsonl", f"{TRANSCRIPTS}/{r['sid']}"):
            with contextlib.suppress(OSError):
                shutil.rmtree(p) if os.path.isdir(p) else os.remove(p)
    if verdict.startswith(("OK", "MISS")) or os.environ.get("ORCH_PING_WAIT") == "0":
        hit_chain(name)  # the ping read the whole prefix, its origins' included
    log(f"ping {name}: {verdict[:160]}")
    return verdict


def cache_check(sid, base_sid, name):
    """Background: record whether a fork's first request read its origin from cache."""
    for _ in range(40):
        v = subprocess.run([os.path.join(HERE, "session_fork_check.py"), sid, base_sid], capture_output=True, text=True).stdout
        if v.startswith(("OK", "MISS")):
            log(f"cache of {name}: {v.split(' first own request ')[-1].split(' (')[0] if 'first own request' in v else v[:80]}"
                + ("" if v.startswith("OK") else " MISS"))
            return
        time.sleep(3)


def main():
    a = sys.argv[1:]
    if not a:
        print(__doc__)
        return 2
    c, rest = a[0], a[1:]

    def opt(name):
        if name in rest:
            i = rest.index(name)
            value = rest[i + 1] if i + 1 < len(rest) else ""
            del rest[i:i + 2]
            return value
        return None
    if c == "step" and len(rest) >= 3:
        print(cmd_step(rest[0], rest[1], rest[2:]))
    elif c == "ask":
        to = opt("--to")
        print(cmd_ask(to, " ".join(rest)) if to and rest else "refused: ask --to kb|planner|designer|task-designer|reviewer TEXT")
    elif c == "tell" and len(rest) >= 2:
        print(cmd_tell(rest[0], " ".join(rest[1:])))
    elif c == "reply" and rest:
        decision = "--decision" in rest
        rest = [x for x in rest if x != "--decision"]
        f = opt("--file")
        qid = rest.pop(0)
        text = open(os.path.join(PROJECT, f), errors="ignore").read() if f else " ".join(rest)
        print(cmd_reply(qid, text, decision) if text.strip() else "refused: reply QID TEXT|--file FILE")
    elif c == "carried" and rest:
        print(cmd_carried(rest[0], " ".join(rest[1:])))
    elif c == "measuring":
        print(cmd_measuring(" ".join(rest)))
    elif c == "escalate":
        text = opt("--efficiency")
        print(cmd_escalate(" ".join(filter(None, [text, *rest]))) if text else "refused: escalate --efficiency TEXT")
    elif c == "park" and rest:
        print(cmd_park(rest[0], " ".join(rest[1:])))
    elif c == "unshelve" and len(rest) == 1:
        print(cmd_unshelve(rest[0]))
    elif c == "finalize" and rest:
        print(cmd_finalize(rest[0], rest[1:]))
    elif c == "result" and len(rest) == 1:
        print(cmd_result(rest[0]))
    elif c == "briefed" and rest:
        print(cmd_briefed(rest[0], rest[1:]))
    elif c == "verdict" and len(rest) >= 2:
        f = opt("--file")
        print(cmd_verdict(rest[0], rest[1], f))
    elif c == "queue":
        print(cmd_queue(rest))
    elif c == "after" and len(rest) == 2:
        print(cmd_after(rest[0], rest[1]))
    elif c == "drop" and len(rest) == 1:
        print(cmd_drop(rest[0]))
    elif c == "planned":
        print(cmd_planned(opt("--notes")))
    elif c == "start":
        print(cmd_start())
    elif c == "stop":
        print(cmd_stop())
    elif c == "talk":
        print(cmd_talk())
    elif c == "graph":
        print(graph_text(full="--all" in rest))
    elif c == "status":
        print(cmd_status())
    elif c == "who" and len(rest) == 1:
        print(cmd_who(rest[0]))
    elif c == "dispatch":
        dispatch()
    elif c == "ping" and len(rest) == 1:
        print(ping(rest[0]))
    elif c == "cache-check" and len(rest) == 3:
        cache_check(*rest)
    else:
        print(__doc__)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
