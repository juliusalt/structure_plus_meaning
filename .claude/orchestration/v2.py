#!/usr/bin/env python3
"""Orchestration v2: a knowledge base, planning episodes, and one session per piece of work
(notes/orchestration-v2-plan.md).

Every self-contained piece of work is a fork: of a sealed base, of the knowledge base, or of a sealed session that is
consulted. A resume only continues the same piece of work (a quick fix, a re-review, an implementer woken after the
efficiency fix it waited for). A session whose cache has expired is never woken or forked.

  knowledge base   kb-N: a fork of the planner's base that never works; its context is what has been integrated
                   into it (HANDOFF.md, the owner's words, the notes of every planning episode). Sealed between
                   integrations; questions to it are answered by forks of it.
  planner          plan-N: one long-lived fork of the knowledge base. Every event reaches it as it happens, as its
                   own message; it orders the graph and decides, and ends only when its window forces it to, writing
                   then the notes the knowledge base is to hold — what it has settled, aggregated, with what has
                   since been answered or superseded left out. Between events it is sealed and held warm.
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
  v2.py propose ID FILE          the task designer: its tasks and where to place them (JSON); the planner places them
  v2.py accept ID                the planner: write a brief's proposed tasks into the graph, as proposed
  v2.py verdict ID accept|reject --file FILE   the reviewer (or the planner, for design and investigation)
  v2.py queue ID...              the planner: the order in which tasks are to be done
  v2.py after ID TASK            the planner: the parked task ID continues when TASK has landed (`none`: now)
  v2.py blockers ID ID...|none   the planner: what task ID waits on, set whole (TaskUpdate only adds)
  v2.py drop ID                  the planner: stop whatever works on task ID
  v2.py planned --notes FILE     the planner: its work ends (its window is full); its notes go to the knowledge base
Harness:
  v2.py start [--fresh] | stop | status | graph | who ROLE | dispatch | talk | ping NAME
      --fresh: leave the knowledge base behind (the next is built from HANDOFF.md, the ledger and the owner's words)
      and charge the first planner with taking stock before it queues anything
"""
import contextlib
import fcntl
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))


def _one_tree(here):
    """The repository's one working tree, even when this copy of the harness sits inside a linked git worktree.

    A worktree is a checkout of the repository, so it carries its own `.claude/orchestration` — and `state/` is
    gitignored, so v2.py run from there makes a second, empty v2.json and acts on that. On 2026-09-20 fix-49.2 was
    captured into `.build/trees/49` and recorded its finalize, its result and its whole account into that parallel
    state: the real harness never saw any of it, declared the session gone, handed its task back to the planner, and
    the session sat blocked by the worktree's own copy of the stop hook with no way to end its turn. A worktree's
    `.git` is a file naming the real one, which is how this is told apart without spending a git call per tool."""
    project = os.path.dirname(os.path.dirname(here))
    dotgit = os.path.join(project, ".git")
    try:
        if os.path.isfile(dotgit):  # "gitdir: /…/<main>/.git/worktrees/<name>"
            gitdir = open(dotgit).read().split(":", 1)[1].strip()
            main = os.path.dirname(os.path.dirname(os.path.dirname(gitdir)))
            if os.path.isdir(os.path.join(main, ".git")):
                return main
    except (OSError, IndexError):
        pass
    return project


PROJECT = os.environ.get("ORCH_PROJECT") or _one_tree(HERE)
# STATE follows the one tree too, not this copy's directory, for the same reason. The shell scripts still take
# `$HERE/state`, which is the same path in every case but one: a copy of the harness inside a linked worktree, which
# nothing runs them from — the daemon and the owner run the main copy. Left as it is rather than teaching five
# scripts to resolve a worktree, which would be more machinery than the fault is worth.
STATE = os.environ.get("ORCH_STATE_DIR") or os.path.join(PROJECT, ".claude", "orchestration", "state")
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
    # The knowledge base is off the shared task list (worker-settings.json is planner-settings.json without it, and
    # nothing else): it may not edit the graph, it has no use for its state, and every session forked from it would
    # carry whatever was injected into it — the sealed kb-1 of 2026-09-20 holds three such injections, about 800
    # tokens, in the prefix that every planner and every consultation reads.
    "kb": dict(origin="max", settings="worker-settings.json", prefix="kb", statements=True, graph=False),
    "planner": dict(origin="kb", settings="planner-settings.json", prefix="plan", statements=True, graph=True),
    "designer": dict(origin="xhigh", settings="worker-settings.json", prefix="design", statements=False, graph=False),
    # It proposes tasks and their placement; the planner decides and the harness writes them. It does not edit the
    # graph, so it is off the shared task list with every other role that does not (the owner, 2026-09-20).
    "task-designer": dict(origin="xhigh", settings="worker-settings.json", prefix="brief", statements=True),
    "investigator": dict(origin="xhigh", settings="worker-settings.json", prefix="investigate", statements=False, graph=False),
    "reviewer": dict(origin="xhigh", settings="worker-settings.json", prefix="review", statements=False, graph=False),
    "implementer": dict(origin="high", settings="worker-settings.json", prefix="implement", statements=False, graph=False),
    "fixer": dict(origin="high", settings="worker-settings.json", prefix="fix", statements=False, graph=False),
    "consultant": dict(origin=None, settings=None, prefix="ask", statements=None, graph=False),
}
PRODUCER = {"design": "designer", "investigate": "investigator", "build": "implementer", "fix": "fixer"}
PRODUCING, SUPPORTING = set(PRODUCER.values()), {"task-designer", "reviewer"}
GRAPH_SETTINGS = "planner-settings.json"  # the one settings file that joins the shared task list (the graph):
# every session started with it sees the others' edits to it, injected into its context. Only the roles that edit
# the graph are given it; every other session's task list is its own, named by its own session.
LIVE = ("starting", "working", "waiting")  # a session in one of these holds its slot

JOB_STALE = int(os.environ.get("ORCH_JOB_STALE", 7200))  # a background job whose output stands still this long is dead
SPEC_ERRORS = int(os.environ.get("ORCH_SPEC_ERRORS", 2))  # tries at a check command that is not runnable
FIX_MINUTES = int(os.environ.get("ORCH_FIX_MINUTES", 15))
KB_INTEGRATE_MAX = int(os.environ.get("ORCH_KB_INTEGRATE_MAX", 1200))  # a knowledge base that never
# replies INTEGRATED would hold every episode and every consultation for ever
CLAUDE_MAX = int(os.environ.get("ORCH_CLAUDE_MAX", 180))  # a CLI call that never returns
KB_BUILD_MAX = int(os.environ.get("ORCH_KB_BUILD_MAX", 3600))  # a load that never replies, likewise
LOST_BLOCKER = 3600  # how often a task waiting for a blocker that is not there is named
TREE_TOLD = 900  # how often the same trouble in the same tree is put to the planner again
TIDY_EVERY = int(os.environ.get("ORCH_TIDY_EVERY", 3600))  # how often state nothing names is swept
WOKEN_KEEP = int(os.environ.get("ORCH_WOKEN_KEEP", 86400))  # a wake mark, for attach.sh to read
BRIEF_BACKLOG = int(os.environ.get("ORCH_BRIEF_BACKLOG", 0))  # 0: no ceiling on the number of open build and fix
# tasks (the owner, 2026-09-20). It was 6 and counted what EXISTS, so 17 open tasks detained every brief while only 5
# of them could start — and a brief is what widens a graph. The count says nothing worth acting on: what a brief is
# admitted by is the width (GRAPH_WIDTH), and what it may add is bounded by the depth (GRAPH_DEPTH).
GRAPH_WIDTH = int(os.environ.get("ORCH_GRAPH_WIDTH", 0))  # 0: the slots. A brief is detailed while the build and fix
# work that can START is below this — the graph is starving concurrency and a brief is what widens it — and detained
# once there is already as much independent work as there are slots to take it (the owner, 2026-09-20).
GRAPH_DEPTH = int(os.environ.get("ORCH_GRAPH_DEPTH", 10))  # the longest chain of open tasks past which a brief may add
# only at the START of the scheduling chain. Taken once, when the brief starts: a brief that begins under the limit
# adds what its work needs, without limit, rather than being halted half-drawn. One begun above it may still add work
# that runs first — a correction, a prerequisite, anything that widens — and is returned to the planner if it hangs
# more work off the end instead. The planner itself is informed and never refused: a graph it has understood to be
# wrong is its to fix (the owner, 2026-09-20).
WORKERS_MAX = int(os.environ.get("ORCH_WORKERS", 2))  # sessions working at once, over the producing, supporting
# and consultation slots: the owner's choice of 2026-09-20. At 1 a finished task waited to be reviewed and a question
# to the knowledge base waited for a gap in production, which is where the serialization actually hurt. It is not what
# limits production: `produce` takes one producing session whatever this says, and past two the machine's two Isabelle
# runs bind (three reached 59 of 60 GiB). The default is written here so that it holds whatever environment starts the
# daemon.
PLANNER_LOG = "PLANNING_LOG.md"  # what was done and how: the planner's log, appended as work lands. No base holds
# it and nothing reads it to plan from, so it may grow; HANDOFF.md stays the state because the log has somewhere else
# to be (the owner, 2026-09-20).
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
# How often a failure that would repeat on every call is said: the guard's, and a task file that cannot be read.
GUARD_QUIET = int(os.environ.get("ORCH_GUARD_QUIET", 600))
WARM_MAX = int(os.environ.get("ORCH_WARM_MAX", 3300))
PING_AGE = int(os.environ.get("ORCH_PING_AGE", 2700))
HOLD_PARK = int(os.environ.get("ORCH_HOLD_PARK", 3 * 3600))  # the owner's choice: a waiting implementer, 3 hours
HOLD_MAX = int(os.environ.get("ORCH_HOLD_MAX", 3 * 3600))  # an author held for consultation, at most
# Nothing between an event and the planner: no gap, no batch. 23 of the 48 sessions of 2026-09-20 were planning
# episodes, each a fork of the knowledge base at about 510K, because an episode was a session; one planner that lives
# across its events costs one such fork for all of them, and reads each as it stands (the owner, 2026-09-20).
KB_MARGIN = 50_000  # a fresh knowledge base loading within this of its limit asks for condensing and a base rebuild
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


def kept_json(path, what):
    """A JSON file the harness keeps, or {} when there is none. A file that IS there and cannot be read is never read
    as an empty one: every caller here writes what it read back, so emptiness would go over the truth — the state's
    sessions, tasks and queue, or the working tree's ownership. The dispatch logs the failure and moves on, the
    hooks fail open, and nothing overwrites a file nobody has understood (2026-09-21)."""
    try:
        return json.load(open(path))
    except FileNotFoundError:
        return {}
    except (OSError, ValueError) as e:
        raise RuntimeError(f"{what} ({path}) is there and cannot be read: {e!r}. Nothing writes over it; move it "
                           "aside only when you know what it should hold.") from e


@contextlib.contextmanager
def state():
    """The orchestration's state, read and written under one lock."""
    os.makedirs(STATE, exist_ok=True)
    with open(os.path.join(STATE, "v2.lock"), "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        path = os.path.join(STATE, "v2.json")
        st = kept_json(path, "the orchestration's state")
        for key, empty in DEFAULTS.items():
            st.setdefault(key, json.loads(json.dumps(empty)))
        yield st
        tmp = path + ".tmp"
        json.dump(st, open(tmp, "w"), indent=1)
        os.replace(tmp, path)


def peek():
    """The state without taking the lock (hooks read it on every tool call)."""
    st = kept_json(os.path.join(STATE, "v2.json"), "the orchestration's state")
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


def event(st, sender, text, kind=None):
    """Something for the planner. `kind` names a class of event that can go stale, so that one whose subject has
    since changed is not carried to the next planner as though it were still true (see fresh_sweep)."""
    st["events"].append({"at": time.strftime("%Y-%m-%dT%H:%M:%S"), "from": sender, "text": text,
                         **({"kind": kind} if kind else {})})


def fresh_sweep(w):
    """Events a fresh start supersedes, dropped before its charge is added.

    An event nobody handled is carried for ever, and two classes of it become false while they wait. A tree-trouble
    notice states what a tree was when it was written: on 2026-09-20 two of them said "the working tree is
    inconsistent … every task's check refuses on this" of a tree that was consistent, and they were still being
    delivered to a new planner three hours and two runs later. And a fresh charge is about the run that issued it,
    so the one a lost planner never handled is not a charge for this run — plan-31 was given two, for two different
    runs, in one message. Nothing else is touched: what the planner has not handled it still needs."""
    kept, dropped = [], []
    for e in w["events"]:
        if e.get("kind") == "fresh-charge":
            dropped.append(e)
        elif e.get("kind") == "tree-trouble" and not tree_trouble(e.get("tree")):
            dropped.append(e)
        else:
            kept.append(e)
    w["events"] = kept
    if dropped:
        log(f"a fresh start supersedes {len(dropped)} unhandled event(s): "
            + ", ".join(sorted({e.get("kind") for e in dropped})))
    return dropped


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
        s = None
        try:
            s = open(LEDGER).read()
        except FileNotFoundError:
            s = "# Owner ledger\n\n## Owner directions\n\n## Open questions to the owner\n"
        except OSError as e:
            # a ledger that is there and cannot be read was replaced by a fresh header and this one entry: every
            # direction the owner had ever given, gone, under the lock that was meant to protect them. The words are
            # kept in the log instead and the file is left alone (2026-09-21).
            log(f"ATTENTION the owner ledger could not be read ({e!r}) and is left untouched. What was said, in "
                f"full:\n{entry}")
        if s is not None:
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


def unread(name):
    """The unread messages for a session, the mailbox emptied; [] when there are none."""
    try:
        with open(mailbox(name), "r+") as f:
            fcntl.flock(f, fcntl.LOCK_EX)
            lines = [json.loads(line) for line in f if line.strip()]
            f.seek(0)
            f.truncate()
    except (OSError, ValueError):
        return []
    return lines


def mail_text(messages):
    return "\n\n".join(f"Message from {m['from']} ({m['at']}):\n{m['text']}" for m in messages)


def take_mail(name):
    """The unread messages for a session, as one text, and the mailbox emptied; "" when there are none."""
    return mail_text(unread(name))


def keep_mail(name, messages):
    """Put messages back, each with its own sender, before whatever arrived meanwhile. A resume that failed read none
    of them, and they used to go back as one message from the harness with their senders buried inside it: the next
    read then said the harness had said what a reviewer or the planner had."""
    if not messages:
        return
    os.makedirs(os.path.join(STATE, "mail"), exist_ok=True)
    with open(mailbox(name), "a+") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        f.seek(0)
        rest = [l for l in f.read().splitlines() if l.strip()]
        f.seek(0)
        f.truncate()
        f.write("".join(json.dumps(m) + "\n" for m in messages) + "".join(l + "\n" for l in rest))


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
    if s.get("state") not in ("working", "waiting", "idle"):
        return
    hand_mail(name)


def hand_mail(name):
    """Give a session what is in its box, if it can take it now. A busy one reads it through its hooks at its next
    tool call; a resume that fails puts every message back with its own sender. deliver() and wake_planner() both
    ended in these six lines, written out twice and free to be repaired in one of the two."""
    r = row(name)
    if r and (r["activity"] == "busy" or running_jobs(name)):
        return
    messages = unread(name)
    if messages and not resume(name, mail_text(messages)):
        keep_mail(name, messages)


# ---------------------------------------------------------------- sessions

NO_LAUNCH = "no-launch"  # while state/no-launch exists nothing starts a session: not the dispatch, not a base
# build, not a layer refresh. A keep-warm ping does go through (claude(warm_ping=True), and base.sh WHO warm is not
# among the commands it holds): it keeps alive what already exists rather than spending anything, and holding it
# would let the bases go cold, which is the very cost this guards against. Stopping, removing and listing still
# work. It is the owner's switch for the time between "the machinery is ready" and "begin", and it exists because
# starting a session by accident costs a cold write of a whole base (2026-09-20).


GRAPH_HELD = "graph-held"  # while state/graph-held exists no task session starts: the graph is the old run's and
# the planner has not yet said what of it still stands. The planner, the knowledge base and consultations of it are
# not held — taking stock is exactly what the hold is for — and the planner's own order (v2.py queue) lifts it.


def why_held(path, name):
    """The reason in a hold's file, or "" when there is no such file. A hold is a switch that must fail closed: the
    file being there is what holds, and reading it is only how the reason is told. Both read any failure as "no such
    file" and so as "nothing is held", which would have let the owner's own switch open under a permission or an I/O
    error (2026-09-21)."""
    if not os.path.exists(path):
        return ""
    try:
        return open(path).read().strip() or f"state/{name} is set"
    except OSError as e:
        return f"state/{name} is set and its reason could not be read ({e!r})"


def graph_held():
    """The reason no task of the graph may start, or ""."""
    return why_held(os.path.join(STATE, GRAPH_HELD), GRAPH_HELD)


def held_back():
    """The reason nothing may start, or ""."""
    return why_held(os.path.join(STATE, NO_LAUNCH), NO_LAUNCH)


def claude(*args, cwd=None, warm_ping=False):
    """The CLI, bounded: it starts and stops background sessions, and a call that never returns would hold the
    watchdog — and with it the dispatch and the pings — for ever. It starts no work while the hold is on, and none
    while the run is stopped; a keep-warm ping is not work — it keeps what exists alive rather than spending
    anything — and goes through both.

    The dispatch reads state/stopped and does nothing, but `v2.py talk` does not go through the dispatch: run while
    everything was stopped it would have forked the knowledge base for a planner, which is the run beginning again
    by another door (2026-09-21). start.sh takes the marker off before it starts anything."""
    stopped = os.path.exists(os.path.join(STATE, "stopped")) and "the run is stopped (state/stopped); start.sh resumes it"
    why = held_back() or stopped
    if "--bg" in args and not warm_ping and why:
        log(f"a session was not started: {why}")
        return subprocess.CompletedProcess(args, 1, "", f"held back: {why}")
    env = {k: v for k, v in os.environ.items() if k not in INHERITED}
    try:
        return subprocess.run(["claude", *args], capture_output=True, text=True, cwd=cwd or PROJECT, env=env,
                              timeout=CLAUDE_MAX)
    except subprocess.TimeoutExpired:
        log(f"ATTENTION `claude {' '.join(str(a) for a in args[:2])}` did not return within {CLAUDE_MAX}s")
        return subprocess.CompletedProcess(args, 124, "", "timed out")


def row(name):
    out = subprocess.run([os.path.join(HERE, "session_row.py"), name], capture_output=True, text=True).stdout.split()
    return dict(zip(("kind", "id", "activity", "sid", "state"), out)) if len(out) >= 4 else None


def layer_record(who):
    """The recorded frontier layer of a base, or None. A layer whose stable base has been rebuilt under it is an
    orphan: it is a fork of a session that is gone, so nothing may fork it and it is not one."""
    try:
        layer = json.load(open(os.path.join(STATE, f"{who}-layer.json")))
        base = json.load(open(os.path.join(STATE, f"{who}-base.json")))
    except (OSError, ValueError):
        return None
    return layer if layer.get("base") == base.get("sessionId") else None


def base_file(who):
    """What a role of this base forks: its frontier layer when one is recorded, the stable base otherwise. A fork of
    the layer reads the whole prefix under it, the stable base included, from cache — measured on 2026-09-20: a fork
    of the sealed knowledge base (a layer over `max` in all but name) read 538,051 of its 538,044 tokens and wrote 62
    — so the layer is what everything forks and what is pinged."""
    if layer_record(who):
        return os.path.join(STATE, f"{who}-layer.json")
    return os.path.join(STATE, f"{who}-base.json")


def base_record(who):
    """(name, record) of a sealed base or its layer, falling back to the present base while the base topic has not
    built it."""
    for name in (who,) + FALLBACK.get(who, ()):
        try:
            b = json.load(open(base_file(name)))
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
    """A session's request reads its own prefix, and so its origin's: each is hit, down to the base. A session that
    forked the layer standing before a refresh reads that one, not the one that replaced it, so it marks nothing for
    the base: otherwise the new layer would look warm while nothing had read it, and the first fork of it would pay a
    cold write of its whole size."""
    seen = set()
    while name and name not in seen:
        seen.add(name)
        rec = peek()["sessions"].get(name) or {}
        origin = rec.get("origin")
        if name in BASES or origin in BASES:
            who = name if name in BASES else origin
            current = (base_record(who)[1] or {}).get("sid")
            if name not in BASES and rec.get("origin_sid") and rec["origin_sid"] != current:
                hit(name)  # its own entry, and nothing of the base: what it reads is no longer what is forked
                return
        hit(name)
        name = None if name in BASES else origin


def hit_age(name):
    path = os.path.join(STATE, f"{name}-base.hit") if name in BASES else hits(name)
    try:
        return time.time() - os.path.getmtime(path)
    except OSError:
        return float("inf")


def warm(name):
    return hit_age(name) < WARM_MAX


def stale(who, tree=None, since=None):
    """The line naming the held files of that base that changed since it was loaded (manifest.py), in the tree the
    session works in — a task with a tree of its own is told what changed in its own. `since` is the session the
    reader actually forked: after a layer refresh that is not the layer standing now, and measuring against the
    wrong load would leave out the files that moved before it, which are the frontier theories being worked on."""
    env = dict(os.environ, ORCH_TREE=tree) if tree else dict(os.environ)
    env.pop("ORCH_LOAD_LIST", None)  # this base names its own list; an inherited one would answer about another
    args = ["changed", who] + (["--since-layer", since] if since else [])
    out = subprocess.run([os.path.join(HERE, "manifest.py"), *args], capture_output=True, text=True, env=env).stdout
    return out.strip() or "no held file has changed since the load"


def stale_of(name, who, tree=None):
    """What has changed since the load this session actually holds — measured against the layer it forked, not the
    one standing now."""
    return stale(who, tree, (peek()["sessions"].get(name) or {}).get("origin_sid"))


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
    # A start that is not confirmed is tried again at the next dispatch, which is every minute: on 2026-09-20 two
    # sessions were started and invisible, and the harness would have started a replacement for each over and over.
    # produce() holds the producing slot to RETRY that way and says so to the planner; every other role — the
    # planner itself, the knowledge base, a review, a brief, a consultation — had nothing, and each of those starts
    # is a fork of a loaded base. The floor is here, where every one of them passes (2026-09-21).
    # by what is being started, not by what it would be called: the planner's and the knowledge base's key is a
    # counter that rises with every attempt, so keying on it would make every retry a new thing and no backoff
    mark = f"start-failed-{role}-{key if role not in ('planner', 'kb') else 'one'}"
    age = age_of(mark)
    if age is not None and age < RETRY:
        return None
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
        st["sessions"][name] = dict(name=name, role=role, origin=who, origin_sid=org["sid"], model=org["model"],
                                    effort=org["effort"], settings=settings, state="starting", starting=time.time(),
                                    **fields)
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
            if not held_back() and not os.path.exists(os.path.join(STATE, "stopped")):
                open(os.path.join(STATE, mark), "w").write(str(time.time()))  # not the hold's doing: back off
            return None
        s.update(sid=r["sid"], id=r["id"], state="working", started=time.time())
    hit(name)
    with contextlib.suppress(OSError):
        os.remove(os.path.join(STATE, mark))
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
            if st["sessions"][name]["state"] in ("done", "parked", "waiting", "idle"):
                st["sessions"][name]["state"] = "working"
        log(f"{name} has running jobs: its message waits as mail")
        return True
    if r:
        claude("stop", r["id"])
        time.sleep(PAUSE)
    started = claude("--bg", "--resume", s["sid"], HARNESS + text, cwd=tree_of(s))
    if started.returncode != 0:
        # Said, not assumed: every caller reads this to decide whether the message it carried still has to be kept
        # (the mail is taken out of the box before the resume), and a session reported resumed that never ran holds
        # its state as working while nothing does it.
        log(f"ATTENTION {name} was not resumed ({(started.stderr or started.stdout).strip()[:120]}): "
            f"{text.split(chr(10), 1)[0][:80]}")
        return False
    with open(os.path.join(STATE, f"{name}.woken"), "a") as f:
        f.write(time.strftime("%Y-%m-%dT%H:%M:%S ") + text.split("\n", 1)[0][:100] + "\n")
    with state() as st:
        rec = st["sessions"][name]
        rec["sealed"] = False
        if rec["state"] in ("done", "parked", "waiting", "idle"):
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
    except (KeyError, FileNotFoundError):
        return []      # it never started, or has written nothing yet: either way it has started no job
    except OSError as e:
        # [] is "no job of its own runs", and the harness seals or resumes a session on that, which kills whatever
        # it started. Nothing said so when the transcript could not be read at all (2026-09-21).
        say_once(f"jobs-unreadable-{name}", f"ATTENTION the transcript of {name} could not be read ({e!r}); its "
                 "background jobs read as none, and sealing or resuming it would kill any that run")
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
    """A session nothing refers to any more: stopped, its listing removed, its guard state forgotten.

    What is still in its box was written to a session that was alive and was never read: a resume that failed puts
    the messages back (hand_mail), and from then on nothing tries again. Eight boxes stood that way on 2026-09-20,
    two of them the planner's corrections to fix-48 about the order of the working tree, and nothing said so to
    anybody. deliver() already names mail that arrives after the end; this names mail the end arrives after."""
    s = peek()["sessions"].get(name) or {}
    left = unread(name)
    if left:
        senders = ", ".join(dict.fromkeys(m["from"] for m in left))
        log(f"ATTENTION {len(left)} message(s) to {name} from {senders} were never read: it is released")
        with state() as w:
            event(w, "the harness", f"{len(left)} message(s) to {name} ({s.get('role')}"
                  + (f" on task {s['task']}" if s.get("task") else "") + f") were never read: from {senders}, and the "
                  "session is released. A resume that fails puts mail back in the box and nothing tries again. If "
                  "what they say still bears on the work, put it where the next session on it will read it — its "
                  "brief, or `v2.py tell`:\n\n" + mail_text(left)[:1500])
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
    if out:  # every action of the harness is a line in the log, and this one takes things out of the state
        log(f"archived {len(out)} piece(s) of state a day old that nothing refers to: "
            + ", ".join(sorted(x["session"]["name"] if "session" in x else x["ask"]["qid"] for x in out)[:8]))
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
    """The sessions doing work now, over every slot: producing, supporting, a quick fix and the consultations. Neither
    the knowledge base nor the planner is one of them — they are the deliberative half, one session each, and gating
    them behind the rate would make the planner answer an event only when a producer happened to stop (the owner,
    2026-09-20: the planner works problem by problem and stays responsive). A parked session is not working either."""
    return [n for n, s in st["sessions"].items()
            if s.get("state") in LIVE and s.get("role") not in ("kb", "planner") and not s.get("released")]


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

EXEMPT = (".build/", ".claude/", "HANDOFF.md", PLANNER_LOG)  # never an owned change: drafts, the harness's files,
# the planner's state and the planner's log


def exempt(path):
    return path.startswith(EXEMPT) or "__pycache__/" in path or path.endswith(".pyc")


def git_out(*args, binary=False, tree=None, quiet=False):
    """Git's output, or None when it failed. A failure is said unless the caller reads it as an answer (`quiet`):
    changed_paths turns None into "no paths", which reads as a clean tree, and from there tree_writer finds no
    owner and leave() tells a task nothing about the work it is leaving. A wrong answer nobody records is the
    shape that cost this run its day."""
    r = subprocess.run(["git", "-C", tree or PROJECT, *args], capture_output=True, text=not binary)
    if r.returncode and not quiet:
        err = (r.stderr if isinstance(r.stderr, str) else r.stderr.decode(errors="ignore")).strip()[-160:]
        log(f"ATTENTION git {' '.join(str(a) for a in args[:3])} failed in {tree or PROJECT}: {err}")
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
def owners(write=True):
    """{path: task} of the changes in the working tree, under a lock; written back unless `write` is False.

    Every reader rewrote it: six of the seven callers only look, and the write guard reaches tree_writer on every
    Write and Edit a session makes, so each of those took an exclusive lock and rewrote the file to change nothing
    — 21 ms a call, and two sessions looking at once serialized on it."""
    os.makedirs(STATE, exist_ok=True)
    path = os.path.join(STATE, "tree-owners.json")
    with open(path + ".lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX if write else fcntl.LOCK_SH)
        data = kept_json(path, "the working tree's ownership")
        yield data
        if write:
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
    mine_apart = TREES and (rec or {}).get("task") and worktree_of((rec or {}).get("task")) != PROJECT
    return next((tid for tid, t in st["tasks"].items() if t.get("stage") in FINISHING and tid not in own
                 and os.path.exists(os.path.join(BUILD, tid, "finalize.json"))
                 and not (mine_apart and worktree_of(tid) != PROJECT)), None)  # each in its own tree: no waiting


def check_isolation():
    """A check sees the working tree: while one runs, no other session writes it. A task whose session still works is
    parked — its work stays where it is — and resumed when the check's task has landed."""
    st = peek()
    checking = next((tid for tid, t in st["tasks"].items() if t.get("stage") == "checking"), None)
    if not checking:
        return
    with owners(write=False) as o:
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
            deliver(name, "the harness", f"Task {checking}'s check is running and sees the working tree, so your task "
                    f"is parked and writes nothing meanwhile.{aside} End your turn; you are resumed, your context "
                    "intact, when the check's task has landed and the producing slot is free.")
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
    except FileNotFoundError:
        return []  # no ROOT or no theories/: not a tree these terms are about, and nothing to say of it
    except OSError as e:
        # anything else — a permission, an I/O error — is not "this tree is fine", which is what [] is read as
        log(f"ATTENTION the tree at {tree} could not be read, so nothing is said of it: {e!r}")
        return []
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


def base_lineage():
    """Every directory the accepted base stands on, the base itself first. Nothing may remove one of these: they are
    what a check reuses, and a check whose parent is gone rebuilds from nothing."""
    out, cur = [], None
    try:
        cur = json.load(open(ACTIVE_CONTEXT))["directory"]
    except (OSError, ValueError, KeyError):
        return out
    while cur and os.path.exists(os.path.join(cur, "accepted-context.json")) and cur not in out:
        out.append(cur)
        cur = json.load(open(os.path.join(cur, "accepted-context.json"))).get("parent")
    return out


def base_at_risk():
    """Whether the accepted base stands inside a task's own directory — where the task that owns it, a re-plan or a
    sweep of run output would take it away with everything that chains from it. Found on 2026-09-20: the base stood
    in .build/tasks/7/check2/proof, because an advancing check was run with its output there."""
    lineage = base_lineage()
    at = BUILD.rstrip(os.sep) + os.sep  # BUILD is already .build/tasks
    return [p for p in lineage if p.startswith(at)]


def base_would_stand_in_a_task(check):
    """The paths of a task's own directory that a base-advancing check names. Such a check writes the whole
    repository's base, and everything checked after it chains from it: under `.build/tasks/{ID}/` the base goes with
    that task when it is dropped, re-planned or its run output swept. Found on 2026-09-20, when task 7's final check
    left the base standing in .build/tasks/7/check2/proof (`base_at_risk`); the rule is in protocols/_production.md."""
    if not ADVANCES.search(check):
        return []
    try:
        words = shlex.split(check)
    except ValueError:
        words = check.split()
    root = BUILD.rstrip(os.sep) + os.sep
    named = []
    for word in words:
        path = word.split("=", 1)[-1]
        if not path or path.startswith("-"):
            continue
        full = os.path.normpath(path if os.path.isabs(path) else os.path.join(PROJECT, path))
        if (full + os.sep).startswith(root):
            named.append(word)
    return named


BASE_IN_A_TASK = (
    "a check that advances the base writes the whole repository's base, and every check after it chains from it. "
    "Under a task's own directory it goes with that task when the task is dropped, re-planned or its run output "
    "swept: {named}. Give it an --output under .build/ directly (.build/check-<date><letter>), as the repository's "
    "own checks do.")


def tree_checked(who, what, tree=None):
    """Say at once when a tree has been left in a state its checks refuse, naming which tree and what did it.

    Until 2026-09-20 this said "the working tree" whatever tree it had been given, and added that every task's check
    refuses on it — true of the shared tree, false of a task's own worktree, which nothing but that task checks. The
    planner was told twice, at 20:24 and 20:25, that the working tree was inconsistent because ROOT declared
    Development_Loci with no file; the shared tree had the file and was consistent throughout, and the trouble was
    task 46's worktree alone, branched from a HEAD that declares a theory whose file is untracked. The same trouble
    is not repeated for the same tree within TREE_TOLD."""
    trouble = tree_trouble(tree)
    if not trouble:
        return trouble
    own = os.path.relpath(tree, PROJECT) if tree and os.path.realpath(tree) != os.path.realpath(PROJECT) else ""
    whose = f"the working tree of task {os.path.basename(own)} ({own})" if own else "the working tree"
    reach = (". Its own checks refuse on this until it is put right; the shared working tree is not affected."
             if own else
             ". Every task's check refuses on this, not only the one whose change caused it, so nothing can "
             "be checked until it is put right.")
    log(f"ATTENTION {whose} is inconsistent after {what} ({who}): " + "; ".join(trouble[:4]))
    mark, said = "tree-told-" + re.sub(r"\W+", "-", own or "main"), "; ".join(trouble)
    told = age_of(mark)  # not `or TREE_TOLD + 1`: an age of 0.0 is falsy and would read as never told
    if told is None or told > TREE_TOLD or _read(mark, STATE) != said:
        open(os.path.join(STATE, mark), "w").write(said)
        with state() as st:
            e = {"kind": "tree-trouble", "tree": tree}
            st["events"].append({"at": time.strftime("%Y-%m-%dT%H:%M:%S"), "from": "the harness", **e,
                                 "text": f"{whose[0].upper()}{whose[1:]} is inconsistent after {what}: "
                                         + "; ".join(trouble) + reach})
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
    with owners(write=False) as o:
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
    """A task of the graph, or None when it is not in the list.

    None is read everywhere as "the planner took it out": startable skips it, with_the_planner leaves it alone and
    reconcile_stages names it to the planner as a conflict. So a file that is there and cannot be read must not
    come back as one that is not there — it is tried again, and said, rather than turned into a statement about
    the graph that is false (2026-09-21)."""
    for _ in range(3):  # a read can meet a write in progress
        try:
            return json.load(open(task_path(tid)))
        except (ValueError, OSError) as e:
            if isinstance(e, OSError) and not os.path.exists(task_path(tid)):
                return None
            trouble = e
            time.sleep(0.05)
    say_once("task-unreadable",
             f"ATTENTION task {tid} is in the list and could not be read ({trouble!r}); it reads as not being there")
    return None


def in_list(tid):
    """Whether the task's file is there at all. read_task returns None for a file that cannot be read as well as for
    one that is not there, and every statement of the form "task N is not in the list" is about the second: an I/O
    fault is not the planner having taken a task out, and saying so would put a false statement of the graph in
    front of the planner, or refuse a proposal for it (2026-09-21)."""
    return os.path.exists(task_path(tid))


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
    done = True
    for d in t.get("blockedBy") or []:
        blocker = read_task(d)
        if blocker is None:  # dropped, or never written: nothing will ever complete it
            done = False
            if not in_list(d):  # and not merely a file that could not be read, which read_task has said
                if (age_of(f"blocker-{tid}-{d}") or LOST_BLOCKER + 1) > LOST_BLOCKER:
                    open(os.path.join(STATE, f"blocker-{tid}-{d}"), "w").write(str(time.time()))
                    with state() as st:
                        event(st, "the harness", f"Task {tid} waits for task {d}, which is not in the task list — "
                              f"dropped, or never written. Nothing will complete it, so {tid} waits for ever: set "
                              f"what it waits on (`v2.py blockers {tid} ...`, or `none`), or drop it too.")
                    log(f"task {tid} waits for task {d}, which is not in the task list")
        elif blocker.get("status") != "completed":
            done = False
            # A task dropped or given back stays pending in the list, so a dependent waits on it with nothing to
            # complete it and nothing saying so — the same shape as a blocker that is not there at all, which was
            # named on 2026-09-20 while this was not.
            if (peek()["tasks"].get(d) or {}).get("stage") == "planner" \
                    and (age_of(f"blocker-{tid}-{d}") or LOST_BLOCKER + 1) > LOST_BLOCKER:
                open(os.path.join(STATE, f"blocker-{tid}-{d}"), "w").write(str(time.time()))
                with state() as st:
                    event(st, "the harness", f"Task {tid} waits for task {d}, which came back to you and has not been "
                          f"re-planned: nothing will complete it as it stands, so {tid} waits. Re-plan {d}, or set "
                          f"what {tid} waits on (`v2.py blockers {tid} ...`, or `none`).")
                log(f"task {tid} waits for task {d}, which is with the planner")
    return done


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
        context = json.load(open(base_file(who)))["context"]  # a layer's context is the whole of it, its base included
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
        # It proposes and no longer edits the graph, so TaskCreate and TaskUpdate are not its production — they are
        # refused to it. Its proposal and its drafts under brief/ are, which is why the protocol names the proposal's
        # path inside that directory: otherwise the one thing it produces would not count and its reads would be cut
        # off after three requests with nothing able to restart the count (2026-09-20).
        return {"deliverables": [f".build/tasks/{tid}/brief/proposal.json"],
                "drafts": f".build/tasks/{tid}/brief/", "task_tools": False}
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
                  BRIEF_BACKLOG=str(BRIEF_BACKLOG), GRAPH_DEPTH=str(GRAPH_DEPTH),
                  WIDTH=str(graph_figures()[0]), DEPTH=str(graph_figures()[1]),
                  SLOTS=str(GRAPH_WIDTH or WORKERS_MAX),
                  FIX_ROUNDS=str(FIX_ROUNDS), HOLD_HOURS=str(HOLD_PARK // 3600), ROOM_DESIGN=str(room_of("design") // 1000),
                  # a number a protocol states in prose is one the harness can change under it: these are its own
                  CONSULT_HOURS=str(HOLD_MAX // 3600), ISABELLE_MAX=str(ISABELLE_MAX),
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


HANDOFF_MAX = int(os.environ.get("ORCH_HANDOFF_MAX", 60_000))  # tokens. A state may hold a great deal — the knowledge
# base carries it beside a 472K base and stays far inside its limit, and a designer reads it whole in a gather, which
# is free of the read limits. This is not a budget but the point past which it is a log and not a state, and the log
# has its own file. Measured 2026-09-20: 6.5K chars after the v1 reset, 81K twelve hours later, with two
# condensations of 2.6K against 80K added — nothing measured it, so nothing pushed the other way.


def handoff_size():
    """(tokens, the section that is largest, its tokens) of HANDOFF.md as it stands."""
    path = os.path.join(PROJECT, "HANDOFF.md")
    try:
        text = open(path, errors="ignore").read()
    except OSError:
        return 0, "", 0
    parts = sorted(((part(text, s) or "", s) for s in PLANNER_SECTIONS), key=lambda x: -len(x[0]))
    return len(text) // 3, parts[0][1], len(parts[0][0]) // 3


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
    with owners(write=False) as o:
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
        return render("kb", NAME=name, STALE=stale_of(name, base_record("max")[0] or "max"))
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
        if s.get("sid") and not integrated(s, s.get("started", 0)) \
                and time.time() - (s.get("started") or time.time()) > KB_BUILD_MAX:
            # the same shape as the integration: a build that never replies holds every episode behind it, because
            # no second build starts while one is recorded (2026-09-20)
            log(f"ATTENTION the knowledge base {building} has been loading for "
                f"{int(time.time() - s['started']) // 60} minutes and has not replied; it is given up")
            with state() as w:
                w["sessions"][building]["state"] = "lost"
                w["kb_building"] = None
                event(w, "the harness", f"The knowledge base {building} did not finish loading within "
                      f"{KB_BUILD_MAX // 60} minutes and is given up; another is built in its place.")
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
        waited = time.time() - (rec.get("integrating_since") or time.time())
        if not integrated(rec, rec.get("integrating_since", 0)) and waited > KB_INTEGRATE_MAX:
            # nothing else bounded this: a knowledge base that never says INTEGRATED stays integrating, and while it
            # does no planning episode and no consultation can fork it — the deliberative half stops for good, and
            # nothing says so (2026-09-20, found before it happened)
            log(f"ATTENTION {kb} has been integrating for {int(waited) // 60} minutes and has not replied; its notes "
                f"are in state/{kb}-notes.md and a new knowledge base is built from HANDOFF.md")
            with state() as w:
                w["sessions"][kb]["state"] = "lost"
                event(w, "the harness", f"The knowledge base {kb} did not finish integrating within "
                      f"{KB_INTEGRATE_MAX // 60} minutes. Its notes stand in state/{kb}-notes.md; a new one is built "
                      "from HANDOFF.md, so anything those notes hold that HANDOFF.md does not is lost to it.")
            kb_build()
            return
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
            t["stage"] = "done"  # the narrow half of the rule reconcile_stages holds in general: this one runs
            # inside produce()'s own walk of the queue, so a queued task is never dispatched after the planner has
            # completed it, whatever the stage said. reconcile_stages covers the tasks this never reaches — the
            # unqueued, and the ones already running — and neither is the sole guard.
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
    tree = os.path.join(PROJECT, TREE_DIR, tid) if TREES and not in_main_tree(tid) else None
    name = launch(role, tid, lambda name: render(role, NAME=name, ID=tid, KIND=kind, SUBJECT=task.get("subject", ""),
                                                 BRIEF=brief.strip(), STALE=stale_of(name, base, tree), WHAT=PLANNED_FIX,
                                                 TREE=tree_text(tid, tree)), task=tid)
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


# A worktree per producing task is OFF until the harness can see a session that works in one. A session started with
# its cwd in a worktree is listed under that cwd and its transcript lands in a project directory of its own, so
# session_row.py does not find it and v2.TRANSCRIPTS does not hold it: on 2026-09-20 fix-49 and implement-46.3 both
# started, ran, and were invisible — their starts were called unconfirmed, their records released, and the harness
# would have launched a replacement every ten minutes while they worked on. Everything that reads a transcript
# (running_jobs, context_of, last_reply, the gauge, the meter, session_fork_check) resolves it through PROJECT.
TREES = os.environ.get("ORCH_TREES", "0") == "1"  # ORCH_TREES=1 for a worktree per producing task
TREE_DIR = ".build/trees"


def in_main_tree(tid):
    """Whether this task's work already stands in the one tree. Such a task keeps working there: a tree of its own
    would be a checkout of HEAD without what it has installed, and carrying the work over would be the harness moving
    a change again. A task that starts fresh gets its own tree."""
    with owners(write=False) as o:
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
    """The task's own working tree if it has one and trees are on, else the one tree.

    It read the directory alone, so a tree left behind by an earlier run captured its task for ever after
    ORCH_TREES was turned off. On 2026-09-20 that put fix-49.2's cwd in `.build/trees/49` — the tree the planner had
    declared discarded — while tree_text, which does consult TREES, told it in the same message that it worked in
    the one tree. A session in a worktree is invisible to the harness (session_row matches by cwd, and the
    transcripts resolve through PROJECT), which is why trees were turned off at all.

    Everything downstream followed it: finalize.py runs the check and makes the commit in this tree, so a task would
    have been checked and committed from a stale branch; and tree_trouble read it, which is where the two notices
    telling the planner that "the working tree is inconsistent" came from — the shared tree was consistent
    throughout and .build/trees/46 was not."""
    if not TREES:
        return PROJECT
    path = os.path.join(PROJECT, TREE_DIR, str(tid))
    return path if os.path.exists(path) else PROJECT


def tree_text(tid, tree=None):
    """Where the session works, said as it is. Until 2026-09-20 every role was told it had a worktree of its own: the
    planner, the task designer, the reviewer and the consultations have none, and a producing task whose work already
    stands in the one tree keeps working there. A session that believes it has a tree it has not writes into a path
    that is not there."""
    # TREES, not the directory alone: a tree left behind by an earlier run would otherwise tell a session it is
    # started in a worktree while worktree_of, which does consult TREES, starts it in the one tree. That is the
    # same fault as worktree_of's, in the other direction, and it is why fix-49.2 was told it had a tree of its own
    # on 2026-09-20 — I reported the opposite at the time, having called this with a record where it wants a task id.
    if tree or (TREES and os.path.isdir(os.path.join(PROJECT, TREE_DIR, str(tid)))):
        return (f"**Your working tree is your task's own.** You are started in it (`{TREE_DIR}/{tid}`, a git worktree "
                f"on the branch `task/{tid}`), it is a whole checkout, and `.build` in it is the one `.build`: your "
                "drafts, the checks' output and their lineage are where they have always been. Install into it, check "
                "in it, and nothing you write there is seen by another task. The finalizer commits on your branch and "
                "brings it into the branch that is pushed, where your lines meet the lines other tasks wrote "
                "meanwhile — cleanly where they stand apart, and with a named conflict where two tasks wrote in the "
                "same place. HANDOFF.md is the planner's in your tree as in any other.")
    return ("**You work in the repository's one working tree**, not a tree of your own: your task's work already "
            "stands there, and another task's uncommitted work may stand beside it. A check reads the whole tree, so "
            "a failure in it may be another task's — say so rather than repairing what is not yours. Install into it, "
            "check in it, and the finalizer commits from it. HANDOFF.md is the planner's here as everywhere.")


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
    changed = set(changed_paths())  # once: inside the comprehension it ran a git subprocess per owned path, and
    with owners(write=False) as o:   # the write guard reaches this on every Write and Edit a session makes
        owned = {p: tid for p, tid in o.items() if p in changed}
    for tid in owned.values():
        if (st["tasks"].get(tid) or {}).get("stage") not in ("done", None) and (read_task(tid) or {}).get(
                "status") != "completed":
            return tid
    return None


def produce():
    """The producing slot: a parked task whose wait is over first (its changes come back into the free working tree),
    then the first ready task in the queue."""
    if graph_held():
        return
    st = peek()
    if slot(st, PRODUCING):
        return
    if at_capacity(st):
        return  # at most WORKERS_MAX sessions work at a time (the owner's rate)
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
            messages = unread(t["session"]) if has_mail(t["session"]) else []
            if not resume(t["session"], text + (f"\n\n{mail_text(messages)}" if messages else "")):
                keep_mail(t["session"], messages)  # kept: a resume that failed read none of it
                with state() as w:
                    w["tasks"][tid]["stage"] = "planner"
                    event(w, "the harness", f"{t['session']}, parked on task {tid}, went cold before its wait was over: "
                          "re-plan the task over what is on disk." + leave(tid, "cold"))
            return
    failed = st.get("start_failed") or {}
    for tid in st["queue"]:
        task = read_task(tid)
        if task is None or task.get("status") == "completed":
            continue  # no record in the list: nothing to brief a session from, and deps_done() reads no blockers off
            # a task that is not there, so it would start for ever. Completed: the planner has said the work is done
            # and the stage is only the harness's own bookkeeping (2026-09-20: tasks 21, 48 and 50).
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
        STALE=stale_of(name, base_record("xhigh")[0] or "max"),
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
        STALE=stale_of(name, base_record("xhigh")[0] or "max")), task=tid)
    depth = graph_shape()[1]  # taken once: a brief that begins under the limit is not halted half-drawn
    with state() as w:
        if name:
            w["tasks"][tid].update(stage="running", session=name, role="task-designer", depth_at_start=depth)
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


def say_once(mark, text, every=None):
    """Log what would otherwise be said on every call — a failure that repeats while its cause stands — at most once
    every GUARD_QUIET. The alternative is a log nobody can read, which is the same as saying nothing."""
    every = GUARD_QUIET if every is None else every
    age = age_of(mark)
    if age is None or age > every:
        with contextlib.suppress(OSError):
            open(os.path.join(STATE, mark), "w").write(str(time.time()))
        log(text)


def startable(st=None):
    """The queued tasks that could start now: ready, and with every blocker completed. It is the width of the graph
    as the planner has drawn it — what a park can hand the producing slot to. Pure: it never says anything to anyone
    (deps_done does, hourly, which is why the status does not use it)."""
    st = st or peek()
    tasks = {t["id"]: t for t in all_tasks()}
    out = []
    for tid in st["queue"]:
        if (st["tasks"].get(tid) or {}).get("stage") != "ready":
            continue
        if tid not in tasks or tasks[tid].get("status") == "completed":
            continue  # deleted from the list while the queue kept it: with no record it has no blockers either, so
            # it read as startable for ever. On 2026-09-20 the planner's first message said "startable now: 21 14"
            # and task 21 had been dropped and was not in the list at all — one of the two was a phantom. And one
            # the planner has completed is not startable either: produce() refuses it, so the report must agree with
            # what the dispatch would do, rather than name it until task_state next heals the stage.
        t = st["tasks"].get(tid) or {}
        if t.get("kind") == "review" and (st["tasks"].get(t.get("reviews") or "") or {}).get("stage") == "done":
            continue  # its subject finished without being reviewed, so pending_reviews will never offer it: naming
            # it here said the graph was wider than anything would take, which is what this figure is read for
        blockers = (tasks.get(tid) or {}).get("blockedBy") or []
        if all((tasks.get(b) or {}).get("status") == "completed" for b in blockers):
            out.append(tid)
    return out


def kind_of(task):
    """A task's kind, from its metadata or its brief."""
    return (task.get("metadata") or {}).get("kind") or field(task.get("description", ""), "Kind")


def graph_shape(kinds=None, skip=()):
    """(width, depth, open) of the task graph as it is drawn, over the tasks that are not completed.

    width  — how many of them have every blocker completed: the work that could run at all, which is what
             concurrency is made of. Not startable(), which also asks whether a task is queued and in form.
    depth  — the longest chain of open tasks: how many turns of the producing slot the last of them waits for.

    The two say what a count of open tasks cannot. On 2026-09-20 the graph held 33 open tasks, 17 of them build or
    fix, and every brief was detained because 17 >= 6 — while its width was 8 and only 5 of those 17 could start at
    all, and its depth was 20, one task wide for 14 of those levels. Counting what exists detains the very work that
    would have widened it; counting what can run says the opposite, and says it for the right reason."""
    tasks = {t["id"]: t for t in all_tasks()}
    # The chain is walked over every open task and only counted over the kinds asked for: a build task waits on the
    # review of the build before it, so filtering the walk by kind cuts the chain at every review and reports a
    # depth of 3 for one that is 20 long.
    every = {k: v for k, v in tasks.items() if v.get("status") != "completed"}
    blocked = {k: [b for b in (v.get("blockedBy") or []) if (tasks.get(b) or {}).get("status") != "completed"]
               for k, v in every.items()}
    open_ = {k: v for k, v in every.items() if kinds is None or kind_of(v) in kinds}
    seen = {}

    def chain(tid, path=()):  # a cycle cannot lengthen a chain, and the graph is not trusted to be free of them
        if tid in seen:
            return seen[tid]
        if tid in path or (tasks.get(tid) or {}).get("status") == "completed":
            return 0
        seen[tid] = 1 + max([chain(b, path + (tid,)) for b in blocked.get(tid, ())], default=0)
        return seen[tid]

    # `skip` leaves a task out of the WIDTH while still walking it for the depth: a task that came back to the
    # planner has every blocker done and so counted as concurrency, though no slot can take it. Two of those would
    # have held the width at the slots for ever and detained every brief, with only the planner able to move them
    # and nothing saying so (2026-09-20).
    return (sum(1 for k in open_ if not blocked[k] and k not in skip),
            max([chain(k) for k in open_], default=0),
            len(open_))


def graph_figures(st=None):
    """(width, depth) as the rule uses them, so the status, the roles' messages and the check cannot differ.

    The width is the build and fix work a slot could take **now**: every blocker done, and no session on it and
    none needed to put it right. A task that came back to the planner, one whose brief is not in form, and one a
    session already has are all counted out — none of the three is work a slot can take. Counting work in flight
    told the planner "1 build and fix tasks can start" of task 52, whose brief is not in form and which nothing can
    start at all, and made the rule it is given — "a brief is admitted again when the slots have taken what can
    start" — one nothing could satisfy: the figure only fell when the work finished (2026-09-21).

    The depth is the WHOLE graph's longest chain, because that is what start_brief records and what cmd_propose
    compares against GRAPH_DEPTH: showing the build-and-fix depth instead said 10 to the planner while the rule was
    applying 11, and the task designer was told a width of 2 against the status's 1 (2026-09-21)."""
    st = st or peek()
    taken = {tid for tid, t in st["tasks"].items() if (t or {}).get("stage") not in ("ready", None)}
    return graph_shape(("build", "fix"), skip=taken)[0], graph_shape()[1]


def build_backlog(st=None):
    """The build and fix tasks that are not completed: what the one producing slot has still to do."""
    return [x["id"] for x in all_tasks() if x.get("status") != "completed"
            and ((x.get("metadata") or {}).get("kind") or field(x.get("description", ""), "Kind")) in ("build", "fix")]


def support():
    """The one supporting slot: a review task of a finished build or fix, or a brief task; the brief first when nothing
    is ready for the producing slot."""
    if graph_held():
        return
    st = peek()
    if slot(st, SUPPORTING):
        return
    if at_capacity(st):
        return  # at most WORKERS_MAX sessions work at a time (the owner's rate)
    reviews = pending_reviews(st)
    briefs, ready = [], False
    for tid in st["queue"]:
        with state() as w:
            t = dict(task_state(w, tid))
        live = (read_task(tid) or {}).get("status") not in (None, "completed")  # the list, not the stage, says
        if live and t.get("stage") == "ready" and t.get("kind") == "brief" and deps_done(tid):
            briefs.append(tid)
        ready = ready or (live and t.get("stage") == "ready" and t.get("kind") in PRODUCING_KINDS and deps_done(tid))
    backlog = build_backlog()
    width, depth = graph_figures(st)
    room = GRAPH_WIDTH or WORKERS_MAX
    why = (f"{width} build and fix tasks can start and there are {room} slots to take them" if width >= room else
           f"{len(backlog)} build and fix tasks are open, past the ceiling of {BRIEF_BACKLOG}"
           if BRIEF_BACKLOG and len(backlog) >= BRIEF_BACKLOG else "")
    if briefs and why:
        if age_of("brief-held") is None or age_of("brief-held") > 900:
            open(os.path.join(STATE, "brief-held"), "w").write(str(time.time()))
            log(f"no brief is detailed while {why}: {', '.join(briefs)} wait")
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
    if graph_held():
        return
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
                STALE=stale_of(name, base_record("high")[0] or "max"), TREE=tree_text(tid)), task=tid, fix={"since": time.time()})
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
        return  # at most WORKERS_MAX sessions work at a time (the owner's rate); a question waits for the gap
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
            STALE=stale_of(name, consulted_base(origin))),
            origin=origin, qid=qid)
        with state() as w:
            w["asks"][qid].update(state="open", session=name) if name else None
        live += bool(name)


def planner_live(st):
    """The planner that is alive: starting, working on what it has been given, waiting on an answer, or between events
    and still warm. One that has written its notes and ended, or that was lost, is not."""
    for name, s in st["sessions"].items():
        if s.get("role") != "planner" or s.get("released"):
            continue
        if s.get("state") in LIVE:
            return name
        if s.get("state") == "idle" and warm(name):
            return name
    return None


def wake_planner(name):
    """Give the planner what has arrived. A turn that is running reads it through its hooks at its next tool call;
    one between events is resumed with it at once."""
    hand_mail(name)


def plan():
    """The planner. One session lives across many events and ends only when its window forces it to (then its notes,
    what it has settled with the superseded left out, are integrated into the knowledge base and the next one forks
    from it). Every event reaches it as it happens and as its own message: nothing is gathered into a batch, so it
    works problem by problem and sees each as it stands (the owner, 2026-09-20)."""
    st = peek()
    if not st["events"]:
        return
    name = planner_live(st)
    if name:
        with state() as w:
            events, w["events"] = w["events"], []
            w["sessions"][name]["events"] = (w["sessions"][name].get("events") or []) + events
        for e in events:  # one message each: two events are two problems, not one batch
            post(name, e["from"], e["text"])
        wake_planner(name)
        return
    if not kb_ready() or st["notes"]:
        return  # the next planner starts from a knowledge base that holds the last one's notes
    with state() as w:
        events, w["events"] = w["events"], []
        n = count(w, "plan")
    name = launch("planner", str(n), lambda name: render(
        "planner", NAME=name, ID="plan", EVENTS=events_text(events), HANDOFF=handoff_parts(), GRAPH=graph_text(), QUEUE=" ".join(peek()["queue"]) or "(empty)",
        STATUS=status_text(), LIST=LIST, OWNER="", FIRST=first_episode(),
        STALE=stale_of(name, base_record("max")[0] or "max")), events=events)
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


STANDSTILL_EVERY = int(os.environ.get("ORCH_STANDSTILL_EVERY", 1800))  # how often a standstill is named again


RETURNED_AFTER = int(os.environ.get("ORCH_RETURNED_AFTER", 1800))  # how long a task may stand with the planner unnamed


def _owned_by(tid):
    """(path, task) of the working-tree changes a task owns, as the guard recorded them."""
    changed = set(changed_paths())  # once, for the same reason
    with owners(write=False) as o:
        return sorted((p, t) for p, t in o.items() if t == str(tid) and p in changed)


def with_the_planner(st):
    """The tasks that really are the planner's to move: stage "planner" (given back, ended partial, failed its check)
    and still pending in the graph. The stage is the harness's own bookkeeping and is never cleared when the task is
    completed or dropped elsewhere, so on 2026-09-20 the standstill told the planner that tasks 5, 9, 18 and 21 had
    come back and needed re-planning when 5, 9 and 18 were committed and completed and 21 had been dropped and was
    not in the list at all — four statements, all false, and the only thing it was told about tasks that day."""
    out = []
    for tid, t in sorted(st["tasks"].items()):
        if (t or {}).get("stage") != "planner":
            continue
        task = read_task(tid)
        if task is None or task.get("status") == "completed":
            continue  # dropped, or finished by the path that does not clear the stage
        out.append(tid)
    return out


NOT_STARTED = ("ready", "planner", "unformed", None)  # stages from which a session has yet to be started


def reconcile_stages():
    """The task list is the graph and the planner writes it; the harness's stage is its own bookkeeping, and nothing
    made it follow. A task the planner completes keeps whatever stage it had: on 2026-09-20 tasks 5, 9 and 18 read as
    the planner's long after they were committed, and 48 and 50 stood at `ready` while the list called them done —
    one queue ordering away from the dispatch starting a session on work that was finished. It runs before anything
    dispatches, because produce() reads the stage and the reconciliation must have happened first.

    A completed task that is *running* or finalizing is not healed but named: a live session on finished work is a
    conflict the planner has to resolve, not bookkeeping to tidy.

    task_state() holds the same rule for a *queued* task, inside produce()'s own walk, and has since before this: a
    queued task was never dispatched after the planner completed it. This is the general case, not the guard that
    case rests on."""
    st = peek()
    heal = [tid for tid, x in st["tasks"].items() if (x or {}).get("stage") in NOT_STARTED
            and (read_task(tid) or {}).get("status") == "completed"]
    if heal:
        with state() as w:
            for tid in heal:
                w["tasks"][tid]["stage"] = "done"
        log("the stage of " + ", ".join(sorted(heal)) + " followed the task list: they are completed")
    for tid, x in sorted(st["tasks"].items()):
        if (x or {}).get("stage") in NOT_STARTED + ("done",):
            continue
        task = read_task(tid)
        if task is None and in_list(tid):
            continue  # there and unreadable: read_task has said so, and it is not a task taken out of the list
        # A task taken out of the list is the same conflict as one completed in it: the harness is working on what the
        # graph no longer has. Only "completed" was read here, and the planner does take tasks out — 21 and 51 were
        # gone from the list while the state still held them (2026-09-21). Their stage is the planner's, so they fall
        # above; a *parked* task taken out would have been resumed by produce() with nothing said.
        if task is not None and task.get("status") != "completed":
            continue
        gone = task is None
        if (age_of(f"finished-{tid}") or LOST_BLOCKER + 1) > LOST_BLOCKER:
            open(os.path.join(STATE, f"finished-{tid}"), "w").write(str(time.time()))
            with state() as w:
                event(w, "the harness", f"Task {tid} is "
                      + ("not in the task list at all" if gone else "completed in the task list")
                      + f" and the harness has it {x.get('stage')}, with {x.get('session') or 'a session'} on it. One "
                      "of the two is wrong: stop the work (`v2.py drop " + tid + "`) if it is done, or "
                      + ("put the task back in the list" if gone else "set the task back to pending") + " if it is not.")
            log(f"task {tid} is " + ("not in the list" if gone else "completed in the list")
                + f" and {x.get('stage')} in the harness")


def returned_tasks():
    """Every task that only the planner can clear, named to it while it stands: one given back to it, one whose
    proposal is not placed, and one whose brief is not in form.

    A task given back to the planner (stage "planner") is moved by nothing else: no session takes it and no queue
    reaches it. Until 2026-09-20 the only thing that said so was standstill(), which is suppressed while anything
    works and while the planner deliberates — and deps_done() names such a task only to a queued dependent, hourly,
    and only if one exists. So tasks 5, 9, 18 and 21 stood with the planner for hours and were named 11.5 minutes
    into the run, at the first second its turn ended into a standstill; nothing about that was a timer, and with work
    in flight it would not have been said at all. Named here on its own, so the notice does not wait on the
    orchestration having nothing to do."""
    st = peek()
    mine = set(with_the_planner(st))
    for tid, t in sorted(st["tasks"].items()):
        mark = os.path.join(STATE, f"returned-{tid}")
        stage = (t or {}).get("stage")
        # Three conditions, one period and one marker: a task nothing but the planner can clear. `unformed` was told
        # once, when task_state first read its brief, and then never again — the standstill does not list it either,
        # so a task whose brief is not in form simply never ran and nothing said so a second time (2026-09-20).
        # A review task whose subject has finished without being reviewed can never start: pending_reviews only
        # offers one whose subject is `reviewing`. Tasks 23 and 47 stood `ready` in the queue that way, reviews of
        # 22 and 46, which the planner completed on taking stock — nothing would ever take them and nothing said so,
        # since a ready task with no open blocker is not in the standstill either (2026-09-20).
        # only the stage: reconcile_stages runs first in the dispatch and has already set a completed task's stage
        # to "done", so reading the list here as well was a second branch nothing could reach
        orphan = (stage == "ready" and t.get("kind") == "review"
                  and (peek()["tasks"].get(t.get("reviews") or "") or {}).get("stage") == "done")
        # a design or an investigation is judged by the planner itself: pending_reviews offers no reviewer for a
        # kind that is not build or fix, so a finished one waits for a verdict nothing else can give. It was said
        # once, in the event when it finished, and nothing said it again (2026-09-21).
        judge = stage == "reviewing" and t.get("kind") not in ("build", "fix")
        owed = tid in mine or (stage == "proposed" and t.get("proposal")) or stage == "unformed" or orphan or judge
        if not owed:
            with contextlib.suppress(OSError):
                os.remove(mark)  # cleared: the next time it comes back is counted afresh
            continue
        try:  # the file holds when it first stood there; its mtime is when that was last said
            since = time.time() - float(open(mark).read())
        except (OSError, ValueError):
            open(mark, "w").write(str(time.time()))
            continue
        if since < RETURNED_AFTER or (age_of(f"returned-{tid}") or 0) < RETURNED_AFTER:
            continue
        os.utime(mark, None)
        if orphan:
            with state() as w:
                event(w, "the harness", f"Review task {tid} has stood {int(since // 60)} minutes with nothing able "
                      f"to start it: it reviews task {t.get('reviews')}, which is finished, and a review is only "
                      "ever started for a task that is in review. Drop it, or set its subject back if the work "
                      "still wants judging.")
            log(f"review task {tid} cannot start: task {t.get('reviews')} is finished")
            continue
        if judge:
            with state() as w:
                event(w, "the harness", f"Task {tid} ({t.get('kind') or 'a design'}) has waited {int(since // 60)} "
                      "minutes for your verdict: a design and an investigation are judged by you, and no reviewer is "
                      f"ever started for one. Read its result (.build/tasks/{tid}/result.md) and record the verdict "
                      f"(`v2.py verdict {tid} accept|reject --file .build/tasks/{tid}/verdict.md`), with `## Summary` "
                      "and, for a rejection, `## Findings`.")
            log(f"task {tid} has waited {int(since // 60)} min for the planner's verdict")
            continue
        if stage == "unformed":
            with state() as w:
                event(w, "the harness", f"Task {tid} has stood {int(since // 60)} minutes with its brief not in "
                      "form, so nothing takes it up and nothing will: the harness said so once, when it first read "
                      "it, and says it again only here. Put the brief in form, or drop the task.")
            log(f"task {tid} has stood {int(since // 60)} min with its brief not in form")
            continue
        if stage == "proposed":
            with state() as w:
                event(w, "the harness", f"Brief task {tid} proposed {t.get('proposed', '?')} task(s) "
                      f"{int(since // 60)} minutes ago and they are still not in the graph. Nothing else places them "
                      f"— the graph is yours alone: read {t.get('proposal')} and place them (`v2.py accept {tid}`), "
                      "or say what to change and leave them where they are. Until you do, none of that work exists.")
            log(f"brief {tid} has waited {int(since // 60)} min to be placed")
            continue
        # A task that came back may also be the one whose installed work stands in the working tree, and then it
        # holds the tree: every other producing session is refused it and parks, and nothing will let it go, because
        # nothing moves a task that is with the planner. That is the blocker-not-in-the-list shape over the tree, and
        # it is said here rather than left to a standstill to show it once everything has parked.
        holds_tree = tree_writer(st) == tid
        waiting = sorted(n for n, s in st["sessions"].items() if s.get("tree_wait") == tid and not s.get("released"))
        with state() as w:
            event(w, "the harness", f"Task {tid} has stood with you for {int(since // 60)} minutes: it came back and "
                  "has not been re-planned, and nothing else moves it. Re-plan it, split it over what exists, or "
                  "drop it (`v2.py drop`) — while it stands, anything that waits on it waits for ever."
                  + (" It also holds the **working tree**: its installed work stands there ("
                     + ", ".join(p for p, x in _owned_by(tid)) + "), so every other producing task is refused the "
                     "tree and parks for a task that cannot complete"
                     + (f" — {', '.join(waiting)} already waits" if waiting else "")
                     + ". Re-planning it, or a task that finalizes its work, is what frees the tree."
                     if holds_tree else ""))
        log(f"task {tid} has stood with the planner for {int(since // 60)} min"
            + ("; it holds the working tree" if holds_tree else ""))


GRAPH_HELD_EVERY = int(os.environ.get("ORCH_GRAPH_HELD_EVERY", 1800))  # how often a held graph is named again


def held_graph():
    """While the graph is held nothing of it runs and only the planner can lift it, so it is named to the planner as
    its own event and named again while it lasts. Not left to standstill(), which answers a different question and is
    suppressed while anything works, while the planner deliberates and while it has events waiting: a planner that
    dropped what the graph no longer needs and then forgot to say the order would have had nothing tell it that the
    run was standing still on its word alone."""
    why = graph_held()
    if not why:
        with contextlib.suppress(OSError):
            os.remove(os.path.join(STATE, "graph-held.told"))
        return
    told = age_of("graph-held.told")
    if told is not None and told < GRAPH_HELD_EVERY:
        return
    open(os.path.join(STATE, "graph-held.told"), "w").write(str(time.time()))
    st = peek()
    waiting = [tid for tid in st["queue"] if (st["tasks"].get(tid) or {}).get("stage") not in ("done", None)]
    with state() as w:
        event(w, "the harness", f"The graph is held, and nothing of it runs: {why}. "
              + (f"{len(waiting)} tasks stand in the queue ({' '.join(waiting[:12])}"
                 + (", …" if len(waiting) > 12 else "") + ") and not one of them will start — no build, no fix, no "
                 "review, no brief — while this stands. " if waiting else "The queue is empty. ")
              + "Two things are yours to do here, and only the second ends it: drop what the graph no longer needs "
                "(`v2.py drop ID`, and take the task out of the list), then say what the order of the rest is "
                "(`v2.py queue ID …`), which is what lifts the hold. Dropping alone does not lift it, and neither "
                "does re-planning: the "
                f"order is the word the harness waits for. You are told again in {GRAPH_HELD_EVERY // 60} minutes "
                "while this lasts.")
    log("the graph is held and the planner is told; its order lifts it")


def standstill():
    """Nothing is working, nothing has happened, and only the planner can move the graph — but the planner is woken by
    events, and there are none. The orchestration stood still three times this way on 2026-09-20 (01:34–03:35,
    04:49–07:24, 07:24–09:38: six and a half hours), two sessions parked for a wait that never ended, their
    three-hour hold the only escape; nothing said so but health.py, to nobody. It is named to the planner instead,
    with what stands and what each thing waits for, and named again while it lasts."""
    st = peek()
    if working(st):
        with contextlib.suppress(OSError):
            os.remove(os.path.join(STATE, "standstill"))
        return
    if st["events"] or st["notes"] or st.get("kb_building") or not kb_ready():
        return  # something is on its way to the planner, or the knowledge base is not ready to fork
    name = planner_live(st)
    if name and (st["sessions"].get(name) or {}).get("state") != "idle":
        return  # the planner is deliberating: that is not a standstill
    if isabelle_runs() or exclusive_holder():
        return  # a run is going, and what waits for it will go on when it ends
    if any((t or {}).get("stage") in FINISHING for t in st["tasks"].values()):
        return  # a finalization is in flight
    if (age_of("standstill") or STANDSTILL_EVERY + 1) < STANDSTILL_EVERY:
        return
    open(os.path.join(STATE, "standstill"), "w").write(str(time.time()))
    stands, mine = [], set(with_the_planner(st))
    for tid, t in sorted(st["tasks"].items()):
        p = t.get("parked") or {}
        if t.get("stage") == "parked":
            mins = int((time.time() - (p.get("since") or time.time())) // 60)
            stands.append(f"task {tid} has been parked {mins} min for "
                          + {"run": "its own run", "tree": "the working tree", "fix": f"task {p.get('after')}",
                             "answer": "the answer to its question"}.get(p.get("for"), p.get("for") or "something"))
        elif tid in mine:
            stands.append(f"task {tid} is yours: it came back and has not been re-planned")
    for tid in st["queue"]:
        t = st["tasks"].get(tid) or {}
        if t.get("stage") != "ready":
            continue
        open_blockers = [b for b in ((read_task(tid) or {}).get("blockedBy") or [])
                         if (read_task(b) or {}).get("status") != "completed"]
        if open_blockers:
            stands.append(f"task {tid} is ready but waits on {', '.join(open_blockers)}")
    backlog = build_backlog(st)
    with state() as w:
        event(w, "the harness", "Nothing is working and nothing in the queue can start: only you can move this. "
              + ("What stands: " + "; ".join(stands) + ". " if stands else "Nothing is parked and nothing is blocked. ")
              + (f"{len(backlog)} build and fix tasks are open" if backlog else "No build or fix task is open")
              + f", and the queue is {' '.join(st['queue']) or 'empty'}. "
              + ("The graph is held and that is why none of it starts (" + graph_held() + "): your order "
                 "(`v2.py queue ID ...`) is what releases it. " if graph_held() else
                 "Queue what can be done, take back a wait that cannot end (`v2.py blockers ID none` for a graph "
                 "blocker, `v2.py after ID none` for a task waiting on its fix), or re-plan what came back to you. ")
              + f"You are told again in {STANDSTILL_EVERY // 60} minutes while this lasts.")
    log("standstill: nothing is working and nothing can start; the planner is told")


def tidied():
    """State that outlives what it was about: a wake mark once its session is long gone, and the frozen sources of a
    base no base names any more. Every one of the day's stalls was state nobody removed, and these are the harmless
    end of that class — removed rather than left to be read by someone later."""
    if (age_of("tidied") or TIDY_EVERY + 1) < TIDY_EVERY:
        return []
    open(os.path.join(STATE, "tidied"), "w").write(str(time.time()))
    packs = set()
    for who in BASES:
        try:
            packs.add(json.load(open(os.path.join(STATE, f"{who}-base.json"))).get("pack"))
        except (OSError, ValueError):
            packs.add(None)
    sweep_packs = None not in packs  # a base whose record cannot be read: its pack is not swept on a guess
    gone = trees_tidied()  # written for this sweep and never called from it, so a tree holding nothing stayed
    sids = {s.get("sid") for s in peek()["sessions"].values()}
    for name in os.listdir(STATE):
        if name.startswith("work-") and name.endswith(".snap") and name[5:-5] not in sids:
            shutil.rmtree(os.path.join(STATE, name), ignore_errors=True)  # the session it measured is gone
            gone.append(name)
    for name in os.listdir(STATE):
        path = os.path.join(STATE, name)
        if name.endswith(".woken") and (age_of(name) or 0) > WOKEN_KEEP:
            os.remove(path)
            gone.append(name)
        elif sweep_packs and name.startswith("base-pack-") and os.path.isdir(path) and path not in packs:
            shutil.rmtree(path, ignore_errors=True)
            gone.append(name)
    # A mailbox outlives its session. An empty one of a session that reads nothing ever again is litter; a box with
    # something in it was already said to have reached nobody (deliver, lost), and is kept while that session is still
    # in the state, so that what it holds can still be read. One whose session the archive has taken away goes.
    sessions = peek()["sessions"]
    # a layer's snapshot is kept while any session still holds that layer, and while it is the one being forked
    holding = {s.get("origin_sid") for s in sessions.values()
               if s.get("state") in LIVE + ("parked", "idle") and not s.get("released")}
    holding |= {(layer_record(who) or {}).get("sessionId") for who in BASES}
    for name in os.listdir(STATE):
        if name.startswith("layer-") and name.endswith("-manifest.json") and name[6:-14] not in holding:
            with contextlib.suppress(OSError):
                os.remove(os.path.join(STATE, name))
            gone.append(name)
    for name in os.listdir(os.path.join(STATE, "mail")) if os.path.isdir(os.path.join(STATE, "mail")) else []:
        if not name.endswith(".jsonl"):
            continue
        path, who = os.path.join(STATE, "mail", name), name[:-len(".jsonl")]
        s = sessions.get(who)
        if s is None or (os.path.getsize(path) == 0 and (s.get("released") or s.get("state") in ("done", "lost"))):
            with contextlib.suppress(OSError):
                os.remove(path)
            gone.append("mail/" + name)
    if gone:
        log(f"tidied {len(gone)} piece(s) of state nothing names any more: {', '.join(sorted(gone)[:6])}"
            + (", …" if len(gone) > 6 else ""))
    return gone


def dispatch_once():
    st = peek()
    if not st["active"] or os.path.exists(os.path.join(STATE, "stopped")):
        return
    for part in (reconcile_stages, tree_care, check_isolation, parking_care, fix_deadlock, efficiency_care, kb_care, produce, support,
                 quick_fix, tidied,
                 consult, returned_tasks, held_graph, standstill, plan):  # before plan: what they say reaches it now
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
                "left, park for it (`v2.py park answer`): the producing slot is free for another worker meanwhile")
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
        if c and c["role"] != "planner" and q.get("session") != c["name"]:
            # every question is answered by the consultation forked for it, or by the planner when it was asked of
            # the planner. Any session could answer any question, and its answer would reach the asker as the
            # harness's own — a session's word put where another's work reads it (2026-09-21).
            return (f"refused: {qid} is answered by the consultation started for it, or by the planner when it was "
                    "asked of the planner. What you know that bears on it goes to its asker through the planner "
                    "(`v2.py ask --to planner`), or into your result.")
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
        if not text.strip():
            # where it was carried is the whole point of saying so: the answer stops being listed, and without it
            # nothing records what became of what it decided
            return (f"refused: v2.py carried {qid} \"where\" — say where what the answer decides now stands (the "
                    "Planner's line of a task, HANDOFF.md), because that is what stops it being loose.")
        q.update(delivered=True, carried=text.strip())
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
            "than the run ends): the producing slot is free for another worker meanwhile.")


def cmd_measuring(text=""):
    """A run whose result is a timing holds the machine alone: another run beside it distorts the number as surely as
    it exceeds the memory, and the harness gave that hold only to a check advancing the base heap (the owner,
    2026-09-20). Claimed before the run is launched; it stands while the run does, and falls of itself after."""
    c = caller()
    if not c or c["role"] not in PRODUCING or not c.get("task"):
        # the roles that run: a task designer has a task too, and reads statements rather than measuring anything,
        # so its claim would hold the machine against every check for the grace it is given (2026-09-21)
        return "refused: a producing session working on a task claims the machine for its measurement"
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
    return (f"parked: end your turn now; the producing slot is free for another worker meanwhile. You are resumed "
            f"here, your context intact, when {what} and the slot is free; if not within {HOLD_PARK // 3600} hours, "
            "you are woken to record "
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
    bad = [f for f in files if not os.path.lexists(os.path.join(PROJECT, f)) and git_out("ls-files", "--error-unmatch", "--", f, quiet=True) is None]
    outside = [f for f in files if os.path.isabs(f) or os.path.normpath(f).startswith("..") or exempt(os.path.normpath(f))
               or subprocess.run(["git", "-C", PROJECT, "check-ignore", "-q", "--", f]).returncode == 0]
    if outside:
        return ("refused: the finalizer commits files of the repository's working tree, not ignored, not under .build/ or "
                f".claude/, relative to the project: {', '.join(outside)}")
    standing = base_would_stand_in_a_task(check or "")
    if standing:
        return "refused: " + BASE_IN_A_TASK.format(named=", ".join(standing))
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
    # A session that ends with a question of its own open reads nothing ever again: six of nineteen answers on
    # 2026-09-20 came to a session that had gone, and each had to be carried by the planner instead. It is told where
    # its answer will go, so that what it assumed is in its result rather than only in its head.
    open_asks = [q for q, a in peek()["asks"].items()
                 if a["from"] == (c or {}).get("name") and a["state"] != "answered"]
    return "recorded. End your turn now." + (
        f" Your question{'s' if len(open_asks) > 1 else ''} {', '.join(open_asks)} "
        f"{'are' if len(open_asks) > 1 else 'is'} still open: you will not read the answer, which goes to "
        f".build/tasks/{tid}/answers/ and to the planner. Say in your result what you assumed instead of it."
        if open_asks else "")


def further_goals(group):
    """Of a group of tasks — proposed or already written — those that would be further GOALS rather than detail.

    `group` is {name: {"blockedBy": [...], "feeds": [...]}}, where a name is a proposal's local key or a task id, and
    `feeds` names tasks already in the graph that are to wait on this one instead.

    Detail is work the graph waits on: something already there waits on it, directly or through the group, so the
    plan is expressed more finely without reaching past where it already ended. Inserting into the middle of a chain
    is detail and is admitted whatever the depth — a brief exists to make planned work concrete, and a detailing bent
    to keep a chain short is worse than a long one (the owner, 2026-09-20).

    A further goal waits on open work already in the graph and nothing already there waits on it: the graph growing
    outward rather than finer. That is what GRAPH_DEPTH bounds.

    Being fed is closed under the group's own edges: if an existing task will wait on X and X waits on Y inside the
    group, Y is fed too. That is how a review task waits on the build it reviews, and why the group is read whole.
    One function serves the proposal and anything already written, so the rule cannot be two rules that differ."""
    tasks = {t["id"]: t for t in all_tasks()}
    is_open = lambda b: b in tasks and tasks[b].get("status") != "completed"
    # `feeds` on a member names the existing tasks that will wait on IT, so the member is the one fed — not the
    # task it names. Written the other way round first, which made every splice read as a further goal.
    fed = {n for n, e in group.items() if e.get("feeds")} | {
        b for x in tasks.values() if x["id"] not in group and x.get("status") != "completed"
        for b in (x.get("blockedBy") or []) if b in group}           # already: existing work waits on us
    stack = list(fed)
    while stack:                                                      # and closed under the group's own edges
        for b in (group.get(stack.pop()) or {}).get("blockedBy") or []:
            if b in group and b not in fed:
                fed.add(b)
                stack.append(b)
    return sorted(n for n, e in group.items()
                  if n not in fed and any(b not in group and is_open(b) for b in (e.get("blockedBy") or [])))


def create_task(subject, description, metadata, blocked_by):
    """Write a task into the graph. The harness does this on the planner's word: the task designer proposes and does
    not edit the list (the owner, 2026-09-20)."""
    d = os.path.join(TASKS, LIST)
    os.makedirs(d, exist_ok=True)
    # Claude Code allocates ids from `.highwatermark` beside the task files, so taking one above the files alone
    # would hand back an id it is about to use again and overwrite the task written here. On 2026-09-20 the mark
    # stood at 51 with task 52 already written, which is exactly that gap. The id goes above both, the mark is
    # raised to it, and an id whose file exists is never taken.
    mark = os.path.join(d, ".highwatermark")
    with open(os.path.join(d, ".alloc.lock"), "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        used = {int(f[:-5]) for f in os.listdir(d) if f[:-5].isdigit() and f.endswith(".json")}
        try:
            high = int((open(mark).read().strip() or "0"))
        except (OSError, ValueError):
            high = 0
        n = max(high, max(used, default=0)) + 1
        tid = str(n)
        if os.path.exists(task_path(tid)):  # never silently over a task that is there
            raise RuntimeError(f"task {tid} already exists: the id allocation is not sound")
        json.dump({"id": tid, "subject": subject, "description": description, "status": "pending",
                   "metadata": metadata, "blocks": [], "blockedBy": list(blocked_by)},
                  open(task_path(tid) + ".tmp", "w"), indent=2)
        os.replace(task_path(tid) + ".tmp", task_path(tid))
        with contextlib.suppress(OSError):
            open(mark, "w").write(str(n))
    return tid


def proposal_problems(entries):
    """What is wrong with a proposal: its form, and every reference it makes."""
    out, keys = [], [e.get("key") for e in entries]
    if not entries:
        return ["the proposal names no task"]
    for k in {k for k in keys if keys.count(k) > 1}:
        out.append(f"two tasks share the key {k!r}")
    for e in entries:
        key = e.get("key") or "(no key)"
        if not e.get("key"):
            out.append("a task has no `key` (its name inside this proposal, for the others to wait on)")
        elif read_task(e["key"]):
            out.append(f"task {key}: its key is the id of a task already in the list, so nothing could tell which "
                       "one a blockedBy means — give it a name of its own")
        if not (e.get("subject") or "").strip():
            out.append(f"task {key}: no subject")
        out += [f"task {key}: {p}" for p in brief_problems(e.get("description", ""))]
    kinds = {e.get("key"): brief_kind(e.get("description", "")) for e in entries}
    reviews = {e.get("key"): reviewed(e.get("description", "")) for e in entries if kinds.get(e.get("key")) == "review"}
    for key, k in kinds.items():
        if k in ("build", "fix") and key not in reviews.values():
            out.append(f"task {key} is a {k} task without a review task (kind review, `Reviews:` naming its key)")
    for r, subject in reviews.items():
        if subject not in keys and not in_list(subject or ""):
            out.append(f"review task {r} reviews {subject!r}, which is neither a task of this proposal nor in the list")
    known = set(keys)
    for e in entries:
        for b in e.get("blockedBy") or []:
            if b not in known and not in_list(b):
                out.append(f"task {e.get('key')} waits on {b!r}, which is neither a task of this proposal nor in the list")
        # `feeds` is what makes a task detail rather than a further goal, so it is checked rather than taken on
        # trust: an unchecked one would exempt a task from the depth rule and then silently not be wired.
        for f in e.get("feeds") or []:
            task = read_task(f)
            if f in known:
                out.append(f"task {e.get('key')} feeds {f!r}, which is a task of this proposal: say blockedBy for that")
            elif not in_list(f):
                out.append(f"task {e.get('key')} feeds {f!r}, which is not in the task list")
            elif task.get("status") == "completed":
                out.append(f"task {e.get('key')} feeds {f!r}, which is completed: nothing waits on it any more")
    return out


def cmd_propose(bid, path):
    """The task designer's tasks and where it would place them. It does not write them: the planner decides and the
    harness writes them (cmd_accept). What it proposes is judged here for form and for placement, so that a brief
    that cannot be placed is said to be unplaceable once, with its work kept, rather than written and refused."""
    c = caller()
    if c and (c["role"] != "task-designer" or c.get("task") != bid):
        return f"refused: brief task {bid} is proposed by its task designer"
    try:
        entries = json.load(open(os.path.join(PROJECT, path)))
        assert isinstance(entries, list)
    except (OSError, ValueError, AssertionError) as e:
        return f"refused: {path} is not a list of tasks in JSON ({e!r})"
    problems = proposal_problems(entries)
    if problems:
        return "refused: the proposal is not in form:\n- " + "\n- ".join(problems)
    goals = further_goals({e["key"]: e for e in entries})
    depth = (peek()["tasks"].get(bid) or {}).get("depth_at_start")
    # above the limit, not at it: every message says "at most GRAPH_DEPTH", and the owner's rule is that a brief may
    # not add a further goal when the depth is *above* the limit. The live chain stood at exactly 10 (2026-09-21).
    if goals and depth is not None and depth > GRAPH_DEPTH:
        return refuse_proposal(bid, entries, goals, depth)
    with state() as w:
        w["tasks"].setdefault(bid, {}).update(stage="proposed", proposal=path, proposed=len(entries))
        event(w, "the harness", f"Brief task {bid} proposes {len(entries)} task(s) and where to place them: "
              + "; ".join(f"{e['key']} ({brief_kind(e.get('description',''))}) after "
                          + (", ".join(e.get("blockedBy") or []) or "nothing") for e in entries)
              + f". The file is {path}. They are not in the graph: you place them "
              "(`v2.py accept " + bid + "`, which writes them as proposed and queues them after this brief), or say "
              "what to change first — the graph is yours alone to edit.")
    kick()
    return (f"proposed {len(entries)} task(s); the planner places them. Record your result (`v2.py result {bid}`) "
            "with what you briefed and why each waits on what it does, and end your turn.")


def refuse_proposal(bid, entries, goals, depth):
    with state() as w:
        w["tasks"].setdefault(bid, {})["stage"] = "planner"
        event(w, "the harness", f"Brief task {bid} is yours to resolve. Its detailing needs {', '.join(goals)} to be "
              f"further goals — waiting on work already in the graph that nothing already there waits on — and the "
              f"chain was {depth} deep when the brief started (at most {GRAPH_DEPTH}). Detail spliced into the graph "
              "is admitted at any depth; work hung past its frontier is not, and the detailing is not wrong for "
              f"needing it. Its proposal stands in .build/tasks/{bid}/ and nothing is in the graph: place what "
              "belongs, shorten what these wait on, or let the work go.")
    log(f"brief {bid} proposed {len(goals)} further goal(s) on a chain {depth} deep: refused, the planner has it")
    kick()
    is_are = "is a further goal" if len(goals) == 1 else "are further goals"
    return (f"refused, and the planner has it: {', '.join(goals)} {is_are}, not further detail, and the "
            f"chain was {depth} deep when this brief started (at most {GRAPH_DEPTH}). Nothing you wrote is lost — "
            "the proposal stands. Do not re-shape the detailing to fit the graph; record your result "
            f"(`v2.py result {bid}`) saying what the work needs and why, and end your turn.")


def cmd_accept(bid):
    """The planner writes a brief's proposed tasks into the graph, as proposed."""
    refused = planner_only("placing a brief's tasks")
    if refused:
        return refused
    rec = peek()["tasks"].get(bid) or {}
    if rec.get("stage") != "proposed" or not rec.get("proposal"):
        return f"refused: brief task {bid} has no proposal waiting"
    try:
        entries = json.load(open(os.path.join(PROJECT, rec["proposal"])))
        assert isinstance(entries, list) and entries
    except (OSError, ValueError, AssertionError) as e:
        return f"refused: {rec['proposal']} cannot be read as a proposal ({e!r}); ask its task designer, or drop it"
    problems = proposal_problems(entries)  # the graph may have moved since it proposed
    if problems:
        return ("refused: the proposal no longer fits the graph:\n- " + "\n- ".join(problems)
                + f"\nTell the task designer (`v2.py tell {bid} ...`) or re-plan the brief.")
    ids, order, repointed = {}, [], {}
    try:  # all of it or none: a half-placed proposal leaves tasks with no edges, and placing it again would write
        for e in entries:  # every one of them a second time. Written first without their edges, so a task may wait
            ids[e["key"]] = create_task(e["subject"], e["description"],  # on one later in the list.
                                        {"kind": brief_kind(e.get("description", "")), "why": e.get("why", "")}, [])
            order.append(ids[e["key"]])
        for e in entries:
            update_task(ids[e["key"]], blockedBy=[ids.get(b, b) for b in (e.get("blockedBy") or [])])
            for f in e.get("feeds") or []:  # existing work re-pointed onto the new: detail, not a further goal
                before = read_task(f)
                if before:
                    # what it waited on before, kept so that a failure after this can put it back: the tasks would
                    # be taken back and an existing one left waiting on an id that no longer exists (2026-09-21)
                    repointed.setdefault(f, list(before.get("blockedBy") or []))
                    update_task(f, blockedBy=[ids[e["key"]]] + [b for b in (before.get("blockedBy") or [])
                                                                if b != bid])
    except Exception as err:  # noqa: BLE001
        for f, waited_on in repointed.items():
            with contextlib.suppress(Exception):
                update_task(f, blockedBy=waited_on)
        for tid in order:
            with contextlib.suppress(OSError):
                os.remove(task_path(tid))
        log(f"placing the proposal of task {bid} failed and was taken back: {err!r}")
        return (f"refused: the proposal could not be placed ({err!r}); the {len(order)} task(s) written before it "
                "failed are taken back, so nothing is half in the graph. The proposal stands where it is.")
    by = rec.get("session")
    with state() as st:
        for e in entries:
            tid = ids[e["key"]]
            st["tasks"].setdefault(tid, {}).update(stage="ready", kind=brief_kind(e.get("description", "")),
                                                   briefed_by=by, briefing=by, queued_at=time.time(), brief_task=bid)
        for e in entries:
            r = reviewed(e.get("description", "")) if brief_kind(e.get("description", "")) == "review" else None
            if r:
                st["tasks"][ids[e["key"]]]["reviews"] = ids.get(r, r)
                st["tasks"].setdefault(ids.get(r, r), {}).setdefault("review_tasks", []).append(ids[e["key"]])
        q = st["queue"]
        at = q.index(bid) + 1 if bid in q else len(q)
        st["queue"] = q[:at] + order + q[at:]
        st["tasks"][bid]["stage"] = "done"
    update_task(bid, status="completed")
    kick()
    return "placed " + ", ".join(f"{e['key']} as {ids[e['key']]}" for e in entries)


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
    missing = [tid for tid in ids if not in_list(tid)]
    if missing:
        # the order is set whole, so a typo in it took the tasks that are really there out of the queue and said
        # only "not in the task list: 99" afterwards. `blockers` refuses the same mistake; this does now too.
        return (f"refused: no task {', '.join(repr(m) for m in missing)} in the list, and the order is set whole — "
                "queueing it would take the tasks that are there out. Name the order again with what is in the list.")
    if not ids:
        # `v2.py queue` with nothing after it emptied the queue and answered "queued": the order is what the planner
        # names, and naming nothing is a typo, not an instruction to stop the run (2026-09-21, found by running it)
        return ("refused: v2.py queue ID ID... — the order is the tasks in the order they are to be done. Naming "
                "none would empty the queue, which is not an order; `v2.py drop ID` takes one task out.")
    since = (c or {}).get("started") or time.time()
    with state() as st:
        for tid in ids:
            t = st["tasks"].get(tid) or {}
            # `done` is terminal bookkeeping and task_state never reads it again, deliberately: between a verdict
            # accepting a task and the planner completing it in the list, re-reading would start the work a second
            # time. But a task the planner has put BACK to pending and then named in its order is one it means to
            # run, and nothing would ever start it again — it would sit in the queue, not startable, unnamed by
            # anything (2026-09-21). The list decides: only a task the list no longer calls completed is re-read.
            reopened = t.get("stage") == "done" and (read_task(tid) or {}).get("status") not in ("completed", None)
            if t.get("stage") in ("planner", "unformed") or reopened:  # re-planned: its stage is read afresh
                st["tasks"][tid] = {k: v for k, v in t.items() if k in ("briefed_by", "briefing", "review_tasks", "reviews")}
        order = list(dict.fromkeys(ids))   # an id named twice is one place in the order, as `blockers` reads its own
        kept = [tid for tid in st["queue"] if tid not in order and (st["tasks"].get(tid) or {}).get("queued_at", 0) > since
                and (st["tasks"].get(tid) or {}).get("stage") != "done"]
        for tid in kept:
            brief = (st["tasks"].get(tid) or {}).get("brief_task")
            at = order.index(brief) + 1 if brief in order else len(order)
            while at < len(order) and order[at] in kept:
                at += 1
            order.insert(at, tid)
        st["queue"] = order
    if graph_held():  # the planner has said what the order is: the graph it inherited is now the graph it chose
        with contextlib.suppress(OSError):
            os.remove(os.path.join(STATE, GRAPH_HELD))
        log("the graph is released: the planner has queued")
        kick()
    kick()
    return "queued" + (f"; kept, briefed since this episode began: {', '.join(kept)}" if kept else "")


def planner_only(what):
    c = caller()
    return f"refused: {what} is the planner's" if c and c["role"] != "planner" else None


def cmd_blockers(tid, ids):
    """The graph's edges are the planner's to set, not only to add (the task designer had them too until it stopped
    writing the graph and began proposing it: it says in its proposal what each task waits on, and `accept` writes
    those edges).

    Claude Code's TaskUpdate offers addBlockedBy and no way back, so until 2026-09-20 a dependency once written could
    not be taken out: the graph was append-only by accident and nothing anywhere said so, while cmd_drop, deps_done
    and the standstill each told the planner to "re-point" a blocker — and the standstill named `v2.py after ID
    none`, which is the efficiency-fix relation and not this one. A planner charged to re-plan an inherited chain as
    work that can run side by side could add edges and delete whole tasks, but could not move one; deleting and
    recreating, which it could do, loses the task's id and its history. That is not a boundary anyone chose."""
    c = caller()
    if c and not ROLES.get(c["role"], {}).get("graph"):
        return ("refused: the graph's edges are the planner's alone. A task designer says in its proposal what each "
                "task waits on (`v2.py propose`), and any other role names what it has found in its result.")
    if not in_list(tid):
        return f"refused: task {tid} is not in the task list"
    want = [] if ids == ["none"] else list(dict.fromkeys(ids))
    tasks = {t["id"]: dict(t) for t in all_tasks()}
    missing = [b for b in want if b not in tasks]
    if missing:
        return f"refused: no task {', '.join(missing)} in the list"
    if tid in want:
        return f"refused: task {tid} cannot wait on itself"
    tasks[tid]["blockedBy"] = want
    circle = [b for b in want if waits_on(tasks, b, tid)]
    if circle:
        return (f"refused: task {', '.join(circle)} already waits on {tid}, through the graph, so this would close a "
                "cycle in which neither could ever start")
    had = read_task(tid).get("blockedBy") or []
    update_task(tid, blockedBy=want)
    kick()
    gone, new = [b for b in had if b not in want], [b for b in want if b not in had]
    log(f"task {tid} waits on {' '.join(want) or 'nothing'} (was {' '.join(had) or 'nothing'})")
    return (f"task {tid} waits on {', '.join(want) or 'nothing'}"
            + (f"; taken out: {', '.join(gone)}" if gone else "")
            + (f"; added: {', '.join(new)}" if new else "")
            + ("" if want else ". It is startable as soon as it is queued."))


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
        if other == "none":  # always: a relation written the wrong way round is taken back, parked or not
            had = t.pop("efficiency_fix", None)
            t.pop("fix_told", None)
            if t.get("stage") == "parked" and (t.get("parked") or {}).get("for") == "fix":
                t["parked"]["after"] = "none"
            return (f"task {tid} waits for nothing now" + (f" (it waited for task {had})" if had else
                    "; it was waiting for nothing"))
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
    # the direction, in full, because it was written the wrong way round once and could not be taken back
    which = (f"TASK {tid} WAITS FOR TASK {other}: {tid} is told when {other} lands, and continues then. Task {other} "
             f"is told nothing and waits for nothing. If you meant it the other way, `v2.py after {other} {tid}`, and "
             f"`v2.py after {tid} none` takes this one back.")
    if t.get("stage") == "parked" and (t.get("parked") or {}).get("for", "fix") == "fix":
        return f"task {tid} continues when {other} has landed. " + which
    return which


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
    waiting = [x["id"] for x in all_tasks() if tid in (x.get("blockedBy") or []) and x.get("status") != "completed"]
    return (f"task {tid} is dropped: it leaves the queue and comes back to you to re-plan, split or take out of the "
            "list. " + ("Stopped: " + ", ".join(names) + "." if names else "Nothing was working on it.") + aside
            + (f". Task {tid} stays in the list and is still the blocker of {', '.join(waiting)}, which wait on it "
               f"until you re-plan it, or point them elsewhere (`v2.py blockers ID ...`, `none` for no blocker)."
               if waiting else ""))


def cmd_planned(notes):
    c = caller()
    if c and c["role"] != "planner":
        return "refused: ending the planner's work is the planner's"
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
        if c:  # its events go with it: by ending it says it has handled them
            st["sessions"][c["name"]].update(state="done", ended=time.time(), events=[])
    kick()
    return "planned. End your turn now; the knowledge base takes up your notes and the next planner starts from them."


# ---------------------------------------------------------------- commands of the harness

FRESH_CHARGE = (
    "This run begins on a knowledge base built fresh: it holds HANDOFF.md, the owner ledger and the owner's words, "
    "and nothing that any planner before you accumulated. The graph you inherit was built under a harness that has "
    "since changed, and some of it exists only because of faults that are now fixed. Before you queue anything, take "
    "stock, and make that your first piece of work:\n"
    "- **What has been produced.** Read what the finished tasks delivered and what stands uncommitted in the working "
    "tree, and write it into HANDOFF.md at the level later work needs. Work that is done but not yet integrated is "
    "the first thing to carry; a task whose deliverable already stands is completed, not repeated. What was done and "
    "how — the course it took, what was abandoned, what it cost — goes to PLANNING_LOG.md, which is new and empty: "
    "HANDOFF.md is what you need to act now, the log is everything true that you no longer need to act on.\n"
    "- **What the graph no longer needs.** Drop what is superseded, what a fault made necessary, and what the work "
    "already answers (`v2.py drop ID`, and take the task out of the list). Say why in your notes: a task dropped "
    "without a reason comes back.\n"
    "Until you have taken stock the graph is **held**: nothing of it runs — no build, no fix, no review, no brief — "
    "and your order (`v2.py queue ID …`) is what lifts it. Dropping alone does not, and neither does re-planning. "
    "Nothing waits on a timer, so take the time this needs; you are reminded while the hold stands.\n"
    "- **What the structure should now be.** The harness has changed under you and the protocols carry what bears on "
    "planning: you live across your events and see each as it happens; the rate is what the owner set and your "
    "status line says it, so a review or a brief runs beside a producer; a task that parks hands the producing slot to anything independent that is ready; and your "
    "status line says how many tasks could start at all. The graph you inherit is a chain — re-plan it as work that "
    "can run beside itself wherever the work truly admits it, and not one step further than that.\n"
    "Only then queue. Nothing of this is a task for anyone else: it is yours, and it is what you do first.")


def layerless():
    """The bases whose list is split but which have no layer to fork. The stable part alone is a reference without
    the direction — no frontier, no tools, no plan, no reasoning inventory, no owner's words — so a role that forked
    it would be missing everything that steers it. An orphaned layer counts as none (layer_record)."""
    import manifest
    out = []
    for who in BASES:
        if not os.path.exists(os.path.join(STATE, f"{who}-base.json")):
            continue
        try:
            split = manifest.has_layer(os.path.join(HERE, manifest.LISTS[who]))
        except (OSError, KeyError):
            continue
        if not split or layer_record(who):
            continue
        # a base built before the list was split holds the layer's files already: what it holds is the question,
        # not what the list says now
        was = os.environ.get("ORCH_LOAD_LIST")
        os.environ["ORCH_LOAD_LIST"] = os.path.join(HERE, manifest.LISTS[who])
        try:
            below = {p for _, p in manifest.held_files("layer")}
        except OSError:
            below = set()
        finally:
            os.environ.pop("ORCH_LOAD_LIST", None) if was is None else os.environ.update(ORCH_LOAD_LIST=was)
        if not below:
            continue  # a layer part that matches no file here is not a layer anyone is missing
        try:
            held = set(json.load(open(os.path.join(STATE, f"{who}-manifest.json")))["files"])
        except (OSError, ValueError, KeyError):
            out.append(who)  # nothing says what it holds: treat it as the reference alone
            continue
        if not (below & held):
            out.append(who)
    return out


def cmd_start(fresh=False):
    if held_back():
        return (f"refused: nothing starts a session while the hold is on ({held_back()}). "
                f"Take it off when you mean to begin: rm {os.path.join(STATE, NO_LAUNCH)}")
    short = layerless()
    if short:
        return ("refused: the list of " + ", ".join(short) + " is split into a stable reference and a frontier layer, "
                "and only the reference is built. Its roles would fork a base with no frontier, no tools, no plan and "
                "none of the owner's words — everything that steers them is in the layer. Build it first ("
                + "; ".join(f"base.sh {w} layer" for w in short) + "), or, to run that base whole instead, take the "
                "`# === layer ===` line out of its load list and build it again: the mark is the decision.")
    if fresh:
        st = peek()
        if st["active"]:
            return ("refused: --fresh begins a run, it does not rejoin one — it leaves the knowledge base and the "
                    "planner behind, which under a run in progress would take the context of whatever is deliberating "
                    "with them. The orchestration is active" + (f" and {', '.join(working(st))} are working" if
                    working(st) else "") + "; stop.sh first.")
        for name, s in list(st["sessions"].items()):  # the planner that lives would not fork the new base
            if s.get("role") == "planner" and not s.get("released") and s.get("state") not in ("done", "lost"):
                release(name)
                log(f"released {name}: the run begins on a knowledge base built fresh")
        old_kb = st["kb"]
        with state() as w:
            w["kb"], w["kb_building"] = None, None
            w["notes"] = []  # they were for the knowledge base that is being left behind
        if old_kb:
            release(old_kb)
        log(f"the knowledge base {old_kb or '(none)'} is left behind; the next one loads HANDOFF.md, the ledger and "
            "the owner's words, and nothing else")
        open(os.path.join(STATE, GRAPH_HELD), "w").write(
            "this run began fresh and the planner has not yet said what of the old graph still stands. The charge is "
            "to take stock first; the graph is released by the planner's own order (v2.py queue ...)")
        open(os.path.join(STATE, "graph-held.told"), "w").write(str(time.time()))  # the charge carries the first
        # telling; held_graph() reminds only if the hold is still standing GRAPH_HELD_EVERY later
        log("the graph is held: no task starts until the planner has taken stock and queued")
    with state() as st:
        st["active"] = True
        first = not st["kb"] and not st.get("kb_building")
        if fresh:
            fresh_sweep(st)  # a charge for a run that is over, and a tree that is no longer in trouble
            event(st, "the owner", FRESH_CHARGE, kind="fresh-charge")
        elif first and not st.get("plan_ended"):
            event(st, "the harness", "The orchestration starts, and there is no task graph yet: build it (the first "
                  "episode's part of this message says from what).")
        for i in st.pop("interrupted", []):
            event(st, "the harness", i)
    # A run does not refresh its layers on principle. The staleness rule already refreshes one whose files have
    # moved, within a minute of starting, and marking them here rebuilt three layers that had just been built
    # (2026-09-20). `state/<who>-layer.refresh` still forces one by hand.
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
    """The planner, ready for the owner to speak to it (talk.sh attaches to it): the one that lives, woken if it was
    between events, or a new one. Under the dispatch's lock, so that the two never start two planners."""
    with open(os.path.join(STATE, "dispatch.lock"), "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        return talk()


OWNER_HERE = ("The owner is here and will speak to you (talk.sh). Their words are recorded verbatim in the owner "
              "ledger; act on them in the graph, the order and the decisions, and carry them into HANDOFF.md and "
              "your notes. Wait for them between turns; when they have gone you are told, and go on with your events.")


def talk():
    st = peek()
    name = planner_live(st)
    if name:  # it lives: the owner joins it, with everything it holds
        with state() as w:
            w["sessions"][name]["owner"] = True
        if peek()["sessions"][name]["state"] == "idle":
            wake_planner(name) if has_mail(name) else resume(name, OWNER_HERE)
        return name
    if not kb_ready() or st["notes"]:
        return ""  # the knowledge base is not ready, or has not yet integrated the last planner's notes
    with state() as w:
        events, w["events"] = w["events"], []
        n = count(w, "plan")
    name = launch("planner", str(n), lambda name: render(
        "planner", NAME=name, ID="plan", EVENTS=events_text(events), HANDOFF=handoff_parts(), GRAPH=graph_text(), QUEUE=" ".join(peek()["queue"]) or "(empty)",
        STATUS=status_text(), LIST=LIST, OWNER="The owner started you to speak with you: wait for the owner's "
        "words (the harness records them verbatim in the owner ledger), act on them in the graph, the order and the "
        "decisions, and carry them into HANDOFF.md and your notes. Wait for them between turns; when they have gone "
        "you are told, and go on with your events.",
        FIRST=first_episode(), STALE=stale_of(name, base_record("max")[0] or "max")), events=events, owner=True)
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
    elif role == "planner":  # it is in no slot between its events, and it is still the one to attach to
        s = st["sessions"].get(planner_live(st) or "")
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
        if not s and label == "planner":  # it lives between its events, sealed and warm, not in any slot
            s = st["sessions"].get(planner_live(st) or "")
        out.append(f"{label}: " + (f"{s['name']}" + (f" on {s['task']}" if s.get("task") else "") + f" ({s['state']})"
                                   if s else "-"))
    out.append("queue: " + (" ".join(f"{t}:{(st['tasks'].get(t) or {}).get('stage', '?')}" for t in st["queue"]) or "-"))
    if graph_held():
        out.append("THE GRAPH IS HELD: " + graph_held() + ". Nothing of it starts meanwhile — no build, no fix, no "
                   "review, no brief — and you are the only one who can lift it. Take stock first, then say what the "
                   "order is (`v2.py queue ID ...`), which releases it; the tasks you drop before that never run.")
    busy = working(st)
    out.append(f"working: {len(busy)} of at most {WORKERS_MAX}" + (f" ({', '.join(busy)})" if busy else ""))
    size, biggest, its = handoff_size()
    over = (f" — over it; `## {biggest}` is {its // 1000}K of that. It is your state, not your log: what was done and "
            f"how goes to {PLANNER_LOG}, which no base holds and nothing reads to plan from. A decision about the "
            "development itself is an entry of DECISIONS.md and here a reference; a decision of yours about the work "
            "— what is built next, in what order, what a task must respect — belongs to the task it governs, in its "
            "brief and its `why`. Neither is restated here, and DECISIONS.md never takes planning, scheduling or "
            "anything else operational.")
    out.append(f"HANDOFF.md: {size // 1000}K tokens of at most {HANDOFF_MAX // 1000}K"
               + (over if size > HANDOFF_MAX else ""))
    ready = startable(st)
    out.append(f"startable now: {' '.join(ready) if ready else 'none'}"
               + ("" if len(ready) > 1 else " — nothing else can start while what runs is parked or checking; only a "
                  "wider graph changes that"))
    backlog = build_backlog(st)
    width, depth = graph_figures(st)
    room = GRAPH_WIDTH or WORKERS_MAX
    out.append(f"graph: {width} build and fix tasks can start, {room} slots to take them; the chain is {depth} deep "
               f"(at most {GRAPH_DEPTH} before a brief may add only detail and work that runs first); "
               f"{len(backlog)} open"
               + (f" of at most {BRIEF_BACKLOG}" if BRIEF_BACKLOG else ", no ceiling")
               + ("; no brief is detailed while there is already as much independent work as there are slots — one "
                  "is admitted again when the slots have taken what can start, and a brief is what widens a graph "
                  "rather than what drains it" if width >= room else "")
               + ("; a brief that starts now may add detail at any depth — work spliced in, that something "
                  "already there waits on — but not further goals hung past the graph's frontier, which are refused "
                  "and come to you" if depth > GRAPH_DEPTH else ""))
    parked = [f"{tid} ({int(time.time() - t['parked']['since']) // 60} min, after {t['parked'].get('after') or '?'})"
              for tid, t in st["tasks"].items() if t.get("stage") == "parked"]
    if parked:
        out.append("parked: " + ", ".join(parked))
    waiting = [tid for tid, t in st["tasks"].items() if t.get("stage") in ("checking", "reviewing", "fixing", "committing")]
    if waiting:
        out.append("finishing: " + ", ".join(f"{tid}:{st['tasks'][tid]['stage']}" for tid in waiting))
    if st["events"]:
        out.append(f"events not yet with the planner: {len(st['events'])}")
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
           f"Keep-warm ping {int(time.time())}. Use no tools. Reply with the single word WARM and end your turn.",
           warm_ping=True)
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
    elif c == "verdict" and len(rest) >= 2:
        f = opt("--file")
        print(cmd_verdict(rest[0], rest[1], f))
    elif c == "queue":
        print(cmd_queue(rest))
    elif c == "after" and len(rest) == 2:
        print(cmd_after(rest[0], rest[1]))
    elif c == "propose" and len(rest) == 2:
        print(cmd_propose(rest[0], rest[1]))
    elif c == "accept" and len(rest) == 1:
        print(cmd_accept(rest[0]))
    elif c == "blockers" and len(rest) >= 2:
        print(cmd_blockers(rest[0], rest[1:]))
    elif c == "drop" and len(rest) == 1:
        print(cmd_drop(rest[0]))
    elif c == "planned":
        print(cmd_planned(opt("--notes")))
    elif c == "start":
        print(cmd_start(fresh="--fresh" in rest))
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
