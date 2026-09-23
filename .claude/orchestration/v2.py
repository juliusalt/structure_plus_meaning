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
  v2.py change <<'EOF'           change files: any number of `=== write PATH` and `=== replace PATH` blocks, all or none
  v2.py again [N] [<<'EOF']      run a session's kept command N (its last) as it was, or fixed by SEARCH/REPLACE
                                 blocks on its text
  v2.py ledger TEXT              the planner: a question to the owner, with its working choice, into the owner ledger
  v2.py read SOURCE...          a read of any source: a file's lines, a fact by name, the task's diff, result or log,
                                 a task's brief, a proposal, the recipes that reach theories (`reach:A,B`; `reach`:
                                 the task's changed ones), the task's probe runs (`probes`), a check the harness ran
                                 (`check:STAMP` or `check:ID`) (a read like any other: each source at most READ_BYTES,
                                 a brief named whole whole, the call at most BATCH_BYTES)
  v2.py ask --to WHOM TEXT       a question to kb, planner, designer, task-designer or reviewer
  v2.py reply QID TEXT|--file F [--decision]   answer a question (a consultation, the planner)
  v2.py tell ID TEXT|--file F    the planner (or the owner): tell the sessions working on task ID what changes their work
  v2.py escalate --efficiency TEXT   a performance problem, reported to the planner (its fix becomes a task); go on
  v2.py park run|fix|tree|answer|machine   nothing productive left: park, the producing slot free for another worker, until
                                 the run ends, the fix lands, the working tree is free or the answer comes
  v2.py finalize ID --check CMD --files PATH... --message FILE   hand over the final check and the commit
  v2.py result ID                record the result written to .build/tasks/ID/result.md
  v2.py end                      end the turn with the call it is in, where it may end, rather than with a message
  v2.py bring-main               a task in its own tree: main (what landed since the tree was made) into its branch
  v2.py check                    a task in its own tree: the repository's check of its work, with main and every other
                                 task's waiting, once for all (train.py's batch); parked until its result comes
  v2.py propose ID FILE          the task designer: its tasks and where to place them (JSON); the planner places them
  v2.py accept ID...             the planner: write briefs' proposed tasks into the graph, as proposed
  v2.py proposal ID [KEY...]     what placing a brief's proposal needs, or those of its briefs whole
  v2.py edit FILE                the planner: an edit of the graph in one call — tasks made, rewritten and deleted,
                                 dependencies set or taken out, the order — judged whole, written all or nothing
  v2.py follow-up TASK:ITEM,...  the planner: a draft brief of reviews' follow-ups under its drafts — copied verbatim,
                                 the names they give among its Inputs, the rest marked for it (--kind build: not a fix)
  v2.py verdict ID accept|reject --file FILE   the reviewer (or the planner, for design and investigation)
  v2.py queue ID...              the planner: the order in which tasks are to be done
  v2.py after ID TASK            the planner: the parked task ID continues when TASK has landed (`none`: now)
  v2.py blockers ID ID...|none   the planner: what task ID waits on, set whole (TaskUpdate only adds)
  v2.py drop ID...               the planner: stop whatever works on those tasks
Every command is batchable: give its arguments again in groups separated by a bare `--`, and each group is carried out
as that command alone (`v2.py reply q1 "..." -- q2 --file F`, `v2.py verdict 5 accept --file A -- 6 reject --file B`).
`queue`, `read`, `drop`, `accept`, `proposal` and `tell ID... TEXT` also take several ids directly.
  v2.py planned --notes FILE     the planner: its work ends (its window is full); its notes go to the knowledge base
Harness:
  v2.py start [--fresh] | stop | status | graph | who ROLE | dispatch | talk | ping NAME
      --fresh: leave the knowledge base behind (the next is built from HANDOFF.md, the ledger and the owner's words)
      and charge the first planner with taking stock before it queues anything
"""
import collections
import contextlib
import fcntl
import glob
import hashlib
import json
import os
import re
import select
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


def _one_harness(here, argv):
    """Run the one tree's copy of the harness, whichever copy was invoked.

    _one_tree puts the state right, but not the code: a worktree checks out HEAD, so its `.claude/orchestration` is
    the harness as it was committed when the tree was made, and every harness change since — committed later, or not
    committed at all — is missing from it. A session in a tree reaches that copy by every door it has: its hooks name
    `$CLAUDE_PROJECT_DIR`, which is its tree, and its commands name `.claude/orchestration/v2.py` relative to where
    it stands. Two versions of the rules then act on one state. So a script of this copy that imports v2 is
    re-executed as the one tree's script of the same name, with the same arguments and the same stdin (nothing has
    read it yet: every entry point imports v2 before it reads its hook). ORCH_ONE_HARNESS keeps it from happening
    twice."""
    main = os.path.join(_one_tree(here), ".claude", "orchestration")
    if os.environ.get("ORCH_ONE_HARNESS") or os.path.realpath(main) == os.path.realpath(here):
        return None
    script = os.path.realpath(argv[0]) if argv and argv[0] not in ("", "-c", "-") else ""
    if not script.startswith(os.path.join(os.path.realpath(here), "")):
        return None  # imported by something that is not the harness's own script: nothing to re-execute
    target = os.path.join(main, os.path.relpath(script, os.path.realpath(here)))
    if not os.path.isfile(target):
        return None
    os.environ["ORCH_ONE_HARNESS"] = "1"
    os.execv(sys.executable, [sys.executable, target, *argv[1:]])


_one_harness(HERE, sys.argv)
PROJECT = os.environ.get("ORCH_PROJECT") or _one_tree(HERE)
# STATE follows the one tree too, not this copy's directory, for the same reason. The shell scripts still take
# `$HERE/state`, which is the same path in every case but one: a copy of the harness inside a linked worktree, which
# nothing runs them from — the daemon and the owner run the main copy. Left as it is rather than teaching five
# scripts to resolve a worktree, which would be more machinery than the fault is worth.
STATE = os.environ.get("ORCH_STATE_DIR") or os.path.join(PROJECT, ".claude", "orchestration", "state")


def transcript_dir(path):
    """Where Claude Code keeps the transcripts of the sessions started in `path`: the path with every character but a
    letter or a digit made `-`, so `…/.build/trees/46` is `…--build-trees-46`."""
    return os.path.expanduser("~/.claude/projects/" + re.sub(r"[^A-Za-z0-9]", "-", path))


TRANSCRIPTS = os.environ.get("ORCH_TRANSCRIPTS") or transcript_dir(PROJECT)
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
FORM_FIELDS = BRIEF_FIELDS + ("Reviews", "Decided", "Yours", "Planner's", "While checks run", "From the review")

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
    # a role's reasoning layer (role_layer_care, behind state/role-layers): a fork of the role's base that reasons once
    # over the run's evidence of the role, which the role's sessions then fork; it uses no tool
    "role-layer": dict(origin=None, settings="worker-settings.json", prefix="layer", statements=False, graph=False),
}
PRODUCER = {"design": "designer", "investigate": "investigator", "build": "implementer", "fix": "fixer"}
PRODUCING, SUPPORTING = set(PRODUCER.values()), {"task-designer", "reviewer"}
LAYERABLE = PRODUCING | SUPPORTING  # the roles that fork a base, each of which may have a reasoning layer
GRAPH_SETTINGS = "planner-settings.json"  # the one settings file that joins the shared task list (the graph):
# every session started with it sees the others' edits to it, injected into its context. Only the roles that edit
# the graph are given it; every other session's task list is its own, named by its own session.
LIVE = ("starting", "working", "waiting")  # a session in one of these holds its slot

JOB_STALE = int(os.environ.get("ORCH_JOB_STALE", 7200))  # a background job whose output stands still this long is dead
SPEC_ERRORS = int(os.environ.get("ORCH_SPEC_ERRORS", 2))  # tries at a check command that is not runnable
# a quick fix's budget: 30 minutes and 15 requests (the owner, 2026-09-21), from 15 and 8 — fix-46 was stopped at its
# eighth request with its one-line repair in hand, one probe short, and its task went back to the planner
FIX_MINUTES = int(os.environ.get("ORCH_FIX_MINUTES", 30))
KB_INTEGRATE_MAX = int(os.environ.get("ORCH_KB_INTEGRATE_MAX", 1200))  # a knowledge base that never
# replies INTEGRATED would hold every episode and every consultation for ever
CLAUDE_MAX = int(os.environ.get("ORCH_CLAUDE_MAX", 180))  # a CLI call that never returns
KB_BUILD_MAX = int(os.environ.get("ORCH_KB_BUILD_MAX", 3600))  # a load that never replies, likewise
LOST_BLOCKER = 3600  # how often a task waiting for a blocker that is not there is named
TREE_TOLD = 900  # how often the same trouble in the same tree is put to the planner again
TIDY_EVERY = int(os.environ.get("ORCH_TIDY_EVERY", 3600))  # how often state nothing names is swept
PACK_KEEP = int(os.environ.get("ORCH_PACK_KEEP", 3 * 3600))  # a pack younger may be one a load is reading
CHECK_KEEP = int(os.environ.get("ORCH_CHECK_KEEP", 3 * 3600))  # a check output no task names, kept this long
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
FIX_ROUNDS = int(os.environ.get("ORCH_FIX_ROUNDS", 15))  # see FIX_MINUTES
# Between two productions a session makes at most ROUNDS reads (a read is a batch); the same failure after fixes
# CIRCLING times in a row stops its checks (work_meter.py enforces them; the protocols state them). Reading was also
# bounded in tokens until 2026-09-21, when every read became bounded in bytes and the owner had it taken out.
ROUNDS = int(os.environ.get("ORCH_ROUNDS", 3))  # the owner's choice of 2026-09-19: few rounds force batched reading
# the second tier (the owner, 2026-09-21): past the ROUNDS requests a production allows, a reading request draws one
# from a reserve of READ_RESERVE, and each production gives one back to it, never beyond READ_RESERVE. The first tier
# makes a session batch; the reserve keeps it from working blind when a step needs more than one batch of reading.
READ_RESERVE = int(os.environ.get("ORCH_READ_RESERVE", 10))
# a batch — one request — is one read, however many reads it holds, which is the point of batching; it reads at most
# BATCH_BYTES, so that one batch cannot read everything, and each read in it — every call's output, a check's too —
# at most READ_BYTES, so that a large chunk is read deliberately, in pieces, rather than taken whole by accident (the
# owner, 2026-09-21: 3K and 30K first, 5K and 50K the same evening). A brief named whole is one unit taken on purpose,
# and is shown whole (whole_brief); `v2.py read` bounds each of its sources, and the call at BATCH_BYTES (cmd_read).
# 80K since 2026-09-22 15:40 (the owner): the sessions' bashOutputMaxChars (128,000) shows a call's output whole up to it
BATCH_BYTES = int(os.environ.get("ORCH_BATCH_BYTES", 80_000))
# 10K since 2026-09-22 15:17 (the owner, on the day's measure: 257 reads cut at 5K in 101 sessions, their whole outputs a
# median 7.5K and 72% within 10K, and the rest read later in 52% of them — a request each, or a read more in the next)
READ_BYTES = int(os.environ.get("ORCH_READ_BYTES", 10_000))
CIRCLING = int(os.environ.get("ORCH_CIRCLING", 3))
# a session's own directory: a call's whole output when what it showed was cut (cut.py), its commands, kept numbered
# for `v2.py again` (work_meter.keep_command), and a check's whole list of errors (check_errors.py) — the newest 50
# outputs and commands, the newest 10 lists, and all of it gone when the session is released: nobody reads on after
OUTPUTS = os.path.join(PROJECT, ".build", "outputs")


def outputs_of(name):
    return os.path.join(OUTPUTS, re.sub(r"[^\w.-]", "_", name or "owner"))
PAUSE = float(os.environ.get("ORCH_PAUSE", 2))  # between stopping a session and resuming it, and between listings
START_MAX = 120  # a start claimed this long ago that has no session yet is abandoned
RETRY = int(os.environ.get("ORCH_START_RETRY", 600))  # an unconfirmed start is tried again after this
# The prompt cache lives an hour past its last hit (promptCacheTtl 1h): a session is warm while its last hit is younger
# than WARM_MAX; a held session is pinged when its last hit is PING_AGE old.
# How often a failure that would repeat on every call is said: the guard's, and a task file that cannot be read.
GUARD_QUIET = int(os.environ.get("ORCH_GUARD_QUIET", 600))
WARM_MAX = int(os.environ.get("ORCH_WARM_MAX", 3300))
PING_AGE = int(os.environ.get("ORCH_PING_AGE", 2700))
PING_RETRY_AFTER = 480  # a failed ping's mark is set back so, against watchdog.pinging's ten minutes: tried again in two
# a parked task whose hold ends within PARK_URGENT is resumed before the planner's order (resume_order): about what one
# landing holds the working tree for, so that one that waited its turn would not have its hold end first
PARK_URGENT = int(os.environ.get("ORCH_PARK_URGENT", 45 * 60))
HOLD_PARK = int(os.environ.get("ORCH_HOLD_PARK", 3 * 3600))  # the owner's choice: a waiting implementer, 3 hours
# A task parked for the one tree waits its turn behind landings that go one at a time, 20-40 minutes each, and a turn
# always comes: tasks 66 and 68 had waited 1.5-1.7 hours on 2026-09-21, and each one whose hold ran out would have
# recorded a partial result and gone back, its context lost. The owner's choice: 6 hours for such a wait (hold_of).
HOLD_TREE = int(os.environ.get("ORCH_HOLD_TREE", 6 * 3600))
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
# 2026-09-19), and reads HANDOFF.md in its first reads; a design task has the room its base leaves, like every other
# (the owner, 2026-09-19: no separate cap).
ROOM = {"planner": int(os.environ.get("ORCH_ROOM_PLANNER", 150_000)),
        "consultant": int(os.environ.get("ORCH_ROOM_CONSULTANT", 60_000))}
KB_MAX = int(os.environ.get("ORCH_KB_MAX", SOFT - max(ROOM["planner"], ROOM["consultant"])))
PROTOCOL_ROOM = 20_000  # a session's first message (protocol and brief) and its first batch of reads, within its room
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


SLOW = float(os.environ.get("ORCH_SLOW", 2.0))  # seconds past which a hook or a session's command says where its time went


def process_age():
    """Seconds since this process started — the interpreter's start and the harness's compilation included, which no
    clock inside the module sees; 0.0 where /proc cannot say."""
    try:
        ticks = int(open("/proc/self/stat").read().rsplit(")", 1)[1].split()[19])
        return max(0.0, float(open("/proc/uptime").read().split()[0]) - ticks / os.sysconf("SC_CLK_TCK"))
    except (OSError, ValueError, IndexError):
        return 0.0


WATCH = []  # the stopwatch of this process, when one runs (lap)


class Stopwatch:
    """Where a hook's or a session's command's time went, said in the log when the whole passes SLOW. A theory change
    took a median 0.8 s with no heavy run going and 7.7 s with one, 13.1 s with two, while every other change stayed
    at about half a second (09-21/22, 478 theory changes, 1.4 hours of the sessions' tool time) — and the parts that
    can be timed apart ran in hundredths of a second on the repository: the next run says which part it is."""

    def __init__(self, what):
        self.what, self.parts, self.last = what, [("start", process_age())], time.time()
        WATCH[:] = [self]

    def lap(self, name):
        now = time.time()
        self.parts.append((name, now - self.last))
        self.last = now

    def done(self, what=None):
        whole = sum(t for _, t in self.parts) + (time.time() - self.last)
        if whole >= SLOW:
            parts = [f"{n} {t:.1f}" for n, t in self.parts + [("the rest", time.time() - self.last)] if t >= 0.05]
            what = what() if callable(what) else what  # named only when it is said: a guard runs on every call
            log(f"slow: {what or self.what} took {whole:.1f} s" + (" — " + ", ".join(parts) if parts else ""))
        WATCH[:] = []


def lap(name):
    """A lap of this process's stopwatch, if one runs."""
    if WATCH:
        WATCH[0].lap(name)


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
    if not control():
        return  # it stays in the box: the watchdog opens every box a turn has not taken (care, planner_mail)
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


WANTED = os.path.join(STATE, "wanted")  # requests to the supervisor from where sessions cannot be controlled (want)
UNCONTROLLED = ("refused: this starts or stops sessions, which nothing run inside Claude Code's sandbox can do "
                "(~/.claude/jobs is not writable there): run it from your own terminal")


def control():
    """Whether this process can start, stop and remove sessions: whether what `claude --bg`, `stop` and `rm` write
    (~/.claude/jobs) is writable here. Inside Claude Code's sandbox it is not, and every session runs its commands
    there, the owner's session too. Tried there, session control half happened: `claude stop` failed unseen and
    release() went on to record the session released while it ran on, watched by nothing, and a dispatch started
    from a session would have claimed a start it could not make (found 2026-09-21, when the sandbox was turned on).
    Such a command asks the supervisor instead (want), which runs outside the sandbox. ORCH_CONTROL=1 or 0 states it
    instead."""
    stated = os.environ.get("ORCH_CONTROL")
    if stated in ("0", "1"):
        return stated == "1"
    home = os.path.expanduser("~")
    for path in (os.path.join(home, ".claude", "jobs"), os.path.join(home, ".claude"), home):
        if os.path.isdir(path):
            return os.access(path, os.W_OK)
    return False


def want(key=None, **request):
    """Ask the supervisor for what this process cannot do (control()): a request in state/wanted/, which the daemon
    notices within seconds and the dispatch carries out first (carry_out_wanted). `key` names a request that is one
    however often it is asked (a dispatch)."""
    os.makedirs(WANTED, exist_ok=True)
    request = dict(request, at=time.strftime("%Y-%m-%dT%H:%M:%S"), by=(caller() or {}).get("name") or "the owner")
    path = os.path.join(WANTED, f"{key or f'{time.time():.6f}-{os.getpid()}'}.json")
    with open(path + ".tmp", "w") as f:
        json.dump(request, f)
    os.replace(path + ".tmp", path)


def carry_out_wanted():
    """What commands without control() asked the supervisor for, in the order asked. Each request is taken (renamed)
    before it is done, so that two passes never do one twice and one that fails is not tried on every pass: the log
    says so instead."""
    try:
        names = sorted(n for n in os.listdir(WANTED) if n.endswith(".json"))
    except OSError:
        return
    for n in names:
        taken = os.path.join(WANTED, n + ".taken")
        try:
            os.replace(os.path.join(WANTED, n), taken)
            with open(taken) as f:
                request = json.load(f)
        except FileNotFoundError:
            continue  # another pass took it
        except (OSError, ValueError) as e:
            log(f"ATTENTION a request to the supervisor could not be read ({n}: {e!r}); it stays as {n}.taken")
            continue
        try:
            if request.get("run"):
                if request["run"] != ["v2.py", "dispatch"]:  # that one is the dispatch this runs in
                    background(*request["run"])
            elif request.get("release"):
                release(request["release"])
            elif request.get("measure"):
                c = peek()["sessions"].get(request["measure"]) or {}
                if c.get("state") in LIVE and not c.get("released") and c.get("role") in PRODUCING and c.get("task"):
                    deliver(c["name"], "the harness", measure_claim(c, request.get("text") or ""))
                else:
                    log(f"the measurement {request['measure']} asked for is not decided: it no longer works on a task")
            else:
                log(f"ATTENTION a request to the supervisor names nothing it does: {json.dumps(request)[:200]}")
        except Exception as e:  # noqa: BLE001  one request must not stop the dispatch
            log(f"ATTENTION the supervisor could not carry out {json.dumps(request)[:200]}: {e!r}")
        with contextlib.suppress(OSError):
            os.remove(taken)


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
    if ("--bg" in args or args[:1] in (("stop",), ("rm",))) and not control():
        log(f"ATTENTION `claude {args[0]}` was not run: {UNCONTROLLED[9:]}")
        return subprocess.CompletedProcess(args, 1, "", UNCONTROLLED)
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


def deltas_on(who):
    """Whether a base's roles fork its delta (notes/plan-delta-layer.md): the bases named in state/deltas, one a line,
    or in ORCH_DELTAS — switched there, so that a delta built by hand is asked its canary question before any fork
    holds it (notes/plan-delta-layer-tasks.md, task 8)."""
    named = os.environ.get("ORCH_DELTAS")
    if named is None:
        try:
            named = open(os.path.join(STATE, "deltas")).read()
        except OSError:
            named = ""
    return who in named.replace(",", " ").split()


def delta_record(who):
    """The recorded delta of a base, or None: one standing on another layer than the recorded one (refreshed since),
    or on a stable base rebuilt since, is an orphan, and nothing forks it."""
    layer = layer_record(who)
    try:
        delta = json.load(open(os.path.join(STATE, f"{who}-delta.json")))
    except (OSError, ValueError):
        return None
    return delta if layer and delta.get("layer") == layer.get("sessionId") and delta.get("base") == layer.get("base") \
        else None


def base_file(who):
    """What a role of this base forks: its delta when the base is switched to deltas and one stands on its layer, its
    frontier layer when one is recorded, the stable base otherwise. A fork reads the whole prefix under it from cache —
    measured on 2026-09-20: a fork of the sealed knowledge base (a layer over `max` in all but name) read 538,051 of
    its 538,044 tokens and wrote 62 — so what everything forks is what is pinged."""
    if deltas_on(who) and delta_record(who):
        return os.path.join(STATE, f"{who}-delta.json")
    if layer_record(who):
        return os.path.join(STATE, f"{who}-layer.json")
    return os.path.join(STATE, f"{who}-base.json")


def base_record(who):
    """(name, record) of a sealed base or its layer, falling back to the present base while the base topic has not
    built it."""
    for name in (who,) + FALLBACK.get(who, ()):
        try:
            b = json.load(open(base_file(name)))
            return name, {"sid": b["sessionId"], "model": b["model"], "effort": b["effort"], "flags": b.get("flags")}
        except (OSError, ValueError, KeyError):
            continue
    return None, None


def delta_size(who):
    """The tokens a base's standing delta adds to its layer — what every request of a fork of it carries beyond the
    layer, and what a refresh of the layer takes back — or 0 when its roles fork the layer itself."""
    d, layer = delta_record(who), layer_record(who)
    if not d or not layer or not base_file(who).endswith("-delta.json"):
        return 0
    return max(0, int(d.get("context") or 0) - int(layer.get("context") or 0))


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
    """A request read this session's (or base's) cache: its entry lives another TTL. It is the entry that request read,
    and nothing under it: a request reads the longest prefix cached, and a shorter entry under it — the base a session
    forked, the layer under a session, the stable base under a layer — is not kept alive by that read (the max layer's
    refresh of 2026-09-21 wrote its stable base anew). Every request of a session marked its origins too (hit_chain):
    plan-42's 95 requests kept kb-10 looking warm while its entry expired (resumed at 12:54, 527K written anew), and
    design-171's the xhigh layer (review-129.2 and 133.2 forked it at 13:45 and 13:48, 235K each), 2026-09-22 — none
    was pinged, marked warm. A fork's start marks its origin, whose entry its first request reads (start)."""
    if name in BASES:
        for mark in ("hit", "used"):
            path = os.path.join(STATE, f"{name}-base.{mark}")
            open(path, "a").close()
            os.utime(path)
        return
    os.makedirs(os.path.join(STATE, "hits"), exist_ok=True)
    with contextlib.suppress(OSError):
        os.remove(hits(name) + ".miss")  # its request wrote its entry anew: it is pinged again from here
    open(hits(name), "a").close()
    os.utime(hits(name))


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
    sessions = peek()["sessions"]
    rec = sessions.get(name) or {}
    for _ in range(5):
        # a fork of a session — a planner of the knowledge base, a consultation of an author, a continuation (C13) —
        # holds that session's load: its origin's sid names no layer, and manifest.py fell back to the layer standing
        # now, which after a refresh is not what the fork holds
        if rec.get("origin") not in sessions:
            break
        rec = sessions[rec["origin"]]
    return stale(who, tree, rec.get("origin_sid"))


def session_flags():
    """The tools and options every base and every fork of one is started with (session-flags). A fork reads its
    origin's prefix from cache only when it is started with the same ones: the tools are the first thing in it."""
    return open(os.path.join(HERE, "session-flags")).read().split()


def other_tools(rec):
    """Whether a base or a session was started with other tools than session-flags gives now, so that every fork of
    it would write its whole prefix again (about 530K tokens for a base). A record written before the flags were
    recorded (2026-09-21, when the owner left the sessions Bash, TaskCreate, TaskUpdate and TaskStop) was started with
    the old ones."""
    return (rec or {}).get("flags") != " ".join(session_flags())


def fork(org, name, settings, prompt, cwd=None):
    """A session-level fork, with the lean tool set every fork must share and its origin's model and effort; its row
    or None."""
    claude("--bg", "--resume", org["sid"], "--fork-session", *session_flags(), "--model", org["model"],
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


UNSET = object()


def launch(role, key, prompt_of, tree=UNSET, **fields):
    """Fork a session for a piece of work: claim it in the state, fork its origin (never a cold session), confirm it.
    prompt_of(name) gives its first message; `tree` is where it is started, which the caller wrote that message from
    (task_tree for a producing role, when the caller did not decide it; the one tree otherwise). Its name, or None."""
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
    origin = fields.pop("origin", None) or role_layer_of(role) or spec["origin"]
    who, org = origin_of(origin)
    if not org:
        log(f"no {role} started for {key}: its origin {origin} does not exist")
        return None
    if who not in BASES and not warm(who):
        log(f"no {role} started for {key}: {who} is cold")
        return None
    if other_tools(org):
        say_once(f"other-tools-{who}", f"ATTENTION no {role} started: {who} was started with other tools than "
                 "session-flags gives now, and a fork of it would write its whole prefix again — "
                 + (f"build it again (base.sh {who} build, then seal)" if who in BASES else
                    "it goes when the base under it is built again"))
        return None
    settings = fields.pop("settings", None) or spec["settings"] or org.get("settings")
    with state() as st:
        name = fresh_name(st, spec["prefix"], key)
        st["sessions"][name] = dict(name=name, role=role, origin=who, origin_sid=org["sid"], model=org["model"],
                                    effort=org["effort"], settings=settings, state="starting", starting=time.time(),
                                    flags=" ".join(session_flags()), **fields)
        if who in BASES and delta_size(who):
            # what each of its requests carries of the delta: the watchdog weighs it against a refresh (carried)
            st["sessions"][name]["delta_tokens"] = delta_size(who)
        elif (st["sessions"].get(who) or {}).get("role") == "role-layer" and st["sessions"][who].get("delta_tokens"):
            st["sessions"][name]["delta_tokens"] = st["sessions"][who]["delta_tokens"]  # a role layer holds it too
    hit(who)  # its first request reads the entry of what it forks, and only that
    if tree is UNSET:
        tree = task_tree(key)[0] if role in PRODUCING else None
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
    hand_told(name)
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
            st["sessions"][name]["resumed"] = time.time()
        log(f"{name} has running jobs: its message waits as mail")
        hand_told(name)
        return True
    if r:
        claude("stop", r["id"])
        time.sleep(PAUSE)
    with contextlib.suppress(OSError):  # a mark its hook never took ends no turn of the resume (turn_over)
        os.remove(os.path.join(STATE, "flags", f"{s['sid']}.ended"))
    kept = ""
    with contextlib.suppress(OSError):  # the notifications that came while it was parked (notified), given now
        kept = open(notified_path(s["sid"]), errors="ignore").read().strip()
    if kept:
        text += "\n\nWhat Claude Code told you while you were parked:\n" + kept
    started = claude("--bg", "--resume", s["sid"], HARNESS + text, cwd=tree_of(s))
    if started.returncode != 0:
        # Said, not assumed: every caller reads this to decide whether the message it carried still has to be kept
        # (the mail is taken out of the box before the resume), and a session reported resumed that never ran holds
        # its state as working while nothing does it.
        log(f"ATTENTION {name} was not resumed ({(started.stderr or started.stdout).strip()[:120]}): "
            f"{text.split(chr(10), 1)[0][:80]}")
        return False
    if kept:
        with contextlib.suppress(OSError):
            os.remove(notified_path(s["sid"]))
    with open(os.path.join(STATE, f"{name}.woken"), "a") as f:
        f.write(time.strftime("%Y-%m-%dT%H:%M:%S ") + text.split("\n", 1)[0][:100] + "\n")
    with state() as st:
        rec = st["sessions"][name]
        rec["sealed"] = False
        if rec["state"] in ("done", "parked", "waiting", "idle"):
            rec["state"] = "working"
        rec["resumed"] = time.time()  # what it writes from now is this round's (cmd_finalize: a result written)
    hit(name)
    log(f"resumed {name}")
    hand_told(name)
    return True


def job_stale(job, output):
    """A background job whose output file has stood still for JOB_STALE is dead: the session was stopped, or the job
    was, and no completion will come. Without the fallback a job that never reports holds its session's mail and its
    resume for ever (2026-09-20: a stopped job held one for eight hours)."""
    try:
        idle = time.time() - os.path.getmtime(output)
    except (OSError, TypeError):
        # its output's directory gone is the machine restarted under it (/tmp is a tmpfs): implement-163 parked for a
        # run at 12:58 on 2026-09-22, the reboot at 13:04 took the run and its output, and the job counted as running,
        # holding the task parked for the rest of its three hours. A file not written yet, in a directory that is
        # there, is a job just started: nothing to judge it by, and it counts as running.
        if output and output.startswith(CLAUDE_TMP) and not os.path.isdir(os.path.dirname(output)):
            job_ended(job, f"job {job}: its output's directory is gone (the machine restarted); it counts as ended")
            return True
        return False
    if idle > JOB_STALE:
        job_ended(job, f"job {job}: its output has stood still for {int(idle) // 60} minutes; it counts as ended")
        return True
    return False


# where Claude Code writes its sessions' background jobs' output: /tmp/claude-<uid>/, which a reboot clears
CLAUDE_TMP = os.environ.get("ORCH_CLAUDE_TMP", f"/tmp/claude-{os.getuid()}/")


def job_ended(job, text):
    """Said once a day per job: every read of its session's jobs judges it again (the watchdog's pass, a result, a
    resume), and said each time the line filled the log (13:58:26 and 13:58:41 on 2026-09-22)."""
    os.makedirs(os.path.join(STATE, "jobs-ended"), exist_ok=True)
    say_once(os.path.join("jobs-ended", job), text, every=86400)


def notified_path(sid):
    return os.path.join(STATE, "notified", f"{sid}.txt")


def notified(rec, text):
    """Keep a background run's notification that came while its session was parked (ctx_gauge owner): read as the
    run's end by running_jobs, and given to the session when it is resumed (resume)."""
    os.makedirs(os.path.join(STATE, "notified"), exist_ok=True)
    with open(notified_path(rec["sid"]), "a") as f:
        f.write(text.strip() + "\n")
    log(f"{rec['name']}, parked, was told a background run ended: kept for its resume, no request made")


def running_jobs(name):
    """The background jobs a session started that have not completed (from its transcript): stopping the session, to
    seal or to resume it, would kill them."""
    s = peek()["sessions"].get(name) or {}
    try:
        path = transcript(s["sid"])  # a session in a tree has its transcript there: read as "no job", it was sealed
        size = os.path.getsize(path)  # and resumed with its jobs killed
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
    with contextlib.suppress(OSError):  # what came while it was parked, kept rather than put to it (notified)
        text += open(notified_path(s["sid"]), errors="ignore").read()
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
    """What the hooks kept about a session: its guard state (the reads it holds, its counts), its production
    snapshots, its window marks."""
    if not sid:
        return
    for path in (os.path.join(STATE, f"work-{sid}.json"), os.path.join(STATE, f"work-{sid}.json.lock"),
                 os.path.join(STATE, "flags", f"{sid}.soft"), os.path.join(STATE, "flags", f"{sid}.hard"),
                 notified_path(sid)):
        with contextlib.suppress(OSError):
            os.remove(path)
    shutil.rmtree(os.path.join(STATE, f"work-{sid}.snap"), ignore_errors=True)


def release(name):
    """A session nothing refers to any more: stopped, its listing removed, its guard state forgotten.

    What is still in its box was written to a session that was alive and was never read: a resume that failed puts
    the messages back (hand_mail), and from then on nothing tries again. Eight boxes stood that way on 2026-09-20,
    two of them the planner's corrections to fix-48 about the order of the working tree, and nothing said so to
    anybody. deliver() already names mail that arrives after the end; this names mail the end arrives after.

    Without control() it is asked of the supervisor, and nothing is recorded as released here: a session is released
    when it has been stopped, not when stopping it was meant."""
    if not control():
        want(release=name)
        log(f"{name} is to be released: asked of the supervisor, which can stop it")
        return
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
    shutil.rmtree(outputs_of(name), ignore_errors=True)  # its kept outputs, commands and lists: read by it alone
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


# The tools one Isabelle run is made by: a probe, a check, a replay, the repository's build, Isabelle's own. A run is the
# outermost of them among an Isabelle process's ancestors — a replay runs checks, a check runs `isabelle build`, and
# `isabelle build` runs a poly process per session it builds.
RUN_TOOLS = re.compile(r"probe_theories\.py|incremental_check\.py|replay_development_answers\.py|tools/build\.py"
                       r"|\bisabelle\s+(?:build|process|ML_process)\b")
# Two kinds of run, two limits (the owner, 2026-09-21): a probe loads a few theories on top of the base heap and takes
# seconds (3-4 s for every ordinary one that day), so up to PROBE_MAX go at once; a check, a replay or a build is heavy —
# three of them filled 59 of the machine's 60 GiB — and ISABELLE_MAX of them go at once. A run whose command names a
# heavy tool is heavy even if it probes too, and one whose tool is not known is heavy: nothing is counted too light.
PROBE_TOOLS = re.compile(r"probe_theories\.py")
HEAVY_TOOLS = re.compile(r"incremental_check\.py|replay_development_answers\.py|tools/build\.py"
                         r"|\bisabelle\s+(?:build|process|ML_process)\b")
PROBE_MAX = int(os.environ.get("ORCH_PROBE_MAX", 8))
# a probe's own --timeout at most, unless its session holds the machine for a measurement: a probe takes seconds, and
# implement-24's hung at a `have` for its whole 900 s (2026-09-21), holding a run slot, while the result said "timeout"
PROBE_SECONDS = int(os.environ.get("ORCH_PROBE_SECONDS", 60))


# No run starts while the machine's available memory is below this, whatever the counts allow (the owner, 2026-09-21):
# the counts approximate the memory runs take, and a heavy check's main process was measured at 7.5 GB that evening
# on a 60 GiB machine whose 89 GB of swap would slow everything once reached.
MEM_MARGIN_GB = float(os.environ.get("ORCH_MEM_MARGIN_GB", 10))


def memory_available_gb():
    """The machine's available memory in GiB (MemAvailable), or None when it cannot be read. /proc/meminfo is the
    machine's inside a session's sandbox too. ORCH_MEM_AVAILABLE_GB states it instead (the tests)."""
    stated = os.environ.get("ORCH_MEM_AVAILABLE_GB")
    if stated is not None:
        return float(stated)
    try:
        for line in open("/proc/meminfo"):
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) / (1024 * 1024)
    except (OSError, ValueError, IndexError) as e:
        say_once("meminfo-unreadable", f"ATTENTION the machine's memory cannot be read, so no run waits for it: {e!r}")
    return None


def memory_short():
    """Why no run may start for want of memory, or None: a machine whose memory cannot be read is not called full —
    that is a broken machine, and the counts still hold."""
    avail = memory_available_gb()
    if avail is not None and avail < MEM_MARGIN_GB:
        return (f"The machine has {avail:.1f} GiB of memory available, below the {MEM_MARGIN_GB:g} GiB a run must leave "
                "free.")
    return None


def run_kind(command):
    """"probe" or "heavy": the kind of the run a command (or a run's root process) makes."""
    return "probe" if PROBE_TOOLS.search(command or "") and not HEAVY_TOOLS.search(command or "") else "heavy"


def machine_processes():
    """{pid: (parent, name, command line)} of every process on this machine that can be read."""
    out = {}
    for pid in filter(str.isdigit, os.listdir("/proc")):
        with contextlib.suppress(OSError, ValueError, IndexError):
            stat = open(f"/proc/{pid}/stat").read()
            parent = int(stat[stat.rindex(")") + 2:].split()[1])
            cmd = open(f"/proc/{pid}/cmdline", "rb").read().replace(b"\0", b" ").decode(errors="ignore").strip()
            out[int(pid)] = (parent, open(f"/proc/{pid}/comm").read().strip(), cmd)
    return out


def claude_process(name, cmd):
    """Whether a process is Claude Code itself (by its name, or its command: `claude …`, or a versioned binary)."""
    return name == "claude" or cmd.startswith("claude ") or "/claude/versions/" in cmd


def run_tool(procs, pid):
    """Whether a process runs one of RUN_TOOLS: a shell, a Python tool or the sandbox around a session's command — not
    a Claude Code session, whose prompt names `tools/incremental_check.py` in its brief and which lives as long as it."""
    _, name, cmd = procs[pid]
    return not claude_process(name, cmd) and RUN_TOOLS.search(cmd) is not None


def outermost_tool(procs, pid):
    """The outermost ancestor of a process (itself included) that runs one of RUN_TOOLS, or the process itself."""
    root, p, seen = pid, procs[pid][0], 0
    while p in procs and seen < 100:
        if run_tool(procs, p):
            root = p
        p, seen = procs[p][0], seen + 1
    return root


def isabelle_run_roots(procs):
    """{Isabelle process: the run it belongs to} — the outermost ancestor running one of RUN_TOOLS, or the process itself
    when none does, so that work whose tool is not known still counts as a run of its own."""
    return {pid: outermost_tool(procs, pid) for pid, (_, name, _) in procs.items() if name == "poly"}


def run_roots(procs):
    """Every run going: each Isabelle process's (isabelle_run_roots), and each tool's that runs whether or not an
    Isabelle shows under it now. A replay runs Isabelle in phases, and a check prepares before its Isabelle starts:
    between them a session's run was in no count — a mark counts until a snapshot shows its run once (session_marks) —
    and batch 255 started beside train 223's check and fix-263's replay, three heavy runs at 3 GiB (2026-09-22 19:40)."""
    return set(isabelle_run_roots(procs).values()) | {outermost_tool(procs, pid) for pid in procs if run_tool(procs, pid)}


def isabelle_load():
    """{"heavy": the heavy runs going, "probe": the probes going}; a run a finalizer has just been let start whose
    Isabelle may not show yet (isabelle_admitted) is a heavy one, a check. ORCH_ISABELLE_RUNS and ORCH_PROBE_RUNS state
    them instead where the machine's own are not the subject (the tests). Inside a session's sandbox, which sees no
    process of the machine, the watchdog's snapshot is read, and one too old to trust counts the machine as full."""
    stated, probes = os.environ.get("ORCH_ISABELLE_RUNS"), os.environ.get("ORCH_PROBE_RUNS")
    if stated is not None:
        return {"heavy": int(stated) + isabelle_admitted(), "probe": int(probes or 0)}
    if not control():
        with contextlib.suppress(OSError, ValueError, KeyError):
            path = os.path.join(STATE, "isabelle-processes.json")
            snap = json.load(open(path))
            if time.time() - os.path.getmtime(path) < SNAPSHOT_FRESH:
                return {"heavy": int(snap.get("heavy", snap["runs"])) + isabelle_admitted(),
                        "probe": int(snap.get("probes", 0))}
        return {"heavy": ISABELLE_MAX + isabelle_admitted(), "probe": PROBE_MAX}
    procs = machine_processes()
    kinds = [run_kind(procs.get(root, (0, "", ""))[2]) for root in run_roots(procs)]
    return {"heavy": kinds.count("heavy") + unseen_finalizer_runs(procs) + session_marks(), "probe": kinds.count("probe")}


def isabelle_runs():
    """Every Isabelle run going on this machine, heavy and probes (isabelle_load), and the runs a finalizer has just
    been let start: what a measurement or a check that advances the base must have none of.

    It counted poly processes until 2026-09-21, against a limit in runs (ISABELLE_MAX: three runs filled the machine's
    memory): one run makes several — `isabelle build` one per session it builds — and a session's probe was refused as
    "11 Isabelle runs are going" while two were, then 10, 9, 7, 3 as the check's sessions finished (implement-78)."""
    # inside a session's sandbox its own process namespace shows no Isabelle at all: `v2.py park machine` answered "a
    # run may start now" while the guard, outside, refused the probe after it as "2 Isabelle runs are going", four
    # times (implement-24, 2026-09-21): isabelle_load reads the watchdog's snapshot there, and what cannot be seen is
    # never free
    load = isabelle_load()
    return load["heavy"] + load["probe"]


SNAPSHOT_FRESH = 180  # the watchdog writes the machine's runs every minute (watchdog.isabelle_snapshot)


def run_blocked(own=(), kind="heavy"):
    """Why a run of a kind ("probe" or "heavy") may not start now for the tasks `own` (a session's task, and the one it
    reviews), or None: another task holds the machine for a measurement, or its kind's limit is reached. The guard
    refuses a session's check for it, and a session parked for the machine is resumed once it is None."""
    claim = exclusive_claim()
    if claim and claim["task"] not in own:
        return f"Task {claim['task']} holds the machine ({claim['why']}): nothing else runs meanwhile."
    if claim:
        # the machine is its own: no task waiting ahead of it counts, since none of them can start until it has run —
        # fix-274 held the claim parked, not resumed, while task 271's finalizer, ahead in the order, waited on that
        # claim: ten idle minutes, until the unseen claim lapsed (2026-09-22 20:37-20:47)
        return None
    pending = pending_claim()
    if pending and pending["task"] not in own:
        return (f"Task {pending['task']} waits to measure on this machine ({pending['why']}): no new run starts until "
                "the runs going have ended and it has measured.")
    if kind != "probe":
        ahead = machine_ahead(peek(), [x for x in own if x])
        if ahead:
            return (f"Task {ahead} waits for a heavy run ahead of yours in the planner's order: the machine goes in "
                    "that order, finalizers' checks and landings included.")
    load = isabelle_load()
    if kind == "probe" and load["probe"] >= PROBE_MAX:
        return f"{load['probe']} probes are going on this machine (at most {PROBE_MAX})."
    if kind != "probe" and load["heavy"] >= ISABELLE_MAX:
        return (f"{load['heavy']} heavy Isabelle runs (checks, replays, builds) are going on this machine (at most "
                f"{ISABELLE_MAX}: three have filled its memory).")
    return memory_short()


# The machine goes in the planner's order, finalizers included (the owner, 2026-09-22): a finalizer took a freed heavy
# slot within POLL seconds, while a task parked for the machine waited to be resumed by a dispatch and then for its
# session's call — task 94 waited two hours behind landings on 2026-09-22. A task waits for a heavy run as a finalizer
# waiting to start its check (MACHINE_WAIT, touched each poll: machine_waiting), as a task resumed for the machine whose check has not
# started yet (MACHINE_TURN, TURN_GRACE at most), or as a task parked for the machine while a slot is free to resume it;
# none starts a heavy run while one ahead of it in the queue waits (machine_ahead).
MACHINE_WAIT, MACHINE_TURN = os.path.join(STATE, "machine-wait"), os.path.join(STATE, "machine-turn")
WAIT_FRESH, TURN_GRACE = 60, 180


def machine_waiters(st):
    """{task: since when} of the tasks waiting for a heavy run (see MACHINE_WAIT)."""
    now, out = time.time(), {}
    for where, fresh in ((MACHINE_WAIT, WAIT_FRESH), (MACHINE_TURN, TURN_GRACE)):
        with contextlib.suppress(OSError):
            for tid in os.listdir(where):
                with contextlib.suppress(OSError, ValueError):
                    at = os.path.getmtime(os.path.join(where, tid))
                    if now - at < fresh:
                        out[tid] = min(out.get(tid, at), float(open(os.path.join(where, tid)).read() or at))
    if not at_capacity(st) and len(producing(st)) < PRODUCERS_MAX:  # a slot could resume it now
        for tid, t in st["tasks"].items():
            p = t.get("parked") or {}
            if t.get("stage") == "parked" and p.get("for") == "machine" and (p.get("run") or "heavy") != "probe":
                out.setdefault(tid, p.get("since") or now)
    return out


def machine_ahead(st, own):
    """The task waiting for a heavy run ahead of `own` (a task, or its task and the one it reviews) in the planner's
    order — its place in the queue, then how long it has waited — or None."""
    queue, waiters = st.get("queue") or [], machine_waiters(st)
    place = lambda tid, at: (queue.index(tid) if tid in queue else len(queue), at)
    mine = min((place(x, waiters.get(x, time.time())) for x in own), default=(len(queue), time.time()))
    ahead = sorted((place(tid, at), tid) for tid, at in waiters.items() if tid not in own and place(tid, at) < mine)
    return ahead[0][1] if ahead else None


def machine_waiting(tid, waiting=True):
    """A finalizer waits for a heavy run (touched each poll: a finalizer gone leaves it stale), or no longer does."""
    path = os.path.join(MACHINE_WAIT, tid)
    if waiting:
        os.makedirs(MACHINE_WAIT, exist_ok=True)
        since = open(path).read() if os.path.exists(path) else str(time.time())
        open(path, "w").write(since)
    else:
        with contextlib.suppress(OSError):
            os.remove(path)


def machine_turn(tid, taken=False):
    """A task resumed for the machine holds its turn until its session's check is let start (admit_session)."""
    path = os.path.join(MACHINE_TURN, tid)
    if taken:
        with contextlib.suppress(OSError):
            os.remove(path)
    else:
        os.makedirs(MACHINE_TURN, exist_ok=True)
        open(path, "w").write(str(time.time()))


ADMITTED = os.path.join(STATE, "isabelle-admitted")  # a file per run a finalizer is starting (finalize.wait_for_isabelle)
ADMIT_GRACE = float(os.environ.get("ORCH_ADMIT_GRACE", 60))  # time enough for a check to reach its Isabelle


SESSION_MARK = "session-"  # a heavy check a session's guard let start (admit_session)
SESSION_GRACE = 600  # a session's mark counts until its run shows (session_marks), never past this


def unseen_finalizer_runs(procs):
    """The runs finalizers have been let start whose Isabelle is not among the machine's processes yet: an admission
    counts while its finalizer lives and no poly descends from it. It counted ADMIT_GRACE (60 s) and then only the
    processes — but a check prepares for minutes before its Isabelle starts, and three finalizers' checks were let
    start one after another as each earlier admission lapsed (tasks 115, 97, 106 at 05:54:42, 05:55:42 and 05:57:40 on
    2026-09-22), the machine at 2.2 GiB."""
    try:
        names = [n for n in os.listdir(ADMITTED) if not n.startswith(SESSION_MARK)]
    except OSError:
        return 0
    lines = set()  # what runs, and everything above it: a runner with a run under it is counted by that run
    for pid, (_, name, _) in procs.items():
        if name == "poly" or run_tool(procs, pid):
            p, seen = pid, 0
            while p in procs and seen < 100:
                lines.add(p)
                p, seen = procs[p][0], seen + 1
    n = 0
    for tid in names:
        # the process that was let start the run: a landing train's or a check batch's lander admits its run under its
        # first member's name, and runs it itself — the member's own finalizer, which runs nothing, made the one run
        # count twice (the train of 144 and 132, 2026-09-22 14:42); a marker a finalizer since ended left (173's, its
        # finalizer stopped at 14:26) counted as a run of the one started after it, and seven checks waited behind it
        marker = os.path.join(ADMITTED, tid)
        try:
            owner = open(marker).read().strip()
            runner = int(owner) if owner.isdigit() else None
            if runner is None:  # a marker from before it named its runner: the task's finalizer, if it is the one
                record = os.path.join(BUILD, tid, "finalizer.pid")
                if os.path.getmtime(marker) < os.path.getmtime(record):
                    continue  # written for a finalizer before the one on record
                runner = int(open(record).read().split()[0])
        except (OSError, ValueError, IndexError):
            continue  # no runner on record: nothing of it runs
        n += runner in procs and runner not in lines
    return n


def session_marks():
    """The heavy checks sessions' guards let start that the watchdog's snapshot does not show yet (admit_session): a
    mark counts until the snapshot holds a heavy run inside a session's sandbox that started after it, each run
    answering one mark, SESSION_GRACE at most. It counted until a snapshot SEEN_AFTER (90 s) newer — twice meanwhile
    once its run showed (implement-30 was told of 3 heavy runs where 2 went, 2026-09-22 07:55), and not at all while a
    check still prepared past it, as the finalizers' did (unseen_finalizer_runs)."""
    try:
        names = [n for n in os.listdir(ADMITTED) if n.startswith(SESSION_MARK)]
    except OSError:
        return 0
    path = os.path.join(STATE, "isabelle-processes.json")
    try:
        taken = os.path.getmtime(path)
        runs = sorted(r["started"] for r in json.load(open(path)).get("roots", [])
                      if r.get("kind") == "heavy" and r.get("session") and r.get("started"))
    except (OSError, ValueError, KeyError, TypeError):
        taken, runs = 0, []
    marks, now = [], time.time()
    for name in names:
        with contextlib.suppress(OSError):
            mark = os.path.join(ADMITTED, name)
            at = os.path.getmtime(mark)
            if now - at > SESSION_GRACE:
                os.remove(mark)
            else:
                marks.append(at)
    n, used = 0, set()
    for at in sorted(marks):
        run = next((i for i, started in enumerate(runs) if i not in used and started >= at - 10), None)
        if run is not None and taken > at:
            used.add(run)  # its run shows: counted there
        else:
            n += 1
    return n


def process_started(pid):
    """When a process of this machine started (epoch seconds), or None when it cannot be read."""
    try:
        stat = open(f"/proc/{pid}/stat").read()
        ticks = int(stat[stat.rindex(")") + 2:].split()[19])
        boot = next(int(line.split()[1]) for line in open("/proc/stat") if line.startswith("btime"))
        return boot + ticks / os.sysconf("SC_CLK_TCK")
    except (OSError, ValueError, IndexError, StopIteration):
        return None


def isabelle_admitted():
    """The runs a finalizer has been let start and whose Isabelle may not be among the machine's processes yet: each
    counts from its admission until its finalizer ends, ADMIT_GRACE at most. On 2026-09-21 three finalizers started in
    one second each counted no run, since none had started one yet, and three checks ran against a limit of two — and
    each one's host tests failed under the load, though they pass alone. A heavy check a session's guard let start
    counts until the watchdog's snapshot, which a sandboxed guard reads, shows its run (session_marks): two sessions'
    checks and a landing check ran together within one snapshot's life on 2026-09-22 (05:43, 6 GiB left)."""
    try:
        names = [n for n in os.listdir(ADMITTED) if not n.startswith(SESSION_MARK)]
    except OSError:
        return 0
    now, n = time.time(), 0
    for name in names:
        with contextlib.suppress(OSError):
            n += now - os.path.getmtime(os.path.join(ADMITTED, name)) < ADMIT_GRACE
    return n + session_marks()


@contextlib.contextmanager
def admission():
    """The lock under which the start of a run is decided and marked: finalize.wait_for_isabelle, and the guard for a
    session's check, so that two deciding at once do not both see room for one run."""
    os.makedirs(STATE, exist_ok=True)
    with open(os.path.join(STATE, "isabelle-admit.lock"), "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        yield


def admit_session(name, task=None):
    """A session's heavy check is let start: it counts as a run until the snapshot shows it (isabelle_admitted), and
    its task's turn at the machine is taken (machine_turn)."""
    os.makedirs(ADMITTED, exist_ok=True)
    open(os.path.join(ADMITTED, SESSION_MARK + (name or "unnamed")), "w").close()
    if task:
        machine_turn(task, taken=True)


EXCLUSIVE = "isabelle-exclusive"
CLAIM_GRACE = float(os.environ.get("ORCH_CLAIM_GRACE", 180))  # to launch the run a session has claimed the machine for
# A measurement queued and then given comes to its session by mail, read at its next tool call: design-171 was given the
# machine at 11:39:04 four minutes into a request that went on four more, and the grace, counted from the grant, cleared
# the claim at 11:42:05 before it had read it — it was refused its run (memory), refused again (a probe's bound
# without the machine), claimed again and waited ten minutes more (2026-09-22). The grace counts from its reading.
CLAIM_UNSEEN = float(os.environ.get("ORCH_CLAIM_UNSEEN", 600))  # at most, for a given claim its session has not read


def claim_exclusive(tid, why, pid=None, session=None, seen=True):
    """Hold the machine for one task: its final check while it advances the base heap, or a session's run whose result
    is a timing, which a neighbour would distort as surely as it would exceed the memory. `seen`: the session has been
    told (its own `measuring`, or a resume that says so); a grant told by mail is not until its next tool call."""
    json.dump({"task": tid, "why": why, "pid": pid, "session": session, "at": time.time(), "seen": seen},
              open(os.path.join(STATE, EXCLUSIVE), "w"))


MEASURE_MAX = int(os.environ.get("ORCH_MEASURE_MAX", 600))  # a session's hold on the machine, at most, under the switch


def measure_bound():
    """The owner's to set (notes/plan-orchestrator-concepts.md C14), off unless state/measure-bound exists or
    ORCH_MEASURE_BOUND=1: a session's measurement holds the machine for MEASURE_MAX at most. The 37 holds of 09-20/22
    took 3.0 hours, and the machine emptied for them 1.5 hours more; four held it past ten minutes, 1.1 hours between
    them — the longest, 31 minutes, one probe that loaded its theories and then timed one judgment, every check of the
    run waiting behind it."""
    return os.environ.get("ORCH_MEASURE_BOUND") == "1" or os.path.exists(os.path.join(STATE, "measure-bound"))


def measure_lapsed(claim):
    """What its session is told when a session's claim has passed MEASURE_MAX under the switch, or ""."""
    if not measure_bound() or not claim.get("session") or claim.get("pid"):
        return ""  # a check that advances the base holds it as long as it runs: only a session's timing is bounded
    since = claim.get("call_at") or claim.get("at") or time.time()
    if time.time() - since <= MEASURE_MAX:
        return ""
    return (f"Your measurement has held the machine for {MEASURE_MAX // 60} minutes, the most a measurement holds it: "
            f"the claim lapsed at {time.strftime('%H:%M')}, and other runs may start beside it from now, so what it "
            "times after this moment is not a held number. Time the one judgment or part the measurement is for — its "
            "theories loaded before the timing begins, which needs no hold — and claim the machine again for that.")


def claim_seen(name):
    """A session has read that the machine is its own (ctx_gauge, when its mail says so): its grace starts now."""
    path = os.path.join(STATE, EXCLUSIVE)
    try:
        claim = json.load(open(path))
    except (OSError, ValueError):
        return
    if isinstance(claim, dict) and claim.get("session") == name and not claim.get("seen", True):
        claim.update(seen=True, at=time.time())
        json.dump(claim, open(path, "w"))


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
    if claim.get("pid") and not control():
        # Inside Claude Code's sandbox no process but the command's own is visible, so the finalizer holding this
        # claim reads as gone: a producing session's `measuring` deleted its claim and took the machine beside the
        # final check (found 2026-09-21, before it ran). What cannot be seen here is judged by the supervisor.
        return claim
    lapsed = measure_lapsed(claim)
    if lapsed:
        try:
            os.remove(path)
        except OSError:
            return None  # another reader lapsed it, and said so
        log(f"the measurement of task {claim.get('task')} held the machine past {MEASURE_MAX // 60} min: its claim lapses")
        with contextlib.suppress(OSError):
            start = claim.get("call_at") or claim.get("at") or time.time()
            with open(os.path.join(BUILD, str(claim.get("task")), "measurements.log"), "a") as f:
                f.write(f"{time.strftime('%Y-%m-%dT%H:%M:%S', time.localtime(start))} to {time.strftime('%H:%M:%S')}: "
                        f"the machine held for {claim.get('why', 'a measurement')} until the bound of "
                        f"{MEASURE_MAX // 60} min lapsed it; other runs may have started beside it from then\n")
        deliver(claim["session"], "the harness", lapsed)
        return None
    grace = CLAIM_GRACE if claim.get("seen", True) else CLAIM_UNSEEN  # counted from its reading (claim_seen)
    alive = (claim.get("pid") and os.path.exists(f"/proc/{claim['pid']}")) or (
        claim.get("session") and (running_jobs(claim["session"]) or time.time() - claim.get("at", 0) < grace
                                  or (claim.get("call") and time.time() - claim.get("call_at", 0) < CALL_MAX)))
    if alive:
        return claim
    with contextlib.suppress(OSError):
        os.remove(path)
        log(f"cleared the machine's claim by task {claim.get('task')}: what held it is gone")
    return None


# A measurement run in the foreground is no job of its session: its hold stood CLAIM_GRACE from the grant and no longer,
# whatever the run did. It idled the machine after a short run — fix-220's 17 s timing held it until 17:25:07, three
# minutes, while two checks waited — and let others start beside a long one: task 128's pair of about 200 s lost its
# hold at 189 s (2026-09-22; seventeen measurements that day, every hold ended so). The call that runs it holds the
# machine from its start to its end (work_meter: claim_call as the guard lets it through, release_claim after it).
CALL_MAX = float(os.environ.get("ORCH_CLAIM_CALL_MAX", 1200))  # a call is bounded at 600 s; past this it is gone


def claim_call(tid, call):
    """The measurement of task tid runs in this call of its session: its hold stands until the call ends."""
    path = os.path.join(STATE, EXCLUSIVE)
    try:
        claim = json.load(open(path))
    except (OSError, ValueError):
        return
    if isinstance(claim, dict) and claim.get("task") == tid and call:
        claim.update(call=call, call_at=time.time())
        json.dump(claim, open(path, "w"))


def release_claim(call):
    """The call that ran a measurement has ended: so has the hold on the machine."""
    path = os.path.join(STATE, EXCLUSIVE)
    try:
        claim = json.load(open(path))
    except (OSError, ValueError):
        return
    if isinstance(claim, dict) and call and claim.get("call") == call:
        with contextlib.suppress(OSError):
            os.remove(path)
        log(f"the measurement of task {claim.get('task')} ended with the call that ran it "
            f"({round(time.time() - claim.get('call_at', time.time()))} s): the machine is free")
        with contextlib.suppress(OSError):  # a durable record in the task's folder, which its review reads (#129's
            # review: "a measuring claim leaves no durable record", 2026-09-22)
            start = claim.get("call_at", time.time())
            os.makedirs(os.path.join(BUILD, str(claim.get("task"))), exist_ok=True)
            with open(os.path.join(BUILD, str(claim.get("task")), "measurements.log"), "a") as f:
                f.write(f"{time.strftime('%Y-%m-%dT%H:%M:%S', time.localtime(start))} to "
                        f"{time.strftime('%H:%M:%S')} ({round(time.time() - start)} s): the machine held for "
                        f"{claim.get('why', 'a measurement')}, no other run beside it\n")
        kick()  # what waited for it — a queued probe, a batch, a parked session — goes at once


def exclusive_holder():
    claim = exclusive_claim()
    return claim["task"] if claim else None


# A measurement claimed while runs were going was refused, to be claimed "when they have ended" — and nothing held new
# runs back meanwhile, while a session parked for the machine was resumed as soon as a heavy slot was free: task 56
# was told three times that a run could start, claimed the machine for a fifteen-second timing, and was refused, other
# runs going each time (2026-09-22). Now it is queued: no new run of another task starts, and once the machine is
# empty the claim is the session's, given to it by message, or with its resume if it parked for the machine.
PENDING = "isabelle-exclusive-pending"
PENDING_MAX = int(os.environ.get("ORCH_MEASURE_WAIT", 1800))  # how long a queued measurement holds new runs back
MACHINE_YOURS = ("The machine is yours for your measurement ({why}): launch it now, within {minutes} minutes, and record "
                 "the numbers it gives before you park or produce; the hold ends with your run. Continue task {tid}.")


def pending_claim():
    """The measurement queued for the machine to empty, or None: it stands while its session does, and PENDING_MAX."""
    path = os.path.join(STATE, PENDING)
    try:
        p = json.load(open(path))
    except (OSError, ValueError):
        return None
    s = peek()["sessions"].get(p.get("session") or "") or {}
    over = time.time() - p.get("at", 0) > PENDING_MAX
    if over or s.get("released") or s.get("state") not in LIVE + ("parked", "idle"):
        with contextlib.suppress(OSError):
            os.remove(path)
        log(f"the measurement queued by task {p.get('task')} is given up: "
            + (f"it waited {PENDING_MAX // 60} minutes" if over else "its session is gone"))
        return None
    return p


def grant(p, seen=False):
    """A queued measurement given the machine: told by mail (grant_pending), read at the session's next tool call, or
    with its resume (`seen`: produce)."""
    claim_exclusive(p["task"], p["why"], session=p["session"], seen=seen)
    with contextlib.suppress(OSError):
        os.remove(os.path.join(STATE, PENDING))
    log(f"task {p['task']} holds the machine for a measurement: {p['why']} (queued since "
        f"{time.strftime('%H:%M:%S', time.localtime(p.get('at', time.time())))})")


def grant_pending():
    """The queued measurement, given once the machine is empty, to a session that is not parked for it (a parked one is
    resumed with it by the producing slot: produce)."""
    p = pending_claim()
    if not p or exclusive_claim() or isabelle_runs():
        return
    if (peek()["sessions"].get(p["session"]) or {}).get("state") == "parked":
        return
    grant(p)
    deliver(p["session"], "the harness", MACHINE_YOURS.format(why=p["why"], minutes=int(CLAIM_GRACE) // 60,
                                                              tid=p["task"]))


def working(st):
    """The sessions doing work now, over every slot: producing, supporting, a quick fix and the consultations. Neither
    the knowledge base nor the planner is one of them — they are the deliberative half, one session each, and gating
    them behind the rate would make the planner answer an event only when a producer happened to stop (the owner,
    2026-09-20: the planner works problem by problem and stays responsive). A parked session is not working either."""
    return [n for n, s in st["sessions"].items()
            if s.get("state") in LIVE and s.get("role") not in ("kb", "planner") and not s.get("released")]


def support_apart():
    """The owner's to set (notes/plan-orchestrator-concepts.md C6), off unless state/support-apart exists or
    ORCH_SUPPORT_APART=1 (a file, so that the daemon and every command read the same): the supporting session (a review
    or a brief) outside the worker cap, in a slot of its own, so that two producers and a review work at once. On
    2026-09-22 both workers were busy 47% of the minutes and a task waited 8.5% of its way for its review; the
    machine's two heavy runs were busy 1.2–1.6 of 2 from 15:00, which is what a third session is worth against."""
    return os.environ.get("ORCH_SUPPORT_APART") == "1" or os.path.exists(os.path.join(STATE, "support-apart"))


OCCUPANCY = "occupancy.log"  # a line a minute, written by the watchdog: when, sessions working, tasks held (sample_occupancy)


def sample_occupancy(now=None):
    """One minute of the run, as the planner's status reads it back (occupancy_text): how many sessions work, and how
    many queued tasks that have not started wait only on blockers past their result — in their check, their review,
    their quick fix or their landing. In the afternoon of 2026-09-22 fewer than two sessions worked in 349 of 638
    minutes, and in 246 of them such a task waited (the plan's finding 11): what the status showed was the moment,
    never the hour."""
    st = peek()
    busy, held = len(working(st)), 0
    for tid in st.get("queue") or []:
        if (st["tasks"].get(tid) or {}).get("stage") not in (None, "ready"):
            continue
        open_ = [b for b in (read_task(tid) or {}).get("blockedBy") or [] if (read_task(b) or {}).get("status") != "completed"]
        held += bool(open_) and all((st["tasks"].get(b) or {}).get("stage") in FINISHING for b in open_)
    path = os.path.join(STATE, OCCUPANCY)
    lines = open(path).read().splitlines()[-2000:] if os.path.exists(path) else []
    open(path, "w").write("\n".join(lines + [f"{int(now or time.time())} {busy} {held}"]) + "\n")


def occupancy_text(now=None):
    """The last hour of sample_occupancy, for the planner's status: "" with less than half an hour of samples."""
    now = now or time.time()
    try:
        rows = [tuple(map(int, l.split())) for l in open(os.path.join(STATE, OCCUPANCY)) if l.strip()]
    except (OSError, ValueError):
        return ""
    rows = [r for r in rows if len(r) == 3 and now - 3600 <= r[0] <= now]
    if len(rows) < 30:
        return ""
    free = sum(1 for _, busy, held in rows if busy < WORKERS_MAX and held)
    return (f"the last hour: {sum(r[1] for r in rows) / len(rows):.1f} of {WORKERS_MAX} sessions working on average"
            + (f"; in {free} of its {len(rows)} minutes a slot stood free while a task waited only on work in its check, "
               "its review or its landing — what the graph's width decides" if free else ""))


CHECK_PASSED = "Its check has passed; the verdicts of its reviews decide whether it is committed."
CHECK_BESIDE = ("Its check runs beside your review: it is committed only once that check passes and every review "
                "accepts, an accept of work that then fails its check is void and the fix is reviewed again, and a "
                "rejection reaches the session with the check's failure, if it fails, in one fix round. The end of its "
                "finalizer's log, read for you below, may not be there yet, or may be an earlier check's.")


def review_beside_check():
    """The owner's to set (notes/plan-orchestrator-concepts.md C9), off unless state/review-beside-check exists or
    ORCH_REVIEW_BESIDE_CHECK=1: a build's or a fix's review starts when its result is recorded, beside its check,
    rather than after it. From result to commit the afternoon of 2026-09-22 took a median 18.4 minutes; started at the
    result, its review would have ended a median 8.2 minutes sooner. An accept waits for the check to pass and is void
    if it fails (the fix is reviewed again); a rejection waits for the check's end and joins its failure, if any, in
    one fix round."""
    return os.environ.get("ORCH_REVIEW_BESIDE_CHECK") == "1" or os.path.exists(os.path.join(STATE, "review-beside-check"))


def at_capacity(st, support=False):
    """Whether the worker cap is reached for a session of the kind asked: apart (support_apart), the supporting
    session neither counts against the others nor waits for them (one at a time still: slot)."""
    apart = support_apart()
    if apart and support:
        return False
    busy = working(st)
    if apart:
        busy = [n for n in busy if (st["sessions"].get(n) or {}).get("role") not in SUPPORTING]
    return len(busy) >= WORKERS_MAX


# Both slots may produce (the owner, 2026-09-22): they were one producing and one supporting, and on 2026-09-22 two
# implementers waited for the one producing slot a designer held while the machine stood idle. WORKERS_MAX still bounds
# every working session; a waiting review takes a free slot before a second producer does (produce), since a finished
# task lands only once it is reviewed.
PRODUCERS_MAX = int(os.environ.get("ORCH_PRODUCERS", 2))


def producing(st):
    """The producing sessions live now (a quick fix is its own slot, as slot() reads it)."""
    return [s for s in st["sessions"].values()
            if s["role"] in PRODUCING and s["state"] in LIVE and not s.get("fix") and not s.get("released")]


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


def sandbox_mount(tree, path):
    """Whether an untracked path (git's `??`) is one of the files the sandbox mounts over a session's working
    directory — .bashrc, .bash_profile, .gitconfig, .mcp.json and the like, at the tree's top, a device inside the
    sandbox and an empty file outside it — and so no one's change: taken by `--files`'s default they would have been
    committed, and listed as the tree's uncommitted work they are noise (not_added reads git's refusal of them the
    same way)."""
    full = os.path.join(tree, path)
    return "/" not in path and path.startswith(".") and (not os.path.isfile(full) or os.path.getsize(full) == 0)


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


def changed_paths(tree=None, among=None):
    """Every path of the working tree that differs from HEAD (modified, added, deleted, untracked), exempt ones left out;
    or, `among` given, those of these paths that differ, exempt or not."""
    out = git_out("status", "--porcelain=v1", "-z", "--untracked-files=all", *(("--", *among) if among else ()),
                  tree=tree) or ""
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
        if code == "??" and not among and sandbox_mount(tree or PROJECT, path):
            continue  # the sandbox's, over the working directory: no one's change (sandbox_mount)
        paths.append(path)
    return sorted({p for p in paths if among or not exempt(p)})


def lands_when_free():
    """A task kept out of main only by the one tree's uncommitted changes past its commit's budget
    (finalize.standing_refused) lands again by itself once they are committed: its commit is made again with no
    session, as queueing it does (cmd_queue). The planner was told to queue it then, and so had to watch the one tree
    for the moment: task 32 waited 60 minutes on task 62's ROOT and THEORY_MAP.md at 02:57 on 2026-09-22, and task
    24 had sat with the planner after what it waited for was committed (2026-09-21). A task dropped (drop) has lost
    its mark: the planner re-plans it."""
    st = peek()
    for tid, t in list(st["tasks"].items()):
        if not (t.get("lands_again") and t.get("stage") == "planner"):
            continue
        tree = worktree_of(tid)
        try:
            files = list(json.load(open(os.path.join(BUILD, tid, "finalize.json")))["files"])
        except (OSError, ValueError, KeyError):
            continue
        if tree == PROJECT or not os.path.isdir(tree):
            continue  # only a task in its own tree is kept out so, and its tree holds the commit it lands from
        handoff = subprocess.run(["git", "-C", tree, "status", "--porcelain", "--", "HANDOFF.md"], capture_output=True,
                                 text=True, timeout=60).stdout.strip()
        standing = one_tree_changes(files + (["HANDOFF.md"] if handoff and "HANDOFF.md" not in files else []))
        if standing:
            continue
        with state() as w:
            t = w["tasks"].get(tid) or {}
            if not (t.get("lands_again") and t.get("stage") == "planner" and review_accepted(w, tid)):
                continue
            why = t.get("lands_again_why")
            w["tasks"][tid] = {k: v for k, v in t.items() if k not in ("lands_again", "lands_again_why",
                                                                        "finishing_since")}
            w["tasks"][tid]["stage"] = "committing"
            event(w, "the harness", f"Task {tid} lands again by itself: " + (
                "other landings held main past its commit's budget, and it tries again" if why == "main" else
                "what stood uncommitted in the one tree over its files is committed now") +
                ". Its commit is made again, with no session; nothing is yours to do for it.")
        log(f"task {tid}: what kept it out of main is committed; its commit is made again, as it stands")
        background("finalize.py", "commit", tid)


def one_tree_changes(paths):
    """{path: task, or None when no task wrote it} of these paths that stand changed and uncommitted in the one tree. A
    task in its own tree lands by a merge into the one tree, and git refuses a merge that would overwrite a working
    change: on 2026-09-21 task 24's landing met task 54's uncommitted THEORY_MAP.md, which 54 committed 56 seconds
    later."""
    changed = changed_paths(among=[os.path.normpath(p) for p in paths]) if paths else []
    with owners(write=False) as o:
        return {p: o.get(p) for p in changed}


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
    if apart((rec or {}).get("task")):
        return None  # its own tree: nothing that holds the one tree holds it
    for tid, t in st["tasks"].items():
        if tid in own or apart(tid):
            continue  # a task in its own tree checks and parks there, and holds nothing of the one tree
        if t.get("stage") == "checking" and os.path.exists(os.path.join(BUILD, tid, "finalize.json")):
            return tid  # its check is running and sees the working tree, which must hold its changes alone
        if t.get("stage") == "parked" and (t.get("parked") or {}).get("holds_tree"):
            return tid  # parked for its own run, which reads its changes in the working tree
    writer = tree_writer(st)  # its installed work stands in the tree until it commits: another task drafts meanwhile
    return writer if writer and writer not in own else None


def locked_files(st, rec):
    """{file: task} of the finalizations in flight in the one tree that are not this session's own: their files are
    theirs until they are committed, while the rest of the working tree stays open (only a running check holds it
    whole). A task in its own tree holds none of the one tree's files: its commit is made in its tree and carries
    nothing written here, and its landing waits for what stands here uncommitted in the files it writes
    (finalize.committed_run) — implement-54 was refused THEORY_MAP.md for task 24's finalization in tree 24, while
    `park tree` told it the tree was free (2026-09-21)."""
    own = {rec.get("task"), rec.get("reviews")}
    out = {}
    for tid, t in st["tasks"].items():
        if t.get("stage") in HOLDS_FILES and tid not in own and not apart(tid):
            try:
                for f in json.load(open(os.path.join(BUILD, tid, "finalize.json")))["files"]:
                    out[os.path.normpath(os.path.join(PROJECT, f))] = tid
            except (OSError, ValueError, KeyError):
                pass
    return out


def finalizing(st, rec=None):
    """The other task whose finalization is in flight in the same tree (one runs at a time there: a second task's
    check would see the first's uncommitted files), or None. Only the one tree is shared: a task in its own tree
    neither waits for another's finalization nor holds one up — it waited for any task's while its own was apart,
    and a one-tree task waited for a tree's, whose check reads nothing of the one tree."""
    own = {(rec or {}).get("task"), (rec or {}).get("reviews")}
    if apart((rec or {}).get("task")):
        return None
    return next((tid for tid, t in st["tasks"].items() if t.get("stage") in FINISHING and tid not in own
                 and os.path.exists(os.path.join(BUILD, tid, "finalize.json")) and not apart(tid)), None)


def check_isolation():
    """A check sees the working tree: while one runs, no other session writes it. A task whose session still works is
    parked — its work stays where it is — and resumed when the check's task has landed."""
    st = peek()
    # a check in a task's own tree reads that tree alone: it parks nobody in the one tree
    checking = next((tid for tid, t in st["tasks"].items() if t.get("stage") == "checking" and not apart(tid)), None)
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


# The proof base's places. Task 144 (2026-09-22, after the reboot of 13:04 took /tmp and every heap in it) moved them to
# a lasting place, `.build/tasks/base-lasting/`, named once in the tools (tools/isabelle_places.py), and left links at
# the old /tmp paths for trees whose tools are older; the harness reads the lasting pointer once it is there.
LASTING = os.environ.get("ORCH_LASTING") or os.path.join(PROJECT, ".build", "tasks", "base-lasting")
OLD_POINTER = os.environ.get("ORCH_OLD_POINTER", "/tmp/structural-active-context.json")
OLD_HOME = os.environ.get("ORCH_OLD_HOME", "/tmp/structural-isabelle")


def lasting():
    return os.path.isfile(os.path.join(LASTING, "active-context.json"))


def places():
    """The proof base's places as main's tools name them — tools/isabelle_places.py once task 144's change has landed,
    the /tmp paths before. A base records its heap by its path: one made with one set of places is refused by tools that
    look in the other ("Accepted heap/database changed": every check from a tree with the older tools failed in a
    second once the /tmp pointer led to the lasting base, 2026-09-22 14:06), so the harness reads and writes the pointer
    main's own checks read, never the other."""
    path = os.path.join(PROJECT, "tools", "isabelle_places.py")
    if os.path.isfile(path):
        text = open(path, errors="ignore").read()
        if "ACTIVE_CONTEXT" in text and "USER_HOME" in text:
            return os.path.join(LASTING, "active-context.json"), os.path.join(LASTING, "isabelle-home")
    return OLD_POINTER, OLD_HOME


ACTIVE_CONTEXT = os.environ.get("ORCH_ACTIVE_CONTEXT") or places()[0]


def relink(path, target):
    temporary = path + ".link"
    with contextlib.suppress(OSError):
        os.remove(temporary)
    os.symlink(target, temporary)
    os.replace(temporary, path)


def keep_pointer_links():
    """The old heap store kept as a link to the lasting one after a reboot takes /tmp: a tree whose tools are older than
    the lasting places finds the heaps its own bases recorded there (task 144 moved the store's contents). The pointers
    are never linked or carried across: a base recorded under one store's path is refused by tools reading the other."""
    if os.environ.get("ORCH_ACTIVE_CONTEXT") and not os.environ.get("ORCH_LASTING"):
        return
    home = os.path.join(LASTING, "isabelle-home")
    try:
        if not os.path.lexists(OLD_HOME) and os.path.isdir(home):
            relink(OLD_HOME, home)
    except OSError as e:
        say_once("pointer-links", f"ATTENTION the old heap store could not be kept as a link: {e!r}")


THEORY_LINE = re.compile(r"^\s{4}(\w+)\s*$", re.M)
IMPORTS = re.compile(r"\bimports\b(.*?)(?:\bkeywords\b|\babbrevs\b|\bbegin\b)", re.S)  # the header, one line or many
IMPORT_NAMES = re.compile(r'"[^"]+"|[\w.\-]+')


def theory_imports(text):
    """The theories a theory's header imports, as it names them (quotes taken off), its comments left out: what the
    tree's trouble, the recipes' reach and a THEORY_MAP.md row's imports column are read from."""
    m = IMPORTS.search(re.sub(r"\(\*.*?\*\)", " ", text or "", flags=re.S))
    return [n.strip('"') for n in IMPORT_NAMES.findall(m.group(1))] if m else []
MARKERS = re.compile(r"^(?:<{7}|>{7}|={7})(?:\s|$)", re.M)


def _read(name, tree=None):
    try:
        return open(os.path.join(tree or PROJECT, name), errors="ignore").read()
    except OSError:
        return ""


def tree_trouble(tree=None, changed=None):
    """What is wrong with the working tree as a whole, in the terms the checks refuse on. Each of these refuses every
    check made in that tree and not only the one whose change caused it, so each is the orchestration's to notice
    rather than a task's to discover: a theory present and undeclared, a line declaring a theory that is not there, an import of a
    theory that is neither present nor in the history, and the markers of a merge that did not resolve — looked for
    in `changed`, or in what git says has changed in the tree."""
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
        for imported in theory_imports(text):
            if "." in imported or imported in known or imported == "Main":
                continue
            out.append(f"theories/{name}.thy imports {imported}, which is neither in the tree nor in the history")
    for path in changed_paths(tree) if changed is None else changed:
        full = os.path.join(tree, path)
        if not os.path.isfile(full) or os.path.getsize(full) > 8_000_000:
            continue
        try:
            if MARKERS.search(open(full, errors="ignore").read()):
                out.append(f"{path} holds the markers of a merge that did not resolve")
        except OSError:
            continue
    return out


TROUBLE_READS = ("ROOT", "DECISIONS.md", "THEORY_MAP.md", "theories")  # all that tree_trouble reads of a tree


def trouble_of(tree, ref, changed=()):
    """tree_trouble of a state of `tree` that is in git and not in its working files: a commit (`HEAD`, a hash, a
    branch), or `index` for what is staged — what HEAD would be if it were committed. What tree_trouble reads, and the
    paths in `changed` (where it looks for merge markers), are taken out into a temporary directory through an index
    of their own, so neither the tree nor its index is touched."""
    import tempfile
    with tempfile.TemporaryDirectory(prefix="snapshot-") as tmp:
        index = os.path.join(tmp, "index")
        env = dict(os.environ, GIT_INDEX_FILE=index)
        git = lambda *a, **k: subprocess.run(["git", "-C", tree, *a], capture_output=True, env=env, **k)
        if ref == "index":
            shutil.copy(subprocess.run(["git", "-C", tree, "rev-parse", "--path-format=absolute", "--git-path",
                                        "index"], capture_output=True, text=True, check=True).stdout.strip(), index)
        else:
            git("read-tree", ref, check=True)
        paths = git("ls-files", "-z", "--", *TROUBLE_READS, *changed, check=True).stdout
        git("checkout-index", "-z", "--stdin", f"--prefix={tmp}/tree/", input=paths, check=True)
        os.makedirs(os.path.join(tmp, "tree"), exist_ok=True)
        return tree_trouble(os.path.join(tmp, "tree"), changed=[p for p in changed if p])


def new_trouble(tree, target="index", base="HEAD"):
    """What committing `target` — the staged index, or a commit — would add to the trouble `base` already has. A
    commit that adds none leaves HEAD no worse; once HEAD is sound, every commit leaves it sound. On 2026-09-20 task
    7's commit took ROOT whole, with the declarations of two theories whose files stayed uncommitted: HEAD declared
    what it did not hold, and every tree made from it refused every check."""
    diff = ["diff", "--cached", "--name-only", "-z", base] if target == "index" else \
        ["diff", "--name-only", "-z", base, target]
    changed = [p for p in (subprocess.run(["git", "-C", tree, *diff], capture_output=True, text=True).stdout or "")
               .split("\0") if p]
    before = set(trouble_of(tree, base, changed))
    return [x for x in trouble_of(tree, target, changed) if x not in before]


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


BASE_KEEP = int(os.environ.get("ORCH_BASE_KEEP", 3600))  # a landing check's base whose landing did not happen, kept
# where the repository's checks store their heaps (tools/proof_contexts.py USER_HOME): /tmp, a tmpfs, so every heap
# kept is memory, and a reboot takes them all (2026-09-22 13:04: every base's heap, and the active pointer, gone)
ISABELLE_HOME = os.environ.get("ORCH_ISABELLE_HOME") or places()[1]


def stored_of(proof):
    """The heap and database files a base's proof stored ({} for none, or one that cannot be read)."""
    try:
        stored = json.load(open(os.path.join(proof, "accepted-context.json"))).get("stored") or {}
    except (OSError, ValueError, AttributeError):
        return {}
    return {k: stored[k] for k in ("heap", "database") if isinstance(stored.get(k), str)}


def prune_bases():
    """The bases the finalizer's landings made (.build/bases/, finalize.recheck): each level of the active base's
    lineage keeps its proof (its heap is what every level above it stands on) and loses its check's bulk once its
    receipts are retained — the recipes' runs and the exports, about 2 GB of 2.1 — and a base no lineage holds (a
    landing that did not happen) goes once it is older than BASE_KEEP. The base in use stays whole."""
    root = os.path.realpath(os.path.join(PROJECT, ".build", "bases"))
    if not os.path.isdir(root):
        return []
    lineage = base_lineage()
    if not lineage:  # no active base (the pointer gone with /tmp): nothing tells what stands on what
        return []
    active = os.path.dirname(os.path.realpath(lineage[0]))
    levels = {os.path.dirname(os.path.realpath(p)) for p in lineage}
    kept = {os.path.realpath(f) for p in lineage for f in stored_of(p).values()}
    heaps = os.path.realpath(ISABELLE_HOME) + os.sep
    removed = []
    for d in sorted(glob.glob(os.path.join(root, "*"))):
        d = os.path.realpath(d)
        if not os.path.isdir(d) or os.path.dirname(d) != root or d == active:
            continue
        if d in levels:
            for bulk in ("recipes", "exports-context"):
                path = os.path.join(d, bulk)
                if os.path.isdir(path) and os.path.dirname(path) == d:
                    shutil.rmtree(path, ignore_errors=True)
                    removed.append(path)
        elif time.time() - os.path.getmtime(d) > BASE_KEEP:
            for f in stored_of(os.path.join(d, "proof")).values():  # its heap, in memory, goes with it
                f = os.path.realpath(f)
                if f.startswith(heaps) and f not in kept and os.path.isfile(f):
                    os.remove(f)
                    removed.append(f)
            # its bulk goes and its reports stay (incremental.json, manifests, boundaries, logs): a check batch's
            # output stands here since it keeps its heap (C10), and `v2.py read check:STAMP` reads its report
            for sub in sorted(os.listdir(d)):
                path = os.path.join(d, sub)
                if os.path.isdir(path) and not os.path.islink(path):
                    shutil.rmtree(path, ignore_errors=True)
                    removed.append(path)
    if removed:
        log(f"pruned {len(removed)} base part(s) nothing stands on: "
            f"{', '.join(os.path.relpath(p, PROJECT) if p.startswith(PROJECT) else p for p in removed[:6])}")
    return removed


COMBINED_KEEP = int(os.environ.get("ORCH_COMBINED_KEEP", 3600))


def prune_combined_outputs():
    """The bulk of every repository check once COMBINED_KEEP old: a check is a whole heapless check, ~2.7 GB with its
    recipes' runs (recipes/) and exports (exports-context/). Each keeps its reports (incremental.json, manifests.json),
    its logs and its proof's own files (build.log, result.json: `read check:` and attribution read them), and loses its
    directories. It pruned the combined checks' outputs only (.build/tasks/trains/, .build/tasks/batches/): the checks
    a task's hand-over names (.build/tasks/NAME/check, check-2, …) and the task-by-task landings' (landing, landing-2,
    …) were never pruned, and held 115 of the 139 GB under .build on 2026-09-22 ("figure out why disk usage is not
    cleaning up", the owner). What the base's lineage stands in, or holds, is never touched."""
    keep = [os.path.realpath(p) for p in base_lineage()]
    near = lambda d: any(k == d or k.startswith(d + os.sep) or d.startswith(k + os.sep) for k in keep)
    removed = []
    for report in glob.glob(os.path.join(BUILD, "**", "incremental.json"), recursive=True):
        d = os.path.realpath(os.path.dirname(report))
        if near(d) or time.time() - os.path.getmtime(d) < COMBINED_KEEP:
            continue
        for part in os.listdir(d):
            path = os.path.join(d, part)
            if not os.path.isdir(path) or os.path.islink(path):
                continue
            if part == "proof":  # its own files stay; what it copied in to run goes
                for inner in os.listdir(path):
                    sub = os.path.join(path, inner)
                    if os.path.isdir(sub) and not os.path.islink(sub):
                        shutil.rmtree(sub, ignore_errors=True)
                        removed.append(sub)
                continue
            shutil.rmtree(path, ignore_errors=True)
            removed.append(path)
    if removed:
        log(f"pruned {len(removed)} part(s) of the checks' outputs: their reports, logs and proof logs kept")
    return removed


def base_at_risk():
    """Whether the accepted base stands inside a task's own directory — where the task that owns it, a re-plan or a
    sweep of run output would take it away with everything that chains from it. Found on 2026-09-20: the base stood
    in .build/tasks/7/check2/proof, because an advancing check was run with its output there."""
    lineage = base_lineage()
    at = BUILD.rstrip(os.sep) + os.sep  # BUILD is already .build/tasks
    lasting = os.path.realpath(LASTING).rstrip(os.sep) + os.sep  # the harness's own store, no task's (the owner, 09-22)
    return [p for p in lineage if p.startswith(at) and not os.path.realpath(p).startswith(lasting)]


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
    # what stands there and whose it is: the step that found the trouble is not what made it. Task 62 took its ROOT
    # line out of the one tree and left its new theory; the trouble was found after task 32's commit and said to be
    # "after its commit (task 32)", every task's check refusing — while tasks in their own trees check there
    # (2026-09-22 03:10)
    standing = {} if own else one_tree_changes(changed_paths())
    by = {}
    for path, tid in standing.items():
        if tid:
            by.setdefault(tid, []).append(path)
    held = "".join(f" What stands uncommitted there is task {tid}'s ({', '.join(sorted(paths)[:4])})."
                   for tid, paths in sorted(by.items()))
    reach = (". Its own checks refuse on this until it is put right; the shared working tree is not affected."
             if own else
             "." + held + " Every check made in the one tree refuses on this until it is put right, not only the "
             "check of the task whose change caused it; a task in a tree of its own checks there and lands as before.")
    log(f"ATTENTION {whose} is inconsistent after {what} ({who}): " + "; ".join(trouble[:4]) + held)
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
    depths = chain_depths()
    for t in all_tasks():
        if t.get("status") == "completed" and not full:
            done += 1
            continue
        meta = t.get("metadata") or {}
        kind = meta.get("kind") or field(t.get("description", ""), "Kind") or "?"
        after = ", ".join(t.get("blockedBy") or []) or "-"
        stage = stage_text((st["tasks"].get(t["id"]) or {}))
        d = depths.get(t["id"])
        lines.append(f"- {t['id']} [{t.get('status')}{', ' + stage if stage else ''}] ({kind}) {t.get('subject', '')}; "
                     f"after {after}" + (f"; chain {d}" + (f", past {GRAPH_DEPTH}: nothing is hung after it"
                                                          if d > GRAPH_DEPTH else "") if d else "")
                     + (f"; owner {t['owner']}" if t.get("owner") else "")
                     + (f"; why: {meta['why']}" if meta.get("why") else ""))
    if done:
        lines.append(f"- and {done} completed task{'s' if done > 1 else ''} (`v2.py graph --all` lists them)")
    return "\n".join(lines) or "(the task list is empty)"


PARKED_FOR = {"run": "for its run", "fix": "for the fix of its performance problem", "tree": "for the working tree",
              "answer": "for an answer", "machine": "for the machine", "check": "for the check it asked for",
              "probe": "for its queued probe"}


def stage_text(rec):
    """A task's passing state as the graph shows it: its stage, and for a parked task what for and since when, for one
    rejected how many times — what the planners of 2026-09-21/22 kept writing into HANDOFF.md by hand (405 of the 908
    blocks by which they edited it changed words of a task's passing state: parked, handing over, landed, a commit, the
    order), a mirror stale between its edits. Rendered at every event instead, for every planner after them."""
    stage = rec.get("stage")
    if not stage:
        return ""
    parked = rec.get("parked") if stage == "parked" else None
    if isinstance(parked, dict):
        stage += (f" {PARKED_FOR.get(parked.get('for'), 'for ' + str(parked.get('for')))}"
                  + (f" since {time.strftime('%H:%M', time.localtime(parked['since']))}" if parked.get("since") else ""))
    if int(rec.get("rejections") or 0):
        stage += f", rejected {rec['rejections']}×"
    return stage


LANDED_SHOWN = int(os.environ.get("ORCH_LANDED_SHOWN", 3 * 3600))  # how far back the planner's status names landings


def landed_lately(since=None):
    """[(task, commit, when)] of the tasks landed in the last LANDED_SHOWN seconds, newest first: their finalized.json,
    written when the finalizer committed and landed them. What a planner wrote as `(`90991eac`)` beside each delivered
    task; git holds it, and the status says it."""
    since = time.time() - LANDED_SHOWN if since is None else since
    out = []
    for path in glob.glob(os.path.join(BUILD, "*", "finalized.json")):
        tid = os.path.basename(os.path.dirname(path))
        try:
            when, rec = os.path.getmtime(path), json.load(open(path))
        except (OSError, ValueError):
            continue
        if when >= since and isinstance(rec, dict) and rec.get("ok") and rec.get("commit"):
            out.append((tid, str(rec["commit"])[:8], when))
    return sorted(out, key=lambda x: -x[2])


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
    if done:
        waits = landing_wait(tid)
        if waits:
            done = False
            d, what = waits
            if (age_of(f"landing-{tid}") or LOST_BLOCKER + 1) > LOST_BLOCKER:
                open(os.path.join(STATE, f"landing-{tid}"), "w").write(str(time.time()))
                with state() as st:
                    event(st, "the harness", f"Task {tid} is ready but would start in a tree of its own, made from HEAD, "
                          f"and HEAD does not hold what it stands on: the work of task {d} has not landed "
                          f"({', '.join(what[:4])}{', …' if len(what) > 4 else ''}). It starts when that work is "
                          "committed. A task that works on that work itself names its paths in its brief, and "
                          "works in the one tree where they stand.")
                log(f"task {tid} waits for the work of task {d} to land")
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


# A file a Deliverable names bare, with no place, is the task's own folder's: a brief made in an edit cannot know its id,
# and says "`report.md`, in this task's own folder" — briefs 253 and 254 did (2026-09-22), and `report.md` was read as a
# file at the repository's root: the result was refused for a final job, and the final job refused a file under .build/
# (q64). A file already at the root (THEORY_MAP.md, DECISIONS.md) stays the root's; a new one there is `./NAME`.
FILE_NAME = re.compile(r"[\w-]+(?:\.[\w-]+)*\.(?:md|json|jsonl|txt|log|thy|ML|py|sh)")


def placed(p, tid):
    """Where a deliverable named `p` of task tid stands."""
    if tid and "/" not in p and FILE_NAME.fullmatch(p) and not os.path.lexists(os.path.join(PROJECT, p)):
        return f".build/tasks/{tid}/{p}"
    return p


def deliverables(text, tid=None):
    out = []
    for p in names_in(section(text, "Deliverable")):
        p = placed(p, tid)
        if ("/" in p or "." in p) and p not in out:
            out.append(p)
    return out


def brief_record(tid, brief):
    """What the harness reads of the brief a session works to — its deliverables, drafts and inputs — written when the
    session starts and again when the planner rewrites the brief: task 254's stood as its brief was at its start after
    plan-46 had added a test module to its Deliverable (2026-09-22 18:44)."""
    os.makedirs(os.path.join(BUILD, tid), exist_ok=True)
    json.dump({"task": tid, "deliverables": deliverables(brief, tid), "drafts": f".build/tasks/{tid}/",
               "inputs": inputs(brief)}, open(os.path.join(BUILD, tid, "brief.json"), "w"))


def inputs(text):
    return names_in(section(text, "Inputs"))


INPUTS_BYTES = 20_000  # the statements a producing session's first message gives it, at most
DERIVED = re.compile(r"(?:_def|\.simps|\.induct|\.cases|\.intros|_def_raw)$")


def inputs_read(brief, tree):
    """The facts and definitions a brief's Inputs and Decided name, stated as the task's tree holds them now (show.py
    --statement: proofs left out), for the producing session's first message — the task-specific reading a role-level
    layer could not give it (notes/plan-orchestrator-concepts.md C2). Before their first change, implementers spent 26%
    and fixers 28% of what they cost on 2026-09-21/22 (8 and 7 requests), and 55% of the files they read then were
    files the brief names; 7 of the 31 rejections whose findings the state held were a contract the brief named proved
    again instead of consumed. A name the tree does not hold is said: one the task is to make, or one that has moved.
    Theories and files named are left to the session's reading; the whole is bounded by INPUTS_BYTES."""
    tree = tree or PROJECT  # None: the task works in the one tree (task_tree)
    places = softly("the decision entries' places", decision_places, brief, tree, default="")
    return "\n\n".join(x for x in (named_statements(brief, tree), places) if x)


def decision_places(brief, tree):
    """Each DECISIONS.md entry a brief names by its heading (quoted, whole or by its beginning), with the lines it
    stands at in the tree now, for the first batch to read: design-258 spent three of its nine reading requests finding
    the entries its brief named by grepping their headings (2026-09-22). "" when the brief names none."""
    try:
        lines = open(os.path.join(tree, "DECISIONS.md"), errors="ignore").read().split("\n")
    except OSError:
        return ""
    heads = [(i + 1, len(m.group(1)), m.group(2).strip()) for i, l in enumerate(lines)
             for m in [re.match(r"^(#{2,4})\s+(.+?)\s*$", l)] if m]
    count = collections.Counter(h for _, _, h in heads)  # a heading many entries share ("Affordability") names none of them
    quoted = re.findall(r'"([^"\n]{12,200})"|\u201c([^\u201d\n]{12,200})\u201d|(?:^|[\s(])\'([^\'\n]{12,200})\'', brief)
    found = []
    for q in dict.fromkeys(" ".join((a or b or c).split()).rstrip(".,;:") for a, b, c in quoted):
        for n, (at, level, h) in enumerate(heads):
            if count[h] == 1 and (h == q or (len(q) >= 20 and h.startswith(q)) or (len(h) >= 20 and q.startswith(h))):
                end = next((a - 1 for a, lv, _ in heads[n + 1:] if lv <= level), len(lines))
                if (at, end, h) not in found:
                    found.append((at, end, h))
                break
    if not found:
        return ""
    return ("The decision entries your brief names, where they stand now — read what you need of them by these lines, "
            "in your first batch:\n" + "\n".join(f"- DECISIONS.md:{a}-{b} — {h}" for a, b, h in found[:20]))


def named_statements(brief, tree):
    """The statements of the facts and definitions a brief names (inputs_read)."""
    names = list(dict.fromkeys(names_in(section(brief, "Inputs")) + names_in(section(brief, "Decided"))))
    wanted = {}
    for n in names:
        base = DERIVED.sub("", n)
        if not re.fullmatch(r"[A-Za-z][\w']*(?:\.[A-Za-z][\w']*)?", base) or ("_" not in base and "." not in base) \
                or FILE_NAME.fullmatch(base):
            continue  # not a fact's name; a file named bare (`commit.md`) is one
        if os.path.exists(os.path.join(tree, "theories", base + ".thy")):
            continue  # a theory: read as the session reads theories
        wanted.setdefault(base, n)
    if not wanted:
        return "(the brief names no fact or definition by name)"
    try:
        out = subprocess.run([sys.executable, os.path.join(HERE, "show.py"), "--statement", *wanted], capture_output=True,
                             text=True, cwd=tree, env=dict(os.environ, ORCH_PROJECT=tree), timeout=60).stdout
    except (OSError, subprocess.SubprocessError) as e:
        return f"(the statements could not be read: {e!r}; `v2.py read NAME` reads each)"
    blocks, missing = [], []
    for block in re.split(r"\n(?=== )", out.strip()):
        m = re.match(r"^== ([\w.']+): no command introduces it", block)
        if m:
            missing.append(wanted.get(m.group(1), m.group(1)))
        elif block.strip() and not re.fullmatch(r"== \S+\n\s*context \S+(?: begin)?\s*", block.strip()):
            blocks.append(block.strip())  # a bare `context NAME` a locale's name brings says nothing of it
    text, left = "", []
    for b in blocks:
        if len(text.encode()) + len(b.encode()) + 2 > INPUTS_BYTES:
            left.append(b.split("\n", 1)[0][3:])
            continue
        text += b + "\n\n"
    if left:
        text += (f"({len(left)} more, left out for room — `v2.py read NAME` reads each: "
                 + ", ".join(left[:12]) + ("…" if len(left) > 12 else "") + ")\n")
    if missing:
        text += ("Not stated in the theories as your tree holds them — HOL's own, a name the task is to make, or one "
                 "that has moved since the brief was written: " + ", ".join(f"`{n}`" for n in missing) + "\n")
    return text.rstrip() or "(the brief names no fact or definition the library holds)"


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
    absolute = one_tree_paths(text)
    if absolute:
        out.append(f"the brief names the repository's own directory by its absolute path ({', '.join(absolute[:3])}): "
                   "a task may work in a tree of its own, where that path is the one tree and not its work. Name "
                   "paths relative to the repository — a check as `python3 -B tools/incremental_check.py …`, which "
                   "the finalizer runs where the task works; `.build/` may be named as it is")
    marked = [f for f in FORM_FIELDS if FOLLOW_MARK in section(text, f)]
    if FOLLOW_MARK in text:
        out.append(f"the brief still holds parts marked for you ({', '.join(marked) or 'its text'}): write each "
                   f"`{FOLLOW_MARK}: …>>` as the brief's own words")
        return out  # the rest of the form is judged when they are written
    size, room = size_of(text), room_of(kind if kind in KINDS else "build")
    if re.search(head("Size"), text, re.M | re.I) and size is None:
        out.append("the Size is an estimate in tokens of work (for example `Size: about 150K`)")
    elif size and size > room:
        out.append(f"the Size ({size // 1000}K) is beyond what a {kind or 'build'} session has room for "
                   f"({room // 1000}K): split the task")
    return out


def room_of(kind):
    """The work a session of this kind has room for: what its base leaves before the notice, less its first message and
    first batch of reads."""
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


CORRECTABLE = ("commit.md", "result.md", "THEORY_MAP.md")  # what a reviewer corrects itself (C7)
FILE_WORD = re.compile(r"^(?:[\w./-]*/)?(?:ROOT|[\w.-]+\.(?:thy|md|py|json|txt|ML|sh|toml|yaml|cfg))$")


def verdict_problems(text, verdict):
    out = [] if part(text, "Summary") else ["the verdict has no `## Summary` part (about 150 words, for the planner)"]
    if verdict == "reject" and not part(text, "Findings"):
        out.append("a rejection lists its blocking findings under `## Findings`")
    corrected = part(text, "Corrected")
    if corrected:
        files = [w for w in re.findall(r"`([^`\s]+)`", corrected) if FILE_WORD.match(w)]
        wrong = [w for w in files if os.path.basename(w) not in CORRECTABLE]
        if verdict == "reject":
            out.append("`## Corrected` comes with an accept: what you corrected no longer blocks, and what blocks is "
                       "a finding")
        if not any(os.path.basename(w) in CORRECTABLE for w in files):
            out.append("`## Corrected` names each file it corrected in backticks (`commit.md`, `result.md`, "
                       "`THEORY_MAP.md`), with why")
        if wrong:
            out.append(f"`## Corrected` names {', '.join(wrong)}: a reviewer corrects only a commit message, a result "
                       "or a THEORY_MAP.md row; anything else it found is a finding, and a rejection")
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


STATEMENTS_READ = (" You read statements, not details: theories through `.claude/orchestration/show.py --statement "
                   "NAME...` or `--statements THEORY` (or `v2.py read`, statements only), results and documents under "
                   ".build/tasks/*/, the plan, the ledger and `git log`; proof text, code bodies, logs and diffs are "
                   "refused to you.")


def statements_only(rec):
    """Whether a session reads statements only: the planner, the task designer, the knowledge base, and a
    consultation of the knowledge base or of a planning episode."""
    if rec.get("role") == "consultant":
        return ROLES[(peek()["sessions"].get(rec.get("origin")) or {}).get("role", "kb")]["statements"] is not False
    return bool(ROLES.get(rec.get("role"), {}).get("statements"))


# ---------------------------------------------------------------- protocols

def grouping_text():
    """The planner's and the task designer's rule on a task's size against its fixed cost — the owner's to set
    (notes/plan-orchestrator-concepts.md C8), off unless state/grouped-repairs exists: "" then. Every task pays the
    same launch, orientation, close, review and landing (a producer's orientation 31–34% of its cost in the afternoon of
    2026-09-22; a review 0.67M), and sessions ended at a third of their window; 23 of the 51 planned fixes from #100 on
    consolidated what was stated twice, several on one line of theories in a row."""
    if not os.path.exists(os.path.join(STATE, "grouped-repairs")):
        return ""
    return ("**A task's size against its fixed cost.** Every task pays the same fixed cost whatever it holds — a "
            "session's launch and first reading, its close, a review, a landing — and a session ends at about a third "
            "of its window. Small repairs of the same theories, and follow-ups that consolidate what is stated twice, "
            "go into one task, up to about half of its room, rather than a task each; a repair another task waits on, "
            "or one of a notion's contract, stays a task of its own.")


def continue_by_fork():
    """The owner's to set (notes/plan-orchestrator-concepts.md C13), off unless state/continue-by-fork exists or
    ORCH_CONTINUE_BY_FORK=1: a task whose metadata says which task's work it continues (`"continues": "N"`) forks the
    session that did that work, while it is warm and has the room, instead of its role's base. Of the 52 fix tasks of
    2026-09-21/22 with a fixer session, 27 named in their brief the task whose review they came from, and that task's
    producer was still warm at the fix's start for 18; a fixer spent 31% of its cost before its first change, orienting
    in work that producer held whole, and grew a median 45K from a producer's median of 638K."""
    return os.environ.get("ORCH_CONTINUE_BY_FORK") == "1" or os.path.exists(os.path.join(STATE, "continue-by-fork"))


CONTINUE_MAX = int(os.environ.get("ORCH_CONTINUE_MAX", 700_000))  # the context past which a producer is not forked:
# a fork starts with it whole and must still have a task's room before the notice (907K)


CONTINUE_GRACE = int(os.environ.get("ORCH_CONTINUE_GRACE", 5400))  # how long after its work a producer whose review asked
# for follow-ups is held for the planner to make them into continuations (C13): its work, check, review and landing
# took a median 22 minutes from its result on 09-22's afternoon, and the planner's turn a median two


def continues_text():
    """The planner's line on marking a continuation (C13), "" while the switch is off."""
    if not continue_by_fork():
        return ""
    return ("**A continuation forks the work it continues.** When a task continues one task's work — a follow-up its "
            "review asked for, a repair of what it built — say so in its metadata, `\"continues\": \"N\"` (in `v2.py "
            "edit`, a create's or a rewrite's field): its session "
            "is then forked from the session that did task N, which holds that work whole, while that session is warm "
            "and has the room, and from its role's base otherwise. Only one task N, and only when the work is N's: a "
            "task drawing on several is briefed from the base as always. Such a brief may name the findings it takes "
            "up by their place (`.build/tasks/N/review.md`, its follow-ups 1 and 3) rather than restate them: the "
            "session reads them there, and the fork holds the work they are about.")


def continued_session(st, tid, role):
    """(session, task) whose work task tid continues and that a session of `role` may fork now, or (None, None): the
    switch on; the task's metadata naming the task it continues; that task's last producing session, with its cache
    warm, run at the effort and on the model of the role's own base (a fork carries its origin's, and a fork at another
    effort than the entry it reads writes it anew), not working now, and within CONTINUE_MAX."""
    if not continue_by_fork() or role not in ("implementer", "fixer"):
        return None, None
    meta = (read_task(tid) or {}).get("metadata") or {}
    source = str(meta.get("continues") or "") if isinstance(meta, dict) else ""
    if not source.isdigit() or source == str(tid):
        return None, None
    base = base_record(ROLES[role]["origin"])[1] or {}
    mine = [(n, x) for n, x in st["sessions"].items() if str(x.get("task")) == source and x.get("role") in PRODUCING
            and x.get("sid") and x.get("state") != "lost"]
    if not mine:
        return None, None
    name, rec = max(mine, key=lambda nx: nx[1].get("started") or 0)
    if rec.get("state") in LIVE or not warm(name) or other_tools(rec):
        return None, None
    if (rec.get("effort"), rec.get("model")) != (base.get("effort"), base.get("model")):
        return None, None
    if (rec.get("context") or context_of(rec["sid"]) or CONTINUE_MAX + 1) > CONTINUE_MAX:
        return None, None
    return name, source


def continued_text(source_session, source, tid, tree):
    """What a continuation's first message says before its protocol: whose context it holds, and that the task it
    holds is over."""
    where = f"`{os.path.relpath(tree, PROJECT)}`" if tree and tree != PROJECT else "the one tree"
    return (f"**You continue task {source}'s work.** You are forked from {source_session}, the session that did task "
            f"{source}: what you hold of that work — its theories, what was read and learned, how it was proved — is "
            f"yours to use. That task is over: its brief, its tree and the rules of its session no longer bind you. "
            f"Your task is {tid}, below, and its brief governs; you work in {where}, as it is now, where task "
            f"{source}'s work stands as it landed — what you remember of files may have changed since.")


def render(role, **values):
    """A role's first message: protocols/<role>.md with its shared parts ({{part}} is protocols/_part.md) and values."""
    text = open(os.path.join(PROTOCOLS, f"{role}.md")).read()
    for _ in range(2):
        text = re.sub(r"\{\{([\w-]+)\}\}", lambda m: open(os.path.join(PROTOCOLS, f"_{m.group(1)}.md")).read().strip(), text)
    values = render_values(**values)
    values.setdefault("CONTINUED", "")  # a continuation's own paragraph (C13), nothing for every other session
    values.setdefault("LAYERED", layered_text(values.get("NAME")))  # a fork of its role's reasoning layer is told so
    values.setdefault("CHECKED", CHECK_PASSED)  # a reviewer's: whether the check it reviews beside has passed (C9)
    missing = [k for k in dict.fromkeys(re.findall(r"\{([A-Z][A-Z_]{2,})\}", text)) if k not in values]
    for k, v in values.items():
        text = text.replace("{" + k + "}", v)
    for left in missing:
        log(f"ATTENTION the {role} protocol has no value for {{{left}}}: it is left out of the message")
        text = text.replace("{" + left + "}", "")
    return text.strip()


def render_values(**values):
    """The values every protocol may name: numbers the harness can change under a protocol's prose, and its texts."""
    return dict(ROUNDS=str(ROUNDS), RESERVE=str(READ_RESERVE),
                  BATCH=str(BATCH_BYTES // 1000), READ_BYTES=str(READ_BYTES // 1000), CIRCLING=str(CIRCLING),
                  FIX_MINUTES=str(FIX_MINUTES),
                  BRIEF_BACKLOG=str(BRIEF_BACKLOG), GRAPH_DEPTH=str(GRAPH_DEPTH),
                  WIDTH=str(graph_figures()[0]), DEPTH=str(graph_figures()[1]),
                  SLOTS=str(GRAPH_WIDTH or WORKERS_MAX),
                  FIX_ROUNDS=str(FIX_ROUNDS), HOLD_HOURS=str(HOLD_PARK // 3600), ROOM_DESIGN=str(room_of("design") // 1000),
                  # a number a protocol states in prose is one the harness can change under it: these are its own
                  CONSULT_HOURS=str(HOLD_MAX // 3600), ISABELLE_MAX=str(ISABELLE_MAX), PROBE_MAX=str(PROBE_MAX),
                  PROBE_SECONDS=str(PROBE_SECONDS), MEM_MARGIN=f"{MEM_MARGIN_GB:g}",
                  PARK_URGENT=str(PARK_URGENT // 60), GROUPING=grouping_text(), CONTINUES=continues_text(),
                  ROOM_TASK=str(room_of("build") // 1000), **values)


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
# base carries it beside a 472K base and stays far inside its limit, and a designer reads of it what it needs, by its
# lines. This is not a budget but the point past which it is a log and not a state, and the log
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


HANDOFF_DELTA_MAX = int(os.environ.get("ORCH_HANDOFF_DELTA_MAX", 15_000))  # characters, beside a planner's first message


def kb_handoff(kb):
    """Where the copy of HANDOFF.md a knowledge base loaded is kept (keep_kb_handoff, at its launch)."""
    return os.path.join(STATE, f"{kb}-handoff.md")


def keep_kb_handoff(kb):
    with contextlib.suppress(OSError):
        shutil.copyfile(os.path.join(PROJECT, "HANDOFF.md"), kb_handoff(kb))


def handoff_items(text):
    """{`## Part`: [its items]} of HANDOFF.md: an item begins after a blank line or at a line at the margin opening a
    bullet, a heading, a bold lead or a table row, and holds the lines under it."""
    parts, name, cur = {}, None, None
    for line in text.split("\n"):
        if line.startswith("## "):
            name, cur = line[3:].strip(), None
            parts[name] = []
            continue
        if name is None:
            continue
        if not line.strip():
            cur = None
        elif cur is None or line.startswith(("- ", "### ", "**", "|")):
            parts[name].append(line)
            cur = len(parts[name]) - 1
        else:
            parts[name][cur] += "\n" + line
    return parts


def handoff_delta(kb):
    """What HANDOFF.md's parts other than `## Now` and `## Open` (given whole) say now that the knowledge base a
    planner forks did not hold: the items added or rewritten since it loaded the file, and the first lines of those
    taken out — the planner holds the rest. Planners read HANDOFF.md again in their first requests where a decision
    turned on it (plan-40 read it in six ranges, 2026-09-22 09:33); the knowledge base holds it as it stood at its
    build, hours before (kb-10: 04:44, forked until 13:30)."""
    try:
        old = open(kb_handoff(kb), errors="ignore").read()
    except OSError:
        return "(the copy of HANDOFF.md the knowledge base loaded was not kept: read the file where a decision turns on it)"
    try:
        new = open(os.path.join(PROJECT, "HANDOFF.md"), errors="ignore").read()
    except OSError:
        return "(HANDOFF.md cannot be read)"
    a, b, out = handoff_items(old), handoff_items(new), []
    for name in [n for n in b if n not in ("Now", "Open")] + [n for n in a if n not in b and n not in ("Now", "Open")]:
        was, now = a.get(name, []), b.get(name, [])
        added = [i for i in now if i not in was]
        gone = [i.split("\n", 1)[0][:120] for i in was if i not in now]
        if not added and not gone:
            continue
        text = "\n".join(added + [f"(taken out: {g})" for g in gone])
        if len(text) > HANDOFF_DELTA_MAX // 2:
            text = (f"({len(added)} item(s) added or rewritten and {len(gone)} taken out since the knowledge base "
                    f"loaded it — more than fits here: read `## {name}` in HANDOFF.md)")
        out.append(f"### {name}\n{text.strip()}")
    whole = "\n\n".join(out)
    if len(whole) > HANDOFF_DELTA_MAX:
        whole = whole[:HANDOFF_DELTA_MAX].rsplit("\n", 1)[0] + "\n(cut here: read HANDOFF.md for the rest)"
    return whole or "(nothing: they are as the knowledge base holds them)"


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
        keep_kb_handoff(name)  # what it loads: a planner forking it is told what has changed since (handoff_delta)
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


# ---------------------------------------------------------------- the roles' reasoning layers

ROLE_LAYER_DONE = "ROLE-LAYER READY"  # the line that ends a layer's reasoning
ROLE_LAYER_AGE = int(os.environ.get("ORCH_ROLE_LAYER_AGE", 4 * 3600))  # past this, rebuilt once the run has shown more
ROLE_LAYER_IDLE = int(os.environ.get("ORCH_ROLE_LAYER_IDLE", 2 * 3600))  # a layer no session of its role wanted this
# long is let go (its keep-warm pings are a cost of their own) and built again when the role is wanted
ROLE_LAYER_BUILD_MAX = int(os.environ.get("ORCH_ROLE_LAYER_BUILD_MAX", 1200))  # a build that never replies
ROLE_LAYER_NEW = int(os.environ.get("ORCH_ROLE_LAYER_NEW", 6))  # sessions of the role ended since a build that make
# its evidence new enough to build again (with a rejection of the role's work since, one is enough)
ROLE_LAYER_PRACTICES = int(os.environ.get("ORCH_ROLE_LAYER_PRACTICES", 12))


def role_layers():
    """The roles whose sessions fork a reasoning layer made for the role — the owner's to set, to test (the owner,
    2026-09-23: "design and build the per-role reasoning layer which I will then either activate or not"). Off unless
    state/role-layers exists (its words name the roles, none or `all` every role that forks a base) or
    ORCH_ROLE_LAYERS says so (`0` or empty: off)."""
    named = os.environ.get("ORCH_ROLE_LAYERS")
    if named is None:
        try:
            named = open(os.path.join(STATE, "role-layers")).read() or "all"
        except OSError:
            return set()
    words = set(named.replace(",", " ").split()) - {"0"}
    if not words:
        return set()
    return set(LAYERABLE) if words & {"all", "1"} else words & LAYERABLE


def role_layer_record(role, st=None):
    return ((st or peek()).get("role_layers") or {}).get(role) or {}


def role_layer_of(role):
    """The name of the reasoning layer the role's sessions fork now, or None — its base's roles fork their base then:
    the switch on for the role; the layer sealed, warm and forked from what the role's base is now (a layer over a
    base rebuilt or refreshed since holds a load its forks would be told nothing about, and is built again)."""
    if role not in role_layers():
        return None
    st = peek()
    name = role_layer_record(role, st).get("name")
    rec = st["sessions"].get(name or "") or {}
    if rec.get("layer_state") != "sealed" or rec.get("released") or not warm(name):
        return None
    org = base_record(ROLES[role]["origin"])[1] or {}
    return name if rec.get("origin_sid") == org.get("sid") and not other_tools(rec) else None


def layered_text(name):
    """What a session forked from its role's reasoning layer is told of it, or ""."""
    st = peek()
    rec = st["sessions"].get(name or "") or {}
    layer = st["sessions"].get(rec.get("origin") or "") or {}
    if layer.get("role") != "role-layer":
        return ""
    return (f"Before this message stands the reasoning of {layer['name']}, your role's reasoning layer: it reasoned "
            f"once, for every session of the {rec.get('role')}, over what the run has shown of the role's work, and "
            "its practices are yours where they fit your task. Your brief, this protocol and the harness govern where "
            "they differ.")


def role_wanted(st, role):
    """Whether the role has work now or has had it lately: a session of it started within ROLE_LAYER_IDLE, or a task
    that one of its sessions would take."""
    if any(s.get("role") == role and time.time() - (s.get("started") or 0) < ROLE_LAYER_IDLE
           for s in st["sessions"].values()):
        return True
    kinds = {r: k for k, r in PRODUCER.items()}
    for tid in dict.fromkeys(list(st["tasks"]) + list(st.get("queue") or [])):
        t = dict(st["tasks"].get(tid) or {})
        if tid in (st.get("queue") or []) and t.get("stage") is None:  # queued, not yet taken up: its brief says
            task = read_task(tid) or {}
            if task.get("status") == "completed":
                continue
            t.setdefault("kind", brief_kind(task.get("description", "")))
        stage = t.get("stage")
        if role == "reviewer" and stage in ("checking", "reviewing"):
            return True
        if role == "fixer" and stage == "fixing":
            return True
        if role == "task-designer" and t.get("kind") == "brief" and stage in (None, "ready"):
            return True
        if role in kinds and t.get("kind", "build") == kinds[role] and stage in (None, "ready"):
            return True
    return False


def generic_protocol(role):
    """A role's protocol as each of its sessions receives it, the parts that are each session's own named instead."""
    text = open(os.path.join(PROTOCOLS, f"{role}.md")).read().replace("{{inherited}}", "")
    for _ in range(2):
        text = re.sub(r"\{\{([\w-]+)\}\}", lambda m: open(os.path.join(PROTOCOLS, f"_{m.group(1)}.md")).read().strip(), text)
    given = {k for k in re.findall(r"\{([A-Z][A-Z_]+)\}", text)}
    rendered = render_values()
    for k in given:  # a session's own part named as the placeholder it is: `<BRIEF>`, `.build/tasks/<ID>/`
        text = text.replace("{" + k + "}", rendered.get(k, f"<{k}>"))
    return text.strip()


def role_layer_new(st, role, rec):
    """Whether the run has shown the role more since its layer was built: ROLE_LAYER_NEW of its sessions ended since,
    or a task of its rejected since."""
    since = rec.get("built") or 0
    ended = [s for s in st["sessions"].values() if s.get("role") == role and (s.get("ended") or 0) > since]
    rejected = any(t.get("rejections") and (t.get("rejected_at") or 0) > since for t in st["tasks"].values()
                   if PRODUCER.get(t.get("kind", "build")) == role or role == "reviewer")
    return len(ended) >= ROLE_LAYER_NEW or (rejected and ended)


def role_layer_due(st, role):
    """Why the role's layer is to be built now, or None."""
    rec = role_layer_record(role, st)
    name = rec.get("name")
    layer = st["sessions"].get(name or "") or {}
    if not name or layer.get("state") == "lost" or layer.get("released"):
        return "it has none"
    org = base_record(ROLES[role]["origin"])[1] or {}
    if layer.get("origin_sid") != org.get("sid"):
        return "its base has been rebuilt or refreshed since it was built"
    if other_tools(layer):
        return "it was started with other tools than session-flags gives now"
    if not warm(name):
        return "it went cold"
    if time.time() - (rec.get("built") or 0) > ROLE_LAYER_AGE and role_layer_new(st, role, rec):
        return f"it is older than {ROLE_LAYER_AGE // 3600} hours and the run has shown the role more since"
    return None


def role_layer_care():
    """Build each switched-on role's reasoning layer when it is wanted and due, in the background: its evidence is read
    by role_evidence.py (transcripts, seconds to a minute, never in the dispatch), then the layer is forked from the
    role's base with it, and sealed when it has replied ROLE_LAYER_DONE. Until then the role forks its base."""
    roles = role_layers()
    st = peek()
    for role in sorted(roles):
        rec = role_layer_record(role, st)
        building = rec.get("building")
        if building:
            s = st["sessions"].get(building) or {}
            if s.get("state") == "lost" or (s.get("sid") and time.time() - (s.get("started") or 0) > ROLE_LAYER_BUILD_MAX
                                            and not role_layer_replied(s)):
                log(f"ATTENTION the {role}'s reasoning layer {building} did not finish; its role forks its base")
                with state() as w:
                    if building in w["sessions"]:
                        w["sessions"][building]["state"] = "lost"
                    w.setdefault("role_layers", {}).setdefault(role, {})["building"] = None
                open(os.path.join(STATE, f"start-failed-role-layer-{role}"), "w").write(str(time.time()))
                continue
            if s.get("sid") and role_layer_replied(s):
                seal(building)
                ctx = context_of(s["sid"])
                previous = rec.get("name")
                with state() as w:
                    w["sessions"][building].update(state="done", layer_state="sealed", context=ctx, ended=time.time())
                    w.setdefault("role_layers", {})[role] = dict(name=building, building=None, built=time.time(),
                                                                 wanted=time.time(), context=ctx,
                                                                 builds=rec.get("builds", 0) + 1)
                if previous and previous != building:
                    release(previous)
                log(f"{building} holds the {role}'s reasoning ({ctx} tokens); the {role}'s sessions fork it")
            continue
        if role_wanted(st, role):
            with state() as w:
                w.setdefault("role_layers", {}).setdefault(role, {})["wanted"] = time.time()
        elif rec.get("name") and time.time() - (rec.get("wanted") or 0) > ROLE_LAYER_IDLE:
            continue  # not held (watchdog.held) and not built again until the role is wanted
        why = role_layer_due(st, role) if role_wanted(st, role) else None
        if why:
            role_layer_build(role, why)
    for role, rec in (st.get("role_layers") or {}).items():  # switched off: what stands is let go
        if role not in roles and rec.get("name") and not (st["sessions"].get(rec["name"]) or {}).get("released"):
            release(rec["name"])
            log(f"the {role}'s reasoning layer {rec['name']} is let go: its switch is off")


def role_layer_replied(s):
    import watchdog
    _, text, at = watchdog.last_reply(s["sid"])
    return at > (s.get("started") or 0) and ROLE_LAYER_DONE in text


def role_layer_build(role, why):
    """Ask for the role's evidence, and fork its layer once it is read (the next dispatch, or this one when the read
    runs at once)."""
    rec = role_layer_record(role)
    evidence = os.path.join(STATE, "role-evidence", f"{role}.md")
    asked = rec.get("evidence_asked") or 0
    try:
        fresh = asked and os.path.getmtime(evidence) >= asked
    except OSError:
        fresh = False
    if not fresh:
        if asked and time.time() - asked < ROLE_LAYER_BUILD_MAX:
            return  # being read
        with state() as w:
            w.setdefault("role_layers", {}).setdefault(role, {})["evidence_asked"] = time.time()
        background("role_evidence.py", role)
        try:
            if os.path.getmtime(evidence) < role_layer_record(role)["evidence_asked"]:
                return
        except OSError:
            return
    text = open(evidence, errors="ignore").read().strip()
    who = ROLES[role]["origin"]

    def prompt(name):
        return render("role-layer", NAME=name, ROLE=role, STALE=stale_of(name, who), PROTOCOL=generic_protocol(role),
                      EVIDENCE=text, PRACTICES=str(ROLE_LAYER_PRACTICES), DONE=ROLE_LAYER_DONE)
    name = launch("role-layer", role, prompt, tree=None, origin=who, layer_of=role)
    if name:
        with state() as w:
            r = w.setdefault("role_layers", {}).setdefault(role, {})
            r.update(building=name, evidence_asked=None)
        log(f"the {role}'s reasoning layer {name} is being built: {why}")


def context_of(sid):
    import ctx_gauge
    return ctx_gauge.context_tokens(transcript(sid))


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


def may_come_back(st, name, s):
    """Whether a producing session that has finished is held for its task's return: the task went back to the planner
    (its landing did not merge or failed twice, its commit was refused, a partial result, a second rejection) or has
    been queued again and not yet started, it is not near its window's end, and it ended within HOLD_MAX. On 2026-09-21
    and 22 a fresh session took over such a task 22 times — released when the task left its finalization, and forked
    anew when the planner queued it again — and made 177 requests (10.8M) before its first change, learning again what
    the session before it held (the owner: "find all such failures, where sessions are not reused")."""
    tid = s.get("task") or ""
    t = st["tasks"].get(tid) or {}
    if name not in (t.get("session"), t.get("previous_session")) or t.get("stage") not in NOT_STARTED:
        return False
    if t.get("lands_again"):
        return False  # it lands again by itself, with no session (lands_when_free)
    if os.path.exists(os.path.join(STATE, "flags", f"{s.get('sid')}.soft")):
        return False  # near its window's end: it could not take the task on again
    task = read_task(tid)
    if task is None or task.get("status") == "completed":
        return False
    return time.time() - (s.get("ended") or s.get("started") or 0) <= HOLD_MAX


def accepted_by(r):
    """The reviewer that accepted a review task's subject, kept through the planner's re-queue of a task reviewed as
    itself (its record is read afresh, and task 80's and 97's were)."""
    return r.get("reviewed_by") if r.get("verdict") == "accept" else r.get("previous_reviewer")


def reusable(tid, role):
    """The session that worked on a task last, when it can take it up again as it stands: held (may_come_back), warm,
    and of the role the task now asks for."""
    st = peek()
    t = st["tasks"].get(tid) or {}
    name = t.get("previous_session") or t.get("session")
    s = st["sessions"].get(name or "") or {}
    if s.get("role") != role or s.get("released") or s.get("state") != "done" or not s.get("sid"):
        return None
    return name if may_come_back(st, name, s) and warm(name) else None


def start_producer(tid):
    task = read_task(tid)
    brief = task["description"]
    kind = brief_kind(brief)
    role = PRODUCER[kind]
    brief_record(tid, brief)
    again = reusable(tid, role)
    sha = hashlib.sha1(brief.strip().encode()).hexdigest()
    if again:
        back = (peek()["tasks"].get(tid) or {}).get("back")
        same = (peek()["tasks"].get(tid) or {}).get("brief_sha") == sha  # it holds the brief it was started with
        with state() as st:  # its record first, as a resume reads it: a producing session, working again
            st["sessions"][again].pop("fix", None)
        if resume(again, f"Task {tid} is yours again: the planner has queued it once more"
                         + (f", after it went back to the planner:\n{back}" if back else ".")
                         + ("\n\nIts brief is as you have it." if same else
                            f"\n\nIts brief as it stands now, changed since you had it:\n\n{brief.strip()}")
                         + "\n\nContinue from where you stand; what the planner told the task meanwhile is in your mail."):
            with state() as st:
                t = task_state(st, tid)
                t.update(stage="running", session=again, role=role, brief_sha=sha)
                t.pop("previous_session", None)  # why it came back stays for the re-review (start_review)
                st.pop("start_failed", None)
            update_task(tid, status="in_progress", owner=again)
            log(f"task {tid} goes back to {again}, which worked on it last")
            return again
    base = base_record(ROLES[role]["origin"])[0] or "max"
    tree, why = task_tree(tid)  # once: the message says where the session is started because it is started there
    source_session, source = softly("the session a continuation forks", continued_session, peek(), tid, role,
                                    default=(None, None))
    more = dict(origin=source_session, continues=source) if source_session else {}
    name = launch(role, tid, lambda name: render(role, NAME=name, ID=tid, KIND=kind, SUBJECT=task.get("subject", ""),
                                                 BRIEF=brief.strip(), STALE=stale_of(name, base, tree), WHAT=PLANNED_FIX,
                                                 TREE=tree_text(tid, tree, why), INPUTS=softly("the brief's statements", inputs_read, brief, tree),
                                                 CONTINUED=continued_text(source_session, source, tid, tree) if source_session else ""),
                  tree=tree, task=tid, **more)
    if not name and source_session:  # the fork was not confirmed: the base, as for any other task, at the next dispatch
        log(f"task {tid} was not started from {source_session}, whose work it continues")
    with state() as st:
        t = task_state(st, tid)
        if name:
            t.update(stage="running", session=name, role=role, brief_sha=sha)
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
    if kind in ("check", "probe"):
        return bool(p.get("result"))
    if kind == "machine":  # the guard's own condition for its kind of run, so that it is not refused again at once
        queued = pending_claim()
        if queued and queued["task"] == tid:  # a measurement: the machine empty, which produce() gives it with
            return not isabelle_runs() and not exclusive_claim()
        return run_blocked((tid,), p.get("run") or "heavy") is None
    return False


PARKED_TEXT = {"fix": "The fix of the performance problem you parked for has landed (task {after}). Continue task {tid}.",
               "run": "The run you parked for has ended; its completion is in your context or below. Continue task {tid}.",
               "tree": "The working tree is yours: install what you drafted and continue task {tid}.",
               "answer": "The answer you parked for is in the mail below. Continue task {tid}.",
               "machine": "A run may start on the machine now: run your check and continue task {tid}.",
               "check": "{result}\n\nContinue task {tid}.",
               "probe": "{result}\n\nContinue task {tid}."}


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


# A worktree per producing task: each works in `.build/trees/ID`, a git worktree on the branch task/ID, so that no
# task's unfinished work holds another out of the tree it works in — which is what the one tree did whenever a task
# was parked, finalizing or given back with its work installed (2026-09-21: task 49, with the planner, held it
# against every producing task). Trees were turned off on 2026-09-20 after their first live run, for three faults,
# each repaired now where it arises:
# - a session started in a tree was invisible: `claude agents` lists it under that cwd and Claude Code keeps its
#   transcript under that tree's own directory, while session_row.py and every reader of a transcript looked under
#   the project's alone. On 2026-09-20 fix-49 and implement-46.3 started, ran and were unseen — their starts called
#   unconfirmed and their records released while they worked on (session_row.py, transcript);
# - a tree carries its own copy of the harness, which acted on a state of its own (_one_tree) and on the rules as
#   they stood at the commit the tree was made from (_one_harness);
# - a tree made from a HEAD that declares a theory whose file stands uncommitted refuses every check in 0.2 s: a new
#   tree is checked before a session is put in it (make_tree), a task whose ground is uncommitted in the one tree
#   works there (in_main_tree), and a task that would start from HEAD without what it stands on waits for it to
#   land (landing_wait).
TREES = os.environ.get("ORCH_TREES", "1") == "1"  # ORCH_TREES=0 for the one tree alone
TREE_DIR = ".build/trees"
ONE_HARNESS = "def _one_harness("  # in a tree's copy of the harness when that copy hands every call to the one harness


def transcript_dirs(base=None):
    """The directory of the project's transcripts and those of its task trees: Claude Code keeps the transcript of a
    session started in a task's own tree under that tree's directory, beside the project's, not in it."""
    base = base or TRANSCRIPTS
    return [base, *sorted(glob.glob(base + re.sub(r"[^A-Za-z0-9]", "-", f"/{TREE_DIR}/") + "*"))]


def transcript(sid):
    """A session's transcript, wherever it was started. Where no directory holds it, the project's path, whose
    absence the caller reads as it always has."""
    for d in transcript_dirs():
        path = os.path.join(d, f"{sid}.jsonl")
        if os.path.exists(path):
            return path
    return os.path.join(TRANSCRIPTS, f"{sid}.jsonl")


def standing_work():
    """{task: paths} of the work that stands uncommitted in the one tree, by the task that wrote it."""
    changed, out = set(changed_paths()), {}
    with owners(write=False) as o:
        for p, t in o.items():
            if p in changed:
                out.setdefault(str(t), []).append(p)
    return out


SHARED_FILES = ("ROOT", "THEORY_MAP.md", "DECISIONS.md", "HANDOFF.md", "PLANNING_LOG.md")


def in_main_tree(tid, standing=None):
    """Why this task works in the one tree rather than a tree of its own, or "" when it does not. A tree is a checkout of HEAD, so a task
    whose ground stands uncommitted in the one tree would not find it there: its own installed work (carrying that
    over would be the harness moving a change again), or a path its brief names — an input or a deliverable — while
    that path stands changed and uncommitted. Task 52, whose whole work is committing four batches installed there,
    would have found none of them in a tree of its own."""
    standing = standing_work() if standing is None else standing
    if standing.get(str(tid)):
        return "your task's own work stands there, uncommitted: " + ", ".join(sorted(standing[str(tid)])[:4])
    brief = (read_task(tid) or {}).get("description") or ""
    named = {os.path.normpath(p.split(":")[0]) for p in inputs(brief) + deliverables(brief, str(tid))}
    # but not the files every task writes a line of, nor the planner's: nearly every brief names THEORY_MAP.md, and
    # while one task in the one tree held a row of it uncommitted, every task started meanwhile was put there too —
    # tasks 56, 62 and 72 on 2026-09-22, and the one tree never emptied. A task in a tree of its own writes its own
    # line, which its landing merges (rows agreed, the landing waiting for the one tree's)
    there = sorted((named & set(changed_paths())) - set(SHARED_FILES))
    return (f"your brief names {', '.join(there[:4])}, which stand{'s' if len(there) == 1 else ''} uncommitted there "
            "and a tree made from HEAD would not have" if there else "")


def unlanded(standing=None):
    """{task: what of its work is not in HEAD}: its paths standing uncommitted in the one tree, and its own tree while
    that still holds a change or a commit not merged."""
    out = {t: list(p) for t, p in (standing_work() if standing is None else standing).items()}
    for x in trees_standing():
        if x["changed"] or x["commits"]:
            out.setdefault(x["task"], []).append(f"{TREE_DIR}/{x['task']} ({x['changed']} changed, {x['commits']} "
                                                 "commits not merged)")
    return out


def landing_wait(tid, tasks=None, pending=None):
    """(task, what) of the first task that task tid waits on — directly, or through the tasks those wait on — whose
    work has not landed in HEAD; None when there is none, or when tid works in the one tree, where that work is.
    A tree is made from HEAD, so a task started in one without the work it stands on would build on nothing: on
    2026-09-21 tasks 22 and 46 were completed in the graph with their theories uncommitted, and every task after them
    would have started from a HEAD that lacks both. Pure: deps_done says it, startable and the width only read it."""
    if not TREES or apart(tid):
        return None  # trees off, or already in its own tree: what it stands on was in HEAD when that was made
    tasks = tasks if tasks is not None else {}
    if brief_kind((tasks.get(tid) or read_task(tid) or {}).get("description") or "") not in PRODUCING_KINDS:
        return None  # a brief, a review or a design's verdict gets no tree: it reads the one tree, where the work is
    standing = standing_work()
    if in_main_tree(tid, standing):
        return None
    pending = unlanded(standing) if pending is None else pending
    if not pending:
        return None
    blockers = lambda t: (tasks.get(t) or read_task(t) or {}).get("blockedBy") or []
    seen, todo = set(), list(blockers(tid))
    while todo:
        d = todo.pop(0)
        if d in seen:
            continue
        seen.add(d)
        if pending.get(d):
            return d, pending[d]
        todo += blockers(d)
    return None


def task_tree(tid):
    """(tree, why): where a producing session on task tid is started — its own tree, made now if it has none, or None
    for the one tree, and then why. Decided once, and the session's message is written from the same answer, so that
    what it is told and where it is started cannot part (on 2026-09-20 they parted twice). A tree that cannot be made
    sound is not handed out: the task works in the one tree as with trees off, and the planner is told why, once for
    each reason."""
    if not TREES or not str(tid).isdigit():
        return None, "trees of their own are off"
    if worktree_of(tid) != PROJECT:
        return worktree_of(tid), ""  # it has one: its work is there
    why = in_main_tree(tid)
    if why:
        return None, why
    path, why = make_tree(tid)
    mark = os.path.join(STATE, "no-tree")
    if path:
        with contextlib.suppress(OSError):
            os.remove(mark)  # trees are made again: what stood in their way no longer does
        return path, ""
    told = open(mark).read() if os.path.exists(mark) else ""
    if told != why or (age_of("no-tree") or TREE_TOLD + 1) > TREE_TOLD:
        open(mark, "w").write(why)
        with state() as st:
            event(st, "the harness", f"Task {tid} works in the one tree, not a tree of its own: {why}. Every task that "
                  "would have had a tree works in the one tree meanwhile, where another's unfinished work can hold it "
                  "out; a tree is made again at the next start once this no longer stands.")
    log(f"ATTENTION task {tid} works in the one tree: {why}")
    return None, f"a tree of its own could not be made: {why}"


def worktree(tid):
    """The working tree of a task, made if it is not there and sound; None when it cannot be (make_tree says why)."""
    return make_tree(tid)[0]


def make_tree(tid):
    """(path, None), or (None, why): a git worktree on the branch task/<tid>, from HEAD, made if it is not there.
    Measured on 2026-09-20: a check inside one reused all 1,797 theories of the base in 172.88 s, so the heaps are
    bound to their session names and not to a path, and two tasks can hold their own trees. What that buys is the
    merge: a ROOT line, a DECISIONS entry and a THEORY_MAP row are lines, and git merges lines — which is the
    granularity every failure of that day lacked.

    A new tree is handed out only when it is sound: its copy of the harness hands every call to the one harness
    (a HEAD from before that rule would run its sessions under older rules), and it is consistent as a checkout of
    HEAD (tree_trouble), since a tree that is not refuses every check its task makes. One that is not is taken away
    at once — it holds nothing yet."""
    path = os.path.join(PROJECT, TREE_DIR, str(tid))
    if os.path.isdir(os.path.join(path, ".git")) or os.path.isfile(os.path.join(path, ".git")):
        return path, None
    os.makedirs(os.path.join(PROJECT, TREE_DIR), exist_ok=True)
    # `-B` resets a branch that is there: one left by a tree taken away before its commits were merged (a landing
    # that met a conflict) would lose them in silence. It is named instead, and its work waits for someone to say
    # which lines stand.
    ahead = git_out("rev-list", "--count", f"HEAD..task/{tid}", quiet=True)
    if ahead and int(ahead.strip() or 0):
        return None, (f"its branch task/{tid} holds {ahead.strip()} commit(s) that are not in main, and a new tree "
                      "would reset it: merge or drop that branch first")
    r = subprocess.run(["git", "-C", PROJECT, "worktree", "add", "-B", f"task/{tid}", path, "HEAD"],
                       capture_output=True, text=True)
    if r.returncode:
        why = f"git could not make it ({(r.stdout + r.stderr).strip()[-200:]})"
        log(f"could not make a working tree for task {tid}: {why}")
        return None, why
    harness = os.path.join(path, ".claude", "orchestration", "v2.py")
    if os.path.exists(harness) and ONE_HARNESS not in open(harness, errors="ignore").read():
        worktree_gone(tid)
        return None, ("HEAD's copy of the harness does not hand its calls to the one harness, so a session in a tree "
                      "would run the rules as they were committed rather than as they are: the harness has to be "
                      "committed first")
    trouble = tree_trouble(path)
    if trouble:
        worktree_gone(tid)
        return None, ("a tree made from HEAD is inconsistent, so every check in it would refuse — "
                      + "; ".join(trouble[:3]) + (f"; and {len(trouble) - 3} more" if len(trouble) > 3 else "")
                      + ". HEAD lacks what stands uncommitted in the one tree: trees are made again once it has landed")
    build_link(path)
    log(f"task {tid} has its own working tree at {TREE_DIR}/{tid} (branch task/{tid})")
    return path, None


def build_link(path):
    """The one .build linked into a tree made from the repository (a task's, or a landing train's integration tree)."""
    common = (git_out("rev-parse", "--git-common-dir") or ".git").strip()  # relative to the project, as git prints it
    exclude = os.path.join(common if os.path.isabs(common) else os.path.join(PROJECT, common), "info", "exclude")
    os.makedirs(os.path.dirname(exclude), exist_ok=True)  # `.build/` in .gitignore matches a directory, and the link
    if ".build" not in (open(exclude).read() if os.path.exists(exclude) else ""):  # below is a file: it would be
        with open(exclude, "a") as f:                                              # committed, and merging it would
            f.write("\n# the one .build, linked into every task's tree\n.build\n")  # replace the real directory
    link = os.path.join(path, ".build")
    if not os.path.lexists(link):
        os.symlink(os.path.join(PROJECT, ".build"), link)  # one .build: drafts, check outputs and their lineage


def worktree_of(tid):
    """The task's own working tree if it has one and trees are on, else the one tree.

    It read the directory alone, so a tree left behind by an earlier run captured its task for ever after
    ORCH_TREES was turned off. On 2026-09-20 that put fix-49.2's cwd in `.build/trees/49` — the tree the planner had
    declared discarded — while its message told it the same. finalize.py runs the check and makes the commit in this
    tree, so a task would have been checked and committed from a stale branch; and tree_trouble read it, which is
    where the two notices telling the planner that "the working tree is inconsistent" came from — the shared tree
    was consistent throughout and .build/trees/46 was not."""
    if not TREES:
        return PROJECT
    path = os.path.join(PROJECT, TREE_DIR, str(tid))
    return path if os.path.exists(path) else PROJECT


def apart(tid):
    """Whether task tid works in a tree of its own: what holds the one tree does not hold it, and its own check,
    finalization and park hold nothing of the one tree."""
    return bool(tid) and worktree_of(tid) != PROJECT


ONE_TREE_RULES = (
    "The tree has one owner at a time: while another task's finalization is in flight (its check, review, fix and "
    "commit), or another task's installed work stands in it unfinished, that task owns it, so that its check, review "
    "and commit see its changes alone. Meanwhile you read the working tree freely but write only under your task's "
    "directory: write new files there as drafts and probe them there, and keep your edits of existing files for "
    "after; you are told when the tree is yours, then install your drafts and continue. A producing session with "
    "nothing productive left meanwhile parks for it (`.claude/orchestration/v2.py park tree`); a final job is handed "
    "over only while the tree is the session's own. A finalization holds the files it will commit while its check "
    "runs, while a quick fix repairs them, and while it commits — not while it is reviewed: a review reads what was "
    "checked and writes nothing, so that window is when an append to a shared record (DECISIONS.md, THEORY_MAP.md, "
    "ROOT) lands. If yours is refused, you are told when the file is free. A task that leaves unfinished (parked, "
    "partial, lost) leaves its installed work **in the working tree, whole** — the harness moves none of it. A change "
    "here is a set of parts (a theory, the ROOT line declaring it, the import reaching it, its row, its entry) and a "
    "part taken out refuses every task's check, not only its own. If your brief says you continue that task's work, "
    "it is already there to continue.")


def tree_text(tid, tree=None, why=""):
    """Where the session works, said as it is: `tree` is where it is started (task_tree's answer), None for the one
    tree, and nothing else is consulted — the text and the start are one decision. Until 2026-09-20 every role was
    told it had a worktree of its own; then the text and the start read the directory apart from each other and
    parted twice. A session that believes it has a tree it has not writes into a path that is not there."""
    if tree:
        rel = os.path.relpath(tree, PROJECT)
        return (f"**Your working tree is your task's own.** You are started in it (`{rel}`, a git worktree on the "
                f"branch `task/{tid}`, made from HEAD), and no other session writes it: nothing another task leaves "
                "unfinished holds you out of it, and nothing you leave holds another. It is a whole checkout, and "
                "`.build` in it is the one `.build`: your drafts, the checks' output and their lineage are where they "
                "have always been. Install into it and check in it. Write nothing of the repository's own directory — "
                f"the absolute paths you hold from the library point there, and a write there is refused: write "
                f"`{rel}/<path>`, or the path relative to where you stand. Run a check from your tree by a path "
                "relative to it (`python3 -B tools/incremental_check.py …`): the tool takes its project from its own "
                "path, so the one tree's absolute path would check the one tree and not your work, and `v2.py "
                "finalize` refuses a check that names it. The finalizer checks and commits on your branch and brings "
                "it into the branch that is pushed, where your lines meet the lines other tasks wrote meanwhile — "
                "cleanly where they stand apart, and with a named conflict where two tasks wrote in the same place. "
                "When work has landed since your check, it is first brought into your branch and the two are checked "
                "together; if they do not stand together, that comes back to you as a failed check, in this tree. "
                "What your work stands on is in HEAD: a task you wait on has landed before you start. Work that "
                "landed in main after your tree was made is not in it: `.claude/orchestration/v2.py bring-main` brings "
                "main into your branch — the harness merges it and commits the merge alone, and what you have changed "
                "and not committed stands as it was; it is refused, with the files, where main changed one of yours. "
                "HANDOFF.md is the planner's in your tree as in any other.")
    reason = why or ("trees of their own are off" if not TREES else "it was not decided that you have one")
    return (f"**You work in the repository's one working tree**, not a tree of your own: {reason}. Another task's "
            "uncommitted work may stand beside yours, and a check reads the whole tree, so a failure in it may be "
            "another task's — say so rather than repairing what is not yours. Install into it, check in it, and the "
            f"finalizer commits from it. {ONE_TREE_RULES} HANDOFF.md is the planner's here as everywhere.")


def review_text(tid, tree=None):
    """Where the work a reviewer judges stands, when that is not the one tree; its session is started there."""
    if not tree:
        return ""
    rel = os.path.relpath(tree, PROJECT)
    return (f"The work stands in its task's own tree, `{rel}` (a git worktree on the branch `task/{tid}`), and you are "
            "started there: read it there, not in the repository's own directory — the absolute paths you hold from "
            "the library point there, and the work is not there until it is committed. `v2.py read` reads that tree. "
            "You write nothing but your verdict.")


def tree_of(rec):
    """The tree the session this record is of was started in, which is where it works and where it is resumed: its
    task's own (a producing session), the reviewed task's (a reviewer of work in a tree), or the one tree. It is what
    launch recorded, not what the task's directory says now: a session resumed anywhere else would be told one tree
    and stand in another. A tree taken away since leaves the one tree."""
    path = os.path.join(PROJECT, (rec or {}).get("tree") or "")
    return path if (rec or {}).get("tree") and os.path.isdir(path) else PROJECT


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
        if not tid.split(".")[0].isdigit():
            continue  # a landing train's or a check batch's tree (train.py, train-a, check-b): reset for every use
        tree = os.path.join(root, tid)
        changed = [p for p in (git_out("status", "--porcelain", tree=tree) or "").splitlines() if p.strip()]
        ahead = len([l for l in (git_out("log", "--format=%h", f"main..task/{tid}") or "").splitlines() if l])
        out.append({"task": tid, "changed": len(changed), "commits": ahead})
    return out


def trees_tidied():
    """Take away every tree that holds nothing: no uncommitted change and no commit of its own."""
    gone = []
    for x in trees_standing():
        # a task still under way keeps its tree even empty: a session parked before it wrote anything is resumed
        # there, told it is its own, and a tree taken from under it would leave it writing into a path that is gone
        stage = (peek()["tasks"].get(x["task"]) or {}).get("stage")
        if not x["changed"] and not x["commits"] and stage not in ("running", "parked", *FINISHING):
            worktree_gone(x["task"])
            gone.append(x["task"])
    return gone


def merged(tid):
    """Bring a task's branch into the one that is pushed. Its lines meet the lines that landed meanwhile, and git
    says which did not meet: a conflict is reported, never resolved behind the tasks."""
    r = subprocess.run(["git", "-C", PROJECT, "merge", "--no-ff", "--no-commit", f"task/{tid}"], capture_output=True,
                       text=True)
    if r.returncode == 0:
        # the planner's state is committed with every task's work, as a commit made in the one tree takes it: with
        # every task in a tree of its own, nothing committed it at all
        if subprocess.run(["git", "-C", PROJECT, "status", "--porcelain", "--", "HANDOFF.md"], capture_output=True,
                          text=True).stdout.strip():
            subprocess.run(["git", "-C", PROJECT, "add", "--", "HANDOFF.md"], capture_output=True, text=True)
        merging = subprocess.run(["git", "-C", PROJECT, "rev-parse", "-q", "--verify", "MERGE_HEAD"],
                                 capture_output=True, text=True).returncode == 0
        if not merging:
            return None  # nothing to take up
        r = subprocess.run(["git", "-C", PROJECT, "commit", "--no-edit", "-m", f"Take up the work of task {tid}"],
                           capture_output=True, text=True)
    if r.returncode == 0:
        return None
    conflicts = [l.split("\t")[-1] for l in (subprocess.run(
        ["git", "-C", PROJECT, "diff", "--name-only", "--diff-filter=U"], capture_output=True,
        text=True).stdout or "").splitlines()]
    subprocess.run(["git", "-C", PROJECT, "merge", "--abort"], capture_output=True, text=True)
    log(f"the work of task {tid} does not merge: {', '.join(conflicts) or (r.stdout + r.stderr).strip()[-300:]}")
    return conflicts or [f"(git: {(r.stdout + r.stderr).strip()[-200:] or 'the merge failed without naming a file'})"]


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


def hold_of(t):
    """How long a parked task is held before it records a partial result: HOLD_TREE when it waits for the one tree or
    for the machine — a turn that always comes, only later when others' checks and landings are many — HOLD_PARK for
    anything else, a fix, an answer or a run that may never come. Task 94, parked for a heavy slot at 05:55 on
    2026-09-22, waited behind a stream of landings and a measurement for two hours with an hour of its three left."""
    return HOLD_TREE if (t.get("parked") or {}).get("for") in ("tree", "machine", "check", "probe") else HOLD_PARK


def hold_left(t):
    """Seconds until a parked task's hold ends (hold_of: then it records a partial result), or None."""
    since = (t.get("parked") or {}).get("since")
    return hold_of(t) - (time.time() - since) if since else None


def resume_order(st):
    """The parked tasks, in the order the producing slot resumes those whose wait is over (the owner, 2026-09-21): one
    whose hold ends within PARK_URGENT first, the nearest first; then the planner's order, its queue; then what the
    queue does not name, the longest parked first. It was the longest parked first alone, and the planner had no way
    to say that the landing which ended the one-tree queue should take the tree next (plan-32, Q8)."""
    place = {tid: i for i, tid in enumerate(st["queue"])}

    def rank(tid):
        t = st["tasks"][tid]
        left = hold_left(t)
        if left is not None and left <= PARK_URGENT:
            return (0, left)
        return (1, place[tid]) if tid in place else (2, (t.get("parked") or {}).get("since", 0))
    return sorted((tid for tid, t in st["tasks"].items() if t.get("stage") == "parked"), key=rank)


def produce():
    """A producing slot: a parked task whose wait is over first (its changes come back into the free working tree),
    in resume_order, then the first ready task in the queue. Up to PRODUCERS_MAX at once, within WORKERS_MAX; the
    second only when no review waits for a slot."""
    if graph_held():
        return
    st = peek()
    live = producing(st)
    if len(live) >= PRODUCERS_MAX:
        return
    if at_capacity(st):
        return  # at most WORKERS_MAX sessions work at a time (the owner's rate)
    if live and not support_apart() and not slot(st, SUPPORTING) and pending_reviews(st):
        return  # the free slot is a review's: support() takes it (apart, a review has a slot of its own)
    for tid in resume_order(st):
        t = st["tasks"][tid]
        p = t.get("parked") or {}
        if parked_ready(st, tid, p):  # before any new task
            text = (PARKED_TEXT.get(p.get("for", "fix"), PARKED_TEXT["fix"]).format(
                        after=p.get("after"), tid=tid, result=p.get("result", ""))
                    if p.get("after") != "none" else f"Continue task {tid} as it is; the planner's answer is in the mail.")
            queued = pending_claim() if p.get("for") == "machine" else None
            if queued and queued["task"] == tid:  # its measurement: the machine is its own, from this resume on
                grant(queued, seen=True)  # its resume says so
                text = MACHINE_YOURS.format(why=queued["why"], minutes=int(CLAIM_GRACE) // 60, tid=tid)
            elif p.get("for") == "machine" and (p.get("run") or "heavy") != "probe":
                machine_turn(tid)  # its turn is held until its check starts: a finalizer would take the slot meanwhile
            holder = tree_holder(st, {"task": tid})
            with state() as w:
                w["tasks"][tid]["stage"] = "running"
                w["tasks"][tid].pop("parked", None)
                fixer = w["sessions"].get(t.get("session") or "") or {}
                if fixer.get("fix") and p.get("since"):
                    # a quick fix's budget is its own work, and the wait was the harness's: fix-22 parked for the tree
                    # two minutes into its fifteen and would have come back past them, ended at its first idle moment
                    # (2026-09-21)
                    fixer["fix"]["since"] += time.time() - p["since"]
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


FIRST_READ = ("result", "log", "probes", "restated", "tree", "diff")


REREAD = ("result", "log", "probes", "restated")  # a re-review's first read: the diff it judged it has, whole


def first_read(tid, sources=FIRST_READ):
    """What a reviewer's first batch reads, read for it and given in its first message: the task's result, the end of
    its finalizer's log, its probes and its diff — as `v2.py read result log probes diff` shows them, each bounded as a
    read bounds it and the diff last, whole where it fits and otherwise as much as the batch's room holds, with how to
    read the rest. Every reviewer of 2026-09-22 opened with that batch (104 of 104), a request each, before it could
    judge anything; the texts are written once either way."""
    out, size = [], 0
    for src in sources:
        text = read_source(src, tid, False, [], {"reads": {}}).rstrip()
        head = f"== {src}\n"
        room = BATCH_BYTES - size - len(head.encode()) - 1
        if src == "diff":
            body = one_read(text, max(room, READ_BYTES))
        else:
            body = one_read(text, min(source_bound(), max(room, 0)) or 1)
        part = head + body + "\n"
        out.append(part)
        size += len(part.encode())
    return "".join(out).rstrip("\n")


def start_review(rid, tid):
    """The review task rid of the finished task tid (rid is tid itself when no review task was briefed: a review
    planned by the harness from the task's brief). The one who judged it before is resumed while warm for a re-review;
    otherwise a new reviewer forks the middle base."""
    st = peek()
    t, r = st["tasks"][tid], st["tasks"].get(rid) or {}
    task, review = read_task(tid) or {}, read_task(rid) or {}
    before = r.get("reviewed_by")
    if before and r.get("verdict") == "reject":
        checked = ("its check runs beside your review" if t.get("stage") == "checking" else "its check passes again")
        text = (f"The findings you listed on task {tid} are fixed and {checked}. Judge those findings and "
                "whatever the fix itself broke; add nothing else. Write the verdict again and record it "
                f"(`v2.py verdict {rid} accept|reject --file .build/tasks/{rid}/review.md`).\n\nWhat your re-review "
                "reads first, read for you — as `v2.py read result log probes restated` shows it now (review-251 "
                "read it again in a request of its own, 2026-09-22):\n\n"
                + softly("the re-review's first read", first_read, tid, REREAD, default="(it could not be read: read it)"))
        if resume(before, text):
            return before
    before = accepted_by(r) if r.get("verdict") != "reject" else None
    held_before = (st["sessions"].get(before or "") or {})
    if before and not held_before.get("released") \
            and not os.path.exists(os.path.join(STATE, "flags", f"{held_before.get('sid')}.soft")):
        # the reviewer that accepted it, held while it had not landed (watchdog.held): it knows the work, and judges
        # what changed since — a fresh one read it all again, 11 times on 2026-09-21/22 (119 requests, 9.1M)
        text = (f"Task {tid}, which you accepted, did not land and was worked on again"
                + (f" ({t['back'][:600]})" if t.get("back") else "") + "; its check passes again. Judge what changed "
                "since your verdict (`v2.py read diff` is its whole diff now) and whatever that broke; what you accepted "
                "and nothing since touched stands. Write the verdict again and record it "
                f"(`v2.py verdict {rid} accept|reject --file .build/tasks/{rid}/review.md`).")
        if resume(before, text):
            with state() as w:
                w["tasks"].get(tid, {}).pop("back", None)
            return before
    own = rid != tid
    tree = worktree_of(tid) if apart(tid) else None  # the work it judges stands there until it is committed
    name = launch("reviewer", rid, lambda name: render(
        "reviewer", NAME=name, ID=rid, TASK=tid, SUBJECT=task.get("subject", ""), WHERE=review_text(tid, tree),
        REVIEW=(review.get("description") or "").strip() if own else "(no review task was briefed: judge the task "
        "against its brief, step by step, then against the principles)",
        BRIEF=(task.get("description") or "").strip(), SESSION=t.get("session", "-"),
        STALE=stale_of(name, base_record("xhigh")[0] or "max", tree), FIRST=first_read(tid),
        INPUTS=softly("the brief's statements", inputs_read, task.get("description") or "", tree),
        CHECKED=CHECK_BESIDE if t.get("stage") == "checking" else CHECK_PASSED,
        BEFORE=f"A previous review rejected it; its findings are in .build/tasks/{rid}/review.md. Judge those findings "
               "and whatever the fix broke; add nothing else." if r.get("verdict") == "reject" else ""),
        tree=tree, task=rid, reviews=tid)
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
        STALE=stale_of(name, base_record("xhigh")[0] or "max"),
        INPUTS=softly("the brief's statements", inputs_read, task.get("description") or "", None)),
        task=tid)
    with state() as w:
        if name:
            w["tasks"][tid].update(stage="running", session=name, role="task-designer")
    if name:
        update_task(tid, status="in_progress", owner=name)
    return name


def pending_reviews(st):
    """(review task, reviewed task) pairs to start: every review task of a finished task in review that has no verdict
    this round (or rejected it last round), and a review planned by the harness for a build or fix nobody briefed one for."""
    out, beside = [], review_beside_check()
    for tid, t in st["tasks"].items():
        if t.get("kind", "build") not in ("build", "fix") or not (
                t.get("stage") == "reviewing" or (beside and t.get("stage") == "checking")):
            continue
        rids = held_reviews(t)
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
        if all((tasks.get(b) or {}).get("status") == "completed" for b in blockers) \
                and not landing_wait(tid, tasks):  # produce() waits for it too: the report agrees with the dispatch
            out.append(tid)
    return out


def waiting_behind(tids, tasks=None):
    """{task: how many open tasks wait on it, directly or through others}: what starting it first would release —
    for the planner's order, which puts dependency before size (planner.md), where a task's wait to start was a third
    of its way on 2026-09-22, most of it on its blockers."""
    tasks = tasks if tasks is not None else {t["id"]: t for t in all_tasks()}
    after = {}
    for k, v in tasks.items():
        if v.get("status") != "completed":
            for b in v.get("blockedBy") or []:
                after.setdefault(b, set()).add(k)
    out = {}
    for tid in tids:
        seen, todo = set(), list(after.get(tid, ()))
        while todo:
            x = todo.pop()
            if x not in seen:
                seen.add(x)
                todo += after.get(x, ())
        out[tid] = len(seen)
    return out


def kind_of(task):
    """A task's kind, from its metadata or its brief."""
    return (task.get("metadata") or {}).get("kind") or field(task.get("description", ""), "Kind")


def graph_shape(kinds=None, skip=(), tasks=None):
    """(width, depth, open) of the task graph as it is drawn, over the tasks that are not completed.

    width  — how many of them have every blocker completed: the work that could run at all, which is what
             concurrency is made of. Not startable(), which also asks whether a task is queued and in form.
    depth  — the longest chain of open tasks: how many turns of the producing slot the last of them waits for.

    The two say what a count of open tasks cannot. On 2026-09-20 the graph held 33 open tasks, 17 of them build or
    fix, and every brief was detained because 17 >= 6 — while its width was 8 and only 5 of those 17 could start at
    all, and its depth was 20, one task wide for 14 of those levels. Counting what exists detains the very work that
    would have widened it; counting what can run says the opposite, and says it for the right reason."""
    # `tasks` measures a graph that is not written: the one a proposal would make (proposal_text)
    tasks = tasks if tasks is not None else {t["id"]: t for t in all_tasks()}
    # The chain is walked over every open task and only counted over the kinds asked for: a build task waits on the
    # review of the build before it, so filtering the walk by kind cuts the chain at every review and reports a
    # depth of 3 for one that is 20 long.
    every = {k: v for k, v in tasks.items() if v.get("status") != "completed"}
    blocked = {k: [b for b in (v.get("blockedBy") or []) if (tasks.get(b) or {}).get("status") != "completed"]
               for k, v in every.items()}
    open_ = {k: v for k, v in every.items() if kinds is None or kind_of(v) in kinds}
    depths = chain_depths(tasks)
    # `skip` leaves a task out of the WIDTH while still walking it for the depth: a task that came back to the
    # planner has every blocker done and so counted as concurrency, though no slot can take it. Two of those would
    # have held the width at the slots for ever and detained every brief, with only the planner able to move them
    # and nothing saying so (2026-09-20).
    return (sum(1 for k in open_ if not blocked[k] and k not in skip),
            max([depths.get(k, 0) for k in open_], default=0),
            len(open_))


def chain_depths(tasks=None):
    """{task: the length of the longest chain of open tasks that ends at it} — the depth the owner's rule reads, per
    chain: a task whose chain is deeper than GRAPH_DEPTH takes no further goal hung after it. Completed tasks end no
    chain, and a cycle cannot lengthen one: the graph is not trusted to be free of them."""
    tasks = tasks if tasks is not None else {t["id"]: t for t in all_tasks()}
    blocked = {k: [b for b in (v.get("blockedBy") or []) if (tasks.get(b) or {}).get("status") != "completed"
                   and b in tasks] for k, v in tasks.items() if v.get("status") != "completed"}
    seen = {}

    def chain(tid, path=()):
        if tid in seen:
            return seen[tid]
        if tid in path or tid not in blocked:
            return 0
        seen[tid] = 1 + max([chain(b, path + (tid,)) for b in blocked[tid]], default=0)
        return seen[tid]

    return {k: chain(k) for k in blocked}


def past_the_limit(group, after):
    """Of the tasks in `group` ({name: {"blockedBy", "feeds"}}, placed into the graph `after`, where their names are
    their ids): those that would be added at the end of a chain already deeper than GRAPH_DEPTH — (name, that
    chain's depth). The owner's rule, per chain: "I do not allow to add to the end of a task chain if it is above 10
    in depth", so that the queue cannot balloon (2026-09-21). A task is at the end when nothing already there waits
    on it, directly or through the group (`spliced`: detail is admitted at any depth), and
    it is not a review — a review waits on the build it judges, which every build must have. The group's own
    chains count: a brief that hung a chain of its own after one of 10 would add past the limit as surely as ten
    single edits would."""
    detail = spliced(group, after)  # read on the graph as it would stand: an edit may re-point work onto a new task
    depths, out = chain_depths(after), []
    for name, e in group.items():
        if name in detail or brief_kind((after.get(name) or {}).get("description") or "") == "review":
            continue
        deepest = max([depths.get(b, 0) for b in e.get("blockedBy") or []
                       if (after.get(b) or {}).get("status") not in ("completed", None)], default=0)
        if deepest > GRAPH_DEPTH:
            out.append((name, deepest))
    return out


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
    # and one that waits for the work it stands on to land: no slot can take it until then either
    tasks = {t["id"]: t for t in all_tasks()}
    taken |= {tid for tid, t in tasks.items() if tid not in taken and t.get("status") != "completed"
              and kind_of(t) in ("build", "fix")
              and all((tasks.get(b) or {}).get("status") == "completed" for b in t.get("blockedBy") or [])
              and landing_wait(tid, tasks)}
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
    if at_capacity(st, support=True):
        return  # at most WORKERS_MAX sessions work at a time (the owner's rate), unless the supporting one is apart
    for tid, t in st["tasks"].items():
        if t.get("stage") == "proposed" and t.get("revise"):  # a correction first: its designer holds the brief
            revise_now(tid)
            return
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
            task, (tree, why) = read_task(tid) or {}, task_tree(tid)  # the task's own tree, where its work is
            name = launch("fixer", tid, lambda name: render(
                "fixer", NAME=name, ID=tid, BRIEF=(task.get("description") or "").strip(), WHAT=text,
                STALE=stale_of(name, base_record("high")[0] or "max", tree), TREE=tree_text(tid, tree, why),
                INPUTS=softly("the brief's statements", inputs_read, task.get("description") or "", tree)), tree=tree,
                task=tid, fix={"since": time.time()})
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
        # a consultation of a session that reads statements only reads as it does (statements_only, the guard), and
        # the knowledge base's own protocol never said so to the forks that answer for it (2026-09-21)
        reads = ROLES[(peek()["sessions"].get(origin) or {}).get("role", "kb")]["statements"]
        name = launch("consultant", qid, lambda name: render(
            "consultant", NAME=name, ID=qid, QID=qid, ASKER=q["from"], TARGET=origin, QUESTION=q["text"], NOTE=note,
            STALE=stale_of(name, consulted_base(origin)), READING=STATEMENTS_READ if reads else ""),
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
        HANDOFF_DELTA=softly("the handoff's delta", handoff_delta, peek()["kb"]),
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


RETURNED_AFTER = int(os.environ.get("ORCH_RETURNED_AFTER", 1800))
STALL_AFTER = int(os.environ.get("ORCH_STALL_AFTER", 300))  # a review nothing will start: said sooner, nothing waits on it  # how long a task may stand with the planner unnamed


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


LANDS = ("build", "fix")  # the kinds whose work is committed: complete when it has landed, and reviewed before it does


def held_reviews(t):
    """The review tasks of a task that the graph still holds: one the planner deleted judges nothing."""
    return [r for r in (t.get("review_tasks") or []) if read_task(r) is not None]


def deciding(t, tid, st=None):
    """The reviews whose verdicts decide task tid: its review tasks the graph still holds or that have given their
    verdict, or the task itself when it has none (the review the harness planned). A design or an investigation is the
    planner's to judge, and no reviewer is ever started for one: its verdict decides alone. Design 66 waited half an
    hour after the planner accepted it, for review task 67 — deleted from the graph, and one nothing would ever have
    judged (2026-09-22)."""
    if t.get("kind", "build") not in ("build", "fix"):
        return [str(tid)]
    tasks = (st or peek())["tasks"]
    return [r for r in (t.get("review_tasks") or []) if read_task(r) is not None or (tasks.get(r) or {}).get("verdict")] \
        or [str(tid)]


def review_accepted(st, tid):
    """Whether every review of task tid has accepted it: its review tasks, or the review the harness planned on it (a
    design's or an investigation's verdict is the planner's, recorded the same way)."""
    t = st["tasks"].get(str(tid)) or {}
    return all((st["tasks"].get(r) or {}).get("verdict") == "accept" for r in deciding(t, tid, st))


def reopen_unlanded():
    """A build or fix is complete when it has landed: its check passed, its review accepted it, and the finalizer
    committed it — review before commit, never after (the owner, 2026-09-21). The planner completed tasks 22, 46, 48
    and 50 on taking stock with their work uncommitted and unreviewed, planned one task to commit all four and their
    reviews to run beside the next build; the reviews could then never start, since a review is started for a task in
    review. Such a task is taken back into the flow at the step it is owed: its check when it has a final job and no
    accepted review, its commit when its review accepted it, and the planner otherwise (no final job: someone must
    finish it). The planner can no longer complete one by hand (work_meter), so this meets only what came before."""
    st, pending = peek(), unlanded()
    for tid, what in sorted(pending.items()):
        task = read_task(tid)
        if not task or task.get("status") != "completed" or brief_kind(task.get("description") or "") not in LANDS:
            continue
        final = os.path.exists(os.path.join(BUILD, tid, "finalize.json"))
        accepted = review_accepted(st, tid)
        stage = ("committing" if accepted else "checking") if final else "planner"
        # The hold holds the graph's work, the harness's own reopening too: while the planner has not said what of the
        # old graph stands, the check or commit waits for its order (release_held_finalizers). On 2026-09-21 a fresh
        # start's hold stood and three reopened checks started at once, together, and failed under the load.
        held = stage in ("checking", "committing") and bool(graph_held())
        update_task(tid, status="in_progress")
        with state() as w:
            t = w["tasks"].setdefault(tid, {})
            t.update(stage=stage, kind=brief_kind(task.get("description") or ""), reopened=time.time())
            t.pop("finishing_since", None)
            if held:
                t["held_finalizer"] = stage
            event(w, "the harness", f"Task {tid} was completed in the graph, but its work never landed: "
                  f"{', '.join(what[:4])} stand{'s' if len(what) == 1 else ''} uncommitted and "
                  + ("its review accepted it" if accepted else "no review has accepted it")
                  + ". A build or fix is complete when it has landed — its check passes, its review accepts it, the "
                  "finalizer commits it — so the harness has taken it back: "
                  + ({"checking": "its check runs " + ("once your order releases the graph" if held else "now")
                                  + ", then its review, then its commit",
                      "committing": "its commit is made " + ("once your order releases the graph" if held else "now"),
                      "planner": "it has no final job, so it is yours to have finished (queue it, and a session "
                                 "finishes it and hands it over)"}[stage])
                  + ". It cannot be completed by hand; a task that commits another's work is refused while that "
                  "work is unreviewed.")
        log(f"task {tid} was completed without landing; taken back to {stage}" + (", held with the graph" if held else ""))
        if stage in ("checking", "committing") and not held:
            background("finalize.py", "check" if stage == "checking" else "commit", tid)


def release_held_finalizers():
    """The checks and commits reopen_unlanded held back while the graph was held, started once it is not; one whose
    task the planner has moved elsewhere meanwhile is only let go."""
    if graph_held():
        return
    for tid, t in peek()["tasks"].items():
        held = t.get("held_finalizer")
        if not held:
            continue
        with state() as w:
            w["tasks"][tid].pop("held_finalizer", None)
            w["tasks"][tid].pop("finishing_since", None)
        if t.get("stage") == held:
            log(f"task {tid}: the graph is released, so its {'check' if held == 'checking' else 'commit'} starts")
            background("finalize.py", "check" if held == "checking" else "commit", tid)


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
    reopen_unlanded()  # first: a build completed without landing is taken back, not healed into done
    release_held_finalizers()
    link_reviews()
    st = peek()
    heal = [tid for tid, x in st["tasks"].items() if (x or {}).get("stage") in NOT_STARTED
            and (read_task(tid) or {}).get("status") == "completed"]
    if heal:
        with state() as w:
            for tid in heal:
                w["tasks"][tid]["stage"] = "done"
        log("the stage of " + ", ".join(sorted(heal)) + " followed the task list: they are completed")
    for tid, x in sorted(st["tasks"].items()):
        if (x or {}).get("stage") in NOT_STARTED + ("done", "deleted"):  # deleted: taken out by the planner's edit
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
    due = {x for _, x in pending_reviews(st)}
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
        # a finished build or fix in review that no review is due for and none is running, and that is not accepted:
        # nothing will start one, and its finalization holds what it holds. A review waiting for the slot is due, so
        # this is only ever the harness's own bookkeeping gone wrong (task 46, 2026-09-21: nine tasks parked behind it)
        stalled = (stage == "reviewing" and t.get("kind", "build") in ("build", "fix") and bool(held_reviews(t))
                   and tid not in due and not review_accepted(st, tid)
                   and not any((st["tasks"].get(r) or {}).get("reviewing") for r in held_reviews(t)))
        owed = tid in mine or (stage == "proposed" and t.get("proposal") and not t.get("revise")) \
            or stage == "unformed" or orphan or judge or stalled
        if not owed:
            with contextlib.suppress(OSError):
                os.remove(mark)  # cleared: the next time it comes back is counted afresh
            continue
        try:  # the file holds when it first stood there; its mtime is when that was last said
            since = time.time() - float(open(mark).read())
        except (OSError, ValueError):
            open(mark, "w").write(str(time.time()))
            continue
        after = STALL_AFTER if stalled else RETURNED_AFTER
        if since < after or (age_of(f"returned-{tid}") or 0) < after:
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
        if stalled:
            log(f"ATTENTION task {tid} stands in review with no review due and none running: the harness's own "
                f"bookkeeping (its rejections against its review tasks' rounds) — nothing will move it")
            with state() as w:
                event(w, "the harness", f"Task {tid} has stood {int(since // 60)} minutes in review with no review "
                      "due and none running, so nothing will start one, and what its finalization holds stays held. "
                      "It is the harness's bookkeeping, not your plan; the owner is told.")
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
                  "has not been re-planned, and nothing else moves it. Re-plan it — rewrite what must change, then "
                  f"queue it (`v2.py queue {tid}`, in your order): a rewrite alone does not restart it —, split it "
                  "over what exists, or drop it (`v2.py drop`) — while it stands, anything that waits on it waits for "
                  "ever."
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


def check_outputs():
    """{directory: task ids naming it} of the check outputs under the build directory: `.build/check-*` — named by a
    task's finalize.json or finalized.json, a rerun (`-2`, `-3`: the finalizer's, beside the evidence of the run
    before) with the name it reruns — and the checks inside a task's own directory (a directory holding a check's
    incremental.json, or its recipes), that task's."""
    named = {}
    for f in glob.glob(os.path.join(BUILD, "*", "finalize*.json")):
        tid = os.path.basename(os.path.dirname(f))
        with contextlib.suppress(OSError):
            for n in re.findall(r"\.build/(check-[\w.-]+)", open(f, errors="ignore").read()):
                named.setdefault(n, set()).add(tid)
    out = {}
    for d in glob.glob(os.path.join(PROJECT, ".build", "check-*")):
        if os.path.isdir(d) and not os.path.islink(d):
            n = os.path.basename(d)
            out[d] = named.get(n, set()) | named.get(re.sub(r"-\d+$", "", n), set())
    for d in glob.glob(os.path.join(BUILD, "*", "*")):
        tid, name = os.path.basename(os.path.dirname(d)), os.path.basename(d)
        # a task's own checks, by the names checks are given — never another directory that holds recipes: a base
        # being made (`.build/tasks/base-advance/base-…`, task 82's) is one, and no task's number names that directory
        if tid.isdigit() and re.match(r"(?:check|landing-|final-check)", name) and os.path.isdir(d) \
                and not os.path.islink(d) and (os.path.exists(os.path.join(d, "incremental.json"))
                                               or os.path.isdir(os.path.join(d, "recipes"))):
            out[d] = {tid}
    return out


def superseded_checks(st):
    """The check outputs nothing will read again: every task that names one has landed or left the graph, and it is
    not the newest of those — `incremental_check.py retain` reads the check of the last landing — or it is named by no
    task and older than CHECK_KEEP. A check's output is about 3 GB, and nothing removed them: 46 of them and those in
    tasks' directories stood at 131 GB on 2026-09-22 (the owner: superseded check outputs are removed as soon as they
    are no longer needed). A check of a task in flight is its review's and its fix's evidence, and stays."""
    def finished(tid):
        g = read_task(tid)
        return g is None or g.get("status") == "completed"
    outputs, now = check_outputs(), time.time()
    landed = [d for d, ts in outputs.items() if ts and all(finished(t) for t in ts)]
    newest = max(landed, key=lambda d: os.path.getmtime(d), default=None)
    read = read_by_the_living(st)
    return sorted(d for d, ts in outputs.items()
                  if ((d in landed and d != newest) or (not ts and now - os.path.getmtime(d) > CHECK_KEEP))
                  and os.path.relpath(d, PROJECT) not in read)


def read_by_the_living(st):
    """The build directory's paths that a session still at work names — in the commands it keeps (its newest
    KEPT_COMMANDS) and in the scripts under its task's directory — as one text: a check output named there is read
    again, whatever landed. Task 128 measured against task 126's landing export, `.build/tasks/126/landing-1/
    exports-context`, and the sweep took it once 126 had landed: a check of the base tree ran again to make it anew
    (2026-09-22)."""
    parts = []
    for name, s in st["sessions"].items():
        if s.get("released") or s.get("state") == "lost":
            continue
        for f in glob.glob(os.path.join(outputs_of(name), "commands", "*.sh")):
            with contextlib.suppress(OSError):
                parts.append(open(f, errors="ignore").read())
        tid = s.get("task")
        for f in glob.glob(os.path.join(BUILD, str(tid), "**", "*.sh"), recursive=True)[:200] if tid else []:
            with contextlib.suppress(OSError):
                if os.path.getsize(f) < 200_000:
                    parts.append(open(f, errors="ignore").read())
    text = "\n".join(parts)
    return {m.rstrip("/") for m in re.findall(r"\.build/(?:tasks/[\w.-]+/)?(?:check|landing|final-check)[\w.-]*", text)}


def tidied():
    """State that outlives what it was about: a wake mark once its session is long gone, and the frozen sources of a
    base no base names any more. Every one of the day's stalls was state nobody removed, and these are the harmless
    end of that class — removed rather than left to be read by someone later."""
    if (age_of("tidied") or TIDY_EVERY + 1) < TIDY_EVERY:
        return []
    open(os.path.join(STATE, "tidied"), "w").write(str(time.time()))
    with contextlib.suppress(Exception):
        prune_bases()  # a landing check's base whose landing did not happen, and the bulk of the lineage's levels
    with contextlib.suppress(Exception):
        prune_combined_outputs()  # the bulk of the trains' and batches' checks, their reports kept
    packs = set()
    for who in BASES:
        try:
            packs.add(json.load(open(os.path.join(STATE, f"{who}-base.json"))).get("pack"))
        except (OSError, ValueError):
            packs.add(None)
        # and the packs of what is being loaded: a base loaded again for its layer, a base being built. The pack of a
        # load in progress is read chunk by chunk and checked at its seal: named by no record yet, it went with the
        # hourly sweep (the max layers' packs of 22:24 and 22:39 on 2026-09-21, after their seal); one younger than a
        # load can take is spared whatever names it
        for part in ("layer", "base-next", "base-building"):
            with contextlib.suppress(OSError, ValueError):
                packs.add(json.load(open(os.path.join(STATE, f"{who}-{part}.json"))).get("pack"))
    sweep_packs = None not in packs  # a base whose record cannot be read: its pack is not swept on a guess
    gone = trees_tidied()  # written for this sweep and never called from it, so a tree holding nothing stayed
    swept = superseded_checks(peek())
    for d in swept:
        shutil.rmtree(d, ignore_errors=True)
        with contextlib.suppress(OSError):
            os.remove(d + ".out")  # the log a check beside the directory wrote
    if swept:
        gone.append(f"{len(swept)} superseded check output(s)")
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
        elif sweep_packs and name.startswith("base-pack-") and os.path.isdir(path) and path not in packs \
                and (age_of(name) or 0) > PACK_KEEP:
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
    holding |= {(delta_record(who) or {}).get("sessionId") for who in BASES}  # the delta standing, forked or not
    standing = {(delta_record(who) or {}).get("text") for who in BASES}
    for name in os.listdir(STATE):  # a delta's text is read by the next build only: the standing ones stay
        path = os.path.join(STATE, name)
        if re.fullmatch(r"(max|xhigh|high)-delta-\d{8}T\d{6}\.(md|json|list)", name) and path not in standing \
                and (age_of(name) or 0) > PACK_KEEP:
            with contextlib.suppress(OSError):
                os.remove(path)
            gone.append(name)
    kbs = {peek().get("kb"), peek().get("kb_building")}
    for name in os.listdir(STATE):  # the copy of HANDOFF.md a knowledge base loaded: while it is the one planners fork
        m = re.fullmatch(r"(kb-\d+)-handoff\.md", name)
        if m and m.group(1) not in kbs:
            with contextlib.suppress(OSError):
                os.remove(os.path.join(STATE, name))
            gone.append(name)
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


SLOW_PART = int(os.environ.get("ORCH_SLOW_PART", 120))  # a part of a pass or a dispatch that takes longer is named


def dispatch_once():
    st = peek()
    if not st["active"] or os.path.exists(os.path.join(STATE, "stopped")):
        return
    for part in (reconcile_stages, tree_care, check_isolation, parking_care, fix_deadlock, efficiency_care, kb_care,
                 role_layer_care, grant_pending, produce, support,
                 quick_fix, tidied,
                 consult, returned_tasks, held_graph, standstill, plan):  # before plan: what they say reaches it now
        began = time.time()
        try:  # one part that fails does not hold up the others; it is logged, and tried again at the next dispatch
            part()
        except Exception as e:  # noqa: BLE001
            log(f"dispatch: {part.__name__} failed: {e!r}")
        if time.time() - began > SLOW_PART:  # the watchdog's pass waits for it (watchdog.contained says the same)
            log(f"the dispatch's {part.__name__} took {time.time() - began:.0f} s")


def dispatch(pre=None, wait=False):
    """Run the dispatch, one at a time: a dispatch asked for while one runs makes that one run again. The watchdog runs
    its care of the sessions (pre) under the same lock and waits for it (wait), so that the two never act on one
    session at once.

    It runs only where sessions can be started (control()); asked for anywhere else, it is asked of the supervisor.
    What was asked of the supervisor is done first, before the care and the dispatch act on the sessions it names."""
    if not control():
        want(key="dispatch", run=["v2.py", "dispatch"])
        return
    again = os.path.join(STATE, "dispatch.again")
    os.makedirs(STATE, exist_ok=True)
    while True:
        with open(os.path.join(STATE, "dispatch.lock"), "w") as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | (0 if wait else fcntl.LOCK_NB))
            except BlockingIOError:
                open(again, "w").close()
                return
            carry_out_wanted()
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
    tests). Without control() it is asked of the supervisor: started from a session it would run in that session's
    sandbox, where a dispatch cannot start a session and a final check or commit cannot write the main checkout."""
    if not control():
        want(key="dispatch" if (script, args) == ("v2.py", ("dispatch",)) else None, run=[script, *args])
        return
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
    st["tasks"][tid]["back"] = text[:1200]  # what its session is told if it is resumed on it again (reusable)
    aside = leave(tid, "back to the planner")
    if aside:
        st.setdefault("withdrawn", []).append(tid)
    event(st, sender, text + aside)


def checked(tid, ok, tail="", ran=True):
    """The finalizer's check of a task has ended. A check that never ran (a command that is not runnable as written)
    is not a failed check: it costs the task no round, and the session is told to correct the command it handed over
    (2026-09-20: a quick fix reused an output directory the tool refuses, and two one-second failures sent a task
    whose check had passed to the planner)."""
    commit_now = False
    with state() as st:
        t = st["tasks"].setdefault(tid, {})
        if t.get("stage") != "checking":  # the watchdog gave the task to the planner meanwhile
            event(st, "the finalizer", f"The check of task {tid} ended after the task had left its check "
                  f"({t.get('stage')}): it {'passed' if ok else 'failed'}; .build/tasks/{tid}/finalize.log.")
            ok = None
        elif ok and t.get("accepted_early"):  # C9: its review accepted it while it was checked — it is committed
            t.pop("accepted_early", None)
            t["stage"], commit_now = "committing", True
        elif ok and t.get("rejected_early") is not None:  # C9: rejected while it was checked — its fix round now
            t["rejections"] = t.get("rejections", 0) + 1
            t.update(stage="fixing", fixing=None, fix_text=t.pop("rejected_early"))
        elif ok:
            t["stage"] = "reviewing"
            if not (review_beside_check() and t.get("reviewing")):  # a review begun beside the check goes on
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
            early = t.pop("rejected_early", None)  # C9: what its review found meanwhile goes into the same fix
            if t.pop("accepted_early", None):  # C9: an accept of work that failed its check is void: the fix is reviewed
                for x in held_reviews(t):
                    st["tasks"].setdefault(x, {}).update(verdict=None, round=None, voided="its check failed after the accept")
            if t["checks_failed"] == 1:
                t.update(stage="fixing", fixing=None, fix_text=f"The finalizer's check of task {tid} failed. The end of "
                         f"its log (.build/tasks/{tid}/finalize.log):\n{tail}"
                         + (f"\n\nAnd its review, made beside the check, rejected it:\n{early}" if early else ""))
                if early:
                    t["rejections"] = t.get("rejections", 0) + 1
            else:
                to_planner(st, tid, "the finalizer", f"Task {tid} failed its check again after a quick fix; it is yours "
                           f"to re-plan. The end of .build/tasks/{tid}/finalize.log:\n{tail}")
    if commit_now:
        background("finalize.py", "commit", tid)  # its end dispatches
        return
    kick()


def first_sentence(text, most=240):
    """A review's summary as the planner is told it at the commit: its first sentence. Whole, it was half of the 141K
    characters of commit events the planners were given in sixteen hours of 2026-09-22 — what the review found, for an
    accepted task, which its review file holds; the follow-ups, which the planner places, are given whole."""
    text = " ".join((text or "").split())
    m = re.match(r"(.{20,}?[.;:])(?:\s|$)", text)
    cut = m.group(1) if m else text
    return cut if len(cut) <= most else cut[:most].rsplit(" ", 1)[0] + " …"


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
        for x in [tid, *held_reviews(peek()["tasks"].get(tid) or {})]:
            update_task(x, status="completed")
        for name in sessions:
            if name and (peek()["sessions"].get(name) or {}).get("role") != "designer":
                release(name)
    kick()


def landed_together(tids, commit, how):
    """Tasks landed together as one landing train (train.py): each done, completed and its sessions released as a
    commit does (committed), and the planner told once."""
    with state() as st:
        said = []
        for tid in tids:
            t = st["tasks"].setdefault(tid, {})
            if t.get("stage") != "committing":
                said.append(f"(task {tid} had left its commit: {t.get('stage')})")
            t["stage"] = "done"
            summary = t.get("summary", "")
            said.append(f"Task {tid}: {summary}" if summary else f"Task {tid}.")
        event(st, "the finalizer", f"Tasks {', '.join(tids[:-1])} and {tids[-1]} landed together as {commit} ({how}). "
              + " ".join(said))
        sessions = [n for tid in tids for n in [(st["tasks"][tid]).get("session")]
                    + [x for x, s in st["sessions"].items() if s.get("reviews") == tid]]
    for tid in tids:
        for x in [tid, *held_reviews(peek()["tasks"].get(tid) or {})]:
            update_task(x, status="completed")
    for name in sessions:
        if name and (peek()["sessions"].get(name) or {}).get("role") != "designer":
            release(name)
    kick()


# What lands in main is checked as it will stand there. A task in its own tree was checked on its branch, made from
# HEAD as it was then; tasks land meanwhile, and two branches that merge cleanly as lines can still not stand
# together as theories. So its landing brings main into its branch and, when that brought anything, runs the
# repository's check of the two together in its tree before main moves. `{output}` is a fresh directory each time:
# the check refuses one that exists.
LANDING_CHECK = os.environ.get("ORCH_LANDING_CHECK", "python3 -B tools/incremental_check.py check --output {output}")
LANDING = "landing.lock"


@contextlib.contextmanager
def landing(deadline, shared=False):
    """Main moves by one landing at a time: the re-check of a task's work with what landed before it must still be
    true when it lands, so no other landing, and no commit of a task in the one tree, moves main in between. A check
    of a task in the one tree takes it `shared`: it reads main's working files, which a landing merges into, so
    main does not move under it — while such checks run beside each other. Yields whether it was taken before
    `deadline`."""
    with open(os.path.join(STATE, LANDING), "a") as f:
        taken = False
        while not taken:
            try:
                fcntl.flock(f, (fcntl.LOCK_SH if shared else fcntl.LOCK_EX) | fcntl.LOCK_NB)
                taken = True
            except BlockingIOError:
                if time.time() > deadline:
                    break
                time.sleep(PAUSE or 0.1)
        try:
            yield taken
        finally:
            if taken:
                fcntl.flock(f, fcntl.LOCK_UN)


def landing_failed(tid, tail):
    """A task accepted in its own tree does not stand with what landed since its check: the repository's check of the
    two together failed. Its tree now holds both, so the fix is made where it will be checked again; a second failure
    goes to the planner, as a second failed check does."""
    with state() as st:
        t = st["tasks"].setdefault(tid, {})
        if t.get("stage") != "committing":
            event(st, "the finalizer", f"The landing check of task {tid} failed after the task had left its commit "
                  f"({t.get('stage')}); .build/tasks/{tid}/landing.log.")
        else:
            t["checks_failed"] = t.get("checks_failed", 0) + 1
            text = (f"Task {tid} was accepted, but its work does not stand with what landed in main since its check: "
                    "what landed is now merged into your branch, so your tree holds both, and the repository's check "
                    f"of the two together failed. The end of its log (.build/tasks/{tid}/landing.log):\n{tail}")
            if t["checks_failed"] == 1:
                t.update(stage="fixing", fixing=None, fix_text=text)
            else:
                to_planner(st, tid, "the finalizer", text + "\n\nIt has failed a check before: it is yours to re-plan.")
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


def source_bound():
    """What each source of a read shows at most: READ_BYTES, or what the call declared — `SHOW=20K v2.py read …`, the
    shell's own assignment, reaches this process as its environment (work_meter.shown_bound reads the same for any
    other call) — within the batch's BATCH_BYTES."""
    m = re.fullmatch(r"(\d+)([kK]?)", os.environ.get("SHOW", "").strip())
    if not m:
        return READ_BYTES
    return max(READ_BYTES, min(int(m.group(1)) * (1000 if m.group(2) else 1), BATCH_BYTES))


def cmd_read(sources):
    """A read of any source, as one call: a file by its lines (`path`, `path:A-B`), a fact or definition by name, the
    session's task's `diff`, `result` and `log` (by their lines too: `diff:A-B`), a task's brief as the graph holds it
    (`task:ID`, `task:ID:A-B`), and a brief's proposal (`proposal:ID` for what placing it needs, `proposal:ID:KEY` for
    one of its briefs, with `:A-B` for its lines). It is a read like any other and bounded as one: each source at most
    READ_BYTES (a brief named whole, whole: whole_brief), the call at most BATCH_BYTES, the sources in order, and those
    there was no room for named. What of a file is in the session's context already is left out and said, and what it
    printed is exactly what it records as read.

    The call was bounded at READ_BYTES whole until 2026-09-21: `read A B C` showed the first source and named the rest
    "no room", while `read A -- B -- C`, three reads, showed each — so a session that named several sources, as the
    protocol invites, was cut, and learnt `--` a request or two later (fix-49.3: five reading requests in 30 s). What
    READ_BYTES is for, a large chunk read deliberately and in pieces, is a bound on each source; the call's own bound
    only made more calls of the same request. `--` groups of a read are now one call (main).

    It was the gather (`step ID N SOURCE...`) until 2026-09-21: the only way to read these sources, allowed once
    a step had produced, never refused by the reading limits and bounded as a whole batch. The owner found it
    redundant, and it was: a production restarts the reading limits, so the first read after one is always allowed,
    and a batch of reads is already one read. Its sources are every read's now."""
    import work_meter
    c = caller()
    tid = c and (c.get("reviews") or c.get("task"))  # a reviewer reads the task it reviews
    wst = work_meter.load(c["sid"]) if c else {"reads": {}}
    statements = statements_only(c or {})
    out, shown, size, unshown = [], [], 0, []
    for src in sources:
        seen = []
        text = read_source(src, tid, statements, seen, wst, work_meter.own_dirs(c or {})).rstrip()
        # a file's lines are bounded where they are read (file_read), and cut again they would be recorded unshown
        whole = whole_brief(src) or src == "diff"  # the diff is a review's substance, read whole where it fits
        part = f"== {src}\n{text if seen else one_read(text, BATCH_BYTES if whole else source_bound())}\n"
        n = len(part.encode())
        if unshown or (out and size + n > BATCH_BYTES):
            unshown.append(src)  # each source bounded, the first shown in any case; the rest whole or not at all
            continue
        out.append(part)
        size += n
        shown += seen
        for path, a, b in seen:  # in context now: a later source of the same read leaves it out too
            work_meter.saw(wst, path, a, b)
    body = "".join(out)
    if unshown:
        body += (f"[this read stops here: a read shows at most {BATCH_BYTES:,} bytes, each source at most "
                 f"{source_bound():,}, and there was no room for {' '.join(unshown)} — read them in a further read]\n")
    if c and shown:
        with work_meter.meter(c["sid"]) as m:  # under its lock: the session's own hooks write it too
            for path, a, b in shown:
                work_meter.saw(m, path, a, b)
    return body.rstrip("\n")


def whole_brief(src):
    """Whether a source is a brief named whole (`task:ID`, `proposal:ID:KEY`), which a read shows whole. READ_BYTES is
    there so that a large chunk is read deliberately, in pieces, rather than taken whole by accident; a brief is one
    unit named on purpose, bounded by its form, and what the planner decides on stands at its end (`Planner's:`,
    `Size:`). On 2026-09-21 the planner took stock of the graph with 9 of its 13 briefs cut at 5,000 bytes (they
    were 5.3-8.4K) and spent three further requests reading their ends."""
    return bool(re.fullmatch(r"task:[^:]+|proposal:[^:]+:[^:]+", src)) and not re.search(r":\d+-\d+$", src)


def one_read(text, limit=READ_BYTES):
    """A source other than a file's lines shows at most READ_BYTES (the owner, 2026-09-21), a brief named whole at most
    BATCH_BYTES: the rest is said, with how to take it — a narrower range of the same source."""
    data = text.encode()
    if len(data) <= limit:
        return text
    head = data[:limit]
    head = head[:head.rfind(b"\n") + 1] if head.rfind(b"\n") >= limit // 2 else head
    lines = head.count(b"\n") + (0 if head.endswith(b"\n") else 1)
    return (head.decode(errors="ignore").rstrip() + f"\n[this source stops here: it showed {len(head):,} of "
            f"{len(data):,} bytes, {lines} lines. A read shows at most {limit:,}: name the rest by its lines "
            "(`path:A-B`, `diff:A-B`, `result:A-B`, `log:A-B`, `task:ID:A-B`, `proposal:ID:KEY:A-B`) in a later "
            "read]")


def file_read(path, rel, lines, a, b, st, shown):
    """Lines a..b of a file as a read of it shows them: what is in the session's context (its meter, st) left out
    and said, and of the rest, numbered, at most READ_BYTES; what is printed is added to `shown`."""
    import work_meter
    known, at = work_meter.in_context(st, path)
    missing = work_meter.gaps(known, a, b)
    left = work_meter.gaps(missing, a, b)
    notes = [work_meter.left_out(rel, left, at)] if left else []
    printed, used, stop = [], 0, None
    for x, y in missing:
        for i in range(x, y + 1):
            line = f"{i:6}\t{lines[i - 1]}"
            used += len(line.encode()) + 1
            if used > source_bound():
                stop = i
                break
            printed.append(line)
            if shown and shown[-1][0] == path and shown[-1][2] == i - 1:
                shown[-1] = (path, shown[-1][1], i)
            else:
                shown.append((path, i, i))
        if stop:
            break
    if stop:
        rest = work_meter.spans(work_meter.gaps([[p, q] for _, p, q in shown] + left, stop, b))
        how = (f"line {stop} alone is more than a read shows: take it in pieces (`sed -n '{stop}p' {rel} | cut -c "
               f"1-{READ_BYTES}`, and on)" if len(f"{stop:6}\t{lines[stop - 1]}".encode()) + 1 > READ_BYTES else
               f"name the rest by its lines (`{rel}:{stop}-{b}`)")
        notes.append(f"[this source stops here, at line {stop}: this read shows at most {source_bound():,} bytes a source "
                     f"(`SHOW=20K` before the call for more, up to {BATCH_BYTES // 1000}K), and lines {rest} of {rel} "
                     f"were not shown — {how} in a later read]")
    return "\n".join(printed + notes)


def lines_of_text(text, a, b):
    """Lines a..b of a text, numbered as a file's are."""
    lines = text.splitlines()
    return "\n".join(f"{i:6}\t{lines[i - 1]}" for i in range(a, min(b, len(lines)) + 1))


ANSWER_BYTES = 4_000  # of each question a result names, and of its answer


def beside_the_result(tid, text):
    """What a result's reader needs beside it and looked for by hand: the commit message its final job hands the
    finalizer — 55 of the day's 106 reviewers read it themselves (96 calls), from wherever its brief had put it
    (review-202 looked in .build/tasks/edited-reach/, its brief's key, before .build/tasks/191/) — and each question the
    result names, with its answer (review-202 dug q63's out of the harness's state in two requests; 2026-09-22)."""
    out = []
    try:
        message = json.load(open(os.path.join(BUILD, tid, "finalize.json"))).get("message")
    except (OSError, ValueError, AttributeError):
        message = None
    if message and os.path.isfile(os.path.join(PROJECT, message)):
        out.append(f"== its commit message ({message})\n" + open(os.path.join(PROJECT, message), errors="ignore").read().strip())
    asks = peek().get("asks") or {}
    for q in dict.fromkeys(re.findall(r"\bq\d+\b", text)):
        ask = asks.get(q) or {}
        if ask.get("text"):
            out.append(f"== {q}, from {ask.get('from')} to {ask.get('to')}: {ask['text'][:ANSWER_BYTES]}\n"
                       + (f"answered: {str(ask['answer'])[:ANSWER_BYTES]}" if ask.get("answer") else "(not answered)"))
    return "".join("\n\n" + x for x in out) + ("\n" if out else "")


def read_source(src, tid, statements, shown, st, own=()):
    """One source of a read: a file or a range of it, the task's diff, result or check log, or a named fact — each
    read in the tree task tid's work stands in, its own while it has one: a reviewer of work in a tree, or its
    producer, would otherwise be shown the one tree, where the work is not until it is committed."""
    import work_meter
    d, tree = (os.path.join(BUILD, tid), worktree_of(tid)) if tid else (None, PROJECT)
    # the graph's own texts, so that they are read as any source is rather than by a command each:
    # a task's brief as the list holds it, and a proposal — what placing it needs, or one of its briefs
    # each by its lines too (`task:ID:A-B`, `proposal:ID:KEY:A-B`): a brief longer than a read is read in pieces
    lines = re.search(r":(\d+)-(\d+)$", src) if src.startswith(("task:", "proposal:")) else None
    ranged = (lambda text: lines_of_text(text, int(lines.group(1)), int(lines.group(2)))) if lines else (lambda t: t)
    name = src[:lines.start()] if lines else src
    if name.startswith("task:"):
        t = read_task(name[5:])
        return ranged(f"{t['id']} [{t.get('status')}] {t.get('subject', '')}\nafter: "
                      f"{', '.join(t.get('blockedBy') or []) or 'nothing'}\n\n{t.get('description', '')}"
                      if t else f"(no task {name[5:]} in the list)")
    if name.startswith("proposal:"):
        bid, _, key = name[len("proposal:"):].partition(":")
        return ranged(cmd_proposal(bid, [key] if key else []))
    ranged = re.fullmatch(r"(diff|result|log)(?::(\d+)-(\d+))?", src)
    if ranged:  # each may be read by its lines, so that one longer than a read is read in pieces rather than not at all
        what, a, b = ranged.group(1), ranged.group(2), ranged.group(3)
        if not tid:
            return f"(you work on no task, so there is no {what} of yours: a task's result is .build/tasks/ID/result.md)"
        if statements and what != "result":
            return "(refused: the statements of your task are your reading, not its diff or log)"
        if what == "result":
            p = os.path.join(d, "result.md")
            text = open(p).read() if os.path.exists(p) else "(no result yet)"
            if not a:
                text += beside_the_result(tid, text)
        elif what == "log":
            p = os.path.join(d, "finalize.log")
            text = open(p, errors="ignore").read() if os.path.exists(p) else "(no log)"
            if not a:  # its end, where a check says how it ended
                return "\n".join(text.splitlines()[-80:])
        else:
            try:
                files = json.load(open(os.path.join(d, "finalize.json")))["files"]
            except (OSError, ValueError, KeyError):
                files = []
            text = subprocess.run(["git", "-C", tree, "diff", "HEAD", "--", *files], capture_output=True,
                                  text=True).stdout + "".join(
                f"\n(new file) {f}\n" + open(os.path.join(tree, f), errors="ignore").read()
                for f in files if subprocess.run(["git", "-C", tree, "ls-files", "--error-unmatch", f],
                                                 capture_output=True).returncode)
        return lines_of_text(text, int(a), int(b)) if a else text
    if src.startswith("check:"):
        return check_text(src[len("check:"):])
    if src == "restated":
        return softly("the restatements", restated_text, tid, tree) if tid else \
            "(you work on no task, so there is no change of yours to read so)"
    if src == "tree":
        return softly("the task's tree", tree_state_text, tid, tree) if tid else \
            "(you work on no task, so there is no tree of yours to read)"
    if src == "probes":
        return probes_text(tid, tree) if tid else "(you work on no task, so there are no probes of yours)"
    if src == "reach" or src.startswith("reach:"):
        return reach_text(tree, src[len("reach:"):].replace(",", " ").split() if ":" in src else None, tid)
    m = re.fullmatch(r"(.+?)(?::(\d+)-(\d+))?", src)
    path = os.path.join(tree, m.group(1))
    if os.path.isfile(path):
        if statements and work_meter.body(path, tree, own):
            if path.endswith(".thy"):
                sys.path.insert(0, HERE)
                from digest import held_text
                return held_text(path, "statements")[0]
            return "(refused: code and logs are not your reading; the statements of theories are)"
        lines = open(path, errors="ignore").read().splitlines()
        a, b = (int(m.group(2)), int(m.group(3))) if m.group(2) else (1, len(lines))
        return file_read(os.path.normpath(path), m.group(1), lines, a, min(b, len(lines)), st, shown)
    args = ["--statement"] if statements else []
    text = subprocess.run([sys.executable, os.path.join(HERE, "show.py"), *args, m.group(1)], capture_output=True,
                          text=True, cwd=tree, env=dict(os.environ, ORCH_PROJECT=tree)).stdout
    # a fact longer than a read, read by its lines (`Theory.name:A-B`), as the cut of its first read says
    return lines_of_text(text, int(m.group(2)), int(m.group(3))) if m.group(2) else text


def check_place(name):
    """The output directory of a repository check the harness ran: by its stamp (a batch's, a train's, a base's), or by a
    task's number, its last check's (finalized.json's check_output). None when there is none."""
    if name.isdigit():
        o = {}
        with contextlib.suppress(OSError, ValueError):
            o = json.load(open(os.path.join(BUILD, name, "finalized.json")))
        out = o.get("check_output") or (o["reused"][:-4] if str(o.get("reused") or "").endswith(".log") else None)
        if out:
            return os.path.join(PROJECT, out) if not os.path.isabs(out) else out
        # before a task's outcome named its check: the newest batch or train whose stamp names the task
        named = [d for root in (os.path.join(BUILD, "batches"), os.path.join(BUILD, "trains"),
                                os.path.join(PROJECT, ".build", "bases"))
                 for d in glob.glob(os.path.join(root, "*"))
                 if os.path.isdir(d) and name in re.split(r"[-]", re.sub(r"^.*?(?:batch|train)", "", os.path.basename(d)))]
        return max(named, key=os.path.getmtime) if named else None
    for root in (os.path.join(BUILD, "batches"), os.path.join(BUILD, "trains"), os.path.join(PROJECT, ".build", "bases")):
        hits = sorted(glob.glob(os.path.join(root, f"*{name}*")))
        hits = [h for h in hits if os.path.isdir(h)]
        if hits:
            return hits[-1]
    return None


def check_text(name):
    """What a repository check the harness ran found, from its own report and log: its status and time, the theories it
    rebuilt, what failed with where, the recipes and host tests that failed, and where its log and report lie. Since
    checks are batched their reports lie under .build/tasks/batches/ (and the landing trains' under .build/bases/),
    not in the task's own directory, and design-218 spent five requests finding one its brief named by its stamp
    (2026-09-22 15:45)."""
    place = check_place(name)
    if not place:
        return (f"(no check named {name}: a batch's or train's stamp — as .build/tasks/batches/, .build/tasks/trains/ "
                "and .build/bases/ name them — or a task's number)")
    rel = os.path.relpath(place, PROJECT)
    lines = [f"report: {rel}/ (incremental.json, manifests.json, the proof's build.log, each recipe's log)"]
    log = place + ".log" if os.path.exists(place + ".log") else None
    if log:
        lines.append(f"log: {os.path.relpath(log, PROJECT)}")
    try:
        r = json.load(open(os.path.join(place, "incremental.json")))
    except (OSError, ValueError):
        return "\n".join(lines + ["(it left no incremental.json: it did not run through)"])
    count = lambda v: v if isinstance(v, int) else len(v or [])
    lines.append(f"status: {r.get('status')} in {round(r.get('seconds') or 0)} s — {r.get('theories', '?')} theories, "
                 f"{count(r.get('rebuilt_theories'))} rebuilt, {count(r.get('reused_theories'))} reused from "
                 f"{os.path.relpath(r['base'], PROJECT) if r.get('base', '').startswith(PROJECT) else r.get('base')}")
    if r.get("error"):
        lines.append(f"error: {r['error'][:600]}")
    failed = r.get("failed_recipes") or []
    if failed:
        lines.append(f"failed recipes ({len(failed)}): " + ", ".join(failed)
                     + f" — each one's log: {rel}/recipes/NAME.log, its report {rel}/recipes/NAME/")
    host = [f"{k} ({', '.join(v.get('failing') or []) or 'exit ' + str(v.get('exit_code'))})"
            for k, v in (r.get("host_tests") or {}).items() if v.get("exit_code")]
    if host:
        lines.append("failed host tests: " + "; ".join(host))
    build = os.path.join(place, "proof", "build.log")
    if os.path.exists(build):  # every error, one line each with where it stands, as check_errors.py lists them
        import check_errors
        errors = list(dict.fromkeys(check_errors.errors_in(open(build, errors="ignore").read())))
        if errors:
            lines.append(f"the proof's errors ({len(errors)}; each one's goal is in {os.path.relpath(build, PROJECT)}):")
            lines += ["- " + e for e in errors]
    return "\n".join(lines)


PROBE_MARKER = "PROBE THEORIES LOADED"  # tools/probe_theories.py: only this line certifies the proofs loaded


def timed(elapsed, d):
    """A probe's two times, each named: Isabelle's for loading the theories (its log's last `elapsed time`) and the run's
    whole (the probe tool's `seconds`: the process and the base heap's load too). One figure unnamed, 0.235 s, stood
    beside the 6.0 s task 188's commit message gave the run, and review-199 took them for a discrepancy (2026-09-22)."""
    try:
        run = json.load(open(os.path.join(d, "probe.summary.json"))).get("seconds")
    except (OSError, ValueError):
        run = None
    return "".join([f"; its theories loaded in {elapsed[-1]} s (Isabelle's elapsed time)" if elapsed else "",
                    f"; the run {run} s in all (the heap's load included)" if run is not None else ""])


# A task's probes are its reviewer's evidence (probes_text), and its session removed them before handing over — fix-245
# at 17:18:56 and implement-221 at 16:12, 2026-09-22, following a rule read as their own ("remove probes promptly"):
# review-246 found no probe.log under .build/tasks/245, as #234's had. The harness keeps a copy of each: every tool
# call of a task's session copies what a probe left under its task's directory that is newer than the copy kept.
PROBES_KEPT = os.path.join(STATE, "probes")
PROBE_FILES = ("probe.log", "probe.summary.json", "probe.ML")


def probe_dirs(tid):
    """The directories outside the task's own folder that its sessions' probes named (`--work`), as the guard recorded
    them when each probe was run (work_meter.probe_work): a probe run in a brief's named folder or under $TMPDIR left
    nothing where `v2.py read probes` looked, and two reviews of 2026-09-22 could not read back the completion marker a
    result claimed (tasks 233 and 245)."""
    try:
        return [d for d in json.load(open(os.path.join(PROBES_KEPT, str(tid), "dirs.json"))) if isinstance(d, str)]
    except (OSError, ValueError, TypeError):
        return []


def note_probe_dirs(tid, dirs):
    """Record the probe directories a task's session is about to run in, those outside the task's own folder."""
    root = os.path.realpath(os.path.join(BUILD, str(tid)))
    have = probe_dirs(tid)
    new = [d for d in dict.fromkeys(os.path.realpath(x) for x in dirs)  # a tree's `.build` is a link to the one
           if not (d + os.sep).startswith(root + os.sep) and d not in have]
    if not tid or not new:
        return
    os.makedirs(os.path.join(PROBES_KEPT, str(tid)), exist_ok=True)
    path = os.path.join(PROBES_KEPT, str(tid), "dirs.json")
    with open(path + ".tmp", "w") as f:
        json.dump(have + new, f)
    os.replace(path + ".tmp", path)


def keep_probes(tid):
    """Copy every probe the task's directory holds, and every one its probes ran elsewhere (probe_dirs) — its log,
    summary and script, and the theories it probed — to PROBES_KEPT/ID/, where no session writes, when it is newer
    than the copy kept there."""
    if not tid:
        return
    root = os.path.join(BUILD, str(tid))
    logs = glob.glob(os.path.join(root, "**", "probe.log"), recursive=True) + [
        os.path.join(d, "probe.log") for d in probe_dirs(tid) if os.path.isfile(os.path.join(d, "probe.log"))]
    for log in logs:
        d = os.path.dirname(log)
        name = os.path.relpath(d, root) if (d + os.sep).startswith(root + os.sep) else \
            "elsewhere" + os.sep + (os.path.relpath(d, PROJECT) if d.startswith(PROJECT + os.sep) else d.strip(os.sep))
        kept = os.path.join(PROBES_KEPT, str(tid), name.replace(os.sep, "__"))
        with contextlib.suppress(OSError):
            if os.path.exists(os.path.join(kept, "probe.log")) and \
                    os.path.getmtime(os.path.join(kept, "probe.log")) >= os.path.getmtime(log):
                continue
            os.makedirs(os.path.join(kept, "theories"), exist_ok=True)
            for f in PROBE_FILES:
                if os.path.isfile(os.path.join(d, f)):
                    shutil.copy2(os.path.join(d, f), os.path.join(kept, f))
            for thy in glob.glob(os.path.join(d, "theories", "*.thy")):
                shutil.copy2(thy, os.path.join(kept, "theories", os.path.basename(thy)))
            json.dump({"from": os.path.relpath(d, PROJECT) if d.startswith(PROJECT + os.sep) else d},
                      open(os.path.join(kept, "from.json"), "w"))


def probe_logs(tid):
    """The task's probe logs, newest first: those under its directory and those its probes ran elsewhere (probe_dirs),
    and the kept copy of each its session removed."""
    here = list(dict.fromkeys(glob.glob(os.path.join(BUILD, str(tid), "**", "probe.log"), recursive=True) + [
        os.path.join(d, "probe.log") for d in probe_dirs(tid) if os.path.isfile(os.path.join(d, "probe.log"))]))
    gone = []
    for log in glob.glob(os.path.join(PROBES_KEPT, str(tid), "*", "probe.log")):
        try:
            origin = json.load(open(os.path.join(os.path.dirname(log), "from.json")))["from"]
        except (OSError, ValueError, KeyError):
            continue
        if not os.path.isfile(os.path.join(PROJECT, origin, "probe.log")):
            gone.append(log)
    return sorted(here + gone, key=os.path.getmtime, reverse=True)


def probe_runs(tid, tree):
    """The task's probe runs, newest first (at most 12): for each its directory as it is to be named, when it ended,
    the theories it loaded, whether its completion marker is there, its error lines, its times, and for each theory
    whether the copy it probed is what the tree holds now — `same` maps a theory to the tree's theory it was (itself,
    or the one whose body a renamed copy has), or None."""
    body = lambda text: text.split("\nbegin", 1)[-1] if "\nbegin" in text else text  # past the header a probe rewrites
    memo, runs = {}, []

    def changed_bodies():  # the theories the task changes, by their body: what a renamed probe copy may be
        if not os.path.isdir(tree):
            return {}
        if "b" not in memo:
            base = (git_out("merge-base", "HEAD", "main", tree=tree) or "").strip() or "HEAD"
            paths = (git_out("diff", "--name-only", base, "--", "theories/", tree=tree) or "").split() + \
                (git_out("ls-files", "--others", "--exclude-standard", "--", "theories/", tree=tree) or "").split()
            memo["b"] = {os.path.basename(p)[:-4]: body(open(os.path.join(tree, p), errors="ignore").read())
                         for p in paths if p.endswith(".thy") and os.path.isfile(os.path.join(tree, p))}
        return memo["b"]
    for log in probe_logs(tid)[:12]:
        d = os.path.dirname(log)
        text = open(log, errors="ignore").read()
        try:
            loaded = re.findall(r'use_thy\w*\s+"([^"]+)"', open(os.path.join(d, "probe.ML"), errors="ignore").read())
        except OSError:
            loaded = []
        copies = {}  # a renamed copy's name → the tree's theory it stands for, as the probe tool says (from_tree)
        with contextlib.suppress(OSError, ValueError, AttributeError, TypeError):
            copies = {c: t for t, c in (json.load(open(os.path.join(d, "probe.summary.json"))).get("from_tree") or {}).items()}
        run = {"dir": d, "at": os.path.getmtime(log), "names": [os.path.basename(p) for p in loaded],
               "errors": [line.strip() for line in text.splitlines() if line.startswith("***")],
               "elapsed": re.findall(r"### ([\d.]+)s elapsed time", text), "complete": PROBE_MARKER in text,
               "same": {}, "said": []}
        for n in run["names"]:
            probed, held = os.path.join(d, "theories", n + ".thy"), os.path.join(tree, "theories", n + ".thy")
            if not os.path.isfile(probed):
                run["said"].append(f"{n} (no copy kept)")
                run["same"][n] = None
                continue
            mine = body(open(probed, errors="ignore").read())
            if os.path.isfile(held):
                equal = mine == body(open(held, errors="ignore").read())
                run["said"].append(f"{n} {'as the tree holds it now' if equal else 'DIFFERS from the tree now'}")
                run["same"][n] = n if equal else None
                continue
            if n in copies:  # the probe tool's own word for which theory the copy stands for (#229's review)
                of = os.path.join(tree, "theories", copies[n] + ".thy")
                equal = os.path.isfile(of) and mine == body(open(of, errors="ignore").read())
                run["said"].append(f"{n}: the tree's {copies[n]} " + ("as it stands" if equal else "as it stood, since changed"))
                run["same"][n] = copies[n] if equal else None
                continue
            # a copy under a name of its own (`P130_Readings`): the tree's theory whose body it is, if any
            twin = next((t for t, b in changed_bodies().items() if b == mine), None)
            run["said"].append(f"{n}: the tree's {twin} as it stands" if twin else f"{n}: no theory the task changed is it now")
            run["same"][n] = twin
        run["where"] = os.path.relpath(d, PROJECT)
        if d.startswith(PROBES_KEPT + os.sep):  # its session removed it: the harness's copy (keep_probes)
            with contextlib.suppress(OSError, ValueError, KeyError):
                run["where"] = json.load(open(os.path.join(d, "from.json")))["from"] + " (removed by its session; the harness's copy)"
        runs.append(run)
    return runs


def probes_text(tid, tree):
    """The task's probe runs (tools/probe_theories.py, each in a directory of its own under .build/tasks/ID/, newest
    first): the theories each loaded, whether its completion marker is there, its errors, its time, and whether each
    theory it probed is the one the tree holds now. A reviewer dug this out with `ls` and `tail` over the probe
    directories, about one request a review (47 in the 55 reviews of 2026-09-22)."""
    runs = probe_runs(tid, tree)
    if not runs:
        return "(no probe of this task: no probe.log under its .build/tasks directory, and none kept by the harness)"
    out = []
    for r in runs:
        state = ("complete: " + PROBE_MARKER if r["complete"] else
                 "NOT complete: no completion marker" + (" (it may still run)" if time.time() - r["at"] < 120 else ""))
        out.append(f"{r['where']} at {time.strftime('%H:%M', time.localtime(r['at']))}: "
                   f"{state}; {len(r['errors'])} error line(s){': ' + '; '.join(r['errors'][:3]) if r['errors'] else ''}"
                   + timed(r["elapsed"], r["dir"]) + "\n  "
                   + "; ".join(r["said"] or ["it loaded no theory: it proves nothing of the task's"]))
    if not os.path.isdir(tree):
        out.append("(the task's tree is gone — its work has landed or been dropped: nothing to compare with)")
    return "\n".join(out)


def probed_whole(tid, tree):
    """(the tree's theories a probe of the task loaded as the tree holds them, to its completion marker with no error
    line, in order; how many such runs): the harness's record of what its session verified by probing, which the
    harness states in the task's commit (finalize.harness_validation) rather than the session narrating it — five of
    the 31 rejections whose findings the state held on 2026-09-23 were a commit message misstating a run."""
    theories, runs = [], 0
    for r in probe_runs(tid, tree):
        if not r["complete"] or r["errors"]:
            continue
        held = [t for t in r["same"].values() if t]
        if held:
            runs += 1
            theories += [t for t in held if t not in theories]
    return theories, runs


RECIPE_EXPORT = re.compile(r"export\s*=\s*['\"]([\w.]+):")
RECIPE_NAME = re.compile(r"\bname\s*=\s*['\"]([^'\"]+)['\"]")


def reach_text(tree, names, tid=None):
    """Which recipes reach each theory, in `tree`'s own sources: a recipe (tools/reconstruct_*.py) reads the theory it
    exports and everything that theory imports, directly or not; a theory no recipe reaches is proved and read by none
    (its liveness is its proofs alone). No names: the theories the task changes. Briefs ask it of a task's result (five
    on 2026-09-22), and implement-130 spent three requests building it by hand — the recipes read, the source graph
    introspected, a script written and its output read back."""
    graph = {}
    for path in glob.glob(os.path.join(tree, "theories", "*.thy")):
        graph[os.path.basename(path)[:-4]] = [n.rsplit(".", 1)[-1]
                                               for n in theory_imports(open(path, errors="ignore").read())]
    recipes = {}
    for path in sorted(glob.glob(os.path.join(tree, "tools", "reconstruct_*.py"))):
        text = open(path, errors="ignore").read()
        export = RECIPE_EXPORT.search(text)
        if export:
            name = RECIPE_NAME.search(text)
            recipes[name.group(1) if name else os.path.basename(path)[12:-3]] = export.group(1)
    closure = {}
    for recipe, root in recipes.items():
        seen, todo = set(), [root]
        while todo:
            t = todo.pop()
            if t in seen or t not in graph:
                continue
            seen.add(t)
            todo += graph[t]
        closure[recipe] = seen
    if not os.path.isdir(tree):
        return "(the task's tree is gone — its work has landed or been dropped)"
    if names is None:  # the task's own: what its tree changes against main
        base = (git_out("merge-base", "HEAD", "main", tree=tree) or "").strip() or "HEAD"
        changed = (git_out("diff", "--name-only", base, "--", "theories/", tree=tree) or "").split()
        changed += (git_out("ls-files", "--others", "--exclude-standard", "--", "theories/", tree=tree) or "").split()
        names = sorted({os.path.basename(p)[:-4] for p in changed if p.endswith(".thy")})
        if not names:
            return "(the task's tree changes no theory against main)"
    out, unreached = [], []
    for n in names:
        if n not in graph:
            out.append(f"{n}: no such theory in " + (os.path.relpath(tree, PROJECT) if tree.startswith(PROJECT + os.sep)
                                                         else "the one tree" if tree == PROJECT else tree))
            continue
        by = sorted(r for r, s in closure.items() if n in s)
        if len(by) == len(recipes) and by:
            out.append(f"{n}: all {len(recipes)} recipes")
        elif len(by) > len(recipes) // 2:
            out.append(f"{n}: {len(by)} of {len(recipes)} recipes — all but " + ", ".join(sorted(set(recipes) - set(by))))
        elif by:
            out.append(f"{n}: {len(by)} of {len(recipes)} recipes — " + ", ".join(f"{r} (exports {recipes[r]})" for r in by))
        else:
            unreached.append(n)
            out.append(f"{n}: no recipe reaches it")
    if unreached:
        out.append(f"reached by no recipe ({len(unreached)}): {', '.join(unreached)}")
    return "\n".join(out)


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
        sender = (c or {}).get("name", "the owner")
        return (revise_proposal(tid, sender, text) or keep_told(tid, sender, text)
                or f"refused: no session works on task {tid}")
    for n in names:
        deliver(n, (c or {}).get("name", "the owner"), text)
    return "told " + ", ".join(names)


def keep_told(tid, sender, text):
    """What the planner tells a task no session works on now — queued again after its landing did not merge, between
    its fix rounds, not yet started — is kept for the session that next works on it (hand_told). It was refused: the
    planner told task 94 three times, "refused: no session works on task 94", and kept the answer in HANDOFF.md in
    case the next session asked (2026-09-22 09:48)."""
    if not in_list(tid):
        return None
    with state() as st:
        t = st["tasks"].setdefault(tid, {})  # a listed task not yet started has no record here until it starts
        if t.get("stage") == "done":
            return None
        t["told"] = (t.get("told") or []) + [{"from": sender, "text": text, "at": time.strftime("%Y-%m-%dT%H:%M:%S")}]
    log(f"told task {tid}, which no session works on now: kept for its next session")
    return f"kept: no session works on task {tid} now, and the one that next does is given it when it starts or is resumed"


def hand_told(name):
    """Give a session that has begun or resumed work on a task what was told the task while nobody worked on it
    (keep_told): mail, read at its next tool call."""
    with state() as st:
        s = st["sessions"].get(name) or {}
        t = st["tasks"].get(s.get("task") or "")
        told = (t or {}).pop("told", None) or []
    for m in told:
        post(name, m["from"], m["text"])


def revise_proposal(bid, sender, text):
    """A proposal waiting to be placed, sent back to its task designer with what to change: the watchdog holds the
    designer while its proposal waits, and support() resumes it with this when the supporting slot is free; it
    proposes again. None when the task is no brief waiting to be placed. On 2026-09-21 the planner told brief 13's
    designer what to change a minute after it proposed and found no session — released three seconds after its result
    — so it re-planned the brief, and a new task designer briefed it again whole (12 requests, 6.8M read from cache)."""
    with state() as st:
        t = st["tasks"].get(bid) or {}
        name = t.get("session")
        designer = st["sessions"].get(name or "") or {}
        if t.get("stage") != "proposed" or designer.get("role") != "task-designer":
            return None
        if designer.get("released") or designer.get("state") == "lost":
            return (f"refused: brief {bid}'s task designer, {name}, is no longer held, so nothing can take a correction "
                    f"of its proposal: place it as it is (`v2.py accept {bid}`), or re-plan the brief (`v2.py drop "
                    f"{bid}`, then rewrite it) and point the new task designer at {t.get('proposal')} to revise.")
        before = t.get("revise") or {}
        t["revise"] = {"from": sender, "at": time.time(),
                       "text": (before["text"] + "\n\n" + text) if before.get("text") else text}
    log(f"the proposal of brief {bid} goes back to {name} with {sender}'s correction")
    kick()
    return (f"sent back to its task designer, {name}: it is resumed with what you said when the supporting slot is "
            f"free, revises its proposal and proposes again, and you are told as before. Until then brief {bid} has "
            "nothing to place.")


def revise_now(bid):
    """Resume a brief's task designer with the planner's correction of its proposal (revise_proposal); when it cannot
    be resumed — its cache went cold, it is gone — the brief goes to the planner, with the correction it had asked."""
    with state() as w:
        t = w["tasks"][bid]
        asked, name, proposal = t.pop("revise"), t.get("session"), t.get("proposal")
    text = (f"Message from {asked['from']}, before your proposal is placed:\n{asked['text']}\n\nNone of your tasks is "
            f"in the graph yet. Revise the proposal ({proposal}) as it says, propose again (`v2.py propose {bid} FILE`), "
            f"record your result again (`v2.py result {bid}`) with what changed and why, and end your turn.")
    if name and resume(name, text):
        with state() as w:
            w["tasks"][bid]["stage"] = "running"
        log(f"{name} resumed to revise the proposal of brief {bid}")
        return name
    with state() as w:
        to_planner(w, bid, "the harness", f"Brief task {bid}'s task designer, {name}, could not be resumed with your "
                   f"correction of its proposal (its cache went cold, or it is gone). Place the proposal as it is "
                   f"(`v2.py accept {bid}` works on it once it is proposed again), or re-plan the brief and point the "
                   f"new task designer at {proposal} to revise. You had asked:\n{asked['text']}")
    log(f"brief {bid}'s task designer could not be resumed to revise its proposal; the brief is the planner's")
    return None


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
        turn_over(c)
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
    if not control():
        # inside Claude Code's sandbox no other run is visible: counted there, the machine is always quiet
        want(measure=c["name"], text=text)
        return ("asked of the supervisor, which sees every run on this machine (this command, in the sandbox, sees "
                "none): its answer comes to you as a message within seconds. Launch the measurement only once it says "
                "the machine is yours; continue meanwhile with what is not a measurement.")
    return measure_claim(c, text)


def measure_claim(c, text):
    """The claim for a producing session's measurement, decided where every run on the machine can be seen: what the
    session is told."""
    holder = exclusive_claim()
    if holder and holder["task"] != c["task"]:
        return (f"refused: task {holder['task']} holds the machine ({holder['why']}). Measure when it has let go; "
                "meanwhile write, or run what is not a measurement.")
    pending = pending_claim()
    if pending and pending["task"] != c["task"]:
        return (f"refused: task {pending['task']} waits to measure first ({pending['why']}); claim the machine again "
                "when it has measured. Meanwhile write, or run what is not a measurement.")
    runs = isabelle_runs()
    why = text.strip() or "a measurement of its own work"
    if runs and not holder:
        json.dump(dict(task=c["task"], why=why, session=c["name"], at=(pending or {}).get("at") or time.time()),
                  open(os.path.join(STATE, PENDING), "w"))
        log(f"task {c['task']} waits for the machine to empty, for a measurement: {runs} run(s) going")
        return (f"queued: {runs} Isabelle run(s) are going, and a timing taken beside them is not the timing of your "
                "work. No new run of another task starts meanwhile, and once these have ended the machine is yours: "
                "you are told by message, or resumed with it if you have parked for the machine (`v2.py park "
                "machine`), which is what to do when nothing else is left — `v2.py end` does not end a producing "
                "session's turn. Continue meanwhile with what needs no machine. Do not claim it again.")
    with contextlib.suppress(OSError):
        os.remove(os.path.join(STATE, PENDING))
    claim_exclusive(c["task"], why, session=c["name"])
    log(f"task {c['task']} holds the machine for a measurement: {text.strip() or '-'}")
    return (f"the machine is yours while your run goes: launch it within {int(CLAIM_GRACE) // 60} minutes. No other "
            "check or measurement starts meanwhile, and the hold ends with your run — record the numbers it gives "
            "before you park or produce.")


def machine_wait(s):
    """The kind of run a supporting session waits on the machine for — its last check refused while the machine was
    full, and none let through since — or None. It holds no producing slot to free, so it does not park: it ends its
    turn (ctx_gauge.may_end) and the watchdog resumes it when a run may start (watchdog.care). A reviewer refused a
    probe was told to park, which is refused to it, and could neither end its turn nor wait (2026-09-21)."""
    if s.get("role") in PRODUCING or not s.get("sid"):
        return None
    import work_meter
    return work_meter.load(s["sid"]).get("run_refused")


def turn_over(c):
    """The call being made ends its session's turn: what it recorded (a result, a verdict, a plan, an answer) or its
    park ends the session's piece of work for now, and the harness has told it to end its turn. The session's
    PostToolUse hook then ends the turn at once (ctx_gauge.turn_ended): the request that would only have said so —
    "Parked while the check runs.", "I rejected task 72; the verdict is recorded" — reads the whole context again,
    about 65K input-equivalent tokens each; 172 such requests in nine hours of 2026-09-22 were 11.1M of 168.7M (the
    owner: the cost balloons). A resume takes the mark away, so it never ends a turn other than the one it was made in."""
    if c and c.get("sid"):
        os.makedirs(os.path.join(STATE, "flags"), exist_ok=True)
        with open(os.path.join(STATE, "flags", f"{c['sid']}.ended"), "w") as f:
            f.write(str(time.time()))


def cmd_end():
    """A turn that no command of the harness ends — the planner's between its events, a reviewer's that waits for its
    own run or its question — ends with its last call rather than with a closing message: that message was a request
    reading the whole context again for nobody (the owner, 2026-09-22: "yes do the planner closing summary removal …
    shouldn't this be done for everyone"). It ends only where the Stop hook would let it (ctx_gauge.may_end); the
    knowledge base's reply is read, and a session the owner speaks to answers the owner, so theirs end with words."""
    c = caller()
    if not c:
        return "refused: `v2.py end` ends a session's turn"
    if c["role"] == "kb" or c.get("owner"):
        return "refused: your turn ends with your reply, which is read"
    import ctx_gauge
    if not ctx_gauge.may_end(c["role"], c):
        return ("refused: your turn does not end here: " + (
            "you hold the producing slot, and it ends with your result recorded or a park" if c["role"] in PRODUCING
            else f"it ends when your piece of work has ended ({ctx_gauge.end_of(c['role'], c)}), or while you wait for "
                 "a question or a run of your own"))
    turn_over(c)
    return "ended"


def snapshot(tid, tree):
    """A commit of a task's tree as its check would see it — its tracked and untracked files, what .gitignore leaves out
    left out, the receipts as its HEAD has them (a retain of its own is no work of the task's, and only a retention
    commits them) but for those its brief delivers — on no branch: (commit, None), or (None, why). What a check batch
    merges (train.Batch). A brief that changes a recipe's words names the report files it re-records, and they are its
    work: taken as HEAD had them, fix-267's check compared its new words with the old ones and could never pass (q65,
    2026-09-22 20:04)."""
    index = os.path.join(STATE, f"snapshot-{tid}.index")
    env = dict(os.environ, GIT_INDEX_FILE=index)
    run = lambda *a: subprocess.run(["git", "-C", tree, *a], capture_output=True, text=True, env=env, timeout=300)
    try:
        for args in (("read-tree", "HEAD"),
                     ("add", "-A", "--ignore-errors", "--", ".", *[f":(exclude){p}" for p in RECEIPTS])):
            r = run(*args)
            refused = not_added(r.stderr) if args[0] == "add" else [r.stderr.strip() or "failed"]
            if r.returncode and refused:
                return None, f"git {args[0]} in its tree: {'; '.join(refused)[-300:]}"
        own = [p for p in delivered_receipts(tid) if os.path.exists(os.path.join(tree, p))]
        if own:
            r = run("add", "-A", "--", *own)
            if r.returncode:
                return None, f"git add of the receipts its brief delivers: {r.stderr.strip()[-300:]}"
        work = run("write-tree").stdout.strip()
        c = subprocess.run(["git", "-C", tree, "commit-tree", work, "-p", "HEAD", "-m",
                            f"The work of task {tid} as its check sees it"], capture_output=True, text=True, timeout=60)
        if c.returncode or not c.stdout.strip():
            return None, f"git commit-tree in its tree: {(c.stdout + c.stderr).strip()[-200:]}"
        return c.stdout.strip(), None
    except (OSError, subprocess.TimeoutExpired) as e:
        return None, f"its tree could not be read: {e!r}"
    finally:
        with contextlib.suppress(OSError):
            os.remove(index)


def not_added(said):
    """What `git add --ignore-errors` could not add that is work: a file the sandbox mounts over the tree (.bash_profile,
    .bashrc: /dev/null, a character device) is no work of the task's, and git refuses it as no regular file — every
    session's `v2.py check` was refused for it (implement-185, 2026-09-22 14:47)."""
    errors = [line for line in said.splitlines() if line.startswith(("error:", "fatal:"))]
    work = [line for line in errors if "can only add regular files" not in line and line != "fatal: adding files failed"]
    if errors and not work:
        return []  # only what the sandbox mounts (git's own summary line beside it says nothing more)
    return work or ([said.strip()] if said.strip() and not errors else errors)


def cmd_check():
    """A producing session's request for the repository's check of its task's work (notes/plan-landing-train.md 1b):
    its tree as it stands, merged with main and the work of every other task waiting for a check, checked once for all
    (train.Batch). The session parks — the producing slot is free meanwhile — and is resumed with the result: what
    failed that is its own, or that it passed. The same tree handed over later is not checked again."""
    c = caller()
    if not c or c["role"] not in PRODUCING or not c.get("task"):
        return "refused: a producing session asks for the check of its task"
    tid = c["task"]
    if not apart(tid):
        return ("refused: your task works in the one tree, where the repository's check reads what every task there "
                "has installed: run it yourself as before (in the background, and `v2.py park run` for it)")
    jobs = running_jobs(c["name"])
    if jobs:
        return f"refused: your runs {', '.join(jobs)} are going on: park for them first, or stop them (TaskStop)"
    import train
    work, why = snapshot(tid, worktree_of(tid))
    if not work:
        return f"refused: {why}"
    tree = git_out("rev-parse", f"{work}^{{tree}}", tree=worktree_of(tid)).strip()
    done = train.passed_tree(tree)
    if done:
        return (f"this very tree passed the repository's check at {time.strftime('%H:%M', time.localtime(done['at']))} "
                f"(its log: {os.path.relpath(done['log'], PROJECT) if done.get('log') else 'gone'}): nothing is run "
                "again. Continue; hand it over as it stands, and it is not checked again then either.")
    train.CHECK_QUEUE.put(tid, head=work, tree=tree, kind="session", asked=c["name"], documents=False)
    with state() as w:
        w["tasks"].setdefault(tid, {}).update(stage="parked", parked={
            "since": time.time(), "for": "check", "why": "", "after": None, "holds_tree": False, "questions": [],
            "holder": None, "run": None})
        w["sessions"][c["name"]]["state"] = "parked"
    log(f"task {tid}'s session asks for the repository's check of its work; it waits for the next batch")
    background("finalize.py", "check-batch")
    kick()
    turn_over(c)
    return ("queued: the repository's check of your tree's work as it stands now, with main and the work of every other "
            "task waiting for one — once for all. End your turn now: you are parked, the producing slot free "
            "meanwhile, and resumed here with its result (what failed that is yours, or that it passed).")


def check_came(tid, ok, text):
    """A batch's result for a task whose session is parked for its check (cmd_check): its resume carries it."""
    with state() as w:
        t = w["tasks"].get(tid) or {}
        p = t.get("parked") or {}
        if t.get("stage") == "parked" and p.get("for") == "check":
            p.update(result=text, passed=ok)
    log(f"the check task {tid}'s session asked for: {'passed' if ok else 'failed'}")
    kick()


def cmd_park(kind, text=""):
    """A producing session with nothing productive left must wait: it parks, and the producing slot is free for another
    worker (the owner, 2026-09-19). It waits for its own run (which keeps the working tree while it reads the task's
    changes), a fix, the working tree, or the answer to its question; it is resumed, its context intact, when that has
    come and the slot and the working tree are free, before any new task starts."""
    c = caller()
    if c and c["role"] not in PRODUCING and kind == "machine":
        if not machine_wait(c):
            return "refused: no run of yours was refused for the machine: run your check"
        turn_over(c)
        return ("you do not park — you hold no producing slot to free: end your turn, and you are resumed here, your "
                "context intact, when a run may start")
    if not c or c["role"] not in PRODUCING:
        return "refused: a producing session parks its task"
    if kind not in ("run", "fix", "tree", "answer", "machine"):
        return "refused: v2.py park run|fix|tree|answer|machine"
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
    run = None
    if kind == "machine":  # the kind of run the guard last refused it, the heavier when none is recorded
        import work_meter
        run = work_meter.load(c["sid"]).get("run_refused") or "heavy"
        queued = pending_claim()
        if queued and queued["task"] == tid:
            run = "measure"  # it waits for the machine to empty (parked_ready), not for a slot
        elif control() and not run_blocked((tid, c.get("reviews")), run):
            return "a run may start now: run it and continue"  # judged only where the machine's runs can be seen
    questions = [q for q, a in st["asks"].items() if a["from"] == c["name"] and a["state"] != "answered"]
    if kind == "answer" and not questions:
        return "refused: no question of yours is open"
    after = (st["tasks"].get(tid) or {}).get("efficiency_fix") if kind == "fix" else None
    aside = "" if kind == "run" else leave(tid, "parked")  # a run reads the task's changes: they stay while it runs
    with state() as w:
        w["tasks"].setdefault(tid, {}).update(stage="parked", parked={
            "since": time.time(), "for": kind, "why": text, "after": after, "holds_tree": kind == "run",
            "questions": questions, "holder": holder, "run": run})
        w["sessions"][c["name"]]["state"] = "parked"
        if kind == "fix" and not after:
            event(w, c["name"], f"Task {tid} is parked for the fix of its performance problem: tell the harness which task "
                  f"fixes it (`v2.py after {tid} FIXTASK`, or `v2.py after {tid} none` to let it continue as it is).")
    kick()
    turn_over(c)
    what = {"run": "your run has ended", "fix": "the fix has landed", "tree": f"task {holder} has let the working tree go",
            "answer": "the answer has come", "machine": "a run may start on the machine"}[kind]
    return (f"parked: end your turn now; the producing slot is free for another worker meanwhile. You are resumed "
            f"here, your context intact, when {what} and the slot is free; if not within "
            f"{hold_of({'parked': {'for': kind}}) // 3600} hours, "
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


def one_tree_paths(text, mine=None):
    """The paths a text names by the repository's absolute path, outside `.build/` and outside the tree `mine`: the
    one tree's own directory, or a task's tree. `.build/` is the one `.build` everywhere and may be named so."""
    out = []
    for m in re.finditer(re.escape(PROJECT) + r"(?=[/\s'\"`;|&)]|$)(/[^\s'\"`;|&),]*)?", text):
        rel = (m.group(1) or "").lstrip("/").rstrip(".")
        shared = rel.startswith(".build/") and not rel.startswith(TREE_DIR + "/")
        if not (shared or (mine and (rel == mine or rel.startswith(mine + "/")))):
            out.append(m.group(0).rstrip("."))
    return list(dict.fromkeys(out))


def check_elsewhere(tid, check):
    """The paths a check command of a task in its own tree names outside that tree and outside `.build/`: the one
    tree's own directory, or another task's tree. The planner's working rule since 2026-09-20 pins a repository check
    to the one tree by an absolute script path, because incremental_check.py takes its project from its own path —
    which, in a tree, is exactly how a check would read the one tree and pass on work it never saw."""
    return one_tree_paths(check, os.path.join(TREE_DIR, str(tid))) if apart(tid) else []


# The files `tools/incremental_check.py retain` writes: the receipts of an accepted check, which a later check reuses.
# The harness retains those of every landing's check and commits them alone once the task has landed
# (finalize.retain_landed; until 2026-09-22 the planner placed a retention with each base advance, HANDOFF Q11). A
# task's own check is of its uncommitted work: task 94 committed its 166 with its theory, main's retention had written
# the same files, and its landing did not merge (2026-09-22 10:03).
RECEIPTS = ("validation/incremental-check.json", "validation/reconstruction/")


def receipts_in(files):
    return [f for f in files if os.path.normpath(f) == RECEIPTS[0] or os.path.normpath(f).startswith(RECEIPTS[1])]


def delivered_receipts(tid):
    """The receipts a task's brief delivers — a retention, or the report words its work changes, named in its
    Deliverable (the planner's rule) — which are its own work, not a check's by-product."""
    try:
        delivered = json.load(open(os.path.join(BUILD, tid, "brief.json"))).get("deliverables") or []
    except (OSError, ValueError, AttributeError):
        delivered = []
    return [os.path.normpath(d).rstrip("/") for d in delivered  # a file among them, or their directory
            if isinstance(d, str) and receipts_in([d, os.path.join(os.path.normpath(d), "x")])]


def receipts_refused(tid, files):
    """Receipts in a task's commit that no retention commits: with other files, and not what its brief delivers."""
    receipts = receipts_in(files)
    if not receipts or len(receipts) == len(files):
        return None
    named = delivered_receipts(tid)
    left = [f for f in receipts if not any(os.path.normpath(f) == d or os.path.normpath(f).startswith(d + "/")
                                           for d in named)]
    if not left:
        return None
    return (f"refused: {left[0]}" + (f" and {len(left) - 1} other receipt(s)" if len(left) > 1 else "") + " are what "
            "`tools/incremental_check.py retain` writes, and only a retention commits them: the harness retains and "
            "commits those of the check your work lands with, or a task whose brief delivers them. Your check is of "
            "your uncommitted work, and its receipts would collide with that retention when your work lands: leave "
            "them out of --files (what retain wrote in your tree is put back when your work lands)")


# A commit of documents only — Markdown outside the theories, the tools and the recorded validation — is checked by
# the finalizer itself (finalize.documents_check): the repository's structural source checks, the rows of THEORY_MAP.md,
# no conflict marker; seconds, and no heavy run. Designs and investigations invented an acceptance check each (design-
# 171: two requests, 2026-09-22) and still took a landing check of five minutes that no document can change the result
# of (the owner: notes/plan-landing-train.md 3.6).
DOCUMENTS_CHECK = "documents"
REPOSITORY_CHECK = "python3 -B tools/incremental_check.py check --output .build/tasks/{tid}/check"  # a hand-over's default
NOT_DOCUMENTS = ("theories/", "tools/", "validation/")


def documents_only(files):
    """Whether a commit takes Markdown documents only, outside the theories, the tools and the recorded validation."""
    return bool(files) and all(os.path.normpath(f).endswith(".md") and not os.path.normpath(f).startswith(NOT_DOCUMENTS)
                               for f in files)


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
    tree = worktree_of(tid)  # the finalizer checks and commits there: the files are the task's tree's
    taken = not files and tree != PROJECT
    if taken:
        # A task's own tree holds its changes alone, so what it has changed is what its commit takes: 78 requests of
        # the implementers and fixers of 2026-09-21/22 read git status and little else, most of them to name --files
        files = changed_paths(tree)
    defaulted = []
    if not check and documents_only(files):
        check = DOCUMENTS_CHECK  # the finalizer's own check of documents (finalize.documents_check)
    elif not check and files:
        # the repository's check, which 109 of the 126 hand-overs whose record stands named, written for them: nine
        # hand-overs of 2026-09-21/22 named one that was not runnable as written, and the batch runs its own anyway
        check = REPOSITORY_CHECK.format(tid=tid)
        defaulted.append(f"its check the repository's (`{check}`)")
    if not message and os.path.isfile(os.path.join(BUILD, str(tid), "commit.md")):
        message = os.path.relpath(os.path.join(BUILD, str(tid), "commit.md"), PROJECT)
        defaulted.append(f"its message {message}")
    # a path HEAD tracks is the repository's own, changed, deleted or matched by .gitignore alike (finalize.stage): task
    # 48's removal of a tracked compiled object was refused as "ignored" (2026-09-21)
    in_head = {f for f in files if git_out("cat-file", "-e", f"HEAD:{f}", quiet=True, tree=tree) is not None}
    bad = [f for f in files if not os.path.lexists(os.path.join(tree, f)) and f not in in_head
           and git_out("ls-files", "--error-unmatch", "--", f, quiet=True, tree=tree) is None]
    outside = [f for f in files if os.path.isabs(f) or os.path.normpath(f).startswith("..")
               or os.path.normpath(f).startswith(EXEMPT)  # the harness's own, always
               or (f not in in_head and (exempt(os.path.normpath(f))  # a compiled object nobody tracks
                                         or subprocess.run(["git", "-C", tree, "check-ignore", "-q", "--", f]).returncode == 0))]
    if outside:
        build = [f for f in outside if os.path.normpath(f).startswith(".build")]
        return ("refused: the finalizer commits files of the repository's working tree, not ignored, not under .build/ or "
                f".claude/, relative to the project: {', '.join(outside)}"
                + (". What stands under .build/ — a report, a result, drafts — is the task's record, read where it "
                   "stands and never committed: leave it out of --files" if build else ""))
    receipts = receipts_refused(tid, files)
    if receipts:
        return receipts
    standing = base_would_stand_in_a_task(check or "")
    if standing:
        return "refused: " + BASE_IN_A_TASK.format(named=", ".join(standing))
    elsewhere = check_elsewhere(tid, check or "")
    if elsewhere:
        return (f"refused: task {tid} works in its own tree ({os.path.relpath(tree, PROJECT)}) and this check names "
                f"{', '.join(elsewhere)}, outside it. The check tool takes its project from its own path, so it would "
                "check that tree and not your work: name it relative to your tree, where the finalizer runs it "
                "(`python3 -B tools/incremental_check.py …`); `.build/` is the one `.build` and may be named as it is.")
    if not check or not files or not message or bad or not os.path.exists(os.path.join(PROJECT, message)):
        return ("refused: v2.py finalize ID --check CMD --files PATH... --message FILE, every file existing (or a deletion "
                "of a tracked one); --check may be left out (the repository's check, or, when every file is a Markdown "
                "document, the finalizer's own of the documents and the sources), --message when the message is "
                f".build/tasks/{tid}/commit.md, --files in a tree of your own (what it has changed)"
                + (f" (missing: {', '.join(bad)})" if bad else ""))
    os.makedirs(os.path.join(BUILD, tid), exist_ok=True)
    json.dump({"check": check, "files": files, "message": message}, open(os.path.join(BUILD, tid, "finalize.json"), "w"), indent=1)
    what = f" ({len(files)} file{'s' * (len(files) > 1)} your tree has changed: {', '.join(files)})" if taken else ""
    what += f" ({'; '.join(defaulted)})" if defaulted else ""
    # The hand-over and the result are one event, and one call makes both (_finishing.md): a result the session wrote
    # this round is recorded with it. Of the 69 producing sessions of 2026-09-21/22 that recorded one, 41 handed over,
    # then wrote their result, then recorded it — two requests of several hundred thousand tokens each after the one
    # that could have held all three — and one made the protocol's single call.
    c, path = caller(), os.path.join(BUILD, tid, "result.md")
    if c and os.path.exists(path) and os.path.getmtime(path) >= max(c.get("started") or 0, c.get("resumed") or 0) - 1:
        text = open(path, errors="ignore").read()
        status = (field(text, "Status").split() or [""])[0].strip(".,").lower()
        if status == "done" and not result_problems(text):
            said = cmd_result(tid)
            if said.startswith("recorded"):
                with state() as st:
                    if c.get("name") in st["sessions"]:
                        st["sessions"][c["name"]]["handed"] = time.time()
                return f"the final job is prepared{what}, and your result (.build/tasks/{tid}/result.md) recorded with it. End your turn now."
            return f"the final job is prepared{what}; your result was not recorded with it: {said}"
    return (f"the final job is prepared{what}; its check runs when you record your result — write it and record it in "
            f"one command: `.claude/orchestration/v2.py result {tid} <<'EOF'`, then the result, then `EOF`")


# A probe the machine refuses (a measurement holds it or waits for it, or every probe slot is taken) was the session's
# to try again: it parked for the machine, was resumed, and ran it — or, with a change in the same call, lost the change
# too (implement-189, implement-182, fix-227, 2026-09-22 17:21–17:30). The owner: "put them in a queue for probes by
# allowing them to call it with a command signifying that they have nothing to do if probe is not ran" — and "why wait
# for a slot to be free in order to run the probe if there is space to run?". A probe led by QUEUE=1 is queued when the
# machine refuses it (work_meter rewrites the call to `v2.py queue-probe`), its session parks, the watchdog runs it as
# soon as the machine has room (run_queued_probes, whatever the producing slot is doing), and the session is resumed
# with its output.
PROBE_QUEUE = os.path.join(STATE, "probe-queue.json")


def probe_queue():
    import train
    return train.Queue(PROBE_QUEUE)


def cmd_queue_probe(encoded):
    """A producing session's probe, refused for the machine and marked QUEUE=1: queued to run in its working directory as
    soon as the machine has room, and the session parked until its output has come."""
    import base64
    c = caller()
    if not c or c["role"] not in PRODUCING or not c.get("task"):
        return "refused: a producing session queues its task's probe"
    try:
        command = base64.b64decode(encoded).decode()
    except ValueError:
        return "refused: the probe to queue could not be read"
    tid, key = c["task"], f"{c['task']}-{int(time.time() * 1000)}"
    probe_queue().put(key, head=None, command=command, cwd=os.getcwd(), session=c["name"], task=tid)
    with state() as w:
        w["tasks"].setdefault(tid, {}).update(stage="parked", parked={
            "since": time.time(), "for": "probe", "why": "", "after": None, "holds_tree": False, "questions": [],
            "holder": None, "run": "probe", "probe": key})
        w["sessions"][c["name"]]["state"] = "parked"
    log(f"task {tid}'s probe waits for room on the machine: it runs as soon as there is, and its session is parked")
    kick()
    turn_over(c)
    return ("queued: your probe runs as soon as the machine has room for it, without you. End your turn now: you are "
            "parked, the producing slot free meanwhile, and resumed here with its output.")


def run_queued_probes():
    """The watchdog's: start each queued probe the machine has room for (the guard's own condition for a probe), and
    give each that has ended its output — cut to a read, kept whole — as the result its parked session is resumed with.
    Whether one ended: its session is then ready to be resumed."""
    q, st, ended = probe_queue(), peek(), False
    for key, e in q.peek().items():
        if e.get("decided") or not e.get("pid"):
            continue
        if os.path.exists(f"/proc/{e['pid']}"):
            continue
        try:
            out = open(e["out"], errors="replace").read()
        except OSError:
            out = "(the probe left no output)"
        text = out if len(out.encode()) <= READ_BYTES else (
            f"[its output's last part; the whole is kept in {os.path.relpath(e['out'], PROJECT)}]\n"
            + out.encode()[-READ_BYTES:].decode(errors="ignore"))
        q.decide(key, 0, "ran")
        with state() as w:
            t = w["tasks"].get(e["task"]) or {}
            p = t.get("parked") or {}
            if t.get("stage") == "parked" and p.get("for") == "probe" and p.get("probe") == key:
                p.update(result="Your queued probe ran:\n" + text)
        log(f"task {e['task']}'s queued probe ran: its session is resumed with its output")
        ended = True
    for key, e in sorted(q.peek().items(), key=lambda x: x[1].get("queued", 0)):
        if e.get("decided") or e.get("pid"):
            continue
        if (st["sessions"].get(e.get("session")) or {}).get("state") != "parked":
            q.decide(key, 1, "dropped")  # its session went on, or away: the probe is no longer waited for
            continue
        if run_blocked((e["task"],), "probe"):
            break  # in the order queued: none jumps the one waiting before it
        import work_meter
        keep = outputs_of(e["session"])
        os.makedirs(keep, exist_ok=True)
        out = os.path.join(keep, f"queued-probe-{key}.txt")
        run = subprocess.Popen(["bash", "-c", work_meter.gathering(e["command"], e["cwd"], keep)], cwd=e["cwd"],
                               stdout=open(out, "w"), stderr=subprocess.STDOUT, start_new_session=True,
                               env=dict(os.environ, ORCH_READ_BYTES=str(READ_BYTES)))
        with q.open() as w:
            if key in w:
                w[key].update(pid=run.pid, out=out, started=time.time())
        log(f"task {e['task']}'s queued probe started: the machine has room for it")
    return ended


def cmd_bring_main():
    """A task's session asks for main in its branch (finalize.bring_main)."""
    c = caller()
    if not c or not c.get("task") or c.get("role") not in PRODUCING:
        return "refused: bring-main is for the session of a task in its own tree"
    import finalize
    return finalize.bring_main(str(c["task"]))


RESULT_ECHO = 10  # seconds: a result recorded by the hand-over, and the same call's `v2.py result` after it


def stdin_text():
    """The text a heredoc gave the command, or "" when it was given none: a terminal, /dev/null, or a pipe nobody
    writes, which is waited for a tenth of a second and no more."""
    try:
        if sys.stdin is None or sys.stdin.isatty():
            return ""
        ready, _, _ = select.select([sys.stdin], [], [], 0.1)
        return sys.stdin.read() if ready else ""
    except (OSError, ValueError):
        return ""


def cmd_result(tid, text=None):
    """Record a producing session's result; `text` (a heredoc's), when given, is written to result.md first, so that
    writing and recording are one command."""
    refused = own_task(tid)
    if refused:
        return refused
    path = os.path.join(BUILD, tid, "result.md")
    c = caller()
    final = os.path.join(BUILD, tid, "finalize.json")
    at = (c or {}).get("handed") or 0  # when a hand-over last recorded this session's result (cmd_finalize)
    if at and (c.get("state") == "done" or time.time() - at < RESULT_ECHO) \
            and os.path.exists(final) and os.path.getmtime(final) <= at:
        # recorded already, by the hand-over (cmd_finalize), and nothing handed over since: the protocol's `&& v2.py
        # result` after it. Read by the time too: a documents check fails in seconds, and its quick fix can resume
        # the session (working again) before that same call reaches here
        if text and text.strip():
            open(path, "w").write(text if text.endswith("\n") else text + "\n")
            return "your result was recorded with the hand-over; its text is now the one given. End your turn now."
        return "recorded already, with the hand-over. End your turn now."
    if text and text.strip():
        os.makedirs(os.path.dirname(path), exist_ok=True)
        open(path, "w").write(text if text.endswith("\n") else text + "\n")
    text = open(path, errors="ignore").read() if os.path.exists(path) else ""
    problems = result_problems(text) if text else [f"write the result to .build/tasks/{tid}/result.md first"]
    if problems:
        return "refused: the result is not in form:\n- " + "\n- ".join(problems)
    status = field(text, "Status").split()[0].strip(".,").lower()
    try:
        committed_files = [p for p in json.load(open(os.path.join(BUILD, tid, "brief.json")))["deliverables"]
                           if not placed(p, tid).startswith(".build/")]
    except (OSError, ValueError, KeyError):
        committed_files = []
    if status == "done" and committed_files and not os.path.exists(final):
        tree = worktree_of(tid)
        unwritten = [p for p in committed_files if not os.path.lexists(os.path.join(tree, p))]
        return (f"refused: your brief delivers {', '.join(committed_files)} into the repository, and a done task's "
                "files there are committed by the finalizer: hand it the final job first (`v2.py finalize "
                f"{tid}` in a tree of your own, `--files` naming them in the one tree)"
                + (f". Not written yet: {', '.join(unwritten)}" if unwritten else "")
                + "; what it delivers under .build/ is read where it stands and is never committed")
    c = caller()
    refused = jobs_refusal(c, "record your result")
    if refused:
        return refused
    # A session that ends with a question of its own open reads nothing ever again: six of nineteen answers on
    # 2026-09-20 came to a session that had gone, and each had to be carried by the planner instead. What it assumed
    # instead goes into its result, which names the question: it was told so after recording, and implement-40 wrote a
    # closing summary instead, a request that left its result as it was (2026-09-22 10:36).
    open_asks = [q for q, a in peek()["asks"].items()
                 if a["from"] == (c or {}).get("name") and a["state"] != "answered"]
    unnamed = [q for q in open_asks if not re.search(rf"\b{re.escape(q)}\b", text)]
    if unnamed:
        return (f"refused: your question{'s' if len(unnamed) > 1 else ''} {', '.join(unnamed)} "
                f"{'are' if len(unnamed) > 1 else 'is'} still open, and you will not read the answer, which goes to "
                f".build/tasks/{tid}/answers/ and to the planner. Say in your result what you assumed instead, naming "
                f"{'each' if len(unnamed) > 1 else 'it'}, and record it again")
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
        elif (c or {}).get("role") == "task-designer" or t.get("role") == "task-designer":
            # a brief's outcome is its proposal, placed by the planner: `reviewing` is no stage of a brief — nothing
            # reviews one, and `accept` reads `proposed`. Recorded after the proposal (as it is told to), the result
            # made every proposal unplaceable and its reminder silent (2026-09-21)
            if t.get("stage") not in ("proposed", "planner"):
                to_planner(st, tid, name or "the harness", f"Brief task {tid} ended without proposing any task: "
                           f".build/tasks/{tid}/result.md says why. Re-plan it, or drop it.")
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
    turn_over(c)
    return "recorded. End your turn now."


def spliced(group, after):
    """The members of a group that are detail, read on the graph `after` as the change would leave it: something
    already there waits on them, directly or through the group's own edges. Detail makes the plan finer without
    reaching past where it already ended, and is admitted at any depth (the owner, 2026-09-20).

    `after` has the group's `feeds` wired already — an existing task that is to wait on a member does — so a member
    that feeds is fed by that edge. Until 2026-09-21 this read the graph as it stood, took `feeds` on trust as a seed,
    and was written twice (the weaker copy once the one in force, with a green test covering the dead one): one
    reading of detail now serves the proposal, `accept`, the planner's edit and its single edits."""
    fed = {b for x in after.values() if x.get("id") not in group and x.get("status") != "completed"
           for b in (x.get("blockedBy") or []) if b in group}          # existing work waits on us
    stack = list(fed)
    while stack:                                                      # and closed under the group's own edges
        for b in (group.get(stack.pop()) or {}).get("blockedBy") or []:
            if b in group and b not in fed:
                fed.add(b)
                stack.append(b)
    return fed


def goal_refusal(tid, blocked_by, waiters=()):
    """Why making task tid wait on `blocked_by` (with `waiters` made to wait on it in the same edit) is refused, or
    None: it would hang tid past the graph's frontier — a further goal, waiting on open work that nothing already
    there waits on — while the chain is deeper than GRAPH_DEPTH. The owner's rule is the brief's (past_the_limit) and
    now the planner's too: "I do not allow to add to the end of a task chain if it is above 10 in depth", so that the
    queue cannot balloon, and the planner is not to try it (2026-09-21). A task that already waits on open work is
    being re-shaped, not added: its edges are the planner's to move."""
    tasks = {t["id"]: dict(t) for t in all_tasks()}
    is_open = lambda b: b in tasks and tasks[b].get("status") != "completed"
    if any(is_open(b) for b in (tasks.get(tid) or {}).get("blockedBy") or []):
        return None
    group = {tid: {"blockedBy": [b for b in blocked_by if b != tid], "feeds": list(waiters)}}
    after = {k: dict(v) for k, v in tasks.items()}
    after.setdefault(tid, {"id": tid, "status": "pending"})["blockedBy"] = group[tid]["blockedBy"]
    for w in waiters:
        if w in after:
            after[w]["blockedBy"] = list(dict.fromkeys((after[w].get("blockedBy") or []) + [tid]))
    past = past_the_limit(group, after)
    if not past:
        return None
    return (f"task {tid} would be added at the end of a chain already {past[0][1]} deep, above {GRAPH_DEPTH}: it waits "
            f"on {', '.join(b for b in blocked_by if is_open(b))} and nothing already in the graph waits on it. "
            "Nothing is added at the end of a chain past the limit. Splice it in instead (make what should wait on it "
            "wait on it first: `addBlocks`, or `v2.py blockers`), hang it on a shorter chain, let it run first — or, "
            "if the chain is long because of work found wrong, delete or rewrite that work first.")


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


def graph_after(bid, entries):
    """(group, after): a proposal's tasks as a group named as they would stand in the graph (`+key`), and the graph
    they would make — its brief task completed, its tasks written with their edges, and what they feed re-pointed onto
    them, as `accept` would leave it. Nothing is written."""
    tasks = {t["id"]: dict(t) for t in all_tasks()}
    keys = {e["key"] for e in entries}
    name = lambda b: "+" + b if b in keys else b
    after = {k: dict(v) for k, v in tasks.items()}
    if bid in after:
        after[bid]["status"] = "completed"  # accept completes the brief task
    group = {}
    for e in entries:
        group["+" + e["key"]] = {"blockedBy": [name(b) for b in e.get("blockedBy") or []],
                                 "feeds": list(e.get("feeds") or [])}
        after["+" + e["key"]] = {"id": "+" + e["key"], "status": "pending", "description": e.get("description", ""),
                                 "blockedBy": group["+" + e["key"]]["blockedBy"]}
        for f in e.get("feeds") or []:
            if f in after:
                after[f]["blockedBy"] = ["+" + e["key"]] + [b for b in after[f].get("blockedBy") or [] if b != bid]
    return group, after


def proposal_text(bid, entries):
    """What the planner needs to place a proposal, and nothing it does not: each task's kind, subject, size and why,
    what it waits on and what it is spliced before, where that puts it — first, detail, inside the brief's own work,
    or a further goal — and the depth the chain would have. Not the briefs: they are written for the sessions that
    will do the work, several thousand characters each, and until 2026-09-21 the planner was told to read the whole
    file to place a proposal, which put every brief of every proposal into the one context that lives across the run
    (`v2.py proposal ID KEY` prints one when a decision turns on it)."""
    tasks = {t["id"]: dict(t) for t in all_tasks()}
    name = lambda x: (f"{x} ({tasks[x]['subject'][:60]})" if x in tasks else x)
    keys = {e["key"] for e in entries}
    group, after = graph_after(bid, entries)
    fed = {n[1:] for n in spliced(group, after)}
    is_open = lambda b: (tasks.get(b) or {}).get("status") not in ("completed", None)
    goals = {e["key"] for e in entries if e["key"] not in fed
             and any(b not in keys and b != bid and is_open(b) for b in e.get("blockedBy") or [])}
    past = {n[1:]: d for n, d in past_the_limit(group, after)}
    depths = chain_depths(after)
    lines = []
    for e in entries:
        kind, size = brief_kind(e.get("description", "")), size_of(e.get("description", ""))
        outside = [b for b in e.get("blockedBy") or [] if b not in keys and b != bid]
        where = (f"PAST THE LIMIT: it would hang after a chain {past[e['key']]} deep" if e["key"] in past else
                 "at the end of a chain" if e["key"] in goals else
                 "detail, spliced in" if e["key"] in fed else
                 "inside the brief's own work" if any(b in keys for b in e.get("blockedBy") or []) else
                 "runs first" if not any((tasks.get(b) or {}).get("status") != "completed" for b in outside) else
                 "after work already in the graph")
        lines.append(f"- {e['key']}: {kind}, \"{e.get('subject', '')}\""
                     + (f", about {size // 1000}K" if size else "") + f" — {where}, chain {depths.get('+' + e['key'], 0)}"
                     + (f"; waits on {', '.join(name(b) if b not in keys else b for b in e['blockedBy'])}"
                        if e.get("blockedBy") else "")
                     + (f"; spliced before {', '.join(name(f) for f in e['feeds'])}" if e.get("feeds") else "")
                     + (f". Why: {e['why']}" if (e.get("why") or "-").strip() not in ("", "-") else ""))
    depth, then = graph_shape(tasks=tasks)[1], graph_shape(tasks=after)[1]
    return ("\n".join(lines) + f"\nThe longest chain goes from {depth} to {then} deep. Nothing is added at the end of a "
            f"chain already deeper than {GRAPH_DEPTH}; detail and work that runs first are added at any depth.")


def cmd_proposal(bid, keys=()):
    """The planner reads a proposal: what placing it needs, or as many of its briefs as a decision turns on, in one
    call — reading is limited so that it is batched, never so that it is rationed (the owner, 2026-09-21)."""
    rec = peek()["tasks"].get(bid) or {}
    try:
        entries = json.load(open(os.path.join(PROJECT, rec["proposal"])))
    except (KeyError, OSError, ValueError):
        return f"refused: brief task {bid} has no proposal that can be read"
    if not keys:
        return proposal_text(bid, entries)
    out = []
    for key in keys:
        e = next((x for x in entries if x.get("key") == key), None)
        out.append(f"refused: the proposal of task {bid} has no task {key!r} (it has "
                   f"{', '.join(x.get('key', '?') for x in entries)})" if e is None else
                   f"== {key}: {e.get('subject', '')}\nwaits on: {', '.join(e.get('blockedBy') or []) or 'nothing'}"
                   + (f"; spliced before {', '.join(e['feeds'])}" if e.get("feeds") else "")
                   + f"\n\n{e.get('description', '')}")
    return "\n\n".join(out)


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
    # per chain, and above the limit, not at it (the owner, 2026-09-21): a task may end a chain of GRAPH_DEPTH and
    # may not hang after one deeper. Measured on the graph the proposal would make, so a brief cannot grow a chain
    # of its own past the limit either; the longest chain of the whole graph, taken when the brief began, was the
    # measure until then, and refused a goal at the end of a short chain whenever another was deep.
    past = past_the_limit(*graph_after(bid, entries))
    if past:
        return refuse_proposal(bid, entries, past)
    placing = proposal_text(bid, entries)
    with state() as w:
        w["tasks"].setdefault(bid, {}).update(stage="proposed", proposal=path, proposed=len(entries))
        event(w, "the harness", f"Brief task {bid} proposes {len(entries)} task(s) and where to place them:\n"
              + placing + "\nThey are not in the graph: you place them (`v2.py accept " + bid + "`, which writes them "
              "as proposed and queues them after this brief), or say what to change first (`v2.py tell " + bid + " "
              "\"...\"`: its task designer, held meanwhile, revises and proposes again) — the graph is yours alone "
              "to edit. Their briefs are for the sessions that will do the work; `v2.py proposal " + bid + " KEY` "
              "prints one when a decision turns on it.")
    kick()
    return (f"proposed {len(entries)} task(s); the planner places them. Record your result (`v2.py result {bid}`) "
            "with what you briefed and why each waits on what it does, and end your turn.")


def refuse_proposal(bid, entries, past):
    said = ", ".join(f"{n[1:]} (after a chain {d} deep)" for n, d in past)
    with state() as w:
        w["tasks"].setdefault(bid, {})["stage"] = "planner"
        event(w, "the harness", f"Brief task {bid} is yours to resolve. Its detailing would add {said} at the end of "
              f"a chain already deeper than {GRAPH_DEPTH}: waiting on it, with nothing already there waiting on them. "
              "Detail spliced into the graph is admitted at any depth, and so is work at the end of a shorter chain; "
              "past the limit it is not, and the detailing is not wrong for needing it. Its proposal stands in "
              f".build/tasks/{bid}/ and nothing is in the graph: place what belongs, shorten the chain it hangs on "
              "(a task found wrong is deleted or rewritten, not worked around), or let the work go.")
    log(f"brief {bid} would add {len(past)} task(s) past a chain above {GRAPH_DEPTH}: refused, the planner has it")
    kick()
    return (f"refused, and the planner has it: {said} would be added at the end of a chain already deeper than "
            f"{GRAPH_DEPTH}, not spliced in as detail. Nothing you wrote is lost — the proposal stands. Do not "
            f"re-shape the detailing to fit the graph; record your result (`v2.py result {bid}`) saying what the work "
            "needs and why, and end your turn.")


class GraphEditFailed(Exception):
    def __init__(self, cause, written):
        super().__init__(repr(cause))
        self.cause, self.written = cause, written


EDIT_OPS = ("create", "rewrite", "blockers", "delete", "queue")


def apply_graph_edit(ops):
    """Write a checked edit of the graph, all of it or none, and return {key: id} of the tasks it made. Tasks are made
    first, without edges, so that one may wait on one made later in the list; then rewrites, edges, what the new
    tasks feed (re-pointed onto them, and off the brief task an `instead` names) and deletions. Every task file it
    touches is kept as it was, and a failure part way puts each back and takes the new ones out: a half-written edit
    leaves tasks with no edges, or existing ones waiting on ids that no longer exist (2026-09-21)."""
    ids, made, kept = {}, [], {}
    resolve = lambda x: ids.get(x, x)

    def keep(tid):
        if tid not in kept and tid not in made:
            kept[tid] = read_task(tid)
    try:
        for op in ops:
            if "create" in op:
                ids[op["create"]] = create_task(op.get("subject", ""), op.get("description", ""),
                                                {"kind": brief_kind(op.get("description", "")), "why": op.get("why", ""),
                                                 **({"continues": str(op["continues"])} if op.get("continues") else {})},
                                                [])
                made.append(ids[op["create"]])
        for op in ops:
            if "create" in op:
                update_task(ids[op["create"]], blockedBy=[resolve(b) for b in op.get("blockedBy") or []])
            elif "rewrite" in op:
                keep(op["rewrite"])
                fields = {k: op[k] for k in ("subject", "description") if k in op}
                if "why" in op or "continues" in op:
                    fields["metadata"] = dict((read_task(op["rewrite"]) or {}).get("metadata") or {},
                                              **{k: op[k] for k in ("why", "continues") if k in op})
                update_task(op["rewrite"], **fields)
            elif "blockers" in op:
                keep(resolve(op["blockers"]))
                update_task(resolve(op["blockers"]), blockedBy=[resolve(b) for b in op.get("set") or []])
        for op in ops:
            for f in op.get("feeds") or []:  # existing work re-pointed onto the new: detail, not a further goal
                keep(f)
                waited = (read_task(f) or {}).get("blockedBy") or []
                update_task(f, blockedBy=[ids[op["create"]]] + [b for b in waited if b != op.get("instead")])
        for op in ops:
            if "delete" in op:
                keep(op["delete"])
                os.remove(task_path(op["delete"]))
    except Exception as err:  # noqa: BLE001
        for tid, was in kept.items():
            with contextlib.suppress(Exception):
                if was is None:
                    os.remove(task_path(tid))
                else:
                    json.dump(was, open(task_path(tid) + ".tmp", "w"), indent=2)
                    os.replace(task_path(tid) + ".tmp", task_path(tid))
        for tid in made:
            with contextlib.suppress(OSError):
                os.remove(task_path(tid))
        log(f"a graph edit failed and was taken back: {err!r}")
        raise GraphEditFailed(err, len(made))
    return ids


PLANS = os.path.join(PROJECT, ".build", "plans")  # the planner's drafts, .build/plans/NAME/


def edit_descriptions(ops):
    """What refuses the briefs an edit names by file, or nothing; each read into its operation's description. The
    planner drafts briefs under .build/plans/NAME/, where `v2.py change` writes and corrects them, and an edit took them
    only inline, as JSON strings: on 2026-09-21 the planner wrote a script to put 14 drafts into one edit, refused as a
    script that writes, a request spent and every brief a second time. `"descriptionFile": PATH` (from the repository,
    under .build/plans/) names the draft instead; the edit is still judged whole, a draft that cannot be read with it."""
    out = []
    for op in ops if isinstance(ops, list) else []:
        if not isinstance(op, dict) or "descriptionFile" not in op:
            continue
        name, path = op.get("create") or op.get("rewrite"), op["descriptionFile"]
        if "description" in op:
            out.append(f"task {name}: a description or a descriptionFile, not both")
            continue
        full = os.path.normpath(os.path.join(PROJECT, str(path)))
        if not full.startswith(PLANS + os.sep):
            out.append(f"task {name}: descriptionFile {path} is not a draft under .build/plans/")
            continue
        try:
            op["description"] = open(full, encoding="utf-8").read().strip()
        except (OSError, UnicodeDecodeError) as e:
            out.append(f"task {name}: descriptionFile {path} cannot be read ({getattr(e, 'strerror', None) or e})")
            continue
        del op["descriptionFile"]
    return out


def graph_edit_problems(ops):
    """What is wrong with a planner's edit of the graph, judged whole before anything is written: its form, every
    reference, what it would leave waiting on a deleted task, a cycle, and a task it would add at the end of a chain
    already past the limit. Deleting, rewriting and re-pointing are never refused for depth: what the planner planned
    before does not bind it (the owner, 2026-09-21)."""
    if not isinstance(ops, list) or not ops:
        return ["the edit is a JSON list of operations, and it names none"]
    tasks = {t["id"]: dict(t) for t in all_tasks()}
    out, keys = [], [op.get("create") for op in ops if isinstance(op, dict) and "create" in op]
    deleted = {op["delete"] for op in ops if isinstance(op, dict) and "delete" in op}
    known = (set(tasks) | set(keys)) - deleted
    for k in {k for k in keys if keys.count(k) > 1}:
        out.append(f"two tasks share the key {k!r}")
    for op in ops:
        which = [k for k in EDIT_OPS if isinstance(op, dict) and k in op]
        if len(which) != 1:
            out.append(f"an operation is exactly one of {', '.join(EDIT_OPS)}: {json.dumps(op)[:120]}")
            continue
        k, x = which[0], op[which[0]]
        if k == "create":
            if not x or x in tasks:
                out.append(f"a new task needs a key of its own, not {x!r}")
            if not (op.get("subject") or "").strip():
                out.append(f"task {x}: no subject")
            out += [f"task {x}: {p}" for p in brief_problems(op.get("description", ""))]
            out += [f"task {x} waits on {b!r}, which is not in the list or this edit" for b in op.get("blockedBy") or []
                    if b not in known]
            out += [f"task {x} feeds {f!r}, which is not an open task of the list" for f in op.get("feeds") or []
                    if f not in tasks or f in deleted or tasks[f].get("status") == "completed"]
        if k in ("create", "rewrite") and op.get("continues") and str(op["continues"]) not in tasks:
            out.append(f"task {x} continues {op['continues']!r}, which is not a task of the list")
        elif k == "rewrite":
            if x not in tasks or x in deleted:
                out.append(f"there is no task {x!r} to rewrite")
            if "description" in op:
                out += [f"task {x}: {p}" for p in brief_problems(op["description"])]
            if set(op) - {"rewrite", "subject", "description", "why", "continues"}:
                out.append(f"a rewrite of task {x} changes its subject, description, why or continues, and nothing else")
        elif k == "blockers":
            if x not in known:
                out.append(f"there is no task {x!r} to set the dependencies of")
            out += [f"task {x} would wait on {b!r}, which is not in the list or this edit"
                    for b in op.get("set") or [] if b not in known]
            if x in (op.get("set") or []):
                out.append(f"task {x} cannot wait on itself")
        elif k == "delete":
            if x not in tasks:
                out.append(f"there is no task {x!r} to delete")
        elif k == "queue":
            out += [f"the order names {q!r}, which is not in the list or this edit" for q in x or [] if q not in known]
            if not x:
                out.append("a queue operation names the order whole, and this one names nothing")
    if out:
        return out
    # the graph as the edit would leave it: new tasks by their keys, which never shadow an id
    after = {k: v for k, v in tasks.items() if k not in deleted}
    for op in ops:
        if "create" in op:
            after[op["create"]] = {"id": op["create"], "status": "pending", "description": op.get("description", ""),
                                   "blockedBy": list(op.get("blockedBy") or [])}
    for op in ops:
        if "blockers" in op:
            after[op["blockers"]] = dict(after[op["blockers"]], blockedBy=list(op.get("set") or []))
        if "rewrite" in op and "description" in op:
            after[op["rewrite"]] = dict(after[op["rewrite"]], description=op["description"])
    for op in ops:
        for f in op.get("feeds") or []:
            after[f] = dict(after[f], blockedBy=[op["create"]] + list(after[f].get("blockedBy") or []))
    for tid, t in after.items():
        gone = [b for b in t.get("blockedBy") or [] if b in deleted]
        if gone and t.get("status") != "completed":
            out.append(f"task {tid} would still wait on {', '.join(gone)}, which this edit deletes: re-point it "
                       f"(`blockers`) or delete it in the same edit")
    for tid in after:
        if any(waits_on(after, b, tid) for b in after[tid].get("blockedBy") or [] if b in after):
            out.append(f"task {tid} would wait on itself through the graph: a cycle nothing could ever start")
            break
    is_open = lambda b: b in tasks and tasks[b].get("status") != "completed"
    group = {op["create"]: {"blockedBy": list(op.get("blockedBy") or []), "feeds": list(op.get("feeds") or [])}
             for op in ops if "create" in op}
    group.update({op["blockers"]: {"blockedBy": list(op.get("set") or []), "feeds": []} for op in ops
                  if "blockers" in op and op["blockers"] in tasks
                  and not any(is_open(b) for b in tasks[op["blockers"]].get("blockedBy") or [])})
    out += [f"task {n} would be added at the end of a chain already {d} deep, above {GRAPH_DEPTH}: splice it in "
            "(make what should wait on it wait on it), hang it on a shorter chain, or let it run first"
            for n, d in past_the_limit(group, after)]
    return out


def cmd_edit(path):
    """The planner's edit of the graph, batched: tasks made, rewritten and deleted, and dependencies set or taken out,
    in one call, judged whole and written all or nothing. TaskCreate and TaskUpdate take one task and one change a
    call, and a correction made of several of them left the graph half changed between calls — a task deleted with
    something still waiting on it, a splice made on one side only (the owner, 2026-09-21: every command batchable,
    writing and editing too)."""
    refused = planner_only("editing the graph")
    if refused:
        return refused
    try:
        ops = json.load(open(os.path.join(PROJECT, path)))
    except (OSError, ValueError) as e:
        return f"refused: {path} is not an edit in JSON ({e!r})"
    problems = edit_descriptions(ops) or graph_edit_problems(ops)
    if problems:
        return "refused, and nothing is written:\n- " + "\n- ".join(problems)
    try:
        ids = apply_graph_edit([op for op in ops if "queue" not in op])
    except GraphEditFailed as err:
        return f"refused: the edit could not be written ({err.cause!r}); what it had written is taken back"
    said = [drop(op["delete"], "deleted") for op in ops if "delete" in op]
    for op in ops:  # a session at work reads its brief as it now stands
        if "rewrite" in op and "description" in op and os.path.exists(os.path.join(BUILD, str(op["rewrite"]), "brief.json")):
            brief_record(str(op["rewrite"]), op["description"])
    link_reviews()
    order = [op["queue"] for op in ops if "queue" in op]
    queued = cmd_queue([ids.get(q, q) for q in order[-1]]) if order else ""
    log(f"the planner edited the graph: {len(ops)} operation(s)" + (f"; made {', '.join(ids.values())}" if ids else ""))
    kick()
    # a task that came back moves again only when it is queued: plan-33 rewrote task 24's brief at 23:30 and it stood
    # until the standstill notice at 23:59 (2026-09-21) — said at once, when the rewrite is made
    touched = {str(op.get("rewrite") or ids.get(op.get("blockers"), op.get("blockers"))) for op in ops
               if "rewrite" in op or "blockers" in op}
    back = [t for t in with_the_planner(peek()) if t in touched]
    return ("edited: " + "; ".join(filter(None, [
        ", ".join(f"{k} is task {v}" for k, v in ids.items()),
        f"{sum(1 for op in ops if 'rewrite' in op)} rewritten" if any("rewrite" in op for op in ops) else "",
        f"{sum(1 for op in ops if 'blockers' in op)} with dependencies set" if any("blockers" in op for op in ops) else "",
        ("deleted " + ", ".join(op["delete"] for op in ops if "delete" in op)) if said else "",
        queued])) + (f". Task{'s' if len(back) > 1 else ''} {', '.join(back)} came back to you and "
                     f"{'move' if len(back) > 1 else 'moves'} again only when queued (`v2.py queue ID...`, in your "
                     "order): a rewrite does not restart a task" if back else ""))


# ---------------------------------------------------------------- changing files

# A session changes files with one command, `v2.py change`, its changes in a quoted heredoc of the same call (the
# owner, 2026-09-21). Edit took one replacement a call, Write one file, and the two were batched in 10 of the 268
# requests that held them; a command's writes — a redirection, `sed -i`, a script — fail silently when they match
# nothing, and name their files only as far as the guard can read the shell. This takes any number of changes to any
# number of files, judges them whole, writes all or none, and names its files exactly: the guard reads the same
# blocks (work_meter.write_targets).
CHANGE_HEAD = re.compile(r"^=== (write|append|replace|replace-all|row|root) (\S.*?)\s*$")
# The index files are edited by the theory they index, as their merges read them (finalize.ROW_KEYS): a THEORY_MAP.md
# row was quoted before it could be replaced and its imports copied by hand (161 requests of the implementers and
# fixers of 2026-09-21/22 did nothing else, 13M; 138 of the map's 1,812 rows named imports their theory no longer
# has), and a ROOT line was found and edited the same way.
KEYED_HEAD = re.compile(r"^([A-Za-z][\w']*)(?:\s+after\s+([A-Za-z][\w']*))?$")
MAP_ROW = re.compile(r"^\|\s*([A-Za-z_][\w.]*)\s*\|")
ROOT_ENTRY = re.compile(r"^(\s{4})([A-Za-z_][\w.]*)\s*$")
SEARCH, DIVIDER, REPLACE = "<<<<<<< SEARCH", "=======", ">>>>>>> REPLACE"
CHANGE_FORM = ("a change begins `=== write PATH` (the whole file follows, to the next `===` line), `=== append PATH` "
               "(what follows is added at the file's end: a log's next entry, nothing to match), or `=== replace "
               f"PATH` or `=== replace-all PATH`, each followed by blocks of `{SEARCH}`, the text as it stands, "
               f"`{DIVIDER}`, the text that replaces it, `{REPLACE}`; or `=== row THEORY` (its THEORY_MAP.md row's "
               "content follows) or `=== root THEORY [after OTHER]` (its declaration in ROOT, nothing follows)")


def marker_at(body, start, marker, nested):
    """The index of the block's own `marker` line from `start`, or None; `nested`: a SEARCH line opens a block inside
    the text, whose own lines are passed over up to its REPLACE (a correction's text is a change's)."""
    depth = 0
    for x in range(start, len(body)):
        if nested and body[x] == SEARCH:
            depth += 1
        elif nested and depth and body[x] == REPLACE:
            depth -= 1
        elif not depth and body[x] == marker:
            return x
    return None


def change_blocks(text, markers=True):
    """(the changes a `v2.py change` text names, in order; what is wrong with its form). A change is a dict with op
    (write, replace, replace-all), path, n (its number, which a refusal names) and text, or old and new. `markers`: a
    block whose text holds a marker line is refused (it lost a line of its own); off for `v2.py again`, whose blocks
    correct a command that is itself made of such lines — fix-48's correction of its change was refused so
    (2026-09-21) — and whose fixed command is checked when it runs."""
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    ops, problems, i = [], [], 0
    while i < len(lines):
        head = CHANGE_HEAD.match(lines[i])
        if not head:
            if lines[i].strip():
                problems.append(f"line {i + 1} stands outside any change: {CHANGE_FORM}")
                while i < len(lines) and not CHANGE_HEAD.match(lines[i]):
                    i += 1
                continue
            i += 1
            continue
        verb, path = head.groups()
        start = i = i + 1
        # a correction (`again`) is one block list on the command it fixes, whose text holds that command's own heads
        # and blocks: read to its end, its markers nested — implement-72's correction of its change, which dropped a
        # `=== replace ROOT` block, was read as a second change and refused (2026-09-22)
        while i < len(lines) and not (markers and CHANGE_HEAD.match(lines[i])):
            i += 1
        body = lines[start:i]
        if verb in ("row", "root"):
            keyed = KEYED_HEAD.match(path)
            text = " ".join(x.strip() for x in body if x.strip())
            if not keyed:
                problems.append(f"`=== {verb} {path}` names no theory: `=== row THEORY [after OTHER]`, then the content "
                                "of its THEORY_MAP.md row; `=== root THEORY [after OTHER]`, alone")
            elif verb == "root" and text:
                problems.append(f"`=== root {path}` is followed by text: a declaration is its head line alone")
            elif verb == "row" and re.search(r"(?<!\\)\|", text):
                problems.append(f"the row of {keyed.group(1)} holds a `|`, which ends a table cell: write it `\\|`")
            else:
                ops.append({"op": verb, "path": "THEORY_MAP.md" if verb == "row" else "ROOT", "n": len(ops) + 1,
                            "theory": keyed.group(1), "after": keyed.group(2), "text": text})
            continue
        if verb in ("write", "append"):
            while body and body[-1] == "":
                body.pop()
            ops.append({"op": verb, "path": path, "n": len(ops) + 1, "text": "".join(x + "\n" for x in body)})
            continue
        j, blocks = 0, 0
        while j < len(body):
            if not body[j].strip():
                j += 1
                continue
            if body[j] != SEARCH:
                problems.append(f"line {start + j + 1}, under `=== {verb} {path}`, stands outside a block: {CHANGE_FORM}")
                break
            k = marker_at(body, j + 1, DIVIDER, not markers)
            r = marker_at(body, k + 1, REPLACE, not markers) if k is not None else None
            if r is None:
                problems.append(f"the block at line {start + j + 1} (`=== {verb} {path}`) has no "
                                f"`{DIVIDER if k is None else REPLACE}` line")
                break
            ops.append({"op": verb, "path": path, "n": len(ops) + 1, "old": "\n".join(body[j + 1:k]),
                        "new": "\n".join(body[k + 1:r])})
            if not ops[-1]["old"]:
                problems.append(f"change {ops[-1]['n']} ({verb} {path}) searches for nothing: a whole file is "
                                "written with `=== write`")
            # A block ends at its first `=======` and its first `>>>>>>> REPLACE`, so a marker line inside its text
            # means one of its own is missing and it has taken in the next block: without its REPLACE line, the next
            # block's markers and texts were written into the file as its replacement (design-66's entry.md, eight
            # blocks, 2026-09-21: five requests to find and repair it)
            for part, at, text, missing in (("search", j + 1, body[j + 1:k], DIVIDER),
                                            ("replacement", k + 1, body[k + 1:r], REPLACE))[:2 if markers else 0]:
                held = next(((x, at + i) for i, x in enumerate(text) if x in (SEARCH, DIVIDER, REPLACE)), None)
                if held:
                    # Either reading leaves the file wrong, so it says both and the way out of each: 20 of the day's
                    # refusals were a `=======` in a replacement (2026-09-22), and being sent to write the file whole
                    # costs a session the file's whole text where two blocks around the line cost it nothing.
                    line, where = held
                    problems.append(f"change {ops[-1]['n']} ({verb} {path}), the block at line {start + j + 1}: its "
                                    f"{part} text holds a `{line}` line at line {start + where + 1}, so either its "
                                    f"own `{missing}` line is missing and it has taken in the next block, or that "
                                    f"line belongs to the {part} text — then make two blocks, one for what stands "
                                    "before that line and one for what stands after, or write the file whole "
                                    "(`=== write`)")
                    break
            blocks, j = blocks + 1, r + 1
        if not blocks and not problems:
            problems.append(f"`=== {verb} {path}` has no {SEARCH} block")
    if not ops and not problems:
        problems.append(f"it names no change: {CHANGE_FORM}")
    return ops, problems


def change_path(base, path):
    return os.path.normpath(os.path.join(base, os.path.expanduser(path)))


def replace_one(text, op, what):
    """(the text with one replacement made, the line it landed at; or what refuses it): its SEARCH must occur once, or
    at least once for replace-all."""
    count = text.count(op["old"])
    if count == 0 or (count > 1 and op["op"] == "replace"):
        first = op["old"].split("\n")[0].strip()
        where = [n for n, line in enumerate(text.split("\n"), 1) if first and first in line][:5]
        return None, None, (f"change {op['n']} ({op['op']} {what}): its SEARCH text occurs {count} times in the {what} "
                            "as it stands, and must occur " + (
                                "once — widen it until it is unique, or use `=== replace-all`" if count else
                                "once" + (f"; its first line stands at line {', '.join(map(str, where))}: compare the "
                                          "rest, whitespace included" if where else "; its first line does not occur "
                                          "either")))
    return (text.replace(op["old"], op["new"], -1 if op["op"] == "replace-all" else 1),
            text[:text.find(op["old"])].count("\n") + 1, None)


def theory_text(base, name, now):
    """A theory's text as the call leaves it (`now`), else as it stands at `base`; None when it is not there."""
    path = change_path(base, os.path.join("theories", f"{name}.thy"))
    if path in now:
        return now[path]
    try:
        return open(path, encoding="utf-8", newline="").read()
    except (OSError, UnicodeDecodeError):
        return None


def keyed_edit(op, text, base, now):
    """(the index file's text with one theory's row or declaration written, the line it stands at, what was done; or
    None, None and what refuses it). A row is `| THEORY | its imports | its content |`, the imports read from the
    theory as the call leaves it; with no content given the row's own stands and its imports are read again. A new row
    goes after the row of the nearest theory ROOT declares before it (a map that follows ROOT's order stays so), else
    after the table's last row. A declaration goes after OTHER's, or after the last line of ROOT declaring one of its
    imports, else after its last theory line."""
    name, lines = op["theory"], text.split("\n")
    source = theory_text(base, name, now)
    if source is None:
        return None, None, (f"theories/{name}.thy is not there, where the {'row' if op['op'] == 'row' else 'declaration'}"
                            "'s imports are read from: write the theory in this call or first")
    imports = theory_imports(source)
    if op["op"] == "root":
        entries = [(i, m.group(2)) for i, m in ((i, ROOT_ENTRY.match(x)) for i, x in enumerate(lines)) if m]
        names = [n for _, n in entries]
        if name in names:
            return text, names.index(name), f"{name} declared already, at line {entries[names.index(name)][0] + 1}"
        if not entries:
            return None, None, "ROOT declares no theory to place it among"
        if op.get("after"):
            if op["after"] not in names:
                return None, None, f"ROOT declares no {op['after']} to place {name} after"
            i = entries[names.index(op["after"])][0]
        else:
            i = max((j for j, n in entries if n in imports), default=entries[-1][0])
        lines.insert(i + 1, f"    {name}")
        return "\n".join(lines), i + 2, f"{name} declared at line {i + 2}"
    rows = [(i, m.group(1)) for i, m in ((i, MAP_ROW.match(x)) for i, x in enumerate(lines)) if m and m.group(1) != "Theory"]
    mine = [i for i, n in rows if n == name]
    if len(mine) > 1:
        return None, None, (f"THEORY_MAP.md holds the row of {name} {len(mine)} times, at lines "
                            f"{', '.join(str(i + 1) for i in mine)}: make it one with a `=== replace` block first")
    content = op["text"]
    if not content:
        if not mine:
            return None, None, f"{name} has no row yet, so its content is to be given: `=== row {name}`, then it"
        m = re.match(r"^\|\s*[^|]*\|[^|]*\|(.*)\|\s*$", lines[mine[0]])
        content = m.group(1).strip() if m else ""
    row = f"| {name} | {', '.join(imports) or 'Main'} | {content} |"
    if mine:
        if op.get("after"):
            return None, None, f"the row of {name} stands already, at line {mine[0] + 1}: `after` places a new row"
        lines[mine[0]] = row
        return "\n".join(lines), mine[0] + 1, f"the row of {name} replaced, at line {mine[0] + 1}"
    if not rows:
        return None, None, "THEORY_MAP.md holds no table row to place the new one among"
    if op.get("after"):  # the map is in sections: beside a row of the writer's choosing
        there = [i for i, n in rows if n == op["after"]]
        if not there:
            return None, None, f"THEORY_MAP.md holds no row of {op['after']} to place the row of {name} after"
        lines.insert(there[0] + 1, row)
        return "\n".join(lines), there[0] + 2, f"the row of {name} written anew, at line {there[0] + 2}"
    root = now.get(change_path(base, "ROOT"))
    if root is None:
        try:
            root = open(change_path(base, "ROOT"), encoding="utf-8", newline="").read()
        except (OSError, UnicodeDecodeError):
            root = ""
    order = [m.group(2) for m in map(ROOT_ENTRY.match, root.split("\n")) if m]
    where = {n: i for i, n in rows}
    before = order[:order.index(name)] if name in order else []
    i = next((where[n] for n in reversed(before) if n in where), rows[-1][0])
    lines.insert(i + 1, row)
    return "\n".join(lines), i + 2, f"the row of {name} written anew, at line {i + 2}"


def changed_texts(ops, base, keyed=None):
    """({path: its text after the changes, and the lines each replacement landed at}, what refuses them): applied in
    order, in memory, each replacement to the file as the changes before it left it. The index edits come after the
    others, declarations (`root`) before rows: each reads its theory as the call leaves it, a row's place is read
    from ROOT as the call leaves it. `keyed` collects what each index edit did, by path."""
    now, at, problems = {}, {}, []
    keyed = {} if keyed is None else keyed
    stage = {"root": 1, "row": 2}
    for op in sorted(ops, key=lambda o: (stage.get(o["op"], 0), o["n"])):
        path = change_path(base, op["path"])
        what = f"change {op['n']} ({op['op']} {op['path'] if op['op'] not in stage else op['theory']})"
        if op["op"] == "write":
            now[path] = op["text"]
            continue
        if op["op"] == "append":
            # a log's next entry at its end — PLANNING_LOG.md was appended to by replacing its last lines, and a text
            # that recurred there refused plan-47's whole change, its mail and HANDOFF.md with it (2026-09-22 21:14)
            if path not in now:
                try:
                    now[path] = open(path, encoding="utf-8", newline="").read() if os.path.exists(path) else ""
                except (OSError, UnicodeDecodeError) as e:
                    problems.append(f"{what}: the file cannot be read ({getattr(e, 'strerror', None) or e})")
                    now[path] = None
            if now[path] is None:
                continue
            gap = "" if not now[path] or now[path].endswith("\n") else "\n"
            at.setdefault(path, []).append(-(now[path].count("\n") + len(gap) + 1))  # negative: an append's first line
            now[path] = now[path] + gap + op["text"]
            continue
        if path not in now:
            try:
                now[path] = open(path, encoding="utf-8", newline="").read()
            except (OSError, UnicodeDecodeError) as e:
                problems.append(f"{what}: the file cannot be read ({getattr(e, 'strerror', None) or e})")
                now[path] = None
        if now[path] is None:
            continue
        if op["op"] in stage:
            try:
                text, line, said = keyed_edit(op, now[path], base, now)
            except Exception as e:  # noqa: BLE001 — refused whole and said, as any change that cannot be made
                text, line, said = None, None, f"it could not be applied ({e!r})"
            if text is None:
                problems.append(f"{what}: {said}")
                continue
            now[path] = text
            keyed.setdefault(path, []).append(said)
            continue
        text, line, problem = replace_one(now[path], op, "file")
        if problem:
            problems.append(problem.replace(f"({op['op']} file)", f"({op['op']} {op['path']})", 1))
            continue
        now[path] = text
        at.setdefault(path, []).append(line)
    return now, at, problems


# A session reads the library in glyphs (⇒, ∀, ‹›: the digests show them so), and a theory is written in Isabelle's
# escapes (\<Rightarrow>): fix-249 wrote its theory in glyphs and then a script of its own to turn them into escapes,
# a request spent on it (2026-09-22). A change writes the glyphs of what it writes into a theory as their escapes,
# by Isabelle's own table; what the file already holds is as it was.
SYMBOLS = os.environ.get("ISABELLE_SYMBOLS", "/opt/isabelle/etc/symbols")
_ESCAPES = {}


def escapes():
    if not _ESCAPES:
        with contextlib.suppress(OSError):
            for line in open(SYMBOLS, errors="ignore"):
                m = re.match(r"^(\\<[^>\s]+>)\s+code:\s*0x([0-9a-fA-F]+)", line)
                if m:
                    _ESCAPES.setdefault(chr(int(m.group(2), 16)), m.group(1))
    return _ESCAPES


def escaped(text):
    """(the text with each glyph Isabelle's table names written as its escape, how many were)."""
    table, n, out = escapes(), 0, []
    for ch in text:
        e = table.get(ch) if ord(ch) > 127 else None
        n += e is not None
        out.append(e or ch)
    return "".join(out), n


def cmd_change(text, base=None):
    """Change files: any number of whole-file writes and exact replacements, in one call, judged whole and written all
    or none. What refuses it is said, change by change; nothing is written then."""
    ops, problems = change_blocks(text)
    if problems:
        return "refused, and nothing was changed:\n- " + "\n- ".join(problems)
    glyphs = 0
    for op in ops:
        if op["path"].endswith(".thy"):
            for key in ("text", "old", "new"):
                if isinstance(op.get(key), str):
                    op[key], n = escaped(op[key])
                    glyphs += n
    base = base or os.getcwd()
    keyed = {}
    now, at, problems = changed_texts(ops, base, keyed)
    if problems:
        return "refused, and nothing was changed:\n- " + "\n- ".join(problems)
    kept = {}
    try:
        for path, new in now.items():
            was = open(path, "rb").read() if os.path.exists(path) else None
            if was is not None and was == new.encode("utf-8"):
                continue
            kept[path] = was
            os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
            tmp = f"{path}.change-{os.getpid()}"
            with open(tmp, "w", encoding="utf-8", newline="") as f:
                f.write(new)
            if was is not None:
                shutil.copymode(path, tmp)
            os.replace(tmp, path)
    except OSError as err:  # a failure part way puts back what was written: the change is all or none
        for path, was in kept.items():
            with contextlib.suppress(OSError):  # the one not yet in place; once in place it is gone, and said so
                os.remove(f"{path}.change-{os.getpid()}")
            with contextlib.suppress(OSError):
                if was is None:
                    os.remove(path)
                else:
                    open(path, "wb").write(was)
        return f"refused: the change could not be written ({err!r}); what it had written is put back"
    written, said = {change_path(base, op["path"]) for op in ops if op["op"] == "write"}, []
    for path in now:
        parts = ["written anew" if kept.get(path, b"") is None else "written"] if path in written else []
        replaced, appended = [x for x in at.get(path, []) if x > 0], [-x for x in at.get(path, []) if x < 0]
        if replaced:
            parts.append(f"{len(replaced)} replaced, at line{'s' * (len(replaced) > 1)} {', '.join(map(str, replaced))}")
        if appended:
            parts.append(f"appended at line{'s' * (len(appended) > 1)} {', '.join(map(str, appended))}")
        parts += keyed.get(path, [])
        if path not in kept:
            parts.append("as it was")
        said.append(f"{os.path.relpath(path, base)} ({', '.join(parts)})")
    # said of an edit of the repository's files, not of a session's own record under .build/ — a verdict, a result, a
    # note, a measurement — which it writes when it is ready and alone: fifteen times in the last session of each role
    # of 2026-09-22, and never followed by a change it could have joined
    note = ("\n[one change in this call. When several are ready — in this file or in others — make them in one call: "
            "it takes any number of changes, written all or none.]"
            if len(ops) == 1 and not os.path.normpath(ops[0]["path"]).startswith(".build") else "")
    if glyphs:
        note += (f"\n[{glyphs} glyph{'s' * (glyphs > 1)} written into a theory as {'their' if glyphs > 1 else 'its'} "
                 "escape (⇒ as \\<Rightarrow>), as Isabelle reads a theory]")
    lap("the change written")
    found = softly("what the sources say after the change", sources_said, base, ops, kept, default=[])
    lap("what the sources say")
    if found:
        note += "\n[the sources, as this change leaves them:\n- " + "\n- ".join(found) + "]"
    return f"changed: {'; '.join(said)}" + note


def import_graph(top, roots):
    """What the repository's own import graph says of the theories `roots` reach, in the tree at `top`: a cycle, or a
    theory imported that is not there (tools/execution_support.source_graph, the tree's own, in a process of its own;
    seconds, no Isabelle). The planner's standing last step before every hand-over ran it with the source checks by
    hand (HANDOFF.md's working rules; 68 requests of implementers and fixers on 2026-09-21/22 did nothing else);
    told with the change that writes a theory, it needs no request. [] where the tree has no such tool."""
    if not roots or not os.path.isfile(os.path.join(top, "tools", "execution_support.py")):
        return []
    code = ("import sys; sys.path.insert(0, 'tools'); from pathlib import Path; import execution_support as e\n"
            "try:\n    e.source_graph(Path('.').resolve(), [], sys.argv[1:])\nexcept Exception as x:\n    print(x)")
    try:
        said = subprocess.run([sys.executable, "-B", "-c", code, *roots], cwd=top, capture_output=True, text=True,
                              timeout=60).stdout.strip()
    except (OSError, subprocess.SubprocessError) as e:
        return [f"the import graph could not be read ({e!r})"]
    return [f"the import graph: {line}" for line in said.splitlines()[:3] if line.strip()]


def softly(what, fn, *args, default=None):
    """What an information-giving part returns, or a note saying it could not be had: what the harness tells a session
    beside its work — the sources after a change, the restatements, a task's tree, a brief's statements, the
    handoff's delta — never breaks the change, the read or the launch it rides on (a launch failed on one on 2026-09-23
    before its test: a task in the one tree has no tree of its own)."""
    try:
        return fn(*args)
    except Exception as e:  # noqa: BLE001 — told, and logged, whatever it was
        log(f"ATTENTION {what} could not be had: {e!r}")
        return default if default is not None else f"({what} could not be had: {e!r})"


ESCAPE = re.compile(r"\b(sorry|oops|axiomatization)\b")
BACKTICKED = re.compile(r"`([A-Za-z][\w']*)`")
DUPLICATE_NAME = 8     # a name as specific as this (and with an underscore) declared elsewhere is worth a look
DUPLICATE_STATED = 30  # a statement as long as this stated elsewhere, word for word


def library_index(theories):
    """({name: the theories declaring it}, {a statement, its spaces made one: (theory, fact)...}) over every theory; a
    definition's body, its arguments by position, stands among the statements as `definition BODY`."""
    from digest import DECLARED, STATED, definition_bodies
    names, stated = {}, {}
    for path in glob.glob(os.path.join(theories, "*.thy")):
        theory = os.path.basename(path)[:-4]
        try:
            text = open(path, errors="ignore").read()
        except OSError:
            continue
        for n in set(DECLARED.findall(text)):
            names.setdefault(n, set()).add(theory)
        for n, statement in STATED.findall(text):
            stated.setdefault(" ".join(statement.strip('"').split()), set()).add((theory, n))
        for n, body in definition_bodies(text):
            stated.setdefault("definition " + body, set()).add((theory, n))
    return names, stated


def tree_state_text(tid, tree):
    """Where a task's work stands in git, as its reviewer and its session read it by hand (the reviewers and producers
    of 2026-09-21/22 ran about 700 git status, diff, show, log and merge-base calls): its tree and branch, where the
    branch left main, its own commits past that, main's commits since then that touch the files it hands over, and
    what stands uncommitted or new in the tree."""
    one = tree == PROJECT
    base = "HEAD" if one else (git_out("merge-base", "HEAD", "main", tree=tree, quiet=True) or "").strip()
    try:
        files = json.load(open(os.path.join(BUILD, str(tid), "finalize.json")))["files"]
    except (OSError, ValueError, KeyError, TypeError):
        files = []
    lines = [f"tree: {'the one tree' if one else os.path.relpath(tree, PROJECT)}"
             + ("" if one else f", branch {(git_out('rev-parse', '--abbrev-ref', 'HEAD', tree=tree, quiet=True) or '?').strip()}"
                               f", left main at {base[:8] or '?'}")]
    if not one and base:
        own = (git_out("log", "--oneline", f"{base}..HEAD", tree=tree, quiet=True) or "").strip()
        lines.append("its commits past main: " + ("; ".join(own.splitlines()[:8]) or "none"))
        since = (git_out("log", "--oneline", f"{base}..main", "--", *files, tree=tree, quiet=True) or "").strip() \
            if files else ""
        lines.append("main's commits since then touching the files it hands over: "
                     + ("; ".join(since.splitlines()[:8]) or "none"))
    status = [p for p in (git_out("status", "--short", "--untracked-files=all", tree=tree, quiet=True) or "").splitlines()
              if not sandbox_mount(tree, p[3:]) and not exempt(p[3:])]
    if one:  # the one tree holds other tasks' work too: this task's own, as the guard recorded who wrote each path
        with owners(write=False) as o:
            mine = {p for p, t in o.items() if t == str(tid)} | set(files)
        status = [p for p in status if p[3:] in mine]
    lines.append("uncommitted or new: " + (", ".join(status[:30]) + (f", and {len(status) - 30} more" if len(status) > 30
                                                                      else "") if status else "nothing"))
    return "\n".join(lines)


def restated_text(tid, tree):
    """What the theories a task changed declare anew that the library has, and what their rows offer that the task
    took out (restated), over the whole change — from where its branch left main (the task's own tree), or from HEAD
    (the one tree). The session was told each as it wrote it; its reviewer reads them together, as `v2.py read
    restated` and in its first read: duplication was the commonest blocking finding (14 of the 31 rejections whose
    findings the state held on 2026-09-23), and 23 of the 51 planned fixes from #100 on consolidated what was
    stated twice."""
    base = (git_out("merge-base", "HEAD", "main", tree=tree, quiet=True) or "").strip() if tree != PROJECT else "HEAD"
    base = base or "HEAD"
    changed = [p for p in (git_out("diff", "--name-only", base, "--", "theories/", tree=tree, quiet=True) or "").split()
               + (git_out("ls-files", "--others", "--exclude-standard", "--", "theories/", tree=tree, quiet=True) or "").split()
               if p.endswith(".thy") and os.path.dirname(p) == "theories"]
    rows = {}
    with contextlib.suppress(OSError):
        for line in open(os.path.join(tree, "THEORY_MAP.md"), errors="ignore"):
            m = MAP_ROW.match(line)
            if m and m.group(1) != "Theory":
                rows.setdefault(m.group(1), []).append(line.rstrip("\n"))
    out, library = [], {}
    for p in sorted(dict.fromkeys(changed)):
        name, full = os.path.basename(p)[:-4], os.path.join(tree, p)
        if not os.path.isfile(full):
            continue
        old = git_out("show", f"{base}:{p}", tree=tree, quiet=True) or ""
        out += restated(name, old, open(full, errors="ignore").read(), os.path.join(tree, "theories"), library,
                        rows.get(name, []))
    return ("\n".join(f"- {x}" for x in out) if out else
            "(the theories the task changed declare nothing anew that the library has — by a specific name, a "
            "statement word for word or a definition's body — and their rows offer nothing the task took out)")


def decisions_citing(names, path, theory):
    """The entries of DECISIONS.md that cite, in backticks, a name a change took out of a theory: an entry stating what
    the work no longer has — task 275's review found its law entry stating the opposite of the delivered work, and
    task 30's an entry silent on what it retired (2026-09-22). Specific names only (at least 8 characters, with an
    underscore); the entries by their headings."""
    names = {n for n in names if len(n) >= DUPLICATE_NAME and "_" in n}
    if not names or not os.path.isfile(path):
        return []
    heading, cited = "", {}
    for line in open(path, errors="ignore"):
        if line.startswith("#"):
            heading = line.strip("# \n")[:80]
            continue
        for n in set(BACKTICKED.findall(line)) & names:
            cited.setdefault(n, []).append(heading)
    return [f"DECISIONS.md cites `{n}`, which this change took out of {theory}, in "
            + "; ".join(f'"{h}"' for h in dict.fromkeys(hs)) for n, hs in sorted(cited.items())][:4]


REMOVAL = re.compile(r"\b(?:remov|replac|supersed|retir|drop|withdr|mov|no longer|gone|former|instead of|was\b|were\b)",
                     re.I)


def removal_note(text, name):
    """Whether a row mentions a name in a note of its removal or replacement: the clause it stands in (to the nearest
    full stop, semicolon or cell border either side) says so."""
    at = text.find(f"`{name}`")
    if at < 0:
        return False
    start = max(text.rfind(c, 0, at) for c in ".;|") + 1
    ends = [i for i in (text.find(c, at + len(name) + 2) for c in ".;|") if i >= 0]
    return bool(REMOVAL.search(text[start:min(ends) if ends else len(text)]))


def restated(name, old, new, theories, library, row):
    """What a change to a theory is told of what it declares anew and of what it takes out: a name, specific enough to
    mean one thing, that another theory declares too; a statement another theory states word for word; and a name its
    THEORY_MAP.md row still offers that the change took out. Of the 31 rejections whose findings the state holds on
    2026-09-23, 14 were a notion or fact the library already had, re-derived or restated (`path_term_inj` stated
    again under its own name, `syntax_branch_eq_iff` three times, `map_filter_member` twice), and three a row offering
    what the task had removed. A hint, not a refusal: two theories may rightly use one name in their own locales."""
    from digest import DECLARED, STATED, definition_bodies
    before, after = set(DECLARED.findall(old)), set(DECLARED.findall(new))
    out, taken = [], before - after
    if taken:
        # a name gone from its theory and declared in another has moved, and a mention of it is a citation of its new
        # home ("over Development_State_Rows's `state_all_families`"); nor is a note of its removal an offer ("the
        # superseded `…` is removed"): of the 15 mentions the rows of 68 landed changes of 09-21/22 kept of names
        # their change took out, most were the one or the other
        if not library:
            library["names"], library["stated"] = library_index(theories)
        taken = {n for n in taken if not (library["names"].get(n, set()) - {name})}
    gone = sorted(n for n in set(BACKTICKED.findall(row[0])) & taken if not removal_note(row[0], n)) if len(row) == 1 else []
    if gone:
        out.append(f"the row of {name} offers {', '.join('`' + n + '`' for n in gone[:5])}, which this change took "
                   f"out of {name}")
    out += decisions_citing(taken, os.path.join(os.path.dirname(theories), "DECISIONS.md"), name)
    added = [n for n in after - before if len(n) >= DUPLICATE_NAME and "_" in n]
    old_stated = {" ".join(st.strip('"').split()) for _, st in STATED.findall(old)} | \
        {"definition " + b for _, b in definition_bodies(old)}
    fresh = [(n, " ".join(st.strip('"').split())) for n, st in STATED.findall(new)] + \
        [(n, "definition " + b) for n, b in definition_bodies(new)]
    fresh = [(n, st) for n, st in fresh if len(st) >= DUPLICATE_STATED and st not in old_stated]
    if not (added or fresh):
        return out
    if not library:
        library["names"], library["stated"] = library_index(theories)
    for n in sorted(added):
        others = sorted(library["names"].get(n, set()) - {name})
        if 0 < len(others) <= 2:
            out.append(f"`{n}`, new in {name}, is declared in {' and '.join(others)} too: the same notion or fact, "
                       "to reuse, or one to name for what differs?")
    for n, st in fresh:
        others = sorted((t, f) for t, f in library["stated"].get(st, set()) if t != name)
        if others:
            out.append(f"`{n}` defines what {others[0][0]}.{others[0][1]} defines, its arguments aside"
                       if st.startswith("definition ") else
                       f"`{n}` states what {others[0][0]}.{others[0][1]} states, word for word")
    return out[:8]


def sources_said(base, ops, kept):
    """What the structural checks say, once a change is written, of the theories it concerns — those it wrote anew,
    whose imports or proofs it changed, whose row or declaration it edited, and those ROOT gained or lost by it: a
    theory present and not declared, a declaration without its file, a proof escaped, a theory without its row, a row
    whose imports are not its theory's. These are the items the finalizer's documents check and the repository's
    source checks refuse on (finalize.documents_check, check.source_checks), told when they arise: 68 requests of the
    implementers and fixers of 2026-09-21/22 ran the source checks by hand, and a missing declaration was found at the
    hand-over. `kept`: each changed file's bytes before the change (None: it is new). Nothing is said of a change
    outside a tree's top (ROOT and theories/ there), nor of what it left as it was."""
    root_path, map_path = change_path(base, "ROOT"), change_path(base, "THEORY_MAP.md")
    theories = change_path(base, "theories")
    if not (os.path.isfile(root_path) and os.path.isdir(theories)):
        return []
    read = lambda path: open(path, encoding="utf-8", errors="ignore").read() if os.path.isfile(path) else None
    was = lambda path: kept[path].decode("utf-8", "ignore") if kept.get(path) is not None else None
    declared = [m.group(2) for m in map(ROOT_ENTRY.match, (read(root_path) or "").split("\n")) if m]
    concerned, out = {}, []
    for op in ops:
        if op["op"] in ("row", "root"):
            concerned.setdefault(op["theory"], set()).update({"declared", "row"})
            continue
        path = change_path(base, op["path"])
        if os.path.dirname(path) == theories and path.endswith(".thy") and path in kept:
            name, old, new = os.path.basename(path)[:-4], was(path), read(path)
            wants = concerned.setdefault(name, set())
            wants.add("escapes")
            if old is None:
                wants.update({"declared", "row"})
            elif new is not None and theory_imports(old) != theory_imports(new):
                wants.add("row")
    if root_path in kept:
        before = [m.group(2) for m in map(ROOT_ENTRY.match, (was(root_path) or "").split("\n")) if m]
        for name in set(declared) ^ set(before):
            concerned.setdefault(name, set()).add("declared")
    rows = {}
    for line in (read(map_path) or "").split("\n"):
        m = MAP_ROW.match(line)
        if m and m.group(1) != "Theory":
            rows.setdefault(m.group(1), []).append(line)
    library = {}  # read once, when a theory written here declares or states something it did not before
    written = [n for n in sorted(concerned) if "escapes" in concerned[n] and os.path.isfile(os.path.join(theories, f"{n}.thy"))]
    out += import_graph(os.path.dirname(theories), written)
    for name in sorted(concerned):
        path = os.path.join(theories, f"{name}.thy")
        text, wants = read(path), concerned[name]
        if "declared" in wants:
            if text is not None and name not in declared:
                out.append(f"theories/{name}.thy is not declared in ROOT (`=== root {name}`)")
            elif text is None and name in declared:
                out.append(f"ROOT declares {name}, and theories/{name}.thy is not there")
        if text is None:
            continue
        if "escapes" in wants:
            old = was(path) or ""
            new = [(n, x.strip()) for n, x in enumerate(text.split("\n"), 1) if ESCAPE.search(x)]
            if len(new) > len([x for x in old.split("\n") if ESCAPE.search(x)]):
                out += [f"theories/{name}.thy:{n} escapes its proof: {x[:80]}" for n, x in new[:3]]
            out += restated(name, old, text, theories, library, rows.get(name, []))
        if "row" in wants and os.path.isfile(map_path):
            mine = rows.get(name, [])
            if not mine:
                out.append(f"{name} has no row in THEORY_MAP.md (`=== row {name}`, then what it offers for reuse)")
            elif len(mine) > 1:
                out.append(f"THEORY_MAP.md holds the row of {name} {len(mine)} times")
            else:
                m = re.match(r"^\|\s*[^|]*\|([^|]*)\|", mine[0])
                named = [x.strip() for x in (m.group(1) if m else "").split(",") if x.strip()]
                imports = theory_imports(text) or ["Main"]
                if named != imports:
                    out.append(f"the row of {name} names the imports {', '.join(named) or '(none)'}, and the theory "
                               f"imports {', '.join(imports)} (`=== row {name}` alone reads them again)")
    return out


def link_reviews():
    """A review task names the task it reviews on its `Reviews:` line, and a review is started for a task in review
    from that task's `review_tasks`. Only `accept` wrote the relation, so a review task the planner wrote itself was
    never linked: the harness planned a review of its own for the build, and the planner's stood ready for ever
    (found 2026-09-21). Every dispatch links what the list says."""
    st, missing = peek(), []
    for t in all_tasks():
        if t.get("status") == "completed" or brief_kind(t.get("description") or "") != "review":
            continue
        x = reviewed(t.get("description") or "")
        if not x or not in_list(x):
            continue
        if (st["tasks"].get(t["id"]) or {}).get("reviews") != x \
                or t["id"] not in ((st["tasks"].get(x) or {}).get("review_tasks") or []):
            missing.append((t["id"], x))
    if missing:
        with state() as w:
            for r, x in missing:
                w["tasks"].setdefault(r, {})["reviews"] = x
                linked = w["tasks"].setdefault(x, {}).setdefault("review_tasks", [])
                if r not in linked:
                    linked.append(r)
        log("review tasks linked to what they review: " + ", ".join(f"{r} -> {x}" for r, x in missing))


def cmd_accept(bid):
    """The planner writes a brief's proposed tasks into the graph, as proposed."""
    refused = planner_only("placing a brief's tasks")
    if refused:
        return refused
    rec = peek()["tasks"].get(bid) or {}
    if rec.get("stage") != "proposed" or not rec.get("proposal"):
        return f"refused: brief task {bid} has no proposal waiting"
    if rec.get("revise"):
        return (f"refused: brief task {bid}'s proposal went back to its task designer with your correction; it "
                "proposes again, and you are told")
    try:
        entries = json.load(open(os.path.join(PROJECT, rec["proposal"])))
        assert isinstance(entries, list) and entries
    except (OSError, ValueError, AssertionError) as e:
        return f"refused: {rec['proposal']} cannot be read as a proposal ({e!r}); ask its task designer, or drop it"
    problems = proposal_problems(entries)  # the graph may have moved since it proposed
    problems += [f"task {n[1:]} would now be added after a chain {d} deep, above {GRAPH_DEPTH}"
                 for n, d in past_the_limit(*graph_after(bid, entries))]
    if problems:
        return ("refused: the proposal no longer fits the graph:\n- " + "\n- ".join(problems)
                + f"\nTell the task designer (`v2.py tell {bid} ...`) or re-plan the brief.")
    ops = [{"create": e["key"], "subject": e["subject"], "description": e["description"], "why": e.get("why", ""),
            "blockedBy": e.get("blockedBy") or [], "feeds": e.get("feeds") or [], "instead": bid} for e in entries]
    try:
        ids = apply_graph_edit(ops)
    except GraphEditFailed as err:
        return (f"refused: the proposal could not be placed ({err.cause!r}); the {err.written} task(s) written before "
                "it failed are taken back, so nothing is half in the graph. The proposal stands where it is.")
    order = [ids[e["key"]] for e in entries]
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
        early = review_beside_check() and t.get("stage") == "checking" and t.get("kind", "build") in ("build", "fix")
        if t.get("stage") != "reviewing" and not early:
            return f"refused: task {tid} is not awaiting a verdict (it is {t.get('stage')})"
        said = dict(verdict=verdict, findings=part(text, "Findings"), summary=part(text, "Summary"),
                    followups=part(text, "Follow-ups"), reviewing=None, verdict_file=path,
                    **({"corrected": part(text, "Corrected")} if part(text, "Corrected") else {}))
        r.update(said)
        if t is not r and t.get("kind", "build") not in ("build", "fix"):
            t.update(said)  # the planner's verdict on a design, given on a review task of it, is the design's
        if c and c["role"] == "reviewer":
            st["sessions"][c["name"]].update(state="done", ended=time.time())
        rids, linked = deciding(t, tid, st), held_reviews(t)
        judged = [st["tasks"].get(x) or {} for x in rids]
        waiting = any(j.get("verdict") is None or j.get("reviewing") for j in judged)
        if not waiting:
            t["reviewing"] = None
        follow = "; ".join(j["followups"] for j in judged if j.get("followups"))
        if waiting:
            pass
        elif all(j["verdict"] == "accept" for j in judged):
            fixed = "; ".join(j["corrected"] for j in judged if j.get("corrected"))
            t["summary"] = " ".join(first_sentence(j.get("summary", "")) + (f" (review: {j['verdict_file']})"
                                                                              if j.get("verdict_file") else "")
                                    for j in judged) + (f" Corrected by its review: {fixed}" if fixed else "") \
                + (f" Follow-ups proposed: {follow}" if follow else "")
            for x in dict.fromkeys(rids + linked):
                if x != tid:
                    st["tasks"].setdefault(x, {})["stage"] = "done"
            if early:  # C9: the accept stands once the check passes (checked), and is void if it fails
                t["accepted_early"] = True
            elif os.path.exists(os.path.join(BUILD, tid, "finalize.json")):
                t["stage"], commit = "committing", True
            else:
                t["stage"] = "done"
                event(st, by, f"Task {tid} is accepted (nothing to commit). {t['summary']}")
        else:
            findings = "\n".join(f"From {x} ({(st['tasks'].get(x) or {}).get('verdict_file')}):\n{j['findings']}"
                                 for x, j in zip(rids, judged) if j["verdict"] == "reject")
            if early and t.get("rejections", 0) == 0:  # C9: its fix waits for the check's end, which may add its failure
                t["rejected_early"] = f"The review of task {tid} rejected it. Its blocking findings, all of them:\n{findings}"
                findings = None
            else:
                t["rejections"] = t.get("rejections", 0) + 1
                t["rejected_at"] = time.time()  # what a role's reasoning layer is built again for (role_layer_new)
            if findings is None:
                pass
            elif t["rejections"] == 1:
                t.update(stage="fixing", fixing=None, fix_text=f"The review of task {tid} rejected it. Its blocking "
                         f"findings, all of them:\n{findings}")
            else:
                to_planner(st, tid, by, f"Task {tid} was rejected again after its fix round; it is yours to decide "
                           f"(accept with follow-ups, a fixer's task, or re-planning). The findings:\n{findings}"
                           + (f"\nFollow-ups proposed: {follow}" if follow else ""))
    if c and c["role"] == "reviewer":
        turn_over(c)
    if waiting:
        kick()
        return f"{verdict}ed task {tid} for review {rid}; its other reviews are pending" + (
            ". End your turn now." if c and c["role"] == "reviewer" else "")
    if t.get("stage") == "done":  # accepted with nothing to commit: the task and its reviews are completed
        for x in dict.fromkeys([tid, *rids, *linked]):
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
    recommit, held = [], len(peek()["queue"])
    with state() as st:
        for tid in ids:
            t = st["tasks"].get(tid) or {}
            if t.get("lands_again") and t.get("stage") == "planner" and review_accepted(st, tid):
                # accepted, and kept out of main only by the one tree's uncommitted changes past its commit's budget
                # (finalize.standing_refused): its commit is made again with no session, and waits for them anew. A
                # new session would find nothing to do, and its check and review would judge the same work again.
                st["tasks"][tid] = {k: v for k, v in t.items() if k not in ("lands_again", "lands_again_why",
                                                                            "finishing_since")}
                st["tasks"][tid]["stage"] = "committing"
                recommit.append(tid)
                continue
            # `done` is terminal bookkeeping and task_state never reads it again, deliberately: between a verdict
            # accepting a task and the planner completing it in the list, re-reading would start the work a second
            # time. But a task the planner has put BACK to pending and then named in its order is one it means to
            # run, and nothing would ever start it again — it would sit in the queue, not startable, unnamed by
            # anything (2026-09-21). The list decides: only a task the list no longer calls completed is re-read.
            # A review that has given its verdict is done here and completed in the list only when the task it reviews
            # commits (committed): named in the order meanwhile it is no reopened task. Read as one, its entry was
            # reset and its verdict lost, so the task it had accepted read as unreviewed — task 32, kept out of main
            # by task 62's uncommitted lines and queued to land again, was started afresh instead, its check and
            # review run a second time on accepted work, and task 76 with it (2026-09-22 02:58).
            awaiting = bool(t.get("verdict")) and (st["tasks"].get(t.get("reviews") or "") or {}).get("stage") not in (
                "done", "deleted", None)
            reopened = t.get("stage") == "done" and not awaiting and (read_task(tid) or {}).get("status") not in (
                "completed", None)
            if t.get("stage") in ("planner", "unformed") or reopened:  # re-planned: its stage is read afresh
                # and its review history kept: `rejections` pairs with its review tasks' rounds (pending_reviews), and
                # dropped it read 0 against a review of round 0 — task 46, rejected, re-planned and checked again, had
                # its re-review taken for done, and nine tasks stood parked behind it (2026-09-21)
                st["tasks"][tid] = {k: v for k, v in t.items()
                                    if k in ("briefed_by", "briefing", "review_tasks", "reviews", "rejections", "told",
                                             "back", "previous_session", "previous_reviewer", "brief_sha")}
                if t.get("session"):  # who worked on it last, resumed when it is started again (reusable)
                    st["tasks"][tid]["previous_session"] = t["session"]
                if accepted_by(t):  # who accepted it, resumed for its review when it is judged again (start_review)
                    st["tasks"][tid]["previous_reviewer"] = accepted_by(t)
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
    # said, so that an order is traced to who set it: at 20:01 on 2026-09-22 the queue held task 267 alone, 59 tasks
    # ready, where plan-46's last edit had queued 68 at 19:41, and nothing in the log said how
    log(f"the order is set by {(c or {}).get('name') or 'the owner'}: {len(order)} task(s), where it held {held}")
    if graph_held():  # the planner has said what the order is: the graph it inherited is now the graph it chose
        with contextlib.suppress(OSError):
            os.remove(os.path.join(STATE, GRAPH_HELD))
        log("the graph is released: the planner has queued")
        kick()
    for tid in recommit:
        log(f"task {tid}: its commit is made again, as it stands")
        background("finalize.py", "commit", tid)
    kick()
    return ("queued" + (f"; kept, briefed since this episode began: {', '.join(kept)}" if kept else "")
            + (f"; {', '.join(recommit)}: its commit is made again, with no session" if recommit else ""))


def cmd_ledger(text):
    """The planner's question to the owner, with the choice it works under meanwhile and its basis: appended under
    "Open questions to the owner" in the owner ledger, numbered and dated. The ledger is the harness's file, which no
    session writes by hand (work_meter.write_guard), and the planner is told to put the owner's questions there: until
    this, it could not (found 2026-09-21, in the pass over what the restrictions left undoable)."""
    refused = planner_only("a question in the owner ledger")
    if refused:
        return refused
    if not text.strip():
        return "refused: name the question, the choice you work under meanwhile, and its basis"
    asker = (caller() or {}).get("name", "the owner")
    with open(LEDGER + ".lock", "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            s = open(LEDGER).read()
        except OSError as e:
            return f"refused: the owner ledger cannot be read ({e.strerror}); nothing is written"
        n = 1 + max((int(x) for x in re.findall(r"^\*\*Q(\d+)\b", s, re.M)), default=0)
        entry = f"**Q{n} (asked {time.strftime('%Y-%m-%d')} by {asker})** — {text.strip()}\n\n"
        at = s.find("## Open questions to the owner")
        end = s.find("\n## ", at + 1) if at >= 0 else -1
        s = (s.rstrip("\n") + "\n\n" + ("" if at >= 0 else "## Open questions to the owner\n\n") + entry if end < 0
             else s[:end + 1] + entry + s[end + 1:])
        open(LEDGER + ".tmp", "w").write(s)
        os.replace(LEDGER + ".tmp", LEDGER)
    log(f"{asker} put Q{n} to the owner in the ledger")
    return f"recorded as Q{n} under \"Open questions to the owner\"; work under the choice until the owner answers"


FOLLOW_MARK = "<<PLANNER"  # a part of a follow-up's draft brief that is the planner's to write (C15)


def follow_items(text):
    """{number: text} of a verdict's `## Follow-ups`, each item whole as its review wrote it: the top-level numbered
    items by their numbers, or else the top-level bullets numbered in order (review-251's were bullets)."""
    body = part(text, "Follow-ups")
    for pattern, numbered in ((r"^(\d+)[.)]\s", True), (r"^[-*]\s", False)):
        starts = list(re.finditer(pattern, body, re.M))
        if starts:
            return {(m.group(1) if numbered else str(i + 1)):
                    body[m.start():starts[i + 1].start() if i + 1 < len(starts) else len(body)].rstrip()
                    for i, m in enumerate(starts)}
    return {}


def verdict_file_of(st, tid):
    """The verdict of task tid's last review that has one (its path from the repository), or None."""
    t = st["tasks"].get(tid) or {}
    files = [x.get("verdict_file") for k, x in st["tasks"].items() if k != tid and x.get("reviews") == tid]
    files += [t.get("verdict_file"), f".build/tasks/{tid}/review.md"]
    return next((f for f in files if f and os.path.isfile(os.path.join(PROJECT, f))), None)


def follow_names(text, tree):
    """The files, theories and facts a follow-up names, as it names them, in order: its backticked names, and the
    theories it names bare (`Native_Table_Reach`, lines 360–370) that the tree holds."""
    out = [n for n in names_in(text) if "_" in n or "." in n or "/" in n]  # `exact`, `obtain`: words, not names
    for w in re.findall(r"\b[A-Z][A-Za-z0-9]*(?:_[A-Za-z0-9]+)+\b", text):
        if w not in out and f"{w}.thy" not in out and os.path.isfile(os.path.join(tree, "theories", w + ".thy")):
            out.append(w)
    return out


def cmd_follow_up(args, kind="fix"):
    """C15 (the owner's yes of 2026-09-23, "if it can be done in a way where information quality stays the same or
    increases"): a draft brief for a task made of reviews' follow-ups, under the planner's drafts. What the harness
    writes is copied: the follow-ups verbatim, where they are, the names they give exactly as they give them; what is
    judged — why now, what it delivers and how it is accepted beyond the check, what is decided, the plan, its size —
    is marked for the planner, and a brief with a mark left is refused. The planner's graph edits took 1.5M output
    tokens and 3.6 hours of its model time over 09-21/22, most of it such briefs, each restating its follow-ups from
    the review in its own words — which the task's session then read against the review again.
    `args`: `TASK:ITEM,ITEM` groups, or a task and its items bare (`272 1 3`)."""
    refused = planner_only("drafting a brief")
    if refused:
        return refused
    if kind not in PRODUCING_KINDS:
        return f"refused: a follow-up's task is one of {', '.join(PRODUCING_KINDS)}, not {kind}"
    wanted, cur = {}, None
    for a in args:
        task, _, items = a.partition(":") if ":" in a else ((None, None, a) if cur else (a, None, ""))
        if task is not None:
            cur = task.lstrip("#")
            wanted.setdefault(cur, [])
        wanted[cur] += [i.strip() for i in items.split(",") if i.strip()]
    if not wanted or not all(wanted.values()):
        return "refused: v2.py follow-up TASK:ITEM[,ITEM]... (or TASK ITEM...) — which follow-ups of which review"
    st = peek()
    c = caller()
    tree = tree_of(c) if c else PROJECT
    serves, inputs, copied, names = [], [], [], []
    for tid, items in wanted.items():
        path = verdict_file_of(st, tid)
        if not path:
            return f"refused: task {tid} has no review with a verdict file"
        found = follow_items(open(os.path.join(PROJECT, path), errors="ignore").read())
        missing = [i for i in items if i not in found]
        if missing:
            return (f"refused: {path} has no follow-up {', '.join(missing)} (its follow-ups: "
                    f"{', '.join(found) or 'none'})")
        which = f"follow-up{'s' if len(items) > 1 else ''} {', '.join(items)}"
        serves.append(f"#{tid}'s review (`{path}`, {which})")
        inputs.append(f"`{path}` ({which})")
        for i in items:
            # quoted, so that a line of it that reads like a field of the form (`Plan: …`) is not taken for one
            copied.append(f"From `{path}`, follow-up {i}:\n" + "\n".join(f"> {line}".rstrip() for line in found[i].split("\n")))
            names += [n for n in follow_names(found[i], tree) if n not in names]
    theories = [n for n in names if os.path.isfile(os.path.join(tree, "theories", re.sub(r"\.thy$", "", n.split("/")[-1]) + ".thy"))]
    draft = "\n".join([
        f"Kind: {kind}",
        f"Serves: {'; '.join(serves)}. {FOLLOW_MARK}: why now — what it serves beyond the review, what waits on it>>",
        f"Deliverable: {FOLLOW_MARK}: the files it changes, in backticks"
        + (f" (the follow-ups name {', '.join(f'`{n}`' for n in theories)})" if theories else "")
        + ">>, `.build/tasks/<its id>/commit.md`",
        f"Acceptance: the repository's check; {FOLLOW_MARK}: what shows each follow-up done>>",
        "Inputs: " + "; ".join(inputs) + (f"; what the follow-ups name: {', '.join(f'`{n}`' for n in names)}"
                                         if names else "") + f". {FOLLOW_MARK}: what else it reads, or nothing>>",
        f"Decided: {FOLLOW_MARK}: what you decide of it, or that nothing is>>",
        f"Plan: {FOLLOW_MARK}: its logical course, at least two numbered steps>>",
        f"Size: {FOLLOW_MARK}: about NK tokens of work>>",
        "From the review:",
        *copied, ""])
    key = "-".join(f"{tid}-{'.'.join(items)}" for tid, items in wanted.items())
    rel = os.path.join(".build", "plans", (c or {}).get("name") or "owner", f"follow-{key}.md")
    os.makedirs(os.path.dirname(os.path.join(PROJECT, rel)), exist_ok=True)
    with open(os.path.join(PROJECT, rel), "w") as f:
        f.write(draft)
    source = next(iter(wanted)) if len(wanted) == 1 else None
    op = {"create": f"f{key.split('-')[0]}", "subject": f"{FOLLOW_MARK}: its subject>>", "descriptionFile": rel,
          "why": f"{FOLLOW_MARK}: why>>", **({"continues": source} if source and continue_by_fork() else {})}
    marks = draft.count(FOLLOW_MARK)
    return (f"drafted {rel}: the follow-ups verbatim under `From the review:`, the review and the {len(names)} names "
            f"they give among its Inputs, and {marks} parts marked `{FOLLOW_MARK}: …>>` for you — read what the "
            "follow-ups name as for any brief, write each mark as the brief's own words (replace them in one "
            "`v2.py change`), and place it by `v2.py edit`, for example " + json.dumps(op, ensure_ascii=False)
            + ". A brief with a mark left is refused.")


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
    goal = goal_refusal(tid, want)
    if goal:
        return "refused: " + goal
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


def cmd_drop(ids):
    refused = planner_only("dropping a task")
    if refused:
        return refused
    return "\n".join(drop(tid) for tid in ids)


def drop(tid, how="dropped"):
    """Stop whatever works on task tid, take it out of the queue and give it back: the planner's, whether it then
    re-plans the task or has deleted it (`v2.py edit`)."""
    st = peek()
    names = [n for n, s in st["sessions"].items() if s.get("task") == tid and not s.get("released")]
    for n in names:
        release(n)
    aside = leave(tid, how)
    with state() as w:
        w["tasks"].setdefault(tid, {})["stage"] = "planner" if how == "dropped" else "deleted"
        w["tasks"][tid].pop("lands_again", None)  # the planner's now to re-plan: it does not land by itself
        w["queue"] = [t for t in w["queue"] if t != tid]
    stopped = "stopped" if control() else "the supervisor stops"  # release() asked it, from inside the sandbox
    if how == "deleted":
        return f"task {tid} is deleted" + (f": {stopped} " + ", ".join(names) if names else "") + aside
    waiting = [x["id"] for x in all_tasks() if tid in (x.get("blockedBy") or []) and x.get("status") != "completed"]
    return (f"task {tid} is dropped: it leaves the queue and comes back to you to re-plan, split or take out of the "
            "list. " + (f"{stopped.capitalize()}: " + ", ".join(names) + "." if names else "Nothing was working on it.")
            + aside
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
    turn_over(c)
    return "planned. End your turn now; the knowledge base takes up your notes and the next planner starts from them."


# ---------------------------------------------------------------- commands of the harness

FRESH_CHARGE = (
    "This run begins on a knowledge base built fresh: it holds HANDOFF.md, the owner ledger and the owner's words, "
    "and nothing that any planner before you accumulated. The graph you inherit was built under a harness that has "
    "since changed, and some of it exists only because of faults that are now fixed. Before you queue anything, take "
    "stock, and make that your first piece of work:\n"
    "- **What has been produced.** Read what the finished tasks delivered and what stands uncommitted in the working "
    "tree and in each task's own tree (`.build/trees/N`, `git -C .build/trees/N status`), and write it into HANDOFF.md "
    "at the level later work needs. Work that is done but not yet integrated is the first thing to carry; a task whose "
    "deliverable already stands is completed, not repeated. A task whose session is gone keeps its tree, and the next "
    "session of it continues there from what the last one wrote; a tree whose task is done or dropped holds work that "
    "never landed — carry it or say why it is superseded. What was done and "
    "how — the course it took, what was abandoned, what it cost — goes to PLANNING_LOG.md, appended after what "
    "earlier planners left there, dated: HANDOFF.md is what you need to act now, the log is everything true that you "
    "no longer need to act on.\n"
    "- **What the graph no longer needs.** Drop what is superseded, what a fault made necessary, and what the work "
    "already answers (`v2.py drop ID`, and take the task out of the list). Say why in your notes: a task dropped "
    "without a reason comes back.\n"
    "Until you have taken stock the graph is **held**: nothing of it runs — no build, no fix, no review, no brief — "
    "and your order (`v2.py queue ID …`) is what lifts it. Dropping alone does not, and neither does re-planning. "
    "Nothing waits on a timer, so take the time this needs; you are reminded while the hold stands.\n"
    "- **What the structure should now be.** The harness has changed under you and the protocols carry what bears on "
    "planning: you live across your events and see each as it happens; the rate is what the owner set and your "
    "status line says it, so a review or a brief runs beside a producer; a task that parks hands the producing slot to anything independent that is ready; and your "
    "status line says how many tasks could start at all. Where the graph you inherit runs as a chain, each task "
    "waiting on the one before, re-plan it as work that can run beside itself wherever the work truly admits it, "
    "and not one step further than that.\n"
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
    for d in (OUTPUTS, BUILD, WANTED):
        # made here, outside the sandbox: a session in a task's tree may write these (settings.local.json) but not
        # their parent, and the sandbox can open only what exists when a command starts
        os.makedirs(d, exist_ok=True)
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
        FIRST=first_episode(), HANDOFF_DELTA=softly("the handoff's delta", handoff_delta, peek()["kb"]),
        STALE=stale_of(name, base_record("max")[0] or "max")), events=events, owner=True)
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
    standing_trees = [f"{x['task']} ({x['changed']} changed, {x['commits']} commits)" for x in trees_standing()]
    out.append("trees: " + ("off — every producing task works in the one tree, where one task's unfinished work holds "
                            "every other out" if not TREES else
                            "each producing task works in a tree of its own, made from HEAD, unless its ground stands "
                            "uncommitted in the one tree (its own installed work, or a path its brief names); a task "
                            "whose blockers' work has not landed waits for it")
               + (f"; standing: {', '.join(standing_trees)}" if standing_trees else "")
               + (f"; NO TREE IS MADE NOW: {open(os.path.join(STATE, 'no-tree')).read()}"
                  if TREES and os.path.exists(os.path.join(STATE, "no-tree")) else ""))
    busy = working(st)
    out.append(f"working: {len(busy)} of at most {WORKERS_MAX}"
               + (" and a supporting session apart" if support_apart() else "") + (f" ({', '.join(busy)})" if busy else ""))
    hour = softly("the last hour's occupancy", occupancy_text, default="")
    if hour:
        out.append(hour)
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
    behind = waiting_behind(ready)
    named = " ".join(f"{t} ({behind[t]} wait on it)" if behind.get(t) else t for t in ready)
    out.append(f"startable now: {named or 'none'}"
               + ("" if len(ready) > 1 else " — nothing else can start while what runs is parked or checking; only a "
                  "wider graph changes that"))
    backlog = build_backlog(st)
    width, depth = graph_figures(st)
    room = GRAPH_WIDTH or WORKERS_MAX
    closed = sorted(((k, d) for k, d in chain_depths().items() if d > GRAPH_DEPTH), key=lambda x: -x[1])
    out.append(f"graph: {width} build and fix tasks can start, {room} slots to take them; the longest chain is {depth} "
               f"deep; nothing is added at the end of a chain deeper than {GRAPH_DEPTH} — by a brief or by you — only "
               "detail and work that runs first"
               + (f" (past the limit now: {', '.join(f'{k} at {d}' for k, d in closed[:8])}"
                  + (f" and {len(closed) - 8} more" if len(closed) > 8 else "") + ")" if closed else "") + "; "
               f"{len(backlog)} open"
               + (f" of at most {BRIEF_BACKLOG}" if BRIEF_BACKLOG else ", no ceiling")
               + ("; no brief is detailed while there is already as much independent work as there are slots — one "
                  "is admitted again when the slots have taken what can start, and a brief is what widens a graph "
                  "rather than what drains it" if width >= room else "")
               + (f"; hang nothing after {', '.join(k for k, _ in closed[:8])} yourself, and a brief that would is "
                  "refused and comes to you" if closed else ""))
    parked = []
    for tid in resume_order(st):
        t, left = st["tasks"][tid], hold_left(st["tasks"][tid])
        parked.append(f"{tid} ({int(time.time() - t['parked']['since']) // 60} min, "
                      + (f"its hold ends in {int(left) // 60} min, so it goes first" if left is not None and
                         left <= PARK_URGENT else f"hold {int(left or 0) // 60} min left")
                      + ("" if tid in st["queue"] else ", not in your order")
                      + (f", after {t['parked']['after']}" if t["parked"].get("after") else "") + ")")
    if parked:
        out.append("parked, in the order they resume when their wait is over (your queue's order; a hold within "
                   f"{PARK_URGENT // 60} min of its end first; what your order does not name last): " + ", ".join(parked))
    waiting = [tid for tid, t in st["tasks"].items() if t.get("stage") in ("checking", "reviewing", "fixing", "committing")]
    if waiting:
        out.append("finishing: " + ", ".join(f"{tid}:{st['tasks'][tid]['stage']}" for tid in waiting))
    landed = softly("the landings", landed_lately, default=[])
    if landed:
        out.append(f"landed in the last {LANDED_SHOWN // 3600} hours: "
                   + ", ".join(f"{t} as {c} ({time.strftime('%H:%M', time.localtime(w))})" for t, c, w in landed[:20])
                   + (f", and {len(landed) - 20} more" if len(landed) > 20 else ""))
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
    if other_tools(s):  # the ping would write the whole prefix again rather than read it
        return f"{name}: not pinged (started with other tools than session-flags gives now)"
    n = f"warm-{name}-{int(time.time())}"  # its own name: a fork an earlier ping left listed is never read for this one
    claude("--bg", "--resume", s["sid"], "--fork-session", *session_flags(),
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
    got = subprocess.run([os.path.join(HERE, "session_fork_check.py"), r["sid"], s["sid"]], capture_output=True,
                         text=True) if r else None
    verdict = ((got.stdout.strip() or "no verdict: " + ((got.stderr.strip().splitlines() or ["nothing said"])[-1])[:160])
               if got else "no ping session")
    if r:
        claude("stop", r["id"])
        claude("rm", r["id"])
        for p in (f"{TRANSCRIPTS}/{r['sid']}.jsonl", f"{TRANSCRIPTS}/{r['sid']}"):
            with contextlib.suppress(OSError):
                shutil.rmtree(p) if os.path.isdir(p) else os.remove(p)
    if verdict.startswith("MISS"):
        # its entry is gone, and a ping cannot make it again: the fork wrote its own prefix, which nothing reads, and
        # the session's own entry comes back only with its next request (hit). Marked warm after a miss, kb-12 was
        # pinged every PING_AGE for 534K a time (2026-09-22 21:28), and every ping after it would have missed too.
        open(hits(name) + ".miss", "w").write(str(time.time()))
    elif verdict.startswith("OK") or os.environ.get("ORCH_PING_WAIT") == "0":
        hit(name)  # the ping read the session's own entry, and not the shorter ones under it (hit)
    else:
        # tried again in two minutes, while the entry may still be warm: a ping with no verdict held its mark for the
        # ten minutes that were left of the entry, and fix-49.3 (22:01) and implement-56 (23:59) went cold ten minutes
        # after one, each a whole session lost (2026-09-21)
        mark = os.path.join(STATE, f"ping-{name}")
        if os.path.exists(mark):
            os.utime(mark, (time.time() - PING_RETRY_AFTER, time.time() - PING_RETRY_AFTER))
    log(f"ping {name}: {verdict[:160]}")
    return verdict


def ping_missed(name):
    """Whether a ping of this session missed its entry and none is to be made until the session itself writes one."""
    return os.path.exists(hits(name) + ".miss")


FORK_MISSED = "forked.miss"  # <who>-forked.miss: a fork of this base wrote its prefix anew (cache_check)


def cache_check(sid, base_sid, name):
    """Background: record whether a fork's first request read its origin from cache. A fork that missed wrote its own
    prefix, which no later fork reads — every fork after it writes the whole prefix again (600K each) until the entry
    is made anew: the base is marked, and the watchdog rebuilds what its roles fork once (deltas, layers). Three
    entries were evicted within four minutes on 2026-09-22 (21:04 the high delta, 21:05 the xhigh layer, 21:07 a held
    session's), each write about 600K."""
    for _ in range(40):
        v = subprocess.run([os.path.join(HERE, "session_fork_check.py"), sid, base_sid], capture_output=True, text=True).stdout
        if v.startswith(("OK", "MISS")):
            log(f"cache of {name}: {v.split(' first own request ')[-1].split(' (')[0] if 'first own request' in v else v[:80]}"
                + ("" if v.startswith("OK") else " MISS"))
            who = (peek()["sessions"].get(name) or {}).get("origin")
            if v.startswith("MISS") and who in BASES:
                open(os.path.join(STATE, f"{who}-{FORK_MISSED}"), "w").write(str(time.time()))
            return
        time.sleep(3)


def main():
    """Every command is batchable (the owner, 2026-09-21): its arguments may be given again, in groups separated by a
    bare `--`, and each group is carried out as that command alone, its answer printed in turn — `v2.py reply q1 "…"
    -- q2 --file F`, `v2.py verdict 5 accept --file A -- 6 reject --file B`. The reading limits exist to make sessions
    batch what they read, and a command that took one thing a call rationed what they could learn instead."""
    a = sys.argv[1:]
    if not a:
        print(__doc__)
        return 2
    c, rest = a[0], a[1:]
    groups, group = [], []
    for x in rest:
        if x == "--":
            groups.append(group)
            group = []
        else:
            group.append(x)
    groups.append(group)
    if c == "read":  # one read, whatever its groups: each source is bounded, and the call as a whole (cmd_read)
        groups = [[x for g in groups for x in g]]
    if c == "ask":
        groups = asked_groups(groups)
    who = caller() if os.environ.get("CLAUDE_CODE_SESSION_ID") else None
    watch = Stopwatch(f"`v2.py {c}` of {who['name']}") if who else None
    codes = [run_command(c, g) for g in groups]
    if watch:
        watch.done()
    return max(codes)


ASK_TARGETS = ("kb", "planner", "designer", "task-designer", "reviewer")


def asked_groups(groups):
    """A batched question names its target once: a group that names none asks the previous group's, and one that
    begins with a bare target word asks that one. implement-192 wrote `ask --to planner "…" -- planner "…"`
    (2026-09-22 22:08): its first question was asked, its second refused, and the call ended failing."""
    out, to = [], None
    for g in groups:
        g = list(g)
        if "--to" in g and g.index("--to") + 1 < len(g):
            to = g[g.index("--to") + 1]
        elif g and g[0] in ASK_TARGETS:
            to = g.pop(0)
            g = ["--to", to] + g
        elif to and g:
            g = ["--to", to] + g
        out.append(g)
    return out


REFUSED = []  # the answers of this process that refused (run_command)


def say(text):
    """A command's answer, printed; a refusal is counted (run_command exits 1 for it)."""
    print(text)
    if isinstance(text, str) and text.startswith("refused"):
        REFUSED.append(text)


def run_command(c, rest):
    """One command, as its single form. One that refuses exits 1, so that what follows it with `&&` in the same call
    does not run: the protocols hand a piece of work over in one call — `v2.py finalize … && v2.py result ID`, `v2.py
    propose … && v2.py result ID` — and a refused hand-over must not be followed by a result that says it was made."""
    rest = list(rest)
    refused_before = len(REFUSED)

    def opt(name):
        if name in rest:
            i = rest.index(name)
            value = rest[i + 1] if i + 1 < len(rest) else ""
            del rest[i:i + 2]
            return value
        return None
    if c == "control" and not rest:  # the shell scripts' test (start.sh, stop.sh, base.sh, warm_daemon.sh)
        if control():
            return 0
        say(UNCONTROLLED)
        return 3
    if c in ("start", "stop", "talk", "ping") and not control():  # the owner's, from their own terminal
        say(UNCONTROLLED)
        return 3
    if c == "read" and rest:
        say(cmd_read(rest))
    elif c == "change" and not rest:
        said = cmd_change(sys.stdin.read())
        say(said)
        return 1 if said.startswith("refused") else 0  # a refused change reads as failing, and is told how to fix it
    elif c == "ledger" and rest:
        say(cmd_ledger(" ".join(rest)))
    elif c == "again":  # the guard carries it out before the call runs: it reaches here only outside a session
        say("refused: `v2.py again` runs a working session's kept command, fixed; the guard does it before the call "
              "runs, and here there is no session's command to fix")
        return 1
    elif c == "ask":
        to = opt("--to")
        say(cmd_ask(to, " ".join(rest)) if to and rest else "refused: ask --to kb|planner|designer|task-designer|reviewer "
            "TEXT (in a batch, a group after `--` asks the previous group's target unless it names one)")
    elif c == "tell" and len(rest) >= 2:
        # `tell ID... TEXT` or `tell ID... --file FILE`: the leading words that are tasks of the list are whom it
        # tells. `--file` was taken for the text: six of plan-45's messages of 2026-09-22 reached their sessions as
        # "--file .build/plans/plan-45/t230.md", and brief-230, whose reading refused that file, never had its own
        f = opt("--file")
        n = next((i for i, x in enumerate(rest if f is not None else rest[:-1]) if not (x.isdigit() and in_list(x))),
                 len(rest) if f is not None else len(rest) - 1)
        tids, words = rest[:max(n, 1)], rest[max(n, 1):]
        if f is not None:
            full = os.path.join(PROJECT, f)
            text = open(full, errors="ignore").read() if f and os.path.isfile(full) else ""
            why = (f"refused: no file {f or '(none named)'}" if not os.path.isfile(full) or not f else
                   f"refused: {f} is empty" if not text.strip() else
                   f"refused: `tell ID... --file FILE` takes no text besides the file's ({' '.join(words)[:80]})"
                   if words else None)
        else:
            text = " ".join(words)
            why = "refused: tell ID... TEXT|--file FILE" if not text.strip() or text.startswith("--") else None
        if why:
            say(why)
            return 1
        for tid in tids:
            say(cmd_tell(tid, text))
    elif c == "reply" and rest:
        decision = "--decision" in rest
        rest = [x for x in rest if x != "--decision"]
        f = opt("--file")
        qid = rest.pop(0)
        text = open(os.path.join(PROJECT, f), errors="ignore").read() if f else " ".join(rest)
        say(cmd_reply(qid, text, decision) if text.strip() else "refused: reply QID TEXT|--file FILE")
    elif c == "carried" and rest:
        say(cmd_carried(rest[0], " ".join(rest[1:])))
    elif c == "measuring":
        say(cmd_measuring(" ".join(rest)))
    elif c == "escalate":
        text = opt("--efficiency")
        say(cmd_escalate(" ".join(filter(None, [text, *rest]))) if text else "refused: escalate --efficiency TEXT")
    elif c == "end" and not rest:
        say(cmd_end())
    elif c == "park" and rest:
        say(cmd_park(rest[0], " ".join(rest[1:])))
    elif c == "unshelve" and len(rest) == 1:
        say(cmd_unshelve(rest[0]))
    elif c == "finalize" and rest:
        say(cmd_finalize(rest[0], rest[1:]))
    elif c == "result" and len(rest) == 1:
        say(cmd_result(rest[0], stdin_text()))
    elif c == "bring-main" and not rest:
        say(cmd_bring_main())
    elif c == "queue-probe" and len(rest) == 1:
        said = cmd_queue_probe(rest[0])
        say(said)
        return 1 if said.startswith("refused") else 0
    elif c == "check" and not rest:
        say(cmd_check())
    elif c == "verdict" and len(rest) >= 2:
        f = opt("--file")
        say(cmd_verdict(rest[0], rest[1], f))
    elif c == "queue":
        say(cmd_queue(rest))
    elif c == "after" and len(rest) == 2:
        say(cmd_after(rest[0], rest[1]))
    elif c == "propose" and len(rest) == 2:
        say(cmd_propose(rest[0], rest[1]))
    elif c == "accept" and rest:
        for bid in rest:
            say(cmd_accept(bid))
    elif c == "proposal" and rest:
        say(cmd_proposal(rest[0], rest[1:]))
    elif c == "edit" and len(rest) == 1:
        say(cmd_edit(rest[0]))
    elif c == "follow-up" and rest:
        kind = opt("--kind") or "fix"
        said = cmd_follow_up(rest, kind=kind)
        say(said)
        return 1 if said.startswith("refused") else 0
    elif c == "blockers" and len(rest) >= 2:
        say(cmd_blockers(rest[0], rest[1:]))
    elif c == "drop" and rest:
        say(cmd_drop(rest))
    elif c == "planned":
        say(cmd_planned(opt("--notes")))
    elif c == "start":
        say(cmd_start(fresh="--fresh" in rest))
    elif c == "stop":
        say(cmd_stop())
    elif c == "talk":
        say(cmd_talk())
    elif c == "graph":
        say(graph_text(full="--all" in rest))
    elif c == "status":
        say(cmd_status())
    elif c == "who" and len(rest) == 1:
        say(cmd_who(rest[0]))
    elif c == "dispatch":
        dispatch()
    elif c == "ping" and len(rest) == 1:
        say(ping(rest[0]))
    elif c == "cache-check" and len(rest) == 3:
        cache_check(*rest)
    else:
        say(__doc__)
        return 2
    return 1 if len(REFUSED) > refused_before else 0


if __name__ == "__main__":
    sys.exit(main())
