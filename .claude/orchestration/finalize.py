#!/usr/bin/env python3
"""The finalizer of a task: no model, only the task's final job, in two parts around its review.

  finalize.py check ID    run the acceptance check of .build/tasks/ID/finalize.json (output in finalize.log) once
                          Isabelle has room (a check that advances the base heap waits until nothing else runs and
                          holds the machine); the task goes to its review when it passes, to a quick fix when it
                          fails the first time, to the planner when it fails again (v2.checked)
  finalize.py commit ID   after the verdict accepted it: commit the named files with the session's message and push
                          (v2.committed); a task in its own tree is committed on its branch and lands with the next
                          landing train (train.py)
  finalize.py land-queue  land what waits in the landing queue, its finalizers ended (started by the watchdog)
  finalize.py check-batch check what waits in the check queue: sessions that asked (v2.py check), finalizers ended

The outcome is recorded in .build/tasks/ID/finalized.json, which efficiency.py credits to the task's session.
"""
import contextlib
import fcntl
import glob
import json
import os
import re
import shutil
import shlex
import signal
import subprocess
import tempfile
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.modules.setdefault("finalize", sys.modules[__name__])  # run as a script, train.py's `import finalize` is this module
import v2  # noqa: E402

TIMEOUT = int(os.environ.get("ORCH_FINAL_MAX", 3600))
WAIT_MAX = int(os.environ.get("ORCH_ISABELLE_WAIT", 3600))
POLL = float(os.environ.get("ORCH_ISABELLE_POLL", 15))
RAN_MIN = float(os.environ.get("ORCH_CHECK_MIN", 20))  # under this, a failure with a tool's own complaint never ran
# The proof base refusing a check before it begins — its heap missing or recorded under another store, its lineage
# broken — is the base's, whoever's check it was: from 14:06 to 14:08 on 2026-09-22 every check failed so in a second
# ("Accepted heap/database changed", the lasting base led to by a link its tools cannot read), and four landings and
# six checks were sent to their tasks' quick fixes. Such a check is run again once the base has changed, or after
# BASE_RETRY, and nobody is told it failed.
BASE_REFUSED = re.compile(r"Accepted heap/database (?:changed|missing)|Accepted database missing|Cyclic proof context "
                          r"lineage|A context without a stored heap cannot be a parent|active context .* does not match|"
                          r"Recorded heap storage differs")
BASE_RETRY = int(os.environ.get("ORCH_BASE_RETRY", 600))


def base_refused(ok, seconds, log):
    """Whether a failed check was refused by the proof base before it began (BASE_REFUSED)."""
    if ok or seconds >= RAN_MIN * 3:
        return False
    try:
        return bool(BASE_REFUSED.search(open(log, errors="ignore").read()[-20000:]))
    except OSError:
        return False


def base_changed_or(until):
    """Wait until the active base changes, or `until`."""
    before = active_pointer()
    while time.time() < until and active_pointer() == before:
        time.sleep(POLL)


def check_again(tid, why):
    """A check the base refused: the task stays where it is and its check is run again (v2.check_again_due)."""
    with v2.state() as w:
        t = w["tasks"].setdefault(tid, {})
        t["check_again"] = {"at": time.time(), "pointer": active_pointer(), "why": why[-300:]}
    v2.say_once(f"base-refused-{tid}", f"ATTENTION the proof base refused task {tid}'s check before it began, not the "
                f"task's work: {why.strip().splitlines()[-1][:200] if why.strip() else ''}; it is run again once the base "
                "has changed", every=1800)
NOT_RUN = re.compile(r"Traceback \(most recent call last\)|^usage:|unrecognized arguments|No such file or directory"
                     r"|command not found|: not found$", re.M)


GIT_ENV = dict(os.environ, GIT_TERMINAL_PROMPT="0")  # never a credentials prompt


def git(*args, timeout=120, tree=None, tries=10):
    """A git command in a tree (the task's own where it has one); a failure or its timeout is a result with a return
    code, never an exception. One refused because another git process holds the index's lock has done nothing and is
    tried again: the landing's commit in task 95's tree met a `git status` there and was taken for the commit gate's
    refusal — the task went back, and a new designer found its work whole (2026-09-22 03:49)."""
    for attempt in range(tries):
        try:
            r = subprocess.run(["git", "-C", tree or v2.PROJECT, *args], capture_output=True, text=True,
                               timeout=timeout, env=GIT_ENV)
        except (subprocess.TimeoutExpired, OSError) as e:
            return subprocess.CompletedProcess(args, 124, "", f"git {' '.join(args[:2])}: {e}")
        if r.returncode == 0 or "index.lock" not in r.stderr or attempt == tries - 1:
            return r
        time.sleep(2)
    return r


git_retrying = git  # every command now tries again on the index's lock


def outcome(tid, **fields):
    path = os.path.join(v2.BUILD, tid, "finalized.json")
    try:
        o = json.load(open(path))
    except (OSError, ValueError):
        o = {}
    o.update(fields)
    json.dump(o, open(path, "w"), indent=1)
    return o


def machine_free(tid, exclusive=False):
    """Whether this task's run may start now, as wait_for_isabelle judges it, without admitting it."""
    holder, load = v2.exclusive_holder(), v2.isabelle_load()
    queued = (v2.pending_claim() or {}).get("task")  # a measurement waiting for the machine to empty
    free = (load["heavy"] + load["probe"] == 0 if exclusive else load["heavy"] < v2.ISABELLE_MAX) \
        and not v2.memory_short() and queued in (None, tid) \
        and not v2.machine_ahead(v2.peek(), [tid])  # the memory a run must leave free; its turn
    return not holder and free


def wait_for_isabelle(tid, exclusive, end=None):
    """A check that advances the base heap waits until no Isabelle runs and holds the machine meanwhile; any other waits
    for a free run (v2.ISABELLE_MAX) and for no advancing check. It waits at most WAIT_MAX seconds (or until `end`),
    then runs anyway. One finalizer decides at a time, and the run it is let start counts as running from then on
    (v2.isabelle_admitted): three that started in one second on 2026-09-21 each counted no run and ran together."""
    end = end or time.time() + WAIT_MAX
    os.makedirs(v2.ADMITTED, exist_ok=True)
    try:
        while True:
            v2.machine_waiting(tid)  # it waits for a heavy run, in the planner's order with every other (machine_ahead)
            with open(os.path.join(v2.STATE, "isabelle-admit.lock"), "w") as lock:
                fcntl.flock(lock, fcntl.LOCK_EX)
                # a check that advances the base waits for no run at all, since the heap it replaces is under every
                # probe too; any other check is a heavy run, and waits only for a heavy slot (probes have their own)
                if machine_free(tid, exclusive) or time.time() >= end:
                    open(os.path.join(v2.ADMITTED, tid), "w").write(str(os.getpid()))  # who runs it (unseen_finalizer_runs)
                    if exclusive:  # with the process that holds it, so that a claim cannot outlive its check
                        v2.claim_exclusive(tid, "its final check advances the base heap", pid=os.getpid())
                    return
            time.sleep(POLL)
    finally:
        v2.machine_waiting(tid, waiting=False)


def admitted_no_more(tid):
    """The finalizer has ended: its run no longer counts as one starting."""
    with contextlib.suppress(OSError):
        os.remove(os.path.join(v2.ADMITTED, tid))


def alive(tid):
    """The finalizer of a task marks itself while it runs (watchdog.finalizer_alive)."""
    path = os.path.join(v2.BUILD, tid, "finalizer.pid")
    open(path, "w").write(str(os.getpid()))
    return path


def check(tid):
    mark = alive(tid)
    try:
        return checked_run(tid)
    finally:
        admitted_no_more(tid)
        with contextlib.suppress(OSError):
            os.remove(mark)


def checked_run(tid):
    d = os.path.join(v2.BUILD, tid)
    if (v2.peek()["tasks"].get(tid) or {}).get("check_again"):
        with v2.state() as w:
            w["tasks"][tid].pop("check_again", None)
    spec = json.load(open(os.path.join(d, "finalize.json")))
    trouble = v2.tree_trouble(v2.worktree_of(tid))
    if trouble:  # every check refuses on this, whatever the task did: spend none of it, and cost the task no round
        tail = "The working tree refuses every check as it stands, whatever this task did:\n- " + "\n- ".join(trouble)
        open(os.path.join(d, "finalize.log"), "w").write(tail + "\n")
        outcome(tid, ok=False, seconds=0)
        v2.log(f"check of task {tid}: not run, the working tree is inconsistent")
        v2.tree_checked("the harness", f"task {tid}'s check was about to run", v2.worktree_of(tid))
        v2.checked(tid, False, tail, ran=False)
        return 1
    standing = v2.base_would_stand_in_a_task(spec["check"])
    if standing:  # a job recorded before the rule, or around it: the base must not come to stand in a task's tree
        tail = "This check was not run: " + v2.BASE_IN_A_TASK.format(named=", ".join(standing))
        open(os.path.join(d, "finalize.log"), "w").write(tail + "\n")
        outcome(tid, ok=False, seconds=0)
        v2.log(f"check of task {tid}: not run, it would leave the base in the task's own directory")
        v2.checked(tid, False, tail, ran=False)
        return 1
    if spec["check"] == v2.DOCUMENTS_CHECK:  # its own check, seconds and no machine: nothing to wait for
        ok, tail = documents_check(v2.worktree_of(tid), spec["files"])
        open(os.path.join(d, "finalize.log"), "w").write(tail + "\n")
        outcome(tid, ok=ok, seconds=0, documents=True)
        v2.log(f"check of task {tid}: {'passed' if ok else 'failed'} (its documents; no machine)")
        say(v2.checked, tid, ok, tail, True)
        return 0 if ok else 1
    import train
    batchable = v2.apart(tid) and BATCHABLE.match(spec["check"]) and not v2.ADVANCES.search(spec["check"])
    if train.BATCHES and batchable:
        code = train.check_in(tid, v2.worktree_of(tid), time.time() + WAIT_MAX)  # with every check waiting, once
        if code is not None:
            return code
        v2.log(f"ATTENTION task {tid}'s check was to join a batch and runs by itself: the batch gave it no answer")
    elif batchable:
        v2.log(f"task {tid}'s check runs by itself: checks are not batched (ORCH_BATCHES)")
    exclusive = bool(v2.ADVANCES.search(spec["check"]))
    deadline = time.time() + WAIT_MAX
    # a check in the one tree reads main's working files, which a landing merges into: main does not move under it
    with (v2.landing(deadline, shared=True) if not v2.apart(tid) else contextlib.nullcontext(True)) as held:
        if not held:
            tail = f"This check was not run: landings held main for {WAIT_MAX // 60} minutes."
            open(os.path.join(d, "finalize.log"), "w").write(tail + "\n")
            outcome(tid, ok=False, seconds=0)
            v2.checked(tid, False, tail, ran=False)
            return 1
        wait_for_isabelle(tid, exclusive, end=deadline)
        LANDING.append([])
        try:
            # the check sees the working tree, which holds this task's changes alone: while a finalization is in
            # flight, every other session writes only under .build/ (v2.tree_holder, the guard)
            code = run_check(tid, d, spec)
        finally:
            later = LANDING.pop()
            if exclusive:
                with contextlib.suppress(OSError):
                    os.remove(os.path.join(v2.STATE, "isabelle-exclusive"))
    for report, args in later:  # once main is let go: a report dispatches, and a dispatch may begin a landing
        report(*args)
    return code


# The repository's check as a task hands it over (every one of the forty hand-overs before 2026-09-22 14:00 that was not
# a documents check was this, with its own --output and at times a --timeout): run by the harness in a check batch
# (train.check_in). A command that also runs something else is the task's own, and runs as it was written.
BATCHABLE = re.compile(r"^\s*python3?\s+(?:-B\s+)?tools/incremental_check\.py\s+check\s+--output\s+\S+"
                       r"(?:\s+--timeout\s+\d+)?\s*$")

ERRORS_HEAD = "[this check reported "


def log_tail(log):
    """What a failed check's log says to the one who acts on it: the list of every error it reported, where the check
    ends by listing them (check_errors.py), and the whole log's place; else its last lines, each cut short. The last 30
    lines were sent whole: task 143's second failure went to the planner as 28 lines of recipes accepted and a summary
    of 1.5K characters, its error list after them (2026-09-22 11:47)."""
    lines = open(log, errors="ignore").read().splitlines()
    rel = os.path.relpath(log, v2.PROJECT)
    starts = [i for i, l in enumerate(lines) if l.startswith(ERRORS_HEAD)]
    if starts:
        block = lines[starts[-1]:]  # bounded by the list itself (check_errors.ROOM), which names where the rest is
        return "\n".join(l[:400] for l in block) + f"\n(the whole log: {rel})"
    return "\n".join(l if len(l) <= 300 else l[:300] + " …" for l in lines[-15:]) + f"\n(the whole log: {rel})"


CHECK_ERRORS = os.path.join(HERE, "check_errors.py")


def listing_errors(tid, command):
    """The check command run through check_errors.py, as a session's own check is (work_meter.bounded): to its end, its
    log ending with every error it reported — Isabelle's from the logs under its --output (the proof's build.log), the
    recipes and host tests that failed — the whole list kept beside its report when the text has no room for it. The
    repository's check logs one JSON line, which names build.log and not one error: since the harness runs the checks
    (batches, trains), task 153 was told its batch failed with that line cut at 300 characters (2026-09-22 15:46),
    and every failure reached its session so."""
    out = re.search(r"--output[ =](\S+)", command)
    watched = ["--watch", out.group(1), "--keep", out.group(1)] if out else ["--keep", os.path.join(v2.BUILD, tid)]
    return " ".join(shlex.quote(a) for a in [sys.executable, "-B", CHECK_ERRORS, *watched, "--", "bash", "-c", command])


def run_logged(tid, command, cwd, log):
    """Run a check command in `cwd` with its output in `log` — ending with every error it reported (listing_errors) —
    its process group registered for the watchdog: (ok, seconds, what the log says to the one who acts on it)."""
    d, started = os.path.join(v2.BUILD, tid), time.time()
    with open(log, "w") as out:
        run = subprocess.Popen(listing_errors(tid, command), shell=True, cwd=cwd, stdout=out, stderr=subprocess.STDOUT,
                               start_new_session=True, env=dict(os.environ, ORCH_READ_BYTES=str(v2.READ_BYTES)))
        with open(os.path.join(d, "finalizer.pid"), "a") as f:
            f.write(f"\n{run.pid}")  # the check's own process group, for the watchdog to end with the finalizer
        try:
            ok = run.wait(timeout=TIMEOUT) == 0
        except subprocess.TimeoutExpired:  # the whole check goes, Isabelle's processes under it included
            for sig, grace in ((signal.SIGTERM, 10), (signal.SIGKILL, 10)):
                with contextlib.suppress(OSError):
                    os.killpg(run.pid, sig)
                with contextlib.suppress(subprocess.TimeoutExpired):
                    run.wait(timeout=grace)
                    break
            out.write(f"\nthe check did not finish within {TIMEOUT} s\n")
            ok = False
    return ok, time.time() - started, log_tail(log)


def fresh_output(tid, check, cwd):
    """The check with a fresh `--output`: the check tool refuses a directory that exists, to keep its evidence, so a
    check run again — after a quick fix, or when a task taken back is checked before its review — would never run as
    written. It costs no session to correct: the next free sibling is used for this run, and said."""
    m = re.search(r"(--output(?:=|\s+))(\S+)", check)
    if not m or not os.path.exists(os.path.join(cwd, m.group(2))):
        return check
    n = 2
    while os.path.exists(os.path.join(cwd, f"{m.group(2)}-{n}")):
        n += 1
    v2.log(f"the check of task {tid} writes to {m.group(2)}-{n}: {m.group(2)} holds an earlier run's evidence")
    return check[:m.start(2)] + f"{m.group(2)}-{n}" + check[m.end(2):]


def documents_check(tree, files, sources=True):
    """(ok, what it found) of a commit of documents only (v2.documents_only), in `tree`: the repository's structural
    source checks (tools/check.py source_checks: every theory declared and present, no proof escaping), every row of
    THEORY_MAP.md naming a theory that is there and none twice, and no conflict marker in a document it commits. What
    HEAD already has is not this commit's: only what it adds is said. Seconds, and no Isabelle. Without `sources` (a
    landing train that also holds code, whose repository check runs the source checks itself) the rows and the markers
    alone."""
    found = []
    r = subprocess.run([sys.executable, "-B", "-c", "import sys, json; sys.path.insert(0, 'tools'); import check; "
                        "print(json.dumps(check.source_checks()['refusals']))"], cwd=tree, capture_output=True,
                       text=True, timeout=300) if sources else None
    try:
        found += json.loads(r.stdout.strip().splitlines()[-1]) if r else []
    except (ValueError, IndexError):
        found.append(f"the source checks did not run: {(r.stderr or r.stdout).strip()[-300:]}")

    def map_problems(text, theories):
        names = [m.group(1) for m in map(ROW_KEYS["THEORY_MAP.md"].match, text.splitlines()) if m and m.group(1) != "Theory"]
        seen, out = set(), []
        for n in names:
            if n not in theories:
                out.append(f"THEORY_MAP.md has a row for {n}, which no theory is")
            elif n in seen:
                out.append(f"THEORY_MAP.md has the row of {n} twice")
            seen.add(n)
        return out
    here = {os.path.basename(p)[:-4] for p in glob.glob(os.path.join(tree, "theories", "*.thy"))}
    head = {os.path.basename(p)[:-4] for p in git("ls-tree", "--name-only", "HEAD", "theories/").stdout.split()
            if p.endswith(".thy")}
    try:
        now = map_problems(open(os.path.join(tree, "THEORY_MAP.md"), errors="ignore").read(), here)
    except OSError:
        now = []
    before = set(map_problems(git("show", "HEAD:THEORY_MAP.md").stdout, head))
    found += [p for p in now if p not in before]
    for f in files:
        try:
            text = open(os.path.join(tree, f), errors="ignore").read()
        except OSError:
            continue
        if CONFLICT_MARK.search(text):
            found.append(f"{f} holds a conflict marker")
    if found:
        return False, (f"{ERRORS_HEAD}{len(found)} error{'s' if len(found) > 1 else ''}, listed here with where each "
                       "stands.]\n" + "\n".join(f"- {x}" for x in found))
    return True, "the documents check passed: the sources' structure, THEORY_MAP.md's rows, no conflict marker"


CONFLICT_MARK = re.compile(r"^(?:<{7}|>{7}) ", re.M)  # a conflict leaves both; "=======" alone is a heading's rule


def documents_task(tid):
    """Whether a task's hand-over is checked by the finalizer's documents check (v2.DOCUMENTS_CHECK)."""
    try:
        return json.load(open(os.path.join(v2.BUILD, tid, "finalize.json"))).get("check") == v2.DOCUMENTS_CHECK
    except (OSError, ValueError):
        return False


def run_check(tid, d, spec):
    cwd = v2.worktree_of(tid)
    # run to its end and ending with every error it reported, as every check the harness runs is (run_logged): the
    # quick fix that follows a failed one is given the log's end, which then holds them all (2026-09-21). It was also
    # wrapped here, and listed its errors twice once run_logged did (2026-09-22)
    check = fresh_output(tid, spec["check"], cwd)
    ok, seconds, tail = run_logged(tid, check, cwd, os.path.join(d, "finalize.log"))
    if base_refused(ok, seconds, os.path.join(d, "finalize.log")):
        check_again(tid, tail)
        return 1
    output = re.search(r"--output\s+(\S+)", check)
    outcome(tid, ok=ok, seconds=round(seconds), check_output=output.group(1) if output else None)
    # a check that exits at once with a tool's own complaint never ran: the command is wrong, not the work
    ran = bool(ok) or seconds >= RAN_MIN or not NOT_RUN.search(tail)
    v2.log(f"check of task {tid}: " + ("passed" if ok else "failed" if ran else "did not run (the command is not "
                                       "runnable as written)"))
    say(v2.checked, tid, ok, tail, ran)
    return 0 if ok else 1


# A draft's unfilled stand-in, in the form this repository writes them (CHECK_NUMBERS, REPLAY_NUMBERS). The braced
# form a protocol uses is NOT one: code writes {NAME} in an f-string and prose quotes the harness's own placeholders,
# and both were refused as drafts (2026-09-20). Those are logged where they are new to a change, never refused.
PLACEHOLDER = re.compile(r"\b[A-Z][A-Z_]{2,}_NUMBERS\b")
BRACED = re.compile(r"\{[A-Z][A-Z_]{2,}\}")


PENDING = "entry-commit.json"  # the entry a commit left open, and the commit that closes it


def entry_heading(lines, i):
    """The `## ...` heading the line i stands under."""
    return next((lines[j].strip() for j in range(i, -1, -1) if lines[j].startswith("## ")), "")


def fill_pending_commit(files, tree=None):
    """An entry closes with ``Recorded <date>, commit `…`.`` and no session can fill that hash before its own commit
    exists, so the commit that makes it records which entry it left open (record_pending_commit) and the next commit
    touching the file closes it. The hash is never guessed from the file's history: `git blame` follows the line's
    text, and a line restored to wording an earlier commit used is attributed to that commit, which once closed an
    entry with a commit carrying none of what it records (2026-09-20)."""
    if "DECISIONS.md" not in files:
        return []
    tree = tree or v2.PROJECT  # defaulted before it is joined: `path` was built from it one line too early
    path, mark = os.path.join(tree, "DECISIONS.md"), os.path.join(v2.STATE, PENDING)
    try:
        pending = json.load(open(mark))
    except (OSError, ValueError):
        return []
    try:
        lines = open(path, errors="ignore").read().splitlines(keepends=True)
    except OSError:
        return []
    for i, line in enumerate(lines):
        if "commit `…`" in line and entry_heading(lines, i) == pending["heading"]:
            lines[i] = line.replace("commit `…`", f"commit `{pending['commit']}`")
            open(path, "w").write("".join(lines))
            os.remove(mark)
            v2.log(f"closed the entry {pending['heading']!r} with commit {pending['commit']}")
            return [pending["commit"]]
    os.remove(mark)  # the entry is gone or was closed otherwise: the record has nothing left to close
    v2.log(f"the entry {pending['heading']!r} no longer waits for a commit; the record is dropped")
    return []


def record_pending_commit(files, ref, tree=None):
    """This commit carries an entry that still ends in `…`: the next commit touching the file closes it with this
    hash, which is the commit that carries what the entry records."""
    if "DECISIONS.md" not in files or not ref:
        return
    try:
        lines = open(os.path.join(tree or v2.PROJECT, "DECISIONS.md"), errors="ignore").read().splitlines()
    except OSError:
        return
    open_at = [i for i, line in enumerate(lines) if "commit `…`" in line]
    if not open_at:
        return
    heading = entry_heading(lines, open_at[-1])
    json.dump({"heading": heading, "commit": ref}, open(os.path.join(v2.STATE, PENDING), "w"), indent=1)
    v2.log(f"the entry {heading!r} waits for commit {ref}; the next commit touching DECISIONS.md closes it")


def foreign(tid, files):
    """The files of this commit that another unfinished task wrote last: its work would be committed under this task's
    message (2026-09-20: task 3's commit carried task 5's half-written entry, placeholders and all)."""
    with v2.owners(write=False) as o:
        marked = {f: o.get(os.path.normpath(f)) for f in files}
    return {f: t for f, t in marked.items() if t and t != tid
            and (v2.read_task(t) or {}).get("status") not in ("completed", None)}


def unreviewed_work(tid, files, own_tree=False):
    """{file: task} of what this commit would carry that no review has accepted: the task's own work while its reviews
    have not all accepted it, and any other task's work in the files. Task 52 was planned to commit four tasks' work
    in one commit with their reviews to follow; a commit is what a review decides, so it comes after. A commit made in
    the task's own tree carries only that tree: who wrote the same paths in the one tree is not in it (task 24 was
    refused for task 54's THEORY_MAP.md, 2026-09-21)."""
    st = v2.peek()
    with v2.owners(write=False) as o:
        marked = {f: (None if own_tree else o.get(os.path.normpath(f))) or tid for f in files}
    return {f: t for f, t in marked.items() if not v2.review_accepted(st, t)}


def refuse(tid, why):
    outcome(tid, ok=False, commit=None, commit_error=why)
    v2.log(f"commit of task {tid} refused: {why}")
    say(v2.committed, tid, None, why)
    return 1


def commit(tid):
    mark = alive(tid)
    try:
        return committed_run(tid)
    finally:
        admitted_no_more(tid)
        with contextlib.suppress(OSError):
            os.remove(mark)


def committed_run(tid):
    """The task's files, and the planner's state as it stands (HANDOFF.md, committed with every task as before). Where
    the task has a tree of its own the commit is made there, on its own branch, and brought into the branch that is
    pushed by a merge — which meets the other tasks' lines line by line instead of file by file.

    Main moves by one landing at a time (v2.landing), and never into a state worse than it was: a commit that would
    leave HEAD with trouble it does not already have is refused (v2.new_trouble). A task in its own tree was checked
    on its branch as HEAD stood when the tree was made; what landed since is brought into its branch first, and when
    that brought anything the repository's check of the two together runs before main moves (land)."""
    d = os.path.join(v2.BUILD, tid)
    spec = json.load(open(os.path.join(d, "finalize.json")))
    tree, files = v2.worktree_of(tid), list(spec["files"])
    own_tree = tree != v2.PROJECT
    # every wait of the commit comes out of one budget, so that waiting, a landing check and the commit stay inside
    # what the watchdog allows the step (watchdog.FINAL_MAX: the Isabelle wait, the run, and a margin)
    deadline = time.time() + WAIT_MAX
    theirs, waited = ({} if own_tree else foreign(tid, files)), 0
    while theirs and waited < v2.COMMIT_WAIT:  # its files were free while this task was reviewed: an append may be
        if waited == 0:                        # in flight, and it lands in seconds — a commit waits rather than fails
            v2.log(f"the commit of task {tid} waits for {', '.join(f'{f} (task {x})' for f, x in theirs.items())}")
        time.sleep(5)
        waited += 5
        theirs = foreign(tid, files)
    if theirs:
        return refuse(tid, "the commit would carry another task's uncommitted work: "
                      + ", ".join(f"{f} (task {t})" for f, t in theirs.items())
                      + ". That task installs and commits its own change; this one commits the rest.")
    unreviewed = unreviewed_work(tid, files, own_tree)
    if unreviewed:
        return refuse(tid, "a task's work is committed after its review has accepted it, never before (the owner, "
                      "2026-09-21), and this commit would carry work no review has accepted: "
                      + ", ".join(f"{f} (task {t})" for f, t in unreviewed.items()) + ". Each lands by its own "
                      "check, review and commit.")
    # A task in its own tree lands by a merge into the one tree, which git refuses while the one tree holds a working
    # change of a file the merge writes. It waits for that change to be committed, out of the same budget and before
    # main is held — the commit it waits for holds main to land. Task 24 was sent to the planner for task 54's
    # THEORY_MAP.md at 23:02:10, and 54 committed it at 23:03:06 (2026-09-21).
    standing = stood_for(tid, landing_paths(tree, files), deadline) if own_tree else {}
    if standing:
        return standing_refused(tid, standing, "Nothing of it was committed")
    import train
    if own_tree and train.ON:  # committed on its branch, queued, and landed with the next train
        return train.hand_in(tid, spec, tree, files, deadline)
    waited = False
    while True:
        with v2.landing(deadline) as held:
            if not held:
                with v2.state() as w:  # nothing of it is wrong: it is made again by itself (v2.lands_when_free)
                    w["tasks"].setdefault(tid, {}).update(lands_again=time.time(), lands_again_why="main")
                return refuse(tid, f"other landings held main for {WAIT_MAX // 60} minutes, so this one did not "
                              "begin; its work is whole. It lands again by itself: its commit is made again, with no "
                              f"session, and you are told. Nothing is yours to do for it unless you mean it not to land "
                              f"(`v2.py drop {tid}`).")
            LANDING.append([])
            try:
                code = commit_and_land(tid, spec, tree, files, own_tree, deadline)
            finally:
                later = LANDING.pop()
        for report, args in later:  # after main is let go: a report dispatches, and a dispatch may begin the next landing
            report(*args)
        if code == MACHINE:  # its check with what landed cannot start now: it waits with main let go, then lands
            if not waited:
                v2.log(f"the landing of task {tid} lets main go while its check with what landed waits for the machine")
                waited = True
            while time.time() < deadline and not machine_free(tid):
                time.sleep(POLL)
            continue
        if not isinstance(code, dict):
            return code
        # What came to stand in the one tree while it landed — its landing check takes minutes, and one-tree tasks
        # write the same index files: task 66's DECISIONS.md refused task 80's merge at 00:00:55 on 2026-09-22 — is
        # waited for with main let go, as before it; its commit stands on its branch and it lands again from there.
        standing = stood_for(tid, list(code), deadline)
        if standing:
            undo_advance(tid)
            return standing_refused(tid, standing, f"Its commit stands on branch task/{tid}")


def stood_for(tid, paths, deadline):
    """What of `paths` still stands uncommitted in the one tree once waited for until `deadline`: {path: task}."""
    standing = v2.one_tree_changes(paths)
    if standing:
        v2.log(f"the landing of task {tid} waits for what stands uncommitted in the one tree: {named(standing)}")
    while standing and time.time() < deadline:
        time.sleep(5 if v2.PAUSE else 0.2)
        standing = v2.one_tree_changes(paths)
    return standing


def standing_refused(tid, standing, done):
    """Its review accepted it and only the one tree's uncommitted changes kept it out of main, past the commit's budget:
    marked so that it lands again by itself once they are committed (v2.lands_when_free), or when queued (v2.cmd_queue),
    its commit made again with no session."""
    with v2.state() as w:
        w["tasks"].setdefault(tid, {})["lands_again"] = time.time()
    return refuse(tid, f"its landing would merge into the one tree over what stands there uncommitted: "
                  f"{named(standing)}, and git refuses to overwrite a working change; it waited {WAIT_MAX // 60} "
                  f"minutes for them. {done}; its work is whole. It lands again by itself once they are committed: its "
                  "commit is made again, with no session, and you are told. Nothing is yours to do for it unless you "
                  f"mean it not to land (`v2.py drop {tid}`).")


LANDING = []  # while a landing holds main: the reports it owes, made once it has let main go


def landing_paths(tree, files):
    """What a landing's merge writes in the one tree: the task's files, and HANDOFF.md when its tree changed it (it is
    committed with the task's change, commit_and_land)."""
    return list(files) + [p for p in ("HANDOFF.md",) if p not in files
                          and git("status", "--porcelain", "--", p, tree=tree).stdout.strip()]


def named(standing):
    return ", ".join(f"{f} ({f'task {t}' if t else 'no task wrote it'})" for f, t in standing.items())


def say(report, *args):
    """A report to the harness (v2.committed, v2.landing_failed): at once, or once the landing in progress is over."""
    if LANDING:
        LANDING[-1].append((report, args))
    else:
        report(*args)


def stage(files, tree):
    """Stage a task's files. A path HEAD tracks is the repository's own whatever .gitignore says, since ignore rules reach
    only untracked files: gone from the tree its deletion is staged (`rm --cached`, nothing when already staged), and
    standing it is added with -f, which for a tracked path lifts only the ignore rule — `git add` refused both as
    "ignored" (task 48's removal of the tracked tools/__pycache__/build.cpython-314.pyc, 2026-09-21). Every other path
    is added as before, and an ignored untracked one stays out."""
    tracked = [f for f in files if git("cat-file", "-e", f"HEAD:{f}", tree=tree).returncode == 0]
    gone = [f for f in tracked if not os.path.lexists(os.path.join(tree or v2.PROJECT, f))]
    rest = [f for f in files if f not in tracked]
    r = None
    for args in ((["add", "--", *rest]) if rest else None,
                 (["add", "-f", "--", *[f for f in tracked if f not in gone]]) if len(tracked) > len(gone) else None,
                 (["rm", "--cached", "--ignore-unmatch", "-q", "--", *gone]) if gone else None):
        if args:
            r = git_retrying(*args, tree=tree)
    return r


def commit_and_land(tid, spec, tree, files, own_tree, deadline):
    made = branch_commit(tid, spec, tree, files, own_tree)
    if isinstance(made, int):
        return made
    c, files = made
    ref = git("rev-parse", "--short", "HEAD", tree=tree).stdout.strip() if c.returncode == 0 else None
    if ref and own_tree:  # its branch meets what landed meanwhile, line by line, and is checked with it
        failed = land(tid, tree, deadline)
        if failed is not None:
            if not isinstance(failed, dict) and failed != MACHINE:
                undo_advance(tid)  # it did not land: the base goes back (a wait or a retry keeps it)
            return failed
        ref = git("rev-parse", "--short", "HEAD").stdout.strip()
        retain_landed(tid)  # the base follows main: its check's receipts, committed after its own merge
    if ref:
        with v2.owners() as o:  # committed: no longer anyone's uncommitted change
            for f in files:
                o.pop(os.path.normpath(f), None)
        record_pending_commit(files, ref, v2.PROJECT)
    error = None if c.returncode == 0 else (c.stdout + c.stderr).strip()[-400:]
    p = git("push", "origin", "HEAD", timeout=180) if ref else None
    pushed = bool(p and p.returncode == 0)
    outcome(tid, commit=ref, commit_error=error, pushed=pushed)
    if ref:
        v2.tree_checked(f"task {tid}", "its commit")
        if own_tree:
            v2.worktree_gone(tid)
    v2.log(f"commit of task {tid}: " + (ref or f"failed: {error}") + ("" if pushed or not ref else " (the push failed)"))
    say(v2.committed, tid, ref and ref + ("" if pushed else " (the push failed)"), error)
    return 0 if ref else 1


def check_summary(out):
    """One sentence of what a repository check's report found (its incremental.json under `out`), or None."""
    try:
        r = json.load(open(os.path.join(v2.PROJECT, out, "incremental.json")))
    except (OSError, ValueError, TypeError):
        return None
    if r.get("status") != "accepted":
        return None
    recipes = r.get("recipes") or {}
    ran = sum(v.get("status") == "accepted" for v in recipes.values())
    kept = sum(v.get("status") in ("reused", "unchanged") for v in recipes.values())
    host = r.get("host_tests") or {}
    tests = " and ".join(f"{v.get('ran', 0)} {k.rstrip('s')} tests" + (f" ({v['skipped']} skipped)" if v.get("skipped")
                                                                       else "") for k, v in host.items()) + (" pass" if host else "")
    count = lambda v: v if isinstance(v, int) else len(v or [])  # the report gives a list, or its count
    return (f"passed in {round(r.get('seconds') or 0)} s — {r.get('theories', '?')} theories, "
            f"{count(r.get('rebuilt_theories'))} rebuilt and {count(r.get('reused_theories'))} reused from the base; "
            f"{ran} recipes run and {kept} reused, all "
            f"accepted" + (f"; {tests}" if tests else ""))


def harness_validation(tid):
    """The paragraph the harness adds to a task's commit: what its own check of the work found. The owner's commits
    close with their checks' results, and a session writes its message before the harness checks the work — task
    181's review rejected a message that said the landing check "is run by the finalizer" (2026-09-22 15:25). None when
    the check left no report (a task's own command)."""
    o = {}
    with contextlib.suppress(OSError, ValueError):
        o = json.load(open(os.path.join(v2.BUILD, tid, "finalized.json")))
    if o.get("documents"):
        return ("Checked by the harness: the documents check (the sources' structure, THEORY_MAP.md's rows, no conflict "
                "marker) passed.")
    out = o.get("check_output") or (o["reused"][:-4] if str(o.get("reused") or "").endswith(".log") else None)
    said = check_summary(os.path.relpath(out, v2.PROJECT) if out and os.path.isabs(out) else out) if out else None
    if not said:
        return None
    others = [t for t in o.get("batch") or [] if t != tid]
    return ("Checked by the harness: the repository's check of this work with main"
            + (f" and the work of task{'s' if len(others) > 1 else ''} "
               + (others[0] if len(others) == 1 else ", ".join(others[:-1]) + " and " + others[-1]) if others else "")
            + f" {said}.")


def branch_commit(tid, spec, tree, files, own_tree):
    """The task's commit where it works (its branch, or main in the one tree): (the commit's result, the files it
    took), or the finalizer's code once it was refused and said why. A commit that stands on its branch already — a
    landing that did not happen — is taken as it stands: a commit of nothing would fail."""
    files = list(files)
    fill_pending_commit(files, tree)
    stage(files, tree)
    staged = git("diff", "--cached", "--", *files, tree=tree).stdout
    added = "\n".join(l for l in staged.splitlines() if l.startswith("+"))
    braced = dict.fromkeys(BRACED.findall(added))
    if braced:
        v2.log(f"task {tid}'s change writes {', '.join(braced)}; taken as its own words, not as a draft's stand-in")
    left = dict.fromkeys(PLACEHOLDER.findall(added))
    if left:
        git_retrying("reset", "-q", "--", *files, tree=tree)
        return refuse(tid, f"the change still carries the placeholder(s) {', '.join(left)}: what they stand for was "
                      "never filled in, and a commit would put them in the history.")
    if git("diff", "--cached", "--quiet", "--", *files, tree=tree).returncode == 1:  # the task's own change comes
        files += [p for p in ("HANDOFF.md",) if p not in files          # with the planner's state, as before
                  and git("status", "--porcelain", "--", p, tree=tree).stdout.strip()]
        stage(files, tree)
    worse = v2.new_trouble(tree)
    if worse:
        git_retrying("reset", "-q", "--", *files, tree=tree)
        return refuse(tid, "the commit would leave HEAD inconsistent, and every tree made from HEAD would refuse "
                      "every check: " + "; ".join(worse) + ". What the commit declares or imports is committed with "
                      "it — name those files too (`v2.py finalize`), or leave out the line that needs them.")
    # a commit that stands on the task's branch from a landing that did not happen (merge_refused) lands as it stands
    # when its commit is made again: nothing is staged, and a commit of nothing fails. Only the finalizer commits
    # there, so a branch ahead of main holds this task's commit.
    stands = own_tree and git("diff", "--cached", "--quiet", "--", *files, tree=tree).returncode == 0 and git(
        "rev-list", "--count", f"{git('rev-parse', 'HEAD').stdout.strip()}..HEAD", tree=tree).stdout.strip() not in ("", "0")
    message = os.path.join(v2.PROJECT, spec["message"])
    checked = harness_validation(tid)
    if checked and not stands:  # the harness's own check, said by the harness beside the session's words
        text = open(message, errors="ignore").read().rstrip()
        if "Checked by the harness:" not in text:
            message = os.path.join(v2.BUILD, tid, "commit-final.md")
            open(message, "w").write(text + "\n\n" + checked + "\n")
    c = subprocess.CompletedProcess([], 0, "", "") if stands else git_retrying(
        "commit", "-F", message, "--", *files, tree=tree)
    if c.returncode and own_tree:  # nothing moved: said as a failed commit, as before
        error = (c.stdout + c.stderr).strip()[-400:]
        outcome(tid, commit=None, commit_error=error, pushed=False)
        v2.log(f"commit of task {tid}: failed: {error}")
        say(v2.committed, tid, None, error)
        return 1
    return c, files


def put_back_receipts(tid, tree):
    """Receipts a task's own tree holds uncommitted — a `retain` it ran, which only a retention commits
    (v2.receipts_refused) — are put back to its branch's before main is merged in: main's retention writes the same
    files, and git merges nothing over a file changed in the tree. The one tree is left as it is: what stands there
    uncommitted may be a retention that is still to be committed."""
    if os.path.realpath(tree) == os.path.realpath(v2.PROJECT):
        return []
    status = git("status", "--porcelain", "--untracked-files=all", "--", v2.RECEIPTS[0], v2.RECEIPTS[1],
                 tree=tree).stdout.splitlines()
    changed = [line[3:] for line in status if line[:2] != "??" and line[3:]]
    new = [line[3:] for line in status if line[:2] == "??"]
    if changed:
        git("checkout", "HEAD", "--", *changed, tree=tree)
    for path in new:
        with contextlib.suppress(OSError):
            os.remove(os.path.join(tree, path))
    if changed or new:
        v2.log(f"task {tid}: {len(changed) + len(new)} receipt(s) its tree held uncommitted are put back before it lands")
    return changed + new


# land's answer when the check it needs, of the task's work with what landed since, cannot start now: main is let go
# while it waits. It held main through the wait: from 11:24 to 12:23 on 2026-09-22 one landing waited for a heavy run
# while measurements and checks had the machine, and tasks 147 and 132 were refused after sixty minutes each behind it,
# their work whole — and each went to the planner, which queued 147 again to its implementer, for nothing.
MACHINE = "machine"


def land(tid, tree, deadline):
    """Bring main into the task's branch, check the two together when that brought anything, and merge the branch
    into main — None once it has landed, or the finalizer's exit code once it was said why not. main is read again
    before the merge: a commit made outside the finalizer (the owner's) is brought in and checked like any other."""
    put_back_receipts(tid, tree)
    for _ in range(3):
        main = git("rev-parse", "HEAD").stdout.strip()
        before = git("rev-parse", "HEAD", tree=tree).stdout.strip()
        if git("merge-base", "--is-ancestor", main, "HEAD", tree=tree).returncode != 0 \
                and time.time() < deadline and not documents_task(tid) and not machine_free(tid):
            return MACHINE  # what landed would be checked with it, and no heavy run may start now
        m = git("merge", "--no-commit", "--no-ff", main, tree=tree)
        merging = git("rev-parse", "-q", "--verify", "MERGE_HEAD", tree=tree).returncode == 0
        if m.returncode:
            conflicts = [l for l in git("diff", "--name-only", "--diff-filter=U", tree=tree).stdout.splitlines() if l]
            left = imports_agreed(tree, conflicts) if merging and conflicts else conflicts
            if left or not conflicts:
                if merging:
                    if left:
                        keep_marked(tid, tree, left, main)  # for its session, when the task is queued again
                    git("merge", "--abort", tree=tree)
                return merge_refused(tid, left or [(m.stdout + m.stderr).strip()[-300:]])
        if merging:
            rows_agreed(tree)
            c = git("commit", "--no-edit", "-m", f"Bring what landed meanwhile into task {tid}", tree=tree)
            if c.returncode:
                git("merge", "--abort", tree=tree)
                return gate_refused(tid, (c.stdout + c.stderr).strip())
        if git("rev-parse", "HEAD", tree=tree).stdout.strip() != before:  # main held what the check never saw
            worse = v2.new_trouble(tree, "HEAD", main)
            if worse:
                return landing_refused(tid, "together with what landed since its check, its work leaves HEAD "
                                       "inconsistent: " + "; ".join(worse))
            ok, tail = recheck(tid, tree, deadline)
            if not ok:
                return landing_refused(tid, tail)
        if git("rev-parse", "HEAD").stdout.strip() != main:
            continue  # main moved outside the finalizer meanwhile: bring that in too, and check it
        # what stood uncommitted in the one tree was waited for before main was held (committed_run); what came since
        # is named as what it is, not as a conflict of lines
        standing = v2.one_tree_changes(git("diff", "--name-only", main, "HEAD", tree=tree).stdout.split())
        if standing:
            return standing  # committed_run lets main go, waits for them, and lands again
        conflicts = v2.merged(tid)
        return merge_refused(tid, conflicts) if conflicts else None
    return merge_refused(tid, ["(main kept moving while this task landed)"])


# The base and the receipts follow main (the owner, 2026-09-22: the finalizer takes them over). A check rebuilds every
# theory changed since the base and re-runs every recipe whose receipt is stale, and the base moved only when the planner
# placed an advance: right after base d a check rebuilt nothing in seconds, after one landing ~155 theories and 35
# recipes in ~330 s, whatever the task had changed (notes/plan-landing-train.md 1a). A landing's check is of exactly
# the tree that becomes main: it advances the base (its heap stored, in .build/bases/, where no task's sweep reaches),
# and once the task has landed its receipts are retained and committed by the harness. A landing that does not happen
# puts the base back where it was.
ADVANCE = os.environ.get("ORCH_ADVANCE_LANDINGS", "1") == "1"
BASES = os.path.join(".build", "bases")
ADVANCED = {}  # tid: (the check's output, the active base before it) while its landing is under way


def active_pointer():
    v2.keep_pointer_links()  # a check with older tools wrote over the link: carried to the lasting pointer first
    try:
        return open(v2.ACTIVE_CONTEXT).read()
    except OSError:
        return None


def restore_base(before):
    """The active base as it was before a landing check advanced it, that landing not having happened."""
    if before is None:
        return
    pointer = os.path.realpath(v2.ACTIVE_CONTEXT)  # through a link at the old path to where the tools keep it now
    temporary = pointer + ".restore"
    open(temporary, "w").write(before)
    os.replace(temporary, pointer)
    v2.log("the base is back where it was: the landing whose check advanced it did not happen")


def undo_advance(tid):
    if tid in ADVANCED:
        restore_base(ADVANCED.pop(tid)[1])


def record_lineage(tid, out, depth, seconds, ok):
    """What the lineage's depth costs, measured (the owner: its depth decided by data): per landing check, the depth
    of the base it stood on, what it rebuilt and how long each phase took (state/lineage.jsonl)."""
    try:
        summary = json.load(open(os.path.join(v2.PROJECT, out, "incremental.json")))
    except (OSError, ValueError):
        summary = {}
    heap = v2.stored_of(os.path.join(v2.PROJECT, out, "proof")).get("heap")
    entry = {"at": time.strftime("%Y-%m-%dT%H:%M:%S"), "task": tid, "depth": depth, "ok": ok, "seconds": round(seconds),
             "rebuilt": len(summary.get("rebuilt_theories") or []), "phases": summary.get("phases") or {},
             "heap_bytes": os.path.getsize(heap) if heap and os.path.isfile(heap) else None}
    with open(os.path.join(v2.STATE, "lineage.jsonl"), "a") as f:
        f.write(json.dumps(entry) + "\n")


def retain_landed(tid):
    """The receipts of the landing check a task landed with, retained in the one tree and committed by the harness."""
    out, _ = ADVANCED.pop(tid, (None, None))
    if not out:
        return None
    r = subprocess.run([sys.executable, "-B", "tools/incremental_check.py", "retain", "--output", out], cwd=v2.PROJECT,
                       capture_output=True, text=True, timeout=900)
    if r.returncode:
        v2.log(f"ATTENTION the receipts of task {tid}'s landing check were not retained: "
               f"{(r.stderr or r.stdout).strip()[-300:]}")
        return None
    paths = [line[3:].strip() for line in git("status", "--porcelain", "--untracked-files=all", "--",
                                                   *v2.RECEIPTS).stdout.splitlines() if line[3:].strip()]
    if not paths:  # the files it changed, each by name: a pathspec of an empty directory is refused
        return None
    git("add", "--", *paths)
    c = git_retrying("commit", "-q", "-m", f"Retain the recipe receipts of the check task {tid} landed with", "--", *paths)
    if c.returncode:
        git("reset", "-q", "--", *paths)
        v2.log(f"ATTENTION the receipts of task {tid}'s landing check were not committed: "
               f"{(c.stdout + c.stderr).strip()[-300:]}")
        return None
    v2.log(f"the base follows main: task {tid}'s landing check is the base, its receipts retained and committed")
    v2.prune_bases()
    return git("rev-parse", "--short", "HEAD").stdout.strip()


def recheck(tid, tree, deadline):
    """The repository's check of the task's work together with what landed since its check, in its tree: (ok, tail).
    A commit of documents is checked by the documents check, with no machine; any other advances the base (ADVANCE)."""
    d, n = os.path.join(v2.BUILD, tid), 1
    if documents_task(tid):
        ok, tail = documents_check(tree, json.load(open(os.path.join(d, "finalize.json")))["files"])
        open(os.path.join(d, "landing.log"), "w").write(tail + "\n")
        outcome(tid, landing_check=ok, landing_seconds=0)
        v2.log(f"landing check of task {tid}: {'passed' if ok else 'failed'} (its documents with what landed; no machine)")
        return ok, tail
    while os.path.exists(os.path.join(d, f"landing-{n}")):
        n += 1
    wait_for_isabelle(tid, False, end=deadline)
    advancing = ADVANCE and "incremental_check.py check" in v2.LANDING_CHECK
    out = os.path.join(BASES, f"{time.strftime('%Y%m%d-%H%M%S')}-task{tid}") if advancing else \
        f".build/tasks/{tid}/landing-{n}"
    command = v2.LANDING_CHECK.format(output=out) + (" --advance-base" if advancing else "")
    before, depth = active_pointer(), len(v2.base_lineage())
    if advancing:
        os.makedirs(os.path.join(v2.PROJECT, BASES), exist_ok=True)
    v2.log(f"task {tid} lands on what landed since its check: the two are checked together ({command})")
    ok, seconds, tail = run_logged(tid, command, tree, os.path.join(d, "landing.log"))
    outcome(tid, landing_check=ok, landing_seconds=round(seconds))
    v2.log(f"landing check of task {tid}: {'passed' if ok else 'failed'} in {round(seconds)} s")
    if advancing:
        record_lineage(tid, out, depth, seconds, ok)
        if ok:  # the base is this check now (it activates itself): until the landing happens, or is undone
            ADVANCED[tid] = (out, ADVANCED.get(tid, (None, before))[1])
    return ok, tail


def listed(paths, most=12):
    """Paths as a message names them: the first `most`, and how many more. Task 94's merge refusal named its 166
    receipt files one by one to the planner and to its session (2026-09-22 10:03)."""
    paths = list(paths)
    return ", ".join(paths[:most]) + (f" and {len(paths) - most} more" if len(paths) > most else "")


def merge_refused(tid, conflicts, why=None):
    outcome(tid, commit=None, commit_error=f"merge conflict: {listed(conflicts)}")
    v2.log(f"the work of task {tid} is committed on its branch but does not merge: {listed(conflicts)}")
    say(v2.committed, tid, None, f"its commit stands on branch task/{tid} and does not merge into main: " + (why or
        f"{listed(conflicts)} were written in the same place by another task. Its work is whole and nothing is "
        "lost; someone must say which lines stand. Queued again, its session finds each file both sides marked in "
        f".build/tasks/{tid}/merge/, writes it there as it should stand and brings main in (`v2.py bring-main`), which "
        "commits the merge; then it hands over again."))
    return 1


# The index files every task writes merge by union (.gitattributes), which keeps both sides' lines where a three-way
# merge cannot order them: right for two rows added at one place, wrong for a row one side changed next to a row the
# other added — both versions stay. Task 24's branch added its row under Development_Loci's while main changed that
# row, and the merge held it twice (2026-09-21 23:29). Rows are keyed by their theory, and each key is merged as
# three-way merges do: the side that changed it wins, a change made on both sides alike stands once, a row one side
# removed and the other left goes. A key both sides changed otherwise is left as union left it, for the gate to name.
ROW_KEYS = {"THEORY_MAP.md": re.compile(r"^\|\s*([A-Za-z_][\w.]*)\s*\|"),
            "ROOT": re.compile(r"^\s+([A-Za-z_][\w.]*)\s*$")}


def agreed(result, base, ours, theirs, key, ours_had=None, theirs_had=None):
    """The union `result` with each key's rows as a three-way merge of `base`, `ours` and `theirs` has them (lists of
    lines; ROW_KEYS). A row one side holds as the other side once had it (`ours_had`, `theirs_had`: row_history) was
    copied from that side, not changed: the other side's row stands. Task 176's branch held rows its session had
    copied from main by hand, main changed them again, and each was both sides' change — twice in THEORY_MAP.md at its
    landing (2026-09-22 16:21), and its merge of main refused by the gate (q62, 16:50)."""
    def rows(lines):
        out = {}
        for line in lines:
            m = key.match(line)
            if m:
                out.setdefault(m.group(1), []).append(line)
        return out
    b, o, t, r = rows(base), rows(ours), rows(theirs), rows(result)
    drop = {}
    for k, found in r.items():
        sides = [x.get(k, []) for x in (b, o, t)]
        if any(len(s) > 1 for s in sides):
            continue  # a key a side itself holds twice is not this merge's to settle
        vb, vo, vt = (s[0] if s else None for s in sides)
        want = vt if vo == vb else vo if vt == vb or vo == vt else False
        if want is False and vo is not None and vo in (theirs_had or {}).get(k, ()):
            want = vt  # ours holds a row theirs once had: a copy of theirs
        elif want is False and vt is not None and vt in (ours_had or {}).get(k, ()):
            want = vo
        if want is False or found == ([want] if want is not None else []) or (want is not None and want not in found):
            continue  # a conflict for the gate; already one version; or the version wanted is not there to keep
        drop[k] = want
    out, kept = [], set()
    for line in result:
        m = key.match(line)
        k = m.group(1) if m else None
        if k in drop:  # the version wanted, where the row's first version stood; none for a row removed
            if k not in kept and drop[k] is not None:
                out.append(drop[k])
            kept.add(k)
            continue
        out.append(line)
    return out


def row_history(tree, since, rev, path, key):
    """{key: every version of its row the file held on `rev`'s own line since `since`} (its first parents: what that
    side was, commit by commit) — sixteen versions of THEORY_MAP.md on main in the five hours after task 176's
    branch was made, read in a fraction of a second."""
    had = {}
    for commit in git("log", "--first-parent", "--format=%H", f"{since}..{rev}", "--", path, tree=tree).stdout.split():
        for line in git("show", f"{commit}:{path}", tree=tree).stdout.splitlines(keepends=True):
            m = key.match(line)
            if m:
                had.setdefault(m.group(1), set()).add(line)
    return had


# A theory's imports are a list, and two tasks that each add one on the same line conflict as text: task 124's branch
# and main each added an import at the end of Native_Execution_Refinements.thy's import list, the landing was refused,
# and a session was spent putting its import on a line of its own (2026-09-22 08:45). A conflicted theory whose sides
# differ only in their imports is merged as ROOT's and THEORY_MAP.md's rows are (rows_agreed): the rest of the file by
# git's three-way merge, the imports as the names either side added less those either removed.
THEORY_HEAD = re.compile(r"\A(?P<pre>.*?\bimports\b)(?P<imports>.*?)(?P<post>^[ \t]*(?:keywords|abbrevs|begin)\b.*)\Z",
                         re.S | re.M)
IMPORT_NAME = re.compile(r'"[^"]+"|[\w.\-]+')
MARK = " (*harness: imports*)\n"


def imports_agreed(tree, conflicts):
    """The conflicts left once each conflicted theory whose sides differ only in their `imports` is merged there and
    staged (see THEORY_HEAD)."""
    left = []
    for path in conflicts:
        sides = [git("show", f":{stage}:{path}", tree=tree) for stage in (1, 2, 3)]  # the base, ours, theirs
        heads = [THEORY_HEAD.match(x.stdout) for x in sides] if path.endswith(".thy") else []
        if not heads or any(x.returncode for x in sides) or not all(heads):
            left.append(path)
            continue
        with tempfile.TemporaryDirectory() as d:
            files = []
            for name, h in zip(("base", "ours", "theirs"), heads):
                files.append(os.path.join(d, name))
                open(files[-1], "w").write(h.group("pre") + MARK + h.group("post"))
            rest = subprocess.run(["git", "merge-file", "-p", files[1], files[0], files[2]], capture_output=True,
                                  text=True)
        if rest.returncode or rest.stdout.count(MARK) != 1:
            left.append(path)  # the rest of the file conflicts too: that is the file's own
            continue
        base, ours, theirs = (IMPORT_NAME.findall(h.group("imports")) for h in heads)
        gone = (set(base) - set(ours)) | (set(base) - set(theirs))
        text = heads[1].group("imports")
        for name in gone & set(ours):
            text = re.sub(r"(?<![\w.\-\"])" + re.escape(name) + r"(?![\w.\-\"])", "", text)
        indent = (re.findall(r"\n([ \t]+)\S", text) or ["    "])[-1]
        added = [n for n in dict.fromkeys(theirs) if n not in ours and n not in gone]
        text = text.rstrip("\n") + "".join(f"\n{indent}{n}" for n in added) + "\n"
        open(os.path.join(tree, path), "w").write(rest.stdout.replace(MARK, text, 1))
        git("add", "--", path, tree=tree)
        v2.log(f"the merge of what landed into {os.path.relpath(tree, v2.PROJECT)} took both sides' imports of {path}")
    return left


MARKER = re.compile(r"^(?:<<<<<<< |>>>>>>> )", re.M)


def merge_drafts(tid):
    return os.path.join(v2.BUILD, tid, "merge")


def keep_marked(tid, tree, paths, main):
    """Each file of a merge in progress that both sides changed on the same lines, as git leaves it — both sides
    marked — kept under .build/tasks/ID/merge/ for the task's session to write as it should stand (bring_main takes it
    then), with the main it was merged against. A session could not see the conflict at all: it runs no merge, and was
    told to write main's version with its lines in it, which bring-main then refused as uncommitted (implement-94.2,
    task 128's landing, 2026-09-22)."""
    drafts = merge_drafts(tid)
    shutil.rmtree(drafts, ignore_errors=True)
    for path in paths:
        full = os.path.join(tree, path)
        if os.path.isfile(full):
            os.makedirs(os.path.dirname(os.path.join(drafts, path)), exist_ok=True)
            shutil.copyfile(full, os.path.join(drafts, path))
    os.makedirs(drafts, exist_ok=True)
    open(os.path.join(drafts, ".main"), "w").write(main)


def resolved_drafts(tid, main, paths):
    """The conflicted paths the session has written as they should stand (keep_marked), against this main."""
    drafts = merge_drafts(tid)
    try:
        if open(os.path.join(drafts, ".main")).read().strip() != main:
            return []  # main has moved since: what was resolved was resolved against other lines
    except OSError:
        return []
    out = []
    for path in paths:
        try:
            text = open(os.path.join(drafts, path), errors="ignore").read()
        except OSError:
            continue
        if not MARKER.search(text):
            out.append(path)
    return out


def bring_main(tid):
    """Main brought into the branch of a task in its own tree while it works (`v2.py bring-main`, asked by its session):
    work it needs that landed after its tree was made. implement-94 could not check against task 36, which was in main
    and not in its branch, and was told to copy main's text into its tree by hand, since no session merges (q50,
    2026-09-22). It is the merge the landing makes (land): the index rows agreed, a theory's imports merged as a list,
    committed alone — what the session has changed and not committed stays as it is — and refused with what stands in
    the way: main's change of a file the session has changed and not committed, or lines both sides changed."""
    tree = v2.worktree_of(tid)
    if not v2.apart(tid) or tree == v2.PROJECT:
        return "refused: your task works in the one tree, whose files are main's as they stand"
    main = git("rev-parse", "HEAD").stdout.strip()
    if git("merge-base", "--is-ancestor", main, "HEAD", tree=tree).returncode == 0:
        return "main is in your branch already: nothing to bring"
    before = git("rev-parse", "HEAD", tree=tree).stdout.strip()
    aside = set_aside(tid, tree, main)
    try:
        said = merged_in(tid, tree, main)
    except BaseException:
        put_back(tree, aside)
        raise
    if said.startswith("refused"):
        put_back(tree, aside)
        return said
    carried, marked, doubled = carry_back(tree, aside, before, main)
    if aside:
        v2.log(f"task {tid}'s uncommitted changes to {', '.join(aside)}, which main changed too, carried onto the merge"
               + (f" ({', '.join(marked)} with lines both changed marked)" if marked else ""))
    return (said + (f"; your changes to {', '.join(carried + marked)}, which main changed too, are carried onto it, "
                    f"each merged with main's (yours as they were: .build/tasks/{tid}/bring-main/), and the rest of "
                    "what you have changed and not committed stands as it was" if aside else
                    "; what you have changed and not committed stands as it was")
            + (f"; in {', '.join(marked)} both changed the same lines: each place is marked (`<<<<<<< main` … "
               "`>>>>>>> yours`) — write it as it should stand, no marker left" if marked else "")
            + (f"; {'; '.join(doubled)}: keep the one that should stand" if doubled else ""))


def set_aside(tid, tree, main):
    """The session's uncommitted versions of files main changed too, kept under .build/tasks/ID/bring-main/ and taken out
    of the tree (HEAD's version back, or none for a file the session made), so that git merges main: {path: its bytes,
    or None for one it removed}. Refusing them — "main changed X, which your tree has changed and not committed" — told
    the session to copy main's version in by hand (`git show main:PATH`), and a branch that holds main's lines without
    main in its history merges them at its landing as both sides' changes: implement-176 did so at 15:35, main changed
    a row it had copied, and its landing found THEORY_MAP.md holding that row twice (2026-09-22 16:21; task 97 at
    05:23)."""
    keep = os.path.join(v2.BUILD, tid, "bring-main")
    shutil.rmtree(keep, ignore_errors=True)
    base = git("merge-base", "HEAD", main, tree=tree).stdout.strip()
    theirs = set(git("diff", "--name-only", base, main, tree=tree).stdout.splitlines())
    mine = set(git("diff", "--name-only", "HEAD", tree=tree).stdout.splitlines()) | set(
        git("ls-files", "--others", "--exclude-standard", tree=tree).stdout.splitlines())
    aside = {}
    for path in sorted(p for p in mine & theirs if p):
        full = os.path.join(tree, path)
        data = open(full, "rb").read() if os.path.isfile(full) else None
        if data is not None:
            os.makedirs(os.path.dirname(os.path.join(keep, path)), exist_ok=True)
            with open(os.path.join(keep, path), "wb") as f:
                f.write(data)
        aside[path] = data
    for path in aside:
        if git("cat-file", "-e", f"HEAD:{path}", tree=tree).returncode == 0:
            git("checkout", "HEAD", "--", path, tree=tree)
        elif os.path.isfile(os.path.join(tree, path)):
            os.remove(os.path.join(tree, path))
    return aside


def put_back(tree, aside):
    """The session's versions set aside, back in the tree as they were."""
    for path, data in aside.items():
        full = os.path.join(tree, path)
        if data is None:
            with contextlib.suppress(OSError):
                os.remove(full)
            continue
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "wb") as f:
            f.write(data)


def carry_back(tree, aside, before, main):
    """The session's versions set aside, carried onto the merge: each a three-way merge of what its work began from
    (`before`), what the merge left and the session's version — a file merged as a union (.gitattributes) with its
    rows agreed (agreed) — a row the session holds as main once had it being main's —, any other with the lines both
    changed marked. (carried, marked, the rows it holds twice)."""
    carried, marked, doubled = [], [], []
    since = git("merge-base", before, main, tree=tree).stdout.strip()
    for path, mine in aside.items():
        full = os.path.join(tree, path)
        if mine is None:  # the session removed it
            with contextlib.suppress(OSError):
                os.remove(full)
            carried.append(path)
            continue
        base = git("show", f"{before}:{path}", tree=tree).stdout if git(
            "cat-file", "-e", f"{before}:{path}", tree=tree).returncode == 0 else ""
        ours = open(full, errors="surrogateescape").read() if os.path.isfile(full) else ""
        theirs = mine.decode(errors="surrogateescape")
        union = path in ROW_KEYS or "union" in git("check-attr", "merge", "--", path, tree=tree).stdout.split(": ")[-1]
        with tempfile.TemporaryDirectory() as d:
            files = []
            for name, text in (("main", ours), ("before", base), ("yours", theirs)):
                files.append(os.path.join(d, name))
                with open(files[-1], "w", errors="surrogateescape") as f:
                    f.write(text)
            r = subprocess.run(["git", "merge-file", "-p"] + (["--union"] if union else [])
                               + ["-L", "main", "-L", "before", "-L", "yours"] + files, capture_output=True)
        text = r.stdout.decode(errors="surrogateescape")
        key = ROW_KEYS.get(path)
        if key:
            lines = lambda t: t.splitlines(keepends=True)
            text = "".join(agreed(lines(text), lines(base), lines(ours), lines(theirs), key,
                                  row_history(tree, since, main, path, key)))
            counts = {}
            for line in lines(text):
                k = key.match(line)
                if k:
                    counts[k.group(1)] = counts.get(k.group(1), 0) + 1
            twice = [k for k, n in counts.items() if n > 1]
            if twice:
                doubled.append(f"{path} holds main's and your version of {', '.join(twice)}")
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "w", errors="surrogateescape") as f:
            f.write(text)
        (marked if r.returncode > 0 and not union else carried).append(path)
    return carried, marked, doubled


def merged_in(tid, tree, main):
    """Main merged into the branch in `tree` and committed, as the landing merges it: what bring_main says, or why it
    was refused (nothing brought)."""
    m = git("merge", "--no-commit", "--no-ff", main, tree=tree)
    merging = git("rev-parse", "-q", "--verify", "MERGE_HEAD", tree=tree).returncode == 0
    resolved = []
    if m.returncode:
        conflicts = [l for l in git("diff", "--name-only", "--diff-filter=U", tree=tree).stdout.splitlines() if l]
        left = imports_agreed(tree, conflicts) if merging and conflicts else conflicts
        if left and merging:  # what the session has written as it should stand, from the marked drafts
            resolved = resolved_drafts(tid, main, left)
            for path in resolved:
                shutil.copyfile(os.path.join(merge_drafts(tid), path), os.path.join(tree, path))
                git("add", "--", path, tree=tree)
            left = [p for p in left if p not in resolved]
            if left:
                keep_marked(tid, tree, left, main)
        if left or not conflicts:
            if merging:
                git("merge", "--abort", tree=tree)
            said = (m.stdout + m.stderr).strip()
            mine = re.findall(r"^\t(\S.*)$", said, re.M)
            if mine:  # what set_aside did not take: never copied in by hand, which leaves main out of the history
                return ("refused: main changed " + ", ".join(mine) + ", which your tree has changed (or made) and not "
                        "committed, and it could not be set aside; nothing was brought. Go on: the landing merges "
                        "them. Do not copy main's version in by hand — a branch holding main's lines without main in "
                        "its history lands them as its own changes.")
            where = os.path.relpath(merge_drafts(tid), v2.PROJECT)
            return ("refused: main and your branch changed the same lines of " + (listed(left) if left else said[-300:])
                    + f"; nothing was brought. Each is in {where}/ as git merges it, both sides marked (`<<<<<<< "
                    "HEAD` yours, `>>>>>>>` main's): write each there as it should stand — main's lines with yours, no "
                    "marker left — with `v2.py change`, and ask again: bring-main then takes them for those files and "
                    "commits the merge.")
    if merging:
        rows_agreed(tree)
        c = git("commit", "--no-edit", "-m", f"Bring main into task {tid}", tree=tree)
        if c.returncode:
            git("merge", "--abort", tree=tree)
            return "refused: the merge would not stand as a commit: " + (c.stdout + c.stderr).strip()[-600:]
    if resolved:
        shutil.rmtree(merge_drafts(tid), ignore_errors=True)
    v2.log(f"main ({main[:8]}) brought into task {tid}'s branch, asked by its session"
           + (f", with its resolution of {', '.join(resolved)}" if resolved else ""))
    return f"main ({main[:8]}) is in your branch now" + (f", with your {', '.join(resolved)}" if resolved else "")


def rows_agreed(tree):
    """The index files of a merge in progress in `tree`, their rows agreed (agreed) and staged."""
    base = git("merge-base", "HEAD", "MERGE_HEAD", tree=tree).stdout.strip()
    for path, key in ROW_KEYS.items():
        full = os.path.join(tree, path)
        if not os.path.exists(full):
            continue
        if git("diff", "--quiet", base, "HEAD", "--", path, tree=tree).returncode == 0 or \
                git("diff", "--quiet", base, "MERGE_HEAD", "--", path, tree=tree).returncode == 0:
            # one side alone changed it: git's merge of it is exact, and a union's doubled rows cannot be there. Read
            # anyway, the file in the tree was the session's uncommitted one — implement-139's new ROOT line and
            # THEORY_MAP row were dropped as rows of neither side, and the rest of its edits staged into the merge
            # commit, by bring-main (2026-09-22 10:05)
            continue
        side = lambda rev: git("show", f"{rev}:{path}", tree=tree).stdout.splitlines(keepends=True)
        result = open(full).read().splitlines(keepends=True)
        out = agreed(result, side(base), side("HEAD"), side("MERGE_HEAD"), key,
                     row_history(tree, base, "HEAD", path, key), row_history(tree, base, "MERGE_HEAD", path, key))
        if out != result:
            open(full, "w").write("".join(out))
            git("add", "--", path, tree=tree)
            v2.log(f"the merge of what landed into {os.path.relpath(tree, v2.PROJECT)} kept one version of each row "
                   f"of {path} both sides touched")


def gate_refused(tid, said, beside=()):
    """Brought together with what landed since its branch was made, its work leaves HEAD with trouble (commit_gate):
    what the gate found, whole — it was cut to git's last 300 characters and called lines "written in the same place
    by another task" (task 24, 2026-09-21)."""
    found = [l.strip()[2:] for l in said.splitlines() if l.strip().startswith("- ")] or [said[:1000]]
    outcome(tid, commit=None, commit_error="with what landed since: " + "; ".join(found))
    v2.log(f"the work of task {tid} does not stand with what landed since its branch was made: {'; '.join(found)}")
    say(v2.committed, tid, None, f"its commit stands on branch task/{tid}, and brought together with what landed since "
        "its branch was made" + (f" and with task{'s' if len(beside) > 1 else ''} {', '.join(beside)}, landing beside "
                                 "it," if beside else "") + " it leaves: " + "; ".join(found) + ". Its work is whole. A session of it makes the two "
        f"agree in its tree and hands over again: say so in its brief, and queue it (`v2.py queue {tid}`).")
    return 1


def landing_refused(tid, tail):
    outcome(tid, commit=None, commit_error="its work does not stand with what landed since its check")
    v2.log(f"task {tid} does not land: its work does not stand with what landed since its check")
    say(v2.landing_failed, tid, tail)
    return 1


if __name__ == "__main__":
    if sys.argv[1:] == ["land-queue"]:
        import train
        sys.exit(train.land_waiting())
    if sys.argv[1:] == ["check-batch"]:
        import train
        sys.exit(train.check_waiting())
    if len(sys.argv) != 3 or sys.argv[1] not in ("check", "commit"):
        print(__doc__)
        sys.exit(2)
    sys.exit((check if sys.argv[1] == "check" else commit)(sys.argv[2]))
