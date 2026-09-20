#!/usr/bin/env python3
"""The finalizer of a task: no model, only the task's final job, in two parts around its review.

  finalize.py check ID    run the acceptance check of .build/tasks/ID/finalize.json (output in finalize.log) once
                          Isabelle has room (a check that advances the base heap waits until nothing else runs and
                          holds the machine); the task goes to its review when it passes, to a quick fix when it
                          fails the first time, to the planner when it fails again (v2.checked)
  finalize.py commit ID   after the verdict accepted it: commit the named files with the session's message and push
                          (v2.committed)

The outcome is recorded in .build/tasks/ID/finalized.json, which efficiency.py credits to the task's session.
"""
import contextlib
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

TIMEOUT = int(os.environ.get("ORCH_FINAL_MAX", 3600))
WAIT_MAX = int(os.environ.get("ORCH_ISABELLE_WAIT", 3600))
POLL = float(os.environ.get("ORCH_ISABELLE_POLL", 15))
RAN_MIN = float(os.environ.get("ORCH_CHECK_MIN", 20))  # under this, a failure with a tool's own complaint never ran
NOT_RUN = re.compile(r"Traceback \(most recent call last\)|^usage:|unrecognized arguments|No such file or directory"
                     r"|command not found|: not found$", re.M)


GIT_ENV = dict(os.environ, GIT_TERMINAL_PROMPT="0")  # never a credentials prompt


def git(*args, timeout=120):
    """A git command; a failure (or its timeout) is a result with a return code, never an exception."""
    try:
        return subprocess.run(["git", "-C", v2.PROJECT, *args], capture_output=True, text=True, timeout=timeout,
                              env=GIT_ENV)
    except (subprocess.TimeoutExpired, OSError) as e:
        return subprocess.CompletedProcess(args, 124, "", f"git {' '.join(args[:2])}: {e}")


def git_retrying(*args):
    """A git command that changes the index, tried again while another git process holds its lock."""
    for _ in range(10):
        r = git(*args)
        if r.returncode == 0 or "index.lock" not in r.stderr:
            return r
        time.sleep(2)
    return r


def outcome(tid, **fields):
    path = os.path.join(v2.BUILD, tid, "finalized.json")
    try:
        o = json.load(open(path))
    except (OSError, ValueError):
        o = {}
    o.update(fields)
    json.dump(o, open(path, "w"), indent=1)
    return o


def wait_for_isabelle(tid, exclusive):
    """A check that advances the base heap waits until no Isabelle runs and holds the machine meanwhile; any other waits
    for a free run (v2.ISABELLE_MAX) and for no advancing check. It waits at most WAIT_MAX seconds, then runs anyway."""
    end = time.time() + WAIT_MAX
    while time.time() < end:
        holder, runs = v2.exclusive_holder(), v2.isabelle_runs()
        if not holder and (runs == 0 if exclusive else runs < v2.ISABELLE_MAX):
            break
        time.sleep(POLL)
    if exclusive:  # with the process that holds it, so that a claim cannot outlive its check (v2.exclusive_claim)
        v2.claim_exclusive(tid, "its final check advances the base heap", pid=os.getpid())


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
        with contextlib.suppress(OSError):
            os.remove(mark)


def checked_run(tid):
    d = os.path.join(v2.BUILD, tid)
    spec = json.load(open(os.path.join(d, "finalize.json")))
    trouble = v2.tree_trouble()
    if trouble:  # every check refuses on this, whatever the task did: spend none of it, and cost the task no round
        tail = "The working tree refuses every check as it stands, whatever this task did:\n- " + "\n- ".join(trouble)
        open(os.path.join(d, "finalize.log"), "w").write(tail + "\n")
        outcome(tid, ok=False, seconds=0)
        v2.log(f"check of task {tid}: not run, the working tree is inconsistent")
        v2.tree_checked("the harness", f"task {tid}'s check was about to run")
        v2.checked(tid, False, tail, ran=False)
        return 1
    exclusive = bool(v2.ADVANCES.search(spec["check"]))
    wait_for_isabelle(tid, exclusive)
    try:
        # the check sees the working tree, which holds this task's changes alone: while a finalization is in flight,
        # every other session writes only under .build/ (v2.tree_holder, the guard)
        return run_check(tid, d, spec)
    finally:
        if exclusive:
            with contextlib.suppress(OSError):
                os.remove(os.path.join(v2.STATE, "isabelle-exclusive"))


def run_check(tid, d, spec):
    started = time.time()
    with open(os.path.join(d, "finalize.log"), "w") as out:
        run = subprocess.Popen(spec["check"], shell=True, cwd=v2.PROJECT, stdout=out, stderr=subprocess.STDOUT,
                               start_new_session=True)
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
    seconds = time.time() - started
    outcome(tid, ok=ok, seconds=round(seconds))
    tail = "\n".join(open(os.path.join(d, "finalize.log"), errors="ignore").read().splitlines()[-30:])
    # a check that exits at once with a tool's own complaint never ran: the command is wrong, not the work
    ran = bool(ok) or seconds >= RAN_MIN or not NOT_RUN.search(tail)
    v2.log(f"check of task {tid}: " + ("passed" if ok else "failed" if ran else "did not run (the command is not "
                                       "runnable as written)"))
    v2.checked(tid, ok, tail, ran=ran)
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


def fill_pending_commit(files):
    """An entry closes with ``Recorded <date>, commit `…`.`` and no session can fill that hash before its own commit
    exists, so the commit that makes it records which entry it left open (record_pending_commit) and the next commit
    touching the file closes it. The hash is never guessed from the file's history: `git blame` follows the line's
    text, and a line restored to wording an earlier commit used is attributed to that commit, which once closed an
    entry with a commit carrying none of what it records (2026-09-20)."""
    path, mark = os.path.join(v2.PROJECT, "DECISIONS.md"), os.path.join(v2.STATE, PENDING)
    if "DECISIONS.md" not in files:
        return []
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


def record_pending_commit(files, ref):
    """This commit carries an entry that still ends in `…`: the next commit touching the file closes it with this
    hash, which is the commit that carries what the entry records."""
    if "DECISIONS.md" not in files or not ref:
        return
    try:
        lines = open(os.path.join(v2.PROJECT, "DECISIONS.md"), errors="ignore").read().splitlines()
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
    with v2.owners() as o:
        marked = {f: o.get(os.path.normpath(f)) for f in files}
    return {f: t for f, t in marked.items() if t and t != tid
            and (v2.read_task(t) or {}).get("status") not in ("completed", None)}


def refuse(tid, why):
    outcome(tid, ok=False, commit=None, commit_error=why)
    v2.log(f"commit of task {tid} refused: {why}")
    v2.committed(tid, None, why)
    return 1


def commit(tid):
    mark = alive(tid)
    try:
        return committed_run(tid)
    finally:
        with contextlib.suppress(OSError):
            os.remove(mark)


def committed_run(tid):
    """The task's files, and the planner's state as it stands (HANDOFF.md, committed with every task as before)."""
    d = os.path.join(v2.BUILD, tid)
    spec = json.load(open(os.path.join(d, "finalize.json")))
    files = list(spec["files"])
    theirs = foreign(tid, files)
    if theirs:
        return refuse(tid, "the commit would carry another task's uncommitted work: "
                      + ", ".join(f"{f} (task {t})" for f, t in theirs.items())
                      + ". That task installs and commits its own change; this one commits the rest.")
    fill_pending_commit(files)
    git_retrying("add", "--", *files)
    staged = git("diff", "--cached", "--", *files).stdout
    added = "\n".join(l for l in staged.splitlines() if l.startswith("+"))
    braced = dict.fromkeys(BRACED.findall(added))
    if braced:
        v2.log(f"task {tid}'s change writes {', '.join(braced)}; taken as its own words, not as a draft's stand-in")
    left = dict.fromkeys(PLACEHOLDER.findall(added))
    if left:
        git_retrying("reset", "-q", "--", *files)
        return refuse(tid, f"the change still carries the placeholder(s) {', '.join(left)}: what they stand for was "
                      "never filled in, and a commit would put them in the history.")
    if git("diff", "--cached", "--quiet", "--", *files).returncode == 1:  # the task's own change comes with the state
        files += [p for p in ("HANDOFF.md",) if p not in files and git("status", "--porcelain", "--", p).stdout.strip()]
        git_retrying("add", "--", *files)
    c = git_retrying("commit", "-F", os.path.join(v2.PROJECT, spec["message"]), "--", *files)
    ref = git("rev-parse", "--short", "HEAD").stdout.strip() if c.returncode == 0 else None
    if ref:
        with v2.owners() as o:  # committed: no longer anyone's uncommitted change
            for f in files:
                o.pop(os.path.normpath(f), None)
    if ref:
        record_pending_commit(files, ref)
    error = None if c.returncode == 0 else (c.stdout + c.stderr).strip()[-400:]
    p = git("push", "origin", "HEAD", timeout=180) if ref else None
    pushed = bool(p and p.returncode == 0)
    outcome(tid, commit=ref, commit_error=error, pushed=pushed)
    if ref:
        v2.tree_checked(f"task {tid}", "its commit")
    v2.log(f"commit of task {tid}: " + (ref or f"failed: {error}") + ("" if pushed or not ref else " (the push failed)"))
    v2.committed(tid, ref and ref + ("" if pushed else " (the push failed)"), error)
    return 0 if ref else 1


if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[1] not in ("check", "commit"):
        print(__doc__)
        sys.exit(2)
    sys.exit((check if sys.argv[1] == "check" else commit)(sys.argv[2]))
