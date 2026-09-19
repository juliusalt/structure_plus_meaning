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
    if exclusive:
        open(os.path.join(v2.STATE, "isabelle-exclusive"), "w").write(tid)


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
    outcome(tid, ok=ok, seconds=round(time.time() - started))
    tail = "\n".join(open(os.path.join(d, "finalize.log"), errors="ignore").read().splitlines()[-30:])
    v2.log(f"check of task {tid}: " + ("passed" if ok else "failed"))
    v2.checked(tid, ok, tail)
    return 0 if ok else 1


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
    git_retrying("add", "--", *files)
    if git("diff", "--cached", "--quiet", "--", *files).returncode == 1:  # the task's own change comes with the state
        files += [p for p in ("HANDOFF.md",) if p not in files and git("status", "--porcelain", "--", p).stdout.strip()]
        git_retrying("add", "--", *files)
    c = git_retrying("commit", "-F", os.path.join(v2.PROJECT, spec["message"]), "--", *files)
    ref = git("rev-parse", "--short", "HEAD").stdout.strip() if c.returncode == 0 else None
    if ref:
        with v2.owners() as o:  # committed: no longer anyone's uncommitted change
            for f in files:
                o.pop(os.path.normpath(f), None)
    error = None if c.returncode == 0 else (c.stdout + c.stderr).strip()[-400:]
    p = git("push", "origin", "HEAD", timeout=180) if ref else None
    pushed = bool(p and p.returncode == 0)
    outcome(tid, commit=ref, commit_error=error, pushed=pushed)
    v2.log(f"commit of task {tid}: " + (ref or f"failed: {error}") + ("" if pushed or not ref else " (the push failed)"))
    v2.committed(tid, ref and ref + ("" if pushed else " (the push failed)"), error)
    return 0 if ref else 1


if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[1] not in ("check", "commit"):
        print(__doc__)
        sys.exit(2)
    sys.exit((check if sys.argv[1] == "check" else commit)(sys.argv[2]))
