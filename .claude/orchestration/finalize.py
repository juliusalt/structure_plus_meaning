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


def git(*args, timeout=120, tree=None):
    """A git command in a tree (the task's own where it has one); a failure or its timeout is a result with a return
    code, never an exception."""
    try:
        return subprocess.run(["git", "-C", tree or v2.PROJECT, *args], capture_output=True, text=True, timeout=timeout,
                              env=GIT_ENV)
    except (subprocess.TimeoutExpired, OSError) as e:
        return subprocess.CompletedProcess(args, 124, "", f"git {' '.join(args[:2])}: {e}")


def git_retrying(*args, tree=None):
    """A git command that changes the index, tried again while another git process holds its lock."""
    for _ in range(10):
        r = git(*args, tree=tree)
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


def wait_for_isabelle(tid, exclusive, end=None):
    """A check that advances the base heap waits until no Isabelle runs and holds the machine meanwhile; any other waits
    for a free run (v2.ISABELLE_MAX) and for no advancing check. It waits at most WAIT_MAX seconds (or until `end`),
    then runs anyway."""
    end = end or time.time() + WAIT_MAX
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


def run_logged(tid, command, cwd, log):
    """Run a check command in `cwd` with its output in `log`, its process group registered for the watchdog: (ok,
    seconds, the log's last 30 lines)."""
    d, started = os.path.join(v2.BUILD, tid), time.time()
    with open(log, "w") as out:
        run = subprocess.Popen(command, shell=True, cwd=cwd, stdout=out, stderr=subprocess.STDOUT,
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
    return ok, time.time() - started, "\n".join(open(log, errors="ignore").read().splitlines()[-30:])


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


def run_check(tid, d, spec):
    import work_meter
    cwd = v2.worktree_of(tid)
    # run to its end and ending with every error it reported, as a session's check does: the quick fix that follows
    # a failed one is given the log's end, which then holds them all (2026-09-21); a long list is kept in the task's
    # run-errors/, which is a run's output and no draft
    check = work_meter.gathering(fresh_output(tid, spec["check"], cwd), cwd, os.path.join(d, "run-errors"))
    ok, seconds, tail = run_logged(tid, check, cwd, os.path.join(d, "finalize.log"))
    outcome(tid, ok=ok, seconds=round(seconds))
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


def unreviewed_work(tid, files):
    """{file: task} of what this commit would carry that no review has accepted: the task's own work while its reviews
    have not all accepted it, and any other task's work in the files. Task 52 was planned to commit four tasks' work
    in one commit with their reviews to follow; a commit is what a review decides, so it comes after."""
    st = v2.peek()
    with v2.owners(write=False) as o:
        marked = {f: o.get(os.path.normpath(f)) or tid for f in files}
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
    unreviewed = unreviewed_work(tid, files)
    if unreviewed:
        return refuse(tid, "a task's work is committed after its review has accepted it, never before (the owner, "
                      "2026-09-21), and this commit would carry work no review has accepted: "
                      + ", ".join(f"{f} (task {t})" for f, t in unreviewed.items()) + ". Each lands by its own "
                      "check, review and commit.")
    with v2.landing(deadline) as held:
        if not held:
            return refuse(tid, f"other landings held main for {WAIT_MAX // 60} minutes, so this one did not begin; "
                          "its work is whole and its commit can be made again")
        LANDING.append([])
        try:
            code = commit_and_land(tid, spec, tree, files, own_tree, deadline)
        finally:
            later = LANDING.pop()
    for report, args in later:  # after main is let go: a report dispatches, and a dispatch may begin the next landing
        report(*args)
    return code


LANDING = []  # while a landing holds main: the reports it owes, made once it has let main go


def say(report, *args):
    """A report to the harness (v2.committed, v2.landing_failed): at once, or once the landing in progress is over."""
    if LANDING:
        LANDING[-1].append((report, args))
    else:
        report(*args)


def commit_and_land(tid, spec, tree, files, own_tree, deadline):
    fill_pending_commit(files, tree)
    git_retrying("add", "--", *files, tree=tree)
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
        git_retrying("add", "--", *files, tree=tree)
    worse = v2.new_trouble(tree)
    if worse:
        git_retrying("reset", "-q", "--", *files, tree=tree)
        return refuse(tid, "the commit would leave HEAD inconsistent, and every tree made from HEAD would refuse "
                      "every check: " + "; ".join(worse) + ". What the commit declares or imports is committed with "
                      "it — name those files too (`v2.py finalize`), or leave out the line that needs them.")
    c = git_retrying("commit", "-F", os.path.join(v2.PROJECT, spec["message"]), "--", *files, tree=tree)
    ref = git("rev-parse", "--short", "HEAD", tree=tree).stdout.strip() if c.returncode == 0 else None
    if ref and own_tree:  # its branch meets what landed meanwhile, line by line, and is checked with it
        failed = land(tid, tree, deadline)
        if failed is not None:
            return failed
        ref = git("rev-parse", "--short", "HEAD").stdout.strip()
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


def land(tid, tree, deadline):
    """Bring main into the task's branch, check the two together when that brought anything, and merge the branch
    into main — None once it has landed, or the finalizer's exit code once it was said why not. main is read again
    before the merge: a commit made outside the finalizer (the owner's) is brought in and checked like any other."""
    for _ in range(3):
        main = git("rev-parse", "HEAD").stdout.strip()
        before = git("rev-parse", "HEAD", tree=tree).stdout.strip()
        m = git("merge", "--no-edit", "-m", f"Bring what landed meanwhile into task {tid}", main, tree=tree)
        if m.returncode:
            conflicts = [l for l in git("diff", "--name-only", "--diff-filter=U", tree=tree).stdout.splitlines() if l]
            git("merge", "--abort", tree=tree)
            return merge_refused(tid, conflicts or [(m.stdout + m.stderr).strip()[-300:]])
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
        conflicts = v2.merged(tid)
        return merge_refused(tid, conflicts) if conflicts else None
    return merge_refused(tid, ["(main kept moving while this task landed)"])


def recheck(tid, tree, deadline):
    """The repository's check of the task's work together with what landed since its check, in its tree: (ok, tail)."""
    d, n = os.path.join(v2.BUILD, tid), 1
    while os.path.exists(os.path.join(d, f"landing-{n}")):
        n += 1
    wait_for_isabelle(tid, False, end=deadline)
    command = v2.LANDING_CHECK.format(output=f".build/tasks/{tid}/landing-{n}")
    v2.log(f"task {tid} lands on what landed since its check: the two are checked together ({command})")
    ok, seconds, tail = run_logged(tid, command, tree, os.path.join(d, "landing.log"))
    outcome(tid, landing_check=ok, landing_seconds=round(seconds))
    v2.log(f"landing check of task {tid}: {'passed' if ok else 'failed'} in {round(seconds)} s")
    return ok, tail


def merge_refused(tid, conflicts):
    outcome(tid, commit=None, commit_error=f"merge conflict: {', '.join(conflicts)}")
    v2.log(f"the work of task {tid} is committed on its branch but does not merge: {', '.join(conflicts)}")
    say(v2.committed, tid, None, f"its commit stands on branch task/{tid} and does not merge into main: "
        f"{', '.join(conflicts)} were written in the same place by another task. Its work is whole and nothing is "
        "lost; someone must say which lines stand.")
    return 1


def landing_refused(tid, tail):
    outcome(tid, commit=None, commit_error="its work does not stand with what landed since its check")
    v2.log(f"task {tid} does not land: its work does not stand with what landed since its check")
    say(v2.landing_failed, tid, tail)
    return 1


if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[1] not in ("check", "commit"):
        print(__doc__)
        sys.exit(2)
    sys.exit((check if sys.argv[1] == "check" else commit)(sys.argv[2]))
