"""Landing trains (notes/plan-landing-train.md 3). A finalizer commits an accepted task on its own branch and queues it
to land; one lander at a time takes every task waiting as one train, merges their branches onto main in an integration
tree in the planner's order, checks the combination once, and moves main once, to exactly what it checked.

Until 2026-09-22 every landing rechecked its own task with what had landed before it, one after another, about five
minutes each on a heavy slot: 38 such rechecks that day, 37 of them passing, and a landing waited for every landing
before it. A combination that fails is resolved by attribution from the check's own report and by bisection on both
heavy slots, never task by task (the owner: "if we allow it to fallback to linear then it becomes the same problem");
what did not fail lands without waiting on what did."""
import contextlib
import fcntl
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import v2  # noqa: E402
import check_errors  # noqa: E402
import finalize as fz  # noqa: E402

ON = os.environ.get("ORCH_TRAINS", "1") == "1"
BATCHES = os.environ.get("ORCH_BATCHES", "1") == "1"  # checks batched across tasks (notes/plan-landing-train.md 1b)
QUEUE = os.path.join(v2.STATE, "landing-queue.json")
KEEP = 3600  # a decided entry stays this long, for the finalizer that waits on it
TREES = ("train-a", "train-b")  # the integration trees, one per heavy slot (v2.trees_standing leaves them be)
LOGS = os.path.join(v2.BUILD, "trains")
LOCK_TRY = float(os.environ.get("ORCH_TRAIN_LOCK_TRY", 5))  # how long a waiting finalizer tries for main at a time
LANDER = os.path.join(v2.STATE, "lander.pid")
PASSED = {}  # (main, ((task, head), ...)): (the checked head, its check's output) — checked once, whatever the wait


# ---------------------------------------------------------------- the queues

class Queue:
    """A queue of tasks waiting for a combination — to land (the landing queue) or to be checked (the check queue):
    {task: entry}, read and written under its own lock (neither is main's). A decided entry stays KEEP for the
    finalizer or session that waits on it."""

    def __init__(self, path):
        self.path = path

    @contextlib.contextmanager
    def open(self):
        with open(self.path + ".lock", "a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            try:
                q = json.load(open(self.path))
            except (OSError, ValueError):
                q = {}
            yield q
            now = time.time()
            q = {t: e for t, e in q.items() if not e.get("decided") or now - e["decided"] < KEEP}
            tmp = self.path + ".tmp"
            json.dump(q, open(tmp, "w"), indent=1)
            os.replace(tmp, self.path)

    def peek(self):
        try:
            return json.load(open(self.path))
        except (OSError, ValueError):
            return {}

    def put(self, tid, **entry):
        with self.open() as q:
            q[tid] = dict(entry, queued=time.time())

    def decide(self, tid, code, what, **fields):
        with self.open() as q:
            e = q.get(tid)
            if e is not None and not e.get("decided"):
                e.update(decided=time.time(), code=code, what=what, **fields)

    def decision(self, tid):
        e = self.peek().get(tid)
        return e if e and e.get("decided") else None

    def queued(self, tid):
        e = self.peek().get(tid)
        return bool(e) and not e.get("decided")

    def mark(self, members, known_fail, log=None):
        """What a lander has found of these members, kept for the next if its budget ends before they are decided."""
        with self.open() as q:
            for tid in members:
                if tid in q and not q[tid].get("decided"):
                    q[tid].update(known_fail=known_fail, fail_log=log if known_fail else None)

    def waiting(self, stands):
        """The undecided entries in the planner's order (its queue, then how long each has waited): [(task, entry)].
        One whose task no longer `stands` (dropped, re-planned) leaves the queue unsaid: it is the planner's."""
        st = v2.peek()
        order = st.get("queue") or []
        out = []
        with self.open() as q:
            for tid, e in list(q.items()):
                if e.get("decided"):
                    continue
                if not stands(tid, e, st):
                    del q[tid]
                    v2.log(f"task {tid} left the {os.path.basename(self.path)[:-5].replace('-', ' ')}: it no longer "
                           "waits for it")
                    continue
                out.append((tid, e))
        return sorted(out, key=lambda x: (order.index(x[0]) if x[0] in order else len(order), x[1]["queued"]))


LANDING_QUEUE = Queue(QUEUE)
peek, decision, queued, mark = LANDING_QUEUE.peek, LANDING_QUEUE.decision, LANDING_QUEUE.queued, LANDING_QUEUE.mark


def enqueue(tid, head, documents):
    LANDING_QUEUE.put(tid, head=head, documents=documents)


def decide(tid, code, what, ref=None):
    LANDING_QUEUE.decide(tid, code, what, ref=ref)


def committing(tid, e, st):
    return (st["tasks"].get(tid) or {}).get("stage") == "committing"


def waiting():
    return LANDING_QUEUE.waiting(committing)


def listing(tids):
    tids = list(tids)
    return tids[0] if len(tids) == 1 else ", ".join(tids[:-1]) + " and " + tids[-1]


# ---------------------------------------------------------------- the integration trees

def integration(name, at):
    """An integration tree at `at`: a detached worktree of the repository, made once and reset for each use, with the
    one .build linked in as every task's tree has it (v2.build_link)."""
    path = os.path.join(v2.PROJECT, v2.TREE_DIR, name)
    if not (os.path.isfile(os.path.join(path, ".git")) or os.path.isdir(os.path.join(path, ".git"))):
        fz.git("worktree", "prune")
        r = fz.git("worktree", "add", "--detach", "-f", path, at)
        if r.returncode:
            raise RuntimeError(f"git could not make the integration tree {name}: {(r.stdout + r.stderr).strip()[-300:]}")
    else:
        fz.git("merge", "--abort", tree=path)
        fz.git("reset", "-q", "--hard", at, tree=path)
        fz.git("clean", "-fdq", tree=path)
    v2.build_link(path)
    return path


def head(tree=None):
    return fz.git("rev-parse", "HEAD", tree=tree).stdout.strip()


def take_up(tree, tid, ref, main, beside):
    """A member's branch merged into the integration tree, as its own landing merged it (imports as a list, the index
    rows agreed): None once committed ("Take up the work of task N"), or the finalizer's code once it was said why it
    cannot be — its lines conflict (kept marked for its session, keep_marked) or the gate finds trouble."""
    m = fz.git("merge", "--no-ff", "--no-commit", ref, tree=tree)
    merging = fz.git("rev-parse", "-q", "--verify", "MERGE_HEAD", tree=tree).returncode == 0
    if m.returncode:
        conflicts = [l for l in fz.git("diff", "--name-only", "--diff-filter=U", tree=tree).stdout.splitlines() if l]
        left = fz.imports_agreed(tree, conflicts) if merging and conflicts else conflicts
        if left or not conflicts:
            if merging and left:
                fz.keep_marked(tid, tree, left, main)  # for its session, when the task is queued again
            fz.git("merge", "--abort", tree=tree)
            return fz.merge_refused(tid, left or [(m.stdout + m.stderr).strip()[-300:]])
    if not merging:
        return None  # nothing of it that main does not hold already
    fz.rows_agreed(tree)
    c = fz.git("commit", "--no-edit", "-m", f"Take up the work of task {tid}", tree=tree)
    if c.returncode:
        fz.git("merge", "--abort", tree=tree)
        return fz.gate_refused(tid, (c.stdout + c.stderr).strip(), beside)
    return None


class Plan:
    """A combination to check: members merged onto main (or stacked onto another plan's head) in one tree."""

    def __init__(self, members, stacked=None):
        self.members, self.stacked = list(members), stacked
        self.tree = self.head = self.out = self.log = self.tail = None
        self.ok, self.seconds, self.checked, self.kind, self.broken = None, 0, False, None, None
        self.reused = False  # it lands on its check batch's kept build of the same content (C10)


def assemble(plan, name, main, entries):
    """Merge a plan's members into its integration tree; the members that cannot be are decided (said) and left out."""
    at = plan.stacked.head if plan.stacked else main
    plan.tree = integration(name, at)
    taken = list(plan.stacked.members) if plan.stacked else []
    for tid in [t for t in plan.members if t not in taken]:
        code = take_up(plan.tree, tid, entries[tid]["head"], main, [t for t in taken])
        if code is None:
            taken.append(tid)
        else:
            decide(tid, code, "refused")
    plan.members = taken
    plan.head = head(plan.tree)


def changed(main, ref):
    """The files a member changes, since where its branch left main."""
    return [f for f in fz.git("diff", "--name-only", f"{main}...{ref}").stdout.splitlines() if f]


# ---------------------------------------------------------------- one check of a combination

def check(plan, main, entries):
    """The repository's check of a plan's tree: the documents check alone when every member is documents only; else
    the documents check of what the members' documents became together (their conflict markers, THEORY_MAP.md's
    rows: nothing else checks them) and then LANDING_CHECK, advancing the base (the base follows main). A plan of one
    member whose branch holds main already is what its own check saw: nothing is checked again."""
    if len(plan.members) == 1 and fz.git("merge-base", "--is-ancestor", main, entries[plan.members[0]]["head"]
                                         ).returncode == 0 and not plan.stacked:
        plan.ok = True
        return
    plan.checked = True
    stamp = time.strftime("%Y%m%d-%H%M%S") + "-train" + "-".join(plan.members[:6])
    os.makedirs(LOGS, exist_ok=True)
    plan.log = os.path.join(LOGS, stamp + ".log")
    documents = [f for f in fz.git("diff", "--name-only", main, "HEAD", tree=plan.tree).stdout.splitlines()
                 if f.endswith(".md")]
    alone = all(entries[t].get("documents") for t in plan.members)
    ok, tail = fz.documents_check(plan.tree, documents, sources=alone) if documents or alone else (True, "")
    if not ok or alone:
        open(plan.log, "w").write(tail + "\n")
        plan.ok, plan.tail, plan.kind = ok, tail, "documents"
        v2.log(f"the train of tasks {listing(plan.members)}: its documents check {'passed' if ok else 'failed'}")
        return
    advancing = fz.ADVANCE and "incremental_check.py check" in v2.LANDING_CHECK
    depth = len(v2.base_lineage())
    reused = kept_build(plan.head, plan.tree) if advancing else None
    if reused:
        plan.out, plan.ok, plan.kind, plan.seconds, plan.tail, plan.reused = reused, True, "repository", 0, "", True
        v2.log(f"the train of tasks {listing(plan.members)} lands on the build its check batch made: the same content, "
               f"checked there ({reused}), adopted as the base, no check again")
        fz.record_lineage("+".join(plan.members), plan.out, depth, 0, True)
        return
    plan.out = os.path.join(fz.BASES, stamp) if advancing else os.path.relpath(os.path.join(LOGS, stamp), v2.PROJECT)
    command = v2.LANDING_CHECK.format(output=plan.out) + (" --advance-base" if advancing else "")
    if advancing:
        os.makedirs(os.path.join(v2.PROJECT, fz.BASES), exist_ok=True)
    v2.log(f"the train of tasks {listing(plan.members)} is checked together with main ({command})")
    ok, plan.seconds, plan.tail = fz.run_logged(plan.members[0], command, plan.tree, plan.log)
    plan.ok, plan.kind = ok, "repository"
    if fz.base_refused(ok, plan.seconds, plan.log):
        plan.ok, plan.broken = None, plan.tail  # the base's, not the train's: nobody is found for it
    v2.log(f"the train of tasks {listing(plan.members)}: its check {'passed' if ok else 'was refused by the base' if plan.broken else 'failed'} in "
           f"{round(plan.seconds)} s")
    if advancing:
        fz.record_lineage("+".join(plan.members), plan.out, depth, plan.seconds, ok)


# A batch's check keeps its heap (incremental_check.py check --keep-heap) and is recorded by the content it checked; a
# landing of that same content adopts it as the base instead of proving the same theories again (C10: the batches'
# proofs took a median 186 s and 2.88 hours of 09-22's afternoon, the trains' 216 s and 2.58 hours, nearly all of it the
# same members' theories). Isabelle cannot join two heaps, so the content must be the same: nothing landed between them.
KEPT = os.path.join(v2.STATE, "kept-builds.json")
KEEP_HEAPS = os.environ.get("ORCH_BATCH_KEEPS_HEAP", "1") != "0"
PLANNING_FILES = ("HANDOFF.md", "PLANNING_LOG.md")  # the planner's state, committed with landings, read by no check


def content_key(ref, tree=None):
    """The content a check reads at a commit: its tree's entries by path and object, the planner's state files aside."""
    listed = fz.git("ls-tree", "-r", ref, tree=tree).stdout.splitlines()
    kept = [line for line in listed if line.split("\t", 1)[-1] not in PLANNING_FILES]
    return hashlib.sha256("\n".join(kept).encode()).hexdigest() if kept else None


def keeps_heap():
    """Whether a batch's check keeps its heap: the repository's check, advancing the base at landings."""
    return KEEP_HEAPS and fz.ADVANCE and "incremental_check.py check" in v2.LANDING_CHECK


def record_build(ref, out, tree=None):
    """A batch's accepted, kept build, by the content it checked."""
    key = content_key(ref, tree)
    try:
        summary = json.load(open(os.path.join(v2.PROJECT, out, "incremental.json")))
    except (OSError, ValueError):
        return
    if not key or summary.get("status") != "accepted" or not summary.get("kept_context"):
        return
    with open(KEPT + ".lock", "a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            kept = json.load(open(KEPT))
        except (OSError, ValueError):
            kept = {}
        kept = {k: v for k, v in kept.items() if time.time() - v.get("at", 0) < v2.BASE_KEEP}
        kept[key] = {"out": out, "at": time.time(), "base": summary.get("base"), "context": summary["kept_context"]}
        json.dump(kept, open(KEPT + ".tmp", "w"), indent=1)
        os.replace(KEPT + ".tmp", KEPT)


def kept_build(ref, tree=None):
    """The output of a batch's kept build of exactly this content, on the base in use now, or None."""
    key = content_key(ref, tree)
    try:
        entry = json.load(open(KEPT)).get(key) if key else None
        current = json.loads(fz.active_pointer() or "{}").get("directory")
    except (OSError, ValueError):
        return None
    if not entry or time.time() - entry.get("at", 0) >= v2.BASE_KEEP:
        return None
    if os.path.realpath(entry.get("base") or "") != os.path.realpath(current or "-"):
        return None  # the base moved since: its build stood on another
    if not os.path.isdir(entry.get("context") or "") or not os.path.isfile(os.path.join(v2.PROJECT, entry["out"],
                                                                                        "incremental.json")):
        return None
    return entry["out"]


def heavy(plan, entries):
    """Whether a plan's check takes a heavy slot."""
    return not all(entries[t].get("documents") for t in plan.members)


def run_checks(c, plans, main, entries, deadline):
    """Check the plans side by side, one heavy slot each: the first when its slot is free (or past the budget, as a
    check waits at most that long), a second only when a second slot is free too. Returns the plans checked, or the
    machine's wait ("machine", task) when not even the first may start — main is let go meanwhile."""
    lead = plans[0].members[0]
    if c.heavy(plans[0], entries) and time.time() < deadline and not fz.machine_free(lead):
        return ("machine", lead)
    run = [plans[0]]
    admitted = []
    if c.heavy(plans[0], entries):
        fz.wait_for_isabelle(lead, False, end=deadline)
        admitted.append(lead)
    for p in plans[1:]:
        if not c.heavy(p, entries):
            run.append(p)
        elif fz.machine_free(p.members[0]):
            fz.wait_for_isabelle(p.members[0], False, end=time.time())
            admitted.append(p.members[0])
            run.append(p)
    def checked(p):
        c.check(p, main, entries)
        # a member checked alone with main that fails is found, and a batch tells it when its own check ends, not when
        # the check beside it does: task 223, found at 18:48:44, waited on the 20 minutes of task 227's half, and the
        # batch's next checks behind it (2026-09-22)
        if c.found_at_once and p.ok is False and not p.stacked and len(p.members) == 1:
            c.fail(p.members[0], main, p)
    try:
        with ThreadPoolExecutor(max_workers=len(run)) as pool:
            list(pool.map(checked, run))
    finally:
        for tid in admitted:
            fz.admitted_no_more(tid)
    return run


# ---------------------------------------------------------------- attribution

FAILING_THEORY = re.compile(r'^\*\*\*.*?\bof "[^"]*/theories/([^"/]+)\.thy"', re.M)
NAMED_THEORY = re.compile(r"(?:theory|Theory)[:\s]+\"?([A-Za-z_][\w.]*)")
DOCUMENT_FILE = re.compile(r"^- (\S+) holds a conflict marker$", re.M)


def imports_graph(tree):
    """{theory: [the local theories it imports]} of a tree's theories/."""
    graph = {}
    root = os.path.join(tree, "theories")
    for name in os.listdir(root) if os.path.isdir(root) else []:
        if not name.endswith(".thy"):
            continue
        try:
            h = fz.THEORY_HEAD.match(open(os.path.join(root, name), errors="ignore").read())
        except OSError:
            continue
        names = [n.strip('"').rsplit(".", 1)[-1] for n in fz.IMPORT_NAME.findall(h.group("imports"))] if h else []
        graph[name[:-4]] = names
    return graph


def closure(graph, theories):
    seen, todo = set(), list(theories)
    while todo:
        t = todo.pop()
        if t in seen:
            continue
        seen.add(t)
        todo += [x for x in graph.get(t, []) if x in graph]
    return seen


def attribute(plan, main, entries):
    """(cleared, suspects) of a plan whose check failed, from the check's own report: a failed theory depends on its
    import closure, a failed recipe reads the files its manifest names, a failed host test the tools; a member is a
    suspect when it changed what failed. What the report does not say — or says of no member (a failure of the
    combination as such) — leaves every member a suspect: the whole is bisected."""
    members = plan.members
    files = {t: set(changed(main, entries[t]["head"])) for t in members}
    everything = ([], list(members))
    suspects, explained = set(), False
    if plan.kind == "documents":
        for line in (plan.tail or "").splitlines():
            if not line.startswith("- "):
                continue
            m = DOCUMENT_FILE.match(line)
            named = m.group(1) if m else "THEORY_MAP.md" if "THEORY_MAP.md" in line else None
            if not named:
                return everything
            explained = True
            suspects |= {t for t in members if named in files[t]}
    else:
        try:
            report = json.load(open(os.path.join(v2.PROJECT, plan.out, "incremental.json")))
        except (OSError, ValueError, TypeError):
            return everything
        error = report.get("error") or ""
        theories = set()
        try:
            log = open(os.path.join(v2.PROJECT, plan.out, "proof", "build.log"), errors="ignore").read()
            theories |= set(FAILING_THEORY.findall(log)) | set(check_errors.unfinished(log) or ())  # a timeout's
        except OSError:
            pass
        for missing, importer in re.findall(r"Missing local theory: ([\w.]+), imported by ([\w.]+)", error):
            theories |= {missing, importer}
        if theories:
            explained = True
            reach = {f"theories/{t}.thy" for t in closure(imports_graph(plan.tree), theories)}
            suspects |= {t for t in members if files[t] & (reach | {"ROOT"})}
        recipes = report.get("failed_recipes") or []
        if recipes:
            explained = True
            try:
                manifests = json.load(open(os.path.join(v2.PROJECT, plan.out, "manifests.json")))
            except (OSError, ValueError):
                return everything
            for r in recipes:
                read = set((manifests.get(r) or {}).get("files") or {})
                if not read:
                    return everything
                suspects |= {t for t in members if files[t] & read}
        failing = [k for k, v in (report.get("host_tests") or {}).items() if v.get("exit_code")]
        if failing:
            explained = True
            suspects |= {t for t in members if any(not f.startswith("theories/") and not f.endswith(".md")
                                                   for f in files[t])}
        if not explained and report.get("status") != "accepted":
            return everything
    if not explained or not suspects:
        return everything
    return [t for t in members if t not in suspects], [t for t in members if t in suspects]


# ---------------------------------------------------------------- landing what passed

def settle_pointer(out, before):
    """The active base after a round: the check that landed (when it advanced the base), or where it was. Two checks
    side by side each select their own base as they pass, so the last to finish would win."""
    now = fz.active_pointer()
    if out:
        try:
            summary = json.load(open(os.path.join(v2.PROJECT, out, "incremental.json")))
            wanted = summary.get("kept_context") or summary.get("active_context")  # a batch's kept build, adopted
        except (OSError, ValueError):
            wanted = None
        try:
            current = json.loads(now or "{}").get("directory")
        except ValueError:
            current = None
        if wanted and os.path.realpath(wanted) != os.path.realpath(current or ""):
            r = subprocess.run([sys.executable, "-B", "tools/incremental_check.py", "adopt", "--proof", wanted],
                               cwd=v2.PROJECT, capture_output=True, text=True, timeout=900)
            if r.returncode:
                v2.log(f"ATTENTION the base could not be set to the check that landed ({wanted}): "
                       f"{(r.stderr or r.stdout).strip()[-300:]}")
        return
    if before is not None and now != before:
        fz.restore_base(before)


def record(plan, ref):
    """What a train leaves after it: its check's receipts retained, and the planner's state as it stands (HANDOFF.md,
    committed with every landing as before), in one commit of the harness; then one push."""
    paths, what = [], []
    if plan.out and plan.kind == "repository" and fz.ADVANCE and "incremental_check.py check" in v2.LANDING_CHECK:
        r = subprocess.run([sys.executable, "-B", "tools/incremental_check.py", "retain", "--output", plan.out],
                           cwd=v2.PROJECT, capture_output=True, text=True, timeout=900)
        if r.returncode:
            v2.log(f"ATTENTION the receipts of the check tasks {listing(plan.members)} landed with were not retained: "
                   f"{(r.stderr or r.stdout).strip()[-300:]}")
        else:
            receipts = [line[3:].strip() for line in fz.git("status", "--porcelain", "--untracked-files=all", "--",
                                                             *v2.RECEIPTS).stdout.splitlines() if line[3:].strip()]
            paths += receipts
            what += ["the recipe receipts of the check"] if receipts else []
    handoff = bool(fz.git("status", "--porcelain", "--", "HANDOFF.md").stdout.strip())
    if handoff:
        paths.append("HANDOFF.md")
    tasks = f"task{'s' if len(plan.members) > 1 else ''} {listing(plan.members)}"
    if paths:
        fz.git("add", "--", *paths)
        message = (f"Retain the recipe receipts of the check {tasks} landed with" + (", and the planner's state"
                   if handoff else "")) if what else f"Retain the planner's state as {tasks} landed"
        said = fz.check_summary(plan.out) if plan.checked and plan.out else None
        if said and plan.reused:  # its batch's check, of exactly what lands
            message += (f"\n\nValidation: the harness's check of {tasks} together with main, in their check batch, of "
                        f"exactly the content that lands (nothing landed between them), {said}; its build is the base.")
        elif said:  # the landing's own check, said where the landing is recorded
            message += (f"\n\nValidation: the harness's check of {tasks} together with main, exactly as it lands, "
                        f"{said}.")
        c = fz.git("commit", "-q", "-m", message, "--", *paths)
        if c.returncode:
            fz.git("reset", "-q", "--", *paths)
            v2.log(f"ATTENTION what tasks {listing(plan.members)} landed with was not committed: "
                   f"{(c.stdout + c.stderr).strip()[-300:]}")
        elif "the recipe receipts of the check" in what:
            v2.log(f"the base follows main: the check tasks {listing(plan.members)} landed with is the base, its "
                   "receipts retained and committed")
            v2.prune_bases()
    p = fz.git("push", "origin", "HEAD", timeout=180)
    return p.returncode == 0


def land(plan, main, entries, before):
    """Main moves to exactly what was checked: a fast-forward of the one tree to the plan's head. None once landed;
    "moved" when main moved meanwhile (the owner's commit: assembled and checked again); or {path: task} standing
    uncommitted in the one tree over what it writes (waited for with main let go)."""
    if head() != main:
        return "moved"
    standing = v2.one_tree_changes(fz.git("diff", "--name-only", main, plan.head).stdout.split())
    if standing:
        return standing
    r = fz.git("merge", "--ff-only", "-q", plan.head)
    if r.returncode:
        v2.log(f"ATTENTION the train of tasks {listing(plan.members)} could not move main: "
               f"{(r.stdout + r.stderr).strip()[-300:]}")
        return "moved"
    settle_pointer(plan.out if plan.checked and plan.kind == "repository" else None, before)
    ref = fz.git("rev-parse", "--short", "HEAD").stdout.strip()
    pushed = record(plan, ref)
    ref = fz.git("rev-parse", "--short", "HEAD").stdout.strip()
    for tid in plan.members:
        try:
            files = list(json.load(open(os.path.join(v2.BUILD, tid, "finalize.json")))["files"])
        except (OSError, ValueError, KeyError):
            files = []
        with v2.owners() as o:  # committed: no longer anyone's uncommitted change
            for f in files:
                o.pop(os.path.normpath(f), None)
        fz.record_pending_commit(files, ref, v2.PROJECT)
        fields = dict(commit=ref, commit_error=None, pushed=pushed, train=plan.members)
        if plan.checked:
            fields.update(landing_check=True, landing_seconds=round(plan.seconds),
                          **({"landing_reused": plan.out} if plan.reused else {}))
        fz.outcome(tid, **fields)
        v2.tree_checked(f"task {tid}", "its commit")
        v2.worktree_gone(tid)
        decide(tid, 0, "landed", ref)
    shown = ref + ("" if pushed else " (the push failed)")
    v2.log(f"the train of tasks {listing(plan.members)} landed as {ref}" + ("" if pushed else " (the push failed)"))
    if len(plan.members) == 1:
        fz.say(v2.committed, plan.members[0], shown, None)
    else:
        how = ("no check of their own: their check batch's build of the same content, adopted" if plan.reused
               else f"one check of the {len(plan.members)} with main, {round(plan.seconds / 60) or 1} min" if plan.checked
               else "checked together")
        fz.say(v2.landed_together, plan.members, shown, how)
    return None


def fail(tid, main, plan):
    """A member found not to stand with what landed: main is brought into its branch — its tree holds both, where its
    fix is made and checked again — and it goes to its quick fix with the errors of the check that isolated it, as a
    landing check that failed did (landing_failed)."""
    tree = v2.worktree_of(tid)
    if os.path.realpath(tree) == os.path.realpath(v2.PROJECT):
        v2.log(f"ATTENTION task {tid} failed in its train but has no tree of its own: main is not brought into it")
        m = merging = None
    else:
        fz.put_back_receipts(tid, tree)
        m = fz.git("merge", "--no-commit", "--no-ff", head(), tree=tree)
        merging = fz.git("rev-parse", "-q", "--verify", "MERGE_HEAD", tree=tree).returncode == 0
    if m is not None and m.returncode:
        conflicts = [l for l in fz.git("diff", "--name-only", "--diff-filter=U", tree=tree).stdout.splitlines() if l]
        left = fz.imports_agreed(tree, conflicts) if merging and conflicts else conflicts
        if left:
            fz.keep_marked(tid, tree, left, head())
            fz.git("merge", "--abort", tree=tree)
            decide(tid, fz.merge_refused(tid, left), "refused")
            return
    if merging:
        fz.rows_agreed(tree)
        fz.git("commit", "--no-edit", "-m", f"Bring what landed meanwhile into task {tid}", tree=tree)
    log = plan.log if plan and plan.log else None
    if log and os.path.exists(log):
        with contextlib.suppress(OSError):
            open(os.path.join(v2.BUILD, tid, "landing.log"), "w").write(open(log, errors="ignore").read())
    tail = (plan.tail if plan else None) or "(the check of the train it was in failed; its log is gone)"
    if plan and plan.out:
        tail += f"\n(the check's report: {plan.out}/ — `v2.py read check:{os.path.basename(plan.out)}`)"
    fz.outcome(tid, landing_check=False, landing_seconds=round(plan.seconds) if plan else 0)
    decide(tid, fz.landing_refused(tid, tail), "failed")


# ---------------------------------------------------------------- the lander

class Group:
    """Members still to be decided: `failing` when a check of them (on main as it then was) failed."""

    def __init__(self, members, failing, plan=None):
        self.members, self.failing, self.plan = list(members), failing, plan


def halves(members):
    k = (len(members) + 1) // 2
    return members[:k], members[k:]


def land_queue(deadline, c=None):
    """Under the landing lock: land what waits, train after train. A train that fails is resolved in rounds of at most
    two checks side by side (run_checks): attribution first — the members its report clears land after one check of
    them, while the suspects are checked stacked on top — then halves of what fails, a half that passes landing, and
    two halves that pass alone (an interaction) landing the first and checking the second on top of it. Returns None
    when nothing waits, or what it waits for with main let go: ("machine", task), or {path: task} standing in the one
    tree. Its first round runs even past the budget, as a check waited at most that long and then ran."""
    c = c or TRAIN
    first, before = True, c.pointer()
    try:
        return rounds(c, deadline, first, before)
    finally:
        c.settle(BEFORE[0] if BEFORE else before)
        BEFORE.clear()


BEFORE = []  # the active base as the last landing left it (settle_pointer puts it back on any way out)


def rounds(c, deadline, first, before):
    BEFORE[:] = [before]
    while True:
        entries = dict(c.waiting())
        if not entries:
            return None
        c.begin()
        fresh = [t for t in entries if not entries[t].get("known_fail")]
        known = [t for t in entries if entries[t].get("known_fail")]
        found = Plan(known)
        found.log = next((entries[t].get("fail_log") for t in known if entries[t].get("fail_log")), None)
        found.tail = fz.log_tail(found.log) if found.log and os.path.exists(found.log) else None
        groups = ([Group(fresh, False)] if fresh else []) + ([Group(known, True, found)] if known else [])
        while groups:
            if not first and time.time() >= deadline:
                return None
            main = c.base()
            for x in groups:
                x.members = [t for t in x.members if not c.queue.decision(t)]
                if x.failing and len(x.members) == 1 and c.found_at_once:
                    c.fail(x.members[0], main, x.plan)
                    x.members = []
            groups[:] = [x for x in groups if x.members]
            if not groups:
                continue
            g = groups[0]
            if g.failing and len(g.members) == 1:
                c.fail(g.members[0], main, g.plan)
                groups.pop(0)
                continue
            if g.failing:
                h1, h2 = halves(g.members)
                plans = [Plan(h1), Plan(h2)]
            else:
                plans = [Plan(g.members)]
                nxt = groups[1] if len(groups) > 1 else None
                if nxt and not (nxt.failing and len(nxt.members) == 1):
                    plans.append(Plan(halves(nxt.members)[0] if nxt.failing else nxt.members, stacked=plans[0]))
            key = lambda p: (main, tuple((t, entries[t]["head"]) for t in (p.stacked.members if p.stacked else [])
                                         + p.members))
            for i, (p, name) in enumerate(zip(plans, c.trees)):
                memo = c.memo.get(key(p))
                if memo and not p.stacked:
                    p.head, p.out, p.ok, p.checked, p.kind = memo["head"], memo["out"], True, memo["checked"], \
                        memo["kind"]
                    p.members = memo["members"]
                    p.seconds = memo["seconds"]
                    continue
                c.assemble(p, name, main, entries)
                if p.stacked:
                    p.members = [t for t in p.members if t not in p.stacked.members]
            plans = [p for p in plans if p.members]
            if not plans:
                continue
            todo = [p for p in plans if p.ok is None]
            if todo:
                ran = run_checks(c, todo, main, entries, deadline)
                if isinstance(ran, tuple):
                    return ran
                broken = next((p for p in ran if p.broken), None)
                if broken:  # the proof base refused it before it began: nothing of the members is known
                    return ("broken", broken.members[0], broken.broken)
                for p in todo:
                    if p not in ran:
                        p.ok = None  # no second slot this round
            first = False
            for p in plans:
                if p.ok:
                    c.memo[key(p)] = {"head": p.head, "out": p.out, "checked": p.checked, "kind": getattr(p, "kind", None),
                                      "members": p.members, "seconds": p.seconds}
            # what passed lands, what failed is narrowed
            if not g.failing:
                p0, p1 = plans[0], (plans[1] if len(plans) > 1 and plans[1].stacked else None)
                if p0.ok:
                    both = p1 is not None and p1.ok
                    top = p1 if both else p0
                    if both:
                        top.members = p0.members + p1.members
                    wait = c.land(top, main, entries, before)
                    if wait == "moved":
                        continue
                    if wait:
                        return ("standing", top.members[0], wait)
                    before = c.pointer()
                    BEFORE[:] = [before]
                    groups.pop(0)
                    if p1 is not None and groups:
                        nxt = groups[0]
                        tested = [t for t in nxt.members if t in (p1.members if not both else top.members)]
                        rest = [t for t in nxt.members if t not in tested]
                        if both:
                            groups[0:1] = [Group(rest, nxt.failing, nxt.plan)] if rest else []
                        elif p1.ok is False:
                            groups[0:1] = [Group(tested, True, p1)] + ([Group(rest, False)] if rest else [])
                elif p0.ok is False:
                    groups[0:1] = narrowed(p0, main, entries, c)
                else:  # its check did not run (no slot at all): the machine's wait
                    return ("machine", p0.members[0])
            else:
                p0, p1 = plans[0], plans[1] if len(plans) > 1 else None
                if p0.ok and p1 is not None and p1.ok:  # each stands alone, not both together: an interaction
                    wait = c.land(p0, main, entries, before)
                    if wait == "moved":
                        continue
                    if wait:
                        return ("standing", p0.members[0], wait)
                    before = c.pointer()
                    BEFORE[:] = [before]
                    groups[0] = Group(p1.members, False)  # checked next on top of the first half
                elif p0.ok:
                    wait = c.land(p0, main, entries, before)
                    if wait == "moved":
                        continue
                    if wait:
                        return ("standing", p0.members[0], wait)
                    before = c.pointer()
                    BEFORE[:] = [before]
                    rest = p1.members if p1 is not None else [t for t in g.members if t not in p0.members]
                    groups[0] = Group(rest, True, p1 if p1 is not None and p1.ok is False else g.plan)
                elif p1 is not None and p1.ok:
                    wait = c.land(p1, main, entries, before)
                    if wait == "moved":
                        continue
                    if wait:
                        return ("standing", p1.members[0], wait)
                    before = c.pointer()
                    BEFORE[:] = [before]
                    groups[0] = Group(p0.members, True, p0)
                elif p0.ok is False:
                    rest = [t for t in g.members if t not in p0.members]
                    groups[0:1] = narrowed(p0, main, entries, c) + (
                        (narrowed(p1, main, entries, c) if p1 is not None and p1.ok is False else [Group(rest, False)])
                        if rest else [])
                else:
                    return ("machine", p0.members[0])
            c.settle(before)
            for x in groups:
                c.queue.mark(x.members, x.failing, x.plan.log if x.plan else None)
        # one train (or batch) a call: its reports are made once main is let go (run_lander), and the next taken then.
        # A lander that went on to the next train while holding them left task 151, landed at 15:30:23, reported as a
        # finalizer that ended without reporting — sent to the planner, queued, and a new session started on it
        return None


class Train:
    """The landing train's part of a round: main is its base, a plan that passes lands (main moves to it), a member
    found goes to its quick fix with main brought into its tree."""
    name, trees, queue, memo = "train", TREES, LANDING_QUEUE, PASSED
    # a member found is told once what its report cleared has landed: the main brought into its tree holds that
    found_at_once = False

    def waiting(self):
        return waiting()

    def begin(self):
        pass

    def base(self):
        return head()

    def assemble(self, plan, name, main, entries):
        assemble(plan, name, main, entries)

    def check(self, plan, main, entries):
        check(plan, main, entries)

    def heavy(self, plan, entries):
        return heavy(plan, entries)

    def land(self, plan, main, entries, before):
        return land(plan, main, entries, before)

    def fail(self, tid, main, plan):
        fail(tid, main, plan)

    def pointer(self):
        return fz.active_pointer()

    def settle(self, before):
        settle_pointer(None, before)


TRAIN = Train()


# ---------------------------------------------------------------- check batches

# The repository's check of every task waiting for one, run once for all (notes/plan-landing-train.md 1b): each task
# ran its own — its session's runs (69 in seventeen hours, 27 of them refused for the machine and tried again), the
# finalizer's (116, 24 of them of a tree the session had just checked), each rebuilding the same dependents and
# re-running the same recipes. A task's work, as its tree stands, is a snapshot (v2.snapshot); a batch merges every
# snapshot waiting onto main in a check tree and checks them together; a failure is resolved as a train's is. A batch
# moves nothing: what passes lands later, with its train, which checks exactly what lands.
CHECK_QUEUE = Queue(os.path.join(v2.STATE, "check-queue.json"))
BATCH_TREES = ("check-a", "check-b")
BATCH_LOGS = os.path.join(v2.BUILD, "batches")
BATCHER = os.path.join(v2.STATE, "batcher.pid")
RESULTS = os.path.join(v2.STATE, "check-results.json")  # {tree: when it passed, and where}: a tree checked is checked
RESULT_KEEP = 86400


def asking(tid, e, st):
    """Whether a check entry's task still waits for it: its finalizer's check, or its session parked for it."""
    t = st["tasks"].get(tid) or {}
    if e.get("kind") == "finalizer":
        return t.get("stage") == "checking"
    return t.get("stage") == "parked" and (t.get("parked") or {}).get("for") == "check"


def passed_tree(tree):
    """When a tree's work passed a batch (within RESULT_KEEP), or None."""
    try:
        r = json.load(open(RESULTS)).get(tree)
    except (OSError, ValueError):
        return None
    return r if r and time.time() - r.get("at", 0) < RESULT_KEEP else None


def record_pass(tree, members, log):
    try:
        results = json.load(open(RESULTS))
    except (OSError, ValueError):
        results = {}
    results = {k: v for k, v in results.items() if time.time() - v.get("at", 0) < RESULT_KEEP}
    results[tree] = {"at": time.time(), "with": members, "log": log}
    tmp = RESULTS + ".tmp"
    json.dump(results, open(tmp, "w"), indent=1)
    os.replace(tmp, RESULTS)


def take_in(tree, tid, ref, first):
    """A member's snapshot merged into the check tree: None, "defer" when its lines meet another member's (it goes to
    the next batch, where they are not), or why it cannot be checked with main at all (its lines meet main's: its
    session brings main in first)."""
    m = fz.git("merge", "--no-ff", "--no-commit", ref, tree=tree)
    merging = fz.git("rev-parse", "-q", "--verify", "MERGE_HEAD", tree=tree).returncode == 0
    if m.returncode:
        conflicts = [l for l in fz.git("diff", "--name-only", "--diff-filter=U", tree=tree).stdout.splitlines() if l]
        left = fz.imports_agreed(tree, conflicts) if merging and conflicts else conflicts
        if left or not conflicts:
            fz.git("merge", "--abort", tree=tree)
            if not first:
                return "defer"
            return (f"its work does not merge with main: {fz.listed(left or [(m.stdout + m.stderr).strip()[-300:]])} "
                    "were changed on both sides. Bring main in (`v2.py bring-main`), write each file both sides "
                    "marked as it should stand, and ask for the check again.")
    if not merging:
        return None
    fz.rows_agreed(tree)
    c = fz.git("commit", "--no-verify", "--no-edit", "-m", f"Check the work of task {tid}", tree=tree)
    if c.returncode:
        fz.git("merge", "--abort", tree=tree)
        return "defer" if not first else f"its work could not be merged with main: {(c.stdout + c.stderr).strip()[-300:]}"
    return None


class Batch:
    """A check batch's part of a round: its base is main and what passed before it in the batch (a virtual landing:
    nothing moves), a plan that passes is told passed, a member found is told its errors."""
    name, trees, queue = "batch", BATCH_TREES, CHECK_QUEUE
    # a member found needs no check, and a batch moves nothing: it is told at once, not after the checks of the groups
    # before it (task 153, found by its batch's report at 15:42:53, was told at 15:46:19, after the 206 s check of
    # task 176, which that report cleared)
    found_at_once = True

    def __init__(self):
        self.memo, self.virtual = {}, None

    def waiting(self):
        return CHECK_QUEUE.waiting(asking)

    def begin(self):
        self.virtual = head()

    def base(self):
        return self.virtual

    def assemble(self, plan, name, main, entries):
        at = plan.stacked.head if plan.stacked else main
        plan.tree = integration(name, at)
        taken = list(plan.stacked.members) if plan.stacked else []
        for tid in [t for t in plan.members if t not in taken]:
            why = take_in(plan.tree, tid, entries[tid]["head"], first=not taken and at == head())
            if why is None:
                taken.append(tid)
            elif why != "defer":
                self.told(tid, False, why, None, [tid], 0)
        plan.members = taken
        plan.head = head(plan.tree)

    def check(self, plan, main, entries):
        plan.checked = True
        stamp = time.strftime("%Y%m%d-%H%M%S") + "-batch" + "-".join(plan.members[:6])
        os.makedirs(BATCH_LOGS, exist_ok=True)
        plan.log = os.path.join(BATCH_LOGS, stamp + ".log")
        keep = keeps_heap()  # in the lasting store, as a train's: a heap is bound to its path (C10)
        plan.out = os.path.join(fz.BASES, stamp) if keep else os.path.relpath(os.path.join(BATCH_LOGS, stamp), v2.PROJECT)
        if keep:
            os.makedirs(os.path.join(v2.PROJECT, fz.BASES), exist_ok=True)
        command = v2.LANDING_CHECK.format(output=plan.out) + (" --keep-heap" if keep else "")
        v2.log(f"the work of task{'s' if len(plan.members) > 1 else ''} {listing(plan.members)} is checked together "
               f"with main ({command})")
        ok, plan.seconds, plan.tail = fz.run_logged(plan.members[0], command, plan.tree, plan.log)
        plan.ok, plan.kind = ok, "repository"
        if fz.base_refused(ok, plan.seconds, plan.log):
            plan.ok, plan.broken = None, plan.tail
        v2.log(f"the check of task{'s' if len(plan.members) > 1 else ''} {listing(plan.members)}: "
               f"{'passed' if ok else 'refused by the base' if plan.broken else 'failed'} in {round(plan.seconds)} s")
        if ok and keep:
            v2.softly("the batch's kept build", record_build, plan.head, plan.out, plan.tree)

    def heavy(self, plan, entries):
        return True

    def land(self, plan, main, entries, before):
        for tid in plan.members:
            tree = fz.git("rev-parse", f"{entries[tid]['head']}^{{tree}}").stdout.strip()
            record_pass(tree, plan.members, plan.log)
            self.told(tid, True, None, plan, plan.members, plan.seconds)
        self.virtual = plan.head
        return None

    def fail(self, tid, main, plan):
        self.told(tid, False, None, plan, plan.members if plan else [tid], plan.seconds if plan else 0)

    def pointer(self):
        return None

    def settle(self, before):
        pass

    def told(self, tid, ok, why, plan, members, seconds):
        """A member's outcome, where it waits: its finalizer's check (the task's outcome, its log, and the check's
        report: to its review or its quick fix, v2.checked), or its session, parked for it (v2.check_came)."""
        entry = CHECK_QUEUE.peek().get(tid) or {}
        others = [t for t in members if t != tid]
        with_ = f"with main{' and the work of task' + ('s ' if len(others) > 1 else ' ') + listing(others) if others else ''}"
        log = plan.log if plan else None
        tail = why or (plan.tail if plan else "") or ""
        report = f"; its report: {plan.out}/, or `v2.py read check:{os.path.basename(plan.out)}`" if plan and plan.out else ""
        text = (f"The repository's check of your work {with_} passed in {round(seconds)} s" + (
                f" (its log: {os.path.relpath(log, v2.PROJECT)}{report})." if log else ".")) if ok else (
                why and f"Your work could not be checked: {why}" or
                f"The repository's check of your work {with_} failed" + (
                    f" (its log: {os.path.relpath(log, v2.PROJECT)}{report})" if log else "") + f":\n{tail}")
        CHECK_QUEUE.decide(tid, 0 if ok else 1, "passed" if ok else "failed", log=log, text=text)
        if entry.get("kind") == "finalizer":
            d = os.path.join(v2.BUILD, tid)
            with contextlib.suppress(OSError):
                open(os.path.join(d, "finalize.log"), "w").write(
                    (open(log, errors="ignore").read() if log and os.path.exists(log) else "") + "\n" + text + "\n")
            fz.outcome(tid, ok=ok, seconds=round(seconds), batch=members, check_output=plan.out if plan else None)
            v2.log(f"check of task {tid}: {'passed' if ok else 'failed'} (" + (
                f"with task{'s' if len(others) > 1 else ''} {listing(others)}" if others else "alone") + ")")
            fz.say(v2.checked, tid, ok, text if ok else tail or text, True)
        else:
            v2.check_came(tid, ok, text)


BATCH = Batch()


def run_batcher(deadline, tid=None):
    """Check what waits, batch after batch, as the batcher whenever none is running. A finalizer (`tid`) returns its
    entry's code once it is decided, or leaves it queued when its budget ends (the watchdog starts a batcher when
    entries wait and nobody checks them)."""
    said = False
    while True:
        d = CHECK_QUEUE.decision(tid) if tid else None
        if d:
            return d["code"]
        wait = "busy"
        with open(BATCHER + ".lock", "a") as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                held = True
            except BlockingIOError:
                held = False
            if held:
                try:
                    wait = land_queue(deadline, BATCH)
                finally:
                    fcntl.flock(lock, fcntl.LOCK_UN)
        d = CHECK_QUEUE.decision(tid) if tid else None
        if d:
            return d["code"]
        if tid and not CHECK_QUEUE.queued(tid):
            return 0
        more = any(not e.get("decided") for e in CHECK_QUEUE.peek().values())
        if wait is None and not tid and not more:
            return 0
        if time.time() >= deadline:
            if tid:
                v2.log(f"task {tid}'s check stays queued past its finalizer's budget: the next batch checks it")
            return 0
        if wait == "busy" or (wait is None and not more):
            time.sleep(fz.POLL if wait is None else 1 if v2.PAUSE else 0.2)
        elif wait is None:
            pass  # one landed (or was checked) and more wait: taken again at once, its reports made meanwhile
        elif wait[0] == "broken":
            v2.say_once("base-refused-combination", "ATTENTION the proof base refused a combined check before it "
                        f"began (tasks waiting stay queued, nobody is found for it): "
                        f"{(wait[2] or '').strip().splitlines()[-1][:200] if (wait[2] or '').strip() else ''}", every=1800)
            fz.base_changed_or(min(deadline, time.time() + fz.BASE_RETRY))
        elif wait[0] == "machine":
            if not said:
                v2.log(f"the check of task {tid or wait[1]} waits for the machine with the others waiting")
                said = True
            while time.time() < deadline and not fz.machine_free(wait[1]):
                time.sleep(fz.POLL)


def check_in(tid, tree, deadline):
    """A finalizer's check of a task in its own tree, when it is the repository's check: its snapshot joins the batch.
    A tree whose work passed a batch already is not checked again (its session asked for the check, and handed over
    what it checked). None when it cannot be batched: the finalizer runs its check itself."""
    snapshot, why = v2.snapshot(tid, tree)
    if not snapshot:
        v2.log(f"task {tid}'s check is run by itself: {why}")
        return None
    work = fz.git("rev-parse", f"{snapshot}^{{tree}}").stdout.strip()
    done = passed_tree(work)
    if done:
        with_ = [t for t in done.get("with", []) if t != tid]
        text = (f"The repository's check of this very tree passed at {time.strftime('%H:%M', time.localtime(done['at']))}"
                + (f", with the work of task{'s' if len(with_) > 1 else ''} {listing(with_)}" if with_ else "")
                + f" (its log: {os.path.relpath(done['log'], v2.PROJECT) if done.get('log') else 'gone'}): not run again.")
        open(os.path.join(v2.BUILD, tid, "finalize.log"), "w").write(text + "\n")
        fz.outcome(tid, ok=True, seconds=0, reused=done.get("log"))
        v2.log(f"check of task {tid}: passed (the tree its session's check passed on)")
        fz.say(v2.checked, tid, True, text, True)
        return 0
    CHECK_QUEUE.put(tid, head=snapshot, tree=work, kind="finalizer", documents=False)
    v2.log(f"task {tid}'s check waits for the next batch")
    return run_batcher(deadline, tid)


def batcher_alive():
    try:
        pid = int(open(BATCHER).read().strip())
    except (OSError, ValueError):
        return False
    return os.path.exists(f"/proc/{pid}")


def check_waiting():
    """`finalize.py check-batch`: the batcher for sessions that asked (v2.py check) and finalizers that have ended."""
    open(BATCHER, "w").write(str(os.getpid()))
    try:
        return run_batcher(time.time() + fz.WAIT_MAX)
    finally:
        with contextlib.suppress(OSError):
            if open(BATCHER).read().strip() == str(os.getpid()):
                os.remove(BATCHER)


def narrowed(plan, main, entries, c=None):
    """The groups a failed plan leaves: one member is found; more are split by attribution into what its report clears
    (checked again first) and the suspects, known to fail together."""
    if len(plan.members) == 1:
        return [Group(plan.members, True, plan)]
    cleared, suspects = attribute(plan, main, entries)
    v2.log(f"the {(c or TRAIN).name} of tasks {listing(plan.members)} failed its check: "
           + (f"its report clears {listing(cleared)}, checked again without "
              + (f"task {suspects[0]}, which it finds" if len(suspects) == 1 else
                 f"tasks {listing(suspects)}, which are checked in halves") if cleared else
              f"its report names no one of them, and they are checked in halves"))
    return ([Group(cleared, False)] if cleared else []) + [Group(suspects, True, plan)]


def run_lander(deadline, tid=None):
    """Land what waits, as the lander whenever main is free. A finalizer (`tid`) returns its entry's code once it is
    decided — by itself or by the lander before it — or leaves its entry queued when its budget ends (the next train
    lands it: the watchdog starts a lander when entries wait and nobody lands them)."""
    said = False
    while True:
        d = decision(tid) if tid else None
        if d:
            return d["code"]
        later, wait = [], "busy"
        with v2.landing(min(deadline, time.time() + LOCK_TRY)) as held:
            if held:
                fz.LANDING.append([])
                try:
                    wait = land_queue(deadline)
                finally:
                    later = fz.LANDING.pop()
        for report, args in later:  # after main is let go: a report dispatches, and a dispatch may begin a landing
            report(*args)
        d = decision(tid) if tid else None
        if d:
            return d["code"]
        if tid and not queued(tid):
            return 0  # it left the queue (dropped, re-planned): the planner's
        more = any(not e.get("decided") for e in peek().values())
        if wait is None and not tid and not more:
            return 0
        if time.time() >= deadline:
            if tid:
                v2.log(f"task {tid} stays queued past its finalizer's budget: the next train lands it")
            return 0
        if wait == "busy" or (wait is None and not more):
            time.sleep(fz.POLL if wait is None else 0.2 if not v2.PAUSE else 1)
        elif wait is None:
            pass  # one landed (or was checked) and more wait: taken again at once, its reports made meanwhile
        elif wait[0] == "broken":
            v2.say_once("base-refused-combination", "ATTENTION the proof base refused a combined check before it "
                        f"began (tasks waiting stay queued, nobody is found for it): "
                        f"{(wait[2] or '').strip().splitlines()[-1][:200] if (wait[2] or '').strip() else ''}", every=1800)
            fz.base_changed_or(min(deadline, time.time() + fz.BASE_RETRY))
        elif wait[0] == "machine":
            if not said:
                v2.log(f"the landing of task {tid or wait[1]} lets main go while its check with what landed waits "
                       "for the machine")
                said = True
            while time.time() < deadline and not fz.machine_free(wait[1]):
                time.sleep(fz.POLL)
        else:  # ("standing", task, {path: task}): what stands uncommitted in the one tree over what it lands
            fz.stood_for(wait[1], list(wait[2]), deadline)


def hand_in(tid, spec, tree, files, deadline):
    """An accepted task in its own tree: committed on its branch, queued, and landed with the next train."""
    made = fz.branch_commit(tid, spec, tree, files, True)
    if isinstance(made, int):
        return made
    enqueue(tid, head(tree), fz.documents_task(tid))
    v2.log(f"task {tid} is committed on its branch and waits to land with the next train")
    return run_lander(deadline, tid)


def lander_alive():
    try:
        pid = int(open(LANDER).read().strip())
    except (OSError, ValueError):
        return False
    return os.path.exists(f"/proc/{pid}")


def land_waiting():
    """`finalize.py land-queue`: the watchdog's lander, for entries whose finalizers have ended. It is known alive for
    its whole life (lander_alive), its waits for the machine included, so that the watchdog starts no second."""
    open(LANDER, "w").write(str(os.getpid()))
    try:
        return run_lander(time.time() + fz.WAIT_MAX)
    finally:
        with contextlib.suppress(OSError):
            if open(LANDER).read().strip() == str(os.getpid()):
                os.remove(LANDER)
