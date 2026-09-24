#!/usr/bin/env python3
"""A live run as data: everything the console shows, and everything the run produces, read as text — to watch a run,
diagnose it, verify it goes smoothly, and find what slows it, what its batching wastes, what fails to be delivered and
what it costs (the owner, 2026-09-24: "build a script that will output an aggregate log of everything that is displayed
in the console so that once I start a run you can use it to monitor the run, diagnose problems, verify that everything
is going smoothly, find bottlenecks, find issues with batching, errors with delivery, problems with economics and fix
all of these"; "it should be a complete data agregator from an active run with functions tailored to extracting
particular information such that it can be used to monitor a live run"; "Not just session summaries everything
produced should be accesible so that you can evaluate every facet of the run").

    console_report.py [report] [--since 3h|90m|2d|2026-09-24T10:00|last|all] [--only SECTION,...] [--quick] [--json]
    console_report.py changes          what changed since the last `changes` pass: new, standing and resolved findings,
                                       tasks that moved, sessions that started or ended, entries warmed or cooled, the
                                       events, checks and costs of the interval — a pass never repeats what the one
                                       before said (the owner, 2026-09-24: "the goal is to not duplicate information")
    console_report.py findings [AREA]  the checks over everything below, grouped by pattern, each with the command that
                                       shows its evidence
    console_report.py waits            where the tasks' time went: each stage and each cause of waiting, the throughput
    console_report.py errors           ATTENTION, FAILED, not confirmed, tracebacks, API errors: grouped, with lines
    console_report.py delivery         calls refused, stopped or failed, grouped by what came back, across sessions;
                                       mail and answers that reached nobody; lost sessions and failed starts
    console_report.py inventory        everything the run produced in the window, by kind, with the ids to open it by
    console_report.py session NAME [--turns|--full] [--from N] [--to N] [--grep RE]   a session's requests and calls
    console_report.py task ID [--files|--file NAME|--history]   a task: brief, stages, sessions, files, history
    console_report.py check TASK|STAMP a check's or a train's runs: its log's end, its verdicts
    console_report.py asks [QID]       the questions and their answers
    console_report.py mail [NAME]      the mailboxes: what waits for whom
    console_report.py plan NAME        a planning episode: the events it was given, its edits, its notes
    console_report.py kb [NAME]        the knowledge bases: builds, integrations, notes, what they hold
    console_report.py base WHO [--text N]   a base's records, parts, the delta's chain and its texts, its builds
    console_report.py layer ROLE       a role's reasoning layer and churn: records, evidence, protocol held
    console_report.py graph [--all] [--briefs]   the task graph as the list holds it
    console_report.py record session|task|ask|state ID   a record from the state (or the archive), raw
    console_report.py file PATH [--lines A-B] [--grep RE]   any file of the project, the state or .build
    console_report.py log [--source v2|warm|watchdog|qa] [--grep RE] [--tail N]

Every figure is the console's own where the console has one (dashboard.py's functions: the same reads of the same
records), and every product is read where the run wrote it: nothing is computed twice or kept apart. It reads only;
it runs inside the sandbox. Every output is bounded (--max, 60,000 characters): what is cut says how to read on.
"""
import argparse
import collections
import functools
import glob
import hashlib
import json
import os
import re
import statistics
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import dashboard as d  # noqa: E402
import v2  # noqa: E402

SECTIONS = ("findings", "run", "sessions", "pipeline", "waits", "machine", "checks", "batching", "delivery", "errors",
            "costs", "bases", "log")
TONES = {"bad": "BAD ", "warn": "WARN", "info": "info"}
ME = ".claude/orchestration/console_report.py"
MARK = os.path.join(os.environ.get("TMPDIR") or "/tmp", "console-report.last.json")


# ---------------------------------------------------------------- small helpers

def k(x):
    x = x or 0
    return f"{x / 1e9:.2f}B" if x >= 1e9 else f"{x / 1e6:.2f}M" if x >= 1e6 else f"{round(x / 1000)}K" if x >= 1000 \
        else str(round(x))


def dur(s):
    return "—" if s is None else d.span_text(s)


def stamp_epoch(stamp):
    """A recorded time as an epoch: UTC where it says so (a trailing Z or an offset), local otherwise."""
    if not stamp:
        return None
    stamp = str(stamp)
    return d.utc_epoch(stamp) if stamp.endswith("Z") or re.search(r"[+-]\d\d:?\d\d$", stamp) else d.local_epoch(stamp[:19])


def line_epoch(line):
    return d.local_epoch(line[:19]) if re.match(r"\d{4}-\d\d-\d\dT", line or "") else None


def clock(stamp):
    """A transcript's time (UTC) on the local clock, as every other time here."""
    at = d.utc_epoch(stamp)
    return time.strftime("%H:%M:%S", time.localtime(at)) if at else str(stamp)[11:19]


def ago(epoch, now):
    return "—" if not epoch else d.span_text(now - epoch) + " ago"


def cut(text, n):
    text = " ".join(str(text or "").split())
    return text if len(text) <= n else text[:n - 1] + "…"


def ids_of(text):
    """The task ids a log line names (`tasks 173, 175 and 181`)."""
    return re.findall(r"\d+", text or "")


def table(rows, cols, limit=None):
    """rows of dicts as aligned columns: cols = [(heading, getter, "<" or ">")]; the last column is not padded."""
    if not rows:
        return ["  (none)"]
    shown = rows[:limit] if limit else rows
    cells = [[str(g(r)) for _, g, _ in cols] for r in shown]
    widths = [max(len(h), *(len(c[i]) for c in cells)) for i, (h, _, _) in enumerate(cols)]
    fmt = lambda vals: "  " + "  ".join(v.rjust(w) if cols[i][2] == ">" else v.ljust(w) if i < len(cols) - 1 else v
                                        for i, (v, w) in enumerate(zip(vals, widths)))
    out = [fmt([h for h, _, _ in cols]).rstrip()] + [fmt(c).rstrip() for c in cells]
    if limit and len(rows) > limit:
        out.append(f"  … {len(rows) - limit} more (--rows {len(rows)})")
    return out


def normal(text, n=110):
    """What a message says, its numbers and names made alike: the key it is grouped by."""
    text = re.sub(r"\b(implement|fix|review|design|brief|investigate|plan|kb|ask|layer|churn)-[\d.]+", r"\1-N", str(text or ""))
    return cut(re.sub(r"[0-9a-f]{8,}", "H", re.sub(r"\d+(\.\d+)?", "N", text)), n)


def parse_since(text, now):
    if text in ("all", "0"):
        return 0.0
    if text == "last":
        return read_mark().get("at") or now - 3 * 3600
    m = re.fullmatch(r"(\d+(?:\.\d+)?)([mhd])", text)
    if m:
        return now - float(m.group(1)) * {"m": 60, "h": 3600, "d": 86400}[m.group(2)]
    t = d.local_epoch(text if len(text) > 16 else text + ":00")
    if t is None:
        raise SystemExit(f"--since: {text!r} is neither 3h/90m/2d, a local time 2026-09-24T10:00, last, nor all")
    return t


def read_mark():
    try:
        return json.load(open(MARK))
    except (OSError, ValueError):
        return {}


def project_rel(path):
    return os.path.relpath(path, v2.PROJECT) if path.startswith(v2.PROJECT + os.sep) else path


# ---------------------------------------------------------------- the sources, each read once and when asked for

class Run:
    """Everything the console reads, and what the run wrote, each read once when something asks for it — a drill-down
    into one session reads that session's transcript and nothing else."""

    def __init__(self, since, quick=False):
        self.now, self.since, self.quick = time.time(), since, quick

    @property
    def hours(self):
        return (self.now - self.since) / 3600 if self.since else 0

    @functools.cached_property
    def st(self):
        return v2.peek()

    @functools.cached_property
    def overview(self):
        return d.overview()

    @functools.cached_property
    def going(self):
        return bool(self.overview.get("active")) and not self.overview.get("stopped")

    @functools.cached_property
    def graph(self):
        return d.graph(max(6.0, self.hours) if self.since else 1e6)

    @functools.cached_property
    def machine(self):
        return d.machine()

    @functools.cached_property
    def checks(self):
        return d.checks()

    @functools.cached_property
    def bases(self):
        if not self.quick:
            d.measure_bases()   # the staleness the Bases view shows
            d.project_bases()   # what a build from scratch would hold
        return d.bases()

    @functools.cached_property
    def builds(self):
        return d.builds()

    @functools.cached_property
    def costs(self):
        return d.costs(self.hours)

    @functools.cached_property
    def log_all(self):
        return d.log_tail(10_000_000)

    @functools.cached_property
    def log(self):
        return [x for x in self.log_all if (line_epoch(x) or 0) >= self.since]

    @functools.cached_property
    def warm(self):
        try:
            return open(os.path.join(v2.STATE, "warm.log"), errors="ignore").read().splitlines()
        except OSError:
            return []

    @functools.cached_property
    def records(self):
        return d.all_sessions(archive=True)

    @functools.cached_property
    def sessions(self):
        return {n: dict(d.session_summary(n, s), record=s) for n, s in self.records.items()}

    @functools.cached_property
    def window(self):
        """The sessions standing now and those active in the window."""
        return [s for s in self.sessions.values() if standing(s)
                or max(d.utc_epoch(s.get("last")) or 0, s.get("started") or 0, s.get("ended") or 0) >= self.since]

    @functools.cached_property
    def status(self):
        return v2.softly("the harness's status", v2.status_text, default="")

    def ran(self, s):
        end = s.get("ended") or d.utc_epoch(s.get("last")) or self.now
        return end - s["started"] if s.get("started") else None


def live(s):
    """A session holding its slot now (v2.LIVE)."""
    return s.get("state") in v2.LIVE and not s.get("released")


def standing(s):
    """A session not let go: live, or parked, idle or done and held (its task may come back to it, its review may ask
    it again) — never ended while it stands."""
    return not s.get("released") and not s.get("archived") and s.get("state") not in ("lost", None)


# ---------------------------------------------------------------- extraction: the tasks' stages, from the log

# (stage, pattern): each log line that moves a task, and the stage it moves it to. A stage with a colon, or one that
# queues or waits, is time waiting; the rest is time worked on (WORKING).
STAGES = [
    ("working", r"^(?:started|resumed) (?:implement|fix|design|investigate|brief)-(\d+)"),
    ("working", r"^task (\d+) goes back to "),
    ("result, awaiting its check", r"^result of task (\d+): "),
    ("check queue", r"^task (\d+)'s check waits for the next batch"),
    ("check queue", r"^task (\d+)'s session asks for the repository's check of its work"),
    ("check: machine", r"^the check of tasks? ([\d, and]+) waits for the machine"),
    ("checking", r"^the work of tasks? ([\d, and]+) is checked together with main"),
    ("checked, awaiting review", r"^the check of tasks? ([\d, and]+): (?:passed|failed)"),
    ("review", r"^(?:started|resumed) review-(\d+)"),
    ("landing queue", r"^task (\d+) is committed on its branch and waits to land"),
    ("landing: tree", r"^the landing of task (\d+) waits for what stands uncommitted"),
    ("landing: machine", r"^the landing of task (\d+) lets main go while its check with what landed waits"),
    ("landing check", r"^the train of tasks ([\d, and]+) is checked together with main"),
    ("landing check", r"^task (\d+) lands on what landed since its check"),
    ("landed", r"^the train of tasks ([\d, and]+) landed as"),
    ("parked: probe", r"^task (\d+)'s probe waits for room on the machine"),
    ("probing", r"^task (\d+)'s queued probe started"),
    ("working", r"^task (\d+)'s queued probe ran"),
    ("parked: measurement", r"^task (\d+) waits for the machine to empty, for a measurement"),
    ("measuring", r"^task (\d+) holds the machine for a measurement"),
    ("working", r"^the measurement of task (\d+) ended"),
    ("waits: planner", r"^task (\d+) waits for task \d+, which is with the planner"),
    ("planner", r"^task (\d+) has stood with the planner"),
    ("working", r"^the run task (\d+) parked for has ended"),
]
STAGE_RES = [(stage, re.compile(p)) for stage, p in STAGES]
WORKING = {"working", "review", "checking", "landing check", "probing", "measuring"}


def task_events(r):
    """{task: [(epoch, stage, line)]} over the whole log, oldest first: the stages each task passed through."""
    out = collections.defaultdict(list)
    for line in r.log_all:
        at = line_epoch(line)
        if not at:
            continue
        said = line[20:]
        for stage, rx in STAGE_RES:
            m = rx.search(said)
            if m:
                for tid in ids_of(m.group(1)):
                    out[tid].append((at, stage, said))
                break
    return out


def run_end(r):
    """Until when time counts: now while the run goes, else the moment it stopped (or its last line): a stopped run's
    open tasks wait for nobody."""
    if r.going:
        return r.now
    stopped = d.local_epoch(str(r.overview.get("stopped") or "")[:19]) if r.overview.get("stopped") else None
    return stopped or max((line_epoch(x) or 0 for x in r.log_all[-50:]), default=r.now) or r.now


def stage_times(r):
    """(the seconds each stage held tasks within the window, summed over tasks; {task: (stage, since)} for every task
    still open — its stage as the state says it now, since the line that moved it last; the tasks landed in the window).
    A task's time in a stage runs from the line that moved it there to the next that moved it on — or, while it is
    open, to now (to the run's stop, when it is stopped)."""
    events, nodes = task_events(r), {n["id"]: n for n in r.graph["nodes"] if not n["done"]}
    spent, current, landed = collections.Counter(), {}, []
    stop = run_end(r)
    for tid, es in events.items():
        for (at, stage, _), nxt in zip(es, es[1:] + [None]):
            end = nxt[0] if nxt else (stop if tid in nodes else at)
            lo, hi = max(at, r.since), min(end, stop)
            if hi > lo and stage != "landed":
                spent[stage] += hi - lo
            if stage == "landed" and at >= r.since:
                landed.append((tid, at))
        if tid in nodes and es:
            n = nodes[tid]
            current[tid] = (f"{n['group']}: {cut(n['status'], 40)}", es[-1][0])
    return spent, current, landed


def waits(r):
    """Where the tasks' time went, as data: {stages: [(stage, seconds, share, waiting?)], waiting, working, throughput
    (landed an hour), landed, current: [(task, stage, since)] of the open tasks, longest first}."""
    spent, current, landed = stage_times(r)
    total = sum(spent.values()) or 1
    rows = [(stage, secs, secs / total, stage not in WORKING) for stage, secs in spent.most_common()]
    span = (r.now - r.since) if r.since else ((r.now - min(at for _, at in landed)) if landed else 0)
    return dict(stages=rows, waiting=sum(x[1] for x in rows if x[3]), working=sum(x[1] for x in rows if not x[3]),
                landed=landed, throughput=len(landed) / (span / 3600) if span > 0 else None,
                current=sorted(((t, s, at) for t, (s, at) in current.items()), key=lambda x: x[2]), until=run_end(r))


# ---------------------------------------------------------------- extraction: checks, each run counted once

# a run of the repository's check: a batch's, a train's, a landing's — each said once by the harness when it ends. The
# lines that tell a session its check's verdict, and the per-task verdicts after a batch, are not runs.
RUN_RES = [("batch", re.compile(r"^the check of tasks? ([\d, and]+): (passed|failed) in (\d+) s")),
           ("train", re.compile(r"^the train of tasks ([\d, and]+): its check (passed|failed) in (\d+) s")),
           ("landing", re.compile(r"^landing check of task (\d+): (passed|failed) in (\d+) s"))]
VERDICT = re.compile(r"^check of task (\d+): (passed|failed|did not run)(?: \((.*)\))?")


def check_runs(r):
    """(the runs in the window [(at, kind, tasks, verdict, seconds)], the per-task verdicts [(at, task, verdict, why)],
    what the harness said of each failed batch [(at, line)])."""
    runs, verdicts, said = [], [], []
    for line in r.log:
        at, text = line_epoch(line), line[20:]
        for kind, rx in RUN_RES:
            m = rx.search(text)
            if m:
                runs.append((at, kind, ids_of(m.group(1)), m.group(2), int(m.group(3))))
                break
        m = VERDICT.search(text)
        if m:
            verdicts.append((at, m.group(1), m.group(2), m.group(3) or ""))
        if re.search(r"^the batch of tasks .* failed its check", text):
            said.append((at, text))
    return runs, verdicts, said


# ---------------------------------------------------------------- extraction: calls that did not deliver

def group_id(key):
    return hashlib.sha1(key.encode()).hexdigest()[:10]


def undelivered(r):
    """{(kind, key): [(session, role, request, text)]} of the window's calls refused (a v2.py command refused its input),
    stopped (the harness's guard stopped the call before it ran) or failed (a command's exit, the tool's failure),
    grouped by what came back, whoever received it; and the count of the harness's notes beside calls."""
    groups, notes = collections.defaultdict(list), 0
    for s in r.window:
        if not (s.get("refused") or s.get("stopped") or s.get("failed") or s.get("notes")):
            continue
        for it in (d.session_turns(s["record"]) or {}).get("items") or []:
            if it["kind"] != "request" or (d.utc_epoch(it["at"]) or 0) < r.since:
                continue
            for c in it["calls"]:
                notes += len(c["notes"])
                text = c["refused"] or c.get("stopped") or (c["result"] if c["error"] else None)
                if not text:
                    continue
                kind = "refused" if c["refused"] else "stopped" if c.get("stopped") else "failed"
                # grouped by what it says, its line breaks folded (a refusal's reason is on its second line)
                groups[(kind, normal(text))].append((s["name"], s.get("role") or "?", it["n"], text))
    return groups, notes


def lost_sessions(r):
    """[(session, what happened)] of the window's sessions that were lost: a start never confirmed (no transcript), or a
    session given up, with the harness's reason where it recorded one (watchdog.lost)."""
    failed_starts = {m.group(1) for m in (re.search(r"start of (\S+) not confirmed", x) for x in r.log) if m}
    out = []
    for s in r.window:
        if s.get("state") != "lost":
            continue
        rec = s["record"]
        if s["name"] in failed_starts or not rec.get("sid"):
            out.append((s, "its start was never confirmed"))
        elif not s.get("requests") and not s.get("cost"):
            out.append((s, "lost; its transcript is gone, so what it did is unknown"
                        + (f" — {rec['lost_why']}" if rec.get("lost_why") else "")))
        else:
            out.append((s, f"lost after {s.get('requests')} requests, {k(s.get('cost'))} of cost"
                        + (f": {rec['lost_why']}" if rec.get("lost_why") else "")))
    return out


def unreached(r):
    """The window's messages and answers that reached nobody: [(at, line)]."""
    return [(line_epoch(x), x[20:]) for x in r.log
            if re.search(r"reached nobody|could not be delivered|not delivered", x)]


# ---------------------------------------------------------------- extraction: errors

ERROR_RE = re.compile(r"ATTENTION|FAILED|Traceback|watchdog error|not confirmed|could not|[Ee]rror:|was not "
                      r"(recorded|resumed|held|started)|the API failed")


def errors(r):
    """{source: {pattern: [line]}} of the window's error lines: the harness's log, the bases' log (warm.log), the
    watchdog's own log, and each session's API errors (state/api-errors-NAME)."""
    out = collections.defaultdict(lambda: collections.defaultdict(list))
    for source, lines in (("v2.log", r.log_all), ("warm.log", r.warm)):
        entries = []
        for x in lines:  # a line without a time continues the one before (a traceback's frames): one entry
            if line_epoch(x) or not entries:
                entries.append([x])
            else:
                entries[-1].append(x)
        for e in entries:
            if (line_epoch(e[0]) or 0) < r.since or not ERROR_RE.search(e[0][20:]):
                continue
            said = e[0][20:] + (f" … {e[-1].strip()}" if len(e) > 1 else "")
            out[source][normal(said, 140)].append(e[0][:20] + said)
    for path in glob.glob(os.path.join(v2.STATE, "api-errors-*")):
        if os.path.getmtime(path) >= r.since:
            text = open(path, errors="ignore").read().strip()
            out["api errors"][f"{os.path.basename(path)[11:]}: {normal(text.splitlines()[-1] if text else '', 70)}"].append(
                f"{time.strftime('%Y-%m-%dT%H:%M:%S', time.localtime(os.path.getmtime(path)))} {cut(text, 300)}")
    return out


# ---------------------------------------------------------------- extraction: economics

def economics(r):
    """What the costs say beyond their totals: the sessions held warm whose pings cost more than their use, the tasks
    whose cost is past three times the median task's, the tasks that went round (fixes and reviews again), and each
    role's share of wall time spent idle."""
    c = r.costs
    held = [h for h in r.bases.get("held") or [] if (h.get("ping_cost") or 0) >= 500_000]
    tasks = c.get("tasks") or []
    median = statistics.median([x["cost"] for x in tasks]) if tasks else 0
    outliers = [x for x in tasks if median and x["cost"] >= 3 * median]
    rounds = []
    for tid, t in r.st["tasks"].items():
        if t.get("stage") in ("done", "deleted"):
            continue
        if (t.get("rejections") or 0) >= 2 or (t.get("checks_failed") or 0) >= 2:
            rounds.append((tid, t.get("rejections") or 0, t.get("checks_failed") or 0, t.get("stage")))
    idle = {}
    for s in r.window:
        role = s.get("role") or "?"
        a = idle.setdefault(role, [0, 0])
        a[0] += s.get("idle_s") or 0
        a[1] += (s.get("model_s") or 0) + (s.get("tools_s") or 0) + (s.get("idle_s") or 0)
    return dict(held=held, outliers=outliers, median=median, rounds=sorted(rounds, key=lambda x: -(x[1] + x[2])),
                idle={role: a[0] / a[1] for role, a in idle.items() if a[1]})


# ---------------------------------------------------------------- the findings: checks over all of the above

class Finding(dict):
    """A finding: tone, area, text, the command that shows its evidence, and a key that names it across passes."""


STATE_AREAS = ("run", "pipeline", "machine", "bases", "attention")


def finding(tone, area, key, text, drill="", kind=None):
    """kind: "state" for a condition that holds now (a pass says it new, standing or resolved), "event" for what
    happened in the window (a pass says the interval's own); by its area unless said."""
    return Finding(tone=tone, area=area, key=f"{area}:{key}", text=text, drill=drill,
                   kind=kind or ("state" if area in STATE_AREAS else "event"))


def findings(r):
    """[Finding]: the console's attention list first, then the checks, each over a pattern rather than a session — a
    guard stop that recurs across sessions is one finding, with its count, the sessions and roles it hit and where to
    read it — worst first."""
    out = [finding(tone, "attention", hashlib.sha1(normal(text).encode()).hexdigest()[:10],
                   text + (f" ({ago(at, r.now)})" if at else ""), f"{ME} findings attention")
           for tone, text, where, at in r.overview["attention"]]
    going, now = r.going, r.now
    # the run itself: the daemon, the watchdog, a stall
    if going and not r.overview.get("daemon"):
        out.append(finding("bad", "run", "daemon", "the run is active and the daemon is down: nothing dispatches, "
                           "checks, lands or pings", f"{ME} log --source watchdog --tail 40"))
    snap = stamp_epoch(r.machine.get("snapshot_at"))
    if going and snap and now - snap > 300:
        out.append(finding("warn", "run", "snapshot", f"the watchdog's snapshot is {dur(now - snap)} old: is it running?",
                           f"{ME} log --source watchdog --tail 40"))
    last = max((line_epoch(x) or 0 for x in r.log_all[-200:]), default=0)
    if going and last and now - last > 1200:
        out.append(finding("warn", "run", "stall", f"nothing has been logged for {dur(now - last)} while the run is "
                           f"active ({len([s for s in r.window if live(s)])} session(s) live)", f"{ME} sessions"))
    # sessions: a call running long, a full context, lost sessions, failed starts
    for s in r.window:
        if not live(s):
            continue
        at = d.utc_epoch(s.get("last_call_at"))
        if going and s.get("last_call_open") and at and now - at > 900:
            out.append(finding("warn", "sessions", f"long-call:{s['name']}", f"{s['name']}'s call has run {dur(now - at)}: "
                               f"{cut(s.get('last_call'), 110)}", f"{ME} session {s['name']} --from -3", kind="state"))
        if (s.get("context") or 0) >= v2.SOFT:
            out.append(finding("warn", "sessions", f"context:{s['name']}", f"{s['name']}'s context is {k(s['context'])}, "
                               f"past the wrap-up line {k(v2.SOFT)}", f"{ME} session {s['name']} --from -3", kind="state"))
    lost = lost_sessions(r)
    by_kind = collections.defaultdict(list)
    for s, what in lost:
        by_kind["start" if "never confirmed" in what else "unknown" if "is unknown" in what else "lost"].append((s, what))
    for kind, xs in by_kind.items():
        names = ", ".join(s["name"] for s, _ in xs[:8]) + (" …" if len(xs) > 8 else "")
        if kind == "lost":
            for s, what in xs:
                out.append(finding("bad", "sessions", f"lost:{s['name']}", f"{s['name']} ({s.get('role')}, task "
                                   f"{s.get('task') or s.get('reviews') or '—'}) {what}", f"{ME} session {s['name']} --from -5"))
        else:
            out.append(finding("warn" if kind == "start" else "info", "sessions", f"{kind}",
                               f"{len(xs)} session(s) {'never started: their start was not confirmed' if kind == 'start' else 'lost, their transcripts gone'}: {names}",
                               f"{ME} log --grep 'not confirmed|lost'"))
    # delivery: each pattern of what did not deliver, across sessions
    groups, _ = undelivered(r)
    for (kind, key), xs in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        sessions = dict.fromkeys(x[0] for x in xs)
        roles = collections.Counter(x[1] for x in xs)
        if len(xs) < 3 and len(sessions) < 2:
            continue
        tone = "warn" if len(xs) >= 5 or len(sessions) >= 3 else "info"
        what = {"refused": "refused", "stopped": "stopped by the guard", "failed": "failed"}[kind]
        out.append(finding(tone, "delivery", f"{kind}:{group_id(key)}",
                           f"{len(xs)} call(s) {what} in {len(sessions)} session(s) ("
                           + ", ".join(f"{role} {n}" for role, n in roles.most_common()) + f"): {key}",
                           f"{ME} delivery {group_id(key)}"))
    unmet = unreached(r)
    if unmet:
        out.append(finding("warn", "delivery", "unreached", f"{len(unmet)} message(s) and answer(s) reached nobody: "
                           + "; ".join(cut(x, 70) for _, x in unmet[-3:]), f"{ME} delivery"))
    # batching: each role's share of requests its protocol puts with the one before, and the worst sessions
    for role, x in batching(r).items():
        if x["requests"] >= 20 and x["joinable"] / x["requests"] >= 0.12:
            worst = ", ".join(f"{s['name']} {s['joinable']}/{s['requests']}" for s in x["worst"][:4])
            out.append(finding("warn", "batching", f"joinable:{role}", f"the {role}s' requests: {x['joinable']} of "
                               f"{x['requests']} joinable with the one before ({x['joinable'] / x['requests']:.0%}); most "
                               f"in {worst}", f"{ME} session {x['worst'][0]['name']} --turns" if x["worst"] else ""))
    # the pipeline: free slots while tasks are ready, overdue parks, heads of long waits
    ready = [n for n in r.graph["nodes"] if n["group"] == "ready"]
    running = [n for n in r.graph["nodes"] if n["group"] == "running"]
    if going and ready and not running and not r.overview["holds"].get("graph"):
        out.append(finding("warn", "pipeline", "idle-slots", f"{len(ready)} task(s) ready and none running: "
                           + ", ".join("#" + n["id"] for n in ready[:8]), f"{ME} waits"))
    for tid, t in r.st["tasks"].items():
        p = t.get("parked") or {}
        if t.get("stage") == "parked" and p.get("since") and now - p["since"] > v2.HOLD_PARK:
            out.append(finding("warn" if going else "info", "pipeline", f"overdue:{tid}",
                               f"#{tid} parked for {p.get('for')} {dur(now - p['since'])}, past its hold of "
                               f"{dur(v2.HOLD_PARK)}", f"{ME} task {tid} --history"))
    for h in r.graph.get("held_up") or []:
        if len(h["waiting"]) >= 5 and h["group"] in ("parked", "planner", "idle"):
            out.append(finding("warn" if going else "info", "pipeline", f"held-up:{h['root']}",
                               f"#{h['root']} ({h['status']}) holds {len(h['waiting'])} open task(s) up, "
                               f"{len(h['direct'])} directly", f"{ME} task {h['root']}"))
    w = waits(r)
    if w["waiting"] + w["working"] > 3600 and w["waiting"] > 1.5 * w["working"]:
        top = [x for x in w["stages"] if x[3]][:3]
        out.append(finding("warn", "pipeline", "waiting", f"the tasks waited {dur(w['waiting'])} and were worked on "
                           f"{dur(w['working'])} in the window; most in " + ", ".join(f"{s} {dur(x)}" for s, x, _, _ in top),
                           f"{ME} waits", kind="event"))
    # checks: queued with nothing to take them, tasks failing again, checks that did not run
    for kind, rows, alive, who in (("check", r.checks["batches"], r.checks["batcher"], "no batch runs"),
                                   ("landing", r.checks["trains"], r.checks["lander"], "no train lands")):
        waiting = [x for x in rows if not x["decided"] and x.get("queued") and now - x["queued"] > 900]
        if going and waiting and not alive:
            out.append(finding("warn", "checks", f"stuck:{kind}", f"{len(waiting)} {kind}(s) queued over 15 min and {who}: "
                               + ", ".join("#" + x["task"] for x in waiting[:8]), f"{ME} checks", kind="state"))
    runs, verdicts, _ = check_runs(r)
    failing = collections.Counter(t for _, t, v, _ in verdicts if v == "failed")
    for tid, n in failing.items():
        if n >= 2:
            out.append(finding("warn", "checks", f"failing:{tid}", f"task {tid}'s check failed {n}× in the window",
                               f"{ME} check {tid}"))
    unrun = [(t, why) for _, t, v, why in verdicts if v == "did not run"]
    if unrun:
        out.append(finding("warn", "checks", "unrun", f"{len(unrun)} check(s) did not run: "
                           + "; ".join(f"#{t} ({cut(why, 60)})" for t, why in unrun[:4]), f"{ME} log --grep 'did not run'"))
    # the machine
    mem, floor = r.machine.get("memory_available_gb"), r.machine["limits"]["memory_floor_gb"]
    if mem is not None and mem < floor:
        out.append(finding("bad", "machine", "memory", f"{mem:.1f} GiB free, under the {floor} GiB floor", f"{ME} report --only machine"))
    # errors: each pattern once
    for source, pats in errors(r).items():
        for key, lines in sorted(pats.items(), key=lambda kv: -len(kv[1]))[:12]:
            tone = "bad" if re.search(r"Traceback|watchdog error|FAILED", key) else "warn"
            out.append(finding(tone, "errors", f"{source}:{hashlib.sha1(key.encode()).hexdigest()[:10]}",
                               f"{source} ×{len(lines)}: {key}", f"{ME} errors"))
    # economics
    t, p = r.costs["total"], r.costs["previous"]
    inputs = t["read"] + t["write"] + t["input"]
    if inputs and t["read"] / inputs < 0.9:
        out.append(finding("warn", "economics", "cache", f"{t['read'] / inputs:.1%} of the input tokens read from cache "
                           "in the window (under 90%): prefixes are written anew", f"{ME} report --only costs"))
    if t["requests"] >= 50 and p["requests"] >= 50:
        now_per, before = t["cost"] / t["requests"], p["cost"] / p["requests"]
        if now_per > before * 1.25:
            out.append(finding("warn", "economics", "request-cost", f"a request costs {k(now_per)}, {now_per / before - 1:.0%} "
                               f"more than in the span before ({k(before)})", f"{ME} report --only costs"))
    cold = r.costs.get("cold") or []
    if cold:
        out.append(finding("warn", "economics", "cold-forks", f"{len(cold)} fork(s) wrote their prefix anew at their first "
                           f"request ({k(sum(x['cost'] for x in cold))} of cost): " + ", ".join(
                               f"{x['name']} of {x['origin']}" for x in cold[:5]), f"{ME} report --only costs"))
    for kind, x in (("keep-warm pings", r.costs["keep"]), ("loads", r.costs["loads"])):
        if x["missed"]:
            out.append(finding("warn", "economics", f"missed:{kind}", f"{x['missed']} of {x['count']} {kind} found their "
                               "entry cold", f"{ME} report --only costs"))
    e = economics(r)
    for h in e["held"]:
        out.append(finding("warn", "economics", f"held:{h['name']}", f"{h['name']} is held warm ({h['held']}): "
                           f"{h['pings']} pings, {k(h['ping_cost'])}", f"{ME} session {h['name']} --from -2", kind="state"))
    for x in e["outliers"][:6]:
        out.append(finding("info", "economics", f"task-cost:{x['task']}", f"task #{x['task']} cost {k(x['cost'])} in "
                           f"{x['sessions']} session(s), {x['cost'] / e['median']:.1f}× the median task's: "
                           f"{cut(x.get('subject'), 60)}", f"{ME} task {x['task']}"))
    for tid, rej, failed, stage in e["rounds"][:6]:
        out.append(finding("info", "economics", f"rounds:{tid}", f"task #{tid} went round: {rej} rejection(s), {failed} "
                           f"failed check(s) (now {stage})", f"{ME} task {tid} --history", kind="state"))
    # the bases
    for b in r.bases["bases"]:
        forked = next((x for x in b["parts"] if x["forked"]), None)
        if going and forked and not forked["entry"]["warm"]:
            out.append(finding("warn", "bases", f"cold:{b['who']}", f"the {b['who']} {forked['part']} its roles fork is "
                               f"cold: the next fork writes its prefix whole ({k(forked['context'])})", f"{ME} base {b['who']}"))
        if b.get("orphan_delta"):
            out.append(finding("warn", "bases", f"orphan:{b['who']}", f"the {b['who']} delta stands on another layer "
                               "than the recorded one", f"{ME} base {b['who']}"))
    for who, proj in (r.bases.get("projected") or {}).items():
        if proj and proj.get("valid") is False:
            out.append(finding("warn", "bases", f"projection:{who}", f"the {who} projection from scratch failed: "
                               f"{cut(proj.get('error'), 140)}", f"{ME} base {who}"))
    for x in r.builds["bases"]:
        if x["status"] and "not built" in x["status"]:
            out.append(finding("warn", "bases", f"build:{x['who']}", f"the {x['who']} layer: {x['status']}", f"{ME} base {x['who']}"))
    order = {"bad": 0, "warn": 1, "info": 2}
    return sorted(out, key=lambda f: order[f["tone"]])


# ---------------------------------------------------------------- batching, by role

def in_window(r, s):
    """A session as its requests in the window count it: whole when it began in the window, else its requests since —
    a standing session's history before the window is no finding of the window."""
    if not r.since or (s.get("started") or 0) >= r.since:
        return s
    reqs = [it for it in (d.session_turns(s["record"]) or {}).get("items") or []
            if it["kind"] == "request" and (d.utc_epoch(it["at"]) or 0) >= r.since]
    if not reqs:
        return None
    return dict(s, requests=len(reqs), calls=sum(len(q["calls"]) for q in reqs),
                ops=round(sum(q.get("ops") or 0 for q in reqs) / len(reqs), 2),
                joinable=sum(1 for q in reqs if q.get("joinable")), first_change=None)


def batching(r):
    """{role: {sessions, requests, calls, ops, joinable, first (requests before its first change, median), model, tools,
    idle, worst (its sessions with the most joinable requests)}} of the requests made in the window."""
    by = collections.defaultdict(list)
    for s in r.window:
        s = in_window(r, s) if s.get("requests") else None
        if s and s.get("requests"):
            by[s.get("role") or "?"].append(s)
    out = {}
    for role, ss in sorted(by.items()):
        req = sum(s["requests"] for s in ss)
        out[role] = dict(sessions=len(ss), requests=req, calls=sum(s.get("calls") or 0 for s in ss),
                         ops=sum((s.get("ops") or 0) * s["requests"] for s in ss),
                         joinable=sum(s.get("joinable") or 0 for s in ss),
                         first=statistics.median([s["first_change"] - 1 for s in ss if s.get("first_change")] or [0]),
                         model=sum(s.get("model_s") or 0 for s in ss), tools=sum(s.get("tools_s") or 0 for s in ss),
                         idle=sum(s.get("idle_s") or 0 for s in ss),
                         worst=sorted((s for s in ss if s.get("joinable")), key=lambda s: -s["joinable"] / s["requests"]))
    return out


# ---------------------------------------------------------------- the report's sections

def s_findings(r, rows, area=None):
    f = [x for x in findings(r) if not area or x["area"] == area]
    counts = collections.Counter(x["tone"] for x in f)
    out = [f"== FINDINGS ({counts['bad']} bad, {counts['warn']} warn, {counts['info']} info)"]
    for x in f:
        out.append(f"  {TONES[x['tone']]} {x['area']:10} {x['text']}" + (f"\n{' ' * 18}→ {x['drill']}" if x["drill"] else ""))
    return out if f else out + ["  nothing found"]


def s_run(r, rows):
    o, now = r.overview, r.now
    state = ("stopped since " + d.local_clock(d.local_epoch(o["stopped"]))) if o.get("stopped") else \
        "running" if o.get("active") else "inactive"
    last = next((x for x in reversed(r.log_all) if re.match(r"\d{4}-", x)), None)
    holds = [h for h, v in o["holds"].items() if v]
    counts = collections.Counter("live" if live(s) else s.get("state") for s in r.window if standing(s))
    out = [f"== RUN {time.strftime('%Y-%m-%d %H:%M')} · window: " + ("everything" if not r.since else
           f"since {d.local_clock(r.since)} ({dur(now - r.since)})"),
           f"  state {state} · daemon {'up' if o.get('daemon') else 'down'} · holds {', '.join(holds) or 'none'} · "
           + ", ".join(f"{n} {kind}" for kind, n in counts.most_common()) + " standing · last event "
           + (f"{ago(line_epoch(last), now)}: {cut(last[20:], 100)}" if last else "—"),
           "  switches " + ", ".join(f"{n} {'on' + (' (' + v['value'] + ')' if v['value'] else '') if v['on'] else 'off'}"
                                     for n, v in o["switches"].items())]
    out += ["  harness status:"] + ["    " + x for x in r.status.splitlines()]
    return out


def session_cols(r):
    return [("session", lambda s: s["name"], "<"), ("role", lambda s: s.get("role") or "", "<"),
            ("task", lambda s: s.get("task") or s.get("reviews") or "—", ">"), ("state", lambda s: s.get("state") or "", "<"),
            ("ran", lambda s: dur(r.ran(s)), ">"), ("req", lambda s: s.get("requests") if s["record"].get("sid") else "?", ">"),
            ("ops/req", lambda s: s.get("ops") or "—", ">"),
            ("1st chg", lambda s: (s["first_change"] - 1) if s.get("first_change") else "—", ">"),
            ("join", lambda s: s.get("joinable") or "", ">"), ("refused", lambda s: s.get("refused") or "", ">"),
            ("stopped", lambda s: s.get("stopped") or "", ">"), ("failed", lambda s: s.get("failed") or "", ">"),
            ("ctx", lambda s: k(s.get("context")), ">"), ("cost", lambda s: k(s.get("cost")), ">"),
            ("model/calls/idle", lambda s: f"{dur(s.get('model_s'))}/{dur(s.get('tools_s'))}/{dur(s.get('idle_s'))}", ">")]


def s_sessions(r, rows):
    now_ = sorted((s for s in r.window if live(s)), key=lambda s: s["name"])
    held = sorted((s for s in r.window if standing(s) and not live(s)), key=lambda s: s["name"])
    out = [f"== SESSIONS: {len(now_)} live, {len(held)} standing (parked, idle or held)"] + table(now_, session_cols(r))
    for s in now_:
        if s.get("last_call"):
            at = d.utc_epoch(s.get("last_call_at"))
            out.append(f"    {s['name']}: {'running ' + dur(r.now - at) if s.get('last_call_open') and at else 'last call'}: "
                       f"{cut(s['last_call'], 150)} · last activity {ago(d.utc_epoch(s.get('last')), r.now)}")
    out += ["  standing:"] + table(held, session_cols(r))
    ended = sorted((s for s in r.window if not standing(s)), key=lambda s: -(s.get("started") or 0))
    out += [f"  ended in the window: {len(ended)}"] + table(ended, session_cols(r) + [
        ("produced", lambda s: cut(", ".join(s.get("produced") or []), 60), "<")], rows)
    return out


def s_pipeline(r, rows):
    g = r.graph
    counts = collections.Counter(n["group"] for n in g["nodes"] if not n["done"])
    out = ["== PIPELINE: " + ", ".join(f"{v} {k_}" for k_, v in counts.most_common()) + f" · queue {len(g['queue'])}"]
    lanes = ["running", "fix", "review", "check", "train", "parked", "planner", "ready", "idle"]
    moving = [n for n in g["nodes"] if not n["done"] and n["group"] != "waiting"]
    out += table(sorted(moving, key=lambda n: (lanes.index(n["group"]) if n["group"] in lanes else 9,
                                               int(n["id"]) if n["id"].isdigit() else 0)),
                 [("task", lambda n: "#" + n["id"], "<"), ("kind", lambda n: n.get("kind") or "", "<"),
                  ("group", lambda n: n["group"], "<"), ("holds", lambda n: n.get("holds") or "", ">"),
                  ("status", lambda n: cut(n["status"], 50) + (f" for {dur(r.now - n['parked_since'])}"
                                                               if n.get("parked_since") else ""), "<"),
                  ("subject", lambda n: cut(n["subject"], 70), "<")], rows)
    out.append("  held up (the heads of the chains of waits, most held first):")
    for h in (g.get("held_up") or [])[:rows]:
        out.append(f"    #{h['root']} {h.get('kind') or ''} [{cut(h['status'], 40)}] holds {len(h['waiting'])} "
                   f"({len(h['direct'])} directly): " + " ".join("#" + x for x in h["waiting"][:16])
                   + (" …" if len(h["waiting"]) > 16 else ""))
    landed = [n for n in g["nodes"] if n["done"]]
    out.append(f"  done in the window: {len(landed)}" + (": " + ", ".join(f"#{n['id']}" for n in landed[:30])
                                                           + (" …" if len(landed) > 30 else "") if landed else ""))
    return out


def s_waits(r, rows):
    w = waits(r)
    total = w["waiting"] + w["working"]
    out = [f"== WAITS: the tasks' time in the window, {dur(total)} in all — worked on {dur(w['working'])}, waiting "
           f"{dur(w['waiting'])} · landed {len(w['landed'])}"
           + (f", {w['throughput']:.2f} an hour" if w["throughput"] is not None else "")]
    out += table([dict(stage=s, secs=x, share=sh, wait=wt) for s, x, sh, wt in w["stages"]],
                 [("stage", lambda x: x["stage"], "<"), ("time", lambda x: dur(x["secs"]), ">"),
                  ("share", lambda x: f"{x['share']:.0%}", ">"), ("", lambda x: "waiting" if x["wait"] else "worked on", "<")])
    out.append("  the open tasks, longest in their stage first:")
    out += [f"    #{t} {stage} for {dur(w['until'] - at)}" for t, stage, at in w["current"][:rows]]
    if w["until"] < r.now - 60:
        out.append(f"  (the run stopped {ago(w['until'], r.now)}: time is counted to then)")
    return out


def s_machine(r, rows):
    m = r.machine
    load, lim = m.get("load") or {}, m["limits"]
    snap = stamp_epoch(m.get("snapshot_at"))
    stale = snap and r.now - snap > 300
    out = [f"== MACHINE (the watchdog's snapshot of {d.local_clock(snap)}, {ago(snap, r.now)}"
           + (": the slots and runs below are as it saw them then" if stale else "") + ")",
           f"  heavy {load.get('heavy', 0)}/{lim['heavy']} · probes {load.get('probe', 0)}/{lim['probes']} · memory free "
           f"{(m.get('memory_available_gb') or 0):.1f} GiB (floor {lim['memory_floor_gb']}) · load {' / '.join(m.get('loadavg') or [])} "
           f"of {m.get('cpus')} threads · measurement window {m.get('measure_seconds')} s",
           f"  held by {('task ' + str(m['claim'].get('task')) + ': ' + cut(m['claim'].get('why'), 80)) if m.get('claim') else 'nobody'}"
           + (f" · waiting to hold it: task {m['pending'].get('task')}" if m.get("pending") else "")
           + (" · sharing it: " + ", ".join(f"task {x['task']}" for x in m["shared"]) if m.get("shared") else "")]
    out += [f"  {x['kind']:5} {x['processes']} proc {x['rss_mb'] / 1024:.1f} GiB {'session' if x['session'] else 'harness'}: "
            f"{cut(x['command'], 120)}" for x in m.get("runs") or []]
    queued = [x for x in m.get("probe_queue") or [] if not x.get("decided")]
    if queued:
        out.append("  probes queued: " + ", ".join(f"task {x['task']} ({ago(x.get('queued'), r.now)})" for x in queued))
    occ = [list(map(float, x.split()[:3])) for x in m.get("occupancy") or [] if len(x.split()) >= 2]
    if occ:
        working = [x[1] for x in occ]
        out.append(f"  the last {len(occ)} min: {statistics.mean(working):.2f} sessions working on average, at most "
                   f"{max(working):.0f}; {sum(1 for x in working if x == 0)} min with none working")
    if r.overview.get("occupancy"):
        out += ["  " + x for x in r.overview["occupancy"].splitlines()]
    return out


def s_checks(r, rows):
    c = r.checks
    out = [f"== CHECKS AND LANDINGS: batcher {'running' if c['batcher'] else 'idle'} · lander {'running' if c['lander'] else 'idle'}"]
    for title, q in (("check queue", c["batches"]), ("landing queue", c["trains"])):
        waiting = [x for x in q if not x["decided"]]
        decided = [x for x in q if x["decided"] and (x.get("decided_at") or 0) >= r.since]
        spans = [x["decided_at"] - x["queued"] for x in decided if x.get("queued") and x.get("decided_at")]
        out.append(f"  {title}: {len(waiting)} waiting" + (": " + ", ".join(f"#{x['task']} {ago(x.get('queued'), r.now)}"
                                                                              for x in waiting) if waiting else "")
                   + f" · {len(decided)} decided in the window"
                   + (f", queued to decided {dur(statistics.median(spans))} median, {dur(max(spans))} at most" if spans else ""))
    runs, verdicts, said = check_runs(r)
    by = collections.Counter((kind, v) for _, kind, _, v, _ in runs)
    secs = [x[4] for x in runs]
    out.append(f"  runs in the window: {len(runs)} (" + ", ".join(f"{kind} {v} {n}" for (kind, v), n in sorted(by.items()))
               + ")" + (f", {statistics.median(secs):.0f} s median, {max(secs)} s at most" if secs else ""))
    out += [f"    {time.strftime('%H:%M', time.localtime(at))} {kind} {' '.join('#' + t for t in ts)}: {v} in {s} s"
            for at, kind, ts, v, s in runs[-rows:]]
    per = collections.Counter(v for _, _, v, _ in verdicts)
    out.append("  verdicts per task: " + (", ".join(f"{v} {n}" for v, n in per.most_common()) or "none"))
    for at, text in said[-rows:]:
        out.append(f"    {time.strftime('%H:%M', time.localtime(at))} {cut(text, 180)}")
    for title, logs in (("batch logs", c["batch_logs"]), ("train logs", c["train_logs"])):
        going = [x for x in logs if x["growing"]]
        if going:
            out.append(f"  {title} growing now: " + ", ".join(f"{x['name']} ({k(x['size'])})" for x in going))
    return out


def s_batching(r, rows):
    b = batching(r)
    out = ["== BATCHING (the window's sessions, by role)"]
    out += table([dict(x, role=role) for role, x in b.items()],
                 [("role", lambda x: x["role"], "<"), ("sessions", lambda x: x["sessions"], ">"),
                  ("requests", lambda x: x["requests"], ">"), ("calls/req", lambda x: f"{x['calls'] / x['requests']:.2f}", ">"),
                  ("ops/req", lambda x: f"{x['ops'] / x['requests']:.2f}", ">"),
                  ("joinable", lambda x: f"{x['joinable'] / x['requests']:.0%}", ">"),
                  ("req before 1st change (median)", lambda x: x["first"], ">"),
                  ("model / calls / idle", lambda x: f"{dur(x['model'])} / {dur(x['tools'])} / {dur(x['idle'])}", ">")])
    worst = sorted((s for x in b.values() for s in x["worst"] if s["requests"] >= 4),
                   key=lambda s: -s["joinable"] / s["requests"])[:rows]
    if worst:
        out.append("  most joinable requests (a session's requests its protocol puts with the one before):")
        out += [f"    {s['name']}: {s['joinable']} of {s['requests']}, {s.get('ops')} ops a request" for s in worst]
    return out


LABEL = {"refused": "refused", "stopped": "stopped by the guard", "failed": "failed"}


def s_delivery(r, rows, grep=None, gid=None):
    """What did not deliver, by pattern; one pattern whole (`delivery ID`: every call, what it said in full)."""
    groups, notes = undelivered(r)
    counts = collections.Counter(kind for kind, _ in groups for _ in groups[(kind, _)])
    out = ["== DELIVERY: " + ", ".join(f"{counts[x]} {LABEL[x]}" for x in ("refused", "stopped", "failed"))
           + f" calls; {notes} notes from the harness beside calls (the window)"]
    shown = 0
    for (kind, key), xs in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        if (grep and not re.search(grep, key + " " + xs[0][3])) or (gid and group_id(key) != gid):
            continue
        roles = collections.Counter(x[1] for x in xs)
        out.append(f"  {LABEL[kind]} ×{len(xs)} ({', '.join(f'{role} {n}' for role, n in roles.most_common())}) "
                   f"[{group_id(key)}]: {key}")
        if gid:
            for name, role, q, text in xs:
                out.append(f"    {name}#{q} ({role}; `session {name} --from {q} --to {q} --full`): {text}")
            continue
        out.append(f"      in {cut(', '.join(dict.fromkeys(f'{n}#{q}' for n, _, q, _ in xs)), 160)}")
        out.append(f"      e.g. {cut(xs[0][3], 400)}")
        shown += 1
        if not grep and shown >= rows:
            out.append(f"  … {len(groups) - shown} more pattern(s): --rows, or `delivery ID` for one whole")
            break
    unmet = unreached(r)
    out.append(f"  reached nobody ({len(unmet)}):")
    out += [f"    {time.strftime('%m-%d %H:%M', time.localtime(at))} {cut(x, 180)}" for at, x in unmet[-rows:]]
    lost = lost_sessions(r)
    out.append(f"  lost sessions and failed starts ({len(lost)}):")
    out += [f"    {s['name']} ({s.get('role')}, task {s.get('task') or s.get('reviews') or '—'}): {what}" for s, what in lost[-rows:]]
    return out


def s_errors(r, rows):
    e = errors(r)
    out = [f"== ERRORS (the window): " + ", ".join(f"{src} {sum(map(len, pats.values()))}" for src, pats in e.items())
           if e else "== ERRORS (the window): none"]
    for src, pats in e.items():
        for key, lines in sorted(pats.items(), key=lambda kv: -len(kv[1]))[:rows]:
            out.append(f"  {src} ×{len(lines)}: {key}")
            out.append(f"      last {lines[-1][:19]}: {cut(lines[-1][20:], 300)}")
    return out


def s_costs(r, rows):
    c = r.costs
    t, p, w = c["total"], c["previous"], c["weights"]
    inputs = t["read"] + t["write"] + t["input"]
    all_ = t["cost"] + c["keep"]["cost"] + c["loads"]["cost"]
    out = [f"== COSTS (input-equivalent tokens: cache read {w['read']}, write {w['write']}, input {w['input']}, output {w['output']})"
           + (f" — nothing since {d.local_clock(c['shifted']['last'])}: the span up to the last activity" if c.get("shifted") else ""),
           f"  {d.local_clock(c['since'])} – {d.local_clock(c['now'])}: all {k(all_)} = sessions {k(t['cost'])} + pings "
           f"{k(c['keep']['cost'])} ({c['keep']['count']}, {c['keep']['missed']} missed) + loads {k(c['loads']['cost'])} "
           f"({c['loads']['count']}, {c['loads']['missed']} cold)",
           f"  sessions {t['sessions']} · requests {t['requests']} · a request "
           + (k(t['cost'] / t['requests']) if t['requests'] else '—')
           + (f" (before: {k(p['cost'] / p['requests'])})" if p["requests"] else "")
           + (f" · read from cache {t['read'] / inputs:.1%}" if inputs else ""),
           "  by kind: " + " · ".join(f"{kind} {k(t[kind])} tokens = {k(t[kind] * w[kind])} ({t[kind] * w[kind] / max(1, t['cost']):.0%})"
                                      for kind in ("read", "write", "input", "output"))
           + f" · a fork's prefix read again {k(t['reread'])} ({t['reread'] / max(1, t['read']):.0%} of what was read)"]
    out.append("  by role:")
    out += table(c["roles"], [("role", lambda x: x["role"], "<"), ("sessions", lambda x: x["sessions"], ">"),
                              ("requests", lambda x: x["requests"], ">"), ("cost", lambda x: k(x["cost"]), ">"),
                              ("median session", lambda x: k(x["median"]), ">"), ("span before", lambda x: k(x["previous"]), ">"),
                              ("written", lambda x: k(x["write"]), ">")])
    e = economics(r)
    out.append("  idle share of wall time, by role: " + ", ".join(f"{role} {x:.0%}" for role, x in sorted(e["idle"].items())))
    out.append("  over time (a line a bar):")
    top = max([sum(b[k_] for k_ in ("read", "write", "input", "output", "pings", "loads")) for b in c["buckets"]] or [1]) or 1
    for b in c["buckets"]:
        total = sum(b[k_] for k_ in ("read", "write", "input", "output", "pings", "loads"))
        if total:
            out.append(f"    {d.local_clock(b['at'])} {'#' * max(1, round(40 * total / top)):40} {k(total):>7}  "
                       + " ".join(f"{k_} {k(b[k_])}" for k_ in ("read", "write", "output", "pings", "loads") if b[k_]))
    out.append("  the costliest sessions:")
    out += table(c["sessions"], [("session", lambda x: x["name"], "<"), ("role", lambda x: x.get("role") or "", "<"),
                                 ("task", lambda x: x.get("task") or "—", ">"), ("requests", lambda x: x["requests"], ">"),
                                 ("written", lambda x: k(x["write"]), ">"), ("cost", lambda x: k(x["cost"]), ">")], rows)
    out.append("  the costliest tasks:")
    out += table(c["tasks"], [("task", lambda x: "#" + x["task"], "<"), ("sessions", lambda x: x["sessions"], ">"),
                              ("requests", lambda x: x["requests"], ">"), ("cost", lambda x: k(x["cost"]), ">"),
                              ("subject", lambda x: cut(x.get("subject"), 70), "<")], rows)
    if e["held"]:
        out.append("  held warm and pinged at a cost: " + ", ".join(f"{h['name']} ({h['held']}, {h['pings']} pings "
                                                                   f"{k(h['ping_cost'])})" for h in e["held"]))
    missed = [x for x in c["keep"]["events"] + c["loads"]["events"] if not x["ok"]]
    if missed:
        out.append("  pings and loads that found their entry cold:")
        out += [f"    {d.local_clock(x['at'])} {x['what']}: wrote {k(x['write'])}, cost {k(x['cost'])}" for x in missed[:rows]]
    return out


def s_bases(r, rows):
    b = r.bases
    out = [f"== BASES AND LAYERS: daemon {'up' if b['daemon'] else 'down'} · {len(b['held'])} other session(s) held warm"]
    for x in r.builds["bases"]:
        out.append(f"  {x['who']}: " + (f"a chain of named parts ({', '.join(x['parts'])})" if x["parts"] else
                                        "the stable base and one medium layer" if x["layer"] else "no layer")
                   + f" · sealed {x['sealed'] or '—'} · {'warm' if x['warm'] else 'cold'}"
                   + (f" · from scratch {k(x['projected'])}" if x["projected"] else "") + (f" · {x['status']}" if x["status"] else ""))
    for base in b["bases"]:
        s = base.get("staleness") or {}
        out.append(f"  {base['who']} parts (forks its {base['forks']}{', deltas on' if base['deltas'] else ''}"
                   f"{', a layer being built' if base.get('building') else ''}):")
        for p_ in base["parts"]:
            e = p_["entry"]
            out.append(f"    {p_['part']:10} {k(p_['own']):>6} own of {k(p_['context']):>6} · sealed {p_.get('sealed') or '—'} · "
                       f"{'warm' if e['warm'] else 'cold'}" + (f", expires in {dur(e['expires_in'])}" if (e.get('expires_in') or 0) > 0 else "")
                       + (f" · {e['misses']} miss(es)" if e.get("misses") else "") + (" · forked" if p_["forked"] else "")
                       + (f" · next ping in {dur(e['next_ping'])}" if e.get("next_ping") is not None else f" · {cut(e.get('why'), 70)}"))
        bits = []
        if s.get("layer_share") is not None:
            bits.append(f"{s['layer_share']:.1%} of the layer moved")
        if s.get("delta_now"):
            bits.append(f"a delta now would hold {k(s['delta_now']['tokens'])}")
        if s.get("pending"):
            bits.append(f"{k(s['pending'])} lacking: owed {k(s.get('pending_owed'))} of {k(s.get('pending_cost'))}")
        if s.get("chain"):
            bits.append(f"{s['chain']} text(s), {s.get('session_len') or 0} in its session")
        if s.get("refresh_plan"):
            start, owed, cost = s["refresh_plan"]
            bits.append(f"refresh from {start} due: owed {k(owed)} of {k(cost)}")
        if bits:
            out.append("    staleness: " + " · ".join(bits))
    if b["roles"]:
        out.append("  roles' own layers:")
        for x in b["roles"]:
            lay, ch = x.get("layer"), x.get("churn")
            out.append(f"    {x['role']:13} forks {x['forks']} · " + (f"layer {lay['name']} {k(x.get('layer_own'))} {'warm' if lay['entry']['warm'] else 'cold'}"
                       if lay else ("layer being built" if x.get("building") else "no layer"))
                       + (f" · churn {ch['name']} {'current' if x.get('churn_current') else 'behind, ' + str(x.get('behind_forks')) + ' fork(s) behind'}" if ch else ""))
    if b["held"]:
        out.append("  held warm: " + ", ".join(f"{h['name']} ({h['held']}, {h['pings']} pings {k(h['ping_cost'])})" for h in b["held"]))
    return out


def s_log(r, rows):
    events = [x for x in r.log if re.match(r"\d{4}-", x) and not d.LOG_NOISE.search(x[20:])]
    out = [f"== LOG (state/v2.log, the window's {len(events)} events of {len(r.log)} lines; the last {min(rows * 3, len(events))}"
           f" — {ME} log for the rest)"]
    out += [f"  {x[5:16].replace('T', ' ')} {cut(x[20:], 200)}" for x in events[-rows * 3:]]
    return out


SECTION_FNS = {"findings": s_findings, "run": s_run, "sessions": s_sessions, "pipeline": s_pipeline, "waits": s_waits,
               "machine": s_machine, "checks": s_checks, "batching": s_batching, "delivery": s_delivery,
               "errors": s_errors, "costs": s_costs, "bases": s_bases, "log": s_log}


# ---------------------------------------------------------------- the pass that says only what changed

def snapshot(r, found):
    """What stands now, as the next `changes` pass compares it: the findings by key, each open task's group and status,
    each standing session's state, each base part's warmth."""
    return dict(at=r.now,
                findings={f["key"]: f["text"] for f in found if f["kind"] == "state"},
                tasks={n["id"]: [n["group"], n["status"]] for n in r.graph["nodes"] if not n["done"]},
                sessions={s["name"]: s.get("state") for s in r.window if standing(s)},
                parts={f"{b['who']}/{x['part']}": bool(x["entry"]["warm"]) for b in r.bases["bases"] for x in b["parts"]})


def changes(r, rows, write=True):
    """What changed since the last `changes` pass (the marker, $TMPDIR/console-report.last.json): the findings new and
    resolved (those standing only counted), the tasks that moved, the sessions that started or ended, the entries that
    warmed or cooled, and the interval's events, checks, landings and costs — never what the pass before said."""
    before = read_mark()
    found = findings(r)
    now = snapshot(r, found)
    out = [f"== CHANGES since {d.local_clock(before.get('at')) if before.get('at') else 'the start of the window'} "
           f"({dur(r.now - r.since)})"]
    old = before.get("findings") or {}
    states = [f for f in found if f["kind"] == "state"]
    new = [f for f in states if f["key"] not in old]
    gone = [key for key in old if key not in now["findings"]]
    events = [f for f in found if f["kind"] == "event"]
    out.append(f"  conditions: {len(new)} new, {len(states) - len(new)} standing, {len(gone)} resolved")
    for f in new:
        out.append(f"    NEW {TONES[f['tone']]} {f['area']:10} {f['text']}" + (f"  → {f['drill']}" if f["drill"] else ""))
    for key in gone[:rows]:
        out.append(f"    resolved: {cut(old[key], 150)}")
    out.append(f"  what happened in the interval ({len(events)}):")
    for f in events:
        out.append(f"    {TONES[f['tone']]} {f['area']:10} {f['text']}" + (f"  → {f['drill']}" if f["drill"] else ""))
    moved = [(t, before.get("tasks", {}).get(t), g) for t, g in now["tasks"].items() if before.get("tasks", {}).get(t) != g]
    left = [t for t in (before.get("tasks") or {}) if t not in now["tasks"]]
    out.append(f"  tasks: {len(moved)} moved, {len(left)} left the open graph" + (" (" + ", ".join("#" + t for t in left[:20]) + ")" if left else ""))
    out += [f"    #{t}: {(o or ['new'])[0]} → {g[0]} ({cut(g[1], 60)})" for t, o, g in moved[:rows * 2]]
    bs, ns = before.get("sessions") or {}, now["sessions"]
    started = [n for n in ns if n not in bs]
    ended = [n for n in bs if n not in ns]
    changed = [(n, bs[n], ns[n]) for n in ns if n in bs and bs[n] != ns[n]]
    out.append(f"  sessions: {len(started)} started, {len(ended)} ended, {len(changed)} changed state")
    out += [f"    + {n} ({ns[n]})" for n in started] + [f"    - {n}" for n in ended] + [f"    {n}: {a} → {b}" for n, a, b in changed]
    bp = before.get("parts") or {}
    flips = [(p, w) for p, w in now["parts"].items() if p in bp and bp[p] != w]
    if flips:
        out.append("  entries: " + ", ".join(f"{p} {'warmed' if w else 'went cold'}" for p, w in flips))
    runs, verdicts, _ = check_runs(r)
    if runs:
        out.append(f"  checks run: " + "; ".join(f"{kind} {' '.join('#' + t for t in ts)} {v} in {s} s" for _, kind, ts, v, s in runs))
    landed = [x for x in r.log if re.search(r"the train of tasks .* landed as", x)]
    if landed:
        out.append("  landed: " + "; ".join(cut(x[20:], 80) for x in landed))
    c = r.costs["total"]
    out.append(f"  cost of the interval: {k(c['cost'])} in {c['requests']} requests of {c['sessions']} sessions, pings "
               f"{k(r.costs['keep']['cost'])}, loads {k(r.costs['loads']['cost'])}")
    events = [x for x in r.log if not d.LOG_NOISE.search(x[20:])]
    out.append(f"  events ({len(events)}):")
    out += [f"    {x[11:16]} {cut(x[20:], 180)}" for x in events[-rows * 4:]]
    if write:
        with open(MARK + ".tmp", "w") as f:
            json.dump(now, f)
        os.replace(MARK + ".tmp", MARK)
    return out


# ---------------------------------------------------------------- the inventory of what the run produced

def inventory(r, rows):
    """Everything the run produced in the window, by kind, with the id each is opened by."""
    since = r.since
    out = [f"== INVENTORY of what the run produced " + ("(everything)" if not since else f"since {d.local_clock(since)}")]
    ss = sorted(r.window, key=lambda s: s.get("started") or 0)
    out.append(f"  sessions ({len(ss)}; `session NAME`): " + ", ".join(
        f"{s['name']}" + ("" if s["record"].get("sid") and os.path.exists(v2.transcript(s["record"]["sid"])) else " (no transcript)")
        for s in ss))
    touched = collections.defaultdict(list)
    for path in glob.glob(os.path.join(v2.BUILD, "*", "*")):
        if os.path.getmtime(path) >= since and os.path.basename(os.path.dirname(path)).isdigit():
            touched[os.path.basename(os.path.dirname(path))].append(os.path.basename(path))
    out.append(f"  task folders ({len(touched)}; `task ID --files`, `task ID --file NAME`): "
               + "; ".join(f"#{t}: {', '.join(sorted(fs))}" for t, fs in sorted(touched.items(), key=lambda kv: int(kv[0]))))
    for title, folder in (("check outputs", os.path.join(v2.BUILD, "batches")), ("train outputs", os.path.join(v2.BUILD, "trains")),
                          ("landing bases", os.path.join(v2.PROJECT, ".build", "bases"))):
        names = sorted(f for f in (os.listdir(folder) if os.path.isdir(folder) else [])
                       if os.path.getmtime(os.path.join(folder, f)) >= since)
        out.append(f"  {title} ({len(names)}; `check STAMP`): " + ", ".join(names[-rows * 2:]))
    plans = sorted(glob.glob(os.path.join(v2.PROJECT, ".build", "plans", "plan-*")), key=os.path.getmtime)
    plans = [p for p in plans if os.path.getmtime(p) >= since]
    out.append(f"  planning episodes ({len(plans)}; `plan NAME`): " + ", ".join(os.path.basename(p) for p in plans))
    notes = [os.path.basename(p) for p in glob.glob(os.path.join(v2.STATE, "kb-*-notes.md")) if os.path.getmtime(p) >= since]
    out.append(f"  knowledge bases' notes ({len(notes)}; `kb NAME`): " + ", ".join(sorted(notes)))
    asks = [(q, a) for q, a in (r.st.get("asks") or {}).items()]
    answers = glob.glob(os.path.join(v2.BUILD, "*", "answers", "*.md"))
    out.append(f"  questions ({len(asks)} in the state, {len(answers)} answers written; `asks [QID]`)")
    boxes = glob.glob(os.path.join(v2.STATE, "mail", "*.jsonl"))
    out.append(f"  mailboxes ({len(boxes)}; `mail [NAME]`): " + ", ".join(os.path.basename(b)[:-6] for b in boxes))
    texts = sorted(os.path.basename(p) for p in glob.glob(os.path.join(v2.STATE, "*-delta-*.md")) if os.path.getmtime(p) >= since)
    out.append(f"  the deltas' texts ({len(texts)}; `base WHO --text N`): " + ", ".join(texts))
    evidence = glob.glob(os.path.join(v2.STATE, "role-evidence", "*.md"))
    out.append(f"  the roles' evidence ({len(evidence)}; `layer ROLE`): " + ", ".join(os.path.basename(e)[:-3] for e in evidence))
    logs = [(p, os.path.getsize(p)) for p in [os.path.join(v2.STATE, x) for x in ("v2.log", "warm.log", "watchdog.log", "qa.log")]
            if os.path.exists(p)]
    out.append("  logs (`log --source NAME`): " + ", ".join(f"{os.path.basename(p)} {k(n)}B" for p, n in logs))
    api = [os.path.basename(p)[11:] for p in glob.glob(os.path.join(v2.STATE, "api-errors-*")) if os.path.getmtime(p) >= since]
    out.append(f"  API errors ({len(api)}; `errors`): " + ", ".join(api))
    tasks = [t for t in v2.all_tasks() if os.path.getmtime(os.path.join(v2.TASKS, v2.LIST, f"{t['id']}.json")) >= since] \
        if os.path.isdir(os.path.join(v2.TASKS, v2.LIST)) else []
    out.append(f"  graph tasks written ({len(tasks)}; `graph --briefs`, `record task ID`): " + ", ".join("#" + t["id"] for t in tasks))
    commits = subprocess.run(["git", "-C", v2.PROJECT, "log", f"--since=@{int(since)}" if since else "-50", "--format=%h %cd %s",
                              "--date=format:%m-%d %H:%M"], capture_output=True, text=True).stdout.strip().splitlines()
    out.append(f"  commits on main ({len(commits)}; `file` for any path):")
    out += [f"    {c}" for c in commits[:rows * 2]]
    for name in ("HANDOFF.md", "PLANNING_LOG.md", ".claude/orchestration/owner-ledger.md"):
        p = os.path.join(v2.PROJECT, name)
        if os.path.exists(p):
            out.append(f"  {name}: {k(os.path.getsize(p))}B, written {ago(os.path.getmtime(p), r.now)} (`file {name}`)")
    return out


# ---------------------------------------------------------------- drill-downs: every product, opened

def session_view(r, name, detail="calls", first=None, last=None, grep=None):
    """A session's record, its summary and its requests: each request's time, usage and cost, its text, and its calls —
    the command and what came back (`--full`: whole; the default: the first lines), refused, stopped or failed marked,
    the harness's notes beside it; the messages it was given between. --from/--to pick requests (negative: from the
    end), --grep keeps the requests that match."""
    rec = r.records.get(name)
    if not rec:
        return [f"no session {name} in the state or the archive"]
    s = dict(d.session_summary(name, rec), record=rec)
    out = [f"== SESSION {name} ({s.get('role')}, task {s.get('task') or s.get('reviews') or '—'}): {s.get('state')}"
           + (" · released" if rec.get("released") else "") + (" · archived" if rec.get("archived") else ""),
           f"  from {rec.get('origin')} ({(rec.get('origin_sid') or '')[:8]}) · model {rec.get('model')} {rec.get('effort')} · "
           f"started {d.local_clock(rec.get('started'))} · ran {dur(r.ran(s))} · transcript "
           + (project_rel(v2.transcript(rec['sid'])) if rec.get("sid") else "none"),
           f"  {s.get('requests')} requests, {s.get('calls')} calls ({s.get('ops')} ops a request), {s.get('joinable')} joinable, "
           f"first change at request {s.get('first_change') or '—'} · refused {s.get('refused')}, stopped {s.get('stopped')}, "
           f"failed {s.get('failed')}, {s.get('notes')} notes · context {k(s.get('context'))} · cost {k(s.get('cost'))} · "
           f"model {dur(s.get('model_s'))}, calls {dur(s.get('tools_s'))}, idle {dur(s.get('idle_s'))}"]
    fields = {x: v for x, v in rec.items() if x not in ("events",) and not isinstance(v, (dict, list)) or x in ("fix", "parked")}
    out.append("  record: " + cut(json.dumps(fields, default=str), 900))
    turns = d.session_turns(rec) or {}
    items = turns.get("items") or []
    reqs = [it for it in items if it["kind"] == "request"]
    lo = (len(reqs) + first + 1 if first and first < 0 else first or 1)
    hi = (len(reqs) + last + 1 if last and last < 0 else last or len(reqs))
    shown = 0
    for it in items:
        if it["kind"] == "request":
            if not lo <= it["n"] <= hi:
                continue
            body = json.dumps(it["calls"], default=str) + " ".join(it.get("text") or [])
            if grep and not re.search(grep, body):
                continue
            shown += 1
            u = it.get("usage") or {}
            out.append(f"  #{it['n']} {clock(it['at'])} read {k(u.get('cache_read_input_tokens'))} written "
                       f"{k(u.get('cache_creation_input_tokens'))} out {k(u.get('output_tokens'))} · {len(it['calls'])} call(s)"
                       + (f", {it.get('ops')} ops" if it.get("ops") is not None else "") + (" · joinable" if it.get("joinable") else ""))
            for text in it.get("text") or []:
                out.append("     says: " + (text if detail == "full" else cut(text, 400)))
            for c in it["calls"]:
                mark = "REFUSED " if c["refused"] else "STOPPED " if c.get("stopped") else "FAILED " if c["error"] else ""
                cmd = c["command"] or ""
                res = c["refused"] or c.get("stopped") or c["result"] or ""
                if detail == "full":
                    out.append(f"     {mark}{c['tool']}: {cmd}")
                    out.append(f"       → {res}")
                elif detail == "turns":
                    out.append(f"     {mark}{c['tool']}: {cut(cmd, 300)}")
                    out.append(f"       → {cut(res, 300)}")
                else:
                    out.append(f"     {mark}{c['tool']}: {cut(cmd.splitlines()[0] if cmd else '', 160)} → {cut(res, 120)}")
                for note in c["notes"]:
                    out.append(f"       note: {cut(note, 300 if detail != 'full' else 100_000)}")
        elif it["kind"] == "message" and not grep:
            out.append(f"  message {clock(it['at'])}: " + (it["text"] if detail == "full" else cut(it["text"], 500)))
    out.append(f"  ({shown} of {len(reqs)} requests shown; --from/--to/--grep pick them, --turns or --full show more)")
    return out


def task_view(r, tid, files=False, file=None, history=False):
    """A task: the graph's record and brief, the harness's record of it, its stages with their times, its sessions, the
    files of its folder (whole with --file NAME), and the log's lines about it (--history)."""
    task = v2.read_task(tid) or {}
    t = r.st["tasks"].get(tid) or {}
    folder = os.path.join(v2.BUILD, tid)
    if file:
        path = os.path.normpath(os.path.join(folder, file))
        if not path.startswith(folder + os.sep) or not os.path.isfile(path):
            return [f"no file {file} in .build/tasks/{tid}/ (`task {tid} --files` lists them)"]
        return [f"== .build/tasks/{tid}/{file}"] + open(path, errors="ignore").read().splitlines()
    out = [f"== TASK #{tid} [{task.get('status')}] {task.get('subject', '')}",
           f"  stage {t.get('stage')} · kind {t.get('kind') or (task.get('metadata') or {}).get('kind')} · after "
           f"{', '.join(task.get('blockedBy') or []) or 'nothing'} · rejections {t.get('rejections', 0)} · checks failed "
           f"{t.get('checks_failed', 0)} · queued {tid in (r.st.get('queue') or [])}"
           + (f" · parked for {t['parked'].get('for')} {ago(t['parked'].get('since'), r.now)}" if t.get("parked") else ""),
           "  state record: " + cut(json.dumps({x: v for x, v in t.items() if x not in ("summary",)}, default=str), 1200)]
    dependents = [x["id"] for x in v2.all_tasks() if tid in (x.get("blockedBy") or [])]
    if dependents:
        out.append("  waited on by: " + ", ".join("#" + x for x in dependents))
    out += ["  brief:"] + ["    " + x for x in (task.get("description") or "(none)").splitlines()]
    es = task_events(r).get(tid) or []
    out.append("  stages:")
    for (at, stage, text), nxt in zip(es, es[1:] + [None]):
        end = nxt[0] if nxt else r.now
        out.append(f"    {time.strftime('%m-%d %H:%M', time.localtime(at))} {stage:20} {dur(end - at):>8}  {cut(text, 110)}")
    out.append("  sessions:")
    ss = [s for s in r.sessions.values() if str(s.get("task")) == tid or str(s.get("reviews")) == tid]
    out += table(sorted(ss, key=lambda s: s.get("started") or 0), session_cols(r))
    listing = sorted(glob.glob(os.path.join(folder, "**"), recursive=True))
    names = [os.path.relpath(p, folder) + ("/" if os.path.isdir(p) else f" ({k(os.path.getsize(p))}B)") for p in listing
             if p != folder]
    out.append(f"  files ({len(names)}; `task {tid} --file NAME`): " + ("" if files else ", ".join(names[:40])
                                                                         + (" …" if len(names) > 40 else "")))
    if files:
        out += ["    " + x for x in names]
    for name in ("result.md", "review.md", "commit.md"):
        text = d.read_build(tid, name)
        if text and not files:
            out.append(f"  {name} (its first lines):")
            out += ["    " + x for x in text.splitlines()[:12]]
    if history:
        out.append("  the log about it:")
        out += ["    " + x for x in d.task_history(tid, 100_000)]
    return out


def check_view(r, key):
    """A check's or a train's runs: by a task (every run that named it) or a stamp (its output folder): the log's lines
    of its runs and verdicts, and each run log's end."""
    out = [f"== CHECK {key}"]
    if key.isdigit():
        lines = [x for x in r.log_all if re.search(r"(check|train|landing|batch)", x) and key in ids_of(x[20:])
                 and re.search(r"check|train|land", x[20:])]
        out += ["  " + x for x in lines]
        logs = [p for p in glob.glob(os.path.join(v2.BUILD, "batches", "*.log")) + glob.glob(os.path.join(v2.BUILD, "trains", "*.log"))
                if re.search(rf"(batch|train)[\d-]*\b{key}\b", os.path.basename(p))]
    else:
        logs = glob.glob(os.path.join(v2.BUILD, "*", f"{key}*.log")) + glob.glob(os.path.join(v2.PROJECT, ".build", "bases", f"{key}*"))
    for p in sorted(logs, key=os.path.getmtime)[-6:]:
        if os.path.isfile(p):
            out.append(f"  -- {project_rel(p)} (its end)")
            out += ["    " + x for x in open(p, errors="ignore").read().splitlines()[-40:]]
        else:
            out.append(f"  -- {project_rel(p)}/: " + ", ".join(sorted(os.listdir(p))[:30]))
    return out


def asks_view(r, qid=None):
    """The questions: from, to, what, and the answer (state, the answers written under .build/tasks/*/answers/)."""
    out = ["== QUESTIONS"]
    for q, a in (r.st.get("asks") or {}).items():
        if qid and q != qid:
            continue
        out.append(f"  {q}: {a.get('from')} → {a.get('to')} · " + ("answered" if a.get("answer") or a.get("answered") else "open")
                   + f" · {cut(a.get('text'), 100000 if qid else 300)}")
        if a.get("answer"):
            out.append(f"    answer: {cut(a.get('answer'), 100000 if qid else 400)}")
    for p in sorted(glob.glob(os.path.join(v2.BUILD, "*", "answers", f"{qid or '*'}.md")), key=os.path.getmtime):
        out.append(f"  -- {project_rel(p)}")
        text = open(p, errors="ignore").read()
        out += ["    " + x for x in (text.splitlines() if qid else [cut(text, 300)])]
    return out


def mail_view(r, name=None):
    out = ["== MAIL (what waits in each box)"]
    for p in sorted(glob.glob(os.path.join(v2.STATE, "mail", f"{name or '*'}.jsonl"))):
        items = []
        for line in open(p, errors="ignore"):
            try:
                items.append(json.loads(line))
            except ValueError:
                continue
        out.append(f"  {os.path.basename(p)[:-6]}: {len(items)}")
        out += [f"    {x.get('at', '')} from {x.get('from')}: {cut(x.get('text'), 100000 if name else 200)}" for x in items]
    return out


def plan_view(r, name):
    """A planning episode: its record and the events it was given, the files of its plan folder (edits, drafts, notes),
    and the log's lines it caused."""
    rec = r.records.get(name) or {}
    out = [f"== PLAN {name}: {rec.get('state')} · started {d.local_clock(rec.get('started'))}"]
    for e in rec.get("events") or []:
        out.append(f"  event {e.get('at')} from {e.get('from')}: {cut(e.get('text'), 600)}")
    folder = os.path.join(v2.PROJECT, ".build", "plans", name)
    for p in sorted(glob.glob(os.path.join(folder, "*")), key=os.path.getmtime):
        out.append(f"  -- {project_rel(p)} ({k(os.path.getsize(p))}B)")
        if p.endswith("notes.md"):
            out += ["    " + x for x in open(p, errors="ignore").read().splitlines()]
    out.append("  the log about it:")
    out += ["    " + x for x in r.log_all if name in x or ("the planner edited the graph" in x and rec.get("started")
                                                              and (line_epoch(x) or 0) >= rec["started"]
                                                              and (line_epoch(x) or 0) <= (rec.get("ended") or r.now))]
    return out


def kb_view(r, name=None):
    out = ["== KNOWLEDGE BASES"]
    kbs = sorted((s for n, s in r.records.items() if s.get("role") == "kb" and (not name or n == name)),
                 key=lambda s: s.get("started") or 0)
    for s in kbs:
        out.append(f"  {s['name']}: {s.get('kb_state')} · started {d.local_clock(s.get('started'))} · context "
                   f"{k(s.get('context'))} · holds max's chain to {s.get('holds_node') or '—'} "
                   f"({s.get('stack_len') or 0} text(s)) · protocols {json.dumps(s.get('protocol_shas') or {})}"
                   + (" · the current one" if r.st.get("kb") == s["name"] else ""))
        notes = os.path.join(v2.STATE, f"{s['name']}-notes.md")
        if name and os.path.exists(notes):
            out += [f"  -- {project_rel(notes)}"] + ["    " + x for x in open(notes, errors="ignore").read().splitlines()]
    out.append("  integrations:")
    out += ["    " + x for x in r.log_all if re.search(r"\bkb-\d+ (integrated|holds the knowledge)", x)
            and (not name or name in x)][-40:]
    return out


def base_view(r, who, text=None):
    """A base: its records (stable, layer or chain, delta), each part, the delta's chain of texts (a text whole with
    --text N), its builds and what its logs said."""
    if text is not None:
        chain = v2.chain_of(v2.delta_record(who))
        if not 0 <= text < len(chain):
            return [f"no text {text}: the {who} chain has {len(chain)}"]
        node = chain[text]
        return [f"== {who}'s text {text}: {v2.node_id(node)} ({k(node.get('tokens'))} tokens)"] + \
            open(node["text"], errors="ignore").read().splitlines()
    out = [f"== BASE {who}"]
    for part in ("base", "layer", "delta", "base-next", "base-building"):
        rec = d.state_json(f"{who}-{part}.json")
        if rec:
            slim = {x: v for x, v in rec.items() if x not in ("parts", "stack")}
            out.append(f"  {who}-{part}.json: " + cut(json.dumps(slim, default=str), 700))
    for p in (v2.layer_record(who) or {}).get("parts") or []:
        out.append(f"    part {p.get('part')}: {p.get('sessionId', '')[:8]} {k(p.get('context'))} sealed {p.get('sealed')}")
    chain = v2.chain_of(v2.delta_record(who))
    d_ = v2.delta_record(who) or {}
    out.append(f"  the delta's chain: {len(chain)} text(s), its session holding {v2.session_len(d_)} "
               f"({(d_.get('sessionId') or 'none')[:8]}); `base {who} --text N` opens one")
    for i, n in enumerate(chain):
        out.append(f"    {i}: {v2.node_id(n)} {n.get('kind')} {k(n.get('tokens'))} tokens, {k(n.get('superseded'))} "
                   f"superseded, sealed {n.get('sealed')}" + (f", in session {n['sessionId'][:8]}" if n.get("sessionId") else ""))
    builds = os.path.join(v2.STATE, f"{who}-delta-builds.jsonl")
    if os.path.exists(builds):
        out.append("  its texts and sessions, as built:")
        out += ["    " + x for x in open(builds, errors="ignore").read().splitlines()[-30:]]
    out.append("  what warm.log said of it:")
    out += ["    " + x for x in r.warm if re.search(rf"\b{who}\b", x)][-30:]
    return out


def layer_view(r, role):
    rec = v2.role_layer_record(role, r.st)
    out = [f"== LAYER of the {role}: " + cut(json.dumps(rec, default=str), 600)]
    for key in ("name", "churn", "building", "churn_building"):
        s = r.records.get(rec.get(key) or "")
        if s:
            slim = {x: v for x, v in s.items() if not isinstance(v, (dict, list))}
            out.append(f"  {key} {s['name']}: " + cut(json.dumps(slim, default=str), 700))
    evidence = os.path.join(v2.STATE, "role-evidence", f"{role}.md")
    if os.path.exists(evidence):
        out += [f"  -- {project_rel(evidence)}"] + ["    " + x for x in open(evidence, errors="ignore").read().splitlines()]
    return out


def graph_view(r, all_=False, briefs=False):
    out = ["== GRAPH (" + v2.LIST + ")"] + ["  " + x for x in v2.graph_text(full=all_).splitlines()]
    if briefs:
        for t in v2.all_tasks():
            if all_ or t.get("status") != "completed":
                out += [f"  -- #{t['id']} {t.get('subject', '')}"] + ["    " + x for x in (t.get("description") or "").splitlines()]
    return out


def record_view(r, kind, key):
    if kind == "session":
        rec = r.records.get(key)
    elif kind == "task":
        rec = dict(graph=v2.read_task(key), state=r.st["tasks"].get(key))
    elif kind == "ask":
        rec = (r.st.get("asks") or {}).get(key)
    elif kind == "state":
        rec = {x: v for x, v in r.st.items() if x not in ("sessions", "tasks")} if key in ("", "-") else r.st.get(key)
    else:
        return [f"record: session, task, ask or state, not {kind}"]
    return json.dumps(rec, indent=1, default=str).splitlines() if rec is not None else [f"no {kind} {key}"]


def file_view(r, path, lines=None, grep=None):
    """Any file of the project, the state or .build — read, never written."""
    full = os.path.normpath(os.path.join(v2.PROJECT, path)) if not os.path.isabs(path) else os.path.normpath(path)
    roots = (v2.PROJECT, v2.STATE, os.path.expanduser("~/.claude/tasks"), os.path.expanduser("~/.claude/projects"))
    if not any(full == x or full.startswith(x + os.sep) for x in roots) or not os.path.isfile(full):
        return [f"no file {path} under the project, the state, the task list or the transcripts"]
    text = open(full, errors="ignore").read().splitlines()
    out = [f"== {project_rel(full)} ({len(text)} lines)"]
    if lines:
        a, _, b = lines.partition("-")
        text = text[int(a) - 1:int(b or a)]
    if grep:
        text = [x for x in text if re.search(grep, x)]
    return out + text


def log_view(r, source="v2", grep=None, tail=200):
    path = {"v2": "v2.log", "warm": "warm.log", "watchdog": "watchdog.log", "qa": "qa.log"}.get(source, source)
    try:
        lines = open(os.path.join(v2.STATE, path), errors="ignore").read().splitlines()
    except OSError:
        return [f"no log {path} in the state"]
    if r.since:
        lines = [x for x in lines if (line_epoch(x) or r.since) >= r.since]
    if grep:
        lines = [x for x in lines if re.search(grep, x)]
    return [f"== {path}: {len(lines)} line(s) in the window, the last {min(tail, len(lines))}"] + lines[-tail:]


# ---------------------------------------------------------------- the command line

def emit(lines, cap):
    text = "\n".join(lines)
    if cap and len(text) > cap:
        text = text[:cap].rsplit("\n", 1)[0] + (f"\n… cut at {cap:,} of {len(text):,} characters: --max, or a narrower "
                                                "--since, --from/--to, --grep, --only")
    print(text)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0], formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("command", nargs="?", default="report")
    ap.add_argument("args", nargs="*")
    ap.add_argument("--since", default=None)
    ap.add_argument("--only", default="")
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--rows", type=int, default=15)
    ap.add_argument("--max", type=int, default=60_000)
    ap.add_argument("--turns", action="store_true")
    ap.add_argument("--full", action="store_true")
    ap.add_argument("--from", dest="first", type=int)
    ap.add_argument("--to", dest="last", type=int)
    ap.add_argument("--grep")
    ap.add_argument("--files", action="store_true")
    ap.add_argument("--file")
    ap.add_argument("--history", action="store_true")
    ap.add_argument("--text", type=int)
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--briefs", action="store_true")
    ap.add_argument("--lines")
    ap.add_argument("--source", default="v2")
    ap.add_argument("--tail", type=int, default=200)
    a = ap.parse_args(argv)
    now = time.time()
    default = "last" if a.command == "changes" else "all" if a.command in (
        "session", "task", "check", "asks", "mail", "plan", "kb", "base", "layer", "graph", "record", "file") else "3h"
    r = Run(parse_since(a.since or default, now), a.quick or a.command not in ("report", "changes", "findings"))
    arg = a.args[0] if a.args else None
    if a.command == "report":
        only = [x for x in a.only.split(",") if x] or list(SECTIONS)
        unknown = set(only) - set(SECTIONS)
        if unknown:
            raise SystemExit(f"--only: no section {', '.join(sorted(unknown))} (of {', '.join(SECTIONS)})")
        if a.json:
            data = dict(findings=findings(r), waits=waits(r), batching={x: {y: v for y, v in b.items() if y != "worst"}
                                                                         for x, b in batching(r).items()},
                        checks=check_runs(r)[:2], costs=r.costs, economics=economics(r))
            print(json.dumps({x: v for x, v in data.items() if x in only or x in ("costs", "economics")}, default=str))
            return 0
        lines = []
        for name in SECTIONS:
            if name in only:
                lines += SECTION_FNS[name](r, a.rows) + [""]
        emit(lines, a.max)
    elif a.command == "changes":
        emit(changes(r, a.rows), a.max)
    elif a.command == "findings":
        if a.json:
            print(json.dumps([f for f in findings(r) if not arg or f["area"] == arg]))
        else:
            emit(s_findings(r, a.rows, arg), a.max)
    elif a.command in ("waits", "errors", "batching", "sessions", "pipeline", "checks", "costs", "bases", "machine"):
        emit(SECTION_FNS[a.command](r, a.rows), a.max)
    elif a.command == "delivery":
        emit(s_delivery(r, a.rows, a.grep, arg), a.max)
    elif a.command == "inventory":
        emit(inventory(r, a.rows), a.max)
    elif a.command == "session" and arg:
        emit(session_view(r, arg, "full" if a.full else "turns" if a.turns else "calls", a.first, a.last, a.grep), a.max)
    elif a.command == "task" and arg:
        emit(task_view(r, arg, a.files, a.file, a.history), a.max)
    elif a.command == "check" and arg:
        emit(check_view(r, arg), a.max)
    elif a.command == "asks":
        emit(asks_view(r, arg), a.max)
    elif a.command == "mail":
        emit(mail_view(r, arg), a.max)
    elif a.command == "plan" and arg:
        emit(plan_view(r, arg), a.max)
    elif a.command == "kb":
        emit(kb_view(r, arg), a.max)
    elif a.command == "base" and arg:
        emit(base_view(r, arg, a.text), a.max)
    elif a.command == "layer" and arg:
        emit(layer_view(r, arg), a.max)
    elif a.command == "graph":
        emit(graph_view(r, a.all, a.briefs), a.max)
    elif a.command == "record" and len(a.args) >= 1:
        emit(record_view(r, a.args[0], a.args[1] if len(a.args) > 1 else ""), a.max)
    elif a.command == "file" and arg:
        emit(file_view(r, arg, a.lines, a.grep), a.max)
    elif a.command == "log":
        emit(log_view(r, a.source, a.grep, a.tail), a.max)
    else:
        raise SystemExit(__doc__)
    return 0


if __name__ == "__main__":
    sys.exit(main())
