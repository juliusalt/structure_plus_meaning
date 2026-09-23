#!/usr/bin/env python3
"""The run's efficiency and quality in one report, over a window of sessions: what tonight's changes are to move.

    python3 -B notes/run-report.py [--since YYYY-MM-DDTHH:MM] [--until YYYY-MM-DDTHH:MM]

Not part of the harness; read-only. It reads every session the state or its archive names (notes/timeline.py's
reading of their transcripts) and v2.log (notes/lifecycle.py's), and prints, for the sessions launched in the window:

  cost by role, and the share of it that is the base read again (input-equivalent: cache read 0.1, 1-hour write 2,
  input 1, output 5);
  for implementers and fixers: requests before the first change and their share of cost; requests that only did
  bookkeeping (a THEORY_MAP.md row, ROOT, commit.md, result.md, source checks, bring-main, git status, the harness's
  closing commands, the todo list) and their share; closes made in one request; the index files edited by key
  (`=== row`, `=== root`) and results given as the command's text;
  what the change replies told (the sources, a name, statement or definition the library has) and the launch
  messages that stated a brief's named facts;
  rejections, and the time a landed task spent in each stage (lifecycle).

The measures of notes/plan-orchestrator-concepts.md (findings 3, 5, 6, 8; C1, C2, C4), taken again so that a run
after the changes can be read against the runs before them.
"""
import contextlib
import importlib.util
import json
import os
import re
import sys
import time
from collections import Counter

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HERE)


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, "notes", file))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


tl = load("timeline", "timeline.py")
lc = load("lifecycle", "lifecycle.py")
sd = tl.sd

BOOK = re.compile(r"THEORY_MAP\.md|\bROOT\b|commit\.md|result\.md|source_checks|bring-main|"
                  r"v2\.py (?:result|finalize|end|park)|git (?:status|log|diff --stat)|\"taskId\"|\"subject\"|"
                  r"check\.source|=== (?:row|root) ")
THEORY = re.compile(r"theories/\w+\.thy")
TOLD = {"sources told": "[the sources, as this change leaves them",
        "a name the library has": "too: the same notion or fact",
        "a statement the library has": "states, word for word",
        "a definition the library has": "defines, its arguments aside",
        "a row offering what was taken out": "which this change took out of"}


def cost(q):
    return q.get("read", 0) * 0.1 + q.get("write", 0) * 2 + q.get("out", 0) * 5


def stamp(text):
    return time.mktime(time.strptime(text, "%Y-%m-%dT%H:%M"))


def session_calls(path, started):
    """[(request's message id, [(command, result text)])] of a session's own requests, in order."""
    reqs, order, calls = {}, [], {}
    for line in open(path, errors="ignore"):
        try:
            r = json.loads(line)
        except ValueError:
            continue
        t = tl.stamp(r.get("timestamp") or "")
        if t is None or t < started - 5 or r.get("isSidechain"):
            continue
        m = r.get("message") or {}
        content = m.get("content")
        if r.get("type") == "assistant" and isinstance(content, list):
            mid = m.get("id")
            if mid not in reqs:
                reqs[mid] = []
                order.append(mid)
            for b in content:
                if isinstance(b, dict) and b.get("type") == "tool_use":
                    i = b.get("input") or {}
                    c = [i.get("command") or json.dumps(i)[:300], ""]
                    reqs[mid].append(c)
                    calls[b.get("id")] = c
        elif r.get("type") == "user" and isinstance(content, list):
            for b in content:
                if isinstance(b, dict) and b.get("type") == "tool_result" and b.get("tool_use_id") in calls:
                    body = b.get("content")
                    if isinstance(body, list):
                        body = "\n".join(x.get("text", "") for x in body if isinstance(x, dict))
                    calls[b["tool_use_id"]][1] = body or ""
    return [reqs[m] for m in order]


HANDOFF_BLOCK = re.compile(r"<<<<<<< SEARCH\n(.*?)\n=======\n(.*?)\n>>>>>>> REPLACE", re.S)
PASSING = re.compile(r"`[0-9a-f]{8}`|\blanded\b|\bparked\b|handing over|\bqueued\b|\*\*Order\*\*|\bin review\b|"
                     r"\bre-review|\brejected\b|\bunder way\b")
STAGE = {"made": "waiting to start", "start": "producing", "resume": "producing", "result": "after its result",
         "check_asked": "its check", "checked:passed": "waiting for its review", "checked:failed": "waiting for a fix",
         "committed": "landing"}


def stages(tasks, st):
    """Where the time of each task landed in the window went, from its made-time to its landing: each interval between
    two of its events charged to the state the earlier one opened (findings 5 of the plan)."""
    total, n = Counter(), 0
    for tid, e in tasks.items():
        if (st["tasks"].get(tid) or {}).get("kind") not in ("build", "fix", "design", "investigate"):
            continue
        land = e.get("landed") or e.get("commit_direct")
        if not land or not e.get("made"):
            continue
        ev = [(t, "made") for t in e["made"][:1]] + [(x[0], "start") for x in e.get("start", [])] + \
             [(x[0], "resume") for x in e.get("resume", [])] + [(x[0], "result") for x in e.get("result", [])] + \
             [(t, "check_asked") for t in e.get("check_asked", [])] + \
             [(x[0], "checked:" + x[1]) for x in e.get("checked", [])] + [(t, "committed") for t in e.get("committed", [])]
        end = min(land)
        ev = sorted(x for x in ev if x[0] <= end) + [(end, None)]
        for (a, k), (b, _) in zip(ev, ev[1:]):
            total[STAGE[k]] += b - a
        n += 1
    spans = []
    for tid, e in tasks.items():  # C9's measure: from a task's first result to its commit (18.4 min median, 09-22 pm)
        res = [x[0] for x in e.get("result", []) if x[1] == "done"]
        if res and e.get("committed"):
            later = [t for t in e["committed"] if t >= min(res)]
            if later:
                spans.append((min(later) - min(res)) / 60)
    if spans:
        spans.sort()
        print(f"\nfrom a task's result to its commit: a median {spans[len(spans) // 2]:.1f} minutes over {len(spans)} "
              "tasks (C9; 21.3 over the 60 of the baseline window, 09-22 12:00–23:00)")
    if n:
        whole = sum(total.values()) or 1
        print(f"\n{n} tasks made and landed in the window, {whole / n / 60:.0f} minutes each from made to landed: "
              + ", ".join(f"{k} {v / n / 60:.0f} min ({v / whole:.0%})" for k, v in total.most_common()))


WORKING = ("implementer", "fixer", "designer", "investigator", "reviewer", "task-designer")
GRAPH = os.path.expanduser("~/.claude/tasks/orchestration-graph")


def idle(since, until, tasks, st, records):
    """Finding 11 of the plan, taken again: the minutes in which fewer than two working sessions were active (a model
    request or a tool running, a wait between turns not counted), and of those how many had open work that waited
    only on blockers past their result (in their check, their review or their landing) — what the order of the
    finalization (C9) and the graph's width decide."""
    act = Counter()
    for x in records:
        if x.get("role") not in WORKING or not x.get("first"):
            continue
        waits = [(w["at"], w["at"] + w["dur"]) for w in x.get("waits") or []]
        for m in range(int(max(x["first"], since) // 60), int(min(x["last"], until) // 60) + 1):
            t = m * 60 + 30
            if x["first"] <= t <= x["last"] and not any(a <= t < b for a, b in waits):
                act[m] += 1
    graph = {}
    for f in os.listdir(GRAPH) if os.path.isdir(GRAPH) else []:
        if f.endswith(".json"):
            with contextlib.suppress(OSError, ValueError):
                d = json.load(open(os.path.join(GRAPH, f)))
                graph[d["id"]] = d
    kind = lambda t: ((graph.get(t) or {}).get("metadata") or {}).get("kind") \
        if isinstance((graph.get(t) or {}).get("metadata"), dict) else None
    first = lambda t, k: min([x[0] if isinstance(x, (list, tuple)) else x for x in tasks.get(t, {}).get(k) or []] or [None]) \
        if tasks.get(t, {}).get(k) else None
    land = lambda t: min((tasks.get(t, {}).get("landed") or []) + (tasks.get(t, {}).get("commit_direct") or []) or [None]) \
        if (tasks.get(t, {}).get("landed") or tasks.get(t, {}).get("commit_direct")) else None
    made = lambda t: first(t, "made") or float((st["tasks"].get(t) or {}).get("queued_at") or 0)
    few = held = 0
    for m in range(int(since // 60), int(until // 60) + 1):
        if act[m] >= 2:
            continue
        few += 1
        t = m * 60 + 30
        for tid, d in graph.items():
            start = first(tid, "start")
            if kind(tid) not in PRODUCING_KINDS or not start or made(tid) > t or start <= t:
                continue
            open_ = [b for b in d.get("blockedBy") or [] if kind(b) in PRODUCING_KINDS and not ((land(b) or 9e18) <= t)]
            if open_ and all((first(b, "result") or 9e18) <= t for b in open_):
                held += 1
                break
    minutes = int(until // 60) - int(since // 60) + 1
    print(f"\nworking sessions: fewer than two active in {few} of {minutes} minutes; in {held} of them a task not yet "
          "started waited only on blockers past their result (finding 11: 349 of 638 and 246, 09-22 12:00–22:37)")


PRODUCING_KINDS = ("build", "fix", "design", "investigate")
SLOW_LINE = re.compile(r"^(\S+) slow: (.+?) of \S+ took ([\d.]+) s(?: — (.*))?$")


def slow(since, until):
    """Finding 15's instrument: the hooks' and the sessions' commands' slow calls in the window, by what they were,
    with the parts that took their time (v2.Stopwatch's lines)."""
    by, parts = {}, Counter()
    for line in open(os.path.join(HERE, "state", "v2.log"), errors="ignore"):
        m = SLOW_LINE.match(line.rstrip("\n"))
        if not m or not (since <= time.mktime(time.strptime(m.group(1), "%Y-%m-%dT%H:%M:%S")) < until):
            continue
        what = re.sub(r"`v2\.py (\w[\w-]*)`", r"v2.py \1", m.group(2))
        by.setdefault(what, []).append(float(m.group(3)))
        for part in (m.group(4) or "").split(", "):
            name, _, secs = part.rpartition(" ")
            with contextlib.suppress(ValueError):
                parts[name] += float(secs)
    if by:
        print("\nslow calls (over ORCH_SLOW): " + "; ".join(
            f"{w} {len(v)}, {span(sum(v))}" for w, v in sorted(by.items(), key=lambda x: -sum(x[1]))[:8])
              + "\n  where their time went: " + ", ".join(f"{n} {span(t)}" for n, t in parts.most_common(8)))


LAYERABLE = ("designer", "investigator", "implementer", "fixer", "task-designer", "reviewer")


def role_layers(chosen, sessions, paths):
    """The owner's test of the role layers: each role's sessions that forked its reasoning layer, beside those of the
    same window that forked its base — requests, requests before the first change, rejections of their task, cost
    (medians) — and what the layers themselves cost."""
    st = json.load(open(os.path.join(HERE, "state", "v2.json")))
    groups, built = {}, []
    for name, x in chosen.items():
        role = x.get("role")
        if role == "role-layer":
            rec = tl.record(name, x, paths[x["sid"]])
            built.append((name, sum(cost(q) for q in rec["requests"])))
            continue
        if role not in LAYERABLE:
            continue
        rec = tl.record(name, x, paths[x["sid"]])
        if not rec["requests"]:
            continue
        calls = session_calls(paths[x["sid"]], x.get("started") or 0)
        first = next((i for i, cs in enumerate(calls) if any("v2.py change" in c for c, _ in cs)), None)
        on = (sessions.get(x.get("origin") or "") or {}).get("role") == "role-layer"
        rejected = bool((st["tasks"].get(str(x.get("task") or "")) or {}).get("rejections"))
        groups.setdefault((role, on), []).append((len(rec["requests"]), first, rejected, sum(cost(q) for q in rec["requests"])))
    if not built and not any(on for _, on in groups):
        return
    med = lambda xs: sorted(xs)[len(xs) // 2] if xs else 0
    print(f"\nrole layers (the owner's test): {len(built)} built, {sum(c for _, c in built) / 1e6:.2f}M in all")
    for role in LAYERABLE:
        for on in (True, False):
            g = groups.get((role, on)) or []
            if not g or not groups.get((role, True)):
                continue
            firsts = [f for _, f, _, _ in g if f is not None]
            print(f"  {role:14} {'its layer' if on else 'its base '} {len(g):3} sessions: requests {med([r for r, _, _, _ in g])}, "
                  f"before the first change {med(firsts) if firsts else '-'}, their task rejected "
                  f"{sum(1 for _, _, x, _ in g if x)}, cost {med([c for _, _, _, c in g]) / 1e6:.2f}M (medians)")


def span(seconds):
    return f"{seconds / 60:.0f} min" if seconds >= 120 else f"{seconds:.0f} s"


def main():
    since = stamp(sys.argv[sys.argv.index("--since") + 1]) if "--since" in sys.argv else time.time() - 86400
    until = stamp(sys.argv[sys.argv.index("--until") + 1]) if "--until" in sys.argv else time.time()
    paths, sessions = sd.transcripts(), tl.all_sessions()
    chosen = {n: s for n, s in sessions.items() if since <= (s.get("started") or 0) < until and s.get("sid") in paths}
    print(f"sessions launched {time.strftime('%m-%d %H:%M', time.localtime(since))} – "
          f"{time.strftime('%m-%d %H:%M', time.localtime(until))}: {len(chosen)}")
    by_role, base_part, n_role = Counter(), Counter(), Counter()
    phase, closes, keyed, told, launched = Counter(), Counter(), Counter(), Counter(), Counter()
    for name, s in chosen.items():
        rec = tl.record(name, s, paths[s["sid"]])
        role, q = s.get("role"), rec["requests"]
        if not q:
            continue
        n_role[role] += 1
        base = q[0]["read"]
        for x in q:
            by_role[role] += cost(x)
            base_part[role] += min(x["read"], base) * 0.1
        if role not in ("implementer", "fixer"):
            continue
        calls = session_calls(paths[s["sid"]], s.get("started") or 0)
        first = next((i for i, cs in enumerate(calls) if any("v2.py change" in c for c, _ in cs)), len(calls))
        phase[(role, "sessions")] += 1
        phase[(role, "requests")] += len(q)
        phase[(role, "before the first change")] += first
        for i, x in enumerate(q):
            phase[(role, "cost")] += cost(x)
            if i < first:
                phase[(role, "cost before the first change")] += cost(x)
            cs = calls[i] if i < len(calls) else []
            if cs and all(BOOK.search(c) and not THEORY.search(c.replace("THEORY_MAP", "")) for c, _ in cs):
                phase[(role, "bookkeeping requests")] += 1
                phase[(role, "cost of bookkeeping")] += cost(x)
        joined = [" ".join(c for c, _ in cs) for cs in calls]
        results = [i for i, t in enumerate(joined) if "v2.py result" in t]
        hands = [i for i, t in enumerate(joined) if "v2.py finalize" in t]
        if hands or results:
            last = max(hands + results)
            closes["one request" if (hands and (not results or results[-1] == hands[-1] or
                                                 "recorded with it" in " ".join(r for _, r in calls[hands[-1]])))
                   and last == (hands[-1] if hands else last) else "more than one"] += 1
        for cs in calls:
            for c, r in cs:
                keyed["=== row"] += len(re.findall(r"^=== row ", c, re.M))
                keyed["=== root"] += len(re.findall(r"^=== root ", c, re.M))
                keyed["result given as its text"] += bool(re.search(r"v2\.py result \S+ <<", c))
                keyed["hand-over without arguments"] += bool(re.search(r"v2\.py finalize \S+\s*(?:$|&&|;|\n)", c))
                for k, mark in TOLD.items():
                    told[k] += r.count(mark)
        head = open(paths[s["sid"]], errors="ignore").read(2_000_000)
        launched["launch stated the brief's facts"] += "What your brief names, as your tree states it now" in head \
            or "What the brief names, as your tree states it now" in head
    total = sum(by_role.values()) or 1
    print(f"\ncost {total / 1e6:.1f}M input-equivalent")
    for role, c in by_role.most_common():
        print(f"  {role:14} {n_role[role]:4} sessions {c / 1e6:7.1f}M {c / total:6.1%}   base read again "
              f"{base_part[role] / c:4.0%}")
    for role in ("implementer", "fixer"):
        n = phase[(role, "sessions")]
        if not n:
            continue
        c = phase[(role, "cost")] or 1
        print(f"\n{role}: {n} sessions, {phase[(role, 'requests')] / n:.1f} requests each; before the first change "
              f"{phase[(role, 'before the first change')] / n:.1f} requests, {phase[(role, 'cost before the first change')] / c:.0%}"
              f" of cost; bookkeeping only {phase[(role, 'bookkeeping requests')] / n:.1f} requests, "
              f"{phase[(role, 'cost of bookkeeping')] / c:.0%} of cost")
    rv = [tl.record(n, x, paths[x["sid"]]) for n, x in chosen.items() if x.get("role") == "reviewer"]
    rv = [r for r in rv if r["requests"]]
    if rv:
        print(f"\nreviewer: {len(rv)} reviews, {sum(len(r['requests']) for r in rv) / len(rv):.1f} requests each, "
              f"{sum(cost(q) for r in rv for q in r['requests']) / len(rv) / 1e6:.2f}M each; the launch message written "
              f"{sum(r['requests'][0]['write'] * 2 for r in rv) / len(rv) / 1e3:.0f}K a review")
    role_layers(chosen, sessions, paths)
    blocks = Counter()
    for name, x in chosen.items():
        if x.get("role") != "planner":
            continue
        for cs in session_calls(paths[x["sid"]], x.get("started") or 0):
            for c, _ in cs:
                if "=== replace HANDOFF.md" not in c:
                    continue
                seg = c.split("=== replace HANDOFF.md", 1)[1].split("\n=== ", 1)[0]
                for old, new in HANDOFF_BLOCK.findall(seg):
                    blocks["blocks"] += 1
                    blocks["passing"] += bool(PASSING.search(old) or PASSING.search(new)) \
                        and PASSING.findall(old) != PASSING.findall(new)
    if blocks:
        print(f"planner: HANDOFF.md edit blocks {blocks['blocks']}, of them changing a task's passing state "
              f"{blocks['passing']} (C12; 405 of 908 on 09-21/22)")
    found = Counter()
    for x in chosen.values():  # the guard's wait for a read's call in its transcript (work_meter, batch_lookups)
        with contextlib.suppress(OSError, ValueError, KeyError):
            for k, v in (json.load(open(os.path.join(HERE, "state", f"work-{x['sid']}.json"))).get("batch_lookups")
                         or {}).items():
                found[k] += v
    if found:
        n = found["found"] + found["missed"]
        print(f"reads' guards: the call found in its transcript {found['found']} of {n} times, "
              f"{found['seconds'] / max(n, 1):.2f} s waited a read")
    switches = [f for f in ("support-apart", "grouped-repairs", "continue-by-fork", "measure-bound", "review-beside-check",
                            "role-layers") if os.path.exists(os.path.join(HERE, "state", f))]
    print(f"the owner's switches on: {', '.join(switches) or 'none'}")
    print(f"\ncloses: {dict(closes)}; keyed and given: {dict(keyed)}")
    print(f"told by the change replies: {dict(told)}")
    print(f"launches: {dict(launched)}")
    tasks, runs, planner, holds = lc.parse(time.strftime("%Y-%m-%dT%H:%M:%S", time.localtime(since)))
    landed = [t for t, e in tasks.items() if e.get("landed") or e.get("commit_direct")]
    print(f"\ntasks landed: {len(landed)}; machine runs: {len(runs)} ({sum(r['end'] - r['start'] for r in runs) / 3600:.1f} h);"
          f" planner turns: {len(planner)}")
    st = json.load(open(os.path.join(HERE, "state", "v2.json")))
    stages(tasks, st)
    near = {n: x for n, x in sessions.items() if since - 6 * 3600 <= (x.get("started") or 0) < until
            and x.get("sid") in paths and x.get("role") in WORKING}
    idle(since, until, tasks, st, [tl.record(n, x, paths[x["sid"]]) for n, x in near.items()])
    slow(since, until)
    landed_on = checked = 0
    for line in open(os.path.join(HERE, "state", "v2.log"), errors="ignore"):
        m = re.match(r"^(\S+) the train of tasks .+? (lands on the build its check batch made|is checked together)", line)
        if m and since <= time.mktime(time.strptime(m.group(1), "%Y-%m-%dT%H:%M:%S")) < until:
            landed_on += m.group(2).startswith("lands")
            checked += not m.group(2).startswith("lands")
    if landed_on or checked:
        print(f"trains: {landed_on} landed on their check batch's kept build (C10), {checked} checked again")
    rejected = [t for t, v in st["tasks"].items() if v.get("rejections") and t in tasks]
    print(f"tasks rejected at least once among those the window touched: {len(rejected)} of "
          f"{sum(1 for t in tasks if (st['tasks'].get(t) or {}).get('kind') in ('build', 'fix', 'design', 'investigate'))}")
    corrected = [t for t, v in st["tasks"].items() if v.get("corrected") and (v.get("reviews") or t) in tasks]
    print(f"reviews that corrected the words themselves and accepted (C7): {len(corrected)}"
          + (f" ({', '.join(sorted(corrected)[:8])})" if corrected else ""))
    drafted = {t for t in tasks if "\nFrom the review:" in ((tl.v2.read_task(t) or {}).get("description") or "")}
    if drafted:
        print(f"tasks briefed from a follow-up draft (C15): {len(drafted)}, rejected at least once "
              f"{sum(1 for t in drafted if (st['tasks'].get(t) or {}).get('rejections'))}; the other briefed tasks: "
              f"{len(rejected) - sum(1 for t in drafted if t in rejected)} rejected")
    return 0


if __name__ == "__main__":
    sys.exit(main())
