#!/usr/bin/env python3
"""How the sessions of every role, and the implementers before them, spend their windows, and what they produce.

  efficiency.py [--from N] [--json]      every role's sessions, and the v1 implementers impl-N onward (8 by default)

Per session: minutes, requests, tool calls per request, output tokens (thinking included), tokens of tool
results, reads and the share of read tokens that went to a file the same session had already read, the minutes
and context before the first write, the calls the guards refused, and what was committed: for a producing session
(designer, investigator, implementer, fixer) the commit its task's finalization made (.build/tasks/ID/finalized.json),
for a v1 implementer the commits made while it ran, with
the lines they added to theories, tools and documents. Reads and writes are told apart as work_meter.py tells them,
so the measure is the one the hooks act on.
"""
import collections
import datetime
import glob
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import work_meter  # noqa: E402
from ctx_gauge import CHARS_PER_TOKEN  # noqa: E402  what the gauge estimates a session's context with

PROJECT = os.environ.get("ORCH_PROJECT") or os.path.dirname(os.path.dirname(HERE))
TRANSCRIPTS = os.environ.get("ORCH_TRANSCRIPTS") or os.path.expanduser(
    "~/.claude/projects/" + PROJECT.replace("/", "-").replace("_", "-"))
ROLES = ("kb", "plan", "brief", "design", "investigate", "implement", "fix", "review", "ask", "impl")
START = re.compile(r"^\s*You are ((" + "|".join(ROLES) + r")-([\w.]+)),")
PRODUCING = ("design", "investigate", "implement", "fix")  # credited with their task's finalized commit
# the guards' refusals (work_meter.py), which a session sees as its tool call's result
REFUSED = re.compile(r"are already in your context|since your last production|Waiting is refused|came back \d+ times|"
                     r"budget .* is spent|starts no subagents|reads statements, not details|That job is still running")


def epoch(ts):
    return datetime.datetime.fromisoformat(ts.replace("Z", "+00:00")).timestamp()


def session(path):
    """The metrics of a session's own part, or None when it is no session of a role and no v1 implementer."""
    name = role = None
    reqs, calls, results, reads = {}, {}, collections.Counter(), collections.Counter()
    read_tok = reread_tok = 0
    seen = set()
    first = last = first_write = None
    refused = 0
    for line in open(path, errors="ignore"):
        try:
            d = json.loads(line)
        except ValueError:
            continue
        m = d.get("message") or {}
        if d.get("type") == "user" and not d.get("isSidechain"):
            c = m.get("content")
            text = c if isinstance(c, str) else " ".join(x.get("text", "") for x in c or [] if isinstance(x, dict))
            s = START.match(text or "")
            if s:
                # a fork's transcript replays its origin's, so the origin's own launch prompt stands in it too. The
                # last one is this session's own, and everything before it is what it forked: taking the first
                # named every planner and every consultation kb-1 and counted the base's requests as theirs, which
                # is why no `plan` session appeared in the report at all (2026-09-21).
                name, role, first = s.group(1), s.group(2), epoch(d["timestamp"])
                reqs, calls, results, reads = {}, {}, collections.Counter(), collections.Counter()
                read_tok = reread_tok = 0
                seen, refused = set(), 0
                last = first_write = None
                continue
        if name is None or d.get("isSidechain"):
            continue
        ts = d.get("timestamp")
        if ts:
            last = epoch(ts)
        if d.get("type") == "assistant" and m.get("id"):
            u = m.get("usage") or {}
            ctx = (u.get("input_tokens") or 0) + (u.get("cache_read_input_tokens") or 0) + (u.get("cache_creation_input_tokens") or 0)
            if ctx and m["id"] not in reqs:
                reqs[m["id"]] = (ctx, u.get("output_tokens") or 0)
            for c in m.get("content") or []:
                if isinstance(c, dict) and c.get("type") == "tool_use":
                    inp = c.get("input") or {}
                    k = work_meter.kind(c.get("name"), inp)
                    r = work_meter.requested(c.get("name"), inp, PROJECT)
                    calls[c["id"]] = (k, r[0] if r else None)
                    if k == "write" and first_write is None and ts:
                        first_write = (epoch(ts) - first, reqs[m["id"]][0] if m["id"] in reqs else 0)
        elif d.get("type") == "user" and isinstance(m.get("content"), list):
            for c in m["content"]:
                if isinstance(c, dict) and c.get("type") == "tool_result" and c.get("tool_use_id") in calls:
                    k, f = calls[c["tool_use_id"]]
                    body = json.dumps(c.get("content") or "")
                    t = len(body) / CHARS_PER_TOKEN
                    results[k] += t
                    if REFUSED.search(body):
                        refused += 1
                    elif k == "read":
                        reads["n"] += 1
                        read_tok += t
                        if f and f in seen:
                            reread_tok += t
                        if f:
                            seen.add(f)
    if name is None or not reqs:
        return None
    ctx = [c for c, _ in reqs.values()]
    return {"name": name, "role": role, "sid": os.path.basename(path)[:8], "start": first, "end": last,
            "minutes": (last - first) / 60, "requests": len(reqs), "calls": len(calls),
            "output": sum(o for _, o in reqs.values()), "results": sum(results.values()),
            "reads": reads["n"], "read_tokens": read_tok, "reread_share": reread_tok / read_tok if read_tok else 0,
            "first_write_min": first_write[0] / 60 if first_write else None,
            "first_write_ctx": first_write[1] - ctx[0] if first_write and first_write[1] else None,
            "growth": max(ctx) - ctx[0], "refused": refused}


def numstat(ref):
    """Lines a commit added to theories, tools and documents outside the orchestration and validation data."""
    out = subprocess.run(["git", "-C", PROJECT, "show", "--numstat", "--format=", ref], capture_output=True, text=True).stdout
    return sum(int(a) for a, _, p in (ln.split("\t") for ln in out.splitlines() if ln.count("\t") == 2)
               if a != "-" and p.endswith((".thy", ".py", ".md")) and not p.startswith((".claude/", "validation/"))
               and p != "HANDOFF.md")


def commits(rows):
    for r in [r for r in rows if r["role"] in PRODUCING]:
        tid = r["name"].split("-", 1)[1].split(".")[0]
        try:
            ref = json.load(open(os.path.join(PROJECT, ".build", "tasks", tid, "finalized.json"))).get("commit")
        except (OSError, ValueError):
            ref = None
        r["commits"], r["lines"] = (1, numstat(ref)) if ref else (0, 0)
    rows = [r for r in rows if r["role"] == "impl"]
    log = subprocess.run(["git", "-C", PROJECT, "log", "--since=2026-09-18T00:00:00Z", "--numstat", "--format=@%ct"],
                         capture_output=True, text=True).stdout
    out, cur = [], None
    for ln in log.splitlines():
        if ln.startswith("@"):
            cur = {"t": int(ln[1:]), "lines": 0}
            out.append(cur)
        elif ln.strip() and cur:
            a, _, p = ln.split("\t")
            if a != "-" and not p.startswith("validation/") and "__pycache__" not in p and p != "HANDOFF.md" \
                    and p.endswith((".thy", ".py", ".md")) and not p.startswith(".claude/"):
                cur["lines"] += int(a)
    for r in rows:
        mine = [c for c in out if r["start"] <= c["t"] <= r["end"] + 120]
        r["commits"], r["lines"] = len(mine), sum(c["lines"] for c in mine)


def main():
    lowest = int(sys.argv[sys.argv.index("--from") + 1]) if "--from" in sys.argv else 8
    rows = [r for r in map(session, (f for d in work_meter.v2.transcript_dirs(TRANSCRIPTS)
                                     for f in glob.glob(d + "/*.jsonl"))) if r]  # a task tree's sessions too
    rows = [r for r in rows if r["role"] != "impl" or int(r["name"].split("-")[1]) >= lowest]
    rows.sort(key=lambda r: (ROLES.index(r["role"]), r["start"]))
    commits(rows)
    if "--json" in sys.argv:
        print(json.dumps(rows, indent=1))
        return 0
    print("session          min  reqs calls/req  outK resultK reads readK reread  1st-write(min,K) refused commits +lines")
    for r in rows:
        fw = f"{r['first_write_min']:.0f},{(r['first_write_ctx'] or 0) / 1000:.0f}" if r["first_write_min"] is not None else "-"
        print(f"{r['name']:16} {r['minutes']:4.0f} {r['requests']:5} {r['calls'] / r['requests']:9.2f} {r['output'] / 1000:5.0f}"
              f" {r['results'] / 1000:7.0f} {r['reads']:5} {r['read_tokens'] / 1000:5.0f} {100 * r['reread_share']:5.0f}%"
              f" {fw:>17} {r['refused']:7} {r.get('commits', '-'):>7} {r.get('lines', '-'):>7}")
    for role in ROLES:
        some = [r for r in rows if r["role"] == role]
        if not some:
            continue
        n = len(some)
        avg = lambda k: sum(r[k] or 0 for r in some) / n
        line = (f"\nmean of {n} {role} session{'s' if n > 1 else ''}: {avg('minutes'):.0f} min, {avg('requests'):.0f} requests, "
                f"{sum(r['calls'] for r in some) / sum(r['requests'] for r in some):.2f} calls per request, "
                f"{avg('output') / 1000:.0f}K output, {avg('read_tokens') / 1000:.0f}K read "
                f"({100 * sum(r['reread_share'] * r['read_tokens'] for r in some) / max(1, sum(r['read_tokens'] for r in some)):.0f}% re-read), "
                f"{sum(r['refused'] for r in some)} refused")
        if "commits" in some[0]:
            line += (f", first write after {avg('first_write_min'):.1f} min and {avg('first_write_ctx') / 1000:.0f}K, "
                     f"{sum(r['commits'] for r in some)} commits adding {sum(r['lines'] for r in some)} lines")
        print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
