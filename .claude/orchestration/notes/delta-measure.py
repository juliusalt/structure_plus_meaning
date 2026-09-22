#!/usr/bin/env python3
"""The delta layer's measurement (notes/plan-delta-layer-tasks.md, task 9): what keeping each base current cost over a
window, and what its forks read at their start.

    python3 -B notes/delta-measure.py SINCE [UNTIL]      times as "YYYY-MM-DD HH:MM" (local)

Per base: layer refreshes and delta builds, each with its cost in input-equivalent tokens (its session's own requests:
cache reads at 0.1, writes at 1.25, fresh input at 1, output at 5), the keep-warm pings (their first request), and the
forks started from it (their first request's read and write, from the log's "cache of" lines). The upkeep an hour is
(refreshes + builds + pings) over the window. The baseline is the same script over 2026-09-22 10:00-20:00.
"""
import glob
import json
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATE = os.path.join(HERE, "state")
PROJECTS = os.path.expanduser("~/.claude/projects")
STAMP = re.compile(r"^(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d) ")


def when(text):
    return time.mktime(time.strptime(text, "%Y-%m-%d %H:%M"))


def lines(path, since, until):
    for line in open(path, errors="ignore"):
        m = STAMP.match(line)
        if m and since <= time.mktime(time.strptime(m.group(1), "%Y-%m-%dT%H:%M:%S")) < until:
            yield line.rstrip("\n")


def cost(usage):
    return (usage.get("cache_read_input_tokens", 0) * 0.1 + usage.get("cache_creation_input_tokens", 0) * 1.25
            + usage.get("input_tokens", 0) + usage.get("output_tokens", 0) * 5)


def session_cost(prefix):
    """The input-equivalent of every request a session made itself (not the prefix it forked), found by its id's start."""
    for path in glob.glob(os.path.join(PROJECTS, "*", prefix + "*.jsonl")):
        seen, total = set(), 0.0
        for line in open(path, errors="ignore"):
            if '"usage"' not in line:
                continue
            d = json.loads(line)
            m = d.get("message") or {}
            if d.get("type") == "assistant" and m.get("id") not in seen:
                seen.add(m.get("id"))
                total += cost(m.get("usage") or {})
        return total
    return None


def first_request(line):
    m = re.search(r"cache_read=(\d+) cache_write=(\d+)", line)
    return (int(m.group(1)), int(m.group(2))) if m else (0, 0)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    since = when(sys.argv[1])
    until = when(sys.argv[2]) if len(sys.argv) > 2 else time.time()
    hours = (until - since) / 3600
    log, warm = os.path.join(STATE, "v2.log"), os.path.join(STATE, "warm.log")
    started = {}
    for line in lines(log, since, until):
        m = re.search(r"started (\S+) \(\S+, from (\w+)\)", line)
        if m:
            started[m.group(1)] = m.group(2)
    forks = {}
    for line in lines(log, since, until):
        m = re.search(r"cache of (\S+): (.*)", line)
        if m and m.group(1) in started:
            forks.setdefault(started[m.group(1)], []).append(first_request(m.group(2)))
    print(f"# {sys.argv[1]} to {sys.argv[2] if len(sys.argv) > 2 else 'now'} ({hours:.1f} h)")
    for who in ("max", "xhigh", "high"):
        refresh, build, ping = [], [], []
        for line in lines(warm, since, until):
            m = re.match(rf" (layer|delta) {who}: \w+ +session fork (\w+)", line[19:])
            if m:
                c = session_cost(m.group(2))
                (refresh if m.group(1) == "layer" else build).append(c or 0)
            elif re.search(rf" warm {who}( stable| layer)?: OK", line):
                r, w = first_request(line)
                ping.append(r * 0.1 + w * 1.25)
        upkeep = sum(refresh) + sum(build) + sum(ping)
        f = forks.get(who, [])
        print(f"{who}: {len(refresh)} layer refreshes ({sum(refresh) / 1000:,.0f}K), {len(build)} delta builds "
              f"({sum(build) / 1000:,.0f}K), {len(ping)} pings ({sum(ping) / 1000:,.0f}K): upkeep "
              f"{upkeep / 1000 / max(hours, 0.01):,.0f}K an hour; {len(f)} forks, their first requests reading "
              f"{sum(r for r, _ in f) / max(len(f), 1) / 1000:,.0f}K and writing {sum(w for _, w in f) / max(len(f), 1) / 1000:,.1f}K "
              "on average")
    return 0


if __name__ == "__main__":
    sys.exit(main())
