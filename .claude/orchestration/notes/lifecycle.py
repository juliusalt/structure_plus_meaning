#!/usr/bin/env python3
"""Every task's way from the graph to main, and every run of the machine, read from state/v2.log.

    python3 -B notes/lifecycle.py [--since YYYY-MM-DD] [--out FILE]

Not part of the harness; read-only but for its output (state/analysis/lifecycle.json by default). Per task: when the
planner made it, when each of its sessions started, resumed and was released, its results, when its check was asked
for, ran and ended, when its reviews started and ended, when it was committed and when it landed. Per machine run (a
batch check, a train's check, a landing check): its tasks, start, end and outcome. Per planner turn: resumed to handled.
The report after it says where the time between a task's creation and its landing went.
"""
import json
import os
import re
import sys
import time
from collections import defaultdict

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATE = os.path.join(HERE, "state")
LINE = re.compile(r"^(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d) (.*)$")
IDS = re.compile(r"\d+(?:\.\d+)?")


def ids(text):
    return IDS.findall(text)


def parse(since=None):
    tasks = defaultdict(lambda: defaultdict(list))
    runs, planner, holds = [], [], []
    open_runs, open_plan = {}, {}
    session_task = {}
    for line in open(os.path.join(STATE, "v2.log"), errors="ignore"):
        m = LINE.match(line.rstrip("\n"))
        if not m:
            continue
        t = time.mktime(time.strptime(m.group(1), "%Y-%m-%dT%H:%M:%S"))
        if since and m.group(1) < since:
            continue
        x = m.group(2)
        if (g := re.match(r"the planner edited the graph: \d+ operation\(s\); made ([\d, ]+)", x)):
            for i in ids(g.group(1)):
                tasks[i]["made"].append(t)
        elif (g := re.match(r"started ((\w+(?:-\w+)*?)-(\d+)(?:\.\d+)?) \(([\w-]+), from (\S+)\)", x)):
            name, _, tid, role, origin = g.groups()
            if role not in ("planner", "kb", "consultant"):
                session_task[name] = tid
                tasks[tid]["start"].append((t, name, role))
        elif (g := re.match(r"resumed (\S+)", x)):
            name = g.group(1)
            if name.startswith("plan-"):
                open_plan[name] = t
            elif name in session_task:
                tasks[session_task[name]]["resume"].append((t, name))
        elif (g := re.match(r"(plan-\d+) has handled what it was given", x)):
            if g.group(1) in open_plan:
                planner.append((open_plan.pop(g.group(1)), t))
        elif (g := re.match(r"started (plan-\d+)", x)):
            open_plan[g.group(1)] = t
        elif (g := re.match(r"released (\S+)", x)):
            name = g.group(1)
            if name in session_task:
                tasks[session_task[name]]["release"].append((t, name))
            if name in open_plan:
                planner.append((open_plan.pop(name), t))
        elif (g := re.match(r"result of task (\d+): (\w+)", x)):
            tasks[g.group(1)]["result"].append((t, g.group(2)))
        elif (g := re.match(r"task (\d+)'s (?:check waits for the next batch|session asks for the repository's check)", x)):
            tasks[g.group(1)]["check_asked"].append(t)
        elif (g := re.match(r"the work of tasks? (.+?) (?:is|are) checked together with main", x)):
            key = ("batch", tuple(ids(g.group(1))))
            open_runs[key] = t
        elif (g := re.match(r"the check of tasks? (.+?): (passed|failed) in (\d+) s", x)):
            key = ("batch", tuple(ids(g.group(1))))
            start = open_runs.pop(key, t - int(g.group(3)))
            runs.append(dict(kind="batch", tasks=list(key[1]), start=start, end=t, ok=g.group(2) == "passed"))
        elif (g := re.match(r"the train of tasks? (.+?) is checked together with main", x)):
            open_runs[("train", tuple(ids(g.group(1))))] = t
        elif (g := re.match(r"the train of tasks? (.+?): its check (passed|failed) in (\d+) s", x)):
            key = ("train", tuple(ids(g.group(1))))
            start = open_runs.pop(key, t - int(g.group(3)))
            runs.append(dict(kind="train", tasks=list(key[1]), start=start, end=t, ok=g.group(2) == "passed"))
        elif (g := re.match(r"the train of tasks? (.+?) landed as (\w+)", x)):
            for i in ids(g.group(1)):
                tasks[i]["landed"].append(t)
        elif (g := re.match(r"landing check of task (\d+): (passed|failed) in (\d+) s", x)):
            runs.append(dict(kind="landing", tasks=[g.group(1)], start=t - int(g.group(3)), end=t,
                             ok=g.group(2) == "passed"))
        elif (g := re.match(r"check of task (\d+): (passed|failed)", x)):
            tasks[g.group(1)]["checked"].append((t, g.group(2)))
        elif (g := re.match(r"task (\d+) is committed on its branch and waits to land", x)):
            tasks[g.group(1)]["committed"].append(t)
        elif (g := re.match(r"commit of task (\d+): (\w+)$", x)):
            tasks[g.group(1)]["committed"].append(t)
            tasks[g.group(1)]["commit_direct"].append(t)
        elif (g := re.match(r"task (\d+) waits for task (\d+), which is with the planner", x)):
            holds.append((t, g.group(1), g.group(2)))
    return tasks, runs, planner, holds


def main():
    since = sys.argv[sys.argv.index("--since") + 1] if "--since" in sys.argv else None
    out = sys.argv[sys.argv.index("--out") + 1] if "--out" in sys.argv else os.path.join(STATE, "analysis",
                                                                                       "lifecycle.json")
    tasks, runs, planner, holds = parse(since)
    with open(out, "w") as f:
        json.dump(dict(tasks={k: dict(v) for k, v in tasks.items()}, runs=runs, planner=planner, holds=holds), f)
    print(f"{len(tasks)} tasks, {len(runs)} runs, {len(planner)} planner turns -> {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
