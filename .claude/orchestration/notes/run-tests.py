#!/usr/bin/env python3
"""Run the harness's tests in parallel shards: run-tests.py [-k EXPR] [TEST_FILE ...]

The whole suite in one pytest took seven minutes, and a full mutation check twenty (2026-09-22), and every change
waited on them; the owner: "update the testing and mutation setup as it is taking way to long bottlenecking our work".
The tests are independent — each makes a world of its own under a temporary directory — so they run as shards, one
pytest each, the longest dealt first by the times recorded of earlier runs (DURATIONS), at a lower priority than the
machine's own work (nice), since the orchestration's checks run beside them. Prints what failed and a total, keeps
each test's time for the next run, and exits 1 when anything failed. Run it from the directory whose tests it runs.
"""
import json
import os
import re
import subprocess
import sys
import tempfile
import time
import xml.etree.ElementTree as ET

WORKERS = int(os.environ.get("ORCH_TEST_WORKERS", max(2, min(16, (os.cpu_count() or 4) // 2))))
DURATIONS = os.environ.get("ORCH_TEST_DURATIONS", os.path.join(tempfile.gettempdir(), "orch-test-durations.json"))
NICE = ["nice", "-n", os.environ.get("ORCH_TEST_NICE", "10")]


def collect(args):
    out = subprocess.run([sys.executable, "-B", "-m", "pytest", "-q", "-p", "no:cacheprovider", "--collect-only", *args],
                         capture_output=True, text=True).stdout
    return [line.strip() for line in out.splitlines() if "::" in line and not line.startswith(" ")]


def shards(ids, times, n):
    """The ids dealt into n shards, longest first, each to the shard with the least time so far."""
    load, out = [0.0] * n, [[] for _ in range(n)]
    for i in sorted(ids, key=lambda x: -times.get(x, 1.0)):
        k = min(range(n), key=load.__getitem__)
        out[k].append(i)
        load[k] += times.get(i, 1.0)
    return [s for s in out if s]


def main():
    argv = sys.argv[1:]
    files = [a for a in argv if a.endswith(".py")] or sorted(f for f in os.listdir(".") if re.fullmatch(r"test_\w+\.py", f))
    extra = [a for a in argv if not a.endswith(".py")]
    ids = collect(files + extra)
    if not ids:
        print("no tests collected")
        return 1
    try:
        times = json.load(open(DURATIONS))
    except (OSError, ValueError):
        times = {}
    parts = shards(ids, times, WORKERS)
    started, runs = time.time(), []
    with tempfile.TemporaryDirectory() as tmp:
        for i, part in enumerate(parts):
            args_file = os.path.join(tmp, f"ids-{i}.txt")
            open(args_file, "w").write("\n".join(part))
            xml = os.path.join(tmp, f"shard-{i}.xml")
            log = open(os.path.join(tmp, f"shard-{i}.log"), "w")
            runs.append((subprocess.Popen(NICE + [sys.executable, "-B", "-m", "pytest", "-q", "-p", "no:cacheprovider",
                                                  f"--junitxml={xml}", f"@{args_file}"],
                                          stdout=log, stderr=subprocess.STDOUT), xml, log.name))
        for run, _, _ in runs:
            run.wait()
        passed, failed = 0, []
        for run, xml, log in runs:
            try:
                root = ET.parse(xml).getroot()
            except (OSError, ET.ParseError):
                failed.append(f"a shard left no report (exit {run.returncode}): {open(log).read()[-800:]}")
                continue
            for case in root.iter("testcase"):
                cls, name = case.get("classname", ""), case.get("name", "")
                module, _, klass = cls.rpartition(".")
                node = f"{module.replace('.', '/')}.py::{klass}::{name}" if module else f"{cls}::{name}"
                times[node] = float(case.get("time") or 0)
                bad = case.find("failure") if case.find("failure") is not None else case.find("error")
                if bad is not None:
                    failed.append(f"FAILED {node} - {(bad.get('message') or '')[:160]}")
                elif case.find("skipped") is None:
                    passed += 1
    with open(DURATIONS + ".tmp", "w") as f:
        json.dump(times, f)
    os.replace(DURATIONS + ".tmp", DURATIONS)
    for line in failed:
        print(line)
    print(f"{len(failed)} failed, {passed} passed in {time.time() - started:.1f}s ({len(parts)} shards)")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
