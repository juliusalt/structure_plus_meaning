#!/usr/bin/env python3
"""The generated indexes as the harness's own generator makes them from the repository at each commit the given runs'
sessions started at — the truth simreport.py checks the forks' stale lines against — made once for every run, on every
core, into OUT/../index-cache/<commit>.json.

    indexcache.py ORCH RUN [RUN ...]
"""
import concurrent.futures
import glob
import json
import os
import subprocess
import sys
import tempfile

SIM = os.path.dirname(os.path.abspath(__file__))
CACHE = os.path.join(SIM, "index-cache")


def make(args):
    orch, project, head = args
    out = os.path.join(CACHE, head + ".json")
    if os.path.exists(out):
        return head, "kept"
    with tempfile.TemporaryDirectory() as d:
        archive = subprocess.Popen(["git", "-C", project, "archive", head], stdout=subprocess.PIPE)
        subprocess.run(["tar", "-x", "-C", d, "--exclude=.claude/orchestration"], stdin=archive.stdout, check=True)
        archive.wait()
        here = os.path.join(d, ".claude", "orchestration")
        os.makedirs(os.path.join(here, "state", "held"))
        for name in os.listdir(orch):  # the harness's files linked, its generated state its own
            if name not in ("state", "notes", "__pycache__"):
                os.symlink(os.path.join(orch, name), os.path.join(here, name))
        env = {k: v for k, v in os.environ.items() if not k.startswith(("ORCH_", "SIM_"))}
        env.update(ORCH_PROJECT=d, ORCH_STATE_DIR=os.path.join(here, "state"), PYTHONDONTWRITEBYTECODE="1")
        subprocess.run([sys.executable, "-B", "-c", "import sys; sys.path.insert(0, sys.argv[1]); "
                        "import select_base_load as s; s.refresh_indexes()", here], env=env, cwd=d,
                       capture_output=True, check=True)
        held = os.path.join(here, "state", "held")
        texts = {os.path.splitext(n)[0]: open(os.path.join(held, n), errors="ignore").read() for n in os.listdir(held)}
    with open(out + ".tmp", "w") as f:
        json.dump(texts, f)
    os.replace(out + ".tmp", out)
    return head, "made"


def main():
    orch, runs = sys.argv[1], sys.argv[2:]
    os.makedirs(CACHE, exist_ok=True)
    heads = set()
    for run in runs:
        heads |= {r.get("head") for r in json.load(open(os.path.join(run, "fake", "sessions.json"))).values()
                  if r.get("head")}
        for line in open(os.path.join(run, "sim.jsonl")):
            r = json.loads(line)
            if r.get("what") == "start" and r.get("head"):
                heads.add(r["head"])
    project = os.path.join(runs[0], "project")
    jobs = [(orch, project, h) for h in sorted(heads)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(16, os.cpu_count() or 4)) as pool:
        done = list(pool.map(make, jobs))
    print(f"{len(done)} commits: {sum(1 for _, s in done if s == 'made')} made, {sum(1 for _, s in done if s == 'kept')} kept")


if __name__ == "__main__":
    main()
