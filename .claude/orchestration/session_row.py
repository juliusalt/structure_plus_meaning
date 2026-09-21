#!/usr/bin/env python3
"""Print `<kind> <id-or-pid> <activity> <session-id> <state>` for the live session of this project (or of one of its
task trees) with the given name; nothing if none.

`activity` is the listing's live field (`busy` or `idle`: whether a turn is running); `state` is the
supervisor's coarser label (`working`, `done`, `blocked`), which can stay `working` long after a turn ended.

A background session whose turn has ended stays listed (state `done`, process alive, still reachable by
message); one that was stopped or has exited is not listed. So "no row" means the session is gone.
"""
import json
import os
import subprocess
import sys

PROJECT = os.environ.get("ORCH_PROJECT") or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
try:
    rows = json.loads(subprocess.run(["claude", "agents", "--json"], capture_output=True, text=True, timeout=60).stdout)
except (ValueError, OSError, subprocess.SubprocessError):
    print("unknown - listing-failed")
    sys.exit(2)
# A session started in a task's own tree (.build/trees/ID) is listed under that tree: matched on the project alone it
# was not found, and on 2026-09-20 two such sessions ran unseen while the harness called their starts unconfirmed.
TREES = os.path.join(os.path.realpath(PROJECT), ".build", "trees", "")


def ours(cwd):
    cwd = os.path.realpath(cwd or "")
    return cwd == os.path.realpath(PROJECT) or (cwd + os.sep).startswith(TREES)


for r in rows:
    if r.get("name") == sys.argv[1] and ours(r.get("cwd")):
        print(r.get("kind", "?"), r.get("id") or r.get("pid"), r.get("status") or r.get("state") or "?",
              r.get("sessionId", "?"), r.get("state") or "-")
        break
