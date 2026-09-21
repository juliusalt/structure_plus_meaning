#!/usr/bin/env python3
"""git's pre-commit and pre-merge-commit hook: a commit may not leave HEAD with trouble it does not already have.

The finalizer holds every commit the orchestration makes to this (v2.new_trouble); the hook holds every other one —
the owner's, a Codex session's — to the same rule, through the same function. HEAD went inconsistent on 2026-09-20
when a commit took ROOT whole, with the declarations of two theories whose files stayed uncommitted, and from then on
every tree made from HEAD refused every check. Once HEAD is sound, a commit that adds no trouble leaves it sound.

Installed by linking it from the repository's hooks (`.git/hooks/pre-commit` and `.git/hooks/pre-merge-commit`, both
to `../../.claude/orchestration/commit_gate.py`); `git commit --no-verify` passes it by. A fault of the gate itself
lets the commit through and says so: it stands in front of the owner's own commits, and a fault of the harness must
not stop them.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))
try:
    import v2  # noqa: E402
    worse = v2.new_trouble(os.getcwd())  # git runs a hook at the top of the working tree the commit is made in
except Exception as e:  # noqa: BLE001
    print(f"commit gate: this commit could not be checked ({e!r}); it goes through unchecked", file=sys.stderr)
    sys.exit(0)
if worse:
    print("commit gate: this commit would leave HEAD inconsistent, and every tree made from HEAD would refuse every "
          "check:", file=sys.stderr)
    for line in worse:
        print(f"  - {line}", file=sys.stderr)
    print("Commit what it declares or imports with it, or leave out the line that needs it "
          "(`git commit --no-verify` passes this gate by).", file=sys.stderr)
    sys.exit(1)
