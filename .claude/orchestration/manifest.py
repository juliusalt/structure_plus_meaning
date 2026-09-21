#!/usr/bin/env python3
"""What a base holds (its load list), and which of it has gone stale since it was loaded.

  manifest.py snapshot [WHO]   record a digest of every held file (run once, after that role's load)
  manifest.py changed [WHO] [--since-layer SID]   one line naming the held files that differ from that role's
                               snapshot; --since-layer measures against the layer that session actually forked
  manifest.py size [WHO]       one line: files, characters, estimated tokens
  manifest.py stale-share [WHO]  one number: the share of the layer's tokens whose files have changed since it loaded

A loaded context is append-only, so a held file is a snapshot; `changed` is
how its holder learns which of its copies no longer match the repository.

A list may be split in two by a `# === layer ===` line (notes/bases-design.md section 8): above it the stable
reference, which the owner rebuilds rarely, and below it the frontier layer, which a fork of the sealed stable base
loads and which the harness refreshes on its own. ORCH_BASE_PART picks one part (`stable` or `layer`); unset, every
command is about the whole, which is what a fork of the layer actually holds — so `changed` reads both snapshots and
says what changed in either.
"""
import glob
import hashlib
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from digest import held_text  # noqa: E402
# the tree the answer is about: a task with a worktree of its own must be told what changed in ITS tree,
# not in the one the harness runs in (2026-09-20)
PROJECT = os.environ.get("ORCH_TREE") or os.environ.get("ORCH_PROJECT") or os.path.dirname(os.path.dirname(HERE))
STATE = os.environ.get("ORCH_STATE_DIR") or os.path.join(HERE, "state")
WHO = sys.argv[2] if len(sys.argv) > 2 else "max"
PART = os.environ.get("ORCH_BASE_PART", "")  # "", "stable" or "layer"
LAYER_MARK = "=== layer ==="
MANIFEST = os.path.join(STATE, f"{WHO}-layer-manifest.json" if PART == "layer" else f"{WHO}-manifest.json")
LAYER_MANIFEST = os.path.join(STATE, f"{WHO}-layer-manifest.json")
# characters per token measured on this project's Opus 5 transcripts, 2026-09-18 (select_base_load.py uses the same)
RATIO = {".md": 3.05, ".txt": 3.05, ".thy": 2.46, ".py": 2.54}
LINE_PREFIX = 7  # characters a Read puts before each line
PART_TOKENS = 18_000  # a single Read returns at most 25,000 tokens
OVERHEAD_TOKENS = 0 if PART == "layer" else 48_000  # fresh session, role prompt, printed list; plus 90 per read.
# A layer costs none of it: it is loaded by a fork of the sealed stable base, which already carries all three.
TARGET = int(os.environ.get("ORCH_BASE_TARGET", 530_000))  # loaded, everything included: the owner's request of 2026-09-19


# One load list per base: the planner's and the knowledge base's (max), the middle one (xhigh), the implementation
# one (high). ORCH_LOAD_LIST names the list to read; base.sh sets it from the base it was asked for (never from
# what it inherited), and the tests set it directly.
LISTS = {"max": "base-load-max.txt", "xhigh": "base-load-xhigh.txt", "high": "base-load-high.txt"}


def load_list():
    return os.environ.get("ORCH_LOAD_LIST") or os.path.join(HERE, LISTS.get(WHO, "base-load-max.txt"))


def has_layer(path=None):
    """Whether this list is split into a stable part and a frontier layer."""
    return any(LAYER_MARK in line for line in open(path or load_list()))


def held_files(part=None):
    """(tier, path) for every file matched by the base's load list; optional tiers are skipped. `part` (or
    ORCH_BASE_PART) narrows it to the stable reference or to the frontier layer below the `# === layer ===` line."""
    part = PART if part is None else part
    tier, where, out, seen = "", "stable", [], set()
    for raw in open(load_list()):
        line = raw.split("  #")[0].strip()  # a trailing "  # …" is a comment
        if line.startswith("#"):
            if LAYER_MARK in line:
                where = "layer"
            elif not line.lstrip("# ").startswith(("everything below", "sealed, and every role", "have changed")):
                tier = line.lstrip("# ").strip()
            continue
        if not line or tier.startswith("optional") or (part and where != part):
            continue
        pattern = os.path.expanduser(line)
        if not os.path.isabs(pattern):
            pattern = os.path.join(PROJECT, pattern)
        for p in sorted(glob.glob(pattern)):
            if p not in seen and os.path.isfile(p):
                seen.add(p)
                LEVELS[p] = next((lv for lv in ("signatures", "definitions") if f"as {lv}" in tier), "statements")
                PARTS[p] = where
                out.append((tier, p))
    return out


LEVELS = {}  # path -> digest level, from the header of the tier that lists it
PARTS = {}   # path -> "stable" or "layer", from where it stands against the list's layer mark


def level_of(path):
    return LEVELS.get(path, "statements")


def tokens(path):
    text, _ = held_text(path, level_of(path))  # theories and tools are held as digests
    return int((len(text.encode()) + LINE_PREFIX * (text.count("\n") + 1)) / RATIO.get(os.path.splitext(path)[1], 2.6))


def digest(path):
    return hashlib.sha1(open(path, "rb").read()).hexdigest()


def short(path):
    return os.path.relpath(path, PROJECT) if path.startswith(PROJECT + os.sep) else path


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "changed"
    files = held_files()
    if mode == "size":
        total = sum(len(held_text(p, level_of(p))[0]) for _, p in files)
        held = sum(tokens(p) for _, p in files)
        reads = sum(1 + tokens(p) // PART_TOKENS for _, p in files)
        print(f"{len(files)} files, {total // 1000}K chars, about {held // 1000}K tokens of files, "
              f"about {(held + OVERHEAD_TOKENS + 90 * reads) // 1000}K loaded with everything included")
        return 0
    if mode == "snapshot":
        os.makedirs(STATE, exist_ok=True)
        record = {"taken": time.strftime("%Y-%m-%dT%H:%M:%S"), "files": {p: digest(p) for _, p in files}}
        json.dump(record, open(MANIFEST, "w"), indent=0)
        total = sum(os.path.getsize(p) for _, p in files)
        print(f"snapshot of {len(files)} held files ({total // 1000}K chars) taken {record['taken']}")
        return 0
    if mode == "stale-share":  # what the refresh rule reads: the share of the layer's tokens whose files have changed
        layer = held_files("layer")
        if not layer or not os.path.exists(LAYER_MANIFEST):
            print("0")
            return 0
        record = json.load(open(LAYER_MANIFEST))["files"]
        total = sum(tokens(p) for _, p in layer) or 1
        moved = sum(tokens(p) for _, p in layer if p not in record or digest(p) != record[p])
        print(f"{moved / total:.3f}")
        return 0
    # A fork holds both parts, so both snapshots are read: the stable one and, when there is a layer, its own —
    # the layer the reader actually forked (--since-layer SID), which after a refresh is not the one standing now.
    layer_snapshot = LAYER_MANIFEST
    if "--since-layer" in sys.argv:
        sid = sys.argv[sys.argv.index("--since-layer") + 1]
        held = os.path.join(STATE, f"layer-{sid}-manifest.json")
        layer_snapshot = held if os.path.exists(held) else LAYER_MANIFEST
    records = [m for m in (MANIFEST, layer_snapshot) if os.path.exists(m)] if not PART else (
        [MANIFEST] if os.path.exists(MANIFEST) else [])
    if not records:
        print(f"no snapshot: the {WHO} load has not been recorded")
        return 1
    record = {"taken": min(json.load(open(m))["taken"] for m in records), "files": {}}
    for m in records:
        record["files"].update(json.load(open(m))["files"])
    now = {p: digest(p) for _, p in files}
    stale = [p for p, h in record["files"].items() if now.get(p) != h]
    new = [p for p in now if p not in record["files"]]
    names = [os.path.splitext(os.path.basename(p))[0] for p in stale] + [
        "+" + os.path.splitext(os.path.basename(p))[0] for p in new
    ]
    shown = ", ".join(names[:60]) + (f", … {len(names) - 60} more" if len(names) > 60 else "")
    print(f"stale since {WHO} load {record['taken']} ({len(names)}): {shown or 'none'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
