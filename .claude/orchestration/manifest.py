#!/usr/bin/env python3
"""What a base holds (its load list), and which of it has gone stale since it was loaded.

  manifest.py list [WHO]       the files of that base's load list (max, xhigh, high), one per line, by tier
  manifest.py snapshot [WHO]   record a digest of every held file (run once, after that role's load)
  manifest.py changed [WHO]    one line naming the held files that differ from that role's snapshot
  manifest.py size [WHO]       one line: files, characters, estimated tokens

A loaded context is append-only, so a held file is a snapshot; `changed` is
how its holder learns which of its copies no longer match the repository.
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
PROJECT = os.path.dirname(os.path.dirname(HERE))
STATE = os.environ.get("ORCH_STATE_DIR") or os.path.join(HERE, "state")
WHO = sys.argv[2] if len(sys.argv) > 2 else "max"
MANIFEST = os.path.join(STATE, f"{WHO}-manifest.json")
# characters per token measured on this project's Opus 5 transcripts, 2026-09-18 (select_base_load.py uses the same)
RATIO = {".md": 3.05, ".txt": 3.05, ".thy": 2.46, ".py": 2.54}
LINE_PREFIX = 7  # characters a Read puts before each line
PART_TOKENS = 18_000  # a single Read returns at most 25,000 tokens
OVERHEAD_TOKENS = 48_000  # fresh session, role prompt, printed list; plus 90 per read
TARGET = int(os.environ.get("ORCH_BASE_TARGET", 530_000))  # loaded, everything included: the owner's request of 2026-09-19
LINE_LIMIT = 1800  # a Read cuts every line after 2,000 characters


# One load list per base: the planner's and the knowledge base's (max), the middle one (xhigh), the implementation
# one (high). ORCH_LOAD_LIST overrides it (base.sh exports it).
LISTS = {"max": "base-load-max.txt", "xhigh": "base-load-xhigh.txt", "high": "base-load-high.txt"}


def load_list():
    return os.environ.get("ORCH_LOAD_LIST") or os.path.join(HERE, LISTS.get(WHO, "base-load-max.txt"))


def held_files():
    """(tier, path) for every file matched by the base's load list; optional tiers are skipped."""
    tier, out, seen = "", [], set()
    for raw in open(load_list()):
        line = raw.split("  #")[0].strip()  # a trailing "  # …" is a comment
        if line.startswith("#"):
            tier = line.lstrip("# ").strip()
            continue
        if not line or tier.startswith("optional"):
            continue
        pattern = os.path.expanduser(line)
        if not os.path.isabs(pattern):
            pattern = os.path.join(PROJECT, pattern)
        for p in sorted(glob.glob(pattern)):
            if p not in seen and os.path.isfile(p):
                seen.add(p)
                LEVELS[p] = next((lv for lv in ("signatures", "definitions") if f"as {lv}" in tier), "statements")
                out.append((tier, p))
    return out


LEVELS = {}  # path -> digest level, from the header of the tier that lists it


def level_of(path):
    return LEVELS.get(path, "statements")


def tokens(path):
    text, _ = held_text(path, level_of(path))  # theories and tools are held as digests
    return int((len(text.encode()) + LINE_PREFIX * (text.count("\n") + 1)) / RATIO.get(os.path.splitext(path)[1], 2.6))


def readable(path):
    """The path to read: the file itself, or a folded copy when it has lines the Read tool would cut."""
    text, digested = held_text(path, level_of(path))
    if not digested and all(len(ln) <= LINE_LIMIT for ln in text.splitlines()):
        return path, 0
    out, cut = [], 0
    for ln in text.splitlines():
        cut += len(ln) > LINE_LIMIT
        while len(ln) > LINE_LIMIT:
            at = ln.rfind(" ", 0, LINE_LIMIT)
            at = at if at > 0 else LINE_LIMIT
            out.append(ln[:at])
            ln = ln[at:].lstrip(" ")
        out.append(ln)
    held = os.path.join(STATE, "held", level_of(path) if digested else "")
    os.makedirs(held, exist_ok=True)
    copy = os.path.join(held, os.path.basename(path))
    open(copy, "w").write("\n".join(out) + "\n")
    return copy, (-1 if digested else cut)


def digest(path):
    return hashlib.sha1(open(path, "rb").read()).hexdigest()


def short(path):
    return os.path.relpath(path, PROJECT) if path.startswith(PROJECT + os.sep) else path


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "changed"
    files = held_files()
    if mode == "list":
        print("# Paths under state/held/statements, state/held/definitions and state/held/signatures are digests of the like-named theories and "
              "tools: proofs and code omitted. Read each listed path as given.")
        tier = None
        for t, p in files:
            if t != tier:
                tier = t
                total = sum(os.path.getsize(q) for u, q in files if u == t)
                print(f"# {t} ({sum(1 for u, _ in files if u == t)} files, {total // 1000}K chars)")
            size = os.path.getsize(p)
            path, cut = readable(p)
            notes = []
            if cut < 0:  # statements only; the snapshot still follows the source
                pass  # held/statements and held/definitions are digests of the like-named sources (see the legend)
            elif cut:  # the listed path is a folded copy; the snapshot still follows the source
                notes.append(f"folded copy of {short(p)}, {cut} of whose lines a Read would cut; cite it by section, not by line")
            if tokens(p) > PART_TOKENS:  # over the Read tool's per-call limit: say how to split it
                lines = sum(1 for _ in open(path, errors="ignore"))
                part = max(50, int(lines * PART_TOKENS / tokens(p)) // 50 * 50)
                notes.append(f"{lines} lines: read together in parts of {part} lines (offset 1, {part + 1}, …)")
            print(short(path) + (f"  [{'; '.join(notes)}]" if notes else ""))
        return 0
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
    if not os.path.exists(MANIFEST):
        print(f"no snapshot: the {WHO} load has not been recorded")
        return 1
    record = json.load(open(MANIFEST))
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
