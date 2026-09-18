#!/usr/bin/env python3
"""Regenerate the measured tier of base-load.txt so that a loaded base lands on the target size.

The list has three parts. The `# pinned…` tiers are kept as written and chosen deliberately, to set the
implementer's direction: the owner's words, the operating rules, the plan, the reasoning inventory, the names
of all theories, and the founding theories of the library's own ideas. `# measured` is generated here: the
frontier and the tools recent implementers actually worked in. `# optional` is kept as written, never loaded.
This script also regenerates state/held/theory-names.md from the current theory
files, in ROOT order, followed by any files not listed there.

The measured tier is chosen from what the implementer sessions actually consulted: for every file named in
a tool call of the last SESSIONS Opus sessions of this project, the sessions that touched it and the
characters pulled from it. A file qualifies when at least MIN_SESSIONS sessions consulted it and what they
pulled amounts to at least MIN_SHARE of the file (a name that merely occurs in commands does not qualify).
Candidates are ranked by density — characters pulled per session, per character of file: what holding the
file saves against what holding it costs — and taken until the budget is full. If room remains, a second pass
takes files that a single session consulted, under the same share rule and ranking.

Sizes use characters per token measured on this project's Opus 5 transcripts (2026-09-18): Markdown and text
3.05, Isabelle 2.46, Python 2.54, for the file-by-file load. The base is now loaded as packed chunks
(base_pack.py), without the Read tool's line numbers, one Bash call per chunk of about 18K bytes, in the form
base_pack.SELECTED; sizes here use base_pack's measured ratios and that form's measured reduction. The budget
is ORCH_BASE_TARGET (530,000, everything included; manifest.TARGET) less the lean session a base starts from
and one tool call per chunk.

usage: select_base_load.py [--dry-run | --refresh-index]
--refresh-index updates only the theory-name catalogue, without selecting or removing load-list entries.
"""
import glob
import json
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from digest import held_text  # noqa: E402
from idea_candidates import founding_theories  # noqa: E402
import manifest  # noqa: E402
from base_pack import (BOOTSTRAP_PREFIX, CHUNK_BYTES, CALL_TOKENS, INDEX_RATIO, PACKED_RATIO,  # noqa: E402
                       SELECTED_FACTOR, SESSION_TOKENS)
PROJECT = os.path.dirname(os.path.dirname(HERE))
TRANSCRIPTS = os.path.expanduser("~/.claude/projects/" + PROJECT.replace("/", "-").replace("_", "-"))
TARGET = manifest.TARGET
SESSIONS = int(os.environ.get("ORCH_SELECT_SESSIONS", 7))
MIN_SESSIONS = 2
MIN_SHARE = 0.10
CHUNK_FILL = CHUNK_BYTES * 0.9  # chunks break at line ends, so they average a little under their bound
FIXED_TOKENS = 0  # the lean session measured by base_pack already includes the role prompt and the load's turns
NEVER = {"HANDOFF.md", ".claude/orchestration/owner-ledger.md", "THEORY_MAP.md"}  # always read fresh, never held


def tokens(path, level="statements"):
    """Estimated tokens of a held file in the packed load, and its share of chunk calls."""
    text, _ = held_text(path, level)  # theories and tools are held as digests: statements, not proofs or code
    size, suffix = len(text.encode()), os.path.splitext(path)[1]
    if os.path.basename(path) == "theory-names.md":
        return int(size / INDEX_RATIO * SELECTED_FACTOR["index"]), size / CHUNK_FILL
    return int(size / PACKED_RATIO.get(suffix, 2.6) * SELECTED_FACTOR.get(suffix, 1.0)), size / CHUNK_FILL


def is_base_load(head):
    """A session that loaded a base (file by file or bundled), as opposed to one that works."""
    return "You are being loaded as the base" in head or BOOTSTRAP_PREFIX in head


def expand(pattern):
    p = os.path.expanduser(pattern)
    p = p if os.path.isabs(p) else os.path.join(PROJECT, p)
    return sorted(q for q in glob.glob(p) if os.path.isfile(q))


def implementer_sessions():
    out = []
    for f in sorted(glob.glob(TRANSCRIPTS + "/*.jsonl"), key=os.path.getmtime, reverse=True):
        head = open(f, errors="ignore").read(600_000)
        if '"model":"claude-opus' in head and "connectivity probe" not in head:
            if is_base_load(head) and "You are impl-" not in open(f, errors="ignore").read():
                continue  # a base itself, not a fork of one
            out.append(f)
        if len(out) == SESSIONS:
            break
    return out


def measure(files):
    use = {}
    for f in files:
        calls = {}
        own = not is_base_load(open(f, errors="ignore").read(600_000))
        for line in open(f, errors="ignore"):
            if not own:  # a fork: everything before its own first message is a copy of the base's load
                own = '"You are impl-' in line or "You are impl-" in line[:400]
                continue
            if '"tool_use"' not in line and '"tool_result"' not in line:
                continue
            try:
                d = json.loads(line)
            except ValueError:
                continue
            content = (d.get("message") or {}).get("content")
            if not isinstance(content, list):
                continue
            for c in content:
                if not isinstance(c, dict):
                    continue
                if c.get("type") == "tool_use":
                    i = c.get("input") or {}
                    text = (i.get("command") or "") + " " + (i.get("file_path") or "")
                    found = set()
                    for n in set(re.findall(r"(?<![\w/.-])((?:theories/|tools/)?[A-Za-z_][\w.-]*\.(?:thy|md|txt|py))\b", text)):
                        b = os.path.basename(n)
                        for cand in (n, "theories/" + b, "tools/" + b, b):
                            if os.path.isfile(os.path.join(PROJECT, cand)):
                                found.add(cand)
                                break
                    calls[c.get("id")] = found
                elif c.get("type") == "tool_result":
                    found = calls.get(c.get("tool_use_id")) or ()
                    body = c.get("content")
                    n = len(body if isinstance(body, str) else json.dumps(body))
                    for p in found:
                        u = use.setdefault(p, [set(), 0])
                        u[0].add(f)
                        u[1] += n // len(found)
    return use


def theory_names():
    """Every actual theory file, in ROOT order; names absent from ROOT come last.

    THEORY_MAP can lag new files. The catalogue describes source existence, not
    acceptance or proof status. ROOT's order is recorded without claiming it is
    a topological order of the imports.
    """
    available = {os.path.basename(p)[:-4] for p in glob.glob(os.path.join(PROJECT, "theories", "*.thy"))}
    names, seen = [], set()
    for line in open(os.path.join(PROJECT, "ROOT")):
        match = re.fullmatch(r'\s+"?([A-Za-z_0-9]+)"?(?:\s+\(global\))?(?:\s+\[[^\]]*\])?\s*', line)
        if match and match[1] in available and match[1] not in seen:
            names.append(match[1])
            seen.add(match[1])
    extra = sorted(available - seen)
    held = os.path.join(HERE, "state", "held")
    os.makedirs(held, exist_ok=True)
    out = ["# Every theory source file, by name, in ROOT order (grep THEORY_MAP.md or the source for its content).",
           "# A listed name records source existence, not acceptance or proof status.", ""]
    out += [" ".join(names[i:i + 8]) for i in range(0, len(names), 8)]
    if extra:
        out += ["", "# Additional source files not listed in ROOT, alphabetically:"]
        out += [" ".join(extra[i:i + 8]) for i in range(0, len(extra), 8)]
    open(os.path.join(held, "theory-names.md"), "w").write("\n".join(out) + "\n")
    return len(names) + len(extra)


def main():
    count = theory_names()
    print(f"theory-names.md: {count} names")
    if "--refresh-index" in sys.argv:
        return
    path = os.path.join(HERE, "base-load.txt")
    text = open(path).read()
    at = {k: re.search(rf"^# {k}\b", text, re.M).start() for k in ("pinned", "every", "measured", "optional")}  # the first pinned tier
    head = text[: at["pinned"]]
    pinned_block = text[at["pinned"]: at["every"]]
    optional_block = text[at["optional"]:]
    pinned = []
    for ln in pinned_block.splitlines()[1:]:
        ln = ln.split("  #")[0].strip()
        if ln and not ln.startswith("#"):
            pinned += expand(ln)
    pinned_tokens = pinned_calls = 0
    for p in pinned:
        t, c = tokens(p)
        pinned_tokens += t
        pinned_calls += c
    # every founding theory that is not pinned at full statements is held as definitions: nothing is discarded
    pinned_names = {os.path.basename(p)[:-4] for p in pinned if p.endswith(".thy")}
    rest = [n for n in founding_theories() if n not in pinned_names]
    rest_tokens = rest_calls = 0
    for n in rest:
        t, c = tokens(os.path.join(PROJECT, "theories", n + ".thy"), "definitions")
        rest_tokens += t
        rest_calls += c
    every_block = ["# every other founding theory, as definitions (generated: commentary, definitions, locales and the names of "
                   "what is proved; one per notion of the library's vocabulary, in import order)"] + [f"theories/{n}.thy" for n in rest]
    pinned_tokens += rest_tokens
    pinned_calls += rest_calls
    pinned += [os.path.join(PROJECT, "theories", n + ".thy") for n in rest]
    sessions = implementer_sessions()
    use = measure(sessions)
    held = {os.path.relpath(p, PROJECT) for p in pinned}
    cands = []
    for rel, (ss, pulled) in use.items():
        full = os.path.join(PROJECT, rel)
        if rel in held or rel in NEVER or pulled < MIN_SHARE * os.path.getsize(full):
            continue
        t, c = tokens(full)
        density = (pulled / len(sessions)) / max(1, os.path.getsize(full))
        cands.append((len(ss), density, rel, t, c, pulled))
    cands.sort(key=lambda x: (x[0] < MIN_SESSIONS, -x[1]))  # repeated use first, then single-session use
    budget = int(TARGET - SESSION_TOKENS - FIXED_TOKENS - pinned_tokens - CALL_TOKENS * pinned_calls)
    chosen, left_out, spent = [], [], 0
    for s, dens, rel, t, c, pulled in cands:
        cost = t + int(CALL_TOKENS * c)
        if spent + cost <= budget:
            chosen.append((s, dens, rel, t, pulled))
            spent += cost
        else:
            left_out.append((s, rel, t))
    block = [f"# measured (generated {time.strftime('%Y-%m-%d')} from {len(sessions)} implementer sessions; "
             f"sessions that consulted it, K chars pulled, about K tokens)"]
    for s, dens, rel, t, pulled in chosen:
        block.append(f"{rel}  # {s} sessions, {pulled // 1000}K pulled, ~{t // 1000 or 1}K tokens")
    total = int(SESSION_TOKENS + FIXED_TOKENS + pinned_tokens + CALL_TOKENS * pinned_calls + spent)
    print(f"target {TARGET // 1000}K: fresh session {SESSION_TOKENS // 1000}K + fixed {FIXED_TOKENS // 1000}K + "
          f"pinned and founding {len(pinned)} files {pinned_tokens // 1000}K (of which {len(rest)} founding theories as definitions, {rest_tokens // 1000}K) + measured {len(chosen)} files {spent // 1000}K "
          f"= about {total // 1000}K loaded, {(1_000_000 - total) // 1000}K of room")
    kinds = {}
    for s, dens, rel, t, pulled in chosen:
        k = os.path.splitext(rel)[1]
        kinds[k] = (kinds.get(k, (0, 0))[0] + 1, kinds.get(k, (0, 0))[1] + t)
    print("measured tier by kind:", {k: f"{n} files, {t // 1000}K" for k, (n, t) in kinds.items()})
    print(f"qualified but over budget: {len(left_out)} files, {sum(t for _, _, t in left_out) // 1000}K tokens; "
          f"largest: {[(r, t // 1000) for _, r, t in sorted(left_out, key=lambda x: -x[2])[:4]]}")
    if "--dry-run" not in sys.argv:
        open(path, "w").write(head + pinned_block + "\n".join(every_block) + "\n" + "\n".join(block) + "\n" + optional_block)
        print("base-load.txt rewritten")


if __name__ == "__main__":
    main()
