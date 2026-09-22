#!/usr/bin/env python3
"""What a base holds (its load list), and which of it has gone stale since it was loaded.

  manifest.py snapshot [WHO]   record a digest of every held file (run once, after that role's load)
  manifest.py changed [WHO] [--since-layer SID]   one line naming the held files that differ from that role's
                               snapshot; --since-layer measures against the layer that session actually forked
  manifest.py size [WHO]       one line: files, characters, estimated tokens
  manifest.py stale-share [WHO]  one number: the share of the layer's tokens whose files have changed since it loaded
  manifest.py delta [WHO]      what the base holds that has changed since each part loaded, in its new form (the
                               delta session's text: notes/plan-delta-layer.md)
  manifest.py delta-share [WHO]  three numbers: the delta's share of the layer's tokens, its stable tokens, its tokens
  manifest.py snapshot-delta WHO PATH  every held file's digest, both parts, marked as a delta's (base.sh WHO delta)

A loaded context is append-only, so a held file is a snapshot; `changed` is
how its holder learns which of its copies no longer match the repository.

A list may be split in two by a `# === layer ===` line (notes/bases-design.md section 8): above it the stable
reference, which the owner rebuilds rarely, and below it the frontier layer, which a fork of the sealed stable base
loads and which the harness refreshes on its own. ORCH_BASE_PART picks one part (`stable` or `layer`); unset, every
command is about the whole, which is what a fork of the layer actually holds — so `changed` reads both snapshots and
says what changed in either.
"""
import difflib
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
ONE = os.environ.get("ORCH_PROJECT") or os.path.dirname(os.path.dirname(HERE))  # the one tree, where loads are recorded
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


# The generated indexes (select_base_load.refresh_indexes): lookup tables that gain a line with almost every commit —
# a theory's name, a decision's heading, a map row. A fork looks a name up in them, it does not read them again whole,
# so what of them has changed is the lines that did, not the file (bases-design.md §1, Staleness, is about a file a
# fork reads again whole). Counted whole, the two in the max layer, 34.5K of its 148K tokens, put it past the refresh
# line after nearly every landing: it was refreshed at 22:24 and again at 22:39 on 2026-09-21, and each refresh of it
# is followed by a new knowledge base.
INDEXES = ("theory-names.md", "decisions-index.md", "theory-map-index.md")


def loaded_texts(who, part):
    """{path: the held text a part of the base loaded} — the stable reference's or the frontier layer's — restored from
    its pack (base_pack.sources_from_pack), or {} when the pack is gone or unreadable."""
    try:
        pack = json.load(open(os.path.join(STATE, f"{who}-{'base' if part == 'stable' else 'layer'}.json")))["pack"]
        import base_pack
        from pathlib import Path
        return {s["path"]: s["text"] for s in base_pack.sources_from_pack(Path(pack))[0]}
    except Exception:  # noqa: BLE001  the measure falls back; it must not fail the refresh rule
        return {}


def layer_texts(who):
    """{path: the text the layer loaded}, or {} — then the files' digests decide, as before."""
    return loaded_texts(who, "layer")


def moved_tokens(path, recorded, loaded):
    """The tokens of a layer file that have moved since the layer loaded: none when what the layer holds of it is the
    same (a proof changed under statements held unchanged), the lines that changed for a generated index, and the whole
    file otherwise — a fork that needs it reads it again whole."""
    whole = tokens(path)
    if path not in recorded:
        return whole
    old = loaded.get(path)
    if old is None:
        return whole if digest(path) != recorded[path] else 0
    now = held_text(path, level_of(path))[0]
    if now == old:
        return 0
    if os.path.basename(path) not in INDEXES:
        return whole
    # by word, not by line: the theory names are wrapped many to a line, and one name put in re-wraps every line after
    # it — the max layer read 34% stale at 07:43 on 2026-09-22 for one new theory, its whole names index counted
    a, b = old.split(), now.split()
    changed = sum(sum(len(x.encode()) + 1 for x in a[i1:i2]) + sum(len(x.encode()) + 1 for x in b[j1:j2])
                  for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes()
                  if op != "equal")
    return min(whole, int(changed / RATIO.get(os.path.splitext(path)[1], 2.6)))


# ---------------------------------------------------------------- the delta (notes/plan-delta-layer.md)
# What a base holds that has changed since the part holding it loaded, in its new form: a fork of the delta session,
# which holds this text as its one message, reads it from cache with the rest, where a fork of the layer was told file
# names and read files again whole — and the layer's refresh counted every changed file whole (the high layer's of
# 19:25 on 2026-09-22: 23.4% by that count, 1.4% by the lines that changed).

PROSE = {"text", "section", "subsection", "subsubsection", "paragraph", "chapter", "txt", "text_raw", "end"}


def units(path, text):
    """{key: text} of the parts a held text is compared by, in order: a theory's commands (by command and name, a
    command with no name by its text), a Markdown document's sections (by heading), any other file's lines."""
    import digest
    base, ext = os.path.basename(path), os.path.splitext(path)[1]
    parts = []
    if ext == ".thy" and base not in INDEXES:
        for cmd, lines in digest.chunks(text):
            body = "\n".join(lines).rstrip()
            named = digest.NAMED.match(lines[0]) if cmd and cmd not in PROSE else None
            parts.append((f"{cmd} {named.group(1)}" if named else body, body))
    elif ext == ".md" and base not in INDEXES:
        section = []
        for line in text.splitlines():
            if line.startswith("#") and section:
                parts.append((section[0], "\n".join(section).rstrip()))
                section = []
            section.append(line)
        if section:
            parts.append((section[0], "\n".join(section).rstrip()))
    else:
        parts = [(line, line) for line in text.splitlines() if line.strip()]
    out = {}
    for key, body in parts:
        k, n = key, 1
        while k in out:
            n += 1
            k = f"{key} #{n}"
        out[k] = body
    return out


def delta_entries(who):
    """[(path, part, kind, text, tokens)] of every held file whose held text differs from what its part loaded: `new`
    (the part did not load it: whole), `gone` (loaded, no longer held: named), `changed` (its parts added or changed, in
    their new form, and those removed, by their keys), `whole` (changed, its part's pack gone: whole)."""
    loaded = {"stable": loaded_texts(who, "stable"), "layer": loaded_texts(who, "layer")}
    out, held = [], set()
    for _, path in held_files(""):
        part = PARTS.get(path, "stable")
        held.add(path)
        now = held_text(path, level_of(path))[0]
        ratio = RATIO.get(os.path.splitext(path)[1], 2.6)
        if not loaded[part]:
            continue  # nothing to compare with: its part's pack is gone (said once, in the header)
        old = loaded[part].get(path)
        if old is None:
            out.append((path, part, "new", now, int(len(now) / ratio)))
            continue
        if old == now:
            continue
        was, kept = units(path, old), units(path, now)
        shown = [body for key, body in kept.items() if was.get(key) != body]
        removed = [key for key in was if key not in kept]
        text = "\n\n".join(shown) if os.path.splitext(path)[1] in (".thy", ".md") else "\n".join(shown)
        if removed:  # by their keys: a command by its name, anything unnamed by its first line
            first = [k.splitlines()[0].strip() if k.strip() else k for k in removed]
            text += ("\n\n" if text else "") + "removed: " + "; ".join(
                k if len(k) <= 80 else k[:77] + "…" for k in first)
        out.append((path, part, "changed", text, int(len(text) / ratio)))
    for part in ("stable", "layer"):
        for path in loaded[part]:
            if path not in held:
                out.append((path, part, "gone", "", 0))
    return out


def delta_text(who):
    """(the delta's text, the tokens it holds of the frontier layer, of the stable reference); ("", 0, 0) when nothing
    has changed."""
    entries = delta_entries(who)
    gone_packs = [part for part in ("stable", "layer") if not loaded_texts(who, part)]
    if not entries:
        return "", 0, 0

    def sealed(part):
        try:
            return json.load(open(os.path.join(STATE, f"{who}-{'base' if part == 'stable' else 'layer'}.json")))["sealed"]
        except (OSError, ValueError, KeyError):
            return "an unrecorded time"
    import subprocess
    head = subprocess.run(["git", "-C", PROJECT, "log", "-1", "--format=%h %cd", "--date=format:%Y-%m-%d %H:%M"],
                          capture_output=True, text=True).stdout.strip() or "(no commit)"
    lines = [f"What you hold has changed since it loaded: the stable reference at {sealed('stable')}, the working "
             f"frontier at {sealed('layer')}. As of main {head}, the text below is the current form of each part it "
             "names, and it supersedes what you hold of those parts; everything else you hold is current. Nothing here "
             "asks for work."]
    if gone_packs:
        lines.append(f"(The {' and '.join(gone_packs)} part's load cannot be read back, so its changes are not here.)")
    for part in ("stable", "layer"):
        for path, p, kind, text, _ in entries:
            if p != part:
                continue
            name = short(path) if path.startswith(PROJECT + os.sep) else path
            where = "the stable reference" if part == "stable" else "the working frontier"
            if kind == "gone":
                lines.append(f"\n== {name} ({where}): no longer held")
            elif kind == "new":
                lines.append(f"\n== {name} ({where}): new to what you hold, whole\n{text}")
            else:
                lines.append(f"\n== {name} ({where}): its parts changed or added, in their current form\n{text}")
    return ("\n".join(lines) + "\n", sum(t for _, p, _, _, t in entries if p == "layer"),
            sum(t for _, p, _, _, t in entries if p == "stable"))


def relative(path, root):
    return os.path.relpath(path, root) if path.startswith(root + os.sep) else path


def changed_since(recorded, now):
    """(the recorded files that differ now, the files held now that were not recorded), each by its path relative to
    its own tree: a load is recorded in the one tree, and a session in a tree of its own holds the same files under
    that tree. Compared by their absolute paths, every file of a tree session's load read as changed and again as new —
    review-79 was told 664 were stale since the xhigh load, of 362 it holds (2026-09-21)."""
    was = {relative(p, ONE): h for p, h in recorded.items()}
    held = {relative(p, PROJECT): h for p, h in now.items()}
    return [p for p, h in was.items() if held.get(p) != h], [p for p in held if p not in was]


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
    if mode == "delta":  # the delta's text (base.sh WHO delta); --counts FILE writes its tokens beside it
        text, layer, stable = delta_text(WHO)
        sys.stdout.write(text)
        if "--counts" in sys.argv:
            json.dump({"layer_tokens": layer, "stable_tokens": stable, "tokens": layer + stable},
                      open(sys.argv[sys.argv.index("--counts") + 1], "w"))
        return 0
    if mode == "snapshot-delta":  # every held file's digest, both parts, as a delta session holds them (base.sh)
        record = {"taken": time.strftime("%Y-%m-%dT%H:%M:%S"), "delta": True,
                  "files": {p: digest(p) for _, p in held_files("")}}
        json.dump(record, open(sys.argv[3], "w"), indent=0)
        print(f"snapshot of {len(record['files'])} held files, as the {WHO} delta holds them, taken {record['taken']}")
        return 0
    if mode == "delta-share":  # what the watchdog reads: the delta's share of the layer, its stable tokens, its whole
        text, layer, stable = delta_text(WHO)
        total = sum(tokens(p) for _, p in held_files("layer")) or 1
        print(f"{layer / total:.3f} {stable} {layer + stable}")
        return 0
    if mode == "stale-share":  # what the refresh rule reads: the share of the layer's tokens whose files have changed
        layer = held_files("layer")
        if not layer or not os.path.exists(LAYER_MANIFEST):
            print("0")
            return 0
        record = json.load(open(LAYER_MANIFEST))["files"]
        total = sum(tokens(p) for _, p in layer) or 1
        loaded = layer_texts(WHO)
        moved = sum(moved_tokens(p, record, loaded) for _, p in layer)
        print(f"{moved / total:.3f}")
        return 0
    # A fork holds both parts, so both snapshots are read: the stable one and, when there is a layer, its own —
    # the layer the reader actually forked (--since-layer SID), which after a refresh is not the one standing now.
    layer_snapshot = LAYER_MANIFEST
    if "--since-layer" in sys.argv:
        sid = sys.argv[sys.argv.index("--since-layer") + 1]
        held = os.path.join(STATE, f"layer-{sid}-manifest.json")
        layer_snapshot = held if os.path.exists(held) else LAYER_MANIFEST
    records = [(part, m) for part, m in (("stable", MANIFEST), ("layer", layer_snapshot)) if os.path.exists(m)] \
        if not PART else ([(PART, MANIFEST)] if os.path.exists(MANIFEST) else [])
    # a delta's snapshot holds both parts as they stood when it was built (base.sh WHO delta): a fork of it is told only
    # what changed after it, not the stable part's changes the delta already holds
    if not PART and os.path.exists(layer_snapshot):
        try:
            if json.load(open(layer_snapshot)).get("delta"):
                records = [("delta", layer_snapshot)]
        except (OSError, ValueError):
            pass
    if not records:
        print(f"no snapshot: the {WHO} load has not been recorded")
        return 1
    print(stale_line(records, files))
    return 0


def stale_line(records, files):
    """What a session holds that has changed, said by the load that brought it in — the stable reference (rebuilt
    rarely, by the owner) and the frontier layer (refreshed by the harness) — each with its own time, and apart from
    them what differs only in the session's own tree: its own work, or files main has changed since its tree was made.
    One line under the older load's time called the whole list stale since then, and task 145's session, its tree made
    before #144's tools landed, was told the tools a layer loaded eight minutes before were stale since 02:00:38 (the
    owner, 2026-09-22 15:00: "why was this said if the layer was updated?")."""
    # a held file outside the tree (the harness's generated indexes, under the one tree's state/) is the one tree's
    held = {relative(p, PROJECT if p.startswith(PROJECT + os.sep) else ONE): digest(p) for _, p in files}
    main = {rel: digest(os.path.join(ONE, rel)) for rel in held} if PROJECT != ONE else None
    name = lambda rel: os.path.splitext(os.path.basename(rel))[0]
    shown = lambda names: ", ".join(names[:40]) + (f", … {len(names) - 40} more" if len(names) > 40 else "") or "none"
    parts, own, recorded, earlier = [], [], set(), {}
    for part, path in records:
        record = json.load(open(path))
        was = {relative(p, ONE): h for p, h in record["files"].items()}
        # a layer's record, kept for the sessions that fork it, holds the stable files it stands on too (base.sh): a
        # file an earlier record holds alike is that load's, and said there alone — it was said under both, the owner
        # asking why twice (2026-09-22 15:30)
        was = {rel: h for rel, h in was.items() if earlier.get(rel) != h}
        earlier.update(was)
        recorded |= set(was)
        changed = []
        for rel, h in was.items():
            now = held.get(rel)
            if now is None:  # not where the session works — the harness's generated indexes are the one tree's alone
                one = os.path.join(ONE, rel)
                if os.path.isfile(one) and digest(one) == h:
                    continue
                changed.append(name(rel))
                continue
            if now == h:
                continue
            if main is not None and main.get(rel) == h:
                own.append(name(rel))  # main still holds what was loaded: the difference is the tree's
            else:
                changed.append(name(rel))
        parts.append(f"since the {WHO} {part} load of {record['taken']} ({len(changed)}): {shown(changed)}")
    new = ["+" + name(rel) for rel in held if rel not in recorded]
    line = "; ".join(parts) + (f"; held now and not loaded ({len(new)}): {shown(new)}" if new else "")
    if own:
        line += (f"; differing in your own tree alone ({len(own)}: the task's work, or files main has changed since "
                 f"the tree was made — the task's session brings main in with `v2.py bring-main`): {shown(own)}")
    return line


if __name__ == "__main__":
    sys.exit(main())
