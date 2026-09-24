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
  manifest.py stable-share [WHO]  four numbers: the stable part's moved share, those tokens, its tokens, what it holds unlisted
  manifest.py snapshot-delta WHO PATH  every held file's digest, both parts, marked as a delta's (base.sh WHO delta)

A loaded context is append-only, so a held file is a snapshot; `changed` is
how its holder learns which of its copies no longer match the repository.

A list may be split in two by a `# === layer ===` line (notes/bases-design.md section 8): above it the stable
reference, which the owner rebuilds rarely, and below it the frontier layer, which a fork of the sealed stable base
loads and which the harness refreshes on its own. ORCH_BASE_PART picks one part (`stable` or `layer`); unset, every
command is about the whole, which is what a fork of the layer actually holds — so `changed` reads both snapshots and
says what changed in either.
"""
import contextlib
import difflib
import glob
import hashlib
import json
import os
import re
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


LAYER_LINE = re.compile(r"^#\s*=== layer(?:\s+([a-z][a-z0-9_-]*))? ===(?:\s.*)?$")


def layer_names(path=None):
    """Named material boundaries in their declared order; the legacy unnamed boundary is `layer`."""
    return [m.group(1) or 'layer' for line in open(path or load_list()) if (m:=LAYER_LINE.match(line.strip()))]


def has_layer(path=None):
    return bool(layer_names(path))


def list_entries(text, project=None, virtual=(), strict=False):
    """Load entries with their own part, depth and purpose, without mutating files or global environment.

    A later, deeper projection explicitly supersedes an earlier shallower one. It does not erase the tokens already
    held below it. Duplicate entries at the same or a shallower depth add nothing and are omitted.
    """
    project = PROJECT if project is None else project
    tier, where, out, seen = '', 'stable', [], {}
    order = {'signatures':0,'definitions':1,'statements':2}
    for raw in text.splitlines():
        line = raw.split('  #')[0].strip()
        if line.startswith('#'):
            mark=LAYER_LINE.match(line)
            if mark:
                where=mark.group(1) or 'layer'
            elif not line.startswith('# ==='):
                tier=line.lstrip('# ').strip()
            continue
        if not line or tier.startswith('optional'):
            continue
        level=next((v for v in ('signatures','definitions') if f'as {v}' in tier),'statements')
        purpose=re.search(r'purpose=(reading|steering|both)\b',tier)
        pattern=os.path.expanduser(line)
        if line.startswith('.claude/orchestration/state/held/'):
            pattern=os.path.join(os.environ.get('ORCH_HELD_DIR') or os.path.join(project,'.claude','orchestration','state','held'),os.path.basename(line))
        if not os.path.isabs(pattern):
            pattern=os.path.join(project,pattern)
        paths=sorted(set(glob.glob(pattern)) | ({pattern} if pattern in virtual else set()))
        if not paths and strict and not glob.has_magic(pattern):
            raise FileNotFoundError('Required base source is missing: '+pattern)
        for path in paths:
            if not os.path.isfile(path) and path not in virtual: continue
            previous=seen.get(path)
            if previous and order[level] <= order[previous]: continue
            out.append(dict(tier=tier,path=path,level=level,part=where,
                            purpose=purpose.group(1) if purpose else 'both',deepens=previous))
            seen[path]=level
    return out


def held_files(part=None):
    """Held files of a material part; `layer` also names the aggregate above the stable reference."""
    part=PART if part is None else part
    out=[]
    for e in list_entries(open(load_list()).read()):
        if part and not (e['part']==part or (part=='layer' and e['part']!='stable')): continue
        LEVELS[e['path']]=e['level']; PARTS[e['path']]=e['part']
        out.append((e['tier'],e['path']))
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
INDEXES = ("theory-names.md", "decisions-index.md", "theory-map-index.md", "tool-index.md", "plan-index.md") + tuple(
    f"{name}-{who}.md" for name in ("theory-map-index", "tool-index") for who in LISTS)  # each base's own


def loaded_texts(who, part):
    """{path: the held text a part of the base loaded} — the stable reference's or the frontier layer's — restored from
    its pack (base_pack.sources_from_pack), or {} when the pack is gone or unreadable."""
    try:
        rec = json.load(open(os.path.join(STATE, f"{who}-{'base' if part == 'stable' else 'layer'}.json")))
        import base_pack
        from pathlib import Path
        chain = rec.get('parts')
        packs = [p['pack'] for p in chain if p.get('pack') and p.get('part') != 'stable'] if chain and part == 'layer' else [rec['pack']]
        return {s["path"]: s["text"] for pack in packs for s in base_pack.sources_from_pack(Path(pack))[0]}
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


def changed_units(path, old, now):
    """A held file's change from `old` to `now`, as the delta and its increments give it: its added or changed units in
    their new form, and those removed, by their keys (a command by its name, anything unnamed by its first line)."""
    was, kept = units(path, old), units(path, now)
    shown = [body for key, body in kept.items() if was.get(key) != body]
    removed = [key for key in was if key not in kept]
    text = "\n\n".join(shown) if os.path.splitext(path)[1] in (".thy", ".md") else "\n".join(shown)
    if removed:
        first = [k.splitlines()[0].strip() if k.strip() else k for k in removed]
        text += ("\n\n" if text else "") + "removed: " + "; ".join(k if len(k) <= 80 else k[:77] + "…" for k in first)
    return text


def delta_entries(who):
    """[(path, part, kind, text, tokens)] of every held file whose held text differs from what its part loaded: `new`
    (the part did not load it: whole), `gone` (loaded, no longer held: named), `changed` (its parts added or changed, in
    their new form, and those removed, by their keys), `whole` (changed, its part's pack gone: whole)."""
    loaded = {"stable": loaded_texts(who, "stable"), "layer": loaded_texts(who, "layer")}
    out, held = [], set()
    for path in dict.fromkeys(p for _, p in held_files("")):
        part = 'stable' if PARTS.get(path, "stable") == 'stable' else 'layer'
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
        text = changed_units(path, old, now)
        out.append((path, part, "changed", text, int(len(text) / ratio)))
    for part in ("stable", "layer"):
        for path in loaded[part]:
            if path not in held:
                out.append((path, part, "gone", "", 0))
    return out


LAST_DELTA = {}  # who -> the entries delta_text read last, which delta_parts divides by part


def delta_parts(who, entries=None):
    """{part: tokens} of the delta's text (or an increment's, `entries`) by the named part holding each change — the
    stable part's too: each part's changes are carried until carrying them has cost what loading that part and those
    over it again costs (the watchdog's refresh_plan), so the cost of carrying is counted by part."""
    if entries is None:
        entries = LAST_DELTA.get(who)
    if entries is None:
        entries = delta_entries(who)
    out = {}
    for path, _, _, _, tokens, *_ in entries:
        if tokens:
            name = PARTS.get(path, "stable")
            out[name] = out.get(name, 0) + tokens
    return out


def delta_text(who):
    """(the delta's text, the tokens it holds of the parts over the stable part, of the stable part); ("", 0, 0) when
    nothing has changed."""
    entries = LAST_DELTA[who] = delta_entries(who)
    gone_packs = [part for part in ("stable", "layer") if not loaded_texts(who, part)]
    if not entries:
        return "", 0, 0

    def sealed(part):
        try:
            return json.load(open(os.path.join(STATE, f"{who}-{'base' if part == 'stable' else 'layer'}.json")))["sealed"]
        except (OSError, ValueError, KeyError):
            return "an unrecorded time"
    lines = [f"What you hold has changed since it loaded: the stable part at {sealed('stable')}, the parts over it "
             f"at {sealed('layer')}. As of main {main_head()}, the text below is the current form of each part it "
             "names, and it supersedes what you hold of those parts; everything else you hold is current. Nothing here "
             "asks for work."]
    if gone_packs:
        lines.append(f"(The {' and '.join(gone_packs)} part's load cannot be read back, so its changes are not here.)")
    render_entries(lines, entries)
    return ("\n".join(lines) + "\n", sum(e[4] for e in entries if e[1] == "layer"),
            sum(e[4] for e in entries if e[1] == "stable"))


def main_head():
    import subprocess
    return subprocess.run(["git", "-C", PROJECT, "log", "-1", "--format=%h %cd", "--date=format:%Y-%m-%d %H:%M"],
                          capture_output=True, text=True).stdout.strip() or "(no commit)"


def render_entries(lines, entries):
    """Each changed file of a delta or an increment, the stable part's first: named with where it is held, and its
    units in their current form, whole when new, named when gone."""
    for part in ("stable", "layer"):
        for path, p, kind, text, *_ in entries:
            if p != part:
                continue
            name = short(path) if path.startswith(PROJECT + os.sep) else path
            where = "the stable part" if part == "stable" else "the parts over it"
            if kind == "gone":
                lines.append(f"\n== {name} ({where}): no longer held")
            elif kind == "new":
                lines.append(f"\n== {name} ({where}): new to what you hold, whole\n{text}")
            else:
                lines.append(f"\n== {name} ({where}): its parts changed or added, in their current form\n{text}")


# ---------------------------------------------------------------- the delta's increments (the owner, 2026-09-23:
# "should the delta not be layered"): the standing delta is a chain — its consolidated message over the parts, then
# increments each forking the one before with only what changed since. A build writes its own increment alone, where a
# delta built again wrote every earlier change again; the chain is consolidated, one message written anew over the
# parts, when what its superseded forms have cost the forks reaches what that costs (watchdog.deltas).

def stack_held(who):
    """{path: the held text the standing delta's messages give a file they changed, None for one they said is gone} —
    what an increment is measured against — or {} when none is recorded for the delta standing now."""
    try:
        held = json.load(open(os.path.join(STATE, f"{who}-delta-held.json")))
        delta = json.load(open(os.path.join(STATE, f"{who}-delta.json")))
        layer = json.load(open(os.path.join(STATE, f"{who}-layer.json"))).get("sessionId")
    except (OSError, ValueError):
        return {}
    # the chain's top is its last text (`top`); a record from before the texts named its top by its session
    if held.get("top") != (delta.get("top") or delta.get("sessionId")) or delta.get("layer") != layer:
        return {}  # another top, or a chain over a layer refreshed since: orphaned, the next text is whole
    return held.get("files") or {}


def increment_entries(who, stacked=None):
    """[(path, part, kind, text, tokens, superseded, now)] of what changed since the standing delta's messages took each
    file in: each held file's units against the text those messages give it (the last that named it), or its part's
    load; `superseded` the tokens of the messages' own earlier forms of units now changed again, which stay held,
    superseded, until the chain is consolidated; `now` the held text now, which the next increment is measured from."""
    loaded = {"stable": loaded_texts(who, "stable"), "layer": loaded_texts(who, "layer")}
    stacked, out, held = (stack_held(who) if stacked is None else stacked), [], set()
    for path in dict.fromkeys(p for _, p in held_files("")):
        part = 'stable' if PARTS.get(path, "stable") == 'stable' else 'layer'
        held.add(path)
        if not loaded[part]:
            continue
        now = held_text(path, level_of(path))[0]
        ratio = RATIO.get(os.path.splitext(path)[1], 2.6)
        base = stacked[path] if path in stacked else loaded[part].get(path)
        if base is None:  # new to what the parts loaded, or back after the messages said it was gone
            out.append((path, part, "new", now, int(len(now) / ratio), 0, now))
            continue
        if base == now:
            continue
        text = changed_units(path, base, now)
        superseded = 0
        if path in stacked:
            was, kept, origin = units(path, base), units(path, now), units(path, loaded[part].get(path) or "")
            superseded = int(sum(len(body) for key, body in was.items()
                                 if kept.get(key) != body and origin.get(key) != body) / ratio)
        out.append((path, part, "changed", text, int(len(text) / ratio), superseded, now))
    for part in ("stable", "layer"):
        for path in loaded[part]:
            if path not in held and stacked.get(path, "") is not None:
                out.append((path, part, "gone", "", 0, 0, None))
    return out


LAST_INCREMENT = {}


def loaded_parts(who):
    """{part: {path: the held text that part loaded}} — the stable reference and each named part of the chain, read
    back from their packs; a part whose pack cannot be read is left out."""
    import base_pack
    from pathlib import Path
    out = {}
    try:
        stable = json.load(open(os.path.join(STATE, f"{who}-base.json")))
        out["stable"] = {s["path"]: s["text"] for s in base_pack.sources_from_pack(Path(stable["pack"]))[0]}
    except Exception:  # noqa: BLE001  a measure; it must not fail the delta's build
        pass
    try:
        chain = json.load(open(os.path.join(STATE, f"{who}-layer.json"))).get("parts") or []
    except (OSError, ValueError):
        chain = []
    for node in chain:
        if node.get("pack") and node.get("part") not in (None, "stable", "reasoning"):
            try:
                out[node["part"]] = {s["path"]: s["text"] for s in base_pack.sources_from_pack(Path(node["pack"]))[0]}
            except Exception:  # noqa: BLE001
                continue
    return out


def old_forms(who):
    """{part: tokens} of what each part loaded that is no longer what the base holds: the units of a held file changed
    or removed since its part loaded, and a file it loaded that is no longer held, whole. Once the delta holds the
    current forms (a message built now), every request of a fork carries these for nothing, and loading the part again
    is what ends it (watchdog.carried_parts: the arithmetic review of 2026-09-23 — a refresh does not end the carrying
    of a part's changes, whose current forms move from the delta into the part, only of its superseded old forms)."""
    now_held = {}
    for _, path in held_files(""):
        now_held.setdefault(path, None)
    out = {}
    for part, texts in loaded_parts(who).items():
        for path, old in texts.items():
            ratio = RATIO.get(os.path.splitext(path)[1], 2.6)
            if path not in now_held:
                n = len(old)
            else:
                now = held_text(path, level_of(path))[0]
                if now == old:
                    continue
                was, kept = units(path, old), units(path, now)
                n = sum(len(body) for key, body in was.items() if kept.get(key) != body)
            if n:
                out[part] = out.get(part, 0) + int(n / ratio)
    return out


def increment_text(who):
    """(the increment's text, the tokens it holds of the parts over the stable part, of the stable part, the tokens of
    earlier forms it supersedes); ("", 0, 0, 0) when nothing has changed since the delta's last message."""
    entries = LAST_INCREMENT[who] = increment_entries(who)
    if not entries:
        return "", 0, 0, 0
    lines = [f"What you hold has changed since the last message of this kind you hold. As of main {main_head()}, the "
             "text below is the current form of each part it names, and it supersedes what you hold of those parts — "
             "as they loaded or as an earlier message gave them; everything else you hold is current. Nothing here asks "
             "for work."]
    render_entries(lines, entries)
    return ("\n".join(lines) + "\n", sum(e[4] for e in entries if e[1] == "layer"),
            sum(e[4] for e in entries if e[1] == "stable"), sum(e[5] for e in entries))


def held_changes(who, node, names=()):
    """What changed in the files base `who` holds since a holder took them in, in their current form (v2.py read
    changes): the texts the chain's text `node` it holds to gives each file it changed (layer-<text id>-held.json,
    base_stack.cut), the parts' loads for the rest (`-` for a holder of the loads alone). `names` picks files as a stale
    line names them (a file's name without its extension, or the end of its path)."""
    stacked = {}
    if node and node != "-":
        try:
            stacked = json.load(open(os.path.join(STATE, f"layer-{node}-held.json"))).get("files") or {}
        except (OSError, ValueError):
            held = {}
            with contextlib.suppress(OSError, ValueError):
                held = json.load(open(os.path.join(STATE, f"{who}-delta-held.json")))
            stacked = (held.get("files") or {}) if held.get("top") == node else {}
    entries = increment_entries(who, stacked=stacked)
    if names:
        entries = [e for e in entries
                   if any(os.path.splitext(os.path.basename(e[0]))[0] == n or e[0].endswith(n) for n in names)]
    if not entries:
        return "(nothing " + ("of those " if names else "") + "you hold has changed since you took it in)"
    lines = [f"What changed in what you hold since you took it in, as of main {main_head()}: the text below is the "
             "current form of each part it names, and it supersedes what you hold of those parts; everything else you "
             "hold of these files is current."]
    render_entries(lines, entries)
    return "\n".join(lines)


def relative(path, root):
    return os.path.relpath(path, root) if path.startswith(root + os.sep) else path


def stable_share(who):
    """The stable reference's drift, counted as the layer's is (moved_tokens), for the stable reference drifts too, and
    more slowly: (the share of the tokens the list's stable part holds whose held text moved since the stable base
    loaded — a file it did not load counted whole —, those tokens, the part's tokens, the tokens the stable base holds
    of files the list no longer names: held for nothing until the owner loads it again), or None with no snapshot."""
    stable, path = held_files("stable"), os.path.join(STATE, f"{who}-manifest.json")
    if not stable or not os.path.exists(path):
        return None
    record = json.load(open(path))["files"]
    loaded = loaded_texts(who, "stable")
    total = sum(tokens(p) for _, p in stable) or 1
    moved = sum(moved_tokens(p, record, loaded) for _, p in stable)
    listed = {p for _, p in stable}
    unlisted = sum(int(len(text) / RATIO.get(os.path.splitext(p)[1], 2.6)) for p, text in loaded.items() if p not in listed)
    return moved / total, moved, total, unlisted


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
            json.dump({"layer_tokens": layer, "stable_tokens": stable, "tokens": layer + stable,
                       "parts": delta_parts(WHO), "old_forms": old_forms(WHO)},
                      open(sys.argv[sys.argv.index("--counts") + 1], "w"))
        if "--held" in sys.argv:  # what the consolidated message gives each file it names: its increments start there
            files = {p: (held_text(p, level_of(p))[0] if kind != "gone" else None) for p, _, kind, *_ in LAST_DELTA[WHO]}
            json.dump({"files": files}, open(sys.argv[sys.argv.index("--held") + 1], "w"))
        return 0
    if mode == "delta-increment":  # an increment's text (base.sh WHO delta --increment), its counts and what it holds
        text, layer, stable, superseded = increment_text(WHO)
        sys.stdout.write(text)
        entries = LAST_INCREMENT[WHO]
        if "--counts" in sys.argv:
            json.dump({"layer_tokens": layer, "stable_tokens": stable, "tokens": layer + stable, "superseded": superseded,
                       "parts": delta_parts(WHO, entries), "old_forms": old_forms(WHO)},
                      open(sys.argv[sys.argv.index("--counts") + 1], "w"))
        if "--held" in sys.argv:
            files = dict(stack_held(WHO))
            files.update({e[0]: e[6] for e in entries})
            json.dump({"files": files}, open(sys.argv[sys.argv.index("--held") + 1], "w"))
        return 0
    if mode == "pending":  # the tokens a delta message built now would hold: an increment's, or a whole delta's
        entries = increment_entries(WHO) if stack_held(WHO) else delta_entries(WHO)
        print(sum(e[4] for e in entries))
        return 0

    if mode == "held-changes":  # what changed since a holder took the files in, in their current form (v2.py read changes)
        print(held_changes(WHO, sys.argv[3], sys.argv[4:]))
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
    if mode == "stable-listed":  # whether the stable base recorded loaded the files the list's stable part names now
        # A layer is built over the recorded stable base when its entry is warm; once the list's stable part names other
        # files (the founding tier chosen by use, 2026-09-22), that base would hold the old reference under a layer
        # chosen for the new one — about 665K on high against the 530K target. Its contents moving is the delta's.
        listed = {p for _, p in held_files("stable")}
        try:
            loaded = set(json.load(open(os.path.join(STATE, f"{WHO}-manifest.json")))["files"])
        except (OSError, ValueError, KeyError):
            print(f"no snapshot of the {WHO} stable base")
            return 1
        if listed == loaded:
            return 0
        print(f"the list's stable part names {len(listed - loaded)} file(s) the {WHO} stable base did not load and "
              f"leaves out {len(loaded - listed)} it did")
        return 1
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
    if mode == "stable-share":  # the same count for the stable reference (stable_share)
        got = stable_share(WHO)
        print(f"{got[0]:.3f} {got[1]} {got[2]} {got[3]}" if got else "0 0 0 0")
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
