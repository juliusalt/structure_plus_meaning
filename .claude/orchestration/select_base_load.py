#!/usr/bin/env python3
"""Regenerate the measured tier of a base's load list (manifest.load_list) so that it lands on the target size.

The list has three parts. The `# pinned…` tiers are kept as written and chosen deliberately, to set the
implementer's direction: the owner's words, the operating rules, the plan, the reasoning inventory, the names
of all theories, and the founding theories of the library's own ideas. `# measured` is generated here: the
frontier and the tools recent implementers actually worked in. `# optional` is kept as written, never loaded.
This script also regenerates state/held/theory-names.md from the current theory files, in ROOT order, followed by
any files not listed there, and the other generated indexes: decisions-index.md and, when the load list holds it,
theory-map-index.md without the theories that list holds anyway.

The measured tier is chosen from what the implementer sessions actually consulted: for every file named in
a tool call of the last SESSIONS Opus sessions of this project that work on the library (a session that works
on the orchestration is left out, as extract_owner_directions.py tells it), the sessions that touched it and
the characters pulled from it. A file qualifies when at least MIN_SESSIONS sessions consulted it and what they
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

usage: select_base_load.py [--dry-run | --refresh-index | --frontier WHO | --founding WHO]
--refresh-index updates only the generated indexes (refresh_indexes), without selecting or removing load-list entries.
--frontier WHO rewrites only the working-frontier tier of that base's list (max, xhigh, high): the theories the last
FRONTIER_SESSIONS sessions of the roles that fork it used, ranked by use per token and taken until the layer's budget
(the target less the stable part and the layer's other entries) or the floor (FRONTIER_FLOOR of the sessions); that
tier is what its layer holds, and base.sh runs this at every layer refresh.
--founding WHO rewrites the founding tier of that list to the founding theories its roles used (FOUNDING_MIN of the
last FOUNDING_SESSIONS sessions): the stable part is the owner's to rebuild, so this is run when it is.

A session uses a theory when it reads it or when its own writing — its tool calls and visible replies, never what came
back to it — names one of the names the theory defines (use_of). Measured on 2026-09-22 (notes/plan-bases-upgrade.md
D1-D4): reading the base prefix is 62% of what the run spends, 176 of the 226 founding theories were used by no
implementer or fixer in a week, and the frontier, a fixed 40 theories measured from 7 sessions, had taken the high base
from 525K to 602K in a day.
"""
import contextlib
import glob
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from digest import DECLARED, held_text  # noqa: E402
import manifest  # noqa: E402
from base_pack import (CHUNK_BYTES, CALL_TOKENS, INDEX_RATIO, PACKED_RATIO, SELECTED_FACTOR,  # noqa: E402
                       SESSION_TOKENS)
from extract_owner_directions import BASE_LOADS, LIBRARY_ROLES, claude_session  # noqa: E402
PROJECT = os.path.dirname(os.path.dirname(HERE))
TRANSCRIPTS = os.path.expanduser("~/.claude/projects/" + PROJECT.replace("/", "-").replace("_", "-"))
TARGET = manifest.TARGET
SESSIONS = int(os.environ.get("ORCH_SELECT_SESSIONS", 7))
MIN_SESSIONS = 2
MIN_SHARE = 0.10
CHUNK_FILL = CHUNK_BYTES * 0.9  # chunks break at line ends, so they average a little under their bound
FIXED_TOKENS = 0  # the lean session measured by base_pack already includes the role prompt and the load's turns
NEVER = {"HANDOFF.md", "PLANNING_LOG.md", ".claude/orchestration/owner-ledger.md", "THEORY_MAP.md"}
FRONTIER_SESSIONS = int(os.environ.get("ORCH_FRONTIER_SESSIONS", 60))  # 7 collapsed to 1 of 40 theories (2026-09-20)
FRONTIER_FLOOR = float(os.environ.get("ORCH_FRONTIER_FLOOR", 0.05))    # nothing used by fewer holds a place (D1)
FRONTIER_EVIDENCE = 10  # fewer sessions than this measure nothing: the frontier is left as it stands
FOUNDING_SESSIONS = int(os.environ.get("ORCH_FOUNDING_SESSIONS", 400))  # a week of the roles (347 on 2026-09-22)
FOUNDING_MIN = 2
FOUNDING_QUIET_DAYS = int(os.environ.get("ORCH_FOUNDING_QUIET_DAYS", 3))  # changed since: the frontier's, not the stable part's
# The layer's measured size against its estimate: the fork's own launch and the chunk calls' turns (2026-09-22 22:18,
# 325,243 measured against 302,435 estimated). The stable part measures as estimated (276,298 against 275,196).
LAYER_FACTOR = 1.075
CLAUSE = 90  # what an index keeps of a theory's map row: its first clause, cut at a word under this many characters
# always read fresh or not at all, never held: the planner's state, the planner's log, the ledger, the theory map


def tokens(path, level="statements"):
    """Estimated tokens of a held file in the packed load, and its share of chunk calls."""
    text, _ = held_text(path, level)  # theories and tools are held as digests: statements, not proofs or code
    size, suffix = len(text.encode()), os.path.splitext(path)[1]
    if os.path.basename(path) == "theory-names.md":
        return int(size / INDEX_RATIO * SELECTED_FACTOR["index"]), size / CHUNK_FILL
    return int(size / PACKED_RATIO.get(suffix, 2.6) * SELECTED_FACTOR.get(suffix, 1.0)), size / CHUNK_FILL


def is_base_load(head):
    """A session that loaded a base (file by file or bundled), as opposed to one that works."""
    return any(prefix in head for prefix in BASE_LOADS)


def expand(pattern):
    p = os.path.expanduser(pattern)
    p = p if os.path.isabs(p) else os.path.join(PROJECT, p)
    return sorted(q for q in glob.glob(p) if os.path.isfile(q))


def implementer_sessions():
    out = []
    for f in sorted(glob.glob(TRANSCRIPTS + "/*.jsonl"), key=os.path.getmtime, reverse=True):
        head = open(f, errors="ignore").read(600_000)
        if '"model":"claude-opus' in head and "connectivity probe" not in head:
            if is_base_load(head) and not any(p in open(f, errors="ignore").read() for p in LIBRARY_ROLES):
                continue  # a base itself, not a fork of one
            if claude_session(f)[1]:
                continue  # it works on the orchestration, not on the library
            out.append(f)
        if len(out) == SESSIONS:
            break
    return out


def fact_theories():
    """Which theory each bare fact name belongs to, so that a read naming a fact counts for its theory."""
    out = {}
    for path in sorted(glob.glob(os.path.join(PROJECT, "theories", "*.thy"))):
        rel = os.path.relpath(path, PROJECT)
        try:
            text = open(path, errors="ignore").read()
        except OSError:
            continue
        for name in re.findall(r"^\s*(?:lemma|theorem|corollary|proposition|definition|fun|primrec|abbreviation)\s+([A-Za-z_][\w']*)\s*[:\[]", text, re.M):
            out.setdefault(name, rel)
    return out


FACT_THEORY = {}


def measure(files):
    if not FACT_THEORY:
        FACT_THEORY.update(fact_theories())
    use = {}
    for f in files:
        calls = {}
        own = not is_base_load(open(f, errors="ignore").read(600_000))
        for line in open(f, errors="ignore"):
            if not own:  # a fork: everything before its own first message is a copy of the base's load
                own = any('"' + p in line or p in line[:400] for p in LIBRARY_ROLES)
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
                    # `v2.py read` (a gather, before 2026-09-21) and show.py name facts, not files (`Theory.fact`, or a bare fact name): that is the
                    # reading the protocols prescribe, and counting only paths made it invisible — which is why the
                    # xhigh roles, who read statements by name, measured one theory on 2026-09-20 and the
                    # implementers, who open whole files, measured six.
                    for theory in set(re.findall(r"(?<![\w/.-])([A-Z][A-Za-z0-9_]*)\.[a-z_][\w'.]*", text)):
                        rel = f"theories/{theory}.thy"
                        if os.path.isfile(os.path.join(PROJECT, rel)):
                            found.add(rel)
                    for name in set(re.findall(r"(?<![\w/.-])([A-Za-z_][\w']*)_(?:def|simps|induct|cases|iff|intro|elim|dest)\b", text)):
                        rel = FACT_THEORY.get(name)
                        if rel:
                            found.add(rel)
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


def founding_theories():
    """idea_candidates.founding_theories, imported when first asked: that module reads THEORY_MAP.md as it loads, and
    imported at the top it made this one unloadable wherever the map does not stand beside it (a test's copy)."""
    from idea_candidates import founding_theories as found
    return found()


NAME = re.compile(r"[A-Za-z][A-Za-z0-9_']{3,}")
DEFINED = {}


def defined_names():
    """{name: the theories that define it}, for the names a session may write: a theory's own name and every name its
    declarations introduce. A name that more than three theories define says nothing of which one a session used."""
    owners = {}
    for path in glob.glob(os.path.join(PROJECT, "theories", "*.thy")):
        rel, theory = os.path.relpath(path, PROJECT), os.path.basename(path)[:-4]
        try:
            text = open(path, errors="ignore").read()
        except OSError:
            continue
        for name in set(DECLARED.findall(text)) | {theory}:
            if len(name) >= 4:
                owners.setdefault(name, set()).add(rel)
    return {n: ts for n, ts in owners.items() if len(ts) <= 3}


def own_writing(path):
    """The names a session itself wrote — in its tool calls and its visible replies, after its own launch — and never
    what came back to it: a name it wrote is one it worked with, a name it was shown may be one it passed over. Names
    are those with an underscore or an inner capital (Isabelle's and Python's), not words."""
    own = not is_base_load(open(path, errors="ignore").read(600_000))
    words = set()
    for line in open(path, errors="ignore"):
        if not own:  # a fork: everything before its own launch is a copy of the base's load
            own = any('"' + p in line or p in line[:400] for p in LIBRARY_ROLES)
            continue
        if '"assistant"' not in line:
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        for c in (d.get("message") or {}).get("content") or []:
            if isinstance(c, dict) and c.get("type") in ("text", "tool_use"):
                said = c.get("text", "") if c["type"] == "text" else json.dumps(c.get("input") or {})
                words |= {w.rstrip("'") for w in NAME.findall(said) if "_" in w or re.search(r"[a-z][A-Z]", w)}
    return words


def use_of(files):
    """{file: the sessions that used it}: a session uses a theory or a tool when it reads it (measure), and a theory too
    when its own writing names one of the names the theory defines — the evidence of work with held content, which a
    session uses without reading (2026-09-22: every one of the high frontier's 40 theories was used, 13% of the forks
    each, while the forks read few of them)."""
    if not DEFINED:
        DEFINED.update(defined_names())
    out = {p: set(u[0]) for p, u in measure(files).items()}
    for f in files:
        for w in own_writing(f):
            for rel in DEFINED.get(w, ()):
                out.setdefault(rel, set()).add(f)
    return out


def ranked_within(use, sizes, room, need):
    """The candidates taken, best first: each used by at least `need` sessions, ranked by sessions per token, and taken
    while they fit in `room` (one that does not fit is passed over for a smaller one below it)."""
    order = sorted((rel for rel in use if len(use[rel]) >= need and sizes.get(rel)),
                   key=lambda rel: (-len(use[rel]) / sizes[rel], rel))
    chosen, spent = [], 0
    for rel in order:
        if spent + sizes[rel] <= room:
            chosen.append(rel)
            spent += sizes[rel]
    return chosen, spent


def held_by(who, part=None):
    """(tier, path) of what a base's list holds, for that base whatever the caller's own list."""
    was = os.environ.get("ORCH_LOAD_LIST")
    os.environ["ORCH_LOAD_LIST"] = os.path.join(HERE, manifest.LISTS[who])
    try:
        files = manifest.held_files(part=part or "")
        return [(tier, p, manifest.level_of(p)) for tier, p in files]
    finally:
        if was is None:
            os.environ.pop("ORCH_LOAD_LIST", None)
        else:
            os.environ["ORCH_LOAD_LIST"] = was


def estimate(entries):
    """Tokens a list's entries take loaded, their chunk calls included."""
    total = calls = 0.0
    for _, p, level in entries:
        t, c = tokens(p, level)
        total += t
        calls += c
    return int(total + CALL_TOKENS * calls)


def layer_room(stable, fixed, target=None, factor=None):
    """The tokens a layer's frontier may take: the target less the stable part, with the layer's measured overhead
    (factor) on everything the layer holds, its other entries (`fixed`) first."""
    target, factor = TARGET if target is None else target, LAYER_FACTOR if factor is None else factor
    return max(0, int((target - stable) / factor - fixed))


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


def theory_map_index(skip=()):
    """Every theory of THEORY_MAP.md with the first clause of what its row says it holds, in the map's order: what
    exists and what it is for, one line each (implementers looked the map up in 21 of 24 sessions). Theories whose
    digest a base holds anyway (`skip`) are left out."""
    rows = re.findall(r"^\| (\w+) \| [^|]* \| (.*?) \|$", open(os.path.join(PROJECT, "THEORY_MAP.md"), errors="ignore").read(), re.M)
    out = ["# What each theory holds: the first clause of its THEORY_MAP.md row (grep the map or the source for the rest).", ""]
    out += [f"{name}: {clause(content)}" for name, content in rows if name != "Theory" and name not in skip]
    held = os.path.join(HERE, "state", "held")
    os.makedirs(held, exist_ok=True)
    open(os.path.join(held, "theory-map-index.md"), "w").write("\n".join(out) + "\n")
    return len(out) - 2


def clause(content, cap=CLAUSE):
    """The first clause of a map row, cut at a whole word under `cap` characters: the index is one line a theory, and
    the design measured it at 56K tokens (1,462 rows, 2026-09-19) where it stood at 100.9K on 2026-09-22 (1,772 rows,
    a median line of 138 characters). The row itself is a grep away."""
    first = re.split(r"[;.](?:\s|$)", content)[0].strip()
    if len(first) <= cap:
        return first
    return first[:cap].rsplit(" ", 1)[0].rstrip(",:;") + " …"


def founding_index(held):
    """The founding theories a list does not hold, one line each (the first clause of its map row): a base whose
    founding tier keeps only what its roles use still says what the others are (D2)."""
    content = dict(re.findall(r"^\| (\w+) \| [^|]* \| (.*?) \|$", open(os.path.join(PROJECT, "THEORY_MAP.md"),
                                                                     errors="ignore").read(), re.M))
    out = ["# The founding theories this base does not hold, with the first clause of each one's THEORY_MAP.md row "
           "(read the source before relying on one).", ""]
    out += [f"{n}: {clause(content.get(n, ''))}" for n in founding_theories() if n not in held]
    target = os.path.join(HERE, "state", "held")
    os.makedirs(target, exist_ok=True)
    open(os.path.join(target, "founding-index.md"), "w").write("\n".join(out) + "\n")
    return len(out) - 2


def decisions_index():
    """Every decision of DECISIONS.md by its heading and the first sentence under it: the decisions known by name,
    each read in full where it is written."""
    text = open(os.path.join(PROJECT, "DECISIONS.md"), errors="ignore").read()
    out = ["# The decisions of DECISIONS.md, by heading and first sentence (read the section itself before relying on it).", ""]
    for head, body in re.findall(r"^(#{2,3} .+)\n+([^\n#][^\n]*(?:\n[^\n#][^\n]*)*)", text, re.M):
        prose = " ".join(body.split())
        end = prose.find(". ")
        out.append(f"{head} — {prose[:end + 1] if 0 <= end < 400 else prose[:300]}")
    held = os.path.join(HERE, "state", "held")
    os.makedirs(held, exist_ok=True)
    open(os.path.join(held, "decisions-index.md"), "w").write("\n".join(out) + "\n")
    return len(out) - 2


def refresh_indexes():
    """Regenerate the indexes a load list may hold from the current sources: the theory names, the decisions, and,
    when the list holds it, the theory map's index without the theories the list holds anyway."""
    count = theory_names()
    decisions_index()
    listed = open(manifest.load_list()).read()
    held = {os.path.basename(p)[:-4] for _, p in manifest.held_files() if p.endswith(".thy")}
    if "theory-map-index.md" in listed:
        theory_map_index(skip=held)
    if "founding-index.md" in listed:
        founding_index(held)
    return count


FRONTIER_HEAD = "# the working frontier"


def forking_roles(who):
    """The roles that fork this base, from v2's own table: xhigh is the designer, task designer, investigator and
    reviewer; high the implementer and the fixer."""
    import v2
    return {role for role, spec in v2.ROLES.items() if spec.get("origin") == who}


def archived_sessions(roles):
    """The sessions of those roles that v2 archived (state/v2-archive.jsonl: released a day ago and referred to by
    nothing): without them a window of FOUNDING_SESSIONS was a day of sessions, never the week it is meant to be."""
    import v2
    out = []
    try:
        for line in open(os.path.join(v2.STATE, "v2-archive.jsonl"), errors="ignore"):
            with contextlib.suppress(ValueError):
                s = json.loads(line).get("session") or {}
                if s.get("role") in roles and s.get("sid"):
                    out.append(s)
    except OSError:
        pass
    return out


def sessions_of(roles, limit=SESSIONS):
    """The transcripts of the most recent sessions of those roles, newest first, taken from the orchestration's own
    record of which session held which role. Until it has one, the v1 implementers stand in, as they did for the
    lists as first written."""
    try:
        import v2
        recorded = [s for s in v2.peek()["sessions"].values() if s.get("role") in roles and s.get("sid")]
        recorded += archived_sessions(roles)
        recorded = sorted({s["sid"]: s for s in recorded}.values(), key=lambda s: s.get("started") or 0, reverse=True)
    except Exception:  # noqa: BLE001 — a missing or unreadable state must not stop a refresh
        recorded = []
    out = [v2.transcript(s["sid"]) for s in recorded]  # a session in a task's tree keeps its transcript there
    out = [f for f in out if os.path.exists(f)][:limit]
    return out or implementer_sessions()


def frontier(who, dry_run=False):
    """Rewrite the working-frontier tier of a base's list from what the roles that fork it used: the theories outside
    the rest of the list that the last FRONTIER_SESSIONS sessions of those roles used (use_of), each by at least
    FRONTIER_FLOOR of them, ranked by use per token at the tier's level and taken until the layer's budget is full
    (layer_room: the target less the stable part and the layer's other entries). The frontier is what the layer holds
    and what goes stale; the tiers above it are the stable reference and are not touched here. With too few sessions to
    measure anything it is left as it stands."""
    path = os.path.join(HERE, manifest.LISTS[who])
    text = open(path).read()
    head = re.search(rf"^{re.escape(FRONTIER_HEAD)}.*$", text, re.M)
    if not head:
        # not every layer holds a frontier: the planner's holds the generated indexes and the direction, which are
        # regenerated at pack time. Nothing to re-measure is not a failure, and a refresh must not stop on it.
        print(f"the {who} list has no working-frontier tier: nothing to re-measure")
        return 0
    after = text[head.end():]
    following = re.search(r"^# ", after, re.M)
    end = head.end() + (following.start() if following else len(after))
    level = next((lv for lv in ("signatures", "definitions") if f"as {lv}" in head.group(0)), "statements")
    was = [ln.split("  #")[0].strip() for ln in after[:following.start() if following else len(after)].splitlines()]
    was = [ln for ln in was if ln and not ln.startswith("#")]
    roles = forking_roles(who)
    files = sessions_of(roles, FRONTIER_SESSIONS)
    if len(files) < FRONTIER_EVIDENCE:
        print(f"the {who} frontier is left as it stands: {len(files)} sessions of {', '.join(sorted(roles))} measure "
              f"nothing (at least {FRONTIER_EVIDENCE})")
        return 0
    use = use_of(files)
    # what the list holds outside this tier, by where it stands: a theory the founding tier now keeps that the frontier
    # held before is the stable part's (counted by name, it was chosen again and held twice, 2026-09-22)
    elsewhere = {ln for ln in (l.split("  #")[0].strip() for l in (text[:head.start()] + text[end:]).splitlines())
                 if ln and not ln.startswith("#")}
    cands, sizes = {}, {}
    for rel, ss in use.items():
        full = os.path.join(PROJECT, rel)
        if not rel.startswith("theories/") or rel in elsewhere or rel in NEVER or not os.path.isfile(full):
            continue
        cands[rel], sizes[rel] = ss, tokens(full, level)[0]
    frontier_paths = {os.path.join(PROJECT, rel) for rel in was}
    stable = estimate(held_by(who, "stable"))
    fixed = estimate([e for e in held_by(who, "layer") if e[1] not in frontier_paths])
    room = layer_room(stable, fixed)
    need = max(MIN_SESSIONS, -(-int(FRONTIER_FLOOR * 1000) * len(files) // 1000))
    chosen, spent = ranked_within(cands, sizes, room, need)
    block = [f"{FRONTIER_HEAD} ({len(chosen)} theories for the {', '.join(sorted(roles))} sessions, chosen "
             f"{time.strftime('%Y-%m-%d')} from the last {len(files)} of them: each used by at least {need}, by use per "
             f"token, within the layer's {room // 1000}K), as {level}"]
    block += [f"{rel}  # {len(cands[rel])} sessions, ~{sizes[rel] // 1000 or 1}K tokens" for rel in chosen]
    print(f"{who} frontier: {len(chosen)} theories, ~{spent // 1000}K of the layer's {room // 1000}K (stable ~{stable // 1000}K, "
          f"the layer's other entries ~{fixed // 1000}K), each used by at least {need} of {len(files)} sessions of "
          f"{', '.join(sorted(roles))}; {len(set(chosen) - set(was))} new, {len(set(was) - set(chosen))} dropped")
    if dry_run:
        return 0
    open(path, "w").write(text[:head.start()] + "\n".join(block) + "\n" + text[end:])
    print(f"{os.path.basename(path)}: the frontier tier rewritten")
    return 0


FOUNDING_HEAD = "# every other founding theory"


def recently_changed(days=None):
    """The theories main changed within the last `days`: work in progress, which the frontier holds and refreshes,
    not the stable part, whose every change would stand in the delta until the owner rebuilt it."""
    days = FOUNDING_QUIET_DAYS if days is None else days
    out = subprocess.run(["git", "-C", PROJECT, "log", f"--since={days} days ago", "--name-only", "--format=", "--",
                          "theories/"], capture_output=True, text=True).stdout
    return {os.path.basename(line)[:-4] for line in out.split() if line.endswith(".thy")}


def founding(who, dry_run=False):
    """Rewrite a list's founding tier to the founding theories its roles used: of every founding theory the central
    ideas do not pin (idea_candidates.founding_theories, a naming heuristic), those that at least FOUNDING_MIN of the
    last FOUNDING_SESSIONS sessions of the roles that fork the base used (use_of). Over the week to 2026-09-22, 176 of
    the 226 were used by no implementer or fixer (D2). The others are said by the indexes: on high the theory map's,
    which leaves out only what the list holds, elsewhere the founding index (founding_index). The stable part is the
    owner's to rebuild: this is run when it is."""
    path = os.path.join(HERE, manifest.LISTS[who])
    text = open(path).read()
    head = re.search(rf"^{re.escape(FOUNDING_HEAD)}.*$", text, re.M)
    if not head:
        print(f"the {who} list has no founding tier: nothing to choose")
        return 0
    after = text[head.end():]
    following = re.search(r"^# ", after, re.M)
    end = head.end() + (following.start() if following else len(after))
    level = next((lv for lv in ("signatures", "definitions") if f"as {lv}" in head.group(0)), "statements")
    pinned = {os.path.basename(p)[:-4] for tier, p, _ in held_by(who) if tier.startswith("pinned")}
    candidates = [n for n in founding_theories() if n not in pinned]
    roles = forking_roles(who)
    files = sessions_of(roles, FOUNDING_SESSIONS)
    if len(files) < FRONTIER_EVIDENCE:
        print(f"the {who} founding tier is left as it stands: {len(files)} sessions measure nothing")
        return 0
    use = use_of(files)
    moving = recently_changed()
    used = [n for n in candidates if len(use.get(f"theories/{n}.thy", ())) >= FOUNDING_MIN]
    kept = [n for n in used if n not in moving]
    block = [f"{FOUNDING_HEAD} its roles used, as {level} (generated {time.strftime('%Y-%m-%d')}: of the "
             f"{len(candidates)} founding theories the central ideas do not pin, the {len(kept)} that at least "
             f"{FOUNDING_MIN} of the last {len(files)} sessions of {', '.join(sorted(roles))} read or named and main "
             f"left unchanged for {FOUNDING_QUIET_DAYS} days — {len(used) - len(kept)} more in use are changing, and the "
             f"frontier holds them; the others are said by the indexes; in import order)"]
    block += [f"theories/{n}.thy" for n in kept]
    print(f"{who} founding tier: {len(kept)} of {len(candidates)} used by at least {FOUNDING_MIN} of {len(files)} sessions "
          f"and unchanged for {FOUNDING_QUIET_DAYS} days ({len(used) - len(kept)} used but changing, left to the frontier)")
    if dry_run:
        return 0
    open(path, "w").write(text[:head.start()] + "\n".join(block) + "\n" + text[end:])
    print(f"{os.path.basename(path)}: the founding tier rewritten")
    return 0


def main():
    if "--frontier" in sys.argv:
        who = sys.argv[sys.argv.index("--frontier") + 1]
        return frontier(who, "--dry-run" in sys.argv)
    if "--founding" in sys.argv:
        who = sys.argv[sys.argv.index("--founding") + 1]
        return founding(who, "--dry-run" in sys.argv)
    count = refresh_indexes()
    print(f"theory-names.md: {count} names")
    if "--refresh-index" in sys.argv:
        return
    path = manifest.load_list()
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
        print(f"{os.path.basename(path)} rewritten")


if __name__ == "__main__":
    sys.exit(main() or 0)
