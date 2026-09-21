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

usage: select_base_load.py [--dry-run | --refresh-index | --frontier WHO]
--refresh-index updates only the generated indexes (refresh_indexes), without selecting or removing load-list entries.
--frontier WHO rewrites only the working-frontier tier of that base's list (max, xhigh, high), measured from the
sessions of the roles that fork it; that tier is what its layer holds, and base.sh runs this at every layer refresh.
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
    out += [f"{name}: {re.split(r'[;.]', content)[0].strip()}" for name, content in rows if name != "Theory" and name not in skip]
    held = os.path.join(HERE, "state", "held")
    os.makedirs(held, exist_ok=True)
    open(os.path.join(held, "theory-map-index.md"), "w").write("\n".join(out) + "\n")
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
    if "theory-map-index.md" in listed:
        theory_map_index(skip={os.path.basename(p)[:-4] for _, p in manifest.held_files() if p.endswith(".thy")})
    return count


FRONTIER_N = int(os.environ.get("ORCH_FRONTIER_N", 40))
FRONTIER_HEAD = "# the working frontier"


def forking_roles(who):
    """The roles that fork this base, from v2's own table: xhigh is the designer, task designer, investigator and
    reviewer; high the implementer and the fixer."""
    import v2
    return {role for role, spec in v2.ROLES.items() if spec.get("origin") == who}


def sessions_of(roles, limit=SESSIONS):
    """The transcripts of the most recent sessions of those roles, newest first, taken from the orchestration's own
    record of which session held which role. Until it has one, the v1 implementers stand in, as they did for the
    lists as first written."""
    try:
        import v2
        recorded = sorted((s for s in v2.peek()["sessions"].values() if s.get("role") in roles and s.get("sid")),
                          key=lambda s: s.get("started") or 0, reverse=True)
    except Exception:  # noqa: BLE001 — a missing or unreadable state must not stop a refresh
        recorded = []
    out = [v2.transcript(s["sid"]) for s in recorded]  # a session in a task's tree keeps its transcript there
    out = [f for f in out if os.path.exists(f)][:limit]
    return out or implementer_sessions()


def frontier(who, dry_run=False):
    """Rewrite the working-frontier tier of a base's list from what the roles that fork it actually consulted. The
    frontier is what the layer holds and what goes stale; the tiers above it are the stable reference and are not
    touched here."""
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
    files = sessions_of(roles)
    use = measure(files)
    elsewhere = {ln for ln in (l.split("  #")[0].strip() for l in text.splitlines())
                 if ln and not ln.startswith("#")} - set(was)
    cands = []
    for rel, (ss, pulled) in use.items():
        full = os.path.join(PROJECT, rel)
        if not rel.startswith("theories/") or rel in elsewhere or rel in NEVER or not os.path.isfile(full):
            continue
        if pulled < MIN_SHARE * os.path.getsize(full):
            continue
        density = (pulled / max(1, len(files))) / max(1, os.path.getsize(full))
        cands.append((len(ss), density, rel, pulled))
    cands.sort(key=lambda x: (x[0] < MIN_SESSIONS, -x[1]))
    measured = [(rel, f"{n} sessions, {pulled // 1000}K pulled") for n, _, rel, pulled in cands[:FRONTIER_N]]
    # What the roles that fork this base have read is thin evidence early in a run — the xhigh roles read statements
    # through gathers, not whole theories — and a tier rebuilt from it alone would collapse (1 of 40 on 2026-09-20).
    # So the measurement promotes what it found and the previous frontier fills the rest, in its own order: the tier
    # keeps its size, and it changes only where there is evidence to change it.
    lines, seen = list(measured), {rel for rel, _ in measured}
    for rel in was:
        if len(lines) >= FRONTIER_N:
            break
        if rel not in seen and os.path.isfile(os.path.join(PROJECT, rel)):
            lines.append((rel, "carried from the frontier before this refresh"))
            seen.add(rel)
    if not lines:
        print(f"the {who} frontier is left as it is: nothing measured and nothing to carry")
        return 0
    block = [f"{FRONTIER_HEAD} ({len(lines)} theories for the {', '.join(sorted(roles))} sessions, re-measured "
             f"{time.strftime('%Y-%m-%d')} from {len(files)} of them: {len(measured)} by what they consulted, "
             f"{len(lines) - len(measured)} carried), as {level}"]
    block += [f"{rel}  # {note}" for rel, note in lines]
    kept = [rel for rel, _ in lines]
    print(f"{who} frontier: {len(lines)} theories ({len(measured)} measured from {len(files)} sessions of "
          f"{', '.join(sorted(roles))}, {len(lines) - len(measured)} carried); "
          f"{len(set(kept) - set(was))} new, {len(set(was) - set(kept))} dropped")
    if dry_run:
        return 0
    open(path, "w").write(text[:head.start()] + "\n".join(block) + "\n" + text[end:])
    print(f"{os.path.basename(path)}: the frontier tier rewritten")
    return 0


def main():
    if "--frontier" in sys.argv:
        who = sys.argv[sys.argv.index("--frontier") + 1]
        return frontier(who, "--dry-run" in sys.argv)
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
