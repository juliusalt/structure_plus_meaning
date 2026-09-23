#!/usr/bin/env python3
"""Select what a base holds by its responsibilities, and what a task is given by its own relations.

A base holds what does not depend on which tasks are queued: the owner's reference pins, the direction, and the
catalogue — the complete discovery indexes and, for the roles that steer by the plan, the notions every part of the
plan names. The relations of a piece of work (the theories its brief names, what they stand on, what uses them) are
the task's own. They are given to its sessions as they start (task_relations here, v2.relations_read), so a base
neither grows with the queue nor is rebuilt when the queue changes: on 2026-09-23 the union of the current tasks'
relations was about 280K tokens for 5 tasks and 620K for 20, and the part of it two or more tasks shared still 480K
for 20. Sizes report the consequence; they never rank or silently remove required content. Source relations aid
discovery; they are not semantic dependency proofs. See notes/plan-bases-two-purposes.md.
"""
import glob
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from digest import DECLARED, held_text  # noqa: E402
import manifest  # noqa: E402
from base_pack import (CHUNK_BYTES, CALL_TOKENS, INDEX_RATIO, PACKED_RATIO, SELECTED_FACTOR,  # noqa: E402
                       SESSION_TOKENS)
PROJECT = os.environ.get("ORCH_PROJECT") or os.path.dirname(os.path.dirname(HERE))
CHUNK_FILL = CHUNK_BYTES * 0.9  # chunks break at line ends, so they average a little under their bound
DEPTH_ORDER = {"signatures": 0, "definitions": 1, "statements": 2}
# The depth at which each base's roles use what a piece of work stands on: high's implementers and fixers consume its
# contracts (statements); xhigh's designers, task designers, investigators and reviewers reason about its meaning
# (definitions); the planner's base holds no task's material, and a planner that asks is given meanings.
SUPPLIER_DEPTH = {"high": "statements", "xhigh": "definitions", "max": "definitions"}
PLAN_BASES = ("max", "xhigh")  # the bases whose roles steer by the whole plan: planner, designers, reviewers
RELATIONS_START = "# === relations ==="
RELATIONS_END = "# === end relations ==="
FRONTIER_HEAD = "# the working frontier"  # a list from before the named parts: its generated tier
NAME = re.compile(r"[A-Za-z][A-Za-z0-9_']{3,}")
# never held by a base: each is read fresh or not at all (the planner's state and log, the ledger, the theory map)
NEVER = {"HANDOFF.md", "PLANNING_LOG.md", ".claude/orchestration/owner-ledger.md", "THEORY_MAP.md"}


def text_tokens(path, text):
    """The operational packed-size estimate, shared by real and virtual catalogue inputs: (tokens, chunk calls)."""
    size, suffix = len(text.encode()), os.path.splitext(path)[1]
    if os.path.basename(path) == "theory-names.md":
        return int(size / INDEX_RATIO * SELECTED_FACTOR["index"]), size / CHUNK_FILL
    return int(size / PACKED_RATIO.get(suffix, 2.6) * SELECTED_FACTOR.get(suffix, 1.0)), size / CHUNK_FILL


def tokens(path, level="statements"):
    return text_tokens(path, held_text(path, level)[0])


def estimate(entries):
    """Tokens a list's entries take loaded, their chunk calls included."""
    total = calls = 0.0
    for _, p, level in entries:
        t, c = tokens(p, level)
        total += t
        calls += c
    return int(total + CALL_TOKENS * calls)


def list_path(who):
    """The list a base is built from: BASE_LOAD_LIST while a build works on its candidate (base_stack.build)."""
    return os.environ.get("BASE_LOAD_LIST") or os.path.join(HERE, manifest.LISTS[who])


def held_by(who, part=None):
    """Each entry's actual projection, including an explicit deepening above the stable reference."""
    return [(e["tier"], e["path"], e["level"]) for e in manifest.list_entries(open(list_path(who)).read(), PROJECT)
            if not part or e["part"] == part or (part == "layer" and e["part"] != "stable")]


def without_generated(text):
    """A list's text without its generated relation block: what the owner's pins and the fixed tiers hold."""
    if RELATIONS_START not in text:
        return text
    a, b = text.index(RELATIONS_START), text.index(RELATIONS_END) + len(RELATIONS_END)
    return text[:a] + text[b:]


def held_levels(who, text=None):
    """{theory: the deepest level the base holds it at}, as its list stands (published or candidate)."""
    text = open(list_path(who)).read() if text is None else text
    out = {}
    for e in manifest.list_entries(text, PROJECT):
        name, ext = os.path.splitext(os.path.basename(e["path"]))
        if ext == ".thy" and DEPTH_ORDER[e["level"]] >= DEPTH_ORDER.get(out.get(name), -1):
            out[name] = e["level"]
    return out


def deeper(depth, held):
    """Whether holding at `depth` adds to what is held at `held` (None: not held at all)."""
    return held is None or DEPTH_ORDER[depth] > DEPTH_ORDER[held]


# ---------------------------------------------------------------- the generated catalogues

def held_dir():
    held = os.path.join(HERE, "state", "held")
    os.makedirs(held, exist_ok=True)
    return held


def theory_names():
    """Every actual theory file, in ROOT order; names absent from ROOT come last.

    THEORY_MAP can lag new files. The catalogue describes source existence, not acceptance or proof status. ROOT's
    order is recorded without claiming it is a topological order of the imports.
    """
    available = {os.path.basename(p)[:-4] for p in glob.glob(os.path.join(PROJECT, "theories", "*.thy"))}
    names, seen = [], set()
    for line in open(os.path.join(PROJECT, "ROOT")):
        match = re.fullmatch(r'\s+"?([A-Za-z_0-9]+)"?(?:\s+\(global\))?(?:\s+\[[^\]]*\])?\s*', line)
        if match and match[1] in available and match[1] not in seen:
            names.append(match[1])
            seen.add(match[1])
    extra = sorted(available - seen)
    out = ["# Every theory source file, by name, in ROOT order (grep THEORY_MAP.md or the source for its content).",
           "# A listed name records source existence, not acceptance or proof status.", ""]
    out += [" ".join(names[i:i + 8]) for i in range(0, len(names), 8)]
    if extra:
        out += ["", "# Additional source files not listed in ROOT, alphabetically:"]
        out += [" ".join(extra[i:i + 8]) for i in range(0, len(extra), 8)]
    open(os.path.join(held_dir(), "theory-names.md"), "w").write("\n".join(out) + "\n")
    return len(names) + len(extra)


def generated_name(name, who=None):
    """A generated catalogue's file: one per base where what it leaves out is what that base holds."""
    return f"{name}-{who}.md" if who else f"{name}.md"


def theory_map_index(write=True, who=None, text=None):
    """The complete vocabulary, each purpose quoted from its source row; missing rows remain explicit.

    For a base (`who`), every theory but those the base holds already — at signatures or deeper, which say what the
    theory is and more: a line for them was the same thing twice (12K tokens a request on max and xhigh, 2026-09-23).
    Each base's own file, so no source disappears from one base's discovery because another holds it.
    """
    rows = dict(re.findall(r"^\| (\w+) \| [^|]* \| (.*?) \|$", open(os.path.join(PROJECT, "THEORY_MAP.md")).read(), re.M))
    held = held_levels(who, text) if who else {}
    names = sorted(n for n in (os.path.basename(p)[:-4] for p in glob.glob(os.path.join(PROJECT, "theories", "*.thy")))
                   if n not in held)
    out = ["# Every theory source and the first clause of its recorded purpose. Read its source for the contract.",
           "# This index describes existence, not acceptance or adequacy. Missing descriptions are explicit."
           + (" The theories this base holds are not repeated here." if who else ""), ""]
    for name in names:
        purpose = re.split(r"[;.](?:\s|$)", rows[name])[0].strip() if name in rows else \
            "No THEORY_MAP description; inspect the source."
        out.append(f"{name}: {purpose}")
    text = "\n".join(out) + "\n"
    if write:
        open(os.path.join(held_dir(), generated_name("theory-map-index", who)), "w").write(text)
    return text


def tool_index(write=True, who=None, text=None):
    """Discoverable tool APIs: each module's first docstring line and its exported function and class names; for a base,
    every tool but those it holds itself (the check and measurement tools xhigh and high hold whole)."""
    import ast
    held = set()
    if who:
        listed = open(list_path(who)).read() if text is None else text
        held = {os.path.basename(e["path"]) for e in manifest.list_entries(listed, PROJECT) if e["path"].endswith(".py")}
    out = ["# Repository tools: module purpose and exported function/class names; inspect the source before use.", ""]
    for path in sorted(glob.glob(os.path.join(PROJECT, "tools", "*.py"))):
        if os.path.basename(path).startswith("test_") or os.path.basename(path) in held:
            continue
        try:
            tree = ast.parse(open(path).read())
        except (SyntaxError, UnicodeError):
            continue
        doc = (ast.get_docstring(tree) or "No module description.").splitlines()[0]
        exported = [n.name for n in tree.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
                    and not n.name.startswith("_")]
        out.append(f"{os.path.relpath(path, PROJECT)}: {doc}\n  {', '.join(exported)}")
    text = "\n".join(out) + "\n"
    if write:
        open(os.path.join(held_dir(), generated_name("tool-index", who)), "w").write(text)
    return text


def plan_index(write=True):
    """The whole plan's discovery map, including obligations with no named implementation; no generated verdict."""
    lib = library()
    out = ["# Whole-plan discovery map; the original plan and problems.txt state the requirements.", ""]
    for part, names in plan_parts(lib["owners"], lib["by_rel"]).items():
        out.append(f"- {part}: " + (", ".join(names) if names else
                                    "No implementation named in this section; this is not a settled obligation."))
    text = "\n".join(out) + "\n"
    if write:
        open(os.path.join(held_dir(), "plan-index.md"), "w").write(text)
    return text


def decisions_index(write=True):
    """Every decision of DECISIONS.md by its heading and the first sentence under it: the decisions known by name,
    each read in full where it is written. An entry is a `##` heading; the `###` sections inside one ("Open", "Evidence
    and limits", "Follow-ups, for the planner") say nothing apart from it, and were a third of the index's lines."""
    text = open(os.path.join(PROJECT, "DECISIONS.md"), errors="ignore").read()
    out = ["# The decisions of DECISIONS.md, by heading and first sentence (read the section itself before relying on it).", ""]
    for head, body in re.findall(r"^(## .+)\n+([^\n#][^\n]*(?:\n[^\n#][^\n]*)*)", text, re.M):
        prose = " ".join(body.split())
        end = prose.find(". ")
        # the first sentence whole, however long: one cut at a character count said half a decision (three did)
        out.append(f"{head} — {prose[:end + 1] if end >= 0 else prose}")
    text = "\n".join(out) + "\n"
    if write:
        open(os.path.join(held_dir(), "decisions-index.md"), "w").write(text)
    return text


def memory_dir():
    """Claude Code's memory directory of this repository: shared by every session of it, the orchestrator's included."""
    return os.path.expanduser("~/.claude/projects/" + re.sub(r"[^A-Za-z0-9]", "-", PROJECT) + "/memory")


def practice(write=True, who=None):
    """The library's working practice: the memory entries library-practice.txt names, each whole but for its
    frontmatter, under its name and description. No base holds the memory directory itself, most of which is the
    orchestrator's own development (library-practice.txt says which entries are left out, and why); an entry named and
    not found is said, not skipped."""
    try:
        rows = [ln.split() for ln in open(os.path.join(HERE, "library-practice.txt"))
                if ln.strip() and not ln.startswith("#")]
    except OSError:
        rows = []  # a harness without its selection (a test's copy) holds no entry, and says so below
    # an entry names the bases whose roles it concerns after its name; none named, every base's
    names = [row[0] for row in rows if not who or len(row) == 1 or who in row[1:]]
    out = ["# The library's working practice",
           "",
           "What the owner said of the library's content and what its development learned about writing and proving it,",
           "recorded in the development's memory by sessions that worked alone with the owner. Their substance holds; their",
           "mechanics (checks, probes, commits, waiting) are the harness's here, as your first message says. Read-only: the",
           "entries are kept where they are written, and library-practice.txt names the ones held here.", ""]
    if not names:
        out += ["(library-practice.txt names no entry)", ""]
    for name in names:
        try:
            text = open(os.path.join(memory_dir(), name + ".md")).read()
        except OSError:
            out += [f"## {name}", "", "(not found in the memory directory: the entry was renamed or removed)", ""]
            continue
        head = re.match(r"^---\n(.*?)\n---\n", text, re.S)
        described = re.search(r"^description:\s*(.+)$", head.group(1), re.M) if head else None
        title = described.group(1).strip().strip('"') if described else name
        out += [f"## {name} — {title}", "", (text[head.end():] if head else text).strip(), ""]
    text = "\n".join(out) + "\n"
    if write:
        open(os.path.join(held_dir(), generated_name("library-practice", who)), "w").write(text)
    return text


def refresh_indexes(who=None):
    """Generate the discovery material from the whole source library and plan, and the library's working practice:
    the decisions and the plan's map shared, the vocabulary, the tools and the practice for each base (`who`, or every
    base whose list stands here), each from its own list."""
    count = theory_names()
    decisions_index()
    plan_index()
    if who is None:  # the shared forms, which no base holds any more, for a reader of the whole library
        theory_map_index()
        tool_index()
        practice()
    for base in [who] if who else [w for w in manifest.LISTS if os.path.exists(os.path.join(HERE, manifest.LISTS[w]))]:
        theory_map_index(who=base)
        tool_index(who=base)
        practice(who=base)
    return count


# ---------------------------------------------------------------- the relations

def forking_roles(who):
    """The roles that fork this base, from v2's own table: xhigh is the designer, task designer, investigator and
    reviewer; high the implementer and the fixer."""
    import v2
    return {role for role, spec in v2.ROLES.items() if spec.get("origin") == who}


def defined_names(project=None):
    """{name: the theories that define it}, for the names a brief may quote: a theory's own name and every name its
    declarations introduce. A name that more than three theories define says nothing of which one is meant."""
    project = project or PROJECT
    owners = {}
    for path in glob.glob(os.path.join(project, "theories", "*.thy")):
        rel, theory = os.path.relpath(path, project), os.path.basename(path)[:-4]
        try:
            text = open(path, errors="ignore").read()
        except OSError:
            continue
        for name in set(DECLARED.findall(text)) | {theory}:
            if len(name) >= 4:
                owners.setdefault(name, set()).add(rel)
    return {n: ts for n, ts in owners.items() if len(ts) <= 3}


def names_in(text, owners, by_rel):
    """Explicit theory references and declared names in code quotations; ordinary prose is not a fact reference.

    Ambiguous quoted names retain every recorded owner. This is discovery evidence, never semantic authority.
    """
    theories = set(by_rel.values())
    found = set(re.findall(r"theories/(\w+)\.thy", text))
    found.update(set(re.findall(r"\b[A-Za-z][A-Za-z_0-9]*\b", text)) & theories)
    for quoted in re.findall(r"`([^`]+)`", text):
        for word in NAME.findall(quoted):
            found.update(by_rel[p] for p in owners.get(word, ()) if p in by_rel)
    return found & theories


def references(thys):
    """A conservative source-reference graph: direct imports and qualified references to repository theories.

    Bare words in proof prose do not identify their owner. Keeping this relation narrower than semantic dependency is
    deliberate: it provides a discovery neighbourhood, not a proof.
    """
    refs, imports = {}, {}
    for name, path in thys.items():
        text = open(path, errors="ignore").read()
        head = re.search(r"\bimports\b(.*?)\bbegin\b", text, re.S)
        direct = {w.strip('"').rsplit(".", 1)[-1] for w in (head.group(1).split() if head else [])}
        imports[name] = sorted(direct & thys.keys())
        qualified = set(re.findall(r"\b([A-Za-z][A-Za-z_0-9]*)\.[A-Za-z][A-Za-z_0-9']*", text))
        refs[name] = sorted((direct | qualified) & thys.keys() - {name})
    return refs, imports


LIBRARY = {}  # project -> (the theories' names, sizes and times, the relations read from them)


def library(project=None):
    """The library's theories and their relations: {thys, by_rel, owners, refs}. Read again only when a theory file
    was added, removed or written since: every session's start and every brief's form check asks for it
    (v2.relations_read, v2.brief_problems), and reading 1,800 theories takes a third of a second."""
    project = project or PROJECT
    directory = os.path.join(project, "theories")
    try:
        seen = tuple(sorted((e.name, e.stat().st_mtime_ns, e.stat().st_size) for e in os.scandir(directory)
                            if e.name.endswith(".thy")))
    except OSError:
        seen = ()
    cached = LIBRARY.get(project)
    if cached and cached[0] == seen:
        return cached[1]
    thys = {os.path.basename(p)[:-4]: p for p in sorted(glob.glob(os.path.join(directory, "*.thy")))}
    by_rel = {os.path.relpath(p, project): n for n, p in thys.items()}
    refs, _ = references(thys)
    lib = dict(thys=thys, by_rel=by_rel, owners=defined_names(project), refs=refs)
    LIBRARY[project] = (seen, lib)
    return lib


def plan_parts(owners, by_rel):
    """Every plan section and every original condition, including parts that name no implemented theory."""
    result = {}
    for path, pattern, label in (("native_control_plan.md", r"^(#{2,3}) (.+)$", "plan"),
                                  ("problems.txt", r"^(\d+)\. (.+)$", "condition")):
        try:
            text = open(os.path.join(PROJECT, path)).read()
        except FileNotFoundError:
            continue
        heads = list(re.finditer(pattern, text, re.M))
        for i, h in enumerate(heads):
            body = text[h.start():heads[i + 1].start() if i + 1 < len(heads) else len(text)]
            key = f"{label}: {h.group(2) if label == 'plan' else h.group(1)}"
            result[key] = sorted(names_in(body, owners, by_rel))
    return result


def current_tasks(roles, tasks=None, state=None):
    """Work whose inputs exist, or which is already under way. Future blocked work stays in the plan and catalogue."""
    import v2
    tasks = v2.all_tasks() if tasks is None else tasks
    state = v2.peek() if state is None else state
    by_id = {str(t["id"]): t for t in tasks}
    records = state.get("tasks", {})
    picked = []
    for tid, task in by_id.items():
        rec = records.get(tid) or {}
        stage = rec.get("stage")
        if task.get("status") == "completed" or stage in ("done", "deleted", "planner"):
            continue
        kind = rec.get("kind") or (task.get("metadata") or {}).get("kind") or v2.brief_kind(task.get("description", ""))
        role = "task-designer" if kind == "brief" else v2.PRODUCER.get(kind)
        if not (role in roles or ("reviewer" in roles and role in v2.PRODUCING)):
            continue
        blockers = [str(x) for x in task.get("blockedBy", [])
                    if by_id.get(str(x), {}).get("status") != "completed" and
                    (records.get(str(x)) or {}).get("stage") != "done"]
        if blockers and stage not in ("running", "parked", "checking", "reviewing", "fixing", "committing"):
            continue
        picked.append(task)
    return sorted(picked, key=lambda t: str(t["id"]))


def relation_choice(who, tasks=None, state=None, text=None):
    """What a base holds by relation: the notions each part of the whole plan and each original condition names, at
    signatures, for the bases whose roles steer by the plan — the whole plan, not the part the run is on. Nothing here
    depends on the task queue (a task's own relations are task_relations'); `tasks` and `state` only name the current
    work for the report."""
    lib = library()
    parts = plan_parts(lib["owners"], lib["by_rel"])
    named = set().union(*map(set, parts.values())) if who in PLAN_BASES and parts else set()
    listed = open(list_path(who)).read() if text is None else text
    levels = held_levels(who, without_generated(listed))
    chosen = sorted(n for n in named if deeper("signatures", levels.get(n)))
    tier = dict(relation="whole-plan notions", purpose="steering", level="signatures",
                paths=[f"theories/{n}.thy" for n in chosen], subjects=sorted(named),
                deepens=[n for n in chosen if n in levels])
    roles = forking_roles(who)
    return dict(roles=sorted(roles), tasks=[str(t["id"]) for t in current_tasks(roles, tasks, state)], tiers=[tier],
                chosen=tier["paths"], plan_parts=parts, unresolved_plan_parts=[p for p, ns in parts.items() if not ns],
                relation_boundary="Explicit source references and direct imports, not a semantic dependency proof.")


def task_relations(who, description, held=None, lib=None):
    """A task's own relations, at the depth the base's roles use each: what the theories its brief names stand on
    (suppliers: statements on high, definitions on xhigh), those theories themselves (subjects, at signatures: the
    session reads what it edits in full) and what uses them (direct consumers, at signatures: the distinctions their
    users need). Each is left out where the session's base already holds it at that depth or deeper."""
    lib = lib or library()
    targets = names_in(description, lib["owners"], lib["by_rel"])
    suppliers = set().union(*(set(lib["refs"][t]) for t in targets)) if targets else set()
    consumers = {n for n, rs in lib["refs"].items() if targets.intersection(rs)} - targets
    levels = dict(held_levels(who) if held is None else held)
    tiers = []
    for relation, depth, names in (("supplier contracts" if who == "high" else "supplier meanings",
                                    SUPPLIER_DEPTH[who], suppliers),
                                   ("work subjects", "signatures", targets),
                                   ("direct consumers", "signatures", consumers)):
        chosen = sorted(n for n in names if deeper(depth, levels.get(n)))
        tiers.append(dict(relation=relation, level=depth, names=chosen, held=sorted(set(names) - set(chosen))))
        levels.update({n: depth for n in chosen})
    return dict(targets=sorted(targets), suppliers=sorted(suppliers), consumers=sorted(consumers), tiers=tiers)


def relations_texts(relations, lib=None, tree=None):
    """[(theory, relation, depth, text)] of a task's relations, each as the task's tree holds it now."""
    lib = lib or library()
    out = []
    for tier in relations["tiers"]:
        for name in tier["names"]:
            path = os.path.join(tree, "theories", f"{name}.thy") if tree else lib["thys"][name]
            if not os.path.isfile(path):
                path = lib["thys"][name]
            out.append((name, tier["relation"], tier["level"], held_text(path, tier["level"])[0]))
    return out


def concurrent_work(tid, relations, tasks=None, state=None, lib=None):
    """[(task, stage, its subjects, how they relate to this task)] for the other current tasks whose subjects are this
    task's subjects, suppliers or consumers: work that may change what this one stands on, or be changed by it, from a
    branch this session does not see (tasks 72, 173 and 221 re-made content a sibling was introducing, 2026-09-22)."""
    import v2
    lib = lib or library()
    state = v2.peek() if state is None else state
    mine = {"subjects": set(relations["targets"]), "suppliers": set(relations["suppliers"]),
            "consumers": set(relations["consumers"])}
    out = []
    for task in current_tasks(set(v2.LAYERABLE), tasks, state):
        if str(task["id"]) == str(tid):
            continue
        theirs = names_in(task.get("description", ""), lib["owners"], lib["by_rel"])
        how = [f"{label}: {', '.join(sorted(theirs & names))}" for label, names in mine.items() if theirs & names]
        if how:
            stage = ((state.get("tasks") or {}).get(str(task["id"])) or {}).get("stage") or "queued"
            out.append((str(task["id"]), stage, sorted(theirs), "; ".join(how)))
    return out


# ---------------------------------------------------------------- the list

def frontier_choice(who):
    """The generated relation block the list holds, and the one the relations call for now."""
    path = list_path(who)
    text = open(path).read()
    choice = relation_choice(who, text=text)
    if RELATIONS_START in text:
        a, b = text.index(RELATIONS_START), text.index(RELATIONS_END) + len(RELATIONS_END)
        was = [line.split("  #")[0].strip() for line in text[a:b].splitlines()
               if line.strip() and not line.startswith("#")]
        return dict(choice, path=path, text=text, start=a, end=b, was=was)
    head = re.search(rf"^{re.escape(FRONTIER_HEAD)}.*$", text, re.M)
    if not head:
        return dict(choice, path=path, text=text, start=len(text), end=len(text), was=[], chosen=[],
                    left="no generated relation tier; the supplied list is retained")
    after = text[head.end():]
    following = re.search(r"^# ", after, re.M)
    end = head.end() + (following.start() if following else len(after))
    was = [ln.split("  #")[0].strip() for ln in text[head.end():end].splitlines()]
    return dict(choice, path=path, text=text, start=head.start(), end=end,
                was=[ln for ln in was if ln and not ln.startswith("#")])


def frontier_text(choice):
    block = [RELATIONS_START]
    for tier in choice["tiers"]:
        block.append(f"# relation: {tier['relation']}; purpose={tier['purpose']}; as {tier['level']}")
        block.extend(tier["paths"])
    block.append(RELATIONS_END)
    return "\n".join(block) + "\n"


def frontier(who, dry_run=False):
    """Write the relation block the list calls for now (base_stack.build writes it into its candidate list, which
    becomes the base's list only when the chain it describes is published)."""
    c = frontier_choice(who)
    if c.get("left"):
        print(f"{who}: {c['left']}")
        return 0
    entries = [(t["relation"], os.path.join(PROJECT, p), t["level"]) for t in c["tiers"] for p in t["paths"]]
    print(f"{who}: {len(c['chosen'])} relation-selected entries; ~{estimate(entries):,} tokens; "
          "no usage ranking or token ceiling")
    if not dry_run:
        open(c["path"], "w").write(c["text"][:c["start"]] + frontier_text(c) + c["text"][c["end"]:].lstrip("\n"))
    return 0


def delivery_tokens(who, task, lib=None, held=None):
    """The tokens a task's sessions on this base are given of its relations (v2.relations_read gives them)."""
    lib = lib or library()
    relations = task_relations(who, task.get("description", ""), held=held, lib=lib)
    total = 0
    for name, _, level, text in relations_texts(relations, lib):
        total += text_tokens(lib["thys"][name], text)[0]
    return total


def projection(who):
    """The exact proposed list, sized without writing any list or generated file, with what each current task of the
    base's roles would be given of its own relations as it starts."""
    import v2
    c = frontier_choice(who)
    text = c["text"] if c.get("left") else c["text"][:c["start"]] + frontier_text(c) + c["text"][c["end"]:]
    directory = os.environ.get("ORCH_HELD_DIR") or os.path.join(PROJECT, ".claude", "orchestration", "state", "held")
    virtual = {}
    generated = (("theory-map-index.md", lambda: theory_map_index(False)), ("tool-index.md", lambda: tool_index(False)),
                 ("decisions-index.md", lambda: decisions_index(False)), ("plan-index.md", lambda: plan_index(False)),
                 ("library-practice.md", lambda: practice(False)),
                 (generated_name("theory-map-index", who), lambda: theory_map_index(False, who, text)),
                 (generated_name("tool-index", who), lambda: tool_index(False, who, text)),
                 (generated_name("library-practice", who), lambda: practice(False, who)))
    for name, make in generated:
        if name in text:
            virtual[os.path.join(directory, name)] = make()
    entries = manifest.list_entries(text, PROJECT, virtual=virtual)
    parts = []
    for part in dict.fromkeys(e["part"] for e in entries):
        es = [e for e in entries if e["part"] == part]
        size = 0
        for e in es:
            if e["path"] in virtual:
                amount, calls = text_tokens(e["path"], virtual[e["path"]])
                size += int(amount + CALL_TOKENS * calls)
            else:
                size += estimate([(e["tier"], e["path"], e["level"])])
        parts.append(dict(part=part, tokens=size + (SESSION_TOKENS if part == "stable" else 0),
                          purposes=sorted({e["purpose"] for e in es}), files=len(es)))
    stable = sum(p["tokens"] for p in parts if p["part"] == "stable")
    layer = sum(p["tokens"] for p in parts if p["part"] != "stable")
    deliveries = []
    if who in SUPPLIER_DEPTH and who != "max":
        lib, held = library(), held_levels(who, text)
        for task in current_tasks(forking_roles(who)):
            deliveries.append(dict(task=str(task["id"]), tokens=delivery_tokens(who, task, lib, held)))
    return dict(stable=stable, layer=layer, total=stable + layer, parts=parts,
                frontier=dict(new=len(set(c["chosen"]) - set(c["was"])), dropped=len(set(c["was"]) - set(c["chosen"]))),
                tasks=c["tasks"], plan_parts=c["plan_parts"], unresolved_plan_parts=c["unresolved_plan_parts"],
                deliveries=deliveries, room_before_reasoning=v2.SOFT - stable - layer - v2.PROTOCOL_ROOM,
                reasoning="unmeasured until built")


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--frontier", choices=sorted(manifest.LISTS))
    group.add_argument("--projection", choices=sorted(manifest.LISTS))
    group.add_argument("--refresh-index", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    if args.refresh_index:
        if not args.dry_run:
            refresh_indexes()
        return 0
    if args.projection:
        print(json.dumps(projection(args.projection), indent=2))
        return 0
    return frontier(args.frontier, args.dry_run)


if __name__ == "__main__":
    raise SystemExit(main())
