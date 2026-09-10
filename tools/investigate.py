#!/usr/bin/env python3
"""Execute the proved finite investigation functions and retain exact run evidence."""
from __future__ import annotations

import argparse
import copy
from contextlib import contextmanager
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import signal
import sys
import tempfile
import time
import uuid

import build

ROOT = Path(__file__).resolve().parents[1]
ENGINE_THEORY = "Presentation_Completion_Investigation"
SCHEMA = "finite-investigation-1"

# Each registered case fixes its source theory, export, and independent scope.
BUILTIN_CASES = {
    "observation_scope": {
        "theory": "Factor_Observation_Scope_Investigation",
        "function": "scope_investigation",
        "help": "Compare native table traversal with complete declared scope admission",
        "question": "Do the selected native decisions distinguish complete observation input admission?",
        "scope": {
            "candidates": {
                "0": "Valid empty table",
                "1": "Empty table with a formed reference in the candidate list",
                "2": "Empty table with a formed reference in the available facet list",
                "3": "Empty table with a selected facet outside the available set",
                "4": "Unused table row outside the available facets",
                "5": "Unused table row outside the declared candidates",
                "6": "Valid nonempty table with no selected observations"
            },
            "facets": {
                "0": "Acceptance by the actual native context list of scoped rows",
                "1": "Acceptance by the native context admission and complete scoped row traversal"
            },
            "values": "The actual Boolean decision: False=0, True=1",
            "comparison": "Equality of complete input admission, independently specified by data domains, the original finite table formation, and selected facet inclusion",
            "coverage": "These seven complete inputs, including empty tables and unused invalid scope fields"
        },
        "semantic_boundary": "Each observation is defined by its actual native call. The independent comparison uses data domains, the original finite observation table formation, and selected-facet inclusion. The complete operation reuses a generic context-admission clause. These executions use proved code equations; native checking of mathematical proofs remains separate."
    },
    "observation": {
        "theory": "Factor_Observation_Investigation",
        "function": "observation_investigation",
        "help": "Compare output presentations of an actual native observation profile",
        "question": "Do the selected native decisions preserve the represented observation set?",
        "scope": {
            "candidates": {
                "0": "The profile in table order",
                "1": "The same profile in reverse order",
                "2": "The same profile with its first row repeated",
                "3": "A different result with the second profile row missing",
            },
            "facets": {
                "0": "Acceptance by the actual ordered native profile operation",
                "1": "Acceptance by the native profile result with a private computation and set comparison",
            },
            "values": "The actual Boolean decision: False=0, True=1",
            "comparison": "Equality of the sets of actual output rows",
            "coverage": "These four output lists for the two-row observation table defined in the source theory",
        },
        "semantic_boundary": (
            "The source theory defines each observation by an actual native operation and proves its code "
            "equation. The comparison independently takes the sets of the output lists. This run executes "
            "those proved finite equations; it does not evaluate arbitrary native programs or check their "
            "mathematical proofs natively."
        ),
    },
    "completion": {
        "theory": "Presentation_Completion_Investigation",
        "function": "completion_investigation",
        "help": "Compute and compare the linked completion example",
        "question": "Do the selected observations distinguish joint completion feasibility?",
        "scope": {
            "candidates": {
                "0": "identity paired with identity",
                "1": "identity paired with negation",
            },
            "facets": {
                "0": "first test has a witness",
                "1": "second test has a witness",
                "2": "both tests share a witness",
            },
            "domain": "All Boolean presentations of one unit subject",
            "comparison": "Preservation of joint feasibility",
        },
    },
    "permission": {
        "theory": "Factor_Permission_Investigation",
        "function": "permission_investigation",
        "help": "Compute actual program formation and truth observations",
        "question": "Do the selected facets preserve complete formation and truth decisions?",
        "scope": {
            "candidates": {
                "0": "narrow interface, empty clause family",
                "1": "variable interface, empty clause family",
                "2": "variable-interface recognizer",
            },
            "arguments": {
                "0": "Payload_Term []",
                "1": "Pair_Term (Payload_Term []) (Payload_Term [])",
            },
            "facets": {
                "0": "call formation",
                "1": "positive truth",
            },
            "values": "Twice the argument index plus its Boolean outcome (False=0, True=1)",
            "comparison": "Equal formation and truth at both supplied arguments",
            "coverage": "These three actual program forms and these two argument values",
        },
        "semantic_boundary": (
            "The exported theory computes the actual program observations using proved equations. Its "
            "table and comparison contracts cover precisely the stated finite scope. The general proof "
            "separately establishes the necessity of both facets for all formed program entries."
        ),
    },
    "pattern": {
        "theory": "Factor_Substitution_Investigation",
        "function": "pattern_investigation",
        "help": "Compute actual substitutions and their two marker observations",
        "question": "Do the selected probes determine the actual substituted patterns?",
        "scope": {
            "replacements": {
                "0": "Pattern_Variable 0",
                "1": "Pattern_Variable 1",
                "2": "Pattern_Payload [0]",
                "3": "Pattern_Payload [1]",
                "4": "Pattern_Target (Whole_Artifact empty_artifact)",
            },
            "template": "Pair of two occurrences of one source variable",
            "facets": {
                "0": "payload marker evaluation",
                "1": "constant target marker evaluation",
            },
            "marker_assignment": "Variable a has payload marker [a]",
            "values": (
                "Codes 0, 1, and 2 encode the resulting repeated pairs of Payload [0], Payload [1], "
                "and the fixed target"
            ),
            "comparison": "Equality of the five actual substituted patterns",
            "coverage": "These five replacements in the repeated-variable pair template",
        },
        "semantic_boundary": (
            "The exported theory performs the substitutions and pattern evaluations. The observation "
            "table, comparison, and output codec have exact contracts for this finite scope. The "
            "separate general theorem determines arbitrary scoped pattern syntax; this execution does "
            "not run an arbitrary native program or check its universal mathematical contracts."
        ),
    },
    "proof_probes": {
        "theory": "Factor_Proof_Probe_Investigation",
        "function": "proof_probes_investigation",
        "help": "Compare finite call probes with complete program decisions",
        "question": "Do the selected call probes determine complete formation and truth agreement?",
        "scope": {
            "candidates": {
                "0": "The existing finite-relation program containing exactly the two marker terms",
                "1": "The existing pattern-family program with one variable recognizer",
            },
            "facets": {
                "0": "Payload_Term [0]",
                "1": "Target_Term (Whole_Artifact empty_artifact)",
                "2": "Pair_Term (Payload_Term [0]) (Payload_Term [0])",
            },
            "values": "Twice the call-formation outcome plus the positive-truth outcome (False=0, True=1)",
            "comparison": "Equal formation and positive truth on every formed term",
            "coverage": (
                "These two fixed actual programs; the three probes form a complete basis for this "
                "family"
            ),
        },
        "semantic_boundary": (
            "The exported observations use proved code equations for the existing programs. The "
            "intended comparison quantifies over every formed term and has a proved decision equation "
            "for this two-program family. A separate theorem shows that any finite collection of "
            "positive probes can miss a difference between finite programs. This execution does not "
            "infer universal truth for an arbitrary program from sample calls."
        ),
    },
    "schema_sockets": {
        "theory": "Factor_Schema_Socket_Investigation",
        "function": "schema_sockets_investigation",
        "help": "Compare exact substitutions with socket-free schema observations",
        "question": "Do the selected observations determine an actual substitution between these linked schemas?",
        "scope": {
            "candidates": {
                "0": "The existing native incidence schema with material socket [18]",
                "1": "The same schema with material socket [19]",
            },
            "facets": {
                "0": "The complete conclusion pattern",
                "1": "The unkeyed material operand values at every valuation",
                "2": "The actual material socket coordinate",
            },
            "values": "The first two facets have value 0; the socket facet has value 18 or 19, with exact equations proved for this case",
            "comparison": "Existence of a pattern substitution from the first actual schema to the second",
            "coverage": "These two socket variants of the existing native incidence schema",
        },
        "semantic_boundary": (
            "The candidates have the same complete rule-instance relation and the same unkeyed material "
            "values at every valuation. Actual substitution retains the socket coordinate. Proved code "
            "equations determine that relation for these two schemas; this finite comparison does not "
            "search arbitrary schemas or infer universal observations from sample valuations."
        ),
    },
}


def builtin_case(kind: str, selected: list[int], collapsed: bool = False) -> dict:
    descriptor = BUILTIN_CASES[kind]
    case = {"schema": SCHEMA, "kind": kind, "selected": selected,
            "question": descriptor["question"], "scope": copy.deepcopy(descriptor["scope"])}
    if "semantic_boundary" in descriptor:
        case["semantic_boundary"] = descriptor["semantic_boundary"]
    if kind == "pattern":
        case["collapsed"] = collapsed
        case["scope"]["marker_assignment"] = "All payload markers are [0]" if collapsed else "Variable a has payload marker [a]"
    return case


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_hash(path: Path) -> str:
    return digest(path.read_bytes())


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def natural(value) -> bool:
    return type(value) is int and value >= 0


def rows(value, width: int) -> bool:
    return isinstance(value, list) and all(isinstance(row, list) and len(row) == width
        and all(natural(x) for x in row) for row in value)


def validate_case(case: dict) -> None:
    require(isinstance(case, dict) and case.get("schema") == SCHEMA, "Unsupported case schema.")
    require(isinstance(case.get("question"), str) and bool(case["question"].strip()), "A question is required.")
    require(isinstance(case.get("scope"), (str, dict)) and bool(case["scope"]), "An explicit scope is required.")
    kind = case.get("kind")
    if kind == "inference":
        require(isinstance(case.get("rules"), list), "rules must be a list.")
        for rule in case["rules"]:
            require(isinstance(rule, dict) and natural(rule.get("conclusion"))
                and rows(rule.get("premises"), 2), "Each rule needs a natural conclusion and premise pairs.")
        require(isinstance(case.get("known"), list) and all(natural(x) for x in case["known"]),
                "known must contain natural identifiers.")
        require(rows(case.get("goals"), 2), "goals must contain occurrence/condition pairs.")
        if "conditions" in case:
            conditions = case["conditions"]
            require(isinstance(conditions, list) and all(isinstance(c, dict) and natural(c.get("id"))
                for c in conditions), "conditions must contain identified objects.")
            ids = {c["id"] for c in conditions}
            require(len(ids) == len(conditions), "Condition identifiers must be unique.")
            used = set(case["known"]) | {a for _, a in case["goals"]}
            for rule in case["rules"]:
                used.add(rule["conclusion"])
                used.update(a for _, a in rule["premises"])
            require(used <= ids, "Every used condition must have metadata when conditions are supplied.")
    elif kind == "basis":
        for name in ("candidates", "facets", "selected"):
            require(isinstance(case.get(name), list) and all(natural(x) for x in case[name]),
                    f"{name} must contain natural identifiers.")
        require(rows(case.get("observations"), 3), "observations must contain facet/candidate/value triples.")
        require(rows(case.get("relation"), 2), "relation must contain candidate pairs.")
        require(all(c in case["candidates"] and d in case["candidates"] for c, d in case["relation"]),
                "Comparison pairs must lie in the supplied candidate domain.")
    elif kind in BUILTIN_CASES:
        require(isinstance(case.get("selected"), list) and all(natural(x) for x in case["selected"]),
                "selected must contain natural facet identifiers.")
        if kind == "pattern":
            require(type(case.get("collapsed")) is bool, "collapsed must be Boolean.")
    else:
        raise ValueError("kind must be inference, basis, or a registered case: " + ", ".join(BUILTIN_CASES))
    evidence = case.get("evidence", [])
    require(isinstance(evidence, list), "evidence must be a list.")
    for item in evidence:
        require(isinstance(item, dict) and isinstance(item.get("path"), str)
            and Path(item["path"]).is_absolute() and isinstance(item.get("sha256"), str)
            and re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) is not None,
            "Evidence entries need absolute paths and SHA-256 digests.")


def verify_evidence(case: dict) -> None:
    for item in case.get("evidence", []):
        require(file_hash(Path(item["path"])) == item["sha256"], f"Evidence changed: {item['path']}")


def theory_imports(source: str, name: str) -> list[str]:
    # Only this repository's deliberately simple theory headers are accepted.
    # No declaration, proof body, or arbitrary Isabelle syntax is parsed here.
    match = re.match(r"\s*theory\s+([A-Za-z_][A-Za-z_0-9]*)\s+imports\s+([\s\S]*?)\s+begin\b", source)
    require(match is not None and match[1] == name, f"Unsupported theory header: {name}")
    tokens = re.findall(r'"[A-Za-z_][A-Za-z_0-9./-]*"|[A-Za-z_][A-Za-z_0-9.-]*', match[2])
    require("".join(tokens) == re.sub(r"\s+", "", match[2]), f"Unsupported imports in {name}")
    return [token.strip('"') for token in tokens]


def source_graph(project: Path, overlays: list[Path], roots: list[str]) -> tuple[dict, dict]:
    inventory = {p.stem: p for p in (project / "theories").glob("*.thy")}
    for directory in overlays:
        require(directory.is_dir(), f"Missing overlay directory: {directory}")
        inventory.update({p.stem: p for p in directory.glob("*.thy")})
    sources, parents, active = {}, {}, set()

    def visit(name: str) -> None:
        if name in active:
            raise ValueError(f"Cyclic theory import: {name}")
        if name in sources:
            return
        if name not in inventory:
            require(name in {"Main", "HOL", "Pure"} or name.startswith(("HOL.", "HOL-Library.")),
                    f"Missing local theory: {name}")
            return
        active.add(name)
        path = inventory[name].resolve()
        data = path.read_bytes()
        imported = theory_imports(data.decode("utf-8"), name)
        for parent in imported:
            visit(parent)
        active.remove(name)
        parents[name] = imported
        sources[name] = {"path": str(path), "sha256": digest(data), "text": data.decode("utf-8")}

    for root in roots:
        require(root in inventory, f"Missing requested theory: {root}")
        visit(root)
    return sources, parents


def import_context(parents: dict, name: str) -> set[str]:
    result = set()

    def visit(node):
        if node in result or node not in parents:
            return
        result.add(node)
        for parent in parents[node]:
            visit(parent)

    visit(name)
    return result


def source_case(args) -> dict:
    project = args.project.resolve()
    receipt_path = (args.accepted_receipt or project / "validation/build.json").resolve()
    receipt_bytes = receipt_path.read_bytes()
    accepted = json.loads(receipt_bytes)
    require(accepted.get("status") == "accepted" and accepted.get("exit_code") == 0
        and accepted.get("sources_unchanged") is True and accepted.get("tools_unchanged") is True,
        "Source readiness requires an accepted, stable build receipt.")
    require(isinstance(accepted.get("sources"), dict), "The build receipt lacks source digests.")
    sources, parents = source_graph(project, args.overlay, args.roots)
    names = sorted(sources)
    ids = {name: i for i, name in enumerate(names)}
    conditions, rules, known = [], [], []
    for name in names:
        context = import_context(parents, name)
        matches = all(accepted["sources"].get(f"theories/{n}.thy") == sources[n]["sha256"] for n in context)
        conditions.append({"id": ids[name], "theory": name, "meaning": "This exact complete theory context has accepted proof evidence",
            "accepted_with_context": matches, "complete_import_context": sorted(context),
            "path": sources[name]["path"], "sha256": sources[name]["sha256"]})
        if matches:
            known.append(ids[name])
        else:
            local = len(names) + ids[name]
            conditions.append({"id": local, "theory": name, "status": "unresolved",
                "meaning": "The local declarations and proofs check in precisely the specified parent contexts",
                "path": sources[name]["path"], "sha256": sources[name]["sha256"]})
            premises = [[0, local]] + [[i + 1, ids[p]] for i, p in enumerate(parents[name]) if p in ids]
            rules.append({"conclusion": ids[name], "premises": premises,
                "source": {"theory": name, "relation": "Local proof checking and all exact parent contexts establish the complete context"}})
    return {"schema": SCHEMA, "kind": "inference", "question": "Which exact proof-context conditions remain for the requested sources?",
        "scope": {"roots": args.roots, "complete_for": "These finite local import closures",
            "external_context": {"base": accepted.get("base_session"), "isabelle_version": accepted.get("isabelle_version")}},
        "semantic_boundary": "This is conditional proof-source readiness. Import edges and source presence do not prove declarations. Local checks may be discharged together by one accepted session.",
        "accepted_receipt": {"path": str(receipt_path), "sha256": digest(receipt_bytes), "invocation": accepted.get("invocation")},
        "evidence": [{"path": s["path"], "sha256": s["sha256"]} for s in sources.values()]
            + [{"path": str(receipt_path), "sha256": digest(receipt_bytes)}],
        "conditions": conditions, "known": known, "rules": rules,
        "goals": [[i, ids[name]] for i, name in enumerate(args.roots)]}


class CommandTimeout(Exception):
    pass


@contextmanager
def deadline(seconds: float):
    def expired(_signum, _frame):
        raise CommandTimeout(f"Command exceeded {seconds:g} seconds.")

    previous = signal.signal(signal.SIGALRM, expired)
    signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous)


@contextmanager
def locked(path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a") as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        yield


def run_command(command: list[str], args, receipt: dict, log, seconds: float, *, check: bool = True) -> str:
    step = {"command": command, "started_utc": build.utc_now(), "status": "running"}
    receipt.setdefault("commands", []).append(step)
    started = time.monotonic()
    try:
        with deadline(seconds):
            code, output = build.run_command(command, args.environment, log, display=False)
        step.update(exit_code=code, status="finished" if code == 0 else "failed")
        if check:
            require(code == 0, f"Command exited with {code}: {' '.join(command)}")
        return output
    except BaseException as error:
        step.update(status="interrupted" if isinstance(error, (build.RunInterrupted, KeyboardInterrupt))
                    else "timed_out" if isinstance(error, CommandTimeout) else "failed", error=str(error))
        raise
    finally:
        step.update(finished_utc=build.utc_now(), elapsed_seconds=time.monotonic() - started)


def current_sources(sources: dict) -> bool:
    return all(file_hash(Path(item["path"])) == item["sha256"] for item in sources.values())


def prepare_engine(args, receipt: dict, output: Path, log, kind: str) -> tuple[Path, Path, dict]:
    version = run_command([args.isabelle, "version"], args, receipt, log, 30).strip()
    engine_theory = BUILTIN_CASES[kind]["theory"] if kind in BUILTIN_CASES else ENGINE_THEORY
    sources, _ = source_graph(ROOT, [], [engine_theory])
    tool_paths = [Path(__file__).resolve(), Path(build.__file__).resolve()]
    tool_hashes = {str(path): file_hash(path) for path in tool_paths}
    material = {"sources": {name: item["sha256"] for name, item in sources.items()},
                "tools": tool_hashes, "isabelle_version": version, "engine_theory": engine_theory}
    key = digest(json.dumps(material, sort_keys=True).encode())
    session = "Finite_Investigation_" + key[:24]
    snapshot = args.engine_cache.resolve() / key
    root_text = (f"session {session} = HOL +\n  options [document = false]\n"
                 f'  sessions "HOL-Library"\n  directories "theories"\n  theories {engine_theory}\n')
    expected = {"ROOT": root_text, **{f"theories/{name}.thy": item["text"] for name, item in sources.items()}}
    receipt.update(engine_key=key, isabelle_version=version, engine_session=session, engine_theory=engine_theory,
        engine_sources={name: {k: v for k, v in item.items() if k != "text"} for name, item in sources.items()},
        tools=tool_hashes, engine_snapshot=str(snapshot))
    with locked(args.engine_cache.resolve() / (key + ".lock")):
        snapshot.mkdir(parents=True, exist_ok=True)
        for name, text in expected.items():
            path = snapshot / name
            if path.exists():
                require(path.read_text() == text, f"Engine snapshot changed: {path}")
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
        snapshot_hashes = {name: digest(text.encode()) for name, text in expected.items()}
        command = [args.isabelle, "build", "-v", "-o", f"threads={args.threads}",
                   "-o", f"timeout={args.build_timeout:g}", "-D", str(snapshot)]
        try:
            run_command(command, args, receipt, log, args.build_timeout + 30)
        except ValueError:
            # Query only the actual session whose build was attempted here.
            try:
                receipt["session_diagnostics"] = run_command(
                    [args.isabelle, "build_log", "-H", "Error", session], args, receipt, log, 30, check=False)
            except Exception as error:
                receipt["diagnostic_error"] = str(error)
            raise
        require(current_sources(sources), "Engine sources changed during proof checking.")
        require(all(file_hash(Path(p)) == h for p, h in tool_hashes.items()), "Investigation tools changed during proof checking.")
        require(all(file_hash(snapshot / p) == h for p, h in snapshot_hashes.items()), "Proof snapshot changed during checking.")
        proof = {"status": "accepted", "invocation": receipt["invocation"], "session": session,
            "isabelle_version": version, "sources": snapshot_hashes, "engine_key": key,
            "meaning": "The complete engine dependency session succeeded in this invocation before export."}
        build.atomic_json(output / "proof.json", proof)
        receipt["proof_receipt_sha256"] = file_hash(output / "proof.json")
        export_dir = output / ("export-" + receipt["invocation"])
        run_command([args.isabelle, "export", "-n", "-d", str(snapshot), "-O", str(export_dir),
                     "-x", f"*{engine_theory}:code/finite_investigation.ML", session], args, receipt, log, 60)
        blobs = list(export_dir.rglob("finite_investigation.ML"))
        require(len(blobs) == 1, "Expected exactly one generated investigation module.")
        engine = blobs[0]
        require(current_sources(sources) and all(file_hash(snapshot / p) == h for p, h in snapshot_hashes.items()),
                "Engine sources changed during export.")
        receipt.update(generated_engine=str(engine), generated_engine_sha256=file_hash(engine),
                       proof_snapshot_hashes=snapshot_hashes)
    if args.poly:
        poly = args.poly.resolve()
    else:
        poly_home = run_command([args.isabelle, "getenv", "-b", "POLYML_HOME"], args, receipt, log, 30).strip()
        require(bool(poly_home), "Isabelle did not identify its Poly/ML installation; pass --poly.")
        poly = Path(poly_home) / (platform.machine() + "-linux") / "poly"
    require(poly.is_file() and os.access(poly, os.X_OK), f"Missing executable Poly/ML: {poly}")
    receipt.update(poly=str(poly), poly_sha256=file_hash(poly))
    receipt["poly_version"] = run_command([str(poly), "--version"], args, receipt, log, 30).strip()
    return engine, poly, sources


def ml_string(value: str) -> str:
    return '"' + "".join(f"\\{byte:03d}" for byte in value.encode("utf-8")) + '"'


def ml_list(values, encode) -> str:
    return "[" + ",".join(encode(value) for value in values) + "]"


def ml_nat(value: int) -> str:
    require(natural(value), "Only natural numbers can be passed as identifiers.")
    return f"n {value}"


def ml_tuple(values) -> str:
    # Isabelle tuples associate to the right; SML tuples do not.
    if len(values) == 2:
        return "(" + ml_nat(values[0]) + "," + ml_nat(values[1]) + ")"
    return "(" + ml_nat(values[0]) + "," + ml_tuple(values[1:]) + ")"


def runtime_program(case: dict, engine: Path) -> str:
    prelude = "use " + ml_string(str(engine)) + ";\n" + r'''
val n = Finite_Investigation.nat_of_integer;
fun jnat x = IntInf.toString (Finite_Investigation.integer_of_nat x);
fun jlist f xs = "[" ^ String.concatWith "," (map f xs) ^ "]";
fun jpair (a,b) = "[" ^ jnat a ^ "," ^ jnat b ^ "]";
fun jtriple (a,(b,c)) = "[" ^ jnat a ^ "," ^ jnat b ^ "," ^ jnat c ^ "]";
fun jquad (a,(b,(c,d))) = "[" ^ jnat a ^ "," ^ jnat b ^ "," ^ jnat c ^ "," ^ jnat d ^ "]";
fun jreason (a,(h,(i,b))) =
  "{\"conclusion\":" ^ jnat a ^ ",\"premises\":" ^ jlist jpair h ^
  ",\"premise\":" ^ jnat i ^ ",\"condition\":" ^ jnat b ^ "}";
fun jprofile (c,p) = "{\"candidate\":" ^ jnat c ^ ",\"profile\":" ^ jlist jpair p ^ "}";
fun jloss (c,(d,p)) = "{\"from\":" ^ jnat c ^ ",\"to\":" ^ jnat d ^ ",\"losses\":" ^ jlist jpair p ^ "}";
'''
    if case["kind"] == "inference":
        rules = ml_list(case["rules"], lambda r: "(" + ml_nat(r["conclusion"]) + ","
                        + ml_list(r["premises"], ml_tuple) + ")")
        call = "Finite_Investigation.investigation_inference " + rules + " " + ml_list(case["known"], ml_nat)
        call += " " + ml_list(case["goals"], ml_tuple)
        return prelude + "val (formed,(residual,(demand,reasons))) = " + call + ";\n" + r'''
val result = "{\"input_formed\":" ^ Bool.toString formed ^
  ",\"residual\":" ^ jlist jpair residual ^ ",\"demand\":" ^ jlist jnat demand ^
  ",\"reasons\":" ^ jlist jreason reasons ^ "}";
print ("INVESTIGATION_RESULT " ^ result ^ "\n");
'''

    if case["kind"] in BUILTIN_CASES:
        function = "Finite_Investigation." + BUILTIN_CASES[case["kind"]]["function"]
        parameter = ("true " if case["collapsed"] else "false ") if case["kind"] == "pattern" else ""
        call = function + " " + parameter + ml_list(case["selected"], ml_nat)
        observations = function + "_observations" + (" " + parameter.strip() if parameter else "")
        facets = [int(f) for f in BUILTIN_CASES[case["kind"]]["scope"]["facets"]]
        repair_args = " ".join(["(map #1 profiles)", ml_list(facets, ml_nat),
                                ml_list(case["selected"], ml_nat), "observations", "relation"])
        extra = ("val observations = " + observations + ";\n"
                 "val relation = " + function + "_relation;\n"
                 'val supplied = ",\\\"observations\\\":" ^ jlist jtriple observations ^\n'
                 '  ",\\\"relation\\\":" ^ jlist jpair relation;\n')
    else:
        call = "Finite_Investigation.investigation_basis " + " ".join([
            ml_list(case[name], ml_nat) for name in ("candidates", "facets", "selected")])
        call += " " + ml_list(case["observations"], ml_tuple) + " " + ml_list(case["relation"], ml_tuple)
        repair_args = call.removeprefix("Finite_Investigation.investigation_basis ")
        extra = 'val supplied = "";\n'
    extra += "val (safe_facets,(conflicts,(repairs,unrepairable))) = Finite_Investigation.investigation_repairs " + repair_args + ";\n"
    extra += "val extension = Finite_Investigation.investigation_extend " + ml_list(case["selected"], ml_nat) + " repairs;\n"
    return prelude + "val (formed,(residual,(profiles,losses))) = " + call + ";\n" + extra + r'''
val result = "{\"input_formed\":" ^ Bool.toString formed ^
  ",\"residual\":" ^ jlist jpair residual ^ ",\"profiles\":" ^ jlist jprofile profiles ^
  ",\"losses\":" ^ jlist jloss losses ^
  ",\"safe_facets\":" ^ jlist jnat safe_facets ^ ",\"conflicts\":" ^ jlist jquad conflicts ^
  ",\"repairs\":" ^ jlist jquad repairs ^ ",\"unrepairable\":" ^ jlist jpair unrepairable ^
  ",\"extension\":" ^ jlist jnat extension ^ supplied ^ "}";
print ("INVESTIGATION_RESULT " ^ result ^ "\n");
'''


def validate_result(result: dict, kind: str) -> None:
    require(isinstance(result, dict) and type(result.get("input_formed")) is bool
        and rows(result.get("residual"), 2), "Malformed evaluator result.")
    if kind == "inference":
        require(isinstance(result.get("demand"), list) and all(natural(x) for x in result["demand"]),
                "Malformed demand result.")
        require(isinstance(result.get("reasons"), list), "Missing reason result.")
        for reason in result["reasons"]:
            require(isinstance(reason, dict) and all(natural(reason.get(k))
                for k in ("conclusion", "premise", "condition")) and rows(reason.get("premises"), 2),
                "Malformed complete reason.")
    else:
        require(isinstance(result.get("profiles"), list) and isinstance(result.get("losses"), list),
                "Missing observation result.")
        require(all(isinstance(p, dict) and natural(p.get("candidate")) and rows(p.get("profile"), 2)
                    for p in result["profiles"]), "Malformed candidate profile.")
        require(all(isinstance(p, dict) and natural(p.get("from")) and natural(p.get("to"))
                    and rows(p.get("losses"), 2) for p in result["losses"]), "Malformed candidate losses.")
        require(isinstance(result.get("safe_facets"), list)
            and all(natural(f) for f in result["safe_facets"])
            and rows(result.get("conflicts"), 4) and rows(result.get("repairs"), 4)
            and rows(result.get("unrepairable"), 2)
            and isinstance(result.get("extension"), list) and all(natural(f) for f in result["extension"]),
            "Malformed repair guidance.")
        if kind in BUILTIN_CASES:
            require(rows(result.get("observations"), 3) and rows(result.get("relation"), 2),
                    "Missing executed observations or relation.")


def run(args, invocation: str, output: Path) -> int:
    receipt_path = output / "receipt.json"
    receipt = {"invocation": invocation, "status": "running", "started_utc": build.utc_now(),
               "exit_code": 1, "role": "Execution evidence with separately qualified semantic meaning"}
    build.atomic_json(receipt_path, receipt)
    build.atomic_json(output / "proof.json", {"invocation": invocation, "status": "not_checked"})
    started = time.monotonic()
    try:
        with (output / "run.log").open("w") as log:
            log.write(f"Invocation: {invocation}\n")
            if args.mode == "run":
                raw = args.case.read_bytes()
                case = json.loads(raw)
                receipt["input"] = {"path": str(args.case.resolve()), "sha256": digest(raw)}
            elif args.mode == "sources":
                case = source_case(args)
            else:
                case = builtin_case(args.mode.replace("-", "_"), args.selected, getattr(args, "collapsed", False))
            validate_case(case)
            verify_evidence(case)
            build.atomic_json(output / "case.json", case)
            contract = case
            if case["kind"] in BUILTIN_CASES:
                contract = builtin_case(case["kind"], case["selected"], case.get("collapsed", False))
                descriptor = BUILTIN_CASES[case["kind"]]
                receipt["registered_operation"] = {key: descriptor[key] for key in ("theory", "function")}
            receipt.update(case_sha256=file_hash(output / "case.json"), question=case["question"], scope=contract["scope"],
                semantic_boundary=contract.get("semantic_boundary", "Results are exact for the supplied finite data. Independent meanings, evidence validity, and wider coverage require their own justification."))
            engine, poly, sources = prepare_engine(args, receipt, output, log, case["kind"])
            program = output / "execute.ML"
            program.write_text(runtime_program(case, engine))
            receipt["runtime_program_sha256"] = file_hash(program)
            runtime_started = time.monotonic()
            runtime = run_command([str(poly), "--script", str(program)], args, receipt, log, args.runtime_timeout)
            receipt["runtime_seconds"] = time.monotonic() - runtime_started
            lines = [line[len("INVESTIGATION_RESULT "):] for line in runtime.splitlines()
                     if line.startswith("INVESTIGATION_RESULT ")]
            require(len(lines) == 1, "The runtime must return exactly one result.")
            result = json.loads(lines[0])
            validate_result(result, case["kind"])
            verify_evidence(case)
            require(current_sources(sources), "Engine source changed during execution.")
            require(all(file_hash(Path(p)) == h for p, h in receipt["tools"].items()), "Investigation tool changed during execution.")
            require(file_hash(engine) == receipt["generated_engine_sha256"], "Generated engine changed during execution.")
            require(file_hash(poly) == receipt["poly_sha256"], "Poly/ML executable changed during execution.")
            require(file_hash(program) == receipt["runtime_program_sha256"], "Runtime program changed during execution.")
            require(file_hash(output / "case.json") == receipt["case_sha256"], "Saved case changed during execution.")
            if "input" in receipt:
                require(file_hash(Path(receipt["input"]["path"])) == receipt["input"]["sha256"], "Input case changed during execution.")
            require(file_hash(output / "proof.json") == receipt["proof_receipt_sha256"], "Proof receipt changed during execution.")
            require(all(file_hash(Path(receipt["engine_snapshot"]) / p) == h
                        for p, h in receipt["proof_snapshot_hashes"].items()), "Proof snapshot changed during execution.")
            receipt.update(result=result, sources_and_tools_unchanged=True,
                status="evaluated" if result["input_formed"] else "rejected", exit_code=0 if result["input_formed"] else 2)
            if case["kind"] == "inference" and "conditions" in case:
                labels = {c["id"]: c for c in case["conditions"]}
                receipt["remaining_goals"] = [{"occurrence": i, "condition": labels[c]} for i, c in result["residual"]]
                receipt["unresolved_demand"] = [labels[c] for c in result["demand"] if labels[c].get("status") == "unresolved"]
    except build.RunInterrupted as error:
        receipt.update(status="interrupted", exit_code=128 + error.signum, error=str(error))
    except KeyboardInterrupt:
        receipt.update(status="interrupted", exit_code=130, error="Interrupted.")
    except CommandTimeout as error:
        receipt.update(status="timed_out", exit_code=124, error=str(error))
    except Exception as error:
        receipt.update(status="failed", exit_code=1, error=str(error))
    finally:
        receipt.update(finished_utc=build.utc_now(), elapsed_seconds=time.monotonic() - started)
        if (output / "run.log").exists():
            receipt["log_sha256"] = file_hash(output / "run.log")
        build.atomic_json(receipt_path, receipt)
    summary = {key: receipt[key] for key in ("status", "exit_code", "elapsed_seconds", "runtime_seconds", "error") if key in receipt}
    summary["receipt"] = str(receipt_path)
    if "result" in receipt:
        summary.update(input_formed=receipt["result"]["input_formed"], residual=receipt["result"]["residual"])
        if "demand" in receipt["result"]:
            summary.update(demanded_conditions=len(receipt["result"]["demand"]), reasons=len(receipt["result"]["reasons"]))
        elif "repairs" in receipt["result"]:
            report = receipt["result"]
            summary.update(repair_witnesses=len(report["repairs"]), conflicts=len(report["conflicts"]),
                unrepairable=len(report["unrepairable"]), extension=report["extension"])
    print(json.dumps(summary, indent=2))
    return receipt["exit_code"]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--isabelle", default="isabelle")
    parser.add_argument("--poly", type=Path)
    parser.add_argument("--threads", type=int, default=min(12, os.cpu_count() or 1))
    parser.add_argument("--build-timeout", type=float, default=300)
    parser.add_argument("--runtime-timeout", type=float, default=60)
    parser.add_argument("--cache-home", type=Path, default=Path(tempfile.gettempdir()) / "structural-isabelle")
    parser.add_argument("--engine-cache", type=Path, default=Path(tempfile.gettempdir()) / "structural-investigation-engines")
    parser.add_argument("--output", type=Path, help="Run directory; receipt.json is replaced atomically for this invocation")
    modes = parser.add_subparsers(dest="mode", required=True)
    raw = modes.add_parser("run", help="Execute an inference or observation-basis JSON case")
    raw.add_argument("case", type=Path)
    for kind, descriptor in BUILTIN_CASES.items():
        command = modes.add_parser(kind.replace("_", "-"), help=descriptor["help"])
        command.add_argument("--selected", type=int, nargs="*", default=[0, 1])
        if kind == "pattern":
            command.add_argument("--collapsed", action="store_true", help="Give both target variables the same payload marker")
    sources = modes.add_parser("sources", help="Investigate exact source-context readiness against an accepted build")
    sources.add_argument("roots", nargs="+")
    sources.add_argument("--project", type=Path, default=ROOT)
    sources.add_argument("--overlay", type=Path, action="append", default=[])
    sources.add_argument("--accepted-receipt", type=Path)
    args = parser.parse_args()
    if args.threads < 1 or any(not math.isfinite(t) or t <= 0 for t in (args.build_timeout, args.runtime_timeout)):
        parser.error("Threads and timeouts must be positive.")
    invocation = str(uuid.uuid4())
    output = (args.output or Path(tempfile.gettempdir()) / "structural-investigations" / invocation).resolve()
    if args.mode == "run" and args.case.resolve() in {output / name for name in ("receipt.json", "proof.json", "case.json", "run.log", "execute.ML")}:
        parser.error("Choose an output directory that does not overwrite the input case.")
    output.mkdir(parents=True, exist_ok=True)
    args.environment = os.environ.copy()
    args.environment["USER_HOME"] = str(args.cache_home.resolve())
    with build.interruption_signals(), locked(output / ".lock"):
        return run(args, invocation, output)


if __name__ == "__main__":
    raise SystemExit(main())
