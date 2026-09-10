#!/usr/bin/env python3
"""Execute learned reasoning and independently check its complete finite reports.

The receipt distinguishes structural generation controls from the native
counter and installed-input examples. Arbitrary control libraries have no
asserted semantic soundness contract. Their finite matching is checked here.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import sys

import investigate

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def freeze(value):
    if isinstance(value, dict):
        return tuple((k, freeze(v)) for k, v in sorted(value.items()))
    if isinstance(value, list):
        return tuple(map(freeze, value))
    return value


def payload(*values):
    return {"payload": list(values)}


def pair(a, b):
    return {"pair": [a, b]}


def variable(n):
    return {"var": n}


EMPTY = {"empty_artifact": True}


def counter(n):
    result = payload()
    for _ in range(n):
        result = pair(payload(), result)
    return result


def direct_pair(a, b, n):
    goal = pair(payload(1), pair(pair(payload(0), a), pair(payload(0), b)))
    instruction = pair(n, pair(a, pair(b, payload())))
    return pair(pair(goal, n), pair(n, pair(pair(payload(), n), pair(instruction, payload()))))


def schema(head, premises=(), materials=()):
    return {"head": head, "premises": list(premises), "materials": list(materials)}


def library(entry, rule, enumeration=None):
    return [{"entry": entry, "schema": rule,
             "enumeration": copy.deepcopy(rule["premises"] if enumeration is None else enumeration)}]


def case(name, lib, frontier, known, goals, operation=None):
    return {"name": name, "library": lib, "frontier": frontier, "known": known,
            "goals": goals, "operation": operation}


def cases():
    rule = schema(direct_pair(variable(0), variable(1), variable(2)),
                  [[i, 340, variable(i)] for i in range(3)])
    lib = library(341, rule)
    frontier = [[340, counter(i)] for i in range(3)]
    goal = [0, 341, direct_pair(counter(0), counter(1), counter(2))]
    result = [case("native-stage-" + str(stage), [] if stage == 0 else lib,
                   frontier, frontier[:2] if stage == 1 else frontier, [goal], ["stage", stage])
              for stage in range(3)]
    false_frontier = frontier[:2] + [[340, payload(0)]]
    false_goal = [0, 341, direct_pair(counter(0), counter(1), payload(0))]
    result += [case("native-false-" + str(trust).lower(), lib, false_frontier,
                    false_frontier if trust else frontier[:2], [false_goal], ["false", trust])
               for trust in [False, True]]
    fresh = [[340, counter(i)] for i in [3, 4, 5]]
    result.append(case("future-counter-values", lib, fresh, fresh,
                       [[17, 341, direct_pair(counter(5), counter(3), counter(4))]]))
    result.append(case("reordered-repeated-frontier", lib, frontier[::-1] + frontier,
                       frontier, [goal, [19, goal[1], goal[2]]]))
    x, y = payload(7), payload(8)
    joined = schema(variable(0), [[0, 10, variable(0)], [1, 11, variable(0)]])
    result += [case("shared-variable-" + str(agree).lower(), library(9, joined),
                    [[10, x], [11, x if agree else y]], [[10, x], [11, x if agree else y]], [[0, 9, x]])
               for agree in [False, True]]
    repeated = schema(variable(0), [[0, 10, variable(0)], [1, 10, variable(0)]])
    result.append(case("separate-premise-occurrences", library(9, repeated), [[10, x]], [], [[0, 9, x]]))
    result.append(case("premise-order", library(9, repeated, repeated["premises"][::-1]),
                       [[10, x]], [[10, x]], [[0, 9, x]]))
    result.append(case("repeated-enumeration", library(9, repeated, repeated["premises"] * 2),
                       [[10, x]], [[10, x]], [[0, 9, x]]))
    result.append(case("missing-premise-enumeration", library(9, repeated, repeated["premises"][:1]),
                       [[10, x]], [[10, x]], [[0, 9, x]]))
    result.append(case("extra-premise-enumeration", library(9, repeated, repeated["premises"] + [[2, 10, variable(0)]]),
                       [[10, x]], [[10, x]], [[0, 9, x]]))
    result.append(case("premise-only-variable", library(9, schema(payload(), [[0, 10, variable(8)]])),
                       [[10, x]], [[10, x]], [[0, 9, payload()]]))
    result.append(case("head-variable-without-premise", library(9, schema(variable(8))), [], [], [[0, 9, x]]))
    material = [variable(8), EMPTY, EMPTY, EMPTY, EMPTY]
    result.append(case("material-only-variable", library(9, schema(payload(), [], [[2, material]])),
                       [[10, EMPTY]], [[10, EMPTY]], [[0, 9, payload()]]))
    result.append(case("complete-empty-material", library(9, schema(payload(), [[0, 10, variable(8)]], [[2, material]])),
                       [[10, EMPTY]], [[10, EMPTY]], [[0, 9, payload()]]))
    for field in range(5):
        changed = copy.deepcopy(material)
        changed[field] = payload()
        result.append(case("false-material-field-" + str(field),
                           library(9, schema(payload(), [[0, 10, variable(8)]], [[2, changed]])),
                           [[10, EMPTY]], [[10, EMPTY]], [[0, 9, payload()]]))
    result.append(case("conflicting-premise-socket", library(9,
                       schema(variable(0), [[0, 10, variable(0)], [0, 11, variable(0)]])),
                       [[10, x], [11, x]], [[10, x], [11, x]], [[0, 9, x]]))
    result.append(case("ordinary-material-socket-collision", library(9,
                       schema(payload(), [[0, 10, variable(8)]], [[0, material]])),
                       [[10, EMPTY]], [[10, EMPTY]], [[0, 9, payload()]]))
    base = case("base", library(9, schema(variable(0), [[0, 10, variable(0)]])),
                [[10, x]], [[10, x]], [[0, 9, x]])
    for field in ["library", "frontier", "known", "goals"]:
        changed = copy.deepcopy(base)
        changed["name"] = "malformed-unused-" + field
        changed[field] += (library(99, schema(payload(256))) if field == "library" else
                           [[8, 99, payload(256)]] if field == "goals" else [[99, payload(256)]])
        result.append(changed)
    changed = copy.deepcopy(base)
    changed.update(name="conflicting-goal-socket", goals=[[0, 9, x], [0, 9, y]])
    result.append(changed)
    return result


def variables(pattern):
    if "var" in pattern:
        return {pattern["var"]}
    return set().union(*(variables(p) for p in pattern.get("pair", [])))


def formed(pattern):
    if "payload" in pattern:
        return all(type(n) is int and 0 <= n < 256 for n in pattern["payload"])
    if "pair" in pattern:
        return all(map(formed, pattern["pair"]))
    return "var" in pattern or pattern == EMPTY


def functional(rows):
    return all(a[0] != b[0] or freeze(a[1:]) == freeze(b[1:]) for a in rows for b in rows)


def schema_formed(rule):
    premises, materials = rule["premises"], rule["materials"]
    return (formed(rule["head"]) and functional(premises) and functional(materials)
            and not ({p[0] for p in premises} & {m[0] for m in materials})
            and all(formed(p) for _, _, p in premises)
            and all(all(map(formed, fields)) for _, fields in materials))


def match(pattern, term):
    if "var" in pattern:
        return {pattern["var"]: term}
    if "pair" not in pattern:
        return {} if pattern == term and formed(term) else None
    if "pair" not in term:
        return None
    a, b = [match(p, t) for p, t in zip(pattern["pair"], term["pair"])]
    if a is None or b is None or any(a[v] != b[v] for v in a.keys() & b.keys()):
        return None
    return {**a, **b}


def evaluate(pattern, valuation):
    if "var" in pattern:
        return valuation[pattern["var"]]
    if "pair" in pattern:
        return pair(*(evaluate(p, valuation) for p in pattern["pair"]))
    return pattern


def schema_key(rule):
    return (freeze(rule["head"]), frozenset(map(freeze, rule["premises"])),
            frozenset(map(freeze, rule["materials"])))


def application_key(application):
    return (application["entry"], schema_key(application["schema"]), freeze(application["conclusion"]),
            frozenset(map(freeze, application["bindings"])), frozenset(map(freeze, application["premises"])))


def reconstruct(item):
    applications = []
    available = {freeze(c) for c in item["frontier"]}
    valid_library = True
    for entry in item["library"]:
        rule = entry["schema"]
        valid = schema_formed(rule) and set(map(freeze, entry["enumeration"])) == set(map(freeze, rule["premises"]))
        valid_library &= valid
        if not valid:
            continue
        scope = variables(rule["head"])
        for _, _, p in rule["premises"]:
            scope |= variables(p)
        for _, fields in rule["materials"]:
            for p in fields:
                scope |= variables(p)
        domains = {v: {} for v in scope}
        for _, d, p in rule["premises"]:
            for e, t in item["frontier"]:
                matched = match(p, t) if d == e else None
                if matched is not None:
                    for v, value in matched.items():
                        if formed(value):
                            domains[v][freeze(value)] = value
        ordered = sorted(scope)
        # Enumerate complete valuations, independently of the executor's
        # ordered recursive premise joins, then check every original premise.
        for values in itertools.product(*(domains[v].values() for v in ordered)):
            valuation = dict(zip(ordered, values))
            premises = [[s, d, evaluate(p, valuation)] for s, d, p in rule["premises"]]
            if any(freeze([d, t]) not in available for _, d, t in premises):
                continue
            # This control family uses the exact empty artifact. Its four
            # complete enumerations must all be empty enumeration terms.
            if any([evaluate(p, valuation) for p in fields] != [EMPTY] * 5 for _, fields in rule["materials"]):
                continue
            applications.append({"entry": entry["entry"], "schema": rule,
                                 "conclusion": evaluate(rule["head"], valuation),
                                 "bindings": [[v, valuation[v]] for v in ordered], "premises": premises})
    rules = {(freeze([a["entry"], a["conclusion"]]), frozenset(map(freeze, a["premises"]))) for a in applications}
    known = set(map(freeze, item["known"]))
    reached = set(known)
    while True:
        more = {q for q, h in rules if {(d, t) for s, d, t in h} <= reached}
        if more <= reached:
            break
        reached |= more
    demand = {freeze([d, t]) for _, d, t in item["goals"]}
    while True:
        more = {(d, t) for q, h in rules if q in demand - known for s, d, t in h}
        if more <= demand:
            break
        demand |= more
    reasons = {(q, h, s, (d, t)) for q, h in rules if q in demand - known for s, d, t in h}
    return {"input_formed": valid_library and functional(item["goals"])
            and all(formed(t) for _, t in item["frontier"] + item["known"])
            and all(formed(t) for _, _, t in item["goals"]),
            "applications": set(map(application_key, applications)),
            "residual": {freeze(g) for g in item["goals"] if freeze(g[1:]) not in reached},
            "demand": demand, "reasons": reasons}


def ml_term(term, pattern=False):
    if "var" in term:
        return "N.Finite_Variable (n " + str(term["var"]) + ")"
    if "pair" in term:
        return "N.Finite_" + ("Pattern_" if pattern else "") + "Pair (" + ",".join(ml_term(t, pattern) for t in term["pair"]) + ")"
    if term == EMPTY:
        return "N.Finite_" + ("Pattern_" if pattern else "") + "Target emptyTarget"
    return "N.Finite_" + ("Pattern_" if pattern else "") + "Payload " + investigate.ml_list(term["payload"], investigate.ml_nat)


def ml_premise(row, pattern=False):
    s, d, t = row
    return "(n " + str(s) + ",(n " + str(d) + "," + ml_term(t, pattern) + "))"


def ml_call(row):
    return "(n " + str(row[0]) + "," + ml_term(row[1]) + ")"


def ml_library(entry):
    rule = entry["schema"]
    premises = investigate.ml_list(rule["premises"], lambda r: ml_premise(r, True))
    materials = investigate.ml_list(rule["materials"], lambda r: "(n " + str(r[0]) + ",N.makea "
                                    + " ".join("(" + ml_term(p, True) + ")" for p in r[1]) + ")")
    return "(n " + str(entry["entry"]) + ",(N.make (" + ml_term(rule["head"], True) + ") (fs " + premises + ") (fs " + materials + ")," + investigate.ml_list(entry["enumeration"], lambda r: ml_premise(r, True)) + "))"


PRELUDE = r'''
structure N = Native_Reasoning;
val n = N.nat_of_integer;
val fs = N.fset_of_list;
val emptyTarget = N.Finite_Whole N.finite_empty_artifact;
val emptyTerm = N.Finite_Target emptyTarget;
fun jnat x = IntInf.toString (N.integer_of_nat x);
fun jlist f xs = "[" ^ String.concatWith "," (map f xs) ^ "]";
fun elements a = case N.fset a of N.Set xs => xs | N.Coset _ => raise Fail "Nonfinite representation";
fun jf f a = jlist f (elements a);
fun jtarget t = if N.finite_reasoning_term_equal (N.Finite_Target t) emptyTerm
 then "{\"empty_artifact\":true}" else raise Fail "Unexpected artifact outside the complete declared control family";
fun jterm (N.Finite_Payload b) = "{\"payload\":" ^ jlist jnat b ^ "}"
 | jterm (N.Finite_Pair (a,b)) = "{\"pair\":[" ^ jterm a ^ "," ^ jterm b ^ "]}"
 | jterm (N.Finite_Target t) = jtarget t;
fun jpattern (N.Finite_Variable v) = "{\"var\":" ^ jnat v ^ "}"
 | jpattern (N.Finite_Pattern_Payload b) = "{\"payload\":" ^ jlist jnat b ^ "}"
 | jpattern (N.Finite_Pattern_Pair (a,b)) = "{\"pair\":[" ^ jpattern a ^ "," ^ jpattern b ^ "]}"
 | jpattern (N.Finite_Pattern_Target t) = jtarget t;
fun jcall (d,t) = "[" ^ jnat d ^ "," ^ jterm t ^ "]";
fun jbinding (v,t) = "[" ^ jnat v ^ "," ^ jterm t ^ "]";
fun jpremise (s,(d,t)) = "[" ^ jnat s ^ "," ^ jnat d ^ "," ^ jterm t ^ "]";
fun jsymbolic (s,(d,p)) = "[" ^ jnat s ^ "," ^ jnat d ^ "," ^ jpattern p ^ "]";
fun jmaterial (s,m) = "[" ^ jnat s ^ "," ^ jlist jpattern
 [N.finite_material_source m,N.finite_material_atoms m,N.finite_material_edges m,
  N.finite_material_counts m,N.finite_material_functions m] ^ "]";
fun jschema s = "{\"head\":" ^ jpattern (N.finite_schema_conclusion s) ^
 ",\"premises\":" ^ jf jsymbolic (N.finite_schema_premises s) ^
 ",\"materials\":" ^ jf jmaterial (N.finite_schema_materials s) ^ "}";
fun japplication (d,(s,(t,(v,h)))) = "{\"entry\":" ^ jnat d ^ ",\"schema\":" ^ jschema s ^
 ",\"conclusion\":" ^ jterm t ^ ",\"bindings\":" ^ jf jbinding v ^ ",\"premises\":" ^ jf jpremise h ^ "}";
fun jreason (q,(h,(s,p))) = "{\"conclusion\":" ^ jcall q ^ ",\"premises\":" ^ jf jpremise h ^
 ",\"premise\":" ^ jnat s ^ ",\"condition\":" ^ jcall p ^ "}";
fun emit id (formed,(applications,(residual,(demand,reasons)))) = print
 ("REASONING_RESULT " ^ Int.toString id ^ " {\"input_formed\":" ^ Bool.toString formed ^
 ",\"applications\":" ^ jf japplication applications ^ ",\"residual\":" ^ jf jpremise residual ^
 ",\"demand\":" ^ jf jcall demand ^ ",\"reasons\":" ^ jf jreason reasons ^ "}\n");
fun jinstruction (N.Pair_Admission_Instruction (d,a,b)) = "[\"pair\"," ^ jnat d ^ "," ^ jnat a ^ "," ^ jnat b ^ "]"
 | jinstruction (N.List_Admission_Instruction (d,a)) = "[\"list\"," ^ jnat d ^ "," ^ jnat a ^ "]";
fun emitInput start = let val (admitted,((root,(next,instructions)),decisions)) = N.generated_input_execution (n start)
 in print ("INPUT_RESULT " ^ IntInf.toString start ^ " {\"domain_admitted\":" ^ Bool.toString admitted ^
 ",\"root\":" ^ jnat root ^ ",\"next\":" ^ jnat next ^ ",\"instructions\":" ^ jlist jinstruction instructions ^
 ",\"decisions\":" ^ jlist Bool.toString decisions ^ "}\n") end;
'''


def run(args):
    if not __debug__:
        raise ValueError("Execution review requires Python assertions to be enabled.")
    output = args.output.resolve()
    if output.exists():
        raise ValueError("The execution output already exists; retain it and use a new directory.")
    output.mkdir(parents=True)
    report = {"status": "failed", "scope": "Complete finite reports for the declared structural controls, native counter examples, and installed complete-input examples"}
    try:
        proof_path = args.proof.resolve()
        proof = json.loads(proof_path.read_text())
        assert proof["status"] == "accepted" and proof["exit_code"] == 0 and proof["sources_unchanged"]
        assert len(proof["exports"]) == 1
        engine = args.engine.resolve() if args.engine else Path(proof["exports"][0]["path"])
        assert digest(engine) == proof["exports"][0]["sha256"]
        source_files = {str(ROOT / "theories" / (name + ".thy")): sha for name, sha in proof["sources"].items()}
        assert all(digest(p) == sha for p, sha in source_files.items())
        inputs = cases()
        (output / "cases.json").write_text(json.dumps(inputs, indent=2) + "\n")
        program = "use " + investigate.ml_string(str(engine)) + ";\n" + PRELUDE
        for i, item in enumerate(inputs):
            operation = item["operation"]
            if operation:
                call = ("N.admission_pair_reasoning_experiment (n " + str(operation[1]) + ")" if operation[0] == "stage"
                        else "N.reasoning_counterexample_experiment " + str(operation[1]).lower())
            else:
                call = "N.natural_learned_investigation " + investigate.ml_list(item["library"], ml_library)
                call += " " + investigate.ml_list(item["frontier"], ml_call)
                call += " (fs " + investigate.ml_list(item["known"], ml_call) + ")"
                call += " (fs " + investigate.ml_list(item["goals"], ml_premise) + ")"
            program += "val () = emit " + str(i) + " (" + call + ");\n"
        starts = [0, 335, 336, 337, 1000, 10**25]
        program += "val () = List.app emitInput [" + ",".join(map(str, starts)) + "];\n"
        runtime = output / "execute.ML"
        runtime.write_text(program)
        tracked = [proof_path, engine, args.poly.resolve(), Path(__file__).resolve(), Path(investigate.__file__).resolve(),
                   runtime, output / "cases.json"]
        hashes = {str(p): digest(p) for p in tracked} | source_files
        (output / "execution-inputs.json").write_text(json.dumps(hashes, indent=2) + "\n")
        with (output / "results.log").open("w") as log:
            completed = subprocess.run([str(args.poly.resolve()), "--script", str(runtime)], stdout=log,
                                       stderr=subprocess.STDOUT, timeout=180, check=False)
        assert completed.returncode == 0, "The generated module or runtime serializer failed; inspect results.log."
        seen, seen_starts, findings = set(), set(), []
        for line in (output / "results.log").read_text().splitlines():
            if line.startswith("REASONING_RESULT "):
                identifier, raw = line.removeprefix("REASONING_RESULT ").split(" ", 1)
                index = int(identifier)
                assert index not in seen and 0 <= index < len(inputs)
                seen.add(index)
                actual = json.loads(raw)
                expected = reconstruct(inputs[index])
                normalized = {"input_formed": actual["input_formed"],
                    "applications": set(map(application_key, actual["applications"])),
                    "residual": set(map(freeze, actual["residual"])), "demand": set(map(freeze, actual["demand"])),
                    "reasons": {(freeze(r["conclusion"]), frozenset(map(freeze, r["premises"])),
                                  r["premise"], freeze(r["condition"])) for r in actual["reasons"]}}
                mismatch = [key for key in expected if expected[key] != normalized[key]]
                assert not mismatch, (inputs[index]["name"], mismatch)
                findings.append({"case": inputs[index]["name"], "formed": actual["input_formed"],
                                 "applications": len(normalized["applications"]), "residual": len(normalized["residual"]),
                                 "demand": len(normalized["demand"]), "reasons": len(normalized["reasons"]),
                                 "checked": list(expected)})
            elif line.startswith("INPUT_RESULT "):
                identifier, raw = line.removeprefix("INPUT_RESULT ").split(" ", 1)
                start = int(identifier)
                assert start in starts and start not in seen_starts
                seen_starts.add(start)
                actual = json.loads(raw)
                expected = {"domain_admitted": start >= 336, "root": start + 2, "next": start + 3,
                    "instructions": [["pair", start, 2, 2], ["list", start + 1, start], ["pair", start + 2, 311, start + 1]],
                    "decisions": [i not in {6, 7, 8, 10} for i in range(11)] if start >= 336 else []}
                assert actual == expected, ("installed input", start)
        assert len(seen) == len(inputs) and seen_starts == set(starts)
        assert all(digest(p) == sha for p, sha in hashes.items()), "Execution evidence changed."
        report.update(status="accepted", reasoning_cases=len(inputs), input_starts=starts, findings=findings,
                      execution_inputs=hashes, results_sha256=digest(output / "results.log"),
                      proof_receipt=str(proof_path), proof_receipt_sha256=digest(proof_path),
                      boundary="Structural controls verify exact generation and conditional reports. Native semantic guarantees come from the separately accepted theory contracts; this host review is not native mathematical-proof admission.")
    except Exception as error:
        report["error"] = str(error)
    (output / "receipt.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in {"execution_inputs", "findings"}}, indent=2))
    if report["status"] != "accepted":
        print((output / "results.log").read_text()[-5000:] if (output / "results.log").exists() else report["error"])
    return int(report["status"] != "accepted")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--poly", type=Path, required=True)
    parser.add_argument("--engine", type=Path, help="Retained generated module, with the exact digest in the proof receipt")
    parser.add_argument("--output", type=Path, required=True)
    return run(parser.parse_args())


if __name__ == "__main__":
    sys.exit(main())
