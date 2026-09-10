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


def specialization_context(a, d, c, b, q):
    return pair(pair(a, pair(d, c)), pair(b, q))


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
    body = specialization_context(*(variable(i) for i in range(5)))
    report_rule = schema(pair(body, variable(5)),
                         [[0, 294, body], [1, 126, pair(variable(4), variable(5))]])
    report_lib = library(342, report_rule)
    a, d, c, b, q, other_q, report, other_report = [payload(i) for i in range(40, 48)]
    context = specialization_context(a, d, c, b, q)
    other_context = specialization_context(a, d, c, b, other_q)
    report_frontier = [[294, context], [126, pair(q, report)]]
    report_goal = [0, 342, pair(context, report)]
    controls = [case("report-without-rule", [], report_frontier, [], [report_goal]),
        case("report-matching-target", report_lib, report_frontier, [], [report_goal], ("report", None)),
        case("report-different-target", report_lib,
             [[294, context], [126, pair(other_q, report)]], [], [report_goal], ("report", None)),
        case("report-two-targets", report_lib,
             report_frontier + [[294, other_context], [126, pair(other_q, other_report)]], [],
             [report_goal, [1, 342, pair(other_context, other_report)]], ("report", None)),
        case("report-two-possible-reports", report_lib,
             report_frontier + [[126, pair(q, other_report)]], [],
             [report_goal, [1, 342, pair(context, other_report)]], ("report", None)),
        case("report-reordered-repeated-frontier", report_lib,
             list(reversed(report_frontier)) + report_frontier, [], [report_goal], ("report", None)),
        case("report-unused-malformed-source", report_lib,
             report_frontier + [[126, payload(256)]], [], [report_goal], ("report", None)),
        case("report-distinct-goal-occurrences", report_lib, report_frontier, [],
             [report_goal, [17, 342, pair(context, report)]], ("report", None))]
    for control in controls:
        control["semantic_boundary"] = (
            "Structural construction control. Both native source premises remain unproved; the known set is empty.")
    result.extend(controls)
    result.extend(binding_cases())
    return result


def sequence(terms):
    result = payload()
    for term in reversed(terms):
        result = pair(term, result)
    return result


def sequence_items(term):
    result = []
    while term != payload():
        if set(term) != {"pair"} or len(term["pair"]) != 2:
            raise ValueError("Not a complete sequence")
        first, term = term["pair"]
        result.append(first)
    return result


def binding_views(owner, rows):
    """Independent row equations, including formation of unreturned fields."""
    if not formed(owner) or not all(map(formed, rows)):
        return None
    fields = []
    for row in rows:
        if set(row) != {"pair"} or len(row["pair"]) != 2:
            return None
        key, values = row["pair"]
        if set(key) != {"pair"} or set(values) != {"pair"}:
            return None
        if len(key["pair"]) != 2 or len(values["pair"]) != 2 or key["pair"][0] != owner:
            return None
        fields.append((key["pair"][1], *values["pair"]))
    return [[pair(key, x) for key, x, y in fields], [pair(key, y) for key, x, y in fields]]


def binding_frontier(owner, rows):
    outputs = binding_views(owner, rows)
    return [] if outputs is None else [[d, pair(owner, pair(sequence(rows), sequence(values)))]
                                      for d, values in zip([345, 346], outputs)]


def binding_call_true(entry, term):
    try:
        owner, body = term["pair"]
        rows, output = body["pair"]
        views = binding_views(owner, sequence_items(rows))
        if views is None:
            return False
        if entry in {345, 346}:
            return sequence_items(output) == views[entry - 345]
        if entry == 347:
            return [sequence_items(t) for t in output["pair"]] == views
    except (KeyError, TypeError, ValueError):
        return False
    return False


def binding_cases():
    owner, other = payload(50), payload(51)
    row = lambda u, key, x, y: pair(pair(u, key), pair(x, y))
    rows = [row(owner, payload(60), payload(8), EMPTY),
            row(owner, payload(61), payload(8), payload(8)),
            row(owner, payload(62), pair(payload(8), payload(9)), pair(EMPTY, EMPTY))]
    rule = schema(pair(variable(0), pair(variable(1), pair(variable(2), variable(3)))),
                  [[0, 345, pair(variable(0), pair(variable(1), variable(2)))],
                   [1, 346, pair(variable(0), pair(variable(1), variable(3)))]])
    lib = library(347, rule)

    def goal(u, source, outputs=None, socket=0):
        if outputs is None:
            outputs = binding_views(u, source) or [[], []]
        return [socket, 347, pair(u, pair(sequence(source), pair(*(sequence(xs) for xs in outputs))))]

    def example(name, sources, goals, enabled=True):
        frontier = [call for u, bs in sources for call in binding_frontier(u, bs)]
        assert all(binding_call_true(*call) for call in frontier)
        item = case(name, lib if enabled else [], frontier, copy.deepcopy(frontier), goals, ("binding", enabled))
        item["binding_sources"] = sources
        item["native_goal_truth"] = [binding_call_true(d, t) for _, d, t in goals]
        item["semantic_boundary"] = (
            "Known traversal calls are constructed by the native row converter. The accepted exactness and closure contracts apply. "
            "This does not admit an entire symbolic argument or arbitrary paired terms as patterns.")
        return item

    same = [[owner, rows]]
    sources = [[owner, rows[:1]], [other, [row(other, payload(60), payload(8), EMPTY)]]]
    two_goals = [goal(u, bs, socket=i) for i, (u, bs) in enumerate(sources)]
    repeated = [rows[0], rows[0], rows[1]]
    wrong_owner = [row(other, payload(60), payload(8), EMPTY)]
    nonpaired = [pair(pair(owner, payload(60)), payload(8))]
    outside_pattern_range = [row(owner, payload(63), EMPTY, payload())]
    malformed = [row(owner, payload(60), payload(8), payload(256))]
    wrong_outputs = copy.deepcopy(binding_views(owner, rows))
    wrong_outputs[1][0] = pair(payload(60), payload(99))
    wrong_tail = [0, 347, pair(owner, pair(sequence(rows), pair(sequence(wrong_outputs[0]), payload(9))))]
    range_control = example("binding-conversion-without-pattern-admission",
                            [[owner, outside_pattern_range]], [goal(owner, outside_pattern_range)])
    range_control["semantic_boundary"] = (
        "The native row conversion succeeds. The observation pair (empty-artifact target, empty payload) "
        "is outside the pattern-observation image: target_valuation_payload forces a literal payload pattern, "
        "whose first observation is also that payload. No pattern or whole-argument admission follows.")
    return [
        example("binding-before-rule", same, [goal(owner, rows)], False),
        example("binding-native-report", same, [goal(owner, rows)]),
        example("binding-empty", [[owner, []]], [goal(owner, [])]),
        example("binding-equal-first-observations", [[owner, rows[:2]]], [goal(owner, rows[:2])]),
        example("binding-repeated-rows", [[owner, repeated]], [goal(owner, repeated)]),
        example("binding-different-owners", sources, two_goals),
        example("binding-reordered-repeated-sources", sources[::-1] + sources, two_goals),
        example("binding-wrong-owner", [[owner, wrong_owner]], [goal(owner, wrong_owner)]),
        example("binding-nonpaired-value", [[owner, nonpaired]], [goal(owner, nonpaired)]),
        range_control,
        example("binding-unused-malformed-component", same + [[owner, malformed]], [goal(owner, rows)]),
        example("binding-unused-malformed-context", same + [[payload(256), []]], [goal(owner, rows)]),
        example("binding-wrong-requested-output", same, [goal(owner, rows, wrong_outputs)]),
        example("binding-wrong-output-tail", same, [wrong_tail]),
        example("binding-distinct-goal-occurrences", same, [goal(owner, rows), goal(owner, rows, socket=17)])]


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
    source_formed = all(formed(u) and all(map(formed, rows)) for u, rows in item.get("binding_sources", []))
    return {"input_formed": source_formed and valid_library and functional(item["goals"])
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


def ml_binding_source(source):
    owner, rows = source
    return "(" + ml_term(owner) + "," + investigate.ml_list(rows, ml_term) + ")"


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
fun emitViews id index (u,rows) = let
 val outputs = case N.finite_binding_observation_outputs u rows of NONE => "null"
  | SOME (xs,ys) => "[" ^ jlist jterm xs ^ "," ^ jlist jterm ys ^ "]";
 val frontier = N.finite_binding_observation_frontier u rows
 in print ("BINDING_RESULT " ^ Int.toString id ^ " " ^ Int.toString index ^
  " {\"outputs\":" ^ outputs ^ ",\"frontier\":" ^ jlist jcall frontier ^ "}\n") end;
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
            if operation and operation[0] == "binding":
                call = ("N.binding_observation_investigation " + str(operation[1]).lower() + " "
                        + investigate.ml_list(item["binding_sources"], ml_binding_source)
                        + " (fs " + investigate.ml_list(item["goals"], ml_premise) + ")")
                for j, source in enumerate(item["binding_sources"]):
                    program += "val () = emitViews " + str(i) + " " + str(j) + " " + ml_binding_source(source) + ";\n"
            elif operation and operation[0] != "report":
                call = ("N.admission_pair_reasoning_experiment (n " + str(operation[1]) + ")" if operation[0] == "stage"
                        else "N.reasoning_counterexample_experiment " + str(operation[1]).lower())
            else:
                call = ("N.specialization_report_investigation" if operation else
                        "N.natural_learned_investigation " + investigate.ml_list(item["library"], ml_library))
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
        seen, seen_starts, seen_views, findings = set(), set(), set(), []
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
                if "native_goal_truth" in inputs[index]:
                    assert all(binding_call_true(*call) for call in inputs[index]["known"])
                    assert all(truth or freeze(goal) in normalized["residual"]
                               for goal, truth in zip(inputs[index]["goals"], inputs[index]["native_goal_truth"]))
                    findings[-1]["native_goal_truth"] = inputs[index]["native_goal_truth"]
            elif line.startswith("BINDING_RESULT "):
                identifier, source_id, raw = line.removeprefix("BINDING_RESULT ").split(" ", 2)
                index, source_index = int(identifier), int(source_id)
                assert 0 <= index < len(inputs) and (index, source_index) not in seen_views
                assert 0 <= source_index < len(inputs[index]["binding_sources"])
                owner, rows = inputs[index]["binding_sources"][source_index]
                actual = json.loads(raw)
                assert actual == {"outputs": binding_views(owner, rows), "frontier": binding_frontier(owner, rows)}
                assert all(binding_call_true(*call) for call in actual["frontier"])
                seen_views.add((index, source_index))
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
        assert seen_views == {(i, j) for i, item in enumerate(inputs) for j in range(len(item.get("binding_sources", [])))}
        assert all(digest(p) == sha for p, sha in hashes.items()), "Execution evidence changed."
        report.update(status="accepted", reasoning_cases=len(inputs), input_starts=starts, binding_source_executions=len(seen_views), findings=findings,
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
