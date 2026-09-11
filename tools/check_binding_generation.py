#!/usr/bin/env python3
"""Compare complete native binding clauses with actual native binding results.

The original question concerns recovery from supplied goals and clauses. Native
traversal computations provide an independent semantic comparison; they enter
the known set only in the explicitly named evidence controls.
"""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path

import check_reasoning as review


LIBRARY = "binding_observation_construction_library"


def load_library(directory):
    receipt_path = directory / "receipt.json"
    receipt = json.loads(receipt_path.read_text())
    assert receipt["status"] == "accepted"
    assert review.digest(directory / "results.log") == receipt["results_sha256"]
    path = directory / ("library-" + LIBRARY + ".json")
    assert review.digest(path) == receipt["exported_libraries"][LIBRARY]["sha256"]
    return json.loads(path.read_text())


def calls_for(owner, rows):
    outputs = review.binding_views(owner, rows)
    assert outputs is not None
    calls = review.binding_frontier(owner, rows)
    calls.append([347, review.pair(owner, review.pair(review.sequence(rows),
        review.pair(*(review.sequence(values) for values in outputs))))])
    if rows:
        calls += [[entry, review.pair(owner, review.pair(rows[0], values[0]))]
                  for entry, values in zip([343, 344], outputs)]
    return calls


def binding_generation_cases(library):
    owner, other = review.payload(50), review.payload(51)
    rows = [review.pair(review.pair(owner, review.payload(60 + i)),
                        review.pair(review.payload(80 + i), review.EMPTY)) for i in range(3)]

    def example(name, goals, sources, *, rounds=2, frontier=(), known=(), enabled=True):
        item = review.case(name, copy.deepcopy(library) if enabled else [],
                           copy.deepcopy(list(frontier)), copy.deepcopy(list(known)),
                           [[s, *copy.deepcopy(q)] for s, q in enumerate(goals)], ("chain", rounds))
        item.update(construction_rounds=rounds,
                    native_libraries=[{"name": LIBRARY}] if enabled else [],
                    diagnose_coverage=True, diagnose_bindings=True, binding_sources=copy.deepcopy(sources),
                    native_goal_truth=[review.binding_call_true(*q) for q in goals])
        return item

    result = [example("binding-clauses-length-" + str(count) + "-depth-" + str(depth),
                      calls_for(owner, rows[:count]), [[owner, rows[:count]]], rounds=depth)
              for count in range(4) for depth in [0, 2, 5]]
    all_calls = calls_for(owner, rows)
    traversals = review.binding_frontier(owner, rows)
    pair_call = next(q for q in all_calls if q[0] == 347)
    wrong_owner = copy.deepcopy(pair_call)
    wrong_owner[1]["pair"][0] = other
    wrong_output = copy.deepcopy(pair_call)
    wrong_output[1]["pair"][1]["pair"][1]["pair"][0] = review.payload()
    malformed = copy.deepcopy(pair_call)
    malformed[1]["pair"][1]["pair"][1]["pair"][1] = review.payload(256)
    other_rows = [review.pair(review.pair(other, review.payload(70)),
                             review.pair(review.payload(90), review.EMPTY))]
    result += [
        example("binding-clauses-no-library", all_calls, [[owner, rows]], enabled=False),
        example("binding-clauses-goals-only-possible", all_calls, [[owner, rows]], frontier=all_calls),
        example("binding-clauses-native-traversal-evidence", [pair_call], [[owner, rows]],
                frontier=traversals, known=traversals),
        example("binding-clauses-empty-traversal-evidence", [calls_for(owner, [])[2]], [[owner, []]],
                frontier=review.binding_frontier(owner, []), known=review.binding_frontier(owner, [])),
        example("binding-clauses-wrong-owner", [wrong_owner], [[owner, rows], [other, rows]]),
        example("binding-clauses-wrong-output", [wrong_output], [[owner, rows]]),
        example("binding-clauses-malformed-output", [malformed], [[owner, rows]]),
        example("binding-clauses-two-contexts", all_calls + calls_for(other, other_rows),
                [[owner, rows], [other, other_rows]]),
    ]
    return result


def assess(cases, results, coverages, binding_reports):
    evidence_names = {"binding-clauses-native-traversal-evidence", "binding-clauses-empty-traversal-evidence"}
    base_indices = [i for i, c in enumerate(cases) if c["name"].startswith("binding-clauses-length-")]
    controls = {
        "complete_actual_library_has_seven_clauses": all(len(cases[i]["library"]) == 7 for i in base_indices),
        "native_goals_are_true": all(all(cases[i]["native_goal_truth"]) for i in base_indices),
        "entry_coverage_finds_no_obstruction": all(not coverages[i]["blocked"] for i in base_indices),
        "complete_clauses_generate_no_applications": all(not results[i]["applications"] for i in base_indices),
        "native_goals_remain_unresolved": all(set(map(review.freeze, cases[i]["goals"])) ==
            set(map(review.freeze, results[i]["residual"])) for i in base_indices),
        "every_actual_clause_has_complete_head_scope": all(not e["head_missing"]
            for i in base_indices for e in binding_reports[i]),
        "established_native_traversals_enable_pair_report": all(not results[i]["residual"]
            for i, c in enumerate(cases) if c["name"] in evidence_names),
        "possible_goals_do_not_supply_evidence": all(set(map(review.freeze, cases[i]["goals"])) ==
            set(map(review.freeze, results[i]["residual"])) for i, c in enumerate(cases)
            if c["name"] == "binding-clauses-goals-only-possible"),
        "malformed_original_goal_rejects_report": all(not results[i]["input_formed"] for i, c in enumerate(cases)
            if c["name"] == "binding-clauses-malformed-output"),
    }
    assert all(controls.values()), controls
    problems = {}
    for i in base_indices:
        for goal, truth in zip(cases[i]["goals"], cases[i]["native_goal_truth"]):
            if not truth or goal not in results[i]["residual"]:
                continue
            matching = [e for e in binding_reports[i] if e["entry"] == goal[1]
                        and review.match(e["schema"]["head"], goal[2]) is not None]
            problems[review.freeze(goal[1:])] = {"call": goal[1:], "matching_clauses": matching}
    return {
        "question": "Can the current construction engine recover actual native binding judgments from their complete clauses and supplied goals, with no known traversal seeds?",
        "assessment": "Inadequate on the supplied native family despite complete clause and entry coverage.",
        "controls": controls,
        "next_problems": list(problems.values()),
        "next_requirement": "Obtain complete bindings for these unresolved native calls while preserving all premise, material, formation, and known-evidence conditions.",
        "binding_obstruction_contract": "finite_schema_generation_missing_variables",
        "boundary": "The comparison establishes failure at the tested finite bounds. Each reported nonempty premise gap proves that clause cannot generate any application for any frontier. An empty head gap identifies available bindings, but does not establish premises or select a complete repair.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ["proof", "poly", "output", "catalog"]:
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--engine", type=Path)
    parser.add_argument("--generic-controls", action="store_true")
    args = parser.parse_args()
    if not __debug__:
        raise ValueError("Execution review requires Python assertions to be enabled.")
    library = load_library(args.catalog)
    cases = binding_generation_cases(library)
    if args.generic_controls:
        cases += [{**item, "diagnose_bindings": True} for item in review.cases()]
    dependencies = [args.catalog / "receipt.json", args.catalog / "results.log",
                    args.catalog / ("library-" + LIBRARY + ".json")]
    status = review.run(args, cases_factory=lambda: cases, cases_source=Path(__file__),
                        cases_dependencies=dependencies)
    if status:
        return status
    results, coverages, binding_reports = {}, {}, {}
    for line in (args.output / "results.log").read_text().splitlines():
        if line.startswith(("REASONING_RESULT ", "COVERAGE_RESULT ", "BINDING_GAPS_RESULT ")):
            kind, identifier, raw = line.split(" ", 2)
            {"REASONING_RESULT": results, "COVERAGE_RESULT": coverages,
             "BINDING_GAPS_RESULT": binding_reports}[kind][int(identifier)] = json.loads(raw)
    assessment = assess(cases, results, coverages, binding_reports)
    assessment["receipt_sha256"] = review.digest(args.output / "receipt.json")
    (args.output / "adequacy.json").write_text(json.dumps(assessment, indent=2) + "\n")
    print(json.dumps({k: v for k, v in assessment.items() if k != "next_problems"}, indent=2))
    print("Unresolved native calls:", len(assessment["next_problems"]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
