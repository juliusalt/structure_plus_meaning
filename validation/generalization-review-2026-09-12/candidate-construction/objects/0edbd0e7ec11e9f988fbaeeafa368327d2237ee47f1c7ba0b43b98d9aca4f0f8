#!/usr/bin/env python3
"""Investigate which target entries the current construction language can reach.

The baseline executes the actual finite representations of the three current
native construction clauses. Source-shaped probes are possible calls only;
they do not assert that any invented environment presents an actual source.
"""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path

import check_construction_chains as chains
import check_reasoning as review


def baseline_cases():
    old = review.cases()
    report = next(x for x in old if x["name"] == "report-matching-target")
    binding = next(x for x in old if x.get("operation") == ("binding", True)
                   and x["frontier"] and x["native_goal_truth"] == [True])
    step = chains.baseline_cases()[1]
    lib = report["library"] + binding["library"] + step["library"]
    frontier = report["frontier"] + binding["frontier"] + step["frontier"]
    known = binding["known"] + step["known"]
    # The source reader's actual public head is a twelve-field list. This is
    # a formed representative for an entry-coverage probe, not source evidence.
    probe = review.sequence([review.payload(i) for i in range(12)])
    goals = [[i, d, probe] for i, d in enumerate([348, 349, 350])]
    goals += [[3, *report["goals"][0][1:]], [4, *binding["goals"][0][1:]],
              [5, *step["goals"][0][1:]]]
    boundary = (
        "The finite schemas decode to the existing native clauses at 342, 347, and 345. "
        "The entry-348/349/350 goals are formed structural probes, not admitted source readings. "
        "The report's 294 and 126 premises are possible only. Known binding calls have exact native contracts. "
        "This run diagnoses this library; it does not prove an impossibility for every library or program.")

    def item(name, rounds, possible=frontier, admitted=known, library=lib):
        result = review.case(name, copy.deepcopy(library), copy.deepcopy(possible), copy.deepcopy(admitted),
                             copy.deepcopy(goals), ("chain", rounds))
        result.update(construction_rounds=rounds, semantic_boundary=boundary)
        return result

    result = [item("coverage-depth-" + str(n), n) for n in [0, 1, 3, 5]]
    result += [item("coverage-library-absent", 3, library=[]),
               item("coverage-evidence-withheld", 3, admitted=[]),
               item("coverage-target-merely-possible", 3, possible=frontier + [[350, probe]]),
               item("coverage-target-supplied-as-known", 3, admitted=known + [[350, probe]])]
    result[-1]["semantic_boundary"] = (
        "A structural control deliberately supplies the unproved goal as known. "
        "Its settlement is conditional on that supplied premise and supplies no native semantic evidence.")
    return result


def coverage_cases():
    result = baseline_cases()
    # This export selects its library internally from the three proved native
    # clause representations. Compare its complete signature to our specification.
    for item in result:
        if item["name"] != "coverage-library-absent":
            item["native_reader_coverage"] = True
    result.extend(copy.deepcopy(review.cases()))
    v, p = review.variable, review.payload
    cycle = review.library(110, review.schema(v(0), [[0, 111, v(0)]]))
    cycle += review.library(111, review.schema(v(0), [[0, 110, v(0)]]))
    result += [
        review.case("coverage-unsupported-cycle", cycle, [[110, p(1)], [111, p(1)]], [], [[0, 111, p(1)]]),
        review.case("coverage-supported-cycle", cycle, [[110, p(1)], [111, p(1)]],
                    [[110, p(1)]], [[0, 111, p(1)]]),
        review.case("coverage-conjunction-needs-both", review.library(112,
                    review.schema(v(0), [[0, 110, v(0)], [1, 111, v(0)]])),
                    [[110, p(1)], [111, p(1)]], [[110, p(1)]], [[0, 112, p(1)]]),
    ]
    changed = copy.deepcopy(result[0])
    changed.update(name="coverage-same-entry-different-known-term")
    changed["known"].append([350, p(99)])
    result.append(changed)
    for item in result:
        item["diagnose_coverage"] = True
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--poly", type=Path, required=True)
    parser.add_argument("--engine", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--coverage", action="store_true")
    args = parser.parse_args()
    status = review.run(args, cases_factory=coverage_cases if args.coverage else baseline_cases,
                        cases_source=Path(__file__), cases_dependencies=[Path(chains.__file__)])
    if status:
        return status
    reports = []
    for line in (args.output / "results.log").read_text().splitlines():
        if line.startswith("REASONING_RESULT "):
            identifier, raw = line.removeprefix("REASONING_RESULT ").split(" ", 1)
            reports.append((int(identifier), json.loads(raw)))
    conditions = {
        "missing_entries_survive_every_tested_depth": all(
            {348, 349, 350} <= {g[1] for g in raw["residual"]} for i, raw in reports if i < 4),
        "possible_goal_does_not_establish_it": any(g[1] == 350 for g in reports[6][1]["residual"]),
        "known_goal_is_retained_as_an_assumption": all(g[1] != 350 for g in reports[7][1]["residual"]),
        "existing_binding_constructions_succeed": all(g[1] not in {345, 347} for g in reports[0][1]["residual"]),
        "unproved_report_premises_remain": any(g[1] == 342 for g in reports[0][1]["residual"]),
        "missing_producers_have_no_application_reasons": all(
            r["conclusion"][0] not in {348, 349, 350} for _, raw in reports for r in raw["reasons"]),
    }
    assert all(conditions.values()), conditions
    if args.coverage:
        coverage = {}
        for line in (args.output / "results.log").read_text().splitlines():
            if line.startswith("COVERAGE_RESULT "):
                identifier, raw = line.removeprefix("COVERAGE_RESULT ").split(" ", 1)
                coverage[int(identifier)] = json.loads(raw)
        inputs = coverage_cases()
        by_name = {x["name"]: coverage[i] for i, x in enumerate(inputs)}
        additional = {
            "native_library_reports_missing_entries": all(
                {348, 349, 350} <= {g[1] for g in coverage[i]["blocked"]} for i in range(4)),
            "unsupported_cycle_stays_blocked": bool(by_name["coverage-unsupported-cycle"]["blocked"]),
            "supported_cycle_passes_entry_check": not by_name["coverage-supported-cycle"]["blocked"],
            "conjunction_requires_every_entry": bool(by_name["coverage-conjunction-needs-both"]["blocked"]),
            "abstraction_does_not_compare_known_terms": all(
                g[1] != 350 for g in by_name["coverage-same-entry-different-known-term"]["blocked"]),
            "concrete_check_retains_different_known_term": any(
                g[1] == 350 for g in reports[-1][1]["residual"]),
        }
        assert all(additional.values()), additional
        conditions.update(additional)
        original_heads = {d for d, _ in coverage[0]["rules"]}
        absent_producers = sorted({g[1] for g in coverage[0]["blocked"]} - original_heads)
    receipt_path = args.output.resolve() / "receipt.json"
    adequacy = {
        "question": "Can the existing construction library construct a call of the new native inference reader at 350?",
        "status": ("proved entry abstraction diagnoses the current library's missing construction capability"
                   if args.coverage else "current library leaves the target unresolved at every tested depth"),
        "conditions": conditions,
        "receipt": str(receipt_path),
        "receipt_sha256": review.digest(receipt_path),
        "proposed_requirement": "Derive a reusable library-coverage obstruction from the actual schema entries and premises, valid at every construction depth and independent of the source term.",
        "boundary": ("The accepted projection theorem makes every reported obstruction valid at every finite construction depth. "
                     "An entry reachable in the abstraction need not have a concrete derivation or a true native source reading."
                     if args.coverage else
                     "The finite runs establish the observed failure. They do not alone prove that additional depth can never help, nor admit the source-shaped probe as a native reading."),
    }
    if args.coverage:
        adequacy["next_problems"] = [
            {"entry": d, "obstruction": "No constructor in the current library has this conclusion entry."}
            for d in absent_producers]
        adequacy["next_requirement"] = (
            "Construct these actual native clause heads conditionally from their component calls, "
            "retaining every source field and every unproved reading condition.")
    (args.output / "adequacy.json").write_text(json.dumps(adequacy, indent=2) + "\n")
    print(json.dumps(adequacy, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
