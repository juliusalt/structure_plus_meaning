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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--poly", type=Path, required=True)
    parser.add_argument("--engine", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    status = review.run(args, cases_factory=baseline_cases, cases_source=Path(__file__))
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
    receipt_path = args.output.resolve() / "receipt.json"
    adequacy = {
        "question": "Can the existing construction library construct a call of the new native inference reader at 350?",
        "status": "current library leaves the target unresolved at every tested depth",
        "conditions": conditions,
        "receipt": str(receipt_path),
        "receipt_sha256": review.digest(receipt_path),
        "proposed_requirement": "Derive a reusable library-coverage obstruction from the actual schema entries and premises, valid at every construction depth and independent of the source term.",
        "boundary": "The finite runs establish the observed failure. They do not alone prove that additional depth can never help, nor admit the source-shaped probe as a native reading.",
    }
    (args.output / "adequacy.json").write_text(json.dumps(adequacy, indent=2) + "\n")
    print(json.dumps(adequacy, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
