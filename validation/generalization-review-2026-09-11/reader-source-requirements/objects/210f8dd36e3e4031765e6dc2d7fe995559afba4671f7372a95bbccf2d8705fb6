#!/usr/bin/env python3
"""Revisit retained reader requests and their necessary source conditions."""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path

import check_guided_reasoning as guided
import check_reasoning as review


def environment_requirements(goals, schema):
    requirements = []
    for goal in goals:
        if goal[1] != 350:
            continue
        values = review.match(schema["head"], goal[2])
        assert values is not None and 0 in values
        requirements.append({"goal": goal, "environment": values[0],
            "contract": "inference_specialization_source_obstruction",
            "source_variable": 0, "source_schema": schema})
    return requirements


def reader_cases(original, *, source_requirements=False):
    cases = []
    schemas = [e["schema"] for e in original[0]["library"] if e["entry"] == 350]
    assert len(schemas) == 1
    schema = schemas[0]
    for index, old in enumerate(original):
        if not old["name"].startswith("reader-"):
            continue
        item = copy.deepcopy(old)
        item["name"] = "guided-" + old["name"]
        if old["operation"] and old["operation"][0] == "chain":
            item = guided.guide_case(old, index)
        item["baseline_source_index"] = index
        item["diagnose_bindings"] = True
        if source_requirements:
            item["environment_requirements"] = environment_requirements(item["goals"], schema)
        assert all(item[f] == old[f] for f in ["library", "frontier", "known", "goals"])
        cases.append(item)
    if source_requirements:
        base = next(c for c in cases if c["name"] == "guided-reader-depth-3")
        for name, environment in [
                ("empty-environment-shape", review.pair(review.payload(), review.payload())),
                ("unsupported-tables-shape", review.pair(review.payload(4), review.payload())),
                ("malformed-pair-shape", review.pair(review.payload(256), review.payload())),
                ("target-source-shape", review.EMPTY)]:
            item = copy.deepcopy(base)
            item["name"] = "reader-" + name
            item["baseline_source_index"] = None
            values = review.match(schema["head"], base["goals"][0][2])
            values[0] = environment
            item["goals"] = [[0, 350, review.evaluate(schema["head"], values)]]
            item["environment_requirements"] = environment_requirements(item["goals"], schema)
            item["semantic_boundary"] = "A necessary outer-shape control; a successful shape result does not establish any reader premise."
            cases.append(item)
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ["proof", "poly", "output", "baseline"]:
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--engine", type=Path)
    parser.add_argument("--source-requirements", action="store_true")
    args = parser.parse_args()
    if not __debug__:
        raise ValueError("Reader requirement review requires Python assertions to be enabled.")
    original, before = guided.load_baseline(args.baseline)
    cases = reader_cases(original, source_requirements=args.source_requirements)
    if args.source_requirements:
        proof = json.loads(args.proof.read_text())
        assert "Factor_Reader_Source_Requirements" in proof["sources"]
    status = review.run(args, cases_factory=lambda: cases, cases_source=Path(__file__),
        cases_dependencies=[args.baseline / name for name in ["receipt.json", "cases.json", "results.log"]])
    if status:
        return status
    reports, gaps, requirements = {}, {}, {}
    for line in (args.output / "results.log").read_text().splitlines():
        if line.startswith(("REASONING_RESULT ", "BINDING_GAPS_RESULT ", "ENVIRONMENT_REQUIREMENT_RESULT ")):
            kind, identifier, raw = line.split(" ", 2)
            {"REASONING_RESULT": reports, "BINDING_GAPS_RESULT": gaps,
             "ENVIRONMENT_REQUIREMENT_RESULT": requirements}[kind][int(identifier)] = json.loads(raw)
    compared = [(i, c) for i, c in enumerate(cases) if c["baseline_source_index"] is not None]
    controls = {
        "original_complete_inputs_preserved": bool(cases),
        "original_formation_preserved": all(reports[i]["input_formed"] == before[c["baseline_source_index"]]["input_formed"]
                                            for i, c in compared),
        "original_applications_preserved": all(set(map(review.application_key, before[c["baseline_source_index"]]["applications"])) <=
            set(map(review.application_key, reports[i]["applications"])) for i, c in compared),
        "original_settlements_preserved": all(set(map(review.freeze, reports[i]["residual"])) <=
            set(map(review.freeze, before[c["baseline_source_index"]]["residual"])) for i, c in compared),
    }
    if args.source_requirements:
        controls["all_original_top_sources_obstructed"] = all(not row["possible_outer_shape"]
            for i, c in compared for row in requirements.get(i, []))
        controls["successful_shape_does_not_settle_reader"] = all(c["goals"][0] in reports[i]["residual"]
            for i, c in enumerate(cases) if c["baseline_source_index"] is None)
        controls["malformed_pair_rejects_original_input"] = all(not reports[i]["input_formed"]
            for i, c in enumerate(cases) if c["name"] == "reader-malformed-pair-shape")
    assert all(controls.values()), controls
    base_index = next(i for i, c in enumerate(cases) if c["name"] == "guided-reader-depth-3")
    report, base = reports[base_index], cases[base_index]
    produced = {review.freeze([a["entry"], a["conclusion"]]) for a in report["applications"]}
    known = set(map(review.freeze, base["known"]))
    pending = [q for q in report["demand"] if review.freeze(q) not in known | produced]
    assessment = {
        "question": "Which source requirements remain when the guided method revisits the complete original reader requests?",
        "controls": controls, "next_conditions": pending, "library_binding_gaps": gaps[base_index],
        "source_requirements": [{"case": cases[i]["name"], "requirements": rows} for i, rows in requirements.items()],
        "receipt_sha256": review.digest(args.output / "receipt.json"),
        "boundary": "Original calls and evidence remain unchanged. Guided construction is conditional. A failed necessary source condition rules out the exact native request; a successful shape check does not establish source admission.",
    }
    (args.output / "adequacy.json").write_text(json.dumps(assessment, indent=2) + "\n")
    print(json.dumps({"cases": len(cases), "controls": controls, "remaining_entries": [d for d, _ in pending],
                      "source_requirement_cases": len(requirements)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
