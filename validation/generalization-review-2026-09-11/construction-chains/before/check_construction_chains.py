#!/usr/bin/env python3
"""Investigate whether generated native calls can feed later constructions.

The baseline uses the existing list-step clause at 345, the actual scalar row
predicate at 343, and the native complete-list converter as an independent
comparison. Supplying an intermediate call is a diagnostic control.
"""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path

import check_reasoning as review


def chain_cases():
    u, other = review.payload(50), review.payload(51)
    row = review.pair(review.pair(u, review.payload(60)), review.pair(review.payload(8), review.EMPTY))
    value = review.pair(review.payload(60), review.payload(8))
    context = lambda owner, a, b: review.pair(owner, review.pair(a, b))
    v = review.variable
    step = review.schema(context(v(0), review.pair(v(1), v(2)), review.pair(v(3), v(4))),
                         [[0, 343, context(v(0), v(1), v(3))], [1, 345, context(v(0), v(2), v(4))]])
    lib = review.library(345, step)
    scalar = [343, context(u, row, value)]
    nil = [345, context(u, review.payload(), review.payload())]
    call = lambda n, owner=u: [345, context(owner, review.sequence([row] * n), review.sequence([value] * n))]
    seed = [scalar, nil]
    assert all(review.binding_call_true(*q) for q in seed)

    def example(name, n, frontier=None, known=None, enabled=True):
        target = call(n)
        result = review.case(name, lib if enabled else [], copy.deepcopy(seed if frontier is None else frontier),
                             copy.deepcopy(seed if known is None else known), [[0, *target]])
        result["native_goal_truth"] = [review.binding_call_true(*target)]
        result["semantic_boundary"] = (
            "The rule is the existing native related_list_step_schema 343 345. "
            "Known scalar and empty-list calls satisfy the existing exact contracts. "
            "This probes reuse of a constructed result; it asserts no complete search over other libraries.")
        return result

    reference_rows = [row, row]
    reference_frontier = review.binding_frontier(u, reference_rows)
    reference = review.case("chain-native-comparison", [], reference_frontier, copy.deepcopy(reference_frontier),
                            [[0, *call(2)]], ("binding", False))
    reference["binding_sources"] = [[u, reference_rows]]
    reference["native_goal_truth"] = [True]
    reference["semantic_boundary"] = (
        "The existing native converter computes the complete two-row goal directly. "
        "This comparison does not supply the goal or the intermediate call to the construction cases.")
    return [
        example("chain-rule-absent", 2, enabled=False),
        example("chain-one-construction", 1),
        example("chain-two-constructions", 2),
        example("chain-three-constructions", 3),
        example("chain-intermediate-supplied", 2, frontier=seed + [call(1)]),
        example("chain-intermediate-with-missing-evidence", 2, frontier=seed + [call(1)], known=[nil]),
        example("chain-repeated-reordered-frontier", 2, frontier=[call(1)] + seed[::-1] + seed),
        example("chain-different-intermediate-context", 2, frontier=seed + [call(1, other)]),
        reference,
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--poly", type=Path, required=True)
    parser.add_argument("--engine", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    status = review.run(args, cases_factory=chain_cases, cases_source=Path(__file__))
    if status:
        return status
    receipt_path = args.output.resolve() / "receipt.json"
    receipt = json.loads(receipt_path.read_text())
    findings = {item["case"]: item for item in receipt["findings"]}
    conditions = {
        "one_construction_settled": findings["chain-one-construction"]["residual"] == 0,
        "two_constructions_unresolved": findings["chain-two-constructions"]["residual"] == 1,
        "three_constructions_unresolved": findings["chain-three-constructions"]["residual"] == 1,
        "supplied_intermediate_settled": findings["chain-intermediate-supplied"]["residual"] == 0,
        "missing_evidence_retained": findings["chain-intermediate-with-missing-evidence"]["residual"] == 1,
        "different_context_not_joined": findings["chain-different-intermediate-context"]["residual"] == 1,
        "native_comparison_settled": findings["chain-native-comparison"]["residual"] == 0,
    }
    assert all(conditions.values()), conditions
    adequacy = {
        "question": "Can the existing generator use a constructed call in a subsequent construction from the original seeds?",
        "requirement": "Construct the two-row native list result using the scalar row call, the empty-list call, and the existing list-step rule.",
        "status": "unmet requirement for this composition workload",
        "conditions": conditions,
        "receipt": str(receipt_path),
        "receipt_sha256": review.digest(receipt_path),
        "interpretation": "The comparison establishes the original goal. The existing driver leaves it unresolved from the seeds; supplying an intermediate frontier call lets the existing inference closure settle it.",
        "remaining_question": "How should generated conditional calls become further construction inputs while retaining their unmet premises?",
        "boundary": "This is a concrete adequacy investigation of the current driver, not a proof of a completed repair or of complete construction search.",
    }
    (args.output / "adequacy.json").write_text(json.dumps(adequacy, indent=2) + "\n")
    print(json.dumps(adequacy, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
