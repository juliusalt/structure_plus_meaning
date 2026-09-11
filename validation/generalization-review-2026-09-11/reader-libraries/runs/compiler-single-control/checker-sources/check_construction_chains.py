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


def baseline_cases():
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


def chain_cases():
    result = baseline_cases()
    one = result[1]
    for name, target_source, rounds, withhold in [
        ("chain-expanded-two-constructions", result[2], 1, False),
        ("chain-expanded-three-constructions", result[3], 2, False),
        ("chain-expanded-insufficient-depth", result[3], 1, False),
        ("chain-expanded-missing-evidence", result[3], 2, True),
        ("chain-expanded-zero-compatible", result[2], 0, False),
    ]:
        item = copy.deepcopy(target_source)
        item.update(name=name, operation=("chain", rounds), construction_rounds=rounds)
        if withhold:
            item["known"] = [q for q in item["known"] if q[0] != 343]
        result.append(item)
    changed = copy.deepcopy(result[-4])
    changed.update(name="chain-expanded-unused-malformed-call")
    changed["frontier"].append([400, review.payload(256)])
    result.append(changed)
    changed = copy.deepcopy(result[-5])
    changed.update(name="chain-expanded-repeated-reordered-frontier")
    changed["frontier"] = changed["frontier"][::-1] + changed["frontier"]
    result.append(changed)

    owner, body = one["frontier"][0][1]["pair"]
    row, value = body["pair"]
    second_row = review.pair(review.pair(owner, review.payload(61)), review.pair(review.payload(9), review.EMPTY))
    second_value = review.pair(review.payload(61), review.payload(9))
    diversity = copy.deepcopy(result[10])
    diversity.update(name="chain-expanded-two-row-alphabet", operation=("chain", 2), construction_rounds=2)
    diversity["frontier"].append([343, review.pair(owner, review.pair(second_row, second_value))])
    diversity["known"] = copy.deepcopy(diversity["frontier"])
    target = review.pair(owner, review.pair(review.sequence([row, second_row, row]),
                                         review.sequence([value, second_value, value])))
    diversity.update(goals=[[0, 345, target]], native_goal_truth=[review.binding_call_true(345, target)])
    result.append(diversity)

    def native_case(name, rounds, target, source_owner=owner, source_row=row, enabled=True, admit_row=True):
        views = review.binding_views(source_owner, [source_row])
        frontier = [] if views is None else [
            [343, review.pair(source_owner, review.pair(source_row, views[0][0]))],
            [345, review.pair(source_owner, review.pair(review.payload(), review.payload()))]]
        known = copy.deepcopy(frontier if admit_row else [q for q in frontier if q[0] != 343])
        item = review.case(name, one["library"] if enabled else [], frontier, known, copy.deepcopy(target["goals"]),
                           ("native_chain", rounds, enabled, admit_row))
        item.update(construction_rounds=rounds, construction_source=[source_owner, source_row],
                    native_goal_truth=[review.binding_call_true(d, t) for _, d, t in item["goals"]],
                    semantic_boundary="The exported native row constructor establishes the actual scalar and empty-list seeds; the existing native list-step library constructs further calls while retaining conditional evidence.")
        return item

    result += [
        native_case("chain-native-seeds-two-constructions", 1, result[2]),
        native_case("chain-native-seeds-three-constructions", 2, result[3]),
        native_case("chain-native-seeds-withheld", 2, result[3], admit_row=False),
        native_case("chain-native-seeds-rule-absent", 2, result[2], enabled=False),
        native_case("chain-native-seeds-wrong-owner", 2, result[2], source_owner=review.payload(51)),
        native_case("chain-native-seeds-malformed-owner", 2, result[2], source_owner=review.payload(256)),
        native_case("chain-native-seeds-malformed-unreturned-value", 2, result[2],
                    source_row=review.pair(row["pair"][0], review.pair(review.payload(8), review.payload(256)))),
    ]
    wrong_value = review.pair(review.payload(60), review.payload(99))
    repeated_input = review.sequence([row, row])
    wrong_outputs = review.sequence([value, wrong_value])
    wrong_termination = review.pair(value, review.pair(value, review.payload(9)))
    wrong_output = {"goals": [[0, 345, review.pair(owner, review.pair(repeated_input, wrong_outputs))]]}
    wrong_tail = {"goals": [[0, 345, review.pair(owner, review.pair(repeated_input, wrong_termination))]]}
    result += [
        native_case("chain-native-false-output", 2, wrong_output),
        native_case("chain-native-false-output-tail", 2, wrong_tail),
    ]
    # The complete pre-existing generic controls also exercise the equivalent
    # finite-set input representation at zero extra rounds.
    for original in review.cases():
        if original.get("binding_sources") is not None:
            continue
        item = copy.deepcopy(original)
        item.update(name="chain-zero-" + original["name"], operation=("chain", 0), construction_rounds=0)
        result.append(item)
    return result


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
        "expanded_two_constructions_settled": findings["chain-expanded-two-constructions"]["residual"] == 0,
        "expanded_three_constructions_settled": findings["chain-expanded-three-constructions"]["residual"] == 0,
        "insufficient_depth_retained": findings["chain-expanded-insufficient-depth"]["residual"] == 1,
        "expanded_missing_evidence_retained": findings["chain-expanded-missing-evidence"]["residual"] == 1,
        "native_seeds_settled": findings["chain-native-seeds-three-constructions"]["residual"] == 0,
        "native_withheld_evidence_retained": findings["chain-native-seeds-withheld"]["residual"] == 1,
        "malformed_original_source_rejected": not findings["chain-native-seeds-malformed-unreturned-value"]["formed"],
        "unused_malformed_call_rejected": not findings["chain-expanded-unused-malformed-call"]["formed"],
        "two_row_alphabet_constructed": findings["chain-expanded-two-row-alphabet"]["residual"] == 0,
        "false_output_retained": findings["chain-native-false-output"]["residual"] == 1,
        "false_output_tail_retained": findings["chain-native-false-output-tail"]["residual"] == 1,
    }
    assert all(conditions.values()), conditions
    adequacy = {
        "question": "Can the existing generator use a constructed call in a subsequent construction from the original seeds?",
        "requirement": "Construct the two-row native list result using the scalar row call, the empty-list call, and the existing list-step rule.",
        "status": "bounded repair meets the demonstrated composition requirement",
        "conditions": conditions,
        "receipt": str(receipt_path),
        "receipt_sha256": review.digest(receipt_path),
        "interpretation": "The original driver leaves the composed goal unresolved. Additional construction rounds generate the intermediate frontier themselves, and the existing conditional inference closes the goal from the original seeds. Withheld evidence and inadequate depth remain unresolved.",
        "remaining_question": "Apply the repaired driver to actual development decisions and assess whether its current reusable language covers those decisions.",
        "boundary": "The universal contracts cover every finite round bound and admitted library. The execution family does not establish complete unbounded search or coverage of every development decision.",
    }
    (args.output / "adequacy.json").write_text(json.dumps(adequacy, indent=2) + "\n")
    print(json.dumps(adequacy, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
