"""Complete finite presenter inputs and independent recovery of public layouts.

The recovery functions consume the established payload-and-pair presentation.
They do not decide native package, schema, or proof-node admission.
"""
from __future__ import annotations

from collections import Counter
import copy

import check_reasoning as review


def artifact(carrier=(), incidence=(), bag=(), functional=()):
    return copy.deepcopy(dict(carrier=list(carrier), incidence=list(incidence),
                              bag=list(bag), functional=list(functional)))


def environment(artifacts=(), bindings=()):
    return copy.deepcopy(dict(artifacts=list(artifacts), bindings=list(bindings)))


def artifact_identity(source):
    return (frozenset(map(review.freeze, source["carrier"])),
            frozenset(map(review.freeze, source["incidence"])),
            frozenset(Counter(map(review.freeze, source["bag"])).items()),
            frozenset(map(review.freeze, source["functional"])))


def environment_identity(source):
    return (frozenset((review.freeze(u), artifact_identity(a))
                      for u, a in source["artifacts"]),
            frozenset(map(review.freeze, source["bindings"])))


def octets(word):
    return all(type(n) is int and 0 <= n < 256 for n in word)


def artifact_formed(source):
    carrier = {tuple(a) for a in source["carrier"]}
    return (all(octets(a) for a in carrier)
            and all(all(tuple(a) in carrier for a in edge) for edge in source["incidence"])
            and all(tuple(a) in carrier and octets(p)
                    for a, p in source["bag"] + source["functional"])
            and review.functional(source["functional"]))


def environment_formed(source):
    rows = [(review.freeze(u), artifact_identity(a)) for u, a in source["artifacts"]]
    bindings = [(review.freeze([u, k]), review.freeze(v)) for u, k, v in source["bindings"]]
    return (review.functional(rows) and review.functional(bindings)
            and all(artifact_formed(a) for _, a in source["artifacts"])
            and all(any(s == u and k in a["carrier"] for s, a in source["artifacts"])
                    and any(w == v for w, _ in source["artifacts"])
                    for u, k, v in source["bindings"]))


def payload_value(term):
    assert set(term) == {"payload"}
    assert all(type(n) is int and n >= 0 for n in term["payload"])
    return term["payload"]


def pair_values(term):
    assert set(term) == {"pair"} and len(term["pair"]) == 2
    return term["pair"]


def natural_value(term):
    count = 0
    while term != review.payload():
        zero, term = pair_values(term)
        assert zero == review.payload()
        count += 1
    return count


def use_value(term):
    if term == review.payload():
        return None
    word, end = pair_values(term)
    assert end == review.payload()
    return [natural_value(n) for n in review.sequence_items(word)]


def artifact_value(term):
    atoms, rest = pair_values(term)
    edges, rest = pair_values(rest)
    bags, functions = pair_values(rest)

    def address_pair(row):
        a, p = pair_values(row)
        return [payload_value(a), payload_value(p)]

    def incidence(row):
        a, rest = pair_values(row)
        return [payload_value(a), *address_pair(rest)]

    return artifact([payload_value(a) for a in review.sequence_items(atoms)],
                    [incidence(e) for e in review.sequence_items(edges)],
                    [address_pair(b) for b in review.sequence_items(bags)],
                    [address_pair(f) for f in review.sequence_items(functions)])


def environment_value(term):
    artifacts, bindings = pair_values(term)
    rows, links = [], []
    for row in review.sequence_items(artifacts):
        use, value = pair_values(row)
        rows.append([use_value(use), artifact_value(value)])
    for row in review.sequence_items(bindings):
        source, target = pair_values(row)
        use, slot = pair_values(source)
        links.append([use_value(use), payload_value(slot), use_value(target)])
    return environment(rows, links)


def data_only(term):
    if term == review.EMPTY:
        return False
    if "payload" in term:
        payload_value(term)
        return True
    return all(data_only(t) for t in pair_values(term))


def cases():
    empty = artifact()
    complete = artifact([[2], [0], [1]], [[[0], [1], [2]]],
                        [[[0], [7]], [[0], [7]], [[2], []]],
                        [[[1], [8]]])
    one_count = copy.deepcopy(complete)
    one_count["bag"].pop(0)
    bag_only = artifact([[0]], bag=[[[0], [7]]])
    function_only = artifact([[0]], functional=[[[0], [7]]])
    reversed_rows = {k: v[::-1] for k, v in complete.items()}
    art_cases = [
        ("empty", empty),
        ("complete-repeated-bag", complete),
        ("same-fields-reordered", reversed_rows),
        ("one-fewer-bag-occurrence", one_count),
        ("bag-attachment", bag_only),
        ("functional-attachment", function_only),
        ("incidence-outside-carrier", artifact([[0]], [[[0], [1], [0]]])),
        ("bag-outside-carrier", artifact([[0]], bag=[[[1], [7]]])),
        ("conflicting-functional-values", artifact([[0]], functional=[[[0], [7]], [[0], [8]]])),
        ("nonbyte-address", artifact([[256]])),
        ("nonbyte-bag-payload", artifact([[0]], bag=[[[0], [256]]])),
        ("nonbyte-functional-payload", artifact([[0]], functional=[[[0], [256]]])),
    ]
    full_env = environment([[None, complete], [[], complete], [[256], empty]],
                           [[None, [0], []], [[], [1], [256]]])
    env_cases = [
        ("empty", environment()),
        ("three-uses-complete-bindings", full_env),
        ("same-tables-reordered", environment(full_env["artifacts"][::-1], full_env["bindings"][::-1])),
        ("wide-natural-use", environment([[[256], empty]])),
        ("missing-target-use", environment([[None, complete]], [[None, [0], []]])),
        ("missing-source-use", environment([[None, complete]], [[[], [0], None]])),
        ("missing-source-slot", environment([[None, complete]], [[None, [99], None]])),
        ("conflicting-artifact-use", environment([[None, complete], [None, empty]])),
        ("conflicting-binding-target", environment([[None, complete], [[], empty]],
                                                 [[None, [0], None], [None, [0], []]])),
        ("unformed-artifact", environment([[None, art_cases[6][1]]])),
        ("nonbyte-slot", environment([[None, empty]], [[None, [256], None]])),
    ]
    projection_cases = [
        ("empty-data", review.payload()),
        ("nested-data", review.pair(review.payload(0, 255), review.pair(review.payload(), review.payload(7)))),
        ("invalid-payload-preserved", review.payload(256)),
        ("nested-invalid-payload-preserved", review.pair(review.payload(), review.payload(256))),
        ("root-target", review.EMPTY),
        ("left-target", review.pair(review.EMPTY, review.payload())),
        ("right-nested-target", review.pair(review.payload(), review.pair(review.payload(), review.EMPTY))),
    ]
    return ([{"kind": "projection", "name": "projection-" + name, "source": source}
             for name, source in projection_cases]
            + [{"kind": "artifact", "name": "artifact-" + name, "source": source}
               for name, source in art_cases]
            + [{"kind": "environment", "name": "environment-" + name, "source": source}
               for name, source in env_cases])


def assess(inputs, outputs):
    assert len(inputs) == len(outputs)
    indexed = {}
    for item, result in zip(inputs, outputs):
        source, kind = item["source"], item["kind"]
        assert result["name"] == item["name"]
        if kind == "projection":
            expected = source if data_only(source) else None
            assert result["value"] == expected, item["name"]
            assert result["source_formed"] == review.formed(source), item["name"]
        else:
            recover, identity, formed = ((artifact_value, artifact_identity, artifact_formed)
                if kind == "artifact" else (environment_value, environment_identity, environment_formed))
            recovered = recover(result["value"])
            assert identity(recovered) == identity(source), item["name"]
            assert result["source_formed"] == formed(source), item["name"]
        expected_formed = result["value"] is not None and review.formed(result["value"])
        assert result["value_formed"] == expected_formed, item["name"]
        indexed[item["name"]] = result
    pairs = [
        ("artifact-complete-repeated-bag", "artifact-same-fields-reordered", True),
        ("artifact-complete-repeated-bag", "artifact-one-fewer-bag-occurrence", False),
        ("artifact-bag-attachment", "artifact-functional-attachment", False),
        ("environment-three-uses-complete-bindings", "environment-same-tables-reordered", True),
    ]
    for a, b, equal in pairs:
        assert (indexed[a]["value"] == indexed[b]["value"]) == equal, (a, b)
    wide = indexed["environment-wide-natural-use"]
    assert wide["source_formed"] and wide["value_formed"]
    complete = environment_value(indexed["environment-three-uses-complete-bindings"]["value"])
    assert {review.freeze(u) for u, _ in complete["artifacts"]} == {None, (), (256,)}
    shape_only = [name for name, result in indexed.items()
                  if name.startswith(("artifact-", "environment-"))
                  and not result["source_formed"] and result["value_formed"]]
    assert {"artifact-incidence-outside-carrier", "artifact-conflicting-functional-values",
            "environment-missing-target-use", "environment-conflicting-binding-target"} <= set(shape_only)
    return {"all_complete_inputs_recovered": True, "all_formation_results_agree": True,
            "permutations_preserved": True, "bag_multiplicity_and_attachment_modes_distinguished": True,
            "distinct_uses_and_wide_naturals_preserved": True,
            "shape_only_sources_rejected_by_formation": shape_only,
            "boundary": "These checks cover finite data conversion and complete source presentation. "
                        "They do not establish native package or inference readings."}
