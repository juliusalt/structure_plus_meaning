"""Conditional construction probes derived from complete exported clauses.

The backward expansion constructs test inputs, not executable inference rules.
Only its terminal calls and requested goals enter the native investigation.
Private fixture values are explicit and carry no source-reading evidence.
"""
from __future__ import annotations

import copy
import itertools
import json
from pathlib import Path

import check_reasoning as review


LIBRARIES = ("specialization_report_reasoning_library",
             "binding_observation_reasoning_library",
             "inference_reader_construction_library")
COMBINED = "inference_reader_investigation_library"


def load_catalogs(directory):
    receipt = json.loads((directory / "receipt.json").read_text())
    assert receipt["status"] == "accepted"
    catalogs = {}
    for name in [*LIBRARIES, *([COMBINED] if COMBINED in receipt["exported_libraries"] else [])]:
        path = directory / ("library-" + name + ".json")
        assert review.digest(path) == receipt["exported_libraries"][name]["sha256"]
        catalogs[name] = json.loads(path.read_text())
    return catalogs


def scope(rule):
    result = review.variables(rule["head"])
    for _, _, pattern in rule["premises"]:
        result |= review.variables(pattern)
    for _, fields in rule["materials"]:
        for pattern in fields:
            result |= review.variables(pattern)
    return result


def expand_fixture(library, call, private_values, *, stop=(), limit=20):
    """Expand a uniquely matching finite ordinary clause; reject ambiguity.

    Private assignments are supplied by the particular test. An unsupported
    call is a condition. Cycles, ambiguity, missing values, and material
    schemas require a different fixture and are never silently discarded.
    """
    if call[0] in stop:
        return [call], []
    candidates = [(entry, review.match(entry["schema"]["head"], call[1]))
                  for entry in library if entry["entry"] == call[0]]
    candidates = [(entry, values) for entry, values in candidates if values is not None]
    if not candidates:
        return [call], []
    if len(candidates) != 1 or limit <= 0:
        raise ValueError("Fixture requires a unique bounded clause expansion.")
    entry, values = candidates[0]
    rule = entry["schema"]
    assert review.schema_formed(rule) and not rule["materials"]
    extra = private_values.get(entry["entry"], {})
    assert not (values.keys() & extra.keys()), "Private assignments may not replace head fields."
    values = {**values, **copy.deepcopy(extra)}
    assert set(values) == scope(rule), (entry["entry"], "incomplete or excessive fixture valuation")
    assert all(review.formed(t) and not review.variables(t) for t in values.values())
    premises = [[s, d, review.evaluate(pattern, values)] for s, d, pattern in rule["premises"]]
    trace = [{"entry": call[0], "schema": rule, "conclusion": call[1],
              "bindings": [[v, values[v]] for v in sorted(values)], "premises": premises}]
    leaves = []
    for _, d, term in premises:
        terminal, child = expand_fixture(library, [d, term], private_values, stop=stop, limit=limit - 1)
        leaves.extend(terminal)
        trace.extend(child)
    return leaves, trace


def fixture(catalogs, offset=0):
    library = sum((catalogs[name] for name in LIBRARIES), [])
    by_entry = {entry["entry"]: entry for entry in library}
    top = by_entry[350]["schema"]
    values = {v: review.payload(30 + offset, v) for v in scope(top)}
    owner = values[5]
    rows = [review.pair(review.pair(owner, review.payload(90)),
                        review.pair(review.payload(91), review.EMPTY)),
            review.pair(review.pair(owner, review.payload(92)),
                        review.pair(review.payload(93), review.payload(94)))]
    values[19] = review.sequence(rows)
    outputs = review.binding_views(owner, rows)
    assert outputs is not None
    private = {
        350: {19: values[19]},
        348: {8: review.payload(100), 9: review.payload(101),
              10: review.sequence(outputs[0]), 11: review.sequence(outputs[1])},
    }
    root = [350, review.evaluate(top["head"], values)]
    frontier, trace = expand_fixture(library, root, private)
    known = review.binding_frontier(owner, rows)
    assert set(map(review.freeze, known)) <= set(map(review.freeze, frontier))
    assert all(review.binding_call_true(*q) for q in known)
    goals = [[s, app["entry"], app["conclusion"]] for s, app in enumerate(trace)
             if app["entry"] in {348, 349, 350}]
    return {"library": library, "frontier": frontier, "trace": trace, "known": known,
            "goals": goals, "owner": owner, "rows": rows, "top_values": values}


def reader_cases(catalogs, *, combined=False):
    base = fixture(catalogs)
    def example(name, rounds=3, selected=(348, 349, 350), **changes):
        selections = [{"name": name} for name in LIBRARIES[:-1]]
        selections += [{"name": LIBRARIES[-1], "entries": list(selected)}]
        if combined:
            originals = {e["entry"] for e in catalogs[COMBINED]} - {e["entry"] for e in catalogs[LIBRARIES[-1]]}
            selections = [{"name": COMBINED, "entries": sorted(originals | set(selected))}]
        library = sum(([e for e in catalogs[s["name"]]
                        if "entries" not in s or e["entry"] in s["entries"]] for s in selections), [])
        item = review.case(name, library, copy.deepcopy(base["frontier"]),
                           copy.deepcopy(base["known"]), copy.deepcopy(base["goals"]), ("chain", rounds))
        item.update(construction_rounds=rounds, native_libraries=selections,
                    diagnose_coverage=True,
                    semantic_boundary="Complete native clause shapes with conditional source readings. "
                    "Only the two actual binding observations are established in the ordinary cases. "
                    "Environment, record, schema, and node payload markers are structural controls; "
                    "they are not asserted to encode actual admitted source readings.")
        item.update(copy.deepcopy(changes))
        if combined and set(selected) == {348, 349, 350}:
            item["native_reader_investigation"] = True
        return item

    result = [example("reader-depth-" + str(n), n) for n in range(5)]
    for count in range(3):
        for selected in itertools.combinations([348, 349, 350], count):
            result.append(example("reader-selected-" + ("-".join(map(str, selected)) or "none"),
                                  selected=selected))
    result.append(example("reader-no-known-evidence", known=[]))
    assumed = example("reader-assumed-all-conditions", known=base["frontier"])
    assumed["semantic_boundary"] = (
        "Logical assumption control: every supplied component call is assumed. "
        "This is not evidence that the source markers have native meanings.")
    result.append(assumed)
    for i, condition in enumerate(base["frontier"]):
        item = copy.deepcopy(assumed)
        item.update(name="reader-withheld-condition-" + str(i),
                    known=[q for q in item["known"] if q != condition])
        result.append(item)
    result += [
        example("reader-reordered-repeated-frontier",
                frontier=base["frontier"][::-1] + base["frontier"]),
        example("reader-unused-malformed-source",
                frontier=base["frontier"] + [[777, review.payload(256)]]),
        example("reader-distinct-goal-occurrences",
                goals=base["goals"] + [[37, *base["goals"][0][1:]]]),
        example("reader-goal-only-possible", frontier=base["frontier"] + [base["goals"][0][1:]]),
    ]
    top = next(e["schema"] for e in base["library"] if e["entry"] == 350)
    for variable in sorted(review.variables(top["head"])):
        changed = {**base["top_values"], variable: review.payload(200, variable)}
        goal = [0, 350, review.evaluate(top["head"], changed)]
        item = example("reader-changed-public-field-" + str(variable), goals=[goal])
        item["expected_no_goal_application"] = True
        result.append(item)
    # Mutate exactly one original premise at a shared variable. Patterns and
    # bindings come from the complete expansion trace, including private rows.
    for entry, socket, variable in [(350, 0, 19), (348, 1, 3), (348, 2, 0), (342, 1, 4)]:
        app = next(a for a in base["trace"] if a["entry"] == entry)
        original = next(row for row in app["premises"] if row[0] == socket)
        pattern = next(p for s, _, p in app["schema"]["premises"] if s == socket)
        assert variable in review.variables(pattern)
        values = dict(app["bindings"]) | {variable: review.payload(201, variable)}
        changed = [original[1], review.evaluate(pattern, values)]
        frontier = [changed if q == original[1:] else q for q in base["frontier"]]
        assert frontier != base["frontier"]
        item = example("reader-broken-join-" + "-".join(map(str, [entry, socket, variable])), frontier=frontier)
        item["expected_no_goal_application"] = True
        result.append(item)
    other = fixture(catalogs, 1)
    result.append(example("reader-two-independent-contexts",
                          frontier=base["frontier"] + other["frontier"],
                          known=base["known"] + other["known"],
                          goals=[[s, *g[1:]] for s, g in enumerate(base["goals"] + other["goals"])]))
    output = review.binding_views(base["owner"], base["rows"])
    binding_goal = [0, 347, review.pair(base["owner"], review.pair(review.sequence(base["rows"]),
                           review.pair(*(review.sequence(xs) for xs in output))))]
    comparison = review.case("reader-native-binding-seed-comparison",
                              catalogs["binding_observation_reasoning_library"],
                              base["known"], base["known"], [binding_goal], ("binding", True))
    comparison.update(binding_sources=[[base["owner"], base["rows"]]], native_goal_truth=[True])
    result.append(comparison)
    return result


def catalogs_dependencies(directory):
    return [directory / "receipt.json"] + [directory / ("library-" + name + ".json")
        for name in [*LIBRARIES, COMBINED] if (directory / ("library-" + name + ".json")).exists()]
