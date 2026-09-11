#!/usr/bin/env python3
"""Check complete libraries compiled from their actual schema fields."""
from __future__ import annotations

import argparse
import copy
from pathlib import Path

import check_reasoning as review
import check_construction_chains as chains


def compiled_sources(sources):
    result = []
    for source in sources:
        ps = source["schema"]["premises"]
        enumeration = (sorted({review.freeze(row): row for row in ps}.values(), key=lambda row: row[0])
                       if review.functional(ps) else [])
        result.append({**copy.deepcopy(source), "enumeration": copy.deepcopy(enumeration)})
    return result


def compilation_cases():
    selected = [x for x in review.cases() if "binding_sources" not in x]
    selected += [x for x in chains.chain_cases() if x["name"].startswith("chain-expanded")]
    v, p = review.variable, review.payload
    selected += [
        review.case("single-schema-premise",
                    review.library(21, review.schema(v(0), [[0, 20, v(0)]])),
                    [[20, p(7)]], [[20, p(7)]], [[0, 21, p(7)]]),
        review.case("duplicate-identical-schema-premise",
                    review.library(21, review.schema(v(0), [[0, 20, v(0)], [0, 20, v(0)]])),
                    [[20, p(7)]], [[20, p(7)]], [[0, 21, p(7)]]),
        review.case("unordered-schema-sockets",
                    review.library(21, review.schema(v(0), [[7, 20, v(0)], [1, 20, v(0)]])),
                    [[20, p(7)]], [[20, p(7)]], [[0, 21, p(7)]]),
        review.case("empty-schema-premise-family", review.library(21, review.schema(p(7))),
                    [], [], [[0, 21, p(7)]]),
    ]
    result = []
    for original in selected:
        item = copy.deepcopy(original)
        sources = [{"entry": e["entry"], "schema": copy.deepcopy(e["schema"])} for e in item["library"]]
        rounds = item.get("construction_rounds", 0)
        item.update(name="compiled-" + item["name"], compilation_sources=sources,
                    library=compiled_sources(sources), operation=("chain", rounds),
                    construction_rounds=rounds, diagnose_coverage=True)
        result.append(item)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--poly", type=Path, required=True)
    parser.add_argument("--engine", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--case", action="append", help="Run named cases from the retained family")
    args = parser.parse_args()
    def selected_cases():
        family = compilation_cases()
        if args.case:
            assert set(args.case) <= {item["name"] for item in family}, "Unknown case name."
            family = [item for item in family if item["name"] in args.case]
        return family
    return review.run(args, cases_factory=selected_cases, cases_source=Path(__file__),
                      cases_dependencies=[Path(chains.__file__)])


if __name__ == "__main__":
    raise SystemExit(main())
