#!/usr/bin/env python3
"""Execute a declared conditional investigation without replacing its cases.

The specification owns the question, complete cases, interpretation boundary,
and evidence identities. Evidence hashes establish provenance, not the truth
or adequacy of an external interpretation of a conditional clause.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import check_reasoning as review


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ["specification", "proof", "poly", "output"]:
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--engine", type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise ValueError("Conditional investigation requires Python assertions.")
    spec = json.loads(args.specification.read_text())
    assert spec["question"] and spec["boundary"] and spec["cases"]
    dependencies = [args.specification]
    for entry in spec["evidence"]:
        path = Path(entry["path"])
        assert path.is_absolute() and review.digest(path) == entry["sha256"]
        dependencies.append(path)
    status = review.run(args, cases_factory=lambda: spec["cases"],
                        cases_source=Path(__file__), cases_dependencies=dependencies)
    if status:
        return status
    reports = {}
    for line in (args.output / "results.log").read_text().splitlines():
        if line.startswith("REASONING_RESULT "):
            identifier, raw = line.removeprefix("REASONING_RESULT ").split(" ", 1)
            reports[int(identifier)] = json.loads(raw)
    assert set(reports) == set(range(len(spec["cases"])))
    demands = []
    for i, item in enumerate(spec["cases"]):
        result = reports[i]
        supplied = set(map(review.freeze, item["known"]))
        constructed = {review.freeze([a["entry"], a["conclusion"]])
                       for a in result["applications"]}
        demands.append({"case": item["name"], "input_formed": result["input_formed"],
                        "residual": result["residual"],
                        "unconstructed_conditions": [q for q in result["demand"]
                            if review.freeze(q) not in supplied | constructed]})
    assessment = {"question": spec["question"], "boundary": spec["boundary"],
                  "receipt_sha256": review.digest(args.output / "receipt.json"),
                  "cases": demands,
                  "interpretation": "Unconstructed conditions are extracted from the complete returned demands. They are not a sufficient repair set when alternatives, cycles, or inconsistent conditions occur. Conditional settlement does not verify the externally supplied rule interpretation or evidence meaning."}
    (args.output / "conditions.json").write_text(json.dumps(assessment, indent=2) + "\n")
    print(json.dumps({"question": spec["question"], "cases": len(demands),
                      "remaining_counts": [len(d["unconstructed_conditions"]) for d in demands]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
