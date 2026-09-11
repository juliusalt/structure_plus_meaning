#!/usr/bin/env python3
"""Build a source-screening comparison from complete executed requirements."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import check_guided_reasoning as guided
import check_reasoning as review
import compare_reasoning_methods as compare


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        raise ValueError("Source comparison requires Python assertions to be enabled.")
    assert not args.output.exists(), "Retain earlier comparisons and use a new directory."
    cases, reports = guided.load_baseline(args.run)
    requirements = {}
    for line in (args.run / "results.log").read_text().splitlines():
        if line.startswith("ENVIRONMENT_REQUIREMENT_RESULT "):
            identifier, raw = line.removeprefix("ENVIRONMENT_REQUIREMENT_RESULT ").split(" ", 1)
            requirements[int(identifier)] = json.loads(raw)
    assert set(requirements) == {i for i, c in enumerate(cases) if c.get("environment_requirements")}
    assert requirements
    observations, measurements = [], []
    for i, rows in requirements.items():
        assert rows and len(rows) == len(cases[i]["environment_requirements"])
        formed = reports[i]["input_formed"]
        possible = all(row["possible_outer_shape"] for row in rows)
        if formed:
            observations.append([0, i, 0])
        if possible:
            observations.append([1, i, 0])
        measurements.append({"candidate": i, "case": cases[i]["name"], "input_formed": formed,
                             "all_necessary_shapes": possible, "requirements": rows})
    evidence = [{"path": str(path.resolve()), "sha256": review.digest(path)} for path in
                [args.run / name for name in ["receipt.json", "cases.json", "results.log"]]
                + [Path(__file__), Path(compare.__file__)]]
    scope = {
        "candidates": {str(i): cases[i]["name"] for i in requirements},
        "facets": {"0": "The original complete construction input is formed",
                   "1": "Every top-reader request passes the necessary environment shape"},
        "comparison": "Preservation of all supplied necessary screening conditions.",
        "boundary": "Failure of the source-shape requirement rules out the exact native request by the retained theorem. Success establishes only that necessary condition. These candidates do not supply complete native source evidence or an inhabited reader example.",
    }
    case = compare.comparison_case(list(requirements), [0, 1], observations, [0],
        question="Does structural input formation distinguish which original reader requests survive the necessary source check?",
        scope=scope, evidence=evidence)
    args.output.mkdir(parents=True)
    (args.output / "case.json").write_text(json.dumps(case, indent=2) + "\n")
    (args.output / "measurements.json").write_text(json.dumps(measurements, indent=2) + "\n")
    print(json.dumps({"candidates": len(case["candidates"]), "observations": len(observations),
                      "case": str(args.output / "case.json")}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
