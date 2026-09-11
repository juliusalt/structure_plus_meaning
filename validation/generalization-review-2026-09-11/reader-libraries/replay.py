#!/usr/bin/env python3
"""Replay complete retained inputs with their exact checker and generated module."""
from pathlib import Path
from argparse import ArgumentParser, Namespace
import hashlib
import inspect
import json
import shutil
import sys


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    base = Path(__file__).resolve().parent
    runs = json.loads((base / "runs/index.json").read_text())
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=sorted(runs), required=True)
    parser.add_argument("--poly", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--project", type=Path, help="Optional matching checkout; otherwise use retained source bytes")
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        parser.error("Use a new output directory.")
    manifest = base / "archive.json"
    if manifest.exists():
        for name, expected in json.loads(manifest.read_text())["files"].items():
            assert digest(base / name) == expected, name
    output.mkdir(parents=True)
    stage = runs[args.stage]
    source = base / stage["path"]
    proofs = json.loads((base / "proofs/index.json").read_text())
    proof = proofs[stage["proof"]]
    assert proof["status"] == "accepted"
    if args.project:
        project = args.project.resolve()
    else:
        project = output / "source"
        (project / "theories").mkdir(parents=True)
        index = json.loads((base / "projects" / (stage["project"] + ".json")).read_text())
        for name, item in index["sources"].items():
            original = base / item["blob"]
            assert digest(original) == item["sha256"], name
            shutil.copy2(original, project / "theories" / (name + ".thy"))
    sys.path.insert(0, str(base / "common-tools"))
    sys.path.insert(0, str(source / "checker-sources"))
    import check_reasoning as review
    review.ROOT = project
    cases_file = source / "cases.json"
    cases = json.loads(cases_file.read_text())
    inputs = Namespace(proof=base / proof["receipt"], engine=base / proof["engine"],
                       poly=args.poly.resolve(), output=output / "run")
    options = {"cases_factory": lambda: cases, "cases_source": cases_file}
    parameters = inspect.signature(review.run).parameters
    if "cases_dependencies" in parameters:
        options["cases_dependencies"] = [Path(__file__), base / "common-tools/build.py"]
    if stage["library_exports"]:
        options["library_exports"] = stage["library_exports"]
    status = review.run(inputs, **options)
    receipt = json.loads((inputs.output / "receipt.json").read_text())
    expected_failure = stage["expected_failure"]
    if expected_failure:
        assert status == 1 and receipt["status"] == "failed"
        assert "Exception- Match raised" in (inputs.output / "results.log").read_text()
    else:
        assert status == 0 and receipt["status"] == "accepted"
        before = json.loads((source / "receipt.json").read_text())
        for field in ["reasoning_cases", "binding_source_executions", "construction_frontier_executions",
                      "construction_seed_executions", "coverage_executions", "compilation_executions"]:
            assert receipt.get(field, 0) == before.get(field, 0), field
        for name, item in before.get("exported_libraries", {}).items():
            assert receipt["exported_libraries"][name]["sha256"] == item["sha256"], name
    evidence = {
        "stage": args.stage,
        "outcome": "expected runtime failure reproduced" if expected_failure else "complete replay accepted",
        "case_source_sha256": digest(cases_file),
        "checker_sha256": digest(Path(review.__file__)),
        "build_helper_sha256": digest(base / "common-tools/build.py"),
        "replay_script_sha256": digest(Path(__file__)),
        "receipt": str(inputs.output / "receipt.json"),
        "receipt_sha256": digest(inputs.output / "receipt.json"),
        "boundary": "Inputs are replayed directly from the retained case file. This is validation of the recorded family, not a new content discovery or a new native mathematical proof.",
    }
    (output / "replay.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(json.dumps(evidence, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
