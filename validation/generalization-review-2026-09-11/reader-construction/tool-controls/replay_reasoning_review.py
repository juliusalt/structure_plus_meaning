#!/usr/bin/env python3
"""Replay an exact retained case family with its original checker and code."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if not __debug__:
        raise ValueError("Evidence replay requires Python assertions to be enabled.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--stage", required=True)
    parser.add_argument("--poly", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    base = args.archive.resolve()
    manifest = json.loads((base / "archive.json").read_text())
    for name, sha in manifest["files"].items():
        assert digest(base / name) == sha, name
    index_path = base / "index.json"
    index = json.loads(index_path.read_text())
    assert index["version"] == 1
    stage = index["runs"][args.stage]
    proof = index["proofs"][stage["proof"]]
    assert proof["status"] == "accepted"
    assert set(stage["external"].values()) == {digest(args.poly.resolve())}
    output = args.output.resolve()
    assert not output.exists(), "Use a new replay directory."
    (output / "source/theories").mkdir(parents=True)
    (output / "tools").mkdir()
    for name, reference in proof["sources"].items():
        shutil.copyfile(base / reference, output / "source/theories" / (name + ".thy"))
    for name, reference in stage["inputs"].items():
        path = Path(name)
        if path.suffix == ".py":
            destination = output / "tools" / path.name
            assert not destination.exists() or digest(destination) == digest(base / reference), path.name
            shutil.copyfile(base / reference, destination)
    sys.path.insert(0, str(output / "tools"))
    import check_reasoning as review
    review.ROOT = output / "source"
    cases_file = base / stage["files"]["cases.json"]
    cases = json.loads(cases_file.read_text())
    parameters = argparse.Namespace(proof=base / proof["receipt"], engine=base / proof["engine"],
                                    poly=args.poly.resolve(), output=output / "run")
    status = review.run(parameters, cases_factory=lambda: cases, cases_source=cases_file,
                        cases_dependencies=[Path(__file__), index_path],
                        library_exports=stage["library_exports"])
    receipt = json.loads((parameters.output / "receipt.json").read_text())
    before = json.loads((base / stage["files"]["receipt.json"]).read_text())
    if stage["expected_failure"]:
        assert status == 1 and receipt["status"] == "failed"
        assert stage["expected_failure"] in (parameters.output / "results.log").read_text()
    else:
        assert status == 0 and receipt["status"] == "accepted"
        for field in ["reasoning_cases", "binding_source_executions", "construction_frontier_executions",
                      "construction_seed_executions", "coverage_executions", "compilation_executions",
                      "native_library_executions"]:
            assert receipt.get(field, 0) == before.get(field, 0), field
        # Compiler diagnostics contain the relocated module's absolute path.
        # Compare every complete machine report, retaining both raw logs.
        labels = {"REASONING_RESULT", "BINDING_RESULT", "CONSTRUCTION_FRONTIER",
                  "CONSTRUCTION_SEED", "COVERAGE_RESULT", "COMPILED_LIBRARY",
                  "LIBRARY_CATALOG", "INPUT_RESULT"}
        reports = lambda path: [line for line in path.read_text().splitlines()
                                if line.partition(" ")[0] in labels]
        assert reports(parameters.output / "results.log") == reports(base / stage["files"]["results.log"])
    evidence = {
        "stage": args.stage, "status": "expected failure reproduced" if stage["expected_failure"] else "accepted",
        "receipt_sha256": digest(parameters.output / "receipt.json"),
        "archive_index_sha256": digest(index_path), "replayer_sha256": digest(Path(__file__)),
        "boundary": "The retained inputs and original code are replayed. This reproduces complete checked reports; it does not rerun case selection or establish new native source readings.",
    }
    (output / "replay.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print(json.dumps(evidence, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
