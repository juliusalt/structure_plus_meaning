"""Shared prerequisites for running code from an accepted source proof."""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import traceback
import uuid

import investigate
from evidence_io import write_json

ROOT = Path(__file__).resolve().parents[1]


def proved_context_partition(sources, parents, accepted_sources):
    """Reuse a theory only when its entire current import context is proved."""
    if not __debug__:
        raise ValueError("Proof context checks require Python assertions.")
    assert sources.keys() == parents.keys()
    reused = {name for name in sources if all(
        accepted_sources.get(parent) == sources[parent]["sha256"]
        for parent in investigate.import_context(parents, name))}
    return reused, sources.keys() - reused


def accepted_proof(path, *, project=ROOT, required_theories=()):
    if not __debug__:
        raise ValueError("Proof export checks require Python assertions.")
    proof = json.loads(Path(path).read_text())
    assert proof["status"] == "accepted" and proof["exit_code"] == 0 and proof["sources_unchanged"]
    sources = {str(project / "theories" / (name + ".thy")): sha
               for name, sha in proof["sources"].items()}
    assert set(required_theories) <= proof["sources"].keys()
    assert all(investigate.file_hash(Path(p)) == sha for p, sha in sources.items())
    return proof, sources


def proved_export(path, engine=None, *, project=ROOT, required_theories=()):
    proof, sources = accepted_proof(path, project=project, required_theories=required_theories)
    assert len(proof["exports"]) == 1
    selected = Path(engine).resolve() if engine is not None else Path(proof["exports"][0]["path"])
    assert investigate.file_hash(selected) == proof["exports"][0]["sha256"]
    return proof, selected, sources


def archive_execution_inputs(output, receipt, inputs, *, external=()):
    """Retain every checked input except explicitly recorded external binaries."""
    external = {Path(path).resolve() for path in external}
    for path, sha in inputs.items():
        if Path(path).resolve() not in external:
            investigate.archive_evidence(output, receipt, "checked module input", Path(path), sha)


def execution_inputs_unchanged(inputs, receipt, *, external=()):
    """Check the live inputs, complete retained coverage and every retained byte."""
    external = {Path(path).resolve() for path in external}
    expected = {(str(Path(path).resolve()), sha) for path, sha in inputs.items()
                if Path(path).resolve() not in external}
    retained = receipt.get("evidence_archive", [])
    available = {(row["path"], row["sha256"]) for row in retained}
    return (expected <= available
            and all(investigate.file_hash(Path(path)) == sha for path, sha in inputs.items())
            and all(investigate.file_hash(Path(row["archive"])) == row["sha256"] for row in retained))


def accepted_execution(directory, poly, proof):
    """Recheck a complete execution before using its results as downstream inputs."""
    if not __debug__:
        raise ValueError("Execution evidence checks require Python assertions.")
    directory, poly, proof = map(lambda path: Path(path).resolve(), (directory, poly, proof))
    receipt = json.loads((directory / "receipt.json").read_text())
    assert receipt["status"] == "accepted"
    assert receipt["proof_receipt_sha256"] == investigate.file_hash(proof), "Different proved execution context."
    assert investigate.file_hash(directory / "results.log") == receipt["results_sha256"]
    assert execution_inputs_unchanged(receipt["execution_inputs"], receipt, external=[poly])
    return receipt


def checked_execution(proof_path, poly, output, *, required_theories, inputs,
                      input_paths, program, assess, question, boundary, timeout=60, project=ROOT):
    """Run one proved module with retained inputs and a caller's result review."""
    proof_path, poly, output = map(lambda p: Path(p).resolve(), (proof_path, poly, output))
    _, engine, sources = proved_export(proof_path, required_theories=required_theories, project=project)
    assert not output.exists(), "Retain preceding executions and use a new directory."
    output.mkdir(parents=True)
    receipt = {"status": "failed", "invocation": str(uuid.uuid4()),
               "question": question, "boundary": boundary}
    try:
        input_file = output / "cases.json"
        write_json(input_file, inputs)
        runtime = output / "execute.ML"
        runtime.write_text(program(engine, inputs))
        directory = Path(__file__).resolve().parent
        modules = {Path(m.__file__).resolve() for m in tuple(sys.modules.values())
                   if getattr(m, "__file__", None) and Path(m.__file__).resolve().is_relative_to(directory)
                   and Path(m.__file__).is_file()}
        paths = {proof_path, engine, poly, runtime, input_file, *modules,
                 *(Path(p).resolve() for p in input_paths), *(Path(p) for p in sources)}
        tracked = {str(p): investigate.file_hash(p) for p in paths}
        write_json(output / "execution-inputs.json", tracked)
        archive_execution_inputs(output, receipt, tracked, external=[poly])
        log_path = output / "results.log"
        with log_path.open("w") as log:
            result = subprocess.run([str(poly), "--script", str(runtime)], stdout=log,
                                    stderr=subprocess.STDOUT, timeout=timeout)
        receipt["exit_code"] = result.returncode
        assert result.returncode == 0, "See the retained results.log."
        assessment = assess(inputs, log_path.read_text())
        stable = execution_inputs_unchanged(tracked, receipt, external=[poly])
        assert stable, "Execution source, input or retained evidence changed."
        write_json(output / "complete-results.json", assessment)
        receipt.update(status="accepted", sources_and_tools_unchanged=stable, assessment=assessment,
                       proof_receipt_sha256=investigate.file_hash(proof_path),
                       export_sha256=investigate.file_hash(engine),
                       results_sha256=investigate.file_hash(log_path), execution_inputs=tracked)
    except Exception as error:
        receipt["status"] = "failed"
        receipt["error"] = str(error)
        receipt["error_type"] = type(error).__name__
        receipt["error_traceback"] = traceback.format_exc()
    write_json(output / "receipt.json", receipt)
    return receipt
