#!/usr/bin/env python3
"""Export selected code modules from one unchanged accepted proof snapshot."""
from __future__ import annotations

import argparse
import copy
import json
import os
from pathlib import Path
import re
import subprocess
import uuid

import investigate
import proved_code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--module", action="append", required=True, metavar="THEORY:FILENAME")
    args = parser.parse_args()
    proof_path, output = args.proof.resolve(), args.output.resolve()
    modules = [value.split(":") for value in args.module]
    assert all(len(row) == 2 and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", row[0])
               and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*\.ML", row[1]) for row in modules)
    assert len({name for _, name in modules}) == len(modules)
    proof, sources = proved_code.accepted_proof(proof_path, required_theories=[t for t, _ in modules])
    snapshot = proof_path.parent
    effective = {str(snapshot / "theories" / (name + ".thy")): sha
                 for name, sha in proof["effective_source_hashes"].items()}
    assert all(investigate.file_hash(Path(p)) == sha for p, sha in effective.items())
    original = proof_path.read_bytes()
    root_file = snapshot / "ROOT"
    session = re.search(r"^session (\S+) =", root_file.read_text()).group(1)
    tracked = {str(p.resolve()): investigate.file_hash(p) for p in
               [proof_path, root_file, Path(__file__), Path(proved_code.__file__),
                Path(investigate.__file__)]} | sources | effective
    assert not output.exists(), "Retain preceding exports and use a new directory."
    output.mkdir(parents=True)
    report = {"status": "failed", "invocation": str(uuid.uuid4()),
              "proof": str(proof_path), "proof_sha256": investigate.digest(original),
              "session": session, "execution_inputs": tracked}
    command = ["isabelle", "export", "-n", "-d", str(snapshot), "-O", str(output / "code")]
    for theory, filename in modules:
        command += ["-x", f"*{theory}:code/{filename}"]
    command.append(session)
    report["command"] = command
    log_path = output / "export.log"
    try:
        with log_path.open("w") as log:
            result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT,
                                    env={**os.environ, "USER_HOME": "/tmp/structural-isabelle"}, timeout=60)
        report["exit_code"] = result.returncode
        assert result.returncode == 0, "See the retained export.log."
        assert proof_path.read_bytes() == original
        assert all(investigate.file_hash(Path(p)) == sha for p, sha in tracked.items())
        exports = []
        for theory, filename in modules:
            paths = list((output / "code").rglob(filename))
            assert len(paths) == 1, (theory, filename, paths)
            path = paths[0]
            entry = {"path": str(path), "sha256": investigate.file_hash(path)}
            derived = copy.deepcopy(proof)
            derived.update(exports=[entry], export_theory=theory, export_command=command,
                           pre_export_receipt_sha256=investigate.digest(original),
                           export_exit_code=0, export_log=str(log_path),
                           export_log_sha256=investigate.file_hash(log_path))
            receipt = output / (path.stem + ".proof.json")
            receipt.write_text(json.dumps(derived, indent=2) + "\n")
            exports.append({"theory": theory, **entry, "proof": str(receipt),
                            "proof_sha256": investigate.file_hash(receipt)})
        report.update(status="accepted", sources_and_tools_unchanged=True, exports=exports,
                      log_sha256=investigate.file_hash(log_path))
    except Exception as error:
        report["error"] = str(error)
    (output / "receipt.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "execution_inputs"}, indent=2))
    return int(report["status"] != "accepted")


if __name__ == "__main__":
    raise SystemExit(main())
