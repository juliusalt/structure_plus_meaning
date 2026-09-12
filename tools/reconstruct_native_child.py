"""Rebuild native child validation from repository sources and the retained source fixture."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys
import time

from evidence_io import write_json
from evidence_io import digest
from machine_reports import boundary

ROOT = Path(__file__).resolve().parents[1]


def main():
    if not __debug__:
        raise ValueError("Reconstruction checks require Python assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--poly", type=Path, required=True)
    parser.add_argument("--proof", type=Path,
                        help="Recheck execution with an existing accepted export; this skips reconstruction of proof and code.")
    parser.add_argument("--session", default="Native_Child_Reconstruction")
    parser.add_argument("--threads", type=int, default=12)
    parser.add_argument("--timeout", type=int, default=480)
    parser.add_argument("--expected", type=Path,
                        default=ROOT / "validation/reconstruction/native-child-reports.json")
    args = parser.parse_args()
    assert args.threads > 0 and args.timeout > 0
    output = args.output.resolve()
    assert not output.exists(), "Use a fresh reconstruction directory."
    output.mkdir(parents=True)
    poly = args.poly.resolve()
    tools = ROOT / "tools"
    env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1", "USER_HOME": "/tmp/structural-isabelle"}
    steps = []
    tracked = {str(path): digest(path) for path in
               [Path(__file__).resolve(), Path(__file__).with_name("machine_reports.py"),
                args.expected.resolve()]}
    expected_reports = json.loads(args.expected.read_text())
    assert expected_reports["version"] == 1

    def run(name, command, timeout):
        log = output / (name + ".log")
        started = time.monotonic()
        with log.open("x") as stream:
            try:
                result = subprocess.run(list(map(str, command)), cwd=ROOT, env=env,
                                        stdout=stream, stderr=subprocess.STDOUT, timeout=timeout)
                code = result.returncode
            except subprocess.TimeoutExpired:
                code = "timeout"
        record = {"name": name, "command": list(map(str, command)), "exit_code": code,
                  "seconds": time.monotonic() - started, "log": str(log)}
        print(json.dumps(record), flush=True)
        return record

    def finish():
        expected = 4 if args.proof else 7
        complete = len(steps) == expected and all(step["exit_code"] == 0 for step in steps)
        reports = {}
        if complete:
            for stage in ["baseline", "catalog", "inputs", "reasoning"]:
                reports[stage] = boundary(output / stage / "results.log")
            complete = reports == expected_reports["reports"]
        stable = all(digest(Path(path)) == sha for path, sha in tracked.items())
        complete = complete and stable
        rebuilt = args.proof is None and all(any(step["name"] == name and step["exit_code"] == 0
                                                for step in steps) for name in ["proof", "export"])
        result = {"status": "accepted" if complete else "failed", "steps": steps,
                  "sources_rebuilt": rebuilt, "source_project": str(ROOT),
                  "report_boundaries": reports, "reports_equal": reports == expected_reports["reports"],
                  "recipe_inputs": tracked, "recipe_inputs_unchanged": stable,
                  "boundary": "A run without --proof reconstructs proof, exported code, baseline inputs and all native checks from repository sources. The optional supplied-export mode rechecks execution only. The assertion child remains an assumption; whole-graph and closed-proof admission are separate."}
        write_json(output / "reconstruction.json", result)
        return int(not complete)

    if args.proof:
        proof = args.proof.resolve()
    else:
        steps.append(run("proof", [sys.executable, "-B", tools / "prove_context.py",
            "--project", ROOT, "--output", output / "proof", "--session", args.session,
            "--threads", args.threads, "--timeout", args.timeout, "Inference_Claim_Input_Execution"], 3600))
        databases = list(Path("/tmp/structural-isabelle/.isabelle").glob(
            "*/heaps/*/log/" + args.session + ".db"))
        if len(databases) != 1:
            steps.append({"name": "diagnostics", "exit_code": "missing_or_ambiguous_database",
                          "databases": list(map(str, databases))})
            return finish()
        steps.append(run("diagnostics", [sys.executable, "-B", tools / "proof_diagnostics.py",
            "--database", databases[0], "--proof", output / "proof/result.json",
            "--output", output / "proof-diagnostics.json"], 120))
        if any(step["exit_code"] != 0 for step in steps):
            return finish()
        steps.append(run("export", [sys.executable, "-B", tools / "export_proved_code.py",
            "--proof", output / "proof/result.json", "--project", ROOT,
            "--output", output / "export", "--module",
            "Inference_Claim_Input_Execution:inference_claim_input.ML"], 180))
        if steps[-1]["exit_code"] != 0:
            return finish()
        proof = output / "export/inference_claim_input.proof.json"

    common = ["--proof", proof, "--poly", poly]
    jobs = [("baseline", [sys.executable, "-B", tools / "check_nonempty_construction_inputs.py",
                           *common, "--output", output / "baseline"], 300),
            ("catalog", [sys.executable, "-B", tools / "check_child_primitives.py",
                          *common, "--project", ROOT, "--output", output / "catalog"], 300)]
    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [pool.submit(run, *job) for job in jobs]
        initial = [future.result() for future in futures]
    steps.extend(initial)
    if any(step["exit_code"] != 0 for step in initial):
        return finish()
    steps.append(run("inputs", [sys.executable, "-B", tools / "check_proved_nonempty_inputs.py",
        *common, "--baseline", output / "baseline", "--output", output / "inputs"], 300))
    if steps[-1]["exit_code"] != 0:
        return finish()
    steps.append(run("reasoning", [sys.executable, "-B", tools / "check_proved_nonempty_reasoning.py",
        *common, "--catalog", output / "catalog", "--inputs", output / "inputs",
        "--output", output / "reasoning"], 1200))
    return finish()


if __name__ == "__main__":
    raise SystemExit(main())
