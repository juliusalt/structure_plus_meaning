"""Reconstruct proved executions and compare their complete retained reports."""
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys
import time

from evidence_io import digest, write_json
from machine_reports import boundary, unique_object


@dataclass(frozen=True)
class Execution:
    name: str
    script: str
    arguments: tuple[str, ...] = ()
    timeout: int = 300


@dataclass(frozen=True)
class Recipe:
    name: str
    roots: tuple[str, ...]
    export: str
    session: str
    groups: tuple[tuple[Execution, ...], ...]
    boundary: str

    @property
    def executions(self):
        return tuple(job.name for group in self.groups for job in group)


def finish_reconstruction(output, project, recipe, steps, expected, tracked, supplied_export):
    names = (() if supplied_export else ("proof", "diagnostics", "export")) + recipe.executions
    stages_complete = tuple(step["name"] for step in steps) == names
    stages_complete = stages_complete and all(step["exit_code"] == 0 for step in steps)
    reports, error = {}, None
    if stages_complete:
        try:
            reports = {stage: boundary(output / stage / "results.log") for stage in recipe.executions}
        except (OSError, ValueError, AssertionError) as failure:
            error = str(failure)
    stable = all(Path(path).is_file() and digest(Path(path)) == sha for path, sha in tracked.items())
    equal = reports == expected["reports"]
    accepted = stages_complete and error is None and equal and stable
    rebuilt = not supplied_export and all(
        any(step["name"] == name and step["exit_code"] == 0 for step in steps)
        for name in ("proof", "diagnostics", "export"))
    result = {"status": "accepted" if accepted else "failed", "recipe": recipe.name, "steps": steps,
              "sources_rebuilt": rebuilt, "source_project": str(project),
              "report_boundaries": reports, "reports_equal": equal,
              "recipe_inputs": tracked, "recipe_inputs_unchanged": stable,
              "boundary": recipe.boundary}
    if error is not None:
        result["error"] = error
    write_json(output / "reconstruction.json", result)
    return result


def main(recipe, entrypoint, argv=None):
    if not __debug__:
        raise ValueError("Reconstruction checks require Python assertions.")
    entrypoint = Path(entrypoint).resolve()
    project = entrypoint.parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--poly", type=Path, required=True)
    parser.add_argument("--proof", type=Path,
                        help="Recheck an existing accepted export without reconstructing proof or code.")
    parser.add_argument("--session", default=recipe.session)
    parser.add_argument("--threads", type=int, default=12)
    parser.add_argument("--timeout", type=int, default=480)
    parser.add_argument("--expected", type=Path,
                        default=project / "validation/reconstruction" / (recipe.name + "-reports.json"))
    args = parser.parse_args(argv)
    assert args.threads > 0 and args.timeout > 0
    assert all(recipe.groups) and len(recipe.executions) == len(set(recipe.executions))
    assert not set(recipe.executions) & {"proof", "diagnostics", "export"}
    expected = json.loads(args.expected.read_text(), object_pairs_hook=unique_object)
    assert expected["version"] == 1 and set(expected["reports"]) == set(recipe.executions)
    output = args.output.resolve()
    assert not output.exists(), "Use a fresh reconstruction directory."
    output.mkdir(parents=True)
    poly = args.poly.resolve()
    tools = project / "tools"
    env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1", "USER_HOME": "/tmp/structural-isabelle"}
    steps = []
    tracked = {str(path): digest(path) for path in
               (entrypoint, Path(__file__).resolve(), Path(__file__).with_name("machine_reports.py"),
                args.expected.resolve())}

    def run(name, command, timeout):
        log = output / (name + ".log")
        started = time.monotonic()
        with log.open("x") as stream:
            try:
                code = subprocess.run(list(map(str, command)), cwd=project, env=env,
                                      stdout=stream, stderr=subprocess.STDOUT, timeout=timeout).returncode
            except subprocess.TimeoutExpired:
                code = "timeout"
        record = {"name": name, "command": list(map(str, command)), "exit_code": code,
                  "seconds": time.monotonic() - started, "log": str(log)}
        print(json.dumps(record), flush=True)
        return record

    def finish():
        result = finish_reconstruction(output, project, recipe, steps, expected, tracked, args.proof is not None)
        return int(result["status"] != "accepted")

    if args.proof:
        proof = args.proof.resolve()
    else:
        steps.append(run("proof", [sys.executable, "-B", tools / "prove_context.py", "--project", project,
            "--output", output / "proof", "--session", args.session, "--threads", args.threads,
            "--timeout", args.timeout, *recipe.roots], 3600))
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
            "--proof", output / "proof/result.json", "--project", project,
            "--output", output / "export", "--module", recipe.export], 180))
        if steps[-1]["exit_code"] != 0:
            return finish()
        proof = output / "export" / (Path(recipe.export.split(":")[1]).stem + ".proof.json")

    substitutions = {"project": str(project), "output": str(output), "proof": str(proof), "poly": str(poly)}
    for group in recipe.groups:
        jobs = [(job.name, [sys.executable, "-B", tools / job.script,
                  "--proof", proof, "--poly", poly,
                  *(argument.format_map(substitutions) for argument in job.arguments),
                  "--output", output / job.name], job.timeout) for job in group]
        if len(jobs) == 1:
            results = [run(*jobs[0])]
        else:
            with ThreadPoolExecutor(max_workers=len(jobs)) as pool:
                futures = [pool.submit(run, *job) for job in jobs]
                results = [future.result() for future in futures]
        steps.extend(results)
        if any(step["exit_code"] != 0 for step in results):
            return finish()
    return finish()
