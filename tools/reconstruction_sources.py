"""Collect a reconstruction recipe's source closure without retaining generated output."""
from __future__ import annotations

import argparse
import ast
from pathlib import Path
import platform
import subprocess

from evidence_io import digest, write_json
import execution_support as investigate


STAGE_TOOLS = (
    "reconstruction_sources.py", "materialize_source_boundary.py", "prove_context.py",
    "proof_diagnostics.py", "export_proved_code.py",
)


def recipe_inputs(path):
    tree = ast.parse(path.read_text(), filename=str(path))
    declarations = [node.value for node in tree.body
                    if isinstance(node, ast.Assign)
                    and any(isinstance(target, ast.Name) and target.id == "RECIPE" for target in node.targets)]
    assert len(declarations) == 1, "Expected one literal reconstruction recipe."
    call = declarations[0]
    assert isinstance(call, ast.Call) and isinstance(call.func, ast.Name) and call.func.id == "Recipe"
    arguments = {item.arg: item.value for item in call.keywords}
    name = ast.literal_eval(arguments["name"])
    roots = ast.literal_eval(arguments["roots"])
    fixtures = ast.literal_eval(arguments["fixtures"]) if "fixtures" in arguments else ()
    assert isinstance(name, str) and roots and all(isinstance(root, str) for root in roots)
    assert all(isinstance(item, str) for item in fixtures)
    jobs = []
    for node in ast.walk(arguments["groups"]):
        if isinstance(node, ast.Call):
            assert isinstance(node.func, ast.Name) and node.func.id == "Execution", "Nonliteral execution declaration."
            assert len(node.args) >= 2
            script = ast.literal_eval(node.args[1])
            assert isinstance(script, str)
            jobs.append(script)
    assert jobs, "The recipe must execute at least one report family."
    return name, tuple(roots), tuple(fixtures), tuple(jobs)


def local_python_closure(directory, seeds, modules=None):
    """The local import closure of seeds; modules shares each file's digest and imports between calls."""
    pending = list(seeds)
    files = {}
    modules = {} if modules is None else modules
    while pending:
        path = pending.pop().resolve()
        assert path.is_relative_to(directory) and path.is_file()
        if path in files:
            continue
        if path not in modules:
            raw = path.read_bytes()
            tree = ast.parse(raw, filename=str(path))
            names = []
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    names.extend(item.name.split(".")[0] for item in node.names)
                elif isinstance(node, ast.ImportFrom):
                    assert not node.level, "Relative tool imports require an explicit source-closure account."
                    if node.module:
                        names.append(node.module.split(".")[0])
            modules[path] = (investigate.digest(raw), names)
        files[path], names = modules[path]
        for name in names:
            candidate = directory / (name + ".py")
            if candidate.is_file():
                pending.append(candidate)
    return files


def collect(project, recipe, poly, *, isabelle_version=None, graph=None, modules=None):
    """A recipe's complete input manifest.

    Given the project's already read source graph, the theory closure is its projection onto the
    recipe roots and the caller checks every collected input once when its validation completes.
    """
    if not __debug__:
        raise ValueError("Source-boundary collection requires assertions.")
    project, recipe, poly = map(lambda path: path.resolve(), [project, recipe, poly])
    directory = project / "tools"
    assert recipe.is_relative_to(directory) and recipe.is_file() and poly.is_file()
    name, roots, fixtures, jobs = recipe_inputs(recipe)
    if graph is None:
        sources, _ = investigate.source_graph(project, [], list(roots))
    else:
        complete, parents = graph
        assert set(roots) <= complete.keys(), "Missing requested theory."
        sources = {theory: complete[theory] for theory in investigate.import_contexts(parents, roots)}
    python = local_python_closure(directory, [recipe, *(directory / item for item in (*STAGE_TOOLS, *jobs))],
                                  modules)
    files = {"theories/" + key + ".thy": value["sha256"] for key, value in sources.items()}
    files.update({str(path.relative_to(project)): sha for path, sha in python.items()})
    for item in (*fixtures, "validation/reconstruction/" + name + "-reports.json"):
        relative = Path(item)
        path = (project / relative).resolve()
        assert not relative.is_absolute() and ".." not in relative.parts
        assert path.is_relative_to(project) and path.is_file(), item
        files[item] = digest(path)
    if graph is None:
        assert investigate.current_sources(sources)
        assert all(digest(project / path) == sha for path, sha in files.items()), "Inputs changed during collection."
    version = isabelle_version or subprocess.run(["isabelle", "version"], capture_output=True, text=True,
                                                check=True).stdout.strip()
    return {
        "version": 1, "roots": list(roots),
        "toolchain": {"isabelle": version, "python": platform.python_version(), "poly_sha256": digest(poly)},
        "command": ["python3", "-B", str(recipe.relative_to(project)), "--poly", "<PolyML executable>",
                    "--output", "<fresh output directory>", "--session", "<fresh Isabelle session>"],
        "files": dict(sorted(files.items())),
        "boundary": "The complete original theory import closure, local Python import closure, declared "
                    "fixtures and complete-report comparison are repository inputs. Proof, code and "
                    "reports are reconstructed outputs. This collection records dependencies and bytes; "
                    "the rebuilt Isabelle proofs and executed native contracts establish meaning.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--recipe", type=Path, required=True)
    parser.add_argument("--poly", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    specification = collect(args.project, args.recipe, args.poly)
    write_json(args.output, specification)
    import json
    print(json.dumps({"manifest": str(args.output), "files": len(specification["files"]),
                      "theories": sum(path.startswith("theories/") for path in specification["files"]),
                      "python": sum(path.endswith(".py") for path in specification["files"])}))


if __name__ == "__main__":
    main()
