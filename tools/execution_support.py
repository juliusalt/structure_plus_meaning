"""Shared physical source, evidence and ML-literal operations; no investigation controller."""
from __future__ import annotations

import hashlib
from pathlib import Path
import re

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_hash(path: Path) -> str:
    return digest(path.read_bytes())


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def natural(value) -> bool:
    return type(value) is int and value >= 0


def theory_imports(source: str, name: str) -> list[str]:
    # Only this repository's deliberately simple theory headers are accepted.
    # No declaration, proof body, or arbitrary Isabelle syntax is parsed here.
    match = re.match(r"\s*theory\s+([A-Za-z_][A-Za-z_0-9]*)\s+imports\s+([\s\S]*?)\s+begin\b", source)
    require(match is not None and match[1] == name, f"Unsupported theory header: {name}")
    tokens = re.findall(r'"[A-Za-z_][A-Za-z_0-9./-]*"|[A-Za-z_][A-Za-z_0-9.-]*', match[2])
    require("".join(tokens) == re.sub(r"\s+", "", match[2]), f"Unsupported imports in {name}")
    return [token.strip('"') for token in tokens]


def source_graph(project: Path, overlays: list[Path], roots: list[str]) -> tuple[dict, dict]:
    inventory = {p.stem: p for p in (project / "theories").glob("*.thy")}
    for directory in overlays:
        require(directory.is_dir(), f"Missing overlay directory: {directory}")
        inventory.update({p.stem: p for p in directory.glob("*.thy")})
    sources, parents, active, chain = {}, {}, set(), []

    def visit(name: str, importer: str = "") -> None:
        # chain is the path the traversal is on, so a refusal names the importer that demanded
        # name, and a cycle the whole chain that closes it, without a second traversal.
        if name in active:
            cycle = chain[chain.index(name):] + [name]
            raise ValueError(f"Cyclic theory import: {name}; " + " imports ".join(cycle) + ".")
        if name in sources:
            return
        if name not in inventory:
            demanded = f", imported by {importer}" if importer else ""
            require(name in {"Main", "HOL", "Pure"} or name.startswith(("HOL.", "HOL-Library.")),
                    f"Missing local theory: {name}{demanded}")
            return
        active.add(name)
        chain.append(name)
        path = inventory[name].resolve()
        data = path.read_bytes()
        imported = theory_imports(data.decode("utf-8"), name)
        for parent in imported:
            visit(parent, name)
        active.remove(name)
        chain.pop()
        parents[name] = imported
        sources[name] = {"path": str(path), "sha256": digest(data), "text": data.decode("utf-8")}

    for root in roots:
        require(root in inventory, f"Missing requested theory: {root}")
        visit(root)
    return sources, parents


def import_contexts(parents: dict, names) -> set[str]:
    """The union of the import contexts of names; each local theory is visited once."""
    result, pending = set(), list(names)
    while pending:
        node = pending.pop()
        if node in result or node not in parents:
            continue
        result.add(node)
        pending.extend(parents[node])
    return result


def import_context(parents: dict, name: str) -> set[str]:
    return import_contexts(parents, [name])


def contexts_satisfying(parents: dict, holds) -> dict[str, bool]:
    """Whether holds is true throughout the entire import context of every local theory.

    A context is the theory and the contexts of its local parents, so each theory is decided once
    from its own condition and its parents' decisions.
    """
    decided = {}
    for root in parents:
        pending = [(root, False)]
        while pending:
            name, expanded = pending.pop()
            if name in decided:
                continue
            local = [parent for parent in parents[name] if parent in parents]
            if expanded:
                require(all(parent in decided for parent in local), f"Cyclic theory import: {name}")
                decided[name] = holds(name) and all(decided[parent] for parent in local)
            else:
                pending.append((name, True))
                pending.extend((parent, False) for parent in local if parent not in decided)
    return decided


def current_sources(sources: dict) -> bool:
    return all(file_hash(Path(item["path"])) == item["sha256"] for item in sources.values())


def archive_evidence(output: Path, receipt: dict, role: str, path: Path, expected: str) -> None:
    data = path.read_bytes()
    require(digest(data) == expected, f"Evidence changed before archiving: {path}")
    archive = output / ("evidence-" + receipt["invocation"]) / expected
    archive.parent.mkdir(parents=True, exist_ok=True)
    if archive.exists():
        require(archive.read_bytes() == data, f"Evidence archive changed: {archive}")
    else:
        archive.write_bytes(data)
    receipt.setdefault("evidence_archive", []).append({"role": role, "path": str(path.resolve()),
        "sha256": expected, "archive": str(archive)})


def ml_string(value: str) -> str:
    return '"' + "".join(f"\\{byte:03d}" for byte in value.encode("utf-8")) + '"'


def ml_list(values, encode) -> str:
    return "[" + ",".join(encode(value) for value in values) + "]"


def ml_nat(value: int) -> str:
    require(natural(value), "Only natural numbers can be passed as identifiers.")
    return f"n {value}"


def ml_tuple(values) -> str:
    # Isabelle tuples associate to the right; SML tuples do not.
    if len(values) == 2:
        return "(" + ml_nat(values[0]) + "," + ml_nat(values[1]) + ")"
    return "(" + ml_nat(values[0]) + "," + ml_tuple(values[1:]) + ")"
