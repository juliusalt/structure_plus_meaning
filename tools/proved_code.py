"""Shared prerequisites for running code from an accepted source proof."""
from __future__ import annotations

import json
from pathlib import Path

import investigate

ROOT = Path(__file__).resolve().parents[1]


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
