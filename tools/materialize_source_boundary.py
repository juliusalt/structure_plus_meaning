"""Materialize a verified repository source boundary without generated evidence."""
from pathlib import Path
import argparse
import json
import shutil

from evidence_io import digest, write_json
from machine_reports import unique_object


def materialize(project, manifest, output):
    if not __debug__:
        raise ValueError("Source-boundary checks require Python assertions.")
    project, manifest, output = (Path(path).resolve() for path in [project, manifest, output])
    specification = json.loads(manifest.read_text(), object_pairs_hook=unique_object)
    assert specification["version"] == 1
    assert not output.exists(), "Use a fresh source directory."
    sources = []
    for name, sha in specification["files"].items():
        relative = Path(name)
        assert not relative.is_absolute() and ".." not in relative.parts
        source = (project / relative).resolve()
        assert source.is_relative_to(project) and source.is_file()
        assert digest(source) == sha, name
        sources.append((relative, source, sha))
    output.mkdir(parents=True)
    for relative, source, sha in sources:
        target = output / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        assert digest(target) == sha and digest(source) == sha, str(relative)
    report = {"source_project": str(project), "manifest_sha256": digest(manifest),
              "files": len(sources), "output": str(output),
              "boundary": "Only the declared source and fixture bytes are materialized. Proof, code and reports must be reconstructed separately."}
    write_json(output / "source-boundary.json", report)
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(materialize(args.project, args.manifest, args.output)))
