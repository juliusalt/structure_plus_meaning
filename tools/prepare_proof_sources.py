"""Prepare a complete source prefix for ordinary proof checks and saved heaps."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re

import execution_support as investigate


def prepare(project: Path, roots: list[str], output: Path, session: str, timeout: int):
    if not __debug__:
        raise ValueError("Source preparation requires Python assertions.")
    assert not output.exists(), "Use a fresh output directory."
    assert re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", session), "Invalid session name."
    assert timeout > 0 and roots
    sources, _ = investigate.source_graph(project, [], roots)
    assert set(roots) <= set(sources)
    (output / "theories").mkdir(parents=True)
    (output / "tools").mkdir()
    for name, source in sources.items():
        target = output / "theories" / (name + ".thy")
        target.write_text(source["text"])
        assert investigate.file_hash(target) == source["sha256"]
    copied_tools = {}
    for name in ["build.py", "check.py"]:
        source = project / "tools" / name
        raw = source.read_bytes()
        target = output / "tools" / name
        target.write_bytes(raw)
        copied_tools["tools/" + name] = investigate.file_hash(target)
        assert source.read_bytes() == raw
    root = ("session " + session + " = HOL +\n"
            "  options [document = false, timeout = " + str(timeout) + "]\n"
            '  sessions "HOL-Library"\n  directories "theories"\n  theories\n' +
            "".join("    " + name + "\n" for name in sources))
    (output / "ROOT").write_text(root)
    assert investigate.current_sources(sources), "Sources changed during preparation."
    report = {"status": "prepared", "source_project": str(project), "roots": roots,
              "session": session, "theories": {n: s["sha256"] for n, s in sources.items()},
              "tools": copied_tools, "root_sha256": investigate.file_hash(output / "ROOT"),
              "boundary": "The original import closure and complete source bytes are copied. "
                          "Ordinary proof checks must establish acceptance before this prefix is reused."}
    (output / "source-manifest.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--session", required=True)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("roots", nargs="+")
    args = parser.parse_args()
    report = prepare(args.project.resolve(), args.roots, args.output.resolve(), args.session, args.timeout)
    print(json.dumps({k: v for k, v in report.items() if k not in ["theories", "tools"]} |
                     {"theory_count": len(report["theories"])}))


if __name__ == "__main__":
    main()
