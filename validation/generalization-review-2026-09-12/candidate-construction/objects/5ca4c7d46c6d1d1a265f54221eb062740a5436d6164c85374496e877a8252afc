#!/usr/bin/env python3
"""Locate completed Isabelle commands in their exact retained source snapshot."""
from __future__ import annotations

import argparse
from compression import zstd
import hashlib
import json
from pathlib import Path
import re
import sqlite3


def source_line(source, offset):
    # Isabelle offsets count escaped symbols as single characters.
    symbols = re.sub(r"\\<[^>]+>", "X", source)
    line = symbols[:max(0, int(offset) - 1)].count("\n") + 1
    return line, source.splitlines()[line - 1]


def command_timings(database):
    with sqlite3.connect("file:" + str(database.resolve()) + "?mode=ro", uri=True) as connection:
        rows = connection.execute("select command_timings from isabelle_session_info").fetchall()
    assert len(rows) == 1 and rows[0][0], "The session has not retained its command timings."
    raw = zstd.decompress(rows[0][0]).decode()
    commands = []
    for match in re.finditer("\x05\x06:\x06([^\x05]+)\x05", raw):
        fields = dict(part.split("=", 1) for part in match[1].split("\x06"))
        if "file" in fields and "offset" in fields:
            commands.append(fields)
    return commands


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", type=Path, required=True)
    parser.add_argument("--sources", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    complete = []
    sources = {}
    for command in command_timings(args.database):
        name = Path(command["file"]).name
        path = args.sources / name
        if not path.is_file():
            continue
        source = path.read_text()
        line, text = source_line(source, command["offset"])
        sources[str(path.resolve())] = hashlib.sha256(path.read_bytes()).hexdigest()
        complete.append({**command, "theory": path.stem, "line": line, "source_line": text})
    result = {"database": str(args.database.resolve()), "sources": sources,
              "tool_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "completed_commands": complete,
              "boundary": "These are retained completed command timings. The next command may be unfinished; timing data does not establish proof acceptance."}
    assert not args.output.exists(), "Retain the preceding diagnostic."
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    for name in sorted({row["theory"] for row in complete}):
        rows = sorted((r for r in complete if r["theory"] == name), key=lambda r: int(r["offset"]))
        print(json.dumps({"theory": name, "last_completed": rows[-3:]}, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
