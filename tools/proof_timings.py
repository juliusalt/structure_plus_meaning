#!/usr/bin/env python3
"""Locate completed Isabelle commands in the exact source text their session checked.

A command's offset counts the symbols of the text Isabelle processed, and that text is retained in
the session's own database (`isabelle_sources`): a check proves rewritten copies of the workspace's
theories (their imports qualified by the providing session), so the workspace's text or a proof's
`original-sources` place a command after the imports some symbols away from where it stands. The
database is therefore both the timings and the text they are located in.

The database belongs to the finished check that wrote it: it is opened read-only and immutable, so
reading it takes no lock and looks for no journal, and nothing here can change it."""
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


def read_only(database):
    """A read-only connection to a finished session database: no lock taken, no journal looked for."""
    return sqlite3.connect("file:" + str(database.resolve()) + "?mode=ro&immutable=1", uri=True)


def command_timings(database):
    with read_only(database) as connection:
        rows = connection.execute("select command_timings from isabelle_session_info").fetchall()
    assert len(rows) == 1 and rows[0][0], "The session has not retained its command timings."
    raw = zstd.decompress(rows[0][0]).decode()
    commands = []
    for match in re.finditer("\x05\x06:\x06([^\x05]+)\x05", raw):
        fields = dict(part.split("=", 1) for part in match[1].split("\x06"))
        if "file" in fields and "offset" in fields:
            commands.append(fields)
    return commands


def checked_sources(database):
    """Each theory text the session checked, by theory name, as the database retains it."""
    with read_only(database) as connection:
        sessions = connection.execute("select session_name from isabelle_session_info").fetchall()
        assert len(sessions) == 1, "Expected one retained session."
        rows = connection.execute("select name,compressed,body from isabelle_sources where session_name=?",
                                  (sessions[0][0],)).fetchall()
    texts = {}
    for name, compressed, body in rows:
        path = Path(name)
        if path.suffix != ".thy":
            continue
        assert path.stem not in texts, "Ambiguous retained theory source: " + path.stem
        texts[path.stem] = (zstd.decompress(body) if compressed else body).decode()
    return texts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--theory", action="append", default=[],
                        help="Print every completed command of this theory with its seconds (repeatable); "
                             "otherwise each theory's last three.")
    args = parser.parse_args()
    assert not args.output.exists(), "Retain the preceding diagnostic."
    texts = checked_sources(args.database)
    complete = []
    for command in command_timings(args.database):
        name = Path(command["file"]).stem
        if name not in texts:
            continue
        line, text = source_line(texts[name], command["offset"])
        complete.append({**command, "theory": name, "line": line, "source_line": text})
    missing = [name for name in args.theory if name not in texts]
    assert not missing, "The session checked no theory named " + ", ".join(missing) + "."
    if args.theory:
        complete = [row for row in complete if row["theory"] in args.theory]
    database = args.database.resolve()
    result = {"database": str(database), "database_sha256": hashlib.sha256(database.read_bytes()).hexdigest(),
              "sources": {name: hashlib.sha256(texts[name].encode()).hexdigest()
                          for name in sorted({row["theory"] for row in complete})},
              "tool_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "completed_commands": complete,
              "boundary": "These are retained completed command timings, located in the source text the session "
                          "checked. The next command may be unfinished; timing data does not establish proof acceptance."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    for name in (args.theory or sorted({row["theory"] for row in complete})):
        rows = sorted((r for r in complete if r["theory"] == name), key=lambda r: int(r["offset"]))
        if args.theory:
            for row in rows:
                print(json.dumps({"theory": name, "line": row["line"], "command": row["name"],
                                  "seconds": float(row["elapsed"]), "source_line": row["source_line"]},
                                 separators=(",", ":")))
        else:
            print(json.dumps({"theory": name, "last_completed": rows[-3:]}, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
