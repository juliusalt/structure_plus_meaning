#!/usr/bin/env python3
"""Recover retained Isabelle messages even when theory timings are absent."""
from __future__ import annotations

import argparse
from compression import zstd
import hashlib
import json
from pathlib import Path
import sqlite3

from observation_contracts import parse_yxml
from proof_timings import command_timings, source_line


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def text_content(node):
    if isinstance(node, str):
        return node
    return "".join(text_content(child) for child in node["body"])


def yxml_elements(raw):
    tree = parse_yxml("\x05\x06diagnostic_body\x05" + raw + "\x05\x06\x05")
    assert all(isinstance(node, dict) for node in tree["body"]), "Expected a complete element sequence."
    return tree["body"]


def diagnose(database, proof, source_map=None):
    proof_bytes = proof.read_bytes()
    proof_digest = hashlib.sha256(proof_bytes).hexdigest()
    receipt = json.loads(proof_bytes)
    expected = receipt["effective_source_hashes"]
    sources = ({name: Path(path) for name, path in source_map.items()}
               if source_map is not None else
               {name: proof.parent / "theories" / (name + ".thy") for name in expected})
    assert sources.keys() == expected.keys(), "The source map must cover the complete rebuilt context."
    assert all(digest(sources[name]) == sha for name, sha in expected.items()), "Changed diagnostic source."
    source_texts = {name: path.read_text() for name, path in sources.items()}
    initial_digest = digest(database)
    with sqlite3.connect("file:" + str(database.resolve()) + "?mode=ro", uri=True) as connection:
        session_rows = connection.execute(
            "select session_name,return_code,length(theory_timings),length(command_timings),errors "
            "from isabelle_session_info").fetchall()
        assert len(session_rows) == 1, "Expected one retained session."
        exports = connection.execute(
            "select theory_name,compressed,body from isabelle_exports "
            "where name=? order by theory_name", ("PIDE/messages",)).fetchall()
        stored_sources = connection.execute(
            "select name,compressed,body from isabelle_sources where session_name=?",
            (session_rows[0][0],)).fetchall()
    error_blob = session_rows[0][4]
    error_yxml = zstd.decompress(error_blob).decode() if error_blob else ""
    error_nodes = yxml_elements(error_yxml)
    assert all(node["tag"] == ":" and not node["attributes"] for node in error_nodes), "Malformed session error list."
    session_errors = [{"tree": node, "text": text_content(node)} for node in error_nodes]
    database_sources = {}
    for name, compressed, body in stored_sources:
        path = Path(name)
        if path.suffix != ".thy" or path.stem not in expected:
            continue
        assert path.stem not in database_sources, "Ambiguous retained theory source."
        raw = zstd.decompress(body) if compressed else body
        database_sources[path.stem] = {"name": name, "sha256": hashlib.sha256(raw).hexdigest()}
    assert database_sources.keys() == expected.keys(), "The database must retain the complete rebuilt source context."
    assert all(database_sources[name]["sha256"] == sha for name, sha in expected.items()), "Database source differs from proof source."

    def location(properties):
        name = Path(properties.get("file", "")).stem
        if name not in source_texts:
            return {"mapped": False, "reason": "No retained rebuilt source for this message position."}
        if "offset" in properties:
            line, content = source_line(source_texts[name], properties["offset"])
        elif "line" in properties:
            line = int(properties["line"])
            content = source_texts[name].splitlines()[line - 1]
        else:
            return {"mapped": False, "reason": "The retained message has no source offset or line."}
        return {"mapped": True, "theory": name, "source_sha256": expected[name],
                "line": line, "source_line": content}

    messages = []
    for theory, compressed, body in exports:
        raw = (zstd.decompress(body) if compressed else body).decode()
        nodes = yxml_elements(raw)
        messages.append({"theory": theory, "raw_yxml": raw,
                         "raw_sha256": hashlib.sha256(raw.encode()).hexdigest(),
                         "messages": [{"tree": node, "text": text_content(node),
                                       "location": location(node["attributes"])} for node in nodes]})
    commands = (command_timings(database) if session_rows[0][3] else [])
    commands = [{**command, "location": location(command)} for command in commands]
    assert digest(database) == initial_digest, "The retained database changed during diagnosis."
    assert digest(proof) == proof_digest, "The proof receipt changed during diagnosis."
    assert all(digest(sources[name]) == sha for name, sha in expected.items()), "Diagnostic source changed."
    return {"database": str(database.resolve()), "database_sha256": initial_digest,
            "proof": str(proof.resolve()), "proof_sha256": proof_digest,
            "session": session_rows[0][0], "return_code": session_rows[0][1],
            "theory_timing_bytes": session_rows[0][2],
            "sources": {name: {"path": str(path.resolve()), "sha256": expected[name]}
                        for name, path in sources.items()},
            "database_sources": database_sources,
            "completed_commands": commands, "message_exports": messages,
            "session_error_yxml": error_yxml, "session_errors": session_errors,
            "boundary": "Every retained session error and PIDE/messages export is read directly from the terminal database, "
                        "independently of the theory-timing domain. Positions refer to the exact retained "
                        "rebuilt source. Completed commands and messages do not establish session acceptance."}


def main():
    if not __debug__:
        raise ValueError("Diagnostic identity checks require assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--database", type=Path, required=True)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--source-map", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists(), "Retain the preceding diagnostic."
    source_map = json.loads(args.source_map.read_text()) if args.source_map else None
    result = diagnose(args.database, args.proof, source_map)
    args.output.write_text(json.dumps(result, separators=(",", ":")) + "\n")
    errors = [{"theory": export["theory"], **message}
              for export in result["message_exports"] for message in export["messages"]
              if message["tree"]["tag"] == "error_message"]
    print(json.dumps({"session": result["session"], "return_code": result["return_code"],
                      "theory_timing_bytes": result["theory_timing_bytes"],
                      "complete_message_exports": len(result["message_exports"]),
                      "messages": sum(len(e["messages"]) for e in result["message_exports"]),
                      "completed_commands": len(result["completed_commands"]),
                      "session_errors": [error["text"] for error in result["session_errors"]],
                      "message_errors": errors}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
