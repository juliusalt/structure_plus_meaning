"""A check's command timings are located in the text its session checked, read without changing the database."""
from compression import zstd
import hashlib
import json
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import unittest

import proof_timings

TOOL = Path(__file__).resolve().parent / "proof_timings.py"
WORKSPACE = 'theory T imports A B begin\nlemma x: True by simp\nexport_code f checking SML\nend\n'
CHECKED = 'theory T imports "Base_1.A" "Base_1.B" begin\nlemma x: True by simp\nexport_code f checking SML\nend\n'
OTHER = 'theory U imports T begin\nend\n'


def timing(fields):
    return "\x05\x06:\x06" + "\x06".join(k + "=" + v for k, v in fields.items()) + "\x05"


def session_database(path, text):
    offset = str(text.index("export_code") + 1)
    raw = timing({"elapsed": "0.2", "name": "theory", "offset": "1", "file": "/proof/theories/T.thy"}) + \
        timing({"elapsed": "3.25", "name": "export_code", "offset": offset, "file": "/proof/theories/T.thy"})
    with sqlite3.connect(path) as connection:
        connection.execute("create table isabelle_session_info (session_name text, command_timings blob)")
        connection.execute("create table isabelle_sources (session_name text, name text, compressed boolean, body blob)")
        connection.execute("insert into isabelle_session_info values (?,?)", ("S", zstd.compress(raw.encode())))
        connection.execute("insert into isabelle_sources values (?,?,?,?)",
                           ("S", "/proof/theories/T.thy", True, zstd.compress(text.encode())))
        connection.execute("insert into isabelle_sources values (?,?,?,?)",
                           ("S", "/proof/theories/U.thy", False, OTHER.encode()))
        connection.execute("update isabelle_session_info set command_timings=?", (zstd.compress((raw + timing(
            {"elapsed": "0.1", "name": "theory", "offset": "1", "file": "/proof/theories/U.thy"})).encode()),))
    connection.close()


class ProofTimings(unittest.TestCase):
    def test_commands_are_located_in_the_checked_text(self):
        with tempfile.TemporaryDirectory() as directory:
            database = Path(directory) / "log" / "S.db"
            database.parent.mkdir()
            session_database(database, CHECKED)
            self.assertNotEqual(WORKSPACE.index("export_code"), CHECKED.index("export_code"))
            before = hashlib.sha256(database.read_bytes()).hexdigest()
            database.chmod(0o444)
            database.parent.chmod(0o555)
            try:
                run = subprocess.run([sys.executable, "-B", str(TOOL), "--database", str(database), "--theory", "T",
                                      "--output", str(Path(directory) / "out" / "timings.json")],
                                     capture_output=True, text=True)
            finally:
                database.parent.chmod(0o755)
            self.assertEqual(run.returncode, 0, run.stderr)
            rows = [json.loads(line) for line in run.stdout.splitlines()]
            self.assertEqual([(r["line"], r["command"], r["seconds"]) for r in rows],
                             [(1, "theory", 0.2), (3, "export_code", 3.25)])
            self.assertEqual(rows[1]["source_line"], "export_code f checking SML")
            retained = json.loads((Path(directory) / "out" / "timings.json").read_text())
            self.assertEqual({row["theory"] for row in retained["completed_commands"]}, {"T"})
            self.assertEqual(list(retained["sources"]), ["T"])
            self.assertEqual(hashlib.sha256(database.read_bytes()).hexdigest(), before)
            self.assertEqual(sorted(p.name for p in database.parent.iterdir()), ["S.db"])

    def test_a_theory_the_session_did_not_check_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            database = Path(directory) / "S.db"
            session_database(database, CHECKED)
            run = subprocess.run([sys.executable, "-B", str(TOOL), "--database", str(database), "--theory", "V",
                                  "--output", str(Path(directory) / "timings.json")], capture_output=True, text=True)
            self.assertNotEqual(run.returncode, 0)
            self.assertIn("checked no theory named V", run.stderr)

    def test_checked_sources_by_theory(self):
        with tempfile.TemporaryDirectory() as directory:
            database = Path(directory) / "S.db"
            session_database(database, CHECKED)
            self.assertEqual(proof_timings.checked_sources(database), {"T": CHECKED, "U": OTHER})


if __name__ == "__main__":
    unittest.main()
