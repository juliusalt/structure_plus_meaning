"""Exercise the full-session evidence required before reusing a parent context."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import investigate
import prove_context


class ParentContextTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="parent-context-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        files = {
            "ROOT": "session Parent = HOL +\n  theories\n    Fixture\n",
            "theories/Fixture.thy": "theory Fixture imports Main begin end\n",
            "tools/build.py": "# fixture build tool\n",
            "tools/check.py": "# fixture source checker\n",
            "validation/build.log": "Finished Parent\n",
        }
        for name, text in files.items():
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        hashes = {name: investigate.file_hash(self.root / name) for name in files}
        self.receipt = {
            "status": "accepted", "exit_code": 0, "invocation": "fixture",
            "sources_unchanged": True, "tools_unchanged": True,
            "command": ["isabelle", "build", "-D", str(self.root)],
            "sources": {name: hashes[name] for name in ["ROOT", "theories/Fixture.thy"]},
            "tools": {name: hashes[name] for name in ["tools/build.py", "tools/check.py"]},
            "log_sha256": hashes["validation/build.log"],
        }
        self.checked = {
            "status": "accepted", "exit_code": 0, "invocation": "fixture",
            "sources_and_tools_unchanged": True, "theory_count": 1,
            "missing_theory_files": [], "unlisted_theories": [], "proof_escape_matches": [],
        }
        self.save()

    def save(self, embed=True):
        if embed:
            self.checked["build_evidence"] = copy.deepcopy(self.receipt)
        for name, value in [("build", self.receipt), ("check", self.checked)]:
            (self.root / "validation" / (name + ".json")).write_text(json.dumps(value))

    def test_accepted_parent_retains_every_input(self):
        session, sources, inputs = prove_context.accepted_parent(self.root)
        self.assertEqual(session, "Parent")
        self.assertEqual(sources, {"Fixture": self.receipt["sources"]["theories/Fixture.thy"]})
        self.assertEqual(set(inputs), {str(self.root / name) for name in [
            "ROOT", "theories/Fixture.thy", "tools/build.py", "tools/check.py",
            "validation/build.log", "validation/build.json", "validation/check.json"]})

    def test_mutated_source_tool_or_log_is_rejected(self):
        for name in ["ROOT", "theories/Fixture.thy", "tools/build.py", "tools/check.py", "validation/build.log"]:
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                path.write_bytes(original + b"changed\n")
                with self.assertRaises(AssertionError):
                    prove_context.accepted_parent(self.root)
                path.write_bytes(original)

    def test_incomplete_inventory_is_rejected(self):
        for name in list(self.receipt["sources"]):
            with self.subTest(name=name):
                sha = self.receipt["sources"].pop(name)
                self.save()
                with self.assertRaises(AssertionError):
                    prove_context.accepted_parent(self.root)
                self.receipt["sources"][name] = sha

    def test_partial_session_command_is_rejected(self):
        for command in [["isabelle", "build", "-d", str(self.root), "Fixture"],
                        ["isabelle", "build", "-D", str(self.root / "elsewhere")]]:
            self.receipt["command"] = command
            self.save()
            with self.assertRaises(AssertionError):
                prove_context.accepted_parent(self.root)

    def test_incomplete_build_tool_inventory_is_rejected(self):
        for name in list(self.receipt["tools"]):
            with self.subTest(name=name):
                sha = self.receipt["tools"].pop(name)
                self.save()
                with self.assertRaises(AssertionError):
                    prove_context.accepted_parent(self.root)
                self.receipt["tools"][name] = sha

    def test_failed_stale_or_escaping_checks_are_rejected(self):
        for field, bad in [("status", "failed"), ("exit_code", 1), ("invocation", "different"),
                           ("sources_and_tools_unchanged", False), ("theory_count", 2),
                           ("missing_theory_files", ["Missing"]), ("unlisted_theories", ["New"]),
                           ("proof_escape_matches", ["sorry"])]:
            with self.subTest(field=field):
                original = self.checked[field]
                self.checked[field] = bad
                self.save()
                with self.assertRaises(AssertionError):
                    prove_context.accepted_parent(self.root)
                self.checked[field] = original

    def test_mismatched_embedded_build_evidence_is_rejected(self):
        self.receipt["invocation"] = "new build"
        self.save(embed=False)
        with self.assertRaises(AssertionError):
            prove_context.accepted_parent(self.root)

    def test_optimized_python_rejects_before_reading_inputs(self):
        command = [sys.executable, "-B", "-O", "-c",
                   "import prove_context; from pathlib import Path; "
                   "prove_context.accepted_parent(Path('/nonexistent-parent-context'))"]
        result = subprocess.run(command, cwd=Path(__file__).parent, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("require Python assertions", result.stderr)


if __name__ == "__main__":
    unittest.main()
