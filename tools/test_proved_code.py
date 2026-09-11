"""Reject stale or unsuccessful proof inputs before any runtime is selected."""
import json
from pathlib import Path
import tempfile
import unittest

import investigate
import proved_code


class ProvedCodeTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="proved-code-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "theories").mkdir()
        self.source = self.root / "theories/Fixture.thy"
        self.source.write_text("theory Fixture imports Main begin end\n")
        self.engine = self.root / "fixture.ML"
        self.engine.write_text("val fixture = true;\n")
        self.proof = self.root / "proof.json"
        self.receipt = {"status": "accepted", "exit_code": 0, "sources_unchanged": True,
                        "sources": {"Fixture": investigate.file_hash(self.source)},
                        "exports": [{"path": str(self.engine), "sha256": investigate.file_hash(self.engine)}]}
        self.write_receipt()

    def write_receipt(self):
        self.proof.write_text(json.dumps(self.receipt))

    def test_exact_inputs_select_original_export(self):
        _, engine, sources = proved_code.proved_export(self.proof, project=self.root,
                                                      required_theories=["Fixture"])
        self.assertEqual(engine, self.engine)
        self.assertEqual(sources[str(self.source)], investigate.file_hash(self.source))

    def test_failed_or_changed_proof_is_rejected(self):
        for field, value in [("status", "failed"), ("exit_code", 1), ("sources_unchanged", False)]:
            with self.subTest(field=field):
                original = self.receipt[field]
                self.receipt[field] = value
                self.write_receipt()
                with self.assertRaises(AssertionError):
                    proved_code.proved_export(self.proof, project=self.root)
                self.receipt[field] = original

    def test_changed_current_source_is_rejected(self):
        self.source.write_text("changed source\n")
        with self.assertRaises(AssertionError):
            proved_code.proved_export(self.proof, project=self.root)

    def test_changed_export_or_unproved_requirement_is_rejected(self):
        with self.assertRaises(AssertionError):
            proved_code.proved_export(self.proof, project=self.root, required_theories=["Missing"])
        self.engine.write_text("changed code\n")
        with self.assertRaises(AssertionError):
            proved_code.proved_export(self.proof, project=self.root)


if __name__ == "__main__":
    unittest.main()
