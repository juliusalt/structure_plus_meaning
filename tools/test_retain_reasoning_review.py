"""Proof retention follows recorded identities after their live paths change."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import retain_reasoning_review as retain


class ProofInputRetention(unittest.TestCase):
    def test_original_parent_and_export_inputs_are_retained(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            context, fallback, live = [base / name for name in ["context", "fallback", "live"]]
            for directory in [context, fallback, live]:
                directory.mkdir()
            old_proof = fallback / "old-proof.json"
            old_proof.write_text(json.dumps({"identity": "original parent proof"}))
            old_parent = fallback / "old-parent.json"
            old_parent.write_text(json.dumps({"proof_receipt_sha256": retain.digest(old_proof)}))
            parent = live / "build.json"
            parent.write_text(json.dumps({"proof_receipt_sha256": "different current proof"}))
            (live / "proof.json").write_text("changed current proof")
            exporter = live / "export.py"
            exporter.write_text("original exporter\n")
            helper = live / "helper.py"
            helper.write_text("original helper\n")
            exported = {str(exporter): retain.digest(exporter)}
            inherited = {str(helper): retain.digest(helper)}
            (context / "result.json").write_text(json.dumps({"status": "accepted", "exit_code": 0,
                "sources_unchanged": True, "sources": {}, "export_inputs": exported}))
            (context / "parent.json").write_text(json.dumps({"receipt": str(parent),
                "receipt_sha256": retain.digest(old_parent), "inputs": inherited}))
            specification = base / "specification.json"
            specification.write_text(json.dumps({"proofs": {"fixture": {"path": str(context)}}, "runs": {}}))
            output = base / "archive"
            arguments = ["retain", "--specification", str(specification), "--output", str(output),
                         "--project", str(base), "--fallback-sources", str(fallback)]
            with patch("sys.argv", arguments), contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(retain.main(), 0)
            proof = json.loads((output / "index.json").read_text())["proofs"]["fixture"]
            self.assertEqual(json.loads((output / proof["parent_proof_receipt"]).read_text()),
                             {"identity": "original parent proof"})
            self.assertEqual(set(proof["inputs"]), {str(parent), str(exporter), str(helper)})
            for path, sha in {**exported, **inherited, str(parent): retain.digest(old_parent)}.items():
                self.assertEqual(retain.digest(output / proof["inputs"][path]), sha)

    def test_compressed_historical_json_keeps_its_original_identity(self):
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            original = base / "original.json"
            original.write_text(json.dumps({"value": [1, 2, 3]}))
            sha = retain.digest(original)
            with patch.object(retain.evidence_io, "PACK_THRESHOLD", 1):
                first = retain.Archive(base / "first", [], [])
                first.add(original)
            (first.output / "archive.json").write_text(json.dumps({"files": first.stored, "encodings": first.encodings}))
            original.write_text(json.dumps({"value": "changed"}))
            second = retain.Archive(base / "second", [first.output], [])
            self.assertEqual(second.read_json(original, sha), {"value": [1, 2, 3]})

    def test_conflicting_procedure_input_identities_are_rejected(self):
        with self.assertRaisesRegex(AssertionError, "conflicting input identities"):
            retain.proof_execution_inputs({"export_inputs": {"source": "first"}},
                                          {"helper_inputs": {"source": "second"}})


if __name__ == "__main__":
    unittest.main()
