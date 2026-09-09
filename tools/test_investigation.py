#!/usr/bin/env python3
"""Exercise execution evidence and failure gates without substituting for Isabelle proofs."""
from __future__ import annotations

import importlib.util
import json
from argparse import Namespace
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest

TOOLS = Path(__file__).resolve().parent
FAKE = r'''#!/usr/bin/env python3
from pathlib import Path
import json, subprocess, sys, time
root = Path(__file__).resolve().parent
mode = (root / "mode").read_text()
if Path(__file__).name == "fake_poly":
    if "--version" in sys.argv:
        print("Poly/ML fixture"); sys.exit(0)
    (root / "runtime_called").write_text("yes")
    if mode in {"timeout", "interrupt"}:
        child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(600)"])
        (root / "child_pid").write_text(str(child.pid))
        time.sleep(600)
    if mode == "case_change":
        with (root / "case.json").open("a") as stream: stream.write(" ")
    if mode == "engine_change":
        for p in (root / "output").rglob("finite_investigation.ML"):
            p.write_text("changed generated engine")
    if mode == "malformed_result":
        print("INVESTIGATION_RESULT {}"); sys.exit(0)
    print("INVESTIGATION_RESULT " + json.dumps({"input_formed": mode != "rejected", "residual": [], "demand": [], "reasons": []}))
    sys.exit(0)
if sys.argv[1] == "version":
    print("Isabelle fixture"); sys.exit(9 if mode == "version_failure" else 0)
if sys.argv[1] == "build_log":
    print("current proof failure"); sys.exit(1)
if sys.argv[1] == "build":
    (root / "build_called").write_text("yes")
    if mode == "proof_failure": sys.exit(7)
    if mode == "source_change":
        with (root / "theories/Presentation_Completion_Investigation.thy").open("a") as stream: stream.write("\nchanged\n")
    if mode == "tool_change":
        with (root / "tools/investigate.py").open("a") as stream: stream.write("\n# changed\n")
    print("Finished fixture"); sys.exit(0)
if sys.argv[1] == "export":
    (root / "export_called").write_text("yes")
    if mode == "export_failure": sys.exit(8)
    output = Path(sys.argv[sys.argv.index("-O") + 1]); output.mkdir(parents=True)
    (output / "finite_investigation.ML").write_text("fixture module; runtime is also a fixture")
    sys.exit(0)
sys.exit(3)
'''


class InvestigationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="structural-investigation-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for name in ("tools", "theories", "output"):
            (self.root / name).mkdir()
        for name in ("build.py", "investigate.py"):
            shutil.copyfile(TOOLS / name, self.root / "tools" / name)
        (self.root / "theories/Presentation_Completion_Investigation.thy").write_text(
            "theory Presentation_Completion_Investigation imports Main begin end\n")
        for name in ("fake_isabelle", "fake_poly"):
            path = self.root / name
            path.write_text(FAKE)
            path.chmod(0o755)
        self.case = {"schema": "finite-investigation-1", "kind": "inference",
                     "question": "Fixture", "scope": "Empty finite fixture", "rules": [], "known": [], "goals": []}
        self.save_case()
        self.mode("success")
        old = {"status": "accepted", "invocation": "OLD", "exit_code": 0}
        for name in ("receipt.json", "proof.json"):
            (self.root / "output" / name).write_text(json.dumps(old))
        (self.root / "output/run.log").write_text("OLD LOG\n")

    def save_case(self):
        (self.root / "case.json").write_text(json.dumps(self.case))

    def mode(self, name):
        (self.root / "mode").write_text(name)

    def command(self, runtime_timeout="2"):
        return [sys.executable, "-B", str(self.root / "tools/investigate.py"),
            "--isabelle", str(self.root / "fake_isabelle"), "--poly", str(self.root / "fake_poly"),
            "--engine-cache", str(self.root / "cache"), "--output", str(self.root / "output"),
            "--runtime-timeout", runtime_timeout, "run", str(self.root / "case.json")]

    def execute(self, mode="success", timeout="2"):
        self.mode(mode)
        result = subprocess.run(self.command(timeout), text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=10)
        receipt = json.loads((self.root / "output/receipt.json").read_text())
        proof = json.loads((self.root / "output/proof.json").read_text())
        self.assertNotEqual(receipt["invocation"], "OLD", result.stdout)
        self.assertEqual(receipt["invocation"], proof["invocation"], result.stdout)
        self.assertNotIn("OLD LOG", (self.root / "output/run.log").read_text())
        self.assertNotEqual(receipt["status"], "running", result.stdout)
        return result, receipt, proof

    def test_success_binds_proof_export_case_and_runtime(self):
        result, receipt, proof = self.execute()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(receipt["status"], "evaluated")
        self.assertEqual(proof["status"], "accepted")
        self.assertTrue(receipt["sources_and_tools_unchanged"])
        for key in ("generated_engine_sha256", "proof_receipt_sha256", "runtime_program_sha256", "case_sha256", "log_sha256"):
            self.assertEqual(len(receipt[key]), 64)

    def test_failed_proof_never_exports_or_executes(self):
        result, receipt, proof = self.execute("proof_failure")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(proof["status"], "not_checked")
        self.assertIn("current proof failure", receipt["session_diagnostics"])
        self.assertFalse((self.root / "export_called").exists())
        self.assertFalse((self.root / "runtime_called").exists())

    def test_startup_and_source_failures_never_export(self):
        for mode in ("version_failure", "source_change", "tool_change"):
            with self.subTest(mode=mode):
                result, receipt, proof = self.execute(mode)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(receipt["status"], "failed")
                self.assertEqual(proof["status"], "not_checked")
                self.assertFalse((self.root / "export_called").exists())

    def test_export_failure_does_not_execute(self):
        result, receipt, proof = self.execute("export_failure")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(receipt["status"], "failed")
        self.assertEqual(proof["status"], "accepted")
        self.assertFalse((self.root / "runtime_called").exists())

    def test_changed_inputs_and_malformed_results_cannot_be_evaluated(self):
        for mode in ("case_change", "engine_change", "malformed_result"):
            with self.subTest(mode=mode):
                result, receipt, _ = self.execute(mode)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(receipt["status"], "failed")

    def test_invalid_identifiers_are_rejected_before_build(self):
        for identifier in (-1, True, "0"):
            with self.subTest(identifier=identifier):
                self.case["known"] = [identifier]
                self.save_case()
                result, receipt, proof = self.execute()
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(receipt["status"], "failed")
                self.assertEqual(proof["status"], "not_checked")
                self.assertFalse((self.root / "build_called").exists())

    def test_evaluator_formation_failure_is_a_rejection(self):
        result, receipt, _ = self.execute("rejected")
        self.assertEqual(result.returncode, 2)
        self.assertEqual(receipt["status"], "rejected")
        self.assertFalse(receipt["result"]["input_formed"])

    def test_source_readiness_uses_the_full_changed_import_context(self):
        sys.path.insert(0, str(self.root / "tools"))
        try:
            spec = importlib.util.spec_from_file_location("investigation_fixture", self.root / "tools/investigate.py")
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
        finally:
            sys.path.pop(0)
        sources = self.root / "theories"
        (sources / "Base.thy").write_text("theory Base imports Main begin end\n")
        (sources / "Middle.thy").write_text("theory Middle imports Base begin end\n")
        accepted = self.root / "accepted.json"
        accepted.write_text(json.dumps({"status": "accepted", "exit_code": 0, "sources_unchanged": True,
            "tools_unchanged": True, "sources": {"theories/" + p.name: module.file_hash(p) for p in sources.glob("*.thy")}}))
        args = Namespace(project=self.root, overlay=[], roots=["Middle"], accepted_receipt=accepted)
        initial = module.source_case(args)
        self.assertEqual(len(initial["known"]), 2)
        self.assertEqual(initial["rules"], [])
        with (sources / "Base.thy").open("a") as stream:
            stream.write("\ntext \\<open>Changed parent context\\<close>\n")
        changed = module.source_case(args)
        self.assertEqual(changed["known"], [])
        self.assertEqual({r["source"]["theory"] for r in changed["rules"]}, {"Base", "Middle"})
        self.assertEqual(len(changed["evidence"]), 3)
        (sources / "Middle.thy").write_text("theory Middle imports Missing begin end\n")
        with self.assertRaisesRegex(ValueError, "Missing local theory"):
            module.source_case(args)

    def test_runtime_serialization_uses_right_associated_tuples(self):
        sys.path.insert(0, str(TOOLS))
        try:
            import investigate
        finally:
            sys.path.pop(0)
        self.assertEqual(investigate.ml_tuple([7, 8, 9]), "(n 7,(n 8,n 9))")
        with self.assertRaises(ValueError):
            investigate.ml_nat(True)
        encoded = investigate.ml_string('quote"\n\\path')
        self.assertNotIn("\n", encoded)
        self.assertEqual(encoded.count('"'), 2)

    def assert_child_stopped(self):
        child = int((self.root / "child_pid").read_text())
        path = Path(f"/proc/{child}/stat")
        limit = time.monotonic() + 2
        while path.exists() and path.read_text().split()[2] != "Z" and time.monotonic() < limit:
            time.sleep(0.01)
        self.assertTrue(not path.exists() or path.read_text().split()[2] == "Z")

    def test_runtime_timeout_records_failure_and_stops_children(self):
        result, receipt, _ = self.execute("timeout", "0.3")
        self.assertEqual(result.returncode, 124, result.stdout)
        self.assertEqual(receipt["status"], "timed_out")
        self.assert_child_stopped()

    def test_interruption_records_failure_and_stops_children(self):
        self.mode("interrupt")
        process = subprocess.Popen(self.command("20"), stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        try:
            limit = time.monotonic() + 5
            while not (self.root / "child_pid").exists() and time.monotonic() < limit:
                time.sleep(0.01)
            self.assertTrue((self.root / "child_pid").exists())
            process.send_signal(signal.SIGTERM)
            output, _ = process.communicate(timeout=5)
            self.assertEqual(process.returncode, 143, output)
            receipt = json.loads((self.root / "output/receipt.json").read_text())
            self.assertEqual(receipt["status"], "interrupted")
            self.assert_child_stopped()
        finally:
            if process.poll() is None:
                process.kill()
            process.communicate()


if __name__ == "__main__":
    unittest.main(verbosity=2)
