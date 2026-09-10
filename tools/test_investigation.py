#!/usr/bin/env python3
"""Exercise execution evidence and failure gates without substituting for Isabelle proofs."""
from __future__ import annotations

import importlib.util
import hashlib
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
    if mode == "archive_change":
        for p in (root / "output").glob("evidence-*/*"):
            p.write_text("changed archived evidence")
    if mode == "malformed_result":
        print("INVESTIGATION_RESULT {}"); sys.exit(0)
    if mode == "registered":
        print("INVESTIGATION_RESULT " + json.dumps({"input_formed": True, "residual": [],
            "profiles": [], "losses": [], "observations": [], "relation": [],
            "safe_facets": [], "conflicts": [], "repairs": [], "unrepairable": [], "extension": [],
            "revision": {"retained": [], "withdrawn": [], "repairs": [], "selection": [], "residual": []}})); sys.exit(0)
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
        (self.root / "theories/Finite_Investigation_Interface.thy").write_text(
            "theory Finite_Investigation_Interface imports Main begin end\n")
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

    def test_basis_relation_retains_foreign_endpoints(self):
        import investigate
        case = {"schema": investigate.SCHEMA, "kind": "basis", "question": "Complete relation",
                "scope": "Empty candidate scope with an independently supplied relation",
                "candidates": [], "facets": [0], "selected": [], "observations": [], "relation": [[2, 2]]}
        investigate.validate_case(case)
        self.assertEqual(case["relation"], [[2, 2]])
        case["candidates"] = [0]
        for relation in ([[2, 0]], [[0, 2]], [[2, 2]], [[2, 2], [2, 2]]):
            case["relation"] = relation
            investigate.validate_case(case)
            self.assertEqual(case["relation"], relation)
        for relation in ([[True, 2]], [[2, -1]], [[2, 2, 2]]):
            case["relation"] = relation
            with self.assertRaises(ValueError):
                investigate.validate_case(case)

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
        for mode in ("case_change", "engine_change", "archive_change", "malformed_result"):
            with self.subTest(mode=mode):
                result, receipt, _ = self.execute(mode)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(receipt["status"], "failed")

    def test_archives_preserve_original_external_evidence_and_tools(self):
        evidence = self.root / "draft.thy"
        original = b"exact historical draft\n"
        evidence.write_bytes(original)
        self.case["evidence"] = [{"path": str(evidence), "sha256": hashlib.sha256(original).hexdigest()}]
        self.save_case()
        result, receipt, _ = self.execute()
        self.assertEqual(result.returncode, 0, result.stdout)
        evidence.write_bytes(b"later draft\n")
        entries = receipt["evidence_archive"]
        self.assertEqual({item["role"] for item in entries}, {"original case", "case evidence", "execution tool"})
        for item in entries:
            self.assertEqual(hashlib.sha256(Path(item["archive"]).read_bytes()).hexdigest(), item["sha256"])
        archived = next(item for item in entries if item["role"] == "case evidence")
        self.assertEqual(Path(archived["archive"]).read_bytes(), original)

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

    def test_registered_case_keeps_its_export_and_scope(self):
        (self.root / "theories/Factor_Proof_Probe_Investigation.thy").write_text(
            "theory Factor_Proof_Probe_Investigation imports Main begin end\n")
        self.case = {"schema": "finite-investigation-1", "kind": "proof_probes", "selected": [0, 1],
                     "question": "Does the proposal cover every program?", "scope": "All programs",
                     "semantic_boundary": "Unrestricted universal coverage", "function": "Untrusted_Export",
                     "theory": "Untrusted_Theory"}
        self.save_case()
        result, receipt, proof = self.execute("registered")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(proof["status"], "accepted")
        self.assertEqual(receipt["registered_operation"], {"theory": "Factor_Proof_Probe_Investigation",
                                                         "function": "proof_probes_investigation"})
        self.assertEqual(receipt["scope"]["coverage"],
                         "These two fixed actual programs; the three probes form a complete basis for this family")
        self.assertNotEqual(receipt["semantic_boundary"], self.case["semantic_boundary"])
        self.assertEqual(json.loads((self.root / "output/case.json").read_text()), self.case)
        exported = Path(receipt["engine_snapshot"]) / "theories" / (receipt["export_theory"] + ".thy")
        source = exported.read_text()
        self.assertIn("investigation_revision", source)
        self.assertIn("proof_probes_investigation_observations", source)
        self.assertNotIn("Untrusted", source)

    def test_registered_socket_case_keeps_its_actual_subject_scope(self):
        (self.root / "theories/Factor_Schema_Socket_Investigation.thy").write_text(
            "theory Factor_Schema_Socket_Investigation imports Main begin end\n")
        self.case = {"schema": "finite-investigation-1", "kind": "schema_sockets", "selected": [2],
                     "question": "Does this compare arbitrary schemas?", "scope": "All schemas",
                     "semantic_boundary": "Unrestricted schema generation", "function": "Untrusted_Export",
                     "theory": "Untrusted_Theory"}
        self.save_case()
        result, receipt, proof = self.execute("registered")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(proof["status"], "accepted")
        self.assertEqual(receipt["registered_operation"], {"theory": "Factor_Schema_Socket_Investigation",
                                                         "function": "schema_sockets_investigation"})
        self.assertEqual(receipt["scope"]["coverage"],
                         "These two socket variants of the existing native incidence schema")
        program = (self.root / "output/execute.ML").read_text()
        self.assertIn("(map #1 profiles) [n 0,n 1,n 2] [n 2] observations relation", program)
        self.assertNotEqual(receipt["semantic_boundary"], self.case["semantic_boundary"])
        self.assertEqual(json.loads((self.root / "output/case.json").read_text()), self.case)

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

    def test_repair_guidance_requires_complete_witness_rows(self):
        sys.path.insert(0, str(TOOLS))
        try:
            import investigate
        finally:
            sys.path.pop(0)
        valid = {"input_formed": True, "residual": [], "profiles": [], "losses": [],
                 "safe_facets": [0], "conflicts": [], "repairs": [[0, 1, 0, 2]], "unrepairable": [], "extension": [0],
                 "revision": {"retained": [], "withdrawn": [], "repairs": [[0, 1, 0, 2]], "selection": [0], "residual": []}}
        investigate.validate_result(valid, "basis")
        for field, value in [("repairs", [[0, 1, 0]]), ("conflicts", [[0, 1, False, 2]]),
                             ("safe_facets", [True]), ("unrepairable", [[0]]), ("extension", [False])]:
            with self.subTest(field=field):
                with self.assertRaisesRegex(ValueError, "Malformed repair guidance"):
                    investigate.validate_result({**valid, field: value}, "basis")
        with self.assertRaisesRegex(ValueError, "Malformed repair guidance"):
            investigate.validate_result({k: v for k, v in valid.items() if k != "repairs"}, "basis")
        for key, value in [("repairs", [[0, 1, 0]]), ("withdrawn", [False]), ("selection", [-1]), ("residual", [[1]])]:
            with self.subTest(revision_field=key):
                with self.assertRaisesRegex(ValueError, "Malformed revision guidance"):
                    investigate.validate_result({**valid, "revision": {**valid["revision"], key: value}}, "basis")
        investigate.validate_result({**valid, "input_formed": False, "revision": None}, "basis")
        with self.assertRaisesRegex(ValueError, "Rejected inputs"):
            investigate.validate_result({**valid, "input_formed": False}, "basis")

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
