#!/usr/bin/env python3
"""Exercise validation failure paths in isolated repositories with a fake Isabelle."""
from __future__ import annotations

import json
import os
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
import json
from pathlib import Path
import subprocess
import sys
import time

root = Path(__file__).resolve().parent
mode = (root / "mode").read_text()
if sys.argv[1] == "version":
    if mode == "spawn_failure":
        Path(__file__).unlink()
    print("current version failure" if mode == "version_failure" else "Isabelle fixture")
    sys.exit(9 if mode == "version_failure" else 0)
if sys.argv[1] == "build_log":
    (root / "diagnostic_called").write_text("called")
    print("current complete session errors" if mode == "failure" else "STALE DIAGNOSTIC")
    sys.exit(0)
print("Running Fixture ...", flush=True)
if mode == "failure":
    print("*** current build failure", flush=True)
    sys.exit(7)
if mode == "source_change":
    with (root / "theories/Fixture.thy").open("a") as stream:
        stream.write("\nchanged during build\n")
if mode == "tool_change":
    with (root / "tools/check.py").open("a") as stream:
        stream.write("\n# changed during build\n")
if mode == "slow":
    child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(600)"])
    (root / "child_pid").write_text(str(child.pid))
    time.sleep(600)
print("Finished Fixture", flush=True)
'''


class ValidationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="structural-validation-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "tools").mkdir()
        (self.root / "theories").mkdir()
        (self.root / "validation").mkdir()
        for name in ("build.py", "check.py"):
            shutil.copyfile(TOOLS / name, self.root / "tools" / name)
        (self.root / "ROOT").write_text("session Fixture = HOL +\n  theories\n    Fixture\n")
        (self.root / "theories/Fixture.thy").write_text("theory Fixture imports Main begin end\n")
        self.fake = self.root / "fake_isabelle"
        self.fake.write_text(FAKE)
        self.fake.chmod(0o755)
        self.set_mode("success")
        self.seed_accepted()

    def set_mode(self, mode):
        (self.root / "mode").write_text(mode)

    def seed_accepted(self):
        old = {"status": "accepted", "exit_code": 0, "invocation": "OLD"}
        for name in ("build.json", "check.json"):
            (self.root / "validation" / name).write_text(json.dumps(old))
        (self.root / "validation/build.log").write_text("OLD LOG\n")
        (self.root / "validation/check-errors.log").write_text("OLD ERRORS\n")

    def command(self, script="check.py", executable=None):
        return [sys.executable, str(self.root / "tools" / script), "--isabelle", str(executable or self.fake),
                "--cache-home", str(self.root / "cache"), "--threads", "1", "--timeout", "1"]

    def run_wrapper(self, script="check.py", executable=None):
        result = subprocess.run(self.command(script, executable), text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=15)
        report = json.loads((self.root / "validation/check.json").read_text())
        receipt = json.loads((self.root / "validation/build.json").read_text())
        self.assertNotEqual(report["invocation"], "OLD", result.stdout)
        self.assertEqual(report["invocation"], receipt["invocation"], result.stdout)
        return result, report, receipt

    def assert_failed(self, mode, executable=None):
        self.set_mode(mode)
        result, report, receipt = self.run_wrapper(executable=executable)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertEqual(report["status"], "failed", result.stdout)
        self.assertNotEqual(receipt["status"], "running", result.stdout)
        self.assertNotIn("OLD LOG", (self.root / "validation/build.log").read_text())
        self.assertNotIn("OLD ERRORS", (self.root / "validation/check-errors.log").read_text())
        return result, report, receipt

    def test_success_carries_this_invocations_complete_evidence(self):
        result, report, receipt = self.run_wrapper()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(report["status"], "accepted")
        self.assertEqual(report["build_evidence"], receipt)
        self.assertTrue(report["sources_and_tools_unchanged"])
        self.assertEqual(set(receipt["sources"]), {"ROOT", "theories/Fixture.thy"})
        self.assertEqual(set(receipt["tools"]), {"tools/build.py", "tools/check.py"})

    def test_missing_executable_replaces_old_acceptance(self):
        self.assert_failed("success", self.root / "missing_isabelle")
        self.assertFalse((self.root / "diagnostic_called").exists())

    def test_version_failure_does_not_query_old_session_diagnostics(self):
        _, _, receipt = self.assert_failed("version_failure")
        self.assertEqual(receipt["exit_code"], 9)
        self.assertFalse((self.root / "diagnostic_called").exists())

    def test_build_spawn_failure_cannot_reuse_an_old_log(self):
        self.assert_failed("spawn_failure")
        self.assertFalse((self.root / "diagnostic_called").exists())

    def test_actual_session_failure_collects_its_errors(self):
        _, report, receipt = self.assert_failed("failure")
        self.assertEqual(receipt["exit_code"], 7)
        self.assertIn("current complete session errors", receipt["session_diagnostics"])
        self.assertEqual(report["build_evidence"], receipt)

    def test_source_and_tool_changes_prevent_acceptance(self):
        for mode in ("source_change", "tool_change"):
            with self.subTest(mode=mode):
                self.seed_accepted()
                _, report, receipt = self.assert_failed(mode)
                self.assertIn("changed during the build", receipt["error"])
                self.assertFalse(report["sources_and_tools_unchanged"])

    def test_malformed_text_cannot_leave_a_stale_accepted_check(self):
        (self.root / "theories/Fixture.thy").write_bytes(b"\xff")
        result, report, receipt = self.run_wrapper()
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertEqual(receipt["status"], "accepted")
        self.assertEqual(report["status"], "failed")
        self.assertIn("codec", report["error"])

    def test_unfinished_proofs_and_incomplete_inventory_prevent_acceptance(self):
        (self.root / "theories/Extra.thy").write_text("lemma unfinished: True\n  sorry\n")
        result, report, receipt = self.run_wrapper()
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertEqual(receipt["status"], "accepted")
        self.assertEqual(report["status"], "failed")
        self.assertEqual(report["unlisted_theories"], ["Extra"])
        self.assertEqual(len(report["proof_escape_matches"]), 1)

    def test_standalone_build_invalidates_previous_combined_acceptance(self):
        result, report, receipt = self.run_wrapper("build.py")
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(receipt["status"], "accepted")
        self.assertEqual(report["status"], "not_checked")

    def test_interruption_records_current_status_and_stops_children(self):
        self.assert_interruption(signal.SIGINT)

    def test_termination_records_current_status_and_stops_children(self):
        self.assert_interruption(signal.SIGTERM)

    def assert_interruption(self, signum):
        self.set_mode("slow")
        process = subprocess.Popen(self.command(), text=True, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            deadline = time.monotonic() + 5
            while not (self.root / "child_pid").exists() and time.monotonic() < deadline:
                # Concurrent readers must always see complete JSON, including during startup.
                for name in ("build.json", "check.json"):
                    json.loads((self.root / "validation" / name).read_text())
                time.sleep(0.01)
            self.assertTrue((self.root / "child_pid").exists())
            running = json.loads((self.root / "validation/check.json").read_text())
            self.assertEqual(running["status"], "running")
            process.send_signal(signum)
            output, _ = process.communicate(timeout=8)
            self.assertEqual(process.returncode, 128 + signum, output)
            for name in ("build.json", "check.json"):
                report = json.loads((self.root / "validation" / name).read_text())
                self.assertEqual(report["status"], "interrupted", output)
                self.assertEqual(report["invocation"], running["invocation"])
            child = int((self.root / "child_pid").read_text())
            proc_stat = Path(f"/proc/{child}/stat")
            deadline = time.monotonic() + 2
            while proc_stat.exists() and time.monotonic() < deadline:
                if proc_stat.read_text().split()[2] == "Z":
                    break
                time.sleep(0.01)
            self.assertTrue(not proc_stat.exists() or proc_stat.read_text().split()[2] == "Z")
        finally:
            if process.poll() is None:
                process.kill()
            process.communicate()


if __name__ == "__main__":
    unittest.main(verbosity=2)
