"""A reconstruction cannot accept stale stages, altered reports or changed recipe inputs."""
import json
from pathlib import Path
import tempfile
import unittest

from evidence_io import digest
from machine_reports import boundary
from reconstruction import Execution, Recipe, finish_reconstruction


class ReconstructionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="reconstruction-test-")
        self.addCleanup(temporary.cleanup)
        self.output = Path(temporary.name)
        self.source = self.output / "recipe.py"
        self.source.write_text("fixed recipe input\n")
        self.tracked = {str(self.source): digest(self.source)}
        self.recipe = Recipe("fixture", ("Fixture",), "Fixture:fixture.ML", "Fixture_Rebuild",
                             ((Execution("native", "fixture.py"),),), "Report comparison fixture.")
        (self.output / "native").mkdir()
        self.report = self.output / "native/results.log"
        self.report.write_text('NATIVE 0 {"input":[1,2],"output":true}\n')
        self.expected = {"version": 1, "reports": {"native": boundary(self.report)}}

    def finish(self, names=("proof", "diagnostics", "export", "native"), supplied=False, failed=None):
        steps = [{"name": name, "exit_code": int(name == failed)} for name in names]
        result = finish_reconstruction(self.output, self.output, self.recipe, steps,
                                       self.expected, self.tracked, supplied)
        self.assertEqual(json.loads((self.output / "reconstruction.json").read_text()), result)
        return result

    def test_missing_duplicate_or_failed_stage_cannot_reuse_matching_output(self):
        for names in [("proof", "export", "native"),
                      ("proof", "diagnostics", "export", "native", "native")]:
            with self.subTest(names=names):
                self.assertEqual(self.finish(names)["status"], "failed")
        self.assertEqual(self.finish(failed="native")["status"], "failed")

    def test_changed_result_field_and_missing_report_are_rejected(self):
        self.report.write_text('NATIVE 0 {"input":[1,2],"output":false}\n')
        self.assertEqual(self.finish()["status"], "failed")
        self.report.unlink()
        result = self.finish()
        self.assertEqual(result["status"], "failed")
        self.assertIn("error", result)

    def test_changed_recipe_bytes_cannot_accept_matching_reports(self):
        self.source.write_text("changed recipe input\n")
        result = self.finish()
        self.assertTrue(result["reports_equal"])
        self.assertFalse(result["recipe_inputs_unchanged"])
        self.assertEqual(result["status"], "failed")

    def test_supplied_export_does_not_claim_source_reconstruction(self):
        result = self.finish(("native",), supplied=True)
        self.assertEqual(result["status"], "accepted")
        self.assertFalse(result["sources_rebuilt"])
        rebuilt = self.finish()
        self.assertEqual(rebuilt["status"], "accepted")
        self.assertTrue(rebuilt["sources_rebuilt"])


if __name__ == "__main__":
    unittest.main()
