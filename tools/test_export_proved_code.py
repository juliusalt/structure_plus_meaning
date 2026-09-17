"""Check the export CLI's source-project boundary independently of Isabelle."""
from contextlib import redirect_stdout
from io import StringIO
import json
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

import export_proved_code
import execution_support as investigate
import proof_contexts


class ExportSourceProjectTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="export-source-project-")
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        self.project = self.base / "restored"
        self.snapshot = self.base / "proof"
        text = ("theory Fixture imports Main begin\nlemma identity: True by simp\n"
                "export_code True in SML module_name Fixture file_prefix fixture\nend\n")
        for directory in [self.project, self.snapshot]:
            (directory / "theories").mkdir(parents=True)
            (directory / "theories/Fixture.thy").write_text(text)
        (self.snapshot / "ROOT").write_text(
            "session Restored_Fixture = HOL +\n  directories theories\n  theories Fixture\n")
        sha = investigate.file_hash(self.project / "theories/Fixture.thy")
        self.proof = self.snapshot / "result.json"
        self.proof.write_text(json.dumps({
            "status": "accepted", "exit_code": 0, "sources_unchanged": True,
            "sources": {"Fixture": sha}, "effective_source_hashes": {"Fixture": sha}}))
        self.output = self.base / "export"
        self.argv = ["export_proved_code.py", "--proof", str(self.proof),
                     "--project", str(self.project), "--output", str(self.output),
                     "--module", "Fixture:fixture.ML"]

    @staticmethod
    def exported_module(command, **kwargs):
        output = Path(command[command.index("-O") + 1])
        target = output / "Restored_Fixture.Fixture/code/fixture.ML"
        target.parent.mkdir(parents=True)
        target.write_text("structure Fixture = struct end;\n")
        return SimpleNamespace(returncode=0)

    def test_matching_restored_source_is_used_and_recorded(self):
        with patch("sys.argv", self.argv), redirect_stdout(StringIO()), \
                patch.object(export_proved_code.subprocess, "run", side_effect=self.exported_module) as execute:
            self.assertEqual(export_proved_code.main(), 0)
        execute.assert_called_once()
        receipt = json.loads((self.output / "receipt.json").read_text())
        self.assertEqual(receipt["source_project"], str(self.project))
        self.assertEqual(receipt["status"], "accepted")
        self.assertIn(str(self.project / "theories/Fixture.thy"), receipt["execution_inputs"])
        self.assertEqual(len(receipt["exports"]), 1)
        module = json.loads((self.output / 'fixture.proof.json').read_text())
        self.assertEqual(module['code_target'], 'SML')
        self.assertFalse(module['complete_artifact_transport'])

    def test_changed_restored_source_is_rejected_before_export(self):
        source = self.project / "theories/Fixture.thy"
        source.write_text(source.read_text() + "\n")
        with patch("sys.argv", self.argv), patch.object(export_proved_code.subprocess, "run") as execute:
            with self.assertRaises(AssertionError):
                export_proved_code.main()
        execute.assert_not_called()
        self.assertFalse(self.output.exists())

    def test_equal_filename_in_another_theory_is_not_the_requested_export(self):
        def both_modules(command, **kwargs):
            result = self.exported_module(command, **kwargs)
            output = Path(command[command.index('-O') + 1])
            extra = output / 'Restored_Fixture.Shared_Fixture/code/fixture.ML'
            extra.parent.mkdir(parents=True)
            extra.write_text('structure Wrong = struct end;\n')
            return result
        with patch('sys.argv', self.argv), redirect_stdout(StringIO()), \
                patch.object(export_proved_code.subprocess, 'run', side_effect=both_modules):
            self.assertEqual(export_proved_code.main(), 0)
        receipt = json.loads((self.output / 'fixture.proof.json').read_text())
        self.assertIn('/Restored_Fixture.Fixture/', receipt['exports'][0]['path'])


class ExportDependencyBoundaryTests(unittest.TestCase):
    def setUp(self):
        ExportSourceProjectTests.setUp(self)
        (self.project / 'ROOT').write_text(
            'session Project = HOL +\n  theories\n    Fixture\n    Independent\n')
        self.independent = self.project / 'theories/Independent.thy'
        self.independent.write_text('theory Independent imports Main begin end\n')
        receipt = self.base / 'accepted-context.json'
        receipt.write_text('{}\n')
        self.context = {
            'project_declaration': proof_contexts.session_declaration(self.project),
            'sources': {name: investigate.file_hash(self.project / 'theories' / (name + '.thy'))
                        for name in ('Fixture', 'Independent')},
            'inputs': {str(receipt): investigate.file_hash(receipt)},
            'receipt': str(receipt), 'directories': [str(self.snapshot)],
            'providers': {name: {'session': 'Restored_Fixture', 'directory': str(self.snapshot),
                                 'theory': 'Restored_Fixture.' + name}
                          for name in ('Fixture', 'Independent')},
        }

    def export(self, roots=None, mutate=False):
        def execute(command, **kwargs):
            result = ExportSourceProjectTests.exported_module(command, **kwargs)
            if mutate:
                self.independent.write_text('an unrelated edit in progress\n')
            return result
        with patch.object(proof_contexts, 'load_parent', return_value=self.context), \
                patch.object(export_proved_code.subprocess, 'run', side_effect=execute), \
                redirect_stdout(StringIO()):
            return export_proved_code.export_context(self.snapshot, self.project, self.output,
                [('Fixture', 'fixture.ML')], roots)

    def test_export_tracks_only_its_complete_required_context(self):
        self.assertEqual(self.export(mutate=True), 0)
        proof = json.loads((self.output / 'fixture.proof.json').read_text())
        self.assertEqual(set(proof['sources']), {'Fixture'})
        receipt = json.loads((self.output / 'receipt.json').read_text())
        self.assertNotIn(str(self.independent), receipt['execution_inputs'])

    def test_additional_client_proof_roots_are_retained(self):
        self.assertEqual(self.export({'Fixture': ['Independent']}), 0)
        proof = json.loads((self.output / 'fixture.proof.json').read_text())
        self.assertEqual(set(proof['sources']), {'Fixture', 'Independent'})
        self.assertEqual(proof['roots'], ['Fixture', 'Independent'])

    def test_additional_client_context_must_remain_unchanged(self):
        self.assertEqual(self.export({'Fixture': ['Independent']}, mutate=True), 1)
        receipt = json.loads((self.output / 'receipt.json').read_text())
        self.assertIn('Export inputs changed', receipt['error'])


if __name__ == "__main__":
    unittest.main()
