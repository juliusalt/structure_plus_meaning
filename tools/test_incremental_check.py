"""Refuse partial or stale validation when retaining the complete repository inventory."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import incremental_check as checker
import execution_support as investigate


class RetentionBoundaryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='incremental-retention-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.output = self.root / 'check'
        self.output.mkdir()
        (self.root / 'fixture.json').write_text('{"input": 1}\n')
        self.manifests = {'first': {'files': {'fixture.json': investigate.file_hash(self.root / 'fixture.json')}}}
        self.summary = {'status': 'accepted', 'recipes': {'first': {'status': 'accepted'}},
                        'host_tests': {'tools': {'exit_code': 0, 'ran': 3, 'skipped': 0}}}
        self.root_patch = patch.object(checker, 'ROOT', self.root)
        self.root_patch.start()
        self.addCleanup(self.root_patch.stop)

    def save(self):
        (self.output / 'incremental.json').write_text(json.dumps(self.summary))
        (self.output / 'manifests.json').write_text(json.dumps(self.manifests))

    def test_partial_check_cannot_overwrite_complete_inventory(self):
        self.save()
        with patch.object(checker, 'recipes', return_value=[{'name': 'first'}, {'name': 'second'}]):
            with self.assertRaisesRegex(AssertionError, 'partial recipe check'):
                checker.retain(self.output)
        self.assertFalse((self.root / 'validation').exists())

    def test_changed_fixture_prevents_retention_before_any_write(self):
        self.save()
        (self.root / 'fixture.json').write_text('{"input": 2}\n')
        with patch.object(checker, 'recipes', return_value=[{'name': 'first'}]):
            with self.assertRaisesRegex(AssertionError, 'inputs changed'):
                checker.retain(self.output)
        self.assertFalse((self.root / 'validation').exists())

    def test_invented_test_counts_are_rejected(self):
        self.save()
        with patch.object(checker, 'recipes', return_value=[{'name': 'first'}]):
            with self.assertRaisesRegex(AssertionError, 'test counts differ'):
                checker.retain(self.output, {'tools': {'ran': 100, 'skipped': 0}})
        self.assertFalse((self.root / 'validation').exists())

    def test_changed_session_configuration_prevents_retention(self):
        root = self.root / 'ROOT'
        root.write_text('session Original = HOL +\n')
        self.summary['validation_inputs'] = {'ROOT': investigate.file_hash(root)}
        self.save()
        root.write_text('session Changed = Pure +\n')
        with patch.object(checker, 'recipes', return_value=[{'name': 'first'}]):
            with self.assertRaisesRegex(AssertionError, 'inputs changed'):
                checker.retain(self.output)
        self.assertFalse((self.root / 'validation').exists())

    def test_conflicting_recipe_versions_are_rejected(self):
        manifests = self.manifests | {'second': {'files': {'fixture.json': 'another version'}}}
        with self.assertRaisesRegex(AssertionError, 'Conflicting input versions'):
            checker.verify_manifest_inputs(manifests)

    def test_missing_unchanged_recipe_input_is_rejected(self):
        (self.root / 'fixture.json').unlink()
        with self.assertRaisesRegex(AssertionError, 'Missing recipe input'):
            checker.verify_manifest_inputs(self.manifests)


class ExecutionBoundaryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='incremental-boundary-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.tools = self.root / 'tools'
        self.tools.mkdir()
        (self.root / 'validation/reconstruction').mkdir(parents=True)
        (self.root / 'theories').mkdir()
        (self.tools / 'shared_reader.py').write_text('VALUE = 1\n')
        (self.tools / 'check_family.py').write_text('import shared_reader\n')
        (self.tools / 'prove_stage.py').write_text('STAGE = 1\n')
        (self.tools / 'reconstruct_family.py').write_text(
            'from reconstruction import Execution, Recipe\n'
            "RECIPE = Recipe(name='family', roots=('Family_Execution',), export='Family_Execution:family.ML',\n"
            "    session='Family', groups=((Execution('presentation', 'check_family.py'),),), boundary='b')\n")
        (self.root / 'validation/reconstruction/family-reports.json').write_text('{"version": 1}\n')
        (self.root / 'theories/Family_Execution.thy').write_text('theory Family_Execution begin end\n')
        self.runtime = self.root / 'runtime-heap'
        self.runtime.write_bytes(b'heap')
        self.export = self.root / 'family.ML'
        self.export.write_text('structure Family = struct end\n')
        self.contract = self.root / 'family_investigation.yxml'
        self.contract.write_text('<contract/>\n')
        self.proof = self.root / 'family.proof.json'
        self.write_proof()
        files = {str(path.relative_to(self.root)): investigate.file_hash(path)
                 for path in [*self.tools.glob('*.py'), self.root / 'validation/reconstruction/family-reports.json',
                              self.root / 'theories/Family_Execution.thy']}
        self.manifest = {'files': files, 'toolchain': {'isabelle': 'Isabelle2025-2', 'poly_sha256': 'poly'}}
        self.row = {'script': 'reconstruct_family.py', 'name': 'family'}
        for name, value in (('ROOT', self.root), ('TOOLS', self.tools), ('NATIVE_RUNTIME', (self.runtime,))):
            patcher = patch.object(checker, name, value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def write_proof(self):
        self.proof.write_text(json.dumps({
            'exports': [{'path': str(self.export), 'sha256': investigate.file_hash(self.export)}],
            'subject_contracts': [{'path': str(self.contract), 'sha256': investigate.file_hash(self.contract)}],
            'export_theory': 'Family_Execution', 'code_target': 'Eval',
            'complete_artifact_transport': False, 'complete_term_transport': False}))

    def test_boundary_contains_execution_inputs_but_not_sources_or_proof_stage_tools(self):
        boundary = checker.execution_boundary(self.row, self.manifest, self.proof)
        self.assertEqual(set(boundary['tools']), {'tools/reconstruct_family.py', 'tools/check_family.py',
                                                  'tools/shared_reader.py'})
        self.assertEqual(set(boundary['declared_inputs']), {'validation/reconstruction/family-reports.json'})
        self.assertEqual(boundary['export']['subject_contracts'],
                         {'family_investigation.yxml': investigate.file_hash(self.contract)})
        self.assertEqual(boundary['runtime'], {str(self.runtime): investigate.file_hash(self.runtime)})
        self.assertNotIn('theories/Family_Execution.thy', json.dumps(boundary))

    def test_changed_theory_with_identical_export_reuses_accepted_execution(self):
        before = checker.execution_boundary(self.row, self.manifest, self.proof)
        (self.root / 'theories/Family_Execution.thy').write_text('theory Family_Execution begin lemma end\n')
        after = checker.execution_boundary(self.row, self.manifest, self.proof)
        verified = {'status': 'accepted', 'reports_equal': True, 'execution_boundary': before}
        self.assertTrue(checker.reusable_execution(verified, after))

    def test_changed_export_contract_tool_or_runtime_is_not_reusable(self):
        before = checker.execution_boundary(self.row, self.manifest, self.proof)
        verified = {'status': 'accepted', 'reports_equal': True, 'execution_boundary': before}
        self.export.write_text('structure Family = struct val changed = 1 end\n')
        self.write_proof()
        self.assertFalse(checker.reusable_execution(verified, checker.execution_boundary(self.row, self.manifest, self.proof)))
        self.export.write_text('structure Family = struct end\n')
        self.contract.write_text('<contract changed="1"/>\n')
        self.write_proof()
        self.assertFalse(checker.reusable_execution(verified, checker.execution_boundary(self.row, self.manifest, self.proof)))
        self.contract.write_text('<contract/>\n')
        self.write_proof()
        self.assertTrue(checker.reusable_execution(verified, checker.execution_boundary(self.row, self.manifest, self.proof)))
        self.runtime.write_bytes(b'other heap')
        self.assertFalse(checker.reusable_execution(verified, checker.execution_boundary(self.row, self.manifest, self.proof)))
        (self.tools / 'shared_reader.py').write_text('VALUE = 2\n')
        with self.assertRaisesRegex(AssertionError, 'differ from the manifest'):
            checker.execution_boundary(self.row, self.manifest, self.proof)

    def test_failed_or_unequal_retained_execution_is_not_reusable(self):
        boundary = checker.execution_boundary(self.row, self.manifest, self.proof)
        self.assertFalse(checker.reusable_execution({'status': 'failed', 'reports_equal': True,
                                                     'execution_boundary': boundary}, boundary))
        self.assertFalse(checker.reusable_execution({'status': 'accepted', 'reports_equal': False,
                                                     'execution_boundary': boundary}, boundary))
        self.assertFalse(checker.reusable_execution({'status': 'accepted', 'reports_equal': True}, boundary))

    def test_reused_execution_is_retained_with_its_current_manifest(self):
        boundary = checker.execution_boundary(self.row, self.manifest, self.proof)
        target = self.root / 'validation/reconstruction'
        reports = {'presentation': {'records': 1, 'tags': {'PRESENTED_REPORT_WORD': 1}, 'sha256': 'word'}}
        (target / 'family-sources.json').write_text(json.dumps({'files': {}}))
        (target / 'family-verified.json').write_text(json.dumps({
            'status': 'accepted', 'reports_equal': True, 'report_boundaries': reports, 'steps': [],
            'execution_boundary': boundary}))
        context = self.root / 'context'
        context.mkdir()
        (context / 'accepted-context.json').write_text('{}')
        output = self.root / 'check'
        output.mkdir()
        (output / 'boundaries.json').write_text(json.dumps({'family': boundary}))
        (output / 'manifests.json').write_text(json.dumps({'family': self.manifest}))
        (output / 'incremental.json').write_text(json.dumps({
            'status': 'accepted', 'base': str(context), 'base_receipt_sha256': 'base', 'base_theories': 1,
            'accepted_proof_context': str(context), 'theories': 1, 'reused_theories': 1, 'rebuilt_theories': [],
            'phases': {}, 'seconds': 1.0, 'source_checks': {},
            'recipes': {'family': {'status': 'reused', 'exit_code': 0, 'seconds': 0.0}},
            'host_tests': {'tools': {'exit_code': 0, 'ran': 1, 'skipped': 0}}}))
        with patch.object(checker, 'recipes', return_value=[{'name': 'family'}]), \
                patch.object(checker.proof_contexts, 'CONTEXT_FILE', 'accepted-context.json'):
            checker.retain(output)
        verified = json.loads((target / 'family-verified.json').read_text())
        self.assertEqual(verified['report_boundaries'], reports)
        self.assertEqual(verified['execution_reuse']['export_module_sha256'], boundary['export']['module_sha256'])
        self.assertEqual(json.loads((target / 'family-sources.json').read_text()), self.manifest)
        inventory = json.loads((target / 'current-verified.json').read_text())
        self.assertEqual((inventory['reused_recipes'], inventory['executed_recipes']), (1, 0))


if __name__ == '__main__':
    unittest.main()
