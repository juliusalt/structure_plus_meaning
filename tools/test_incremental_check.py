"""Refuse partial or stale validation when retaining the complete repository inventory."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import incremental_check as checker
import investigate


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


if __name__ == '__main__':
    unittest.main()
