"""The compact retention boundary still covers original controls and native words."""
import copy
from pathlib import Path
import re
import unittest

from reconstruct_overnight import assessment_boundary, request_functions


class ReconstructionBoundaryTests(unittest.TestCase):
    def test_changed_control_is_detected_even_when_words_match(self):
        original = {'wrong_reports': [None], 'words': {'original': {'bytes': 1, 'sha256': 'a'}}}
        changed = copy.deepcopy(original)
        changed['wrong_reports'] = [True]
        self.assertNotEqual(assessment_boundary(original), assessment_boundary(changed))

    def test_native_word_changes_are_detected(self):
        original = {'words': {'original': {'bytes': 1, 'sha256': 'a'}}}
        changed = {'words': {'original': {'bytes': 1, 'sha256': 'b'}}}
        self.assertNotEqual(assessment_boundary(original), assessment_boundary(changed))

    def test_physical_timing_and_dictionary_order_are_not_report_content(self):
        first = {'result': [1, None], 'words': {}, 'timings': [100], 'scope': 'run one'}
        second = {'words': {}, 'result': [1, None], 'timings': [200], 'scope': 'run two'}
        self.assertEqual(assessment_boundary(first), assessment_boundary(second))

    def test_all_requests_generate_without_historical_paths(self):
        for name in ('certificates', 'materials', 'sources'):
            with self.subTest(request=name):
                functions, _, _ = request_functions(name, Path('/fresh/output'))
                code = functions['program'](Path('/fresh/export.ML'), {})
                decoded = re.sub(r'\\([0-9]{3})', lambda m: chr(int(m[1])), code)
                self.assertIn('/fresh/export.ML', decoded)
                self.assertNotIn('/tmp/native-control', decoded)


if __name__ == '__main__':
    unittest.main()
