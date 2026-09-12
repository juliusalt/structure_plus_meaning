"""Retained semantic outputs must survive replay without helper substitution."""
import importlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

import replay_reasoning_review as replay


class TimedRetainedReports(unittest.TestCase):
    def application_report(self, seconds, plan):
        return 'APPLICATION_CONSTRUCTION 0 ' + json.dumps({
            'seconds': seconds, 'report': {'formed': True, 'uncovered': [], 'plan': plan}})

    def test_clock_variation_preserves_the_complete_semantic_report(self):
        a = self.application_report('1.0', [['head']])
        b = self.application_report('2.0', [['head']])
        c = self.application_report('2.0', None)
        normalize = lambda raw: replay.timed_data_reports(raw, 'application_candidates')
        self.assertEqual(normalize(a), normalize(b))
        self.assertNotEqual(normalize(a), normalize(c))

    def test_other_seconds_fields_are_preserved(self):
        a = 'APPLICATION_INPUT 0 {"seconds": 1}'
        b = 'APPLICATION_INPUT 0 {"seconds": 2}'
        self.assertNotEqual(replay.timed_data_reports(a, 'application_candidates'),
                            replay.timed_data_reports(b, 'application_candidates'))

    def test_generic_clock_variation_does_not_hide_changed_bindings(self):
        normalize = lambda raw: replay.timed_data_reports(raw, 'directed_search')
        self.assertEqual(normalize('BINDINGS 0 [[[1,2]]] 1.0'), normalize('BINDINGS 0 [[[1,2]]] 2.0'))
        self.assertNotEqual(normalize('BINDINGS 0 [[[1,2]]] 1.0'), normalize('BINDINGS 0 [[[1,3]]] 1.0'))

    def test_assessment_keeps_nested_semantic_fields(self):
        a = {'cases': [{'seconds': 1.0, 'report': {'seconds': 3}}], 'boundary': 'exact'}
        b = {'cases': [{'seconds': 2.0, 'report': {'seconds': 4}}], 'boundary': 'exact'}
        self.assertNotEqual(replay.timed_data_assessment(a), replay.timed_data_assessment(b))
        self.assertEqual(a['cases'][0]['seconds'], 1.0)

    def test_witness_order_preserves_every_witness_content(self):
        witnesses = [{"part": ["head"], "missing_requirements": [1]},
                     {"part": ["premise", 2, 3], "missing_requirements": [4]}]
        a = {"cases": [{"seconds": 1, "necessity_witnesses": witnesses}]}
        b = {"cases": [{"seconds": 2, "necessity_witnesses": list(reversed(witnesses))}]}
        self.assertEqual(replay.timed_data_assessment(a), replay.timed_data_assessment(b))
        b["cases"][0]["necessity_witnesses"] = witnesses + [witnesses[0]]
        self.assertNotEqual(replay.timed_data_assessment(a), replay.timed_data_assessment(b))
        b["cases"][0]["necessity_witnesses"] = [dict(witnesses[0], missing_requirements=[9]), witnesses[1]]
        self.assertNotEqual(replay.timed_data_assessment(a), replay.timed_data_assessment(b))

    def test_retained_helper_overrides_a_loaded_and_preferred_local_copy(self):
        name = 'retained_replay_helper_probe'
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            retained, local = base / 'retained', base / 'local'
            retained.mkdir(); local.mkdir()
            (retained / (name + '.py')).write_text("identity = 'retained'\n")
            (local / (name + '.py')).write_text("identity = 'local'\n")
            sys.path.insert(0, str(local))
            finder = None
            try:
                self.assertEqual(importlib.import_module(name).identity, 'local')
                finder = replay.pin_restored_modules(retained)
                self.assertEqual(importlib.import_module(name).identity, 'retained')
            finally:
                sys.modules.pop(name, None)
                sys.path.remove(str(local))
                if finder is not None:sys.meta_path.remove(finder)


if __name__ == '__main__':
    unittest.main()
