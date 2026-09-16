"""Footer transport reconstructs complete ordered records through native references."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import machine_reports
import native_artifact_stream as codec
import native_program_json
import native_stream_json
import program_evaluation_json
import shared_object_stream


class NativeFooterStreamTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='native-footer-test-')
        self.addCleanup(temporary.cleanup)
        self.path = Path(temporary.name) / 'results.log'
        self.artifact = {'carrier': [[1], [1]], 'incidence': [[[1], [2], [3]]],
                         'counted_data': [[[1], [256]], [[1], [256]]], 'functional_data': []}
        self.term = {'pair': [{'payload': [256]},
                             {'target': {'anchored_artifact': [self.artifact, [3]]}}]}
        self.raw_term = {'pair': [{'payload': [256]},
                                 {'target': {'anchored_artifact': [{codec.REFERENCE: 0}, [3]]}}]}
        self.values = [[self.term, self.term, self.artifact], [], None]

    def line(self, tag, value, indices=''):
        return tag + ' ' + indices + json.dumps(value) + '\n'

    def stream(self):
        return [self.line(codec.BEGIN, {'version': 3}),
                self.line('RESULT', [{codec.TERM_REFERENCE: 0}, {codec.TERM_REFERENCE: 0},
                                     {codec.REFERENCE: 0}], '4 '),
                self.line('RESULT', [], '4 '), self.line('RESULT', None, '2 '),
                self.line(codec.TERM_TABLE, [self.raw_term]),
                self.line(codec.ARTIFACT_TABLE, [self.artifact]),
                self.line(codec.END, {'entries': 1, 'terms': 1})]

    def test_footer_preserves_original_bytes_order_and_mutable_occurrences(self):
        self.path.write_text(''.join(self.line('RESULT', value, str(index) + ' ')
                                    for value, index in zip(self.values, [4, 4, 2])))
        original = list(machine_reports.reports(self.path))
        expected = machine_reports.boundary(self.path)
        self.path.write_text(''.join(self.stream()))
        self.assertEqual(list(machine_reports.reports(self.path)), original)
        self.assertEqual(machine_reports.boundary(self.path), expected)
        records = list(machine_reports.reports(self.path, deferred=True))
        digest = hashlib.sha256()
        for row, old in zip(records, original):
            self.assertIsNone(row.materialized)
            self.assertTrue(machine_reports.record_equal(row, old))
            machine_reports.canonical_update(digest, row)
            self.assertIsNone(row.materialized)
        self.assertEqual(digest.hexdigest(), expected['sha256'])
        self.assertEqual(machine_reports.field(records[0], 0), self.term)
        records[0]['value'][0]['pair'][1]['target']['anchored_artifact'][0]['carrier'].clear()
        self.assertEqual(records[0]['value'][1], self.term)
        self.assertEqual(records[0]['value'][2], self.artifact)

    def test_complete_empty_tables_and_records_are_preserved(self):
        self.path.write_text(self.line(codec.BEGIN, {'version': 3}) + self.line('RESULT', []) +
            self.line(codec.TERM_TABLE, []) + self.line(codec.ARTIFACT_TABLE, []) +
            self.line(codec.END, {'entries': 0, 'terms': 0}))
        self.assertEqual(list(machine_reports.reports(self.path)),
                         [{'tag': 'RESULT', 'indices': [], 'value': []}])

    def test_missing_repeated_indexed_mixed_and_unfinished_tables_refuse(self):
        rows = self.stream()
        variants = [rows[:-1], rows[:4] + rows[5:], rows[:5] + rows[6:],
                    rows[:5] + [rows[4]] + rows[5:],
                    rows[:4] + [self.line(codec.TERM_TABLE, [self.raw_term], '0 ')] + rows[5:],
                    rows[:5] + [rows[1]] + rows[5:], rows + [rows[1]],
                    [rows[0], rows[0], *rows[1:]],
                    [rows[0], self.line(codec.ENTRY, self.artifact, '0 '), *rows[1:]],
                    [rows[0], self.line(codec.TERM_ENTRY, self.raw_term, '0 '), *rows[1:]],
                    rows[:5] + [self.line(codec.ARTIFACT_TABLE, {})] + rows[6:]]
        for stream in variants:
            for deferred in [False, True]:
                with self.subTest(stream=stream, deferred=deferred):
                    self.path.write_text(''.join(stream))
                    with self.assertRaises(ValueError):
                        list(machine_reports.reports(self.path, deferred=deferred))

    def test_footer_metadata_outside_its_protocol_refuses(self):
        for tag in [codec.TERM_TABLE, codec.ARTIFACT_TABLE]:
            for prefix in ['', self.line(codec.BEGIN, {'version': 1})]:
                self.path.write_text(prefix + self.line(tag, []))
                with self.assertRaises(ValueError):
                    list(machine_reports.reports(self.path))

    def test_footer_counts_and_coverage_are_checked_before_records_are_yielded(self):
        for end in [{'entries': 0, 'terms': 1}, {'entries': 1, 'terms': 0},
                    {'entries': True, 'terms': 1}, {'entries': 1, 'terms': 1.0},
                    {'entries': 1, 'terms': 1, 'extra': 0}]:
            rows = self.stream()
            rows[-1] = self.line(codec.END, end)
            self.path.write_text(''.join(rows))
            with self.assertRaises(ValueError):
                next(machine_reports.reports(self.path))
        rows = self.stream()
        rows[1] = self.line('RESULT', {codec.REFERENCE: 0})
        self.path.write_text(''.join(rows))
        with self.assertRaises(ValueError):
            next(machine_reports.reports(self.path))

    def test_bad_complete_values_and_cyclic_or_out_of_range_references_refuse(self):
        for term in [{codec.TERM_REFERENCE: 0}, {codec.TERM_REFERENCE: 1},
                     {'pair': []}, {'payload': [True]},
                     {'target': {'whole_artifact': {codec.REFERENCE: 1}}}]:
            rows = self.stream()
            rows[4] = self.line(codec.TERM_TABLE, [term])
            self.path.write_text(''.join(rows))
            with self.assertRaises(ValueError):
                list(machine_reports.reports(self.path))
        for reference in [{codec.TERM_REFERENCE: True}, {codec.REFERENCE: -1},
                          {codec.TERM_REFERENCE: 0, 'extra': 1}]:
            rows = self.stream()
            rows[1] = self.line('RESULT', reference)
            self.path.write_text(''.join(rows))
            with self.assertRaises(ValueError):
                list(machine_reports.reports(self.path))
        broken = copy.deepcopy(self.artifact)
        broken['functional_data'] = [[[1]]]
        rows = self.stream()
        rows[5] = self.line(codec.ARTIFACT_TABLE, [broken])
        self.path.write_text(''.join(rows))
        with self.assertRaises(ValueError):
            list(machine_reports.reports(self.path))

    def test_streaming_renderer_defers_tables_and_preserves_existing_object_stream(self):
        code = (native_program_json.ARTIFACT_ROWS + program_evaluation_json.PRELUDE +
                native_stream_json.PRELUDE)
        result = codec.program(code, parallel=True, terms=True)
        self.assertIn('NATIVE_ARTIFACT_STREAM {\\"version\\":3}', result)
        self.assertIn('N.complete_artifact_reference rows', result)
        self.assertIn('N.complete_term_reference term', result)
        self.assertIn('fun wartifact rows = print (jartifact rows);', result)
        self.assertNotIn('NATIVE_ARTIFACT_VALUE', result)
        self.assertNotIn('NATIVE_TERM_VALUE', result)
        self.assertLess(result.index('NATIVE_TERM_TABLE'), result.index('NATIVE_ARTIFACT_TABLE'))
        self.assertLess(result.index('NATIVE_ARTIFACT_TABLE'), result.index('NATIVE_ARTIFACT_END'))
        self.assertNotIn('= ref ', result)
        existing = shared_object_stream.program_with_references(code, 'TEST')
        self.assertEqual(codec.program(existing, parallel=True, terms=True), existing)


if __name__ == '__main__':
    unittest.main()
