"""Complete reference transport preserves records and rejects incomplete streams."""
import json
from pathlib import Path
import tempfile
import unittest
import hashlib
import native_program_json
import program_evaluation_json

import machine_reports
import native_artifact_stream as codec


class NativeArtifactStreamTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='native-artifact-stream-test-')
        self.addCleanup(temporary.cleanup)
        self.path = Path(temporary.name) / 'results.log'
        self.artifact = {'carrier': [[1], [1]], 'incidence': [[[1], [2], [3]]],
                         'counted_data': [[[1], [256]], [[1], [256]]], 'functional_data': []}
        self.original = {'a': self.artifact, 'again': [self.artifact, None], 'empty': []}

    def line(self, tag, value, indices=''):
        return tag + ' ' + indices + json.dumps(value) + '\n'

    def stream(self):
        ref = {codec.REFERENCE: 0}
        row = {'a': ref, 'again': [ref, None], 'empty': []}
        return [self.line(codec.BEGIN, {'version': 1}), self.line(codec.ENTRY, self.artifact, '0 '),
                self.line('RESULT', row, '4 '), self.line('RESULT', row, '4 '),
                self.line(codec.END, {'entries': 1})]

    def test_complete_records_and_boundaries_equal_original_occurrences(self):
        self.path.write_text(self.line('RESULT', self.original, '4 ') * 2)
        expected = list(machine_reports.reports(self.path))
        boundary = machine_reports.boundary(self.path)
        self.path.write_text(''.join(self.stream()))
        self.assertEqual(list(machine_reports.reports(self.path)), expected)
        self.assertEqual(machine_reports.boundary(self.path), boundary)

    def test_truncation_rebinding_missing_dictionary_and_extra_fields_refuse(self):
        original = self.stream()
        variants = [original[:-1], [original[0], *original[2:]],
                    original[:2] + [original[1]] + original[2:],
                    [original[0], original[1].replace('VALUE 0 ', 'VALUE 1 '), *original[2:]],
                    original[:-1] + [self.line(codec.END, {'entries': 2})],
                    [original[0], original[1].replace('"carrier"', '"other"'), *original[2:]],
                    original + [original[2]], [original[0], original[0], *original[1:]]]
        for stream in variants:
            with self.subTest(stream=stream):
                self.path.write_text(''.join(stream))
                with self.assertRaises(ValueError):
                    list(machine_reports.reports(self.path))

    def test_reference_range_boolean_index_and_ambiguous_reference_refuse(self):
        for ref in [{codec.REFERENCE: 1}, {codec.REFERENCE: True},
                    {codec.REFERENCE: 0, 'extra': self.artifact}]:
            lines = self.stream()
            lines[2] = self.line('RESULT', ref)
            self.path.write_text(''.join(lines))
            with self.assertRaises(ValueError):
                list(machine_reports.reports(self.path))

    def test_unreferenced_dictionary_value_refuses(self):
        lines = self.stream()
        self.path.write_text(''.join([*lines[:2], lines[-1]]))
        with self.assertRaises(ValueError):
            list(machine_reports.reports(self.path))

    def test_transport_counts_do_not_conflate_booleans_floats_and_naturals(self):
        for value in [True, 1.0, '1']:
            for index, tag, field in [(0, codec.BEGIN, 'version'), (-1, codec.END, 'entries')]:
                with self.subTest(value=value, field=field):
                    lines = self.stream()
                    lines[index] = self.line(tag, {field: value})
                    self.path.write_text(''.join(lines))
                    with self.assertRaises(ValueError):
                        list(machine_reports.reports(self.path))

    def test_legacy_values_are_not_interpreted_as_new_transport(self):
        self.path.write_text(self.line('RESULT', {codec.REFERENCE: 9}))
        self.assertEqual(list(machine_reports.reports(self.path))[0]['value'], {codec.REFERENCE: 9})

    def test_mutating_one_decoded_occurrence_cannot_change_another(self):
        self.path.write_text(''.join(self.stream()))
        records = machine_reports.reports(self.path)
        first = next(records)
        first['value']['a']['counted_data'].clear()
        self.assertEqual(first['value']['again'][0], self.artifact)
        self.assertEqual(next(records)['value'], self.original)
        self.assertEqual(list(records), [])

    def test_expansion_does_not_add_a_recursive_depth_limit(self):
        decoder = codec.Decoder()
        decoder.table = [self.artifact]
        value = {codec.REFERENCE: 0}
        for _ in range(12000):
            value = [value]
        result = decoder.expand(value)
        for _ in range(12000):
            result = result[0]
        self.assertEqual(result, self.artifact)

    def test_term_and_artifact_references_compose_and_keep_original_bytes(self):
        value = {'pair': [{'payload': [256]}, {'target': {'whole_artifact': self.artifact}}]}
        self.path.write_text(self.line('RESULT', [value, value]))
        expected = machine_reports.boundary(self.path)
        stored = {'pair': [{'payload': [256]}, {'target': {'whole_artifact': {codec.REFERENCE: 0}}}]}
        lines = [self.line(codec.BEGIN, {'version': 2}), self.line(codec.ENTRY, self.artifact, '0 '),
                 self.line(codec.TERM_ENTRY, stored, '0 '),
                 self.line('RESULT', [{codec.TERM_REFERENCE: 0}, {codec.TERM_REFERENCE: 0}]),
                 self.line(codec.END, {'entries': 1, 'terms': 1})]
        self.path.write_text(''.join(lines))
        self.assertEqual(machine_reports.boundary(self.path), expected)
        records = list(machine_reports.reports(self.path))
        records[0]['value'][0]['pair'][0]['payload'].clear()
        self.assertEqual(records[0]['value'][1], value)

    def test_term_encoder_uses_versioned_complete_native_operations(self):
        code = native_program_json.ARTIFACT_ROWS + program_evaluation_json.PRELUDE
        result = codec.program(code, parallel=True, terms=True)
        self.assertIn('N.complete_term_reference term', result)
        self.assertIn('NATIVE_ARTIFACT_STREAM {\\"version\\":2}', result)
        self.assertIn('\\"terms\\":', result)
        self.assertIn('fun jterm_raw value', result)
        self.assertEqual(result.count('fun jterm term'), 1)
        self.assertNotIn('= ref ', result)

    def test_unrecognized_streaming_renderer_refuses(self):
        code = native_program_json.ARTIFACT_ROWS + 'fun wemit tag body = body ();\n'
        with self.assertRaises(AssertionError):
            codec.program(code, parallel=True, terms=True)

    def test_malformed_or_forward_term_references_refuse(self):
        for value in [{'pair': []}, {'payload': [True]}, {'unknown': []},
                      {codec.TERM_REFERENCE: 0}]:
            self.path.write_text(self.line(codec.BEGIN, {'version': 2}) +
                self.line(codec.TERM_ENTRY, value, '0 ') +
                self.line('RESULT', {codec.TERM_REFERENCE: 0}) +
                self.line(codec.END, {'entries': 0, 'terms': 1}))
            with self.assertRaises(ValueError):
                list(machine_reports.reports(self.path))

    def test_deferred_records_hash_every_original_byte_without_materializing(self):
        self.path.write_text(''.join(self.stream()))
        eager = list(machine_reports.reports(self.path))
        expected = hashlib.sha256()
        for row in eager:
            machine_reports.canonical_update(expected, row)
        deferred = list(machine_reports.reports(self.path, deferred=True))
        actual = hashlib.sha256()
        for row in deferred:
            self.assertIsNone(row.materialized)
            machine_reports.canonical_update(actual, row)
            self.assertIsNone(row.materialized)
        self.assertEqual(actual.digest(), expected.digest())
        self.assertEqual(machine_reports.field(deferred[0], 'a'), self.artifact)
        self.assertEqual(machine_reports.value_keys(deferred[0]), set(self.original))
        self.assertIsNone(deferred[0].materialized)
        self.assertTrue(machine_reports.record_equal(deferred[0], eager[0]))
        self.assertTrue(machine_reports.field_equal(deferred[0], ('a',), eager[0], ('a',)))
        eager[0]['value']['a']['carrier'].append([7])
        self.assertFalse(machine_reports.record_equal(deferred[0], eager[0]))
        self.assertFalse(machine_reports.field_equal(deferred[0], ('a',), eager[0], ('a',)))

    def test_complete_byte_comparison_handles_different_chunk_boundaries(self):
        self.assertTrue(machine_reports._same_bytes([b'', b'abc', b'def'], [b'ab', b'', b'cdef']))
        self.assertFalse(machine_reports._same_bytes([b'abc', b'def'], [b'abcdefg']))
        self.assertFalse(machine_reports._same_bytes([b'abc', b'def'], [b'abXdef']))

    def test_reference_aware_canonical_bytes_keep_escaping_scalars_and_order(self):
        self.path.write_text(''.join(self.stream()))
        rows = list(machine_reports.reports(self.path, deferred=True))
        decoder = rows[0].decoder
        raw = {'z': [True, None, -0.0, 1.25, 'Ω\n"\\'],
               'a': [{codec.REFERENCE: 0}, {codec.REFERENCE: 0}]}
        expected = json.dumps(decoder.expand(raw), sort_keys=True, separators=(',', ':'), allow_nan=False).encode()
        self.assertEqual(b''.join(decoder.canonical_chunks(raw)), expected)
        raw['a'].reverse()
        self.assertEqual(b''.join(decoder.canonical_chunks(raw)), expected)


if __name__ == '__main__':
    unittest.main()
