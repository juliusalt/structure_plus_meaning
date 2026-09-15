"""Compression must preserve output, errors and the original reconstruction guards."""
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import compressed_machine_reports
import compressed_native_execution
import compressed_reconstruction
from evidence_io import digest
import machine_reports
import reconstruction


class CompressedExecutionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='compressed-execution-test-')
        self.addCleanup(temporary.cleanup)
        self.output = Path(temporary.name)

    def test_binary_output_and_nonzero_return_are_preserved(self):
        payload = bytes(range(256)) * 8193
        source = self.output / 'original.bin'
        source.write_bytes(payload)
        compressed = self.output / 'results.gz'
        command = [sys.executable, '-c',
                   'import pathlib,sys; sys.stdout.buffer.write(pathlib.Path(sys.argv[1]).read_bytes()); sys.exit(7)', str(source)]
        code, identity = compressed_native_execution.compressed_execution(command, compressed, 10)
        self.assertEqual(code, 7)
        self.assertEqual(gzip.decompress(compressed.read_bytes()), payload)
        self.assertEqual(identity, {'sha256': hashlib.sha256(payload).hexdigest(), 'bytes': len(payload)})

    def test_timeout_keeps_a_readable_complete_compression_container(self):
        compressed = self.output / 'timeout.gz'
        command = [sys.executable, '-c',
                   'import sys,time; sys.stdout.write("retained prefix"); sys.stdout.flush(); time.sleep(5)']
        with self.assertRaises(subprocess.TimeoutExpired):
            compressed_native_execution.compressed_execution(command, compressed, 1)
        self.assertEqual(gzip.decompress(compressed.read_bytes()), b'retained prefix')

    def test_parser_and_canonical_boundary_match_the_original(self):
        raw = self.output / 'results.log'
        raw.write_text('physical timing line\nNATIVE 1 {"value":[null,true,"quoted \\\" word",{"x":[1,2]}]}\n'
                       'NATIVE 2 {"value":false}\n')
        compressed = raw.with_name('results.log.gz')
        compressed.write_bytes(gzip.compress(raw.read_bytes()))
        self.assertEqual(list(compressed_machine_reports.reports(compressed)), list(machine_reports.reports(raw)))
        self.assertEqual(compressed_reconstruction.compressed_boundary(raw), machine_reports.boundary(raw))
        compressed.write_bytes(gzip.compress(b'NATIVE {"repeated":1,"repeated":2}\n'))
        with self.assertRaises(ValueError):
            compressed_reconstruction.compressed_boundary(raw)

    def test_reconstruction_keeps_stage_report_and_input_guards(self):
        source = self.output / 'recipe.py'
        source.write_text('fixed recipe bytes\n')
        tracked = {str(source): digest(source)}
        native = self.output / 'native'
        native.mkdir()
        raw = native / 'results.log'
        compressed = native / 'results.log.gz'
        content = b'NATIVE 0 {"input":[1,2],"output":true}\n'
        compressed.write_bytes(gzip.compress(content))
        expected = {'version': 1, 'reports': {'native': compressed_reconstruction.compressed_boundary(raw)}}
        recipe = reconstruction.Recipe('fixture', ('Fixture',), 'Fixture:fixture.ML', 'Fixture_Rebuild',
                                       ((reconstruction.Execution('native', 'fixture.py'),),), 'Storage fixture.')

        def finish(names=('proof', 'diagnostics', 'export', 'native'), failed=None, supplied=False):
            steps = [{'name': name, 'exit_code': int(name == failed)} for name in names]
            with compressed_reconstruction.compressed_storage():
                result = reconstruction.finish_reconstruction(self.output, self.output, recipe, steps,
                                                               expected, tracked, supplied)
            self.assertIs(reconstruction.boundary, machine_reports.boundary)
            return result

        self.assertEqual(finish()['status'], 'accepted')
        self.assertEqual(finish(('proof', 'export', 'native'))['status'], 'failed')
        self.assertEqual(finish(failed='native')['status'], 'failed')
        self.assertFalse(finish(('native',), supplied=True)['sources_rebuilt'])
        compressed.write_bytes(gzip.compress(content.replace(b'true', b'false')))
        self.assertEqual(finish()['status'], 'failed')
        compressed.write_bytes(gzip.compress(content))
        source.write_text('changed recipe bytes\n')
        self.assertFalse(finish()['recipe_inputs_unchanged'])
        compressed.unlink()
        self.assertIn('error', finish())


if __name__ == '__main__':
    unittest.main()
