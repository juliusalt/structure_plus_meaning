"""The probe writes, beside its log, the summary it prints, with the options it ran with."""

import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import probe_theories


class ProbeSummaryFile(unittest.TestCase):
    def run_probe(self, work, text, timed_out):
        run = {'exit': 'timeout' if timed_out else 0, 'text': text, 'timed_out': timed_out,
               'last_command': 'lemma x' if timed_out else None, 'errors': ['timed out'] if timed_out else []}
        prelude = {'Pre': Path('/p/Pre.thy')}
        with mock.patch.object(probe_theories.proof_contexts, 'load_parent',
                               return_value={'sources': {'A': 'x'}, 'session': 'S', 'directories': []}), \
                mock.patch.object(probe_theories, 'workspace_theories', return_value={'New': 'n', 'Pre': 'p'}), \
                mock.patch.object(probe_theories, 'changed', return_value={'New': None}), \
                mock.patch.object(probe_theories, 'prepare', return_value=(work / 'thy', {'New': []})), \
                mock.patch.object(probe_theories, 'ordered', return_value=['New']), \
                mock.patch.object(probe_theories, 'run_logged', return_value=run):
            return probe_theories.probe(Path('/base'), work, [], [], {'Old': 'Pre'}, prelude, 0, 60)

    def check(self, timed_out, text):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            summary = self.run_probe(work, text, timed_out)
            self.assertEqual(summary['summary'], str(work / 'probe.summary.json'))
            self.assertEqual(Path(summary['summary']).parent, Path(summary['log']).parent)
            self.assertEqual(json.loads(Path(summary['summary']).read_text()), summary)
            self.assertEqual((summary['parallel_proofs'], summary['timeout']), (0, 60))
            self.assertEqual(summary['prelude'], {'Pre': '/p/Pre.thy'})
            self.assertEqual(summary['substituted'], {'Old': 'Pre'})
            self.assertIn('seconds', summary)
            return summary

    def test_completed(self):
        summary = self.check(False, 'Loading New\nPROBE THEORIES LOADED\n')
        self.assertTrue(summary['loaded'])
        self.assertEqual(summary['marker'], 'PROBE THEORIES LOADED')

    def test_timed_out(self):
        summary = self.check(True, 'Loading New\nlemma x\n')
        self.assertFalse(summary['loaded'])
        self.assertIsNone(summary['marker'])
        self.assertTrue(summary['timed_out'])


if __name__ == '__main__':
    unittest.main()
