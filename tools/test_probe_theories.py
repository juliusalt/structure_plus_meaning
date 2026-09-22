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
                mock.patch.object(probe_theories, 'prepare', return_value=(work / 'thy', {'New': []}, {'New': []})), \
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


class ChangedBaseTheories(unittest.TestCase):
    """Changed base theories are loaded from the tree under renamed copies, in dependency order."""

    SOURCES = {'A': 'theory A imports Main\nbegin\ndefinition foo where "foo = (0::nat)"\nend\n',
               'B': 'theory B imports A C\nbegin\nlemma "A.foo = 0" by (simp add: A.foo_def)\nend\n',
               'N': 'theory N imports B\nbegin\nend\n'}
    CONTEXT = {'sources': {'A': 'a', 'B': 'b', 'C': 'c', 'D': 'd', 'E': 'e'}, 'session': 'S', 'directories': [],
               'providers': {n: {'theory': 'S.' + n} for n in 'ABCDE'},
               'imports': {'A': ['Main'], 'B': ['A', 'C'], 'C': ['A'], 'D': ['C'], 'E': ['Main']}}

    def present(self, directory):
        paths = {}
        for name, text in self.SOURCES.items():
            paths[name] = directory / (name + '.thy')
            paths[name].write_text(text)
        return paths

    def test_prepare_renames(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            present = self.present(root)
            renamed = {'A': 'A_Probe', 'B': 'B_Probe'}
            out, imports, complete = probe_theories.prepare(root / 'work', self.CONTEXT, present, {'A', 'B', 'N'},
                                                             {}, {}, renamed)
            self.assertEqual(sorted(p.name for p in out.glob('*.thy')), ['A_Probe.thy', 'B_Probe.thy', 'N.thy'])
            b = (out / 'B_Probe.thy').read_text()
            self.assertTrue(b.startswith('theory B_Probe imports "A_Probe" "S.C"'))
            self.assertIn('A_Probe.foo = 0', b)
            self.assertIn('A_Probe.foo_def', b)
            self.assertIn('imports "B_Probe"', (out / 'N.thy').read_text())
            self.assertEqual(probe_theories.ordered(imports), ['A', 'B', 'N'])
            self.assertEqual(complete['B'], ['A', 'C'])

    def test_summary(self):
        run = {'exit': 0, 'text': 'PROBE THEORIES LOADED\n', 'timed_out': False, 'last_command': None, 'errors': []}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            present = self.present(root)
            with mock.patch.object(probe_theories.proof_contexts, 'load_parent', return_value=self.CONTEXT), \
                    mock.patch.object(probe_theories, 'workspace_theories', return_value=present), \
                    mock.patch.object(probe_theories, 'changed', return_value={'A': 'a', 'B': 'b', 'N': None}), \
                    mock.patch.object(probe_theories, 'run_logged', return_value=run):
                summary = probe_theories.probe(Path('/base'), root / 'work', [], [], {}, {}, 0, 60)
            self.assertEqual(summary['from_tree'], {'A': 'A_Probe', 'B': 'B_Probe'})
            self.assertEqual(summary['new'], ['N'])
            self.assertEqual(summary['order'], ['A', 'B', 'N'])
            self.assertEqual(summary['certified'], ['A', 'B', 'N'])
            self.assertEqual(summary['not_rechecked'], ['C', 'D'])
            self.assertEqual(summary['stale_heap_imports'], {'B': ['A']})
            self.assertEqual(summary['from_heap_despite_change'], [])
            script = (root / 'work' / 'probe.ML').read_text().splitlines()
            self.assertEqual([line.rsplit('/', 1)[1].rstrip('";') for line in script[:3]],
                             ['A_Probe', 'B_Probe', 'N'])

    def test_from_heap(self):
        run = {'exit': 0, 'text': 'PROBE THEORIES LOADED\n', 'timed_out': False, 'last_command': None, 'errors': []}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            present = self.present(root)
            with mock.patch.object(probe_theories.proof_contexts, 'load_parent', return_value=self.CONTEXT), \
                    mock.patch.object(probe_theories, 'workspace_theories', return_value=present), \
                    mock.patch.object(probe_theories, 'changed', return_value={'A': 'a', 'N': None}), \
                    mock.patch.object(probe_theories, 'run_logged', return_value=run):
                summary = probe_theories.probe(Path('/base'), root / 'work', ['N'], ['N'], {}, {}, 0, 60,
                                               from_heap=['A'])
            self.assertEqual(summary['from_tree'], {})
            self.assertEqual(summary['from_heap_despite_change'], ['A'])
            self.assertEqual(summary['not_rechecked'], [])


if __name__ == '__main__':
    unittest.main()
