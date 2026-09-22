"""The probe: its summary file, renamed copies of changed and intermediate base theories, the refusal of a
load its bound cannot hold, and stale heap imports reported as the cause of a run's messages."""

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
        (work / 'New.thy').write_text('theory New imports Main\nbegin\nend\n')
        (work / 'Pre.thy').write_text('theory Pre imports Main\nbegin\nend\n')
        with mock.patch.object(probe_theories.proof_contexts, 'load_parent',
                               return_value={'sources': {'A': 'x'}, 'session': 'S', 'directories': []}), \
                mock.patch.object(probe_theories, 'workspace_theories',
                                  return_value={'New': work / 'New.thy', 'Pre': work / 'Pre.thy'}), \
                mock.patch.object(probe_theories, 'changed', return_value={'New': None}), \
                mock.patch.object(probe_theories, 'prepare', return_value=(work / 'thy', {'New': []}, {'New': []})), \
                mock.patch.object(probe_theories, 'load_estimate', return_value=(9.0, 100)), \
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
    """Changed base theories, and the unchanged theories between them and a loaded theory, are loaded from the
    tree under renamed copies, in dependency order."""

    SOURCES = {'A': 'theory A imports Main\nbegin\ndefinition foo where "foo = (0::nat)"\nend\n',
               'B': 'theory B imports A C\nbegin\nlemma "A.foo = 0" by (simp add: A.foo_def)\nend\n',
               'C': 'theory C imports A\nbegin\nend\n',
               'N': 'theory N imports B\nbegin\nend\n'}
    CONTEXT = {'sources': {'A': 'a', 'B': 'b', 'C': 'c', 'D': 'd', 'E': 'e'}, 'session': 'S', 'directories': [],
               'providers': {n: {'theory': 'S.' + n} for n in 'ABCDE'},
               'imports': {'A': ['Main'], 'B': ['A', 'C'], 'C': ['A'], 'D': ['C'], 'E': ['Main']}}
    OK = {'exit': 0, 'text': 'PROBE THEORIES LOADED\n', 'timed_out': False, 'last_command': None, 'errors': []}

    def present(self, directory, sources=None):
        paths = {}
        for name, text in (sources or self.SOURCES).items():
            paths[name] = directory / (name + '.thy')
            paths[name].write_text(text)
        return paths

    def run_probe(self, root, differing, targets=(), load=(), from_heap=(), run=None, context=None,
                  sources=None):
        present = self.present(root, sources)
        run = run or self.OK
        with mock.patch.object(probe_theories.proof_contexts, 'load_parent', return_value=context or self.CONTEXT), \
                mock.patch.object(probe_theories, 'workspace_theories', return_value=present), \
                mock.patch.object(probe_theories, 'changed', return_value=differing), \
                mock.patch.object(probe_theories, 'run_logged', return_value=run) as runner:
            summary = probe_theories.probe(Path('/base'), root / 'work', list(targets), list(load), {}, {}, 0, 60,
                                           from_heap=list(from_heap))
        return summary, runner

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
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            summary, _ = self.run_probe(root, {'A': 'a', 'B': 'b', 'N': None})
            self.assertEqual(summary['from_tree'], {'A': 'A_Probe', 'B': 'B_Probe', 'C': 'C_Probe'})
            self.assertEqual(summary['intermediate'], ['C'])
            self.assertEqual(summary['new'], ['N'])
            self.assertEqual(summary['order'], ['A', 'C', 'B', 'N'])
            self.assertEqual(summary['certified'], ['A', 'C', 'B', 'N'])
            self.assertEqual(summary['not_rechecked'], ['D'])
            self.assertEqual(summary['stale_heap_imports'], {})
            self.assertIsNone(summary['cause'])
            self.assertEqual(summary['from_heap_despite_change'], [])
            script = (root / 'work' / 'probe.ML').read_text().splitlines()
            self.assertEqual([line.rsplit('/', 1)[1].rstrip('";') for line in script[:4]],
                             ['A_Probe', 'C_Probe', 'B_Probe', 'N'])
            self.assertIn('imports "A_Probe"', (root / 'work' / 'theories' / 'C_Probe.thy').read_text())

    def test_intermediate_between_two_changed(self):
        """#261's shape: B does not import A itself, only through the unchanged C."""
        sources = dict(self.SOURCES, B='theory B imports C\nbegin\nend\n')
        context = dict(self.CONTEXT, imports=dict(self.CONTEXT['imports'], B=['C']))
        with tempfile.TemporaryDirectory() as directory:
            summary, _ = self.run_probe(Path(directory), {'A': 'a', 'B': 'b'}, context=context, sources=sources)
            self.assertEqual(summary['intermediate'], ['C'])
            self.assertEqual(summary['order'], ['A', 'C', 'B'])
            self.assertEqual(summary['stale_heap_imports'], {})
            self.assertEqual(summary['certified'], ['A', 'C', 'B'])

    def test_intermediates_graph_only(self):
        graph = {'A': [], 'C': ['A'], 'X': ['C'], 'B': ['X'], 'D': ['C'], 'Y': ['Main']}
        self.assertEqual(probe_theories.intermediate_theories(graph, {'B': ['X']}, {'A', 'B'}, {'A', 'B'}),
                         ['C', 'X'])
        self.assertEqual(probe_theories.intermediate_theories(graph, {'B': ['X']}, {'A', 'B'}, {'A', 'B'}, {'X'}),
                         ['C'])
        self.assertEqual(probe_theories.intermediate_theories(graph, {'N': ['Y']}, {'A'}, {'A', 'N'}), [])

    def test_theory_closure_certified(self):
        with tempfile.TemporaryDirectory() as directory:
            summary, _ = self.run_probe(Path(directory), {'A': 'a', 'B': 'b', 'N': None}, targets=['B'])
            self.assertEqual(summary['order'], ['A', 'C', 'B'])
            self.assertEqual(summary['certified'], ['A', 'C', 'B'])

    def test_load_additive(self):
        sources = dict(self.SOURCES, E='theory E imports Main\nbegin\nend\n')
        with tempfile.TemporaryDirectory() as directory:
            summary, _ = self.run_probe(Path(directory), {'A': 'a'}, load=['E'], sources=sources)
            self.assertEqual(sorted(summary['from_tree']), ['A', 'E'])

    def test_refused_before_load(self):
        with tempfile.TemporaryDirectory() as directory:
            with mock.patch.object(probe_theories, 'STARTUP_SECONDS', 100):
                summary, runner = self.run_probe(Path(directory), {'A': 'a', 'B': 'b', 'N': None})
            runner.assert_not_called()
            self.assertFalse(summary['loaded'])
            self.assertEqual(summary['certified'], [])
            self.assertIn('A -> C -> B -> N', summary['refused'])
            self.assertIn('intermediates: C', summary['refused'])
            self.assertEqual(summary['errors'], [summary['refused']])
            self.assertGreater(summary['estimate_seconds'], 60)

    def test_stale_cause(self):
        run = {'exit': 1, 'text': '*** Undefined constant: "foo"\n', 'timed_out': False, 'last_command': None,
               'errors': ['*** Undefined constant: "foo"']}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'work').mkdir()
            summary, _ = self.run_probe(root, {'A': 'a', 'B': 'b'}, from_heap=['C'], run=run)
            self.assertEqual(summary['intermediate'], [])
            self.assertEqual(summary['stale_heap_imports'], {'B': ['A']})
            self.assertTrue(summary['cause'].startswith('stale_heap_imports: B reaches the heap copy of A'))
            self.assertEqual(summary['errors'], [summary['cause']])
            self.assertEqual(summary['messages'], ['*** Undefined constant: "foo"'])
            self.assertEqual(summary['certified'], [])
            self.assertIn('PROBE CAUSE: stale_heap_imports', (root / 'work' / 'probe.log').read_text())

    def test_from_heap(self):
        with tempfile.TemporaryDirectory() as directory:
            summary, _ = self.run_probe(Path(directory), {'A': 'a', 'N': None}, targets=['N'], load=['N'],
                                        from_heap=['A'])
            self.assertEqual(summary['from_tree'], {})
            self.assertEqual(summary['from_heap_despite_change'], ['A'])
            self.assertEqual(summary['not_rechecked'], [])


class BaseContext(unittest.TestCase):
    def test_unverified_reads_claims(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            claims = {'session': 'S', 'sources': {'A': 'a'}, 'imports': {'A': []}, 'providers': {},
                      'directories': ['d'], 'stored': {}}
            (base / 'accepted-context.json').write_text(json.dumps(claims))
            with mock.patch.object(probe_theories.proof_contexts, 'load_parent') as verify:
                self.assertEqual(probe_theories.base_context(base)['sources'], {'A': 'a'})
                verify.assert_not_called()
                probe_theories.base_context(base, verify=True)
                verify.assert_called_once()


if __name__ == '__main__':
    unittest.main()
