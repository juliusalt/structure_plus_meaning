"""The probe: its summary file, renamed copies of changed and intermediate base theories, the refusal of a
load its bound cannot hold, stale heap imports reported as the cause of a run's messages, code checks skipped
and named, and a base's own sources."""

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
                mock.patch.object(probe_theories, 'prepare',
                                  return_value=(work / 'thy', {'New': []}, {'New': []}, {})), \
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
            out, imports, complete, skipped = probe_theories.prepare(root / 'work', self.CONTEXT, present,
                                                                      {'A', 'B', 'N'}, {}, {}, renamed)
            self.assertEqual(skipped, {})
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
                         [])
        self.assertEqual(probe_theories.intermediate_theories(graph, {'B': ['X', 'C']}, {'A', 'B'}, {'A', 'B'},
                                                              {'X'}), ['C'])
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


class SkippedCodeChecks(unittest.TestCase):
    """`export_code … checking` needs Isabelle's Scala side: it is blanked in the probe's copy and named."""

    TEXT = ('theory T imports Main\nbegin\n'
            'export_code a b\n  checking SML\n'
            'export_code c in Eval module_name M file_prefix m\n'
            'export_code "(\\<le>) :: t \\<Rightarrow> _" (* c *) checking SML OCaml\n'
            'text \\<open>checking SML\\<close>\nlemma "x = x" by simp\nend\n')

    def test_scan(self):
        written, skipped = probe_theories.skip_code_checks(self.TEXT)
        self.assertEqual(skipped, [{'line': 3, 'command': 'export_code a b checking SML'},
                                   {'line': 6, 'command':
                                    'export_code "(\\<le>) :: t \\<Rightarrow> _" (* c *) checking SML OCaml'}])
        self.assertEqual(written.count('\n'), self.TEXT.count('\n'))
        self.assertNotIn('checking SML\n', written)
        self.assertIn('export_code c in Eval module_name M file_prefix m\n', written)
        self.assertIn('text \\<open>checking SML\\<close>\nlemma "x = x" by simp\nend\n', written)
        self.assertEqual(probe_theories.skip_code_checks('export_code a\ntext \\<open>checking\\<close>\n'),
                         ('export_code a\ntext \\<open>checking\\<close>\n', []))

    def test_summary_names_skipped(self):
        sources = dict(ChangedBaseTheories.SOURCES, A=ChangedBaseTheories.SOURCES['A'].replace(
            '\nend\n', '\nexport_code foo checking SML\nend\n'))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            summary, _ = ChangedBaseTheories().run_probe(root, {'A': 'a', 'B': 'b', 'N': None}, sources=sources)
            expected = {'A': [{'line': 4, 'command': 'export_code foo checking SML'}]}
            self.assertEqual(summary['skipped_code_checks'], expected)
            self.assertEqual(summary['certified'], ['A', 'C', 'B', 'N'])
            self.assertEqual(summary['errors'], [])
            self.assertNotIn('export_code', (root / 'work' / 'theories' / 'A_Probe.thy').read_text())
            self.assertIn('PROBE SKIPPED: A line 4: export_code foo checking SML',
                          (root / 'work' / 'probe.log').read_text())


class AdvancedBase(unittest.TestCase):
    """A theory the tree left as main had it, whose base text is main's newer text, refuses the probe."""

    def test_advanced_theories(self):
        theories = probe_theories.ROOT / 'theories'
        present = {n: theories / (n + '.thy') for n in ('A', 'B', 'C', 'D')}
        batch = b'x blob 2\nb1\ny blob 2\nc1\n'
        outputs = {'merge-base': b'p\n', 'diff': b'theories/A.thy\n', 'ls-files': b'', 'cat-file': batch}
        digests = {b'b1': 'hb', b'c1': 'other'}
        with mock.patch.object(probe_theories, 'git_output', side_effect=lambda *a, text=None: outputs[a[0]]), \
                mock.patch.object(probe_theories.investigate, 'digest', side_effect=digests.get):
            self.assertEqual(probe_theories.advanced_theories({'A': 'ha', 'B': 'hb', 'C': 'hc', 'D': None}, present),
                             ['B'])
        self.assertEqual(probe_theories.advanced_theories({'A': 'ha'}, {'A': Path('/elsewhere/A.thy')}), [])

    def test_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'work').mkdir()
            with mock.patch.object(probe_theories, 'advanced_theories', return_value=['C', 'D']):
                summary, runner = ChangedBaseTheories().run_probe(root, {'A': 'a', 'C': 'c', 'D': 'd'})
            runner.assert_not_called()
            self.assertEqual(summary['advanced'], ['C', 'D'])
            self.assertFalse(summary['loaded'])
            self.assertIn('bring-main', summary['refused'])
            self.assertEqual(summary['errors'], [summary['refused']])
            self.assertFalse((root / 'work' / 'theories').exists())


class BaseSources(unittest.TestCase):
    def test_reads_base_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            sources = Path(directory) / 'original-sources'
            sources.mkdir()
            (sources / 'A.thy').write_text('theory A imports Main\nbegin\nend\n')
            self.assertEqual(probe_theories.workspace_theories((), sources), {'A': sources / 'A.thy'})


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
