#!/usr/bin/env python3
"""Every refusal the check makes before it builds names, in the text a session reads, what it found.

The cases are driven from synthetic source trees, never from this repository's own sources: a
refusal is exercised by a tree that carries exactly the offending item, and the assertion is that
the offender appears in the text.
"""
from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

import sys

import check
import execution_support
import incremental_check
import probe_theories


def write_project(root: Path, declared: list, files: dict) -> Path:
    """A synthetic project: a ROOT declaring `declared`, and the theory files of `files`."""
    (root / 'theories').mkdir(parents=True)
    lines = ['session Synthetic = Pure +', '  options [document = false]', '  theories']
    lines += ['    ' + name for name in declared]
    (root / 'ROOT').write_text('\n'.join(lines) + '\n')
    for name, body in files.items():
        (root / 'theories' / (name + '.thy')).write_text(body)
    return root


def theory(name: str, body: str = '') -> str:
    return 'theory ' + name + '\n  imports Pure\nbegin\n' + body + 'end\n'


class ProbeTimeout(unittest.TestCase):
    """A probe is bounded without naming its limit, and a timed-out one names where it stood."""

    def test_default_timeout_is_sixty_seconds(self):
        self.assertEqual(probe_theories.DEFAULT_TIMEOUT, 60)

    def test_timed_out_run_names_its_last_command_and_log(self):
        with tempfile.TemporaryDirectory() as scratch:
            log = Path(scratch) / 'probe.log'
            stand_in = [sys.executable, '-u', '-c',
                        "print('### theory Candidate'); print('have stuck: \"P\"'); print(); "
                        "import time; time.sleep(30)"]
            run = probe_theories.run_logged(stand_in, log, 1)
            self.assertTrue(run['timed_out'])
            self.assertEqual(run['exit'], 'timeout')
            self.assertEqual(run['last_command'], 'have stuck: "P"')
            self.assertTrue(run['errors'])
            self.assertIn('have stuck: "P"', run['errors'][-1])
            self.assertIn(str(log), run['errors'][-1])

    def test_completed_run_is_not_a_timeout(self):
        with tempfile.TemporaryDirectory() as scratch:
            log = Path(scratch) / 'probe.log'
            run = probe_theories.run_logged([sys.executable, '-c', "print('done')"], log, 30)
            self.assertFalse(run['timed_out'])
            self.assertEqual(run['exit'], 0)
            self.assertIsNone(run['last_command'])
            self.assertEqual(run['errors'], [])


class SourceCheckRefusals(unittest.TestCase):
    """The three members of check.source_checks() that refuse, each naming its offender."""

    def test_accepted_sources_refuse_nothing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = write_project(Path(directory), ['Only'], {'Only': theory('Only')})
            structure = check.source_checks(root)
            self.assertEqual(structure['refusals'], [])
            self.assertEqual(structure['theory_count'], 1)

    def test_unlisted_theory_names_its_file(self):
        with tempfile.TemporaryDirectory() as directory:
            root = write_project(Path(directory), ['Declared'],
                                 {'Declared': theory('Declared'), 'Extra': theory('Extra')})
            structure = check.source_checks(root)
            self.assertEqual(structure['unlisted_theories'], ['Extra'])
            text = incremental_check.source_check_refusal(structure)
            self.assertIn('theories/Extra.thy', text)
            self.assertNotIn('theories/Declared.thy', text)

    def test_missing_theory_file_names_the_root_line_that_declares_it(self):
        with tempfile.TemporaryDirectory() as directory:
            root = write_project(Path(directory), ['First', 'Absent'], {'First': theory('First')})
            structure = check.source_checks(root)
            self.assertEqual(structure['missing_theory_files'], ['Absent'])
            text = incremental_check.source_check_refusal(structure)
            self.assertIn('ROOT line 5 declares Absent', text)
            self.assertIn('theories/Absent.thy', text)

    def test_proof_escape_names_its_file_line_and_text(self):
        source = 'theory Escaped\n  imports Pure\nbegin\nlemma trivial: "True" sorry\nend\n'
        with tempfile.TemporaryDirectory() as directory:
            root = write_project(Path(directory), ['Escaped'], {'Escaped': source})
            structure = check.source_checks(root)
            self.assertEqual([(e['file'], e['line']) for e in structure['proof_escape_matches']],
                             [('theories/Escaped.thy', 4)])
            text = incremental_check.source_check_refusal(structure)
            self.assertIn('theories/Escaped.thy:4', text)
            self.assertIn('sorry', text)

    def test_every_offender_is_named_together(self):
        source = 'theory Escaped\n  imports Pure\nbegin\nlemma trivial: "True" oops\nend\n'
        with tempfile.TemporaryDirectory() as directory:
            root = write_project(Path(directory), ['Escaped', 'Absent'],
                                 {'Escaped': source, 'Extra': theory('Extra')})
            text = incremental_check.source_check_refusal(check.source_checks(root))
            for named in ('Absent', 'theories/Extra.thy', 'theories/Escaped.thy:4', 'oops'):
                self.assertIn(named, text)


class SourceGraphRefusal(unittest.TestCase):
    """The source graph's failures carry, into the report, the theory and who demanded it."""

    def test_missing_local_theory_reaches_the_report_text(self):
        with tempfile.TemporaryDirectory() as directory:
            root = write_project(Path(directory), ['Present'], {'Present': theory('Present')})
            with self.assertRaises(ValueError) as raised:
                execution_support.source_graph(root, [], ['Absent'])
            # The report writes exactly this text as its error, so the theory's name reaches the reader.
            reported = f'{type(raised.exception).__name__}: {raised.exception}'
            self.assertIn('Absent', reported)
            self.assertIn('Missing requested theory: Absent', reported)


    def test_unresolved_import_names_the_theory_that_demanded_it(self):
        source = 'theory Present\n  imports Absent\nbegin\nend\n'
        with tempfile.TemporaryDirectory() as directory:
            root = write_project(Path(directory), ['Present'], {'Present': source})
            with self.assertRaises(ValueError) as raised:
                execution_support.source_graph(root, [], ['Present'])
            reported = f'{type(raised.exception).__name__}: {raised.exception}'
            self.assertIn('Missing local theory: Absent', reported)
            self.assertIn('imported by Present', reported)

    def test_cyclic_import_names_the_chain_that_closes_it(self):
        files = {'Head': 'theory Head\n  imports Middle\nbegin\nend\n',
                 'Middle': 'theory Middle\n  imports Tail\nbegin\nend\n',
                 'Tail': 'theory Tail\n  imports Head\nbegin\nend\n'}
        with tempfile.TemporaryDirectory() as directory:
            root = write_project(Path(directory), sorted(files), files)
            with self.assertRaises(ValueError) as raised:
                execution_support.source_graph(root, [], ['Head'])
            reported = f'{type(raised.exception).__name__}: {raised.exception}'
            self.assertIn('Cyclic theory import: Head', reported)
            # The importer that closes the cycle, and the chain the traversal walked to reach it.
            self.assertIn('Tail imports Head', reported)
            self.assertIn('Head imports Middle imports Tail imports Head', reported)

class BaseAndRecipeRefusals(unittest.TestCase):
    """The remaining refusals of the pre-build path, over synthetic directories and names."""

    def test_stale_output_directory_is_named(self):
        # This refusal precedes the report, so its text reaches the session as the failure itself.
        with tempfile.TemporaryDirectory() as directory:
            output = (Path(directory) / 'output').resolve()
            output.mkdir()
            with self.assertRaises(AssertionError) as raised:
                incremental_check.validate(Path(directory) / 'base', output, threads=1, jobs=1,
                                           selected=[], all_recipes=False, timeout=1,
                                           lineage=('unused-lineage',))
            self.assertIn(str(output), str(raised.exception))

    def test_changed_session_declaration_names_both_declarations(self):
        text = incremental_check.declaration_refusal(Path('/synthetic/base'),
                                                     'session Now = Pure +', 'session Then = Pure +')
        self.assertIn('/synthetic/base', text)
        self.assertIn('session Now = Pure +', text)
        self.assertIn('session Then = Pure +', text)

    def test_base_without_a_stored_heap_names_the_base(self):
        self.assertIn('/synthetic/base', incremental_check.stored_heap_refusal(Path('/synthetic/base')))

    def test_stale_active_context_names_its_selection_and_receipt(self):
        text = incremental_check.active_context_refusal(Path('/synthetic/active.json'),
                                                        '/synthetic/context', '/synthetic/context/receipt.json')
        self.assertIn('/synthetic/active.json', text)
        self.assertIn('/synthetic/context', text)
        self.assertIn('receipt.json', text)

    def test_repeated_recipe_name_is_named(self):
        text = incremental_check.repeated_recipe_refusal(['alpha', 'beta', 'alpha'])
        self.assertIn('alpha', text)
        self.assertNotIn('beta', text)

    def test_unknown_recipe_name_is_named_beside_the_declared_ones(self):
        text = incremental_check.unknown_recipe_refusal(['absent', 'alpha'], ['alpha', 'beta'])
        self.assertIn('absent', text)
        self.assertIn('beta', text)


if __name__ == '__main__':
    unittest.main()
