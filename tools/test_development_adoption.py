"""An unsuccessful adoption withdraws its installation and writes its receipt (task 254, the review's P2).

Each test runs development_adoption.adopt on the retained demanded-identity answer against a temporary
project holding copies of the layer theory and ROOT, so no repository file is written. The two judgments
and the incremental check are stubs, no Isabelle run is made, and one failure is injected. An unsuccessful
adoption must leave the answer's theory absent, the layer and ROOT at their original text and a receipt
written. Every exit is covered by the tool's one cleanup path (task 255): any exception, BaseException
included, a failure inside install() after its first write, and SIGTERM or SIGHUP during the check; a
withdrawal that fails part-way names the file it could not restore.
"""
import argparse
import contextlib
import io
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import types
import unittest
from unittest import mock

import development_adoption
import development_answer

RECORD = development_answer.ROOT / 'validation/development-answers/demanded-identity.json'
TIMEOUT = subprocess.TimeoutExpired(['development_answer.py', 'answer'], 1200)
ACCEPTED = {'status': 'judged', 'accepted': True, 'adopted': True,
            'summary': {'counts': [0, 0, 0, 0, 1, 1, 0, 1], 'published': True}}


class AdoptionExits(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.project = Path(directory.name) / 'project'
        (self.project / 'theories').mkdir(parents=True)
        self.record = json.loads(RECORD.read_text())
        self.answer = self.record['answer']
        self.name = development_answer.answer_name(self.answer)
        self.theory = self.project / 'theories' / (self.name + '.thy')
        self.layer = self.project / 'theories' / (development_adoption.LAYER + '.thy')
        self.root = self.project / 'ROOT'
        shutil.copyfile(development_answer.ROOT / 'theories' / self.layer.name, self.layer)
        shutil.copyfile(development_answer.ROOT / 'ROOT', self.root)
        self.original = {'layer': self.layer.read_text(), 'root': self.root.read_text()}
        self.output = Path(directory.name) / 'adoption'

    def adopt(self, final=ACCEPTED, check=None, before=None, control=False, patches=()):
        """Run the adoption; return its exit code, or the exception it raised."""
        record, answer = self.record, self.answer

        def judge(answer_file, out, timeout):
            if out.name == 'before':
                if before is not None:
                    raise before
                judged = out / 'project' / 'theories' / (development_answer.answer_name(answer) + '.thy')
                judged.parent.mkdir(parents=True)
                judged.write_text(development_answer.answer_theory(development_answer.STATES['refinement_layer'],
                                                                   answer))
                return {'status': 'judged', 'accepted': record['summary'].get('accepted'),
                        'summary': record['summary'], 'verdict_word': record['verdict_word'],
                        'publication_word': record.get('publication_word'), 'seconds': 0.0}
            if isinstance(final, BaseException):
                raise final
            return final

        def run(command, **options):
            if check is not None:
                raise check
            return self.adopt_check_run()(command, **options)

        adopted = development_answer.adopted
        project = self.project
        with mock.patch.object(development_adoption, 'ROOT', project), \
                mock.patch.object(development_adoption, 'judge', judge), \
                mock.patch('subprocess.run', run), \
                mock.patch.object(development_answer, 'adopted', lambda a, p=project: adopted(a, p)):
            for patch in patches:
                patch.start()
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    return development_adoption.adopt(argparse.Namespace(record=RECORD, output=self.output,
                                                                         timeout=600, control=control))
            except BaseException as raised:  # noqa: B036 - an injected interrupt is an outcome here
                return raised
            finally:
                for patch in patches:
                    patch.stop()

    @staticmethod
    def adopt_check_run():
        """The stub of an accepted incremental check."""
        def run(command, **options):
            out = Path(command[command.index('--output') + 1])
            out.mkdir(parents=True)
            (out / 'incremental.json').write_text(json.dumps(
                {'status': 'accepted', 'recipes': {}, 'phases': {}, 'rebuilt_theories': []}))
            return types.SimpleNamespace(returncode=0)
        return run

    def assertWithdrawn(self, outcome):
        self.assertTrue(isinstance(outcome, BaseException) or outcome != 0, outcome)
        self.assertFalse(self.theory.exists(), 'the answer theory stayed installed')
        self.assertEqual(self.layer.read_text(), self.original['layer'], 'the layer import stayed installed')
        self.assertEqual(self.root.read_text(), self.original['root'], 'the ROOT entry stayed installed')
        receipt = self.output / 'receipt.json'
        self.assertTrue(receipt.is_file(), 'no receipt was written')
        self.assertNotEqual(json.loads(receipt.read_text())['status'], 'adopted')

    # Handled on HEAD.

    def test_oserror_at_the_final_judgment_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final=OSError('injected')))

    def test_refusal_at_the_final_judgment_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final={**ACCEPTED, 'accepted': False}))

    def test_control_withdraws_a_successful_adoption(self):
        self.assertEqual(self.adopt(control=True), 0)
        self.assertFalse(self.theory.exists())
        self.assertEqual((self.layer.read_text(), self.root.read_text()),
                         (self.original['layer'], self.original['root']))
        receipt = json.loads((self.output / 'receipt.json').read_text())
        self.assertEqual((receipt['status'], receipt.get('withdrawn')), ('adopted', True))

    def test_success_leaves_the_adoption_installed(self):
        self.assertEqual(self.adopt(), 0)
        self.assertTrue(self.theory.is_file())
        self.assertIn(self.name, development_adoption.investigate.theory_imports(self.layer.read_text(),
                                                                                 development_adoption.LAYER))
        self.assertIn('    ' + self.name + '\n', self.root.read_text())
        receipt = json.loads((self.output / 'receipt.json').read_text())
        self.assertEqual(receipt['status'], 'adopted')
        self.assertNotIn('withdrawn', receipt)

    # Exceptions of any type, before the check, during it and at the final judgment.

    def test_timeout_at_the_final_judgment_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final=TIMEOUT))

    def test_interrupt_at_the_final_judgment_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final=KeyboardInterrupt()))

    def test_interrupt_during_the_check_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(check=KeyboardInterrupt()))

    def test_uncaught_type_in_the_final_checks_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final={**ACCEPTED, 'summary': {'counts': None, 'published': True}}))

    def test_timeout_at_the_first_judgment_writes_a_receipt(self):
        self.assertWithdrawn(self.adopt(before=TIMEOUT))

    def test_system_exit_at_the_final_judgment_is_withdrawn(self):
        outcome = self.adopt(final=SystemExit(3))
        self.assertIsInstance(outcome, SystemExit)
        self.assertWithdrawn(outcome)

    # Termination signals during the check: withdrawn, then delivered again to the handler in place before.

    def assertSignalWithdrawn(self, signum):
        delivered = []
        previous = signal.signal(signum, lambda s, frame: delivered.append(s))
        self.addCleanup(signal.signal, signum, previous)

        def sending(command, **options):
            os.kill(os.getpid(), signum)
            raise AssertionError('the signal did not interrupt the check')
        self.assertWithdrawn(self.adopt(patches=[mock.patch('subprocess.run', sending)]))
        self.assertEqual(delivered, [signum])
        self.assertEqual(json.loads((self.output / 'receipt.json').read_text())['error_type'], 'RunInterrupted')

    def test_sigterm_during_the_check_is_withdrawn(self):
        self.assertSignalWithdrawn(signal.SIGTERM)

    def test_sighup_during_the_check_is_withdrawn(self):
        self.assertSignalWithdrawn(signal.SIGHUP)

    def test_ignored_sighup_during_the_check_is_ignored(self):
        previous = signal.signal(signal.SIGHUP, signal.SIG_IGN)
        self.addCleanup(signal.signal, signal.SIGHUP, previous)
        run = self.adopt_check_run()

        def sending(command, **options):
            os.kill(os.getpid(), signal.SIGHUP)
            return run(command, **options)
        self.assertEqual(self.adopt(patches=[mock.patch('subprocess.run', sending)]), 0)
        self.assertTrue(self.theory.is_file())
        self.assertEqual(json.loads((self.output / 'receipt.json').read_text())['status'], 'adopted')
        self.assertIs(signal.getsignal(signal.SIGHUP), signal.SIG_IGN)

    def test_unwritable_receipt_keeps_the_original_exception(self):
        def failing(path, value):
            raise OSError('injected OSError writing the receipt')
        outcome = self.adopt(final=TIMEOUT,
                             patches=[mock.patch.object(development_adoption, 'write_json', failing)])
        self.assertIsInstance(outcome, OSError)
        self.assertIs(outcome.__cause__, TIMEOUT)
        self.assertFalse(self.theory.exists())
        self.assertEqual((self.layer.read_text(), self.root.read_text()),
                         (self.original['layer'], self.original['root']))

    # Failures inside install() after its first write.

    def test_failure_writing_the_layer_after_the_theory_is_withdrawn(self):
        layer, write_text = self.layer, Path.write_text

        def failing(path, *args, **options):
            if path == layer:
                raise OSError('injected OSError writing the layer')
            return write_text(path, *args, **options)
        self.assertWithdrawn(self.adopt(patches=[mock.patch.object(Path, 'write_text', failing)]))

    def test_failure_hashing_the_installed_files_is_withdrawn(self):
        theories, file_hash = self.project / 'theories', development_adoption.investigate.file_hash

        def failing(path):
            if Path(path).parent == theories:
                raise OSError('injected OSError hashing the installed files')
            return file_hash(path)
        self.assertWithdrawn(self.adopt(patches=[mock.patch.object(development_adoption.investigate, 'file_hash',
                                                                   failing)]))

    # A withdrawal that fails part-way restores what it can and names what it could not.

    def test_partial_withdrawal_names_the_unrestored_file(self):
        root, write_text, writes = self.root, Path.write_text, []

        def failing(path, *args, **options):
            if path == root:
                writes.append(path)
                if len(writes) > 1:
                    raise OSError('injected OSError restoring ROOT')
            return write_text(path, *args, **options)
        outcome = self.adopt(final={**ACCEPTED, 'accepted': False},
                             patches=[mock.patch.object(Path, 'write_text', failing)])
        self.assertIsInstance(outcome, OSError)
        self.assertFalse(self.theory.exists())
        self.assertEqual(self.layer.read_text(), self.original['layer'])
        receipt = json.loads((self.output / 'receipt.json').read_text())
        self.assertEqual(receipt['status'], 'refused')
        self.assertNotIn('withdrawn', receipt)
        self.assertEqual(sorted(receipt['withdrawal']['restored']),
                         ['theories/' + self.name + '.thy', 'theories/' + self.layer.name])
        self.assertEqual(list(receipt['withdrawal']['unrestored']), ['ROOT'])


if __name__ == '__main__':
    unittest.main()
