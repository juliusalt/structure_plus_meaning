"""An unsuccessful adoption withdraws its installation and writes its receipt (task 254, the review's P2).

Each test runs development_adoption.adopt on the retained demanded-identity answer against a temporary
project holding copies of the layer theory, ROOT and the answer's record, so no repository file is written.
The precondition's judgment, the tree's revision, the incremental check and the context the check accepted
are stubs, no Isabelle run is made, and one failure is injected. An unsuccessful adoption must leave the
answer's theory absent, the layer and ROOT at their original text, no retained receipt, and a receipt
written to its output. Every exit is covered by the tool's one cleanup path (task 255): any exception,
BaseException included, a failure inside install() after its first write, and SIGTERM or SIGHUP during the
check; a withdrawal that fails part-way names the file it could not restore. The final step checks the
adoption's evidence and the check's accepted context (task 265): the installed file changed after
installation, a context recording another digest and a tree that differs from its commit are each refused.
"""
import argparse
import contextlib
import hashlib
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
RETAINED = Path('validation/development-adoptions')


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
        self.record_path = self.project / 'validation/development-answers' / RECORD.name
        self.record_path.parent.mkdir(parents=True)
        shutil.copyfile(RECORD, self.record_path)
        self.original = {'layer': self.layer.read_text(), 'root': self.root.read_text()}
        self.output = Path(directory.name) / 'adoption'
        self.frame_text = development_answer.answer_theory(development_answer.STATES['refinement_layer'],
                                                           self.answer)
        self.frame = hashlib.sha256(self.frame_text.encode()).hexdigest()
        self.retained = self.project / RETAINED / (self.name + '.json')

    def adopt(self, final=None, check=None, before=None, control=False, tree='revision-of-the-tree', patches=()):
        """Run the adoption; return its exit code, or the exception it raised.

        `final` is what the check's accepted context records: None the installed frame's digest, a
        BaseException raised while it is read, or the recorded sources themselves."""
        record, answer, frame, frame_text = self.record, self.answer, self.frame, self.frame_text

        def judge(answer_file, out, timeout):
            if before is not None:
                raise before
            judged = out / 'project' / 'theories' / (development_answer.answer_name(answer) + '.thy')
            judged.parent.mkdir(parents=True)
            judged.write_text(frame_text)
            return {'status': 'judged', 'accepted': record['summary'].get('accepted'),
                    'summary': record['summary'], 'verdict_word': record['verdict_word'],
                    'publication_word': record.get('publication_word'), 'frame_sha256': frame, 'seconds': 0.0}

        def sources(context):
            if isinstance(final, BaseException):
                raise final
            return {self.name: frame} if final is None else final

        def revision(project=None):
            if isinstance(tree, BaseException):
                raise tree
            return tree

        def run(command, **options):
            if check is not None:
                raise check
            return self.adopt_check_run()(command, **options)

        with mock.patch.object(development_adoption, 'ROOT', self.project), \
                mock.patch.object(development_adoption, 'judge', judge), \
                mock.patch.object(development_adoption, 'context_sources', sources), \
                mock.patch.object(development_adoption, 'revision', revision), \
                mock.patch('subprocess.run', run):
            for patch in patches:
                patch.start()
            try:
                with contextlib.redirect_stdout(io.StringIO()):
                    return development_adoption.adopt(argparse.Namespace(record=self.record_path,
                                                                         output=self.output,
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
                {'status': 'accepted', 'recipes': {}, 'phases': {}, 'rebuilt_theories': [],
                 'accepted_proof_context': str(out / 'proof')}))
            return types.SimpleNamespace(returncode=0)
        return run

    def assertWithdrawn(self, outcome):
        self.assertTrue(isinstance(outcome, BaseException) or outcome != 0, outcome)
        self.assertFalse(self.theory.exists(), 'the answer theory stayed installed')
        self.assertEqual(self.layer.read_text(), self.original['layer'], 'the layer import stayed installed')
        self.assertEqual(self.root.read_text(), self.original['root'], 'the ROOT entry stayed installed')
        self.assertFalse(self.retained.exists(), 'a receipt was retained')
        receipt = self.output / 'receipt.json'
        self.assertTrue(receipt.is_file(), 'no receipt was written')
        self.assertNotEqual(json.loads(receipt.read_text())['status'], 'adopted')

    # The final evidence step, which replaces the published state judged against itself.

    def test_oserror_at_the_final_evidence_step_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final=OSError('injected')))

    def test_context_with_another_digest_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final={self.name: '0' * 64}))

    def test_context_without_the_theory_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final={}))

    def test_installed_file_changed_after_installation_is_withdrawn(self):
        run, theory = self.adopt_check_run(), self.theory

        def changing(command, **options):
            theory.write_text(theory.read_text() + '\n(* changed *)\n')
            return run(command, **options)
        self.assertWithdrawn(self.adopt(patches=[mock.patch('subprocess.run', changing)]))
        receipt = json.loads((self.output / 'receipt.json').read_text())
        self.assertEqual(receipt['steps']['evidence']['obstruction'], ['installed'])

    def test_control_withdraws_a_successful_adoption(self):
        self.assertEqual(self.adopt(control=True), 0)
        self.assertFalse(self.theory.exists())
        self.assertEqual((self.layer.read_text(), self.root.read_text()),
                         (self.original['layer'], self.original['root']))
        receipt = json.loads((self.output / 'receipt.json').read_text())
        self.assertEqual((receipt['status'], receipt.get('withdrawn'), receipt['control']), ('adopted', True, True))
        self.assertEqual(json.loads(self.retained.read_text()), receipt)
        evidence = development_answer.adoption_evidence(self.answer, self.project)
        self.assertEqual((evidence['present'], evidence['holds']), (False, False))

    def test_success_leaves_the_adoption_installed(self):
        self.assertEqual(self.adopt(), 0)
        self.assertTrue(self.theory.is_file())
        self.assertIn(self.name, development_adoption.investigate.theory_imports(self.layer.read_text(),
                                                                                 development_adoption.LAYER))
        self.assertIn('    ' + self.name + '\n', self.root.read_text())
        receipt = json.loads((self.output / 'receipt.json').read_text())
        self.assertEqual(receipt['status'], 'adopted')
        self.assertNotIn('withdrawn', receipt)
        self.assertEqual((receipt['answer_digest'], receipt['frame_sha256'], receipt['revision'], receipt['record']),
                         (development_answer.answer_digest(self.answer), self.frame, 'revision-of-the-tree',
                          'validation/development-answers/' + RECORD.name))
        self.assertEqual(receipt['steps']['installation']['theory_sha256'], self.frame)
        self.assertEqual(receipt['steps']['context']['recorded_sha256'], self.frame)
        self.assertEqual(json.loads(self.retained.read_text()), receipt)
        self.assertTrue(development_answer.adoption_evidence(self.answer, self.project)['holds'])

    # Refusals before anything: the answer's name already stands, or the tree differs from its commit.

    def test_already_adopted_is_refused(self):
        self.assertEqual(self.adopt(), 0)
        state = {path: path.read_bytes() for path in (self.theory, self.layer, self.root, self.retained)}
        shutil.rmtree(self.output)
        outcome = self.adopt()
        self.assertIsInstance(outcome, AssertionError)
        self.assertIn('already adopted', str(outcome))
        self.assertEqual({path: path.read_bytes() for path in state}, state)

    def test_obstructing_theory_is_refused_and_left_alone(self):
        self.theory.write_text('planted\n')
        outcome = self.adopt()
        self.assertIsInstance(outcome, AssertionError)
        self.assertIn('obstructs', str(outcome))
        self.assertEqual(self.theory.read_text(), 'planted\n')
        self.assertEqual((self.layer.read_text(), self.root.read_text()),
                         (self.original['layer'], self.original['root']))
        self.assertFalse(self.retained.exists())

    def test_tree_differing_from_its_commit_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(tree=AssertionError('The tree differs from its commit: ROOT')))
        self.assertNotIn('precondition', json.loads((self.output / 'receipt.json').read_text())['steps'])

    def test_revision_refuses_a_changed_tree(self):
        project = self.project
        git = ['git', '-C', str(project), '-c', 'user.email=t@t', '-c', 'user.name=t']
        subprocess.run([*git, 'init', '-q'], check=True)
        subprocess.run([*git, 'add', '-A'], check=True)
        subprocess.run([*git, 'commit', '-qm', 'tree'], check=True)
        head = subprocess.run([*git, 'rev-parse', 'HEAD'], check=True, capture_output=True, text=True).stdout.strip()
        self.assertEqual(development_adoption.revision(project), head)
        (project / 'tools').mkdir()
        (project / 'tools' / 'untracked.py').write_text('')
        with self.assertRaises(AssertionError):
            development_adoption.revision(project)
        (project / 'tools' / 'untracked.py').unlink()
        self.root.write_text(self.root.read_text() + '\n')
        with self.assertRaises(AssertionError):
            development_adoption.revision(project)
        self.root.write_text(self.original['root'])
        (project / 'validation' / 'elsewhere.json').write_text('{}')
        self.assertEqual(development_adoption.revision(project), head)

    def test_frame_other_than_the_judged_one_is_refused(self):
        self.frame = '1' * 64
        self.assertWithdrawn(self.adopt())

    # Exceptions of any type, before the check, during it and at the final evidence step.

    def test_timeout_at_the_final_evidence_step_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final=TIMEOUT))

    def test_interrupt_at_the_final_evidence_step_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final=KeyboardInterrupt()))

    def test_interrupt_during_the_check_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(check=KeyboardInterrupt()))

    def test_uncaught_type_in_the_final_step_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final=[]))

    def test_unwritable_retained_receipt_is_withdrawn(self):
        retained, write_text = self.retained, Path.write_text

        def failing(path, *args, **options):
            if path == retained:
                raise OSError('injected OSError retaining the receipt')
            return write_text(path, *args, **options)
        self.assertWithdrawn(self.adopt(patches=[mock.patch.object(Path, 'write_text', failing)]))

    def test_timeout_at_the_first_judgment_writes_a_receipt(self):
        self.assertWithdrawn(self.adopt(before=TIMEOUT))

    def test_system_exit_at_the_final_evidence_step_is_withdrawn(self):
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

    def test_sigint_is_delivered_last_after_the_summary(self):
        delivered = []
        previous = signal.signal(signal.SIGTERM, lambda s, frame: delivered.append(s))
        self.addCleanup(signal.signal, signal.SIGTERM, previous)
        self.addCleanup(signal.signal, signal.SIGINT, signal.getsignal(signal.SIGINT))
        signal.signal(signal.SIGINT, signal.default_int_handler)
        withdraw = development_adoption.withdraw

        def sending(command, **options):
            os.kill(os.getpid(), signal.SIGINT)
            raise AssertionError('the signal did not interrupt the check')

        def withdrawing(plan):
            os.kill(os.getpid(), signal.SIGTERM)
            return withdraw(plan)
        outcome = self.adopt(patches=[mock.patch('subprocess.run', sending),
                                      mock.patch.object(development_adoption, 'withdraw', withdrawing)])
        self.assertIsInstance(outcome, KeyboardInterrupt)
        self.assertWithdrawn(outcome)
        self.assertEqual(delivered, [signal.SIGTERM])

    def test_signal_before_the_first_step_is_raised_there(self):
        delivered = []
        previous = signal.signal(signal.SIGTERM, lambda s, frame: delivered.append(s))
        self.addCleanup(signal.signal, signal.SIGTERM, previous)
        interruption = development_adoption.build.interruption_signals

        @contextlib.contextmanager
        def entering(state):
            with interruption(state):
                os.kill(os.getpid(), signal.SIGTERM)
                yield
        self.assertWithdrawn(self.adopt(patches=[mock.patch.object(development_adoption.build,
                                                                   'interruption_signals', entering)]))
        receipt = json.loads((self.output / 'receipt.json').read_text())
        self.assertEqual((receipt['error_type'], receipt['steps']), ('RunInterrupted', {}))
        self.assertEqual(delivered, [signal.SIGTERM])

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
        outcome = self.adopt(final={self.name: '0' * 64},
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
