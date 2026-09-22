"""An unsuccessful adoption withdraws its installation and writes its receipt (task 254, the review's P2).

Each test runs development_adoption.adopt on the retained demanded-identity answer against a temporary
project holding copies of the layer theory and ROOT, so no repository file is written. The two judgments
and the incremental check are stubs, no Isabelle run is made, and one failure is injected. An unsuccessful
adoption must leave the answer's theory absent, the layer and ROOT at their original text and a receipt
written. The exits the tool leaves unhandled are expected failures, each naming its cause: the handler
catches only AssertionError, OSError, ValueError and KeyError, and withdraws only once install() has
returned, so a failure after install()'s first write is not withdrawn either. A fix removes the markers of
the exits it covers. SIGTERM during the check is examined in task 254's report, not here.
"""
import argparse
import contextlib
import io
import json
from pathlib import Path
import shutil
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
            out = Path(command[command.index('--output') + 1])
            out.mkdir(parents=True)
            (out / 'incremental.json').write_text(json.dumps(
                {'status': 'accepted', 'recipes': {}, 'phases': {}, 'rebuilt_theories': []}))
            return types.SimpleNamespace(returncode=0)

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

    # Unhandled on HEAD: an exception type the handler does not catch.

    @unittest.expectedFailure
    def test_timeout_at_the_final_judgment_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final=TIMEOUT))

    @unittest.expectedFailure
    def test_interrupt_at_the_final_judgment_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final=KeyboardInterrupt()))

    @unittest.expectedFailure
    def test_interrupt_during_the_check_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(check=KeyboardInterrupt()))

    @unittest.expectedFailure
    def test_uncaught_type_in_the_final_checks_is_withdrawn(self):
        self.assertWithdrawn(self.adopt(final={**ACCEPTED, 'summary': {'counts': None, 'published': True}}))

    @unittest.expectedFailure
    def test_timeout_at_the_first_judgment_writes_a_receipt(self):
        self.assertWithdrawn(self.adopt(before=TIMEOUT))

    # Unhandled on HEAD: caught, but raised inside install() after its first write, before `original` is known.

    @unittest.expectedFailure
    def test_failure_writing_the_layer_after_the_theory_is_withdrawn(self):
        layer, write_text = self.layer, Path.write_text

        def failing(path, *args, **options):
            if path == layer:
                raise OSError('injected OSError writing the layer')
            return write_text(path, *args, **options)
        self.assertWithdrawn(self.adopt(patches=[mock.patch.object(Path, 'write_text', failing)]))

    @unittest.expectedFailure
    def test_failure_hashing_the_installed_files_is_withdrawn(self):
        theories, file_hash = self.project / 'theories', development_adoption.investigate.file_hash

        def failing(path):
            if Path(path).parent == theories:
                raise OSError('injected OSError hashing the installed files')
            return file_hash(path)
        self.assertWithdrawn(self.adopt(patches=[mock.patch.object(development_adoption.investigate, 'file_hash',
                                                                   failing)]))


if __name__ == '__main__':
    unittest.main()
