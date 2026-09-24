"""A replay's groups are decided by its rows: an unproduced run is not a differing word."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

import replay_development_answers as replay


def row(produced=True, reconstructed=True, status='judged'):
    """One answer's row, in the three fields the classification reads."""
    return {'produced': produced, 'reconstructed': reconstructed, 'status': status if produced else None}


NONE = {'adopted': [], 'obstructed': [], 'differing': [], 'unproduced': []}


class AnswerGroups(unittest.TestCase):
    """Produced and unproduced runs crossed with reconstructed, differing, adopted and obstructed answers."""

    def test_a_produced_reconstruction_falls_into_no_group(self):
        self.assertEqual(replay.answer_groups({'reconstructed-answer': row()}), NONE)

    def test_a_compared_word_that_differs_is_a_re_evaluation(self):
        groups = replay.answer_groups({'changed-answer': row(reconstructed=False)})
        self.assertEqual(groups['differing'], ['changed-answer'])
        self.assertEqual(groups['unproduced'], [])

    def test_a_run_that_left_no_judgment_is_unproduced_and_not_differing(self):
        groups = replay.answer_groups({'timed-out-answer': row(produced=False, reconstructed=False)})
        self.assertEqual(groups['unproduced'], ['timed-out-answer'])
        self.assertEqual(groups['differing'], [])

    def test_a_judged_build_failure_is_reconstructed_and_not_unproduced(self):
        # The retained `failed-proof` record parts the two notions: the harness judged that this
        # answer's build failed, so the row's own status is `failed` while its run produced that
        # judgment and its words were compared and reconstructed.
        self.assertEqual(replay.answer_groups({'failed-proof': row(status='failed')}), NONE)

    def test_an_adopted_answer_is_counted_in_no_comparison_group_and_passes(self):
        groups = replay.answer_groups({'indexed-data-walk': row(reconstructed=False, status='adopted')})
        self.assertEqual(groups, {**NONE, 'adopted': ['indexed-data-walk']})
        self.assertEqual(replay.replay_exit(groups, []), 0)

    def test_an_obstructed_answer_is_its_own_group_and_fails_the_replay(self):
        groups = replay.answer_groups({'failed-proof': row(reconstructed=False, status='obstructed')})
        self.assertEqual(groups, {**NONE, 'obstructed': ['failed-proof']})
        self.assertEqual(replay.replay_exit(groups, []), 1)

    def test_a_run_that_left_no_judgment_is_unproduced_whatever_was_expected(self):
        groups = replay.answer_groups({'indexed-data-walk': row(produced=False, reconstructed=False)})
        self.assertEqual(groups, {**NONE, 'unproduced': ['indexed-data-walk']})
        self.assertEqual(replay.replay_exit(groups, []), 1)

    def test_an_unrecorded_adoption_fails_the_replay(self):
        self.assertEqual(replay.replay_exit(NONE, ['Development_Answer_x.json']), 1)
        self.assertEqual(replay.replay_exit(NONE, []), 0)

    def test_every_retained_adoption_has_its_answers_record(self):
        self.assertEqual(replay.unrecorded_adoptions(), [])
        with tempfile.TemporaryDirectory() as temporary:
            self.assertEqual(replay.unrecorded_adoptions(Path(temporary)), ['Development_Answer_0ccf746fe2cf.json'])

    def test_the_groups_are_sorted_and_every_answer_is_accounted_for(self):
        groups = replay.answer_groups({'b-differs': row(reconstructed=False), 'a-differs': row(reconstructed=False),
                                       'c-unproduced': row(produced=False, reconstructed=False),
                                       'd-reconstructed': row()})
        self.assertEqual(groups['differing'], ['a-differs', 'b-differs'])
        self.assertEqual(groups['unproduced'], ['c-unproduced'])


class ReplayOrder(unittest.TestCase):
    """The longest answers are started first, and a record that kept no seconds is started last."""

    def test_records_are_ordered_longest_first_and_the_seconds_less_kept_their_order(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            for name, kept in [('a-unknown', {}), ('b-short', {'elapsed_seconds': 4.5}),
                               ('c-unknown', {}), ('d-long', {'elapsed_seconds': 90})]:
                (directory / (name + '.json')).write_text(json.dumps({'status': 'judged', **kept}))
            ordered = replay.replay_order(sorted(directory.glob('*.json')))
            self.assertEqual([path.stem for path in ordered],
                             ['d-long', 'b-short', 'a-unknown', 'c-unknown'])


class UnproducedRuns(unittest.TestCase):
    """A harness run that leaves no judgment is returned, never raised at the pool that replays."""

    def test_a_run_that_outlives_its_limit_leaves_its_answer_unproduced(self):
        with tempfile.TemporaryDirectory() as temporary:
            elapsed, produced, left = replay.run_harness(
                [sys.executable, '-c', 'import sys, time; print("progress", flush=True); '
                 'print("warning", file=sys.stderr, flush=True); time.sleep(30)'], Path(temporary), 0.5)
            self.assertFalse(produced)
            self.assertIn('0.5s limit', left)
            self.assertIn('progress', left)
            self.assertIn('warning', left)
            self.assertLess(elapsed, 30)

    def test_an_unproduced_row_carries_no_harness_status(self):
        # A run that left no judgment is not the harness judging that a build failed, as failed-proof is.
        observation = replay.unproduced_observation('the harness run left no judgment')
        self.assertIsNone(observation['status'])
        self.assertNotEqual(observation['status'], json.loads(
            (replay.RECORDS / 'failed-proof.json').read_text())['status'])
        self.assertEqual(observation['error'], 'the harness run left no judgment')

    def replayed(self, record, observed, rerecord, words=None):
        """Replay one record through a harness that leaves `observed` and retains it as judged now."""
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            path = directory / 'records' / 'answer.json'
            path.parent.mkdir()
            path.write_text(json.dumps(record))
            commands = []

            def harness(command, run, timeout):
                commands.append(command)
                (run / 'run').mkdir()
                (run / 'run' / 'answer.json').write_text(json.dumps(observed))
                (run / 'retained.json').write_text(json.dumps({**observed, 'harness_sha256': 'now'}))
                return 1.0, True, ''
            original = replay.run_harness
            replay.run_harness = harness
            try:
                name, row = replay.replay(path, directory / 'out', 10, rerecord, directory / 'parts.json',
                                          directory / 'proof.json')
            finally:
                replay.run_harness = original
            return row, json.loads(path.read_text()), commands[0]

    def test_a_rerecorded_row_is_reconstructed_against_the_word_it_wrote(self):
        record = {'answer': {'request': {}}, 'status': 'judged', 'verdict_word': 'old', 'publication_word': 'p',
                  'executor_sha256': 'kept'}
        row, written, command = self.replayed(record, {'status': 'judged', 'verdict_word': 'new', 'publication_word': 'p'},
                                              True)
        self.assertTrue(row['reconstructed'])
        self.assertEqual((row['verdict_word'], row['expected_verdict_word']), ('new', 'new'))
        self.assertEqual(row['replaced']['verdict_word'], 'old')
        self.assertEqual((written['verdict_word'], written['executor_sha256']), ('new', 'kept'))
        self.assertEqual(command[-4:], ['--parts', command[-3], '--proof', command[-1]])
        self.assertEqual(replay.answer_groups({'answer': row}), NONE)

    def test_a_parts_reading_that_could_not_be_read_is_unproduced_and_not_failed(self):
        record = {'answer': {'request': {}}, 'status': 'refused', 'refusal': 'r'}
        row, written, command = self.replayed(record, {'status': 'failed', 'judgment': False,
                                                       'error': "The answer's parts could not be read."}, True)
        self.assertFalse(row['produced'])
        self.assertIsNone(row['status'])
        self.assertEqual(row['error'], "The answer's parts could not be read.")
        self.assertEqual(written, record)
        self.assertEqual(replay.answer_groups({'answer': row}), {**NONE, 'unproduced': ['answer']})

    def test_without_rerecording_a_changed_word_still_differs(self):
        record = {'answer': {'request': {}}, 'status': 'judged', 'verdict_word': 'old', 'publication_word': 'p'}
        row, written, command = self.replayed(record, {'status': 'judged', 'verdict_word': 'new', 'publication_word': 'p'},
                                              False)
        self.assertFalse(row['reconstructed'])
        self.assertNotIn('replaced', row)
        self.assertEqual(written, record)
        self.assertEqual(replay.answer_groups({'answer': row})['differing'], ['answer'])

    def test_a_status_change_is_never_rerecorded(self):
        record = {'answer': {'request': {}}, 'status': 'judged', 'verdict_word': 'old', 'publication_word': 'p'}
        row, written, command = self.replayed(record, {'status': 'refused', 'refusal': 'r'}, True)
        self.assertFalse(row['reconstructed'])
        self.assertEqual(written, record)

    def test_an_answer_whose_shared_reading_wrote_no_outcome_reads_its_own_parts(self):
        answers = {stem: {'request': {'state': 'development_seed', 'subject': 'Theory_Name.c_' + stem},
                          'definitions': '', 'equation': 'c_' + stem + ' = True', 'proof': 'by simp'}
                   for stem in ('accepted', 'refused', 'silent')}
        outcomes = {'accepted': (0, None), 'refused': (1, "The answer's proof part is refused: r"),
                    'silent': (1, None)}
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            records = []
            for stem, answer in answers.items():
                records.append(directory / (stem + '.json'))
                records[-1].write_text(json.dumps({'answer': answer, 'status': 'judged'}))

            def read_parts(read, base, output, timeout):
                output.mkdir(parents=True)
                digests = {replay.development_answer.answer_digest(a): stem for stem, a in answers.items()}
                return {digest: {'answer_digest': digest, 'base': str(base), 'exit_code': outcomes[stem][0],
                                 'refusal': outcomes[stem][1], 'seconds': 1.0, 'answers_read': 3, 'log': 'l'}
                        for digest, stem in digests.items()}
            original = replay.development_answer.read_parts
            replay.development_answer.read_parts = read_parts
            try:
                paths, seconds = replay.read_shared_parts(records, directory, directory / 'out', 10)
            finally:
                replay.development_answer.read_parts = original
            self.assertEqual(sorted(paths), ['accepted', 'refused'])
            self.assertEqual(json.loads(paths['refused'].read_text())['refusal'], outcomes['refused'][1])

    def shared_proofs(self, accepted):
        """Records of seeded and layer answers, their parts readings, and a session that is accepted or not."""
        def answer(stem, state, subject):
            return {'request': {'state': state, 'subject': subject}, 'definitions': '',
                    'equation': 'c_' + stem.replace('-', '_') + ' = True', 'proof': 'by simp'}
        cases = {'seed-a': ('development_seed', 'T.s', 'judged', 0), 'seed-b': ('development_seed', 'T.s', 'judged', 0),
                 'seed-failed': ('development_seed', 'T.s', 'failed', 0),
                 'seed-refused': ('development_seed', 'T.s', 'refused', 1),
                 'layer-x1': ('refinement_layer', 'T.x', 'judged', 0), 'layer-x2': ('refinement_layer', 'T.x', 'judged', 0),
                 'layer-y': ('refinement_layer', 'T.y', 'judged', 0)}
        calls = []
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            records, parts = [], {}
            for stem, (state, subject, status, code) in cases.items():
                records.append(directory / (stem + '.json'))
                records[-1].write_text(json.dumps({'answer': answer(stem, state, subject), 'status': status}))
                parts[stem] = directory / (stem + '-parts.json')
                parts[stem].write_text(json.dumps({'exit_code': code}))

            def prove_answers(answers, base, output, timeout):
                calls.append(sorted(a['equation'] for a in answers))
                output.mkdir(parents=True)
                return {replay.development_answer.answer_digest(a): {'exit_code': 0 if accepted else 1, 'session': 's'}
                        for a in answers}
            original = replay.development_answer.prove_answers
            replay.development_answer.prove_answers = prove_answers
            try:
                paths, report, kept = replay.read_shared_proofs(records, parts, directory, directory / 'out', 10)
            finally:
                replay.development_answer.prove_answers = original
            return calls, sorted(paths), report, kept

    def test_answers_of_one_request_theory_share_a_proof_session(self):
        calls, paths, report, kept = self.shared_proofs(True)
        # The seeded answers join the first layer subject's session; the other subject has one answer, so no
        # session; the answers retained failed or refused at their parts are proved alone.
        self.assertEqual(calls, [['c_layer_x1 = True', 'c_layer_x2 = True', 'c_seed_a = True', 'c_seed_b = True']])
        self.assertEqual(paths, ['layer-x1', 'layer-x2', 'seed-a', 'seed-b'])
        self.assertEqual([(session['answers'], session['accepted']) for session in report],
                         [(['layer-x1', 'layer-x2', 'seed-a', 'seed-b'], True)])
        self.assertEqual(kept, ['s'])

    def test_a_proof_session_not_accepted_leaves_every_answer_to_prove_itself(self):
        calls, paths, report, kept = self.shared_proofs(False)
        self.assertEqual(len(calls), 1)
        self.assertEqual((paths, kept), ([], []))
        self.assertEqual([session['accepted'] for session in report], [False])

    def test_a_harness_that_cannot_be_started_leaves_its_answer_unproduced(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            elapsed, produced, left = replay.run_harness([str(directory / 'no-such-harness')], directory, 5)
            self.assertFalse(produced)
            self.assertIn('left no judgment', left)


if __name__ == '__main__':
    unittest.main()
