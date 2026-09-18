import json
from pathlib import Path
import tempfile
import unittest

import development_answer


ANSWER = {'request': {'state': 'development_seed', 'subject': 'Theory_Name.constant_name'},
          'definitions': 'definition helper where "helper=True"',
          'equation': 'constant_name x=helper', 'proof': '  by simp'}


class FrameTest(unittest.TestCase):
    def test_answer_is_placed_in_the_fixed_frame(self):
        text = development_answer.answer_theory(development_answer.STATES['development_seed'], ANSWER)
        self.assertTrue(text.startswith('theory Development_Answer\n  imports Native_Control_Seed_Subject\nbegin\n'))
        self.assertIn('definition helper where "helper=True"', text)
        self.assertIn('declare [[code drop: Theory_Name.constant_name]]', text)
        self.assertIn('lemma development_answer [code]:\n  "constant_name x=helper"\n  by simp', text)
        self.assertTrue(text.endswith('\nend\n'))

    def test_verification_reads_the_requested_state_and_subject(self):
        state = development_answer.STATES['development_seed']
        text = development_answer.verification_theory('development_seed', state, 'Theory_Name.constant_name')
        self.assertIn('imports Development_Answer Development_Seed_Verification Development_Refinement_Repair', text)
        self.assertIn('@{thm development_seed_roots_def}, @{thm development_seed_context_def}', text)
        self.assertIn("STR ''Theory_Name.constant_name''", text)
        self.assertIn('module_name Development_Answer_Verification', text)

    def test_malformed_answers_are_refused_before_any_build(self):
        with tempfile.TemporaryDirectory() as directory:
            for broken in [{**ANSWER, 'extra': ''},
                           {**ANSWER, 'request': {'state': 'other', 'subject': 'Theory_Name.constant_name'}},
                           {**ANSWER, 'request': {'state': 'development_seed', 'subject': 'unqualified'}}]:
                path = Path(directory) / 'answer.json'
                path.write_text(json.dumps(broken))
                with self.assertRaises(AssertionError):
                    development_answer.validate(json.loads(path.read_text()))



class ExecutorTest(unittest.TestCase):
    def test_restating_answer_reads_only_the_packet(self):
        import development_executor
        packet = {'request': {'state': 'development_seed', 'subject': 'Theory_Name.constant_name'},
                  'statement': 'constant_name x \\<equiv> True', 'support': [], 'context': [],
                  'facts': ['development_demanded_code'],
                  'answer': {'fields': ['request', 'definitions', 'equation', 'proof']}}
        answer = development_executor.restating_answer(packet)
        self.assertEqual(development_answer.validate(answer), answer)
        self.assertEqual(answer['equation'], packet['statement'])
        self.assertIn('development_demanded_code', answer['proof'])



class PacketFrameTest(unittest.TestCase):
    def test_packet_theory_presents_the_named_request(self):
        state = development_answer.STATES['development_seed']
        text = development_answer.packet_theory('development_seed', state, 'Theory_Name.constant_name')
        self.assertIn('imports Native_Control_Seed_Subject Development_Seed_Verification Development_Request_Packets', text)
        self.assertIn("development_named_request development_seed_context (development_seed_requests "
                      "development_seed_unanswered) STR ''Theory_Name.constant_name''", text)
        self.assertIn('Development_Request_Packets.export_packet', text)

    def test_demanded_request_theory_exports_one_subject_from_the_layer(self):
        state = development_answer.STATES['refinement_layer']
        text = development_answer.request_theory(state, 'Theory_Name.constant_name')
        self.assertTrue(text.startswith('theory Development_Request\n  imports Native_Execution_Refinements'))
        self.assertIn('[("_subject", [\\<^term>\\<open>Theory_Name.constant_name\\<close>])]', text)
        self.assertIn('development_demanded_loop_state', text)


if __name__ == '__main__':
    unittest.main()
