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
        name = development_answer.answer_name(ANSWER)
        text = development_answer.answer_theory(development_answer.STATES['development_seed'], ANSWER)
        self.assertTrue(text.startswith('theory ' + name + '\n  imports Native_Control_Seed_Subject\nbegin\n'))
        self.assertIn('Isabelle_Constant_Closure.note_code_equations', text)
        self.assertIn('definition helper where "helper=True"', text)
        self.assertIn('declare [[code drop: Theory_Name.constant_name]]', text)
        self.assertIn('lemma development_answer [code]:\n  "constant_name x=helper"\n  by simp', text)
        self.assertTrue(text.endswith('\nend\n'))

    def test_answer_name_is_its_canonical_content(self):
        name = development_answer.answer_name(ANSWER)
        self.assertRegex(name, r'^Development_Answer_[0-9a-f]{12}$')
        reordered = json.loads(json.dumps(dict(reversed(list(ANSWER.items())))))
        self.assertEqual(development_answer.answer_name(reordered), name)
        self.assertNotEqual(development_answer.answer_name({**ANSWER, 'proof': '  by auto'}), name)

    def test_layer_answer_is_framed_where_it_is_adopted(self):
        state = development_answer.STATES['refinement_layer']
        layer = (development_answer.ROOT / 'theories' / (state['layer'] + '.thy')).read_text()
        imports = development_answer.investigate.theory_imports(layer, state['layer'])
        answer = {**ANSWER, 'request': {'state': 'refinement_layer', 'subject': 'Theory_Name.constant_name'}}
        text = development_answer.answer_theory(state, answer)
        self.assertIn('  imports ' + ' '.join(imports) + ' Isabelle_Constant_Closure\nbegin\n', text)
        self.assertNotIn('Development_Request', text.split('begin')[0])

    def test_verification_reads_the_requested_state_and_subject(self):
        state = development_answer.STATES['development_seed']
        name = development_answer.answer_name(ANSWER)
        text = development_answer.verification_theory('development_seed', state, 'Theory_Name.constant_name', name)
        self.assertIn('imports Native_Control_Seed_Subject ' + name + ' Development_Seed_Verification '
                      'Development_Refinement_Repair', text)
        self.assertIn('@{thm development_seed_roots_def}, @{thm development_seed_context_def}', text)
        self.assertIn('\\<^theory>\\<open>' + name + '\\<close>', text)
        self.assertIn("STR ''Theory_Name.constant_name''", text)
        self.assertIn('module_name Development_Answer_Verification', text)

    def test_adopted_answer_is_judged_as_the_published_state(self):
        state = development_answer.STATES['refinement_layer']
        text = development_answer.verification_theory('development_demanded', state, 'Theory_Name.constant_name')
        self.assertIn('imports Development_Request Development_Successor Development_Refinement_Repair', text)
        self.assertIn('"development_answer_state=development_demanded_state"', text)
        self.assertIn('"development_answer_introduced_positions=[]"', text)
        self.assertNotIn('define_again', text)

    def test_verification_publishes_the_admitted_answer(self):
        state = development_answer.STATES['refinement_layer']
        text = development_answer.verification_theory('development_demanded', state, 'Theory_Name.constant_name')
        self.assertIn('Development_Refinement_Repair Development_Admitted_Publication\nbegin', text)
        self.assertIn('development_admitted_publication\n    development_demanded_state r development_answer_state '
                      'development_answer_introduced_positions', text)
        self.assertIn('export_code development_answer_verdict_value development_answer_publication_value', text)
        self.assertIn('development_answer_published P', text)

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
                  'constant': {'name': 'Theory_Name.constant_name', 'type': "'a \\<Rightarrow> bool"},
                  'support': [], 'context': [{'kind': 'definition', 'text': 'constant_name \\<equiv> \\<lambda>x. True'},
                                             {'kind': 'code equation', 'text': 'constant_name x \\<equiv> True'}],
                  'facts': ['development_demanded_code'],
                  'answer': {'fields': ['request', 'definitions', 'equation', 'proof']}}
        answer = development_executor.restating_answer(packet)
        self.assertEqual(development_answer.validate(answer), answer)
        self.assertEqual(answer['equation'], 'constant_name x \\<equiv> True')
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
