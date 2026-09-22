import json
from pathlib import Path
import shutil
import subprocess
import sys
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

    def test_the_published_state_is_never_judged_against_itself(self):
        state = development_answer.STATES['refinement_layer']
        name = development_answer.answer_name(ANSWER)
        text = development_answer.verification_theory('development_demanded', state, 'Theory_Name.constant_name', name)
        self.assertIn('imports Development_Request ' + name + ' Development_Successor Development_Refinement_Repair', text)
        self.assertIn('define_again', text)
        self.assertNotIn('"development_answer_state=development_demanded_state"', text)
        with self.assertRaises(TypeError):
            development_answer.verification_theory('development_demanded', state, 'Theory_Name.constant_name')

    def test_verification_publishes_the_admitted_answer(self):
        state = development_answer.STATES['refinement_layer']
        text = development_answer.verification_theory('development_demanded', state, 'Theory_Name.constant_name',
                                                      development_answer.answer_name(ANSWER))
        self.assertIn('Development_Refinement_Repair Development_Admitted_Publication\nbegin', text)
        self.assertIn('development_admitted_publication\n    development_demanded_state r development_answer_state '
                      'development_answer_introduced_positions', text)
        self.assertIn('export_code development_answer_verdict_value development_answer_publication_value', text)
        self.assertIn('development_answer_published P', text)

    def test_parts_are_read_as_strings_in_the_frame(self):
        state = development_answer.STATES['development_seed']
        injected = {**ANSWER, 'definitions': '  ML \\<open>val _ = ()\\<close>\n', 'proof': '  by simp\n\n'}
        text = development_answer.parts_theory(state, injected)
        self.assertTrue(text.startswith('theory Development_Answer_Parts_Check\n  imports Native_Control_Seed_Subject '
                                        'Development_Answer_Parts\nbegin\n'))
        definitions, equation, proof = development_answer.placed_parts(injected)
        self.assertEqual(definitions, 'ML \\<open>val _ = ()\\<close>')
        self.assertEqual(proof, '  by simp')
        for part in (definitions, equation, proof):
            self.assertIn(development_answer.investigate.ml_string(part), text)
        self.assertNotIn('ML \\<open>val', text)
        framed = development_answer.answer_theory(state, injected)
        self.assertIn(definitions + '\n\ndeclare [[code drop:', framed)
        self.assertIn('"' + equation + '"\n' + proof + '\n\nend\n', framed)

    def test_refusal_is_read_from_isabelle_logs(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'build.log'
            log.write_text("*** The answer's definitions part is refused: the command ML is not a declared part\n*** At")
            self.assertEqual(development_answer.parts_refusal(Path(directory) / 'missing.log', Path(directory)),
                             "The answer's definitions part is refused: the command ML is not a declared part")

    def test_malformed_answers_are_refused_before_any_build(self):
        with tempfile.TemporaryDirectory() as directory:
            for broken in [{**ANSWER, 'extra': ''},
                           {**ANSWER, 'request': {'state': 'other', 'subject': 'Theory_Name.constant_name'}},
                           {**ANSWER, 'request': {'state': 'development_seed', 'subject': 'unqualified'}}]:
                path = Path(directory) / 'answer.json'
                path.write_text(json.dumps(broken))
                with self.assertRaises(AssertionError):
                    development_answer.validate(json.loads(path.read_text()))



class AdoptionTest(unittest.TestCase):
    # Adoption is a relation between an answer, the content Isabelle accepted and the published state, established
    # by its evidence and never by a file name (task 263, after P1 of task 253: a file that is not a theory, and the
    # judged frame left behind by an unsuccessful adoption, were read as adopted).
    RECORDS = development_answer.ROOT / 'validation' / 'development-answers'
    JUDGMENT = {'verdict_word', 'publication_word', 'accepted', 'summary', 'refusal'}

    def answer(self, record):
        return json.loads((self.RECORDS / (record + '.json')).read_text())['answer']

    def project(self, directory, answer, text, keep=False):
        """A project holding the repository's ROOT, layer boundary and receipts and one file of the answer's name;
        unless kept, neither ROOT nor the boundary names the answer's theory."""
        project = Path(directory)
        (project / 'theories').mkdir()
        shutil.copytree(development_answer.ROOT / development_answer.ADOPTIONS, project / development_answer.ADOPTIONS)
        layer = development_answer.STATES['refinement_layer']['layer'] + '.thy'
        name = development_answer.answer_name(answer)
        for source, target in ((development_answer.ROOT / 'ROOT', project / 'ROOT'),
                               (development_answer.ROOT / 'theories' / layer, project / 'theories' / layer)):
            content = source.read_text()
            target.write_text(content if keep else content.replace('    ' + name + '\n', '').replace(' ' + name + ' ', ' '))
        (project / 'theories' / (name + '.thy')).write_text(text)
        return project

    def failed(self, evidence):
        return {key for key, connection in evidence['connections'].items() if not connection['holds']}

    def test_an_unimported_invalid_theory_of_the_expected_name_is_not_adoption(self):
        answer = self.answer('failed-proof')
        name = development_answer.answer_name(answer)
        with tempfile.TemporaryDirectory() as directory:
            project = self.project(directory, answer, 'theory ' + name + '\n  imports No_Such_Theory\nbegin\nnot a theory\nend\n')
            evidence = development_answer.adoption_evidence(answer, project)
            self.assertTrue(evidence['present'])
            self.assertFalse(evidence['holds'])
            # failed-proof answers the seed state, which has no adoption boundary: that connection fails as well.
            self.assertEqual(self.failed(evidence), {'state', 'receipt', 'installed', 'declared', 'imported'})
            self.assertEqual(evidence['obstruction'], ['state', 'receipt', 'installed', 'declared', 'imported'])

    def test_a_judged_frame_left_unimported_is_not_adoption(self):
        answer = self.answer('demanded-identity')
        frame = development_answer.answer_theory(development_answer.STATES['refinement_layer'], answer)
        with tempfile.TemporaryDirectory() as directory:
            evidence = development_answer.adoption_evidence(answer, self.project(directory, answer, frame))
            self.assertFalse(evidence['holds'])
            self.assertEqual(self.failed(evidence), {'receipt', 'installed', 'declared', 'imported'})

    def test_the_adopted_walk_holds_every_connection(self):
        answer = self.answer('indexed-data-walk')
        evidence = development_answer.adoption_evidence(answer)
        self.assertTrue(evidence['present'])
        self.assertTrue(evidence['holds'])
        self.assertEqual(evidence['obstruction'], [])
        self.assertTrue(all(connection['holds'] for connection in evidence['connections'].values()))
        self.assertEqual(evidence['connections']['receipt']['bound'], ['Development_Answer_0ccf746fe2cf.json'])
        self.assertEqual(evidence['connections']['installed']['present_sha256'],
                         '9102596f55e2ea2c5af2fed3f9cd3ed4be02b05a3ca81778aa1a71ae03169ea2')
        self.assertEqual(evidence['unverified'], development_answer.UNVERIFIED)

    def test_a_file_of_the_walks_name_with_other_content_is_obstructed(self):
        answer = self.answer('indexed-data-walk')
        text = (development_answer.ROOT / 'theories' / (development_answer.answer_name(answer) + '.thy')).read_text()
        with tempfile.TemporaryDirectory() as directory:
            project = self.project(directory, answer, text + '\n', keep=True)
            evidence = development_answer.adoption_evidence(answer, project)
            self.assertEqual(self.failed(evidence), {'installed'})

    def test_a_seed_state_file_is_never_adoption(self):
        answer = {**ANSWER, 'request': {'state': 'development_seed', 'subject': 'Theory_Name.constant_name'}}
        with tempfile.TemporaryDirectory() as directory:
            project = self.project(directory, answer, development_answer.answer_theory(
                development_answer.STATES['development_seed'], answer), keep=True)
            evidence = development_answer.adoption_evidence(answer, project)
            self.assertIn('state', self.failed(evidence))
            self.assertFalse(evidence['holds'])

    def test_a_supplied_receipt_is_checked_as_a_found_one(self):
        answer = self.answer('indexed-data-walk')
        receipts = development_answer.adoption_receipts()
        walk = receipts['Development_Answer_0ccf746fe2cf.json']
        self.assertTrue(development_answer.adoption_evidence(answer, receipt=walk)['holds'])
        self.assertFalse(development_answer.adoption_evidence(answer, receipt={**walk, 'withdrawn': True})['holds'])
        control = self.answer('demanded-reformulated')
        self.assertIn('receipt', development_answer.adoption_evidence(control)['obstruction'])

    def test_an_adoption_report_carries_no_judgment(self):
        for record in ('indexed-data-walk', 'failed-proof'):
            answer = self.answer(record)
            report = development_answer.adoption_report(answer, development_answer.adoption_evidence(answer), '/base')
            self.assertFalse(self.JUDGMENT & set(report))
            self.assertEqual(report['unverified'], development_answer.UNVERIFIED)
        self.assertEqual(report['status'], 'obstructed')
        self.assertEqual(report['obstruction'], report['evidence']['obstruction'])

    def test_the_harness_reports_the_adopted_walk_without_a_judgment(self):
        with tempfile.TemporaryDirectory() as directory:
            answer = Path(directory) / 'answer.json'
            answer.write_text(json.dumps(self.answer('indexed-data-walk')))
            completed = subprocess.run([sys.executable, '-B', str(development_answer.ROOT / 'tools' / 'development_answer.py'),
                                        'answer', '--answer', str(answer), '--output', str(Path(directory) / 'run')],
                                       capture_output=True, text=True, timeout=60)
            self.assertEqual(completed.returncode, 0, completed.stderr)
            report = json.loads((Path(directory) / 'run' / 'answer.json').read_text())
            self.assertEqual(report['status'], 'adopted')
            self.assertFalse(self.JUDGMENT & set(report))
            self.assertFalse((Path(directory) / 'run' / 'project').exists())


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
