import unittest

import check_presented_report
import development_executor
import native_answers as na


ENTITY = {'code_equation': {'application': [{'application': [{'constant': [0, {'application': [1, []]}]},
                                                               {'free': [2, {'variable': [3, 4, [5]]}]}]},
                                              {'abstraction': [{'free': [6, []]}, {'bound': 0}]}]}}
ANSWER = {'request': {'state': 'development_seed', 'subject': 'Theory_Name.constant_name'},
          'names': ['Pure.eq', 'HOL.bool', 'x', 'a', 'HOL.type', 'b', 'c'], 'removed': [ENTITY], 'added': [ENTITY]}


class TransportTest(unittest.TestCase):
    def test_answer_round_trips_through_its_octets(self):
        octets = na.answer_octets(ANSWER)
        read = na.answer_json(na.octets_term(octets))
        self.assertEqual(read, {k: ANSWER[k] for k in ('names', 'removed', 'added')})

    def test_word_is_the_shared_word_of_a_target_free_term(self):
        term = na.answer_term(ANSWER)
        word = na.shared_word(term)
        self.assertEqual(word[:1], [False])
        self.assertEqual(na.shared_word_term(word), term)

    def test_bits_that_present_no_answer_are_refused(self):
        octets = na.answer_octets(ANSWER)
        with self.assertRaises(na.Refused):
            na.octets_term(octets[:-1])
        with self.assertRaises(na.Refused):
            na.octets_term(bytes(len(octets)))
        with self.assertRaises(na.Refused):
            na.shared_word_term(na.shared_word(na.answer_term(ANSWER)) + [True])

    def test_malformed_answers_are_refused_before_encoding(self):
        with self.assertRaises(AssertionError):
            na.answer_term({**ANSWER, 'extra': 1})
        with self.assertRaises(AssertionError):
            na.answer_term({**ANSWER, 'names': ['\u00e9']})
        with self.assertRaises(AssertionError):
            na.answer_term({**ANSWER, 'added': [{'axiom': ENTITY['code_equation']}]})

    def test_packet_is_read_back_and_answered_by_the_executor(self):
        packet = {'names': ANSWER['names'], 'constant': {'constant': [2, {'application': [1, []]}]},
                  'support': [0, 1, 4], 'context': [ENTITY], 'incumbent': [ENTITY]}
        term = na.data_list([na.pair(na.data_list([na.name(n) for n in packet['names']]),
                             na.pair(na.term_term(packet['constant']),
                                     na.pair(na.data_list([na.position(p) for p in packet['support']]),
                                             na.pair(na.data_list([na.entity_term(e) for e in packet['context']]),
                                                     na.data_list([na.entity_term(e) for e in packet['incumbent']])))))])
        read = na.packet_json(na.octets_term(na.packed(na.shared_word(term))))
        self.assertEqual(read, packet)
        self.assertIsNone(na.packet_json(na.octets_term(na.packed(na.shared_word(na.data_list([]))))))
        answer = development_executor.restating_native_answer({'request': ANSWER['request'], 'packet': read})
        self.assertEqual(answer, {'request': ANSWER['request'], 'names': packet['names'],
                                  'removed': packet['incumbent'], 'added': packet['incumbent']})

    def test_report_value_takes_a_subject_and_the_bits_of_a_file(self):
        inputs = {'module': 'Native_Development_Seed', 'report': 'development_seed_native_judgment_value',
                  'scope': None, 'selections': None, 'subject': 'Theory_Name.constant_name', 'bits': '/tmp/answer.octets'}
        text = check_presented_report.program('/tmp/engine.ML', inputs, '/tmp/report.word')
        self.assertIn('N.development_seed_native_judgment_value "', text)
        self.assertIn('(file_bits "', text)
        self.assertIn('fun file_bits path', text)
        scoped = dict(inputs, report='development_seed_verification_value', scope='development_seed_unanswered',
                      subject=None, bits=None)
        self.assertIn('(N.development_seed_verification_value N.development_seed_unanswered)',
                      check_presented_report.program('/tmp/engine.ML', scoped, '/tmp/report.word'))


if __name__ == '__main__':
    unittest.main()
