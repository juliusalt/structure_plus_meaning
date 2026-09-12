"""Known-call validation keeps the complete call and its evidence boundary."""
import unittest
from pathlib import Path
import check_reasoning as reasoning
from reasoning_known_calls import KnownCallContract


def exact_example(entry, term):
    return entry == 28 and term == {'payload': [7]}


def non_boolean(entry, term):
    return 'true'


class KnownCallTests(unittest.TestCase):
    def test_default_binding_contract_retains_its_scope(self):
        term = reasoning.pair(reasoning.payload(50), reasoning.pair(reasoning.payload(), reasoning.payload()))
        contract = KnownCallContract(reasoning.binding_call_true, 'existing complete binding observation')
        self.assertEqual(contract.validate([[345, term]]), 1)
        with self.assertRaisesRegex(AssertionError, 'declared condition'):
            contract.validate([[28, term]])

    def test_custom_condition_checks_both_entry_and_entire_term(self):
        contract = KnownCallContract(exact_example, 'exact supplied example')
        self.assertEqual(contract.validate([[28, {'payload': [7]}]]), 1)
        for call in [[29, {'payload': [7]}], [28, {'payload': [7, 8]}]]:
            with self.assertRaisesRegex(AssertionError, 'declared condition'):
                contract.validate([call])

    def test_truthy_values_do_not_establish_a_condition(self):
        with self.assertRaisesRegex(ValueError, 'Boolean'):
            KnownCallContract(non_boolean, 'must be Boolean').validate([[28, {'payload': [7]}]])

    def test_actual_operation_and_declared_evidence_are_retained(self):
        source = Path(__file__).resolve()
        contract = KnownCallContract(exact_example, 'exact supplied example', (source,))
        self.assertIn(source, contract.inputs())
        self.assertEqual(contract.record()['operation'], exact_example.__qualname__)
        with self.assertRaisesRegex(ValueError, 'exist'):
            KnownCallContract(exact_example, 'missing evidence', (source / 'absent',)).inputs()


if __name__ == '__main__':
    unittest.main()
