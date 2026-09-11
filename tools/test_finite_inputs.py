"""Keep the complete deep source coordinate when preparing independent cases."""
import unittest

import check_reasoning as review
import finite_presentation_cases as values
import check_finite_inference as native


class FiniteInputTests(unittest.TestCase):
    def test_long_source_use_is_copied_completely_and_independently(self):
        natural = review.payload()
        for _ in range(256):
            natural = review.pair(review.payload(), natural)
        original = review.pair(review.sequence([natural]), review.payload())
        cloned = review.clone_json(original)
        self.assertEqual(values.use_value(cloned), [256])
        cloned["pair"][1]["payload"].append(1)
        self.assertEqual(values.use_value(original), [256])
        self.assertEqual(original["pair"][1]["payload"], [])

    def test_source_reference_rejects_foreign_evidence_and_goals(self):
        call = [94, review.payload()]
        goal = [0, 350, review.payload()]
        case = {"name": "reference", "native_source_reference": True,
                "known": [call], "goals": [goal], "native_source_goal_truth": [True]}
        native.validate_reference_cases([case], [call], [goal])
        case["known"] = [[94, review.payload(1)]]
        with self.assertRaises(AssertionError):
            native.validate_reference_cases([case], [call], [goal])
        case["known"] = [call]
        case["goals"] = [[0, 350, review.payload(1)]]
        with self.assertRaises(AssertionError):
            native.validate_reference_cases([case], [call], [goal])

    def test_unformed_report_cannot_count_as_a_settlement(self):
        goal = [0, 350, review.payload()]
        case = {"name": "formed-gate", "goals": [goal],
                "expected_report": {"input_formed": False, "settled_goals": [0]}}
        with self.assertRaises(AssertionError):
            review.check_expected_report(case, {"input_formed": False, "residual": []})
        case["expected_report"] = {"input_formed": True, "settled_goals": [0]}
        review.check_expected_report(case, {"input_formed": True, "residual": []})
        with self.assertRaises(AssertionError):
            review.check_expected_report(case, {"input_formed": True, "residual": [goal]})


if __name__ == "__main__":
    unittest.main()
