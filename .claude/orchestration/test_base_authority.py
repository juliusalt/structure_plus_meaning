"""Generated priming prompts must not enter the owner's authority channel."""
import unittest
import extract_owner_directions as directions


class AuthorityTests(unittest.TestCase):
    def test_generated_reasoning_and_churn_prompts_are_not_owner_directions(self):
        for name in ('layer-reviewer','churn-implementer','reference-1','max-reasoning','xhigh-reasoning','high-reasoning'):
            with self.subTest(name=name):
                self.assertIsNone(directions.owner_statement(f'You are {name}, the reasoning over the reference.',set(),'session'))
        self.assertEqual(directions.owner_statement('Keep the complete plan in view.',set(),'session'),
                         'Keep the complete plan in view.')
