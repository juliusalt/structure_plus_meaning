"""Retain report indices, complete fields, order and repeated occurrences."""
from pathlib import Path
import tempfile
import unittest

import machine_reports


class MachineReportTests(unittest.TestCase):
    def test_complete_records_keep_indices_order_and_duplicates(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "results.log"
            first = 'GUIDED_STATE 3 2 {"known":[],"unused":{"field":[1,2]}}\n'
            second = 'INPUT_RESULT {"formed":false}\n'
            path.write_text("compiler diagnostic\n" + first + second + first)
            records = list(machine_reports.reports(path))
            self.assertEqual(len(records), 3)
            self.assertEqual(records[0]["indices"], [3, 2])
            self.assertEqual(records[1]["indices"], [])
            self.assertEqual(records[0], records[2])
            self.assertEqual(records[0]["value"]["unused"], {"field": [1, 2]})
            original = machine_reports.boundary(path)
            self.assertEqual(original["records"], 3)
            for text in [first + second, second + first + first,
                         (first + second + first).replace('[1,2]', '[1,3]', 1)]:
                path.write_text(text)
                self.assertNotEqual(machine_reports.boundary(path)["sha256"], original["sha256"])

    def test_repeated_json_fields_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "results.log"
            path.write_text('INPUT_RESULT 0 {"formed":true,"formed":false}\n')
            with self.assertRaisesRegex(ValueError, "Repeated report field"):
                machine_reports.boundary(path)


if __name__ == "__main__":
    unittest.main()
