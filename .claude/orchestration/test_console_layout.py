"""The actual layout script renders the new part/role data; no HTTP server or model is needed."""
from pathlib import Path
import shutil
import subprocess
import unittest

HERE=Path(__file__).resolve().parent


class LayoutTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('node'),'Node is needed for the actual JavaScript renderer')
    def test_named_parts_and_role_placement_render_without_invented_reasoning_size(self):
        result=subprocess.run(['node',str(HERE/'notes/console-dom-check.js')],capture_output=True,text=True,timeout=20)
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertIn('passed',result.stdout)
