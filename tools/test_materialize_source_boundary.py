"""A source boundary copies only verified inputs and rejects invalid paths before writing."""
import json
from pathlib import Path
import tempfile
import unittest

from evidence_io import digest
from materialize_source_boundary import materialize


class SourceBoundaryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="source-boundary-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.project = self.root / "project"
        self.project.mkdir()
        (self.project / "source.thy").write_text("exact source bytes\n")
        (self.project / "generated.log").write_text("excluded generated output\n")
        self.manifest = self.root / "boundary.json"
        self.output = self.root / "restored"

    def specify(self, files):
        self.manifest.write_text(json.dumps({"version": 1, "files": files}))

    def test_only_declared_sources_are_copied_and_existing_output_is_preserved(self):
        source = self.project / "source.thy"
        self.specify({"source.thy": digest(source)})
        materialize(self.project, self.manifest, self.output)
        self.assertEqual((self.output / "source.thy").read_bytes(), source.read_bytes())
        self.assertFalse((self.output / "generated.log").exists())
        with self.assertRaises(AssertionError):
            materialize(self.project, self.manifest, self.output)
        self.assertEqual((self.output / "source.thy").read_bytes(), source.read_bytes())

    def test_changed_source_and_escaping_paths_fail_before_output_creation(self):
        source = self.project / "source.thy"
        self.specify({"source.thy": digest(source)})
        source.write_text("changed source\n")
        with self.assertRaises(AssertionError):
            materialize(self.project, self.manifest, self.output)
        self.assertFalse(self.output.exists())
        outside = self.root / "outside.thy"
        outside.write_text("outside the declared repository\n")
        (self.project / "alias.thy").symlink_to(outside)
        for name in ["../outside.thy", str(outside), "alias.thy"]:
            with self.subTest(name=name):
                self.specify({name: digest(outside)})
                with self.assertRaises(AssertionError):
                    materialize(self.project, self.manifest, self.output)
                self.assertFalse(self.output.exists())

    def test_duplicate_manifest_fields_are_rejected(self):
        self.manifest.write_text('{"version":1,"files":{},"files":{}}')
        with self.assertRaises(ValueError):
            materialize(self.project, self.manifest, self.output)
        self.assertFalse(self.output.exists())


if __name__ == "__main__":
    unittest.main()
