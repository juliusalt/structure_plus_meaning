"""Preserve raw identities through packing, prior references and selective replay."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import evidence_io
from retain_reasoning_review import Archive


class EvidenceStorageTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="evidence-storage-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.source = self.root / "original"
        self.source.write_bytes(bytes(range(256)) * 20 + b"\n  retained whitespace\n")
        self.sha = evidence_io.digest(self.source)

    def manifest(self, archive):
        index = archive.output / "index.json"
        index.write_text("{}\n")
        files = archive.stored | {"index.json": evidence_io.digest(index)}
        manifest = {"files": files, "encodings": archive.encodings}
        (archive.output / "archive.json").write_text(json.dumps(manifest))
        return manifest

    def test_packed_roundtrip_and_prior_reference(self):
        with patch.object(evidence_io, "PACK_THRESHOLD", 1):
            first = Archive(self.root / "first", [], [])
            reference = first.add(self.source, self.sha)
        self.assertTrue(reference.endswith(".gz"))
        self.assertNotEqual(first.stored[reference], self.sha)
        self.manifest(first)
        second = Archive(self.root / "second", [first.output], [])
        inherited = second.add(self.root / "missing-original", self.sha)
        manifest = self.manifest(second)
        view = evidence_io.decoded_view(second.output, manifest, [inherited], self.root / "replay")
        self.assertEqual((view / inherited).read_bytes(), self.source.read_bytes())
        self.assertEqual(evidence_io.digest(view / inherited), self.sha)

    def test_stored_and_decoded_corruption_are_rejected(self):
        with patch.object(evidence_io, "PACK_THRESHOLD", 1):
            archive = Archive(self.root / "archive", [], [])
            reference = archive.add(self.source, self.sha)
        self.manifest(archive)
        with self.assertRaises(AssertionError):
            evidence_io.unpack(archive.output / reference,
                               archive.encodings[reference] | {"sha256": "0" * 64})
        (archive.output / reference).write_bytes(b"changed storage")
        with self.assertRaises(AssertionError):
            Archive(self.root / "reject", [archive.output], [])

    def test_unselected_large_blob_is_not_materialized(self):
        other = self.root / "other"
        other.write_bytes(b"another complete value\n" * 400)
        with patch.object(evidence_io, "PACK_THRESHOLD", 1):
            archive = Archive(self.root / "selective", [], [])
            selected = archive.add(self.source)
            omitted = archive.add(other)
        manifest = self.manifest(archive)
        view = evidence_io.decoded_view(archive.output, manifest, [selected], self.root / "selected-replay")
        self.assertEqual((view / selected).read_bytes(), self.source.read_bytes())
        self.assertFalse((view / omitted).exists())

    def test_plain_archive_keeps_existing_references(self):
        archive = Archive(self.root / "plain", [], [])
        reference = archive.add(self.source)
        manifest = self.manifest(archive)
        self.assertEqual(manifest["encodings"], {})
        self.assertEqual(evidence_io.decoded_view(archive.output, manifest, [reference], self.root / "unused"),
                         archive.output)


if __name__ == "__main__":
    unittest.main()
