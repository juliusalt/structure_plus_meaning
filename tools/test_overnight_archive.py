"""Lossless archival and refusal checks for preserved development evidence."""
import gzip
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import overnight_archive as archive


class OvernightArchiveTests(unittest.TestCase):
    def test_packed_roundtrip_with_duplicates_and_git_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = root / 'sources'
            sources.mkdir()
            oid = subprocess.check_output(['git', 'rev-parse',
                'a863e709ff27067485ff6939e2bd6626982bd680:ROOT'], cwd=archive.ROOT, text=True).strip()
            original = archive.git_bytes(oid)
            (sources / 'ROOT').write_bytes(original)
            payload = bytes(range(256)) * 9
            (sources / 'draft.bin').write_bytes(payload)
            (sources / 'duplicate.bin').write_bytes(payload)
            digest = archive.sha(original)
            baseline = {digest: {'git_blob': oid, 'sha256': digest, 'bytes': len(original)}}
            target = root / 'archive'
            with patch.object(archive, 'baseline_blobs', return_value=baseline):
                summary = archive.create(target, {'base_commit': 'test', 'roots': [str(sources)]})
            self.assertEqual((summary['paths'], summary['distinct_blobs'], summary['git_blobs']), (3, 2, 1))
            archive.pack(target)
            # The original paths are unavailable during both verification and extraction.
            for path in sources.iterdir():
                path.unlink()
            sources.rmdir()
            self.assertEqual(archive.verify(target)['paths'], 3)
            restored = root / 'restored'
            archive.extract(target, restored, '')
            location = restored / sources.relative_to('/')
            self.assertEqual((location / 'ROOT').read_bytes(), original)
            self.assertEqual((location / 'draft.bin').read_bytes(), payload)
            self.assertEqual((location / 'duplicate.bin').read_bytes(), payload)
            with self.assertRaises(AssertionError):
                archive.extract(target, restored, '')

    def test_refuses_corrupt_content(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            digest = archive.sha(b'original')
            archive.write_gzip(root / 'blobs' / (digest + '.gz'), b'changed!')
            with self.assertRaises(AssertionError):
                archive.read_blob(root, {'sha256': digest, 'bytes': 8})

    def test_refuses_parent_traversal(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            digest = archive.sha(b'payload')
            archive.write_gzip(root / 'blobs' / (digest + '.gz'), b'payload')
            index = {'files': {'/../escaped': digest},
                     'blobs': {digest: {'sha256': digest, 'bytes': 7}}}
            archive.write_gzip(root / 'index.json.gz', json.dumps(index).encode())
            with self.assertRaises(AssertionError):
                archive.extract(root, root / 'restored', '')
            self.assertFalse((root / 'escaped').exists())


if __name__ == '__main__':
    unittest.main()
