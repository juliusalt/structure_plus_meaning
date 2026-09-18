"""Preserve historical files by bytes, independently of their original locations.

This is storage, not proof admission. Historical receipts remain unmodified and
are never treated as current accepted contexts. Git supplies unchanged baseline
sources; other distinct bytes are packed once, with independently checked decoding.
"""
from __future__ import annotations

import argparse
from compression import zstd
from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
import json
import io
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
DEFAULT = ROOT / 'validation/overnight-20260918/archive'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git_bytes(oid):
    return subprocess.check_output(['git', 'cat-file', 'blob', oid], cwd=ROOT)


def write_gzip(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('wb') as raw:
        with gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0) as stream:
            stream.write(data)


def load_index(archive):
    with gzip.open(archive / 'index.json.gz', 'rt') as stream:
        return json.load(stream)


def read_blob(archive, record):
    if 'git_blob' in record:
        data = git_bytes(record['git_blob'])
    else:
        digest = record['sha256']
        assert len(digest) == 64 and all(c in '0123456789abcdef' for c in digest)
        data = gzip.decompress((archive / 'blobs' / (digest + '.gz')).read_bytes())
    assert len(data) == record['bytes'] and sha(data) == record['sha256']
    return data


def blob_data(archive, index, wanted=None):
    wanted = set(index['blobs']) if wanted is None else set(wanted)
    git_records = [(d, r) for d, r in index['blobs'].items() if d in wanted and 'git_blob' in r]
    with ThreadPoolExecutor(max_workers=8) as pool:
        for digest, data in pool.map(lambda item: (item[0], read_blob(archive, item[1])), git_records):
            yield digest, data
    pending = wanted - {d for d, _ in git_records}
    packed = archive / 'blobs.tar.zst'
    parts = sorted((archive / 'pack').glob('*.part'))
    if packed.exists() or parts:
        # Bounded chunks keep individual Git objects below hosting size limits.
        source = packed if packed.exists() else io.BytesIO(b''.join(p.read_bytes() for p in parts))
        with zstd.open(source, 'rb', options={zstd.DecompressionParameter.window_log_max: 30}) as stream, \
                tarfile.open(fileobj=stream, mode='r|') as tar:
            for member in tar:
                if member.name not in pending:
                    continue
                assert member.isfile()
                data = tar.extractfile(member).read()
                record = index['blobs'][member.name]
                assert len(data) == record['bytes'] and sha(data) == member.name
                pending.remove(member.name)
                yield member.name, data
        assert not pending, 'Missing packed blobs: ' + str(sorted(pending))
    else:
        for digest in sorted(pending):
            yield digest, read_blob(archive, index['blobs'][digest])


def pack(archive):
    """Share compression across historical receipts as well as exact duplicate files."""
    index = load_index(archive)
    target = archive / 'blobs.tar.zst'
    assert not (archive / 'pack').exists(), 'Archive is already packed.'
    examples = {}
    for name, digest in index['files'].items():
        examples.setdefault(digest, Path(name))
    records = [(d, r) for d, r in index['blobs'].items() if 'git_blob' not in r]
    records.sort(key=lambda item: (examples[item[0]].suffix, examples[item[0]].name, item[0]))
    options = {zstd.CompressionParameter.compression_level: 12,
               zstd.CompressionParameter.window_log: 30,
               zstd.CompressionParameter.enable_long_distance_matching: 1,
               zstd.CompressionParameter.nb_workers: 4}
    if not target.exists():
        with zstd.open(target, 'wb', options=options) as stream, tarfile.open(fileobj=stream, mode='w|') as tar:
            for digest, record in records:
                data = read_blob(archive, record)
                info = tarfile.TarInfo(digest)
                info.size = len(data)
                info.mode = 0o644
                tar.addfile(info, io.BytesIO(data))
    # The newly written pack is independently decoded before redundant storage is removed.
    assert sum(1 for _ in blob_data(archive, index)) == len(index['blobs'])
    (archive / 'pack').mkdir()
    with target.open('rb') as stream:
        part = 0
        for data in iter(lambda: stream.read(32 * 1024 * 1024), b''):
            (archive / 'pack' / ('%03d.part' % part)).write_bytes(data)
            part += 1
    assert sha(target.read_bytes()) == sha(b''.join(p.read_bytes() for p in sorted((archive / 'pack').glob('*.part'))))
    target.unlink()
    shutil.rmtree(archive / 'blobs')
    summary = verify(archive)
    (archive / 'pack-verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    return summary


def baseline_blobs(commit):
    entries = subprocess.check_output(['git', 'ls-tree', '-rz', commit,
        '--', 'theories', 'tools', 'ROOT', '*.md', '*.txt'], cwd=ROOT).split(b'\0')
    objects = {entry.split(b'\t')[0].split()[2].decode() for entry in entries if entry}
    result = {}
    # One cat-file process avoids thousands of process launches.
    with subprocess.Popen(['git', 'cat-file', '--batch'], cwd=ROOT,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as process:
        for oid in sorted(objects):
            process.stdin.write((oid + '\n').encode())
            process.stdin.flush()
            header = process.stdout.readline().split()
            assert header[1] == b'blob'
            data = process.stdout.read(int(header[2]))
            assert process.stdout.read(1) == b'\n'
            result[sha(data)] = {'git_blob': oid, 'sha256': sha(data), 'bytes': len(data)}
        process.stdin.close()
        assert process.wait() == 0
    return result


def create(archive, manifest):
    assert not archive.exists(), 'Use a fresh archive directory.'
    paths = set()
    for name in manifest['roots']:
        root = Path(name).resolve()
        assert root.exists(), root
        paths.update([root] if root.is_file() else (p for p in root.rglob('*') if p.is_file()))
    assert not any(p.is_symlink() for p in paths), 'Symlinks need an explicit disposition.'
    excluded = []
    selected = []
    for path in sorted(paths):
        if '__pycache__' in path.parts or path.suffix == '.pyc':
            excluded.append(str(path))
        else:
            selected.append(path)

    def identify(path):
        before = path.stat()
        data = path.read_bytes()
        after = path.stat()
        assert (before.st_size, before.st_mtime_ns) == (after.st_size, after.st_mtime_ns), path
        return str(path), sha(data), len(data)

    with ThreadPoolExecutor(max_workers=8) as pool:
        rows = list(pool.map(identify, selected))
    baseline = baseline_blobs(manifest['base_commit'])
    blobs, originals = {}, {}
    files = {}
    for name, digest, size in rows:
        files[name] = digest
        blobs[digest] = baseline.get(digest, {'sha256': digest, 'bytes': size})
        originals.setdefault(digest, name)
    archive.mkdir(parents=True)

    def retain(item):
        digest, record = item
        if 'git_blob' in record:
            return
        data = Path(originals[digest]).read_bytes()
        assert sha(data) == digest
        write_gzip(archive / 'blobs' / (digest + '.gz'), data)

    with ThreadPoolExecutor(max_workers=8) as pool:
        list(pool.map(retain, blobs.items()))
    index = {'version': 1, 'base_commit': manifest['base_commit'],
             'boundary': 'Lossless physical storage only; original absolute paths are historical identifiers. '
                         'Restored receipts do not authorize proof-context adoption.',
             'files': files, 'blobs': blobs, 'excluded_rebuildable_python_caches': excluded}
    write_gzip(archive / 'index.json.gz', json.dumps(index, sort_keys=True, separators=(',', ':')).encode())
    (archive / 'capture.json').write_text(json.dumps(manifest, indent=2) + '\n')
    # Verify every original again, after publication, including duplicate paths.
    with ThreadPoolExecutor(max_workers=8) as pool:
        checked = list(pool.map(identify, selected))
    assert rows == checked, 'Original input changed during capture.'
    summary = verify(archive)
    summary['original_paths_unchanged_during_capture'] = True
    (archive / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    return summary


def verify(archive):
    index = load_index(archive)
    assert set(index['files'].values()) <= index['blobs'].keys()
    records = list(index['blobs'].values())
    assert sum(1 for _ in blob_data(archive, index)) == len(records)
    return {'status': 'verified', 'paths': len(index['files']), 'distinct_blobs': len(records),
            'git_blobs': sum('git_blob' in r for r in records),
            'original_bytes': sum(index['blobs'][d]['bytes'] for d in index['files'].values()),
            'distinct_bytes': sum(r['bytes'] for r in records),
            'stored_bytes': sum(p.stat().st_size for p in archive.rglob('*') if p.is_file()),
            'index_sha256': sha((archive / 'index.json.gz').read_bytes())}


def extract(archive, destination, prefix):
    index = load_index(archive)
    assert not destination.exists(), 'Extract only into a fresh directory.'
    destination.mkdir(parents=True)
    count = 0
    selected = {}
    for name, digest in index['files'].items():
        if prefix and not (name == prefix or name.startswith(prefix.rstrip('/') + '/')):
            continue
        selected.setdefault(digest, []).append(name)
    for digest, data in blob_data(archive, index, selected):
        for name in selected[digest]:
            parts = PurePosixPath(name).parts
            assert parts[0] == '/' and '..' not in parts and '.' not in parts
            path = destination.joinpath(*parts[1:])
            assert path.resolve().is_relative_to(destination.resolve())
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            count += 1
    assert count, 'No archived paths matched.'
    return {'status': 'extracted', 'files': count, 'destination': str(destination),
            'boundary': 'Historical file bytes only; absolute receipt locators have not been rewritten or adopted.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, default=DEFAULT)
    sub = parser.add_subparsers(dest='action', required=True)
    capture = sub.add_parser('capture')
    capture.add_argument('--manifest', type=Path, required=True)
    sub.add_parser('verify')
    sub.add_parser('pack')
    restore = sub.add_parser('extract')
    restore.add_argument('--output', type=Path, required=True)
    restore.add_argument('--prefix', default='')
    args = parser.parse_args()
    if not __debug__:
        raise ValueError('Archive verification requires assertions.')
    if args.action == 'capture':
        result = create(args.archive, json.loads(args.manifest.read_text()))
    elif args.action == 'verify':
        result = verify(args.archive)
    elif args.action == 'pack':
        result = pack(args.archive)
    else:
        result = extract(args.archive, args.output.resolve(), args.prefix)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
