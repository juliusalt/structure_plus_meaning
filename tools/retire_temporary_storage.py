"""Retire temporary storage after recording what replaces it.

The workflow keeps temporary storage bounded and requires the retained evidence that
replaces a removed copy. This tool decides that mechanically where it can: every file of
a retired path is either byte-identical to a blob reachable in repository history, or it
falls under the path's declared disposition, whose named replacement is itself checked —
retained evidence must be tracked in the repository at the recorded commit, and a
regenerable path must name the command that rebuilds it. A declaration removes nothing on
its own: a path that does not exist, a retired path inside the repository, an untracked
replacement or a missing justification refuses the whole retirement. Kept paths are
recorded with the same justification, so the record states what may still be discarded
and what restores it.
"""
from __future__ import annotations

import argparse
import datetime
import json
from pathlib import Path
import shutil
import subprocess

import execution_support as investigate

ROOT = Path(__file__).resolve().parent.parent
DISPOSITIONS = {'superseded': (), 'evidence_retained': ('retained_evidence',), 'regenerable': ('regenerated_by',)}


def git(*arguments, stdin=None):
    return subprocess.run(['git', *arguments], cwd=ROOT, input=stdin, capture_output=True, text=True, check=True).stdout


def reachable_blobs():
    """Every object reachable from any reference, so a match means the content is in the history."""
    return {line.split(' ', 1)[0] for line in git('rev-list', '--objects', '--all').splitlines()}


def blob_identifiers(paths):
    assert not any('\n' in str(path) for path in paths), 'A path with a newline cannot be hashed by path list.'
    if not paths:
        return []
    return git('hash-object', '--stdin-paths', stdin=''.join(str(path) + '\n' for path in paths)).split()


def tracked(path):
    return subprocess.run(['git', 'ls-files', '--error-unmatch', str(path)],
                          cwd=ROOT, capture_output=True, text=True).returncode == 0


def classify(path, blobs):
    """Summarize a retired path: its repository sources, and what else it holds, by extension."""
    files = sorted(p for p in ([path] if path.is_file() else path.rglob('*')) if p.is_file() and not p.is_symlink())
    identifiers = blob_identifiers(files)
    sources, other = [], {}
    for file, identifier in zip(files, identifiers):
        if identifier in blobs:
            sources.append({'source': str(file), 'git_blob': identifier,
                            'sha256': investigate.file_hash(file), 'reachable_in_repository_history': True})
        else:
            other[file.suffix or file.name] = other.get(file.suffix or file.name, 0) + 1
    return {'path': str(path), 'files': len(files), 'bytes': sum(f.stat().st_size for f in files),
            'directory': path.is_dir(), 'repository_sources': len(sources),
            'other_files_by_extension': dict(sorted(other.items()))}, sources


def check_entry(entry, *, retired):
    path = Path(entry['path'])
    assert path.exists(), 'Declared path is absent: ' + str(path)
    assert ROOT not in path.resolve().parents and path.resolve() != ROOT, \
        'This tool retires temporary storage, not repository content: ' + str(path)
    if not retired:
        assert entry.get('reason'), 'A kept path states why it is kept: ' + str(path)
        return
    required = DISPOSITIONS.get(entry.get('disposition'))
    assert required is not None, 'Unknown disposition for ' + str(path)
    assert entry.get('reason'), 'A retired path states its reason: ' + str(path)
    for field in required:
        assert entry.get(field), 'Disposition %s needs %s: %s' % (entry['disposition'], field, path)
    for evidence in entry.get('retained_evidence', []):
        assert (ROOT / evidence).is_file() and tracked(ROOT / evidence), \
            'Retained evidence is not tracked in the repository: ' + evidence
    return path


def retire(manifest, record, apply):
    head = git('rev-parse', 'HEAD').strip()
    assert manifest['repository_commit'] == head, \
        'The manifest was prepared against %s, HEAD is %s.' % (manifest['repository_commit'], head)
    assert not git('status', '--porcelain', '--untracked-files=no').strip(), \
        'Retirement records reachability; commit the workspace changes first.'
    blobs = reachable_blobs()
    retired, sources = [], []
    for entry in manifest['retired']:
        path = check_entry(entry, retired=True)
        summary, found = classify(path, blobs)
        retired.append(summary | {key: entry[key] for key in entry if key != 'path'})
        sources += found
    for entry in manifest['kept']:
        check_entry(entry, retired=False)
    if apply:
        for summary in retired:
            path = Path(summary['path'])
            shutil.rmtree(path) if path.is_dir() else path.unlink()
    write = {'status': 'complete' if apply else 'reported', 'repository_commit': head,
             'retired': retired, 'kept': manifest['kept'], 'source_checks': sources,
             'boundary': manifest['boundary'],
             'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    record.write_text(json.dumps(write, indent=1, sort_keys=True) + '\n')
    print(json.dumps({'status': write['status'], 'retired': len(retired),
                      'bytes': sum(summary['bytes'] for summary in retired), 'repository_sources': len(sources),
                      'kept': len(manifest['kept']), 'record': str(record)}))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True, help='Declared retired and kept temporary paths.')
    parser.add_argument('--record', type=Path, default=ROOT / 'validation/temporary-cleanup.json')
    parser.add_argument('--apply', action='store_true', help='Remove the retired paths; otherwise only report.')
    args = parser.parse_args()
    if not __debug__:
        raise ValueError('Retirement requires Python assertions.')
    manifest = json.loads(args.manifest.read_text())
    return retire(manifest, args.record, args.apply)


if __name__ == '__main__':
    raise SystemExit(main())
