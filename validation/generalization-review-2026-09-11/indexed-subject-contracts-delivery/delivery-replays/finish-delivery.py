"""Retain completed replay evidence without changing its bound archive index."""
from pathlib import Path
import hashlib
import json
import shutil
import sys

root = Path('/home/julius/structure_and_semantics')
b = Path(__file__).parent
archive = root/'validation/generalization-review-2026-09-11/indexed-subject-contracts-delivery'
sys.path.insert(0, str(root/'tools'))
import build
import check
import evidence_io
import investigate

digest = investigate.file_hash
index_digest = digest(archive/'index.json')
manifest = json.loads((archive/'archive.json').read_text())
results = [json.loads((b/'delivery-replays1'/stage/'replay.json').read_text())
           for stage in ['initial', 'followed']]
assert all(r['status'] == 'accepted' and r['archive_index_sha256'] == index_digest for r in results)
target = archive/'delivery-replays'
assert not target.exists()
shutil.copytree(b/'delivery-replays1', target)
for stage in ['initial', 'followed']:
    shutil.copyfile(b/('delivery-replay-'+stage+'.log'), target/(stage+'.log'))
shutil.copyfile(Path(__file__), target/'finish-delivery.py')
for p in target.rglob('*'):
    if p.is_file():
        manifest['files'][str(p.relative_to(archive))] = digest(p)
summary = {'archive_index_sha256': index_digest, 'replays': results,
           'boundary': 'Both original repair investigations reproduce all complete outputs and original independent assessments. Replaying them does not rerun native mathematical-proof checking or establish arbitrary host computation semantics.'}
(archive/'replay-checks.json').write_text(json.dumps(summary, indent=2)+'\n')
manifest['files']['replay-checks.json'] = digest(archive/'replay-checks.json')
with (archive/'README.md').open('a') as output:
    output.write('\nBoth retained proof-repair investigations also replay successfully. Their complete\nresults and original independent assessments reproduce exactly; the replay\nreceipts bind the unchanged archive index. See [replay checks](replay-checks.json).\n')
manifest['files']['README.md'] = digest(archive/'README.md')
assert digest(archive/'index.json') == index_digest
for name, sha in manifest['files'].items():
    assert digest(archive/name) == sha, name
for name, encoding in manifest.get('encodings', {}).items():
    evidence_io.unpack(archive/name, encoding)
(archive/'archive.json').write_text(json.dumps(manifest, indent=2)+'\n')
receipt=json.loads((root/'validation/build.json').read_text())
checked=json.loads((root/'validation/check.json').read_text())
assert receipt['status']==checked['status']=='accepted'
assert checked['build_evidence']==receipt and checked['invocation']==receipt['invocation']
assert receipt['sources']==build.source_hashes() and receipt['tools']==build.tool_hashes()
assert digest(root/'validation/build.log')==receipt['log_sha256']
assert check.source_checks()['theory_count']==827
print(json.dumps({'replays':2, 'verified_files':len(manifest['files']),
                  'verified_encodings':len(manifest.get('encodings',{})),
                  'unchanged_index_sha256':index_digest, 'current_build_invocation':receipt['invocation']},indent=2))
