"""The existing complete packet-order check, factored over a record iterator."""
from collections import Counter
import hashlib

import compressed_machine_reports


def assess_records(inputs, records, *, prefix, introductory=()):
    iterator = iter(records)
    counts, checksum = Counter(), hashlib.sha256()

    def take(suffix, indices):
        tag = prefix + '_' + suffix
        row = next(iterator)
        assert row['tag'] == tag and row['indices'] == indices
        compressed_machine_reports.canonical_update(checksum, row)
        counts[tag] += 1
        return row['value']

    try:
        scope = take('SCOPE', [])
        requested = scope if inputs['cases'] is None else inputs['cases']
        assert set(requested) <= set(scope)
        for tag in introductory:
            take(tag, [])
        for w in requested:
            take('CONTEXT', [w])
            for m in inputs['candidates']:
                take('CANDIDATE', [w, m])
        for w in requested:
            take('ASSESSMENT', [w])
        assert take('COMPARISON', [])['scope'] == requested
        for selection in inputs['selections']:
            assert take('INVESTIGATION', [])['selected'] == selection
        assert take('SOURCE_SCOPE', []) == requested
        for w in requested:
            take('SOURCE', [w])
        assert next(iterator, None) is None
    finally:
        close = getattr(iterator, 'close', None)
        if close:
            close()
    return {'complete_scope': scope, 'executed_scope': requested, 'original_source_scope': requested,
            'reproduction_boundary': {'records': sum(counts.values()), 'tags': dict(sorted(counts.items())),
                                      'sha256': checksum.hexdigest()},
            'boundary': 'Every complete native context, candidate, assessment, comparison, revision and '
                        'original source occupies its declared position. This is presentation checking.'}
