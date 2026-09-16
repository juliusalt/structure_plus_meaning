"""Validate the complete record order of a native context and candidate packet."""
from collections import Counter
import hashlib

import compressed_machine_reports


def assess(inputs, path, *, prefix, introductory=()):
    # Deferred records hash each shared dictionary value through its retained exact encoding.
    iterator = iter(compressed_machine_reports.reports(path, deferred=True))
    counts = Counter()
    checksum = hashlib.sha256()

    def take(suffix, indices):
        tag = prefix + '_' + suffix
        row = next(iterator)
        assert row['tag'] == tag and row['indices'] == indices
        compressed_machine_reports.canonical_update(checksum, row)
        counts[tag] += 1
        return row

    scope = take('SCOPE', [])['value']
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
    assert take('COMPARISON', [])['value']['scope'] == requested
    for selection in inputs['selections']:
        assert take('INVESTIGATION', [])['value']['selected'] == selection
    assert take('SOURCE_SCOPE', [])['value'] == requested
    for w in requested:
        take('SOURCE', [w])
    assert next(iterator, None) is None
    return {'complete_scope': scope, 'executed_scope': requested, 'original_source_scope': requested,
            'reproduction_boundary': {'records': sum(counts.values()), 'tags': dict(sorted(counts.items())),
                                      'sha256': checksum.hexdigest()},
            'boundary': 'Every complete native context, candidate, assessment, comparison, revision and '
                        'original source is parsed in its declared position. No record or field is '
                        'filtered. Presentation checking adds no semantic observation or decision.'}
