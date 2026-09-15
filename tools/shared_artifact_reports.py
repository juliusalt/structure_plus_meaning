"""Validate and expand complete artifacts retained by native exact references."""
from collections import Counter
import hashlib

import compressed_machine_reports
import native_packet_sequence

REFERENCE = '__artifact_ref__'
ARTIFACT_FIELDS = {'carrier', 'incidence', 'counted_data', 'functional_data'}


def _word(value):
    assert isinstance(value, list)
    assert all(type(n) is int and n >= 0 for n in value)


def _artifact(value):
    assert isinstance(value, dict) and set(value) == ARTIFACT_FIELDS
    assert all(isinstance(value[name], list) for name in ARTIFACT_FIELDS)
    for address in value['carrier']:
        _word(address)
    for name, width in [('incidence', 3), ('counted_data', 2), ('functional_data', 2)]:
        for row in value[name]:
            assert isinstance(row, list) and len(row) == width
            for word in row:
                _word(word)


def read_transport(path, prefix):
    iterator = compressed_machine_reports.reports(path)
    try:
        records = list(iterator)
    finally:
        iterator.close()
    assert records, 'Missing complete native records and artifact table.'
    footer = records.pop()
    assert footer['tag'] == prefix + '_ARTIFACTS' and footer['indices'] == []
    table = footer['value']
    assert isinstance(table, list)
    for artifact in table:
        _artifact(artifact)
    referenced, occurrences = set(), 0

    def inspect(value):
        nonlocal occurrences
        if isinstance(value, dict):
            if REFERENCE in value:
                assert set(value) == {REFERENCE}, 'Ambiguous artifact reference.'
                index = value[REFERENCE]
                assert type(index) is int and 0 <= index < len(table), 'Invalid artifact reference.'
                referenced.add(index)
                occurrences += 1
            else:
                for field in value.values():
                    inspect(field)
        elif isinstance(value, list):
            for field in value:
                inspect(field)

    for row in records:
        assert row['tag'] != prefix + '_ARTIFACTS', 'Repeated artifact table.'
        inspect(row['value'])
    assert referenced == set(range(len(table))), 'An artifact table row has no emitted occurrence.'
    checksum, counts = hashlib.sha256(), Counter()
    for row in [*records, footer]:
        compressed_machine_reports.canonical_update(checksum, row)
        counts[row['tag']] += 1
    return records, table, {
        'codec': 'complete-artifact-references-v1', 'native_reports': len(records),
        'artifact_rows': len(table), 'artifact_occurrences': occurrences,
        'all_references_in_range': True, 'every_table_row_referenced': True,
        'reproduction_boundary': {'records': len(records) + 1,
                                 'tags': dict(sorted(counts.items())), 'sha256': checksum.hexdigest()}}


def expanded_reports(path, prefix):
    records, table, _ = read_transport(path, prefix)

    def expand(value):
        if isinstance(value, dict):
            if REFERENCE in value:
                return table[value[REFERENCE]]
            return {key: expand(field) for key, field in value.items()}
        if isinstance(value, list):
            return [expand(field) for field in value]
        return value

    for row in records:
        yield {**row, 'value': expand(row['value'])}


def assess(inputs, path, *, prefix, introductory=()):
    records, _, transport = read_transport(path, prefix)
    packet = native_packet_sequence.assess_records(inputs, records, prefix=prefix, introductory=introductory)
    return {**packet, 'stored_body_boundary': packet['reproduction_boundary'],
            'reproduction_boundary': transport['reproduction_boundary'], 'artifact_transport': transport,
            'boundary': 'Every original native record remains in its declared position. Each artifact '
                        'occurrence refers to complete ordered carrier, incidence, counted-data and '
                        'functional-data rows. Native exact-reference and preservation theorems '
                        'justify recovery of every occurrence. The checksum covers the compact '
                        'stored records and complete table; it is not an expanded-result checksum.'}
