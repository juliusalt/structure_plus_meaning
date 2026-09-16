"""Read complete tagged JSON reports and retain a compact reproduction boundary."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

import native_artifact_stream

TAG = re.compile(r"[A-Z][A-Z_0-9]*")
INDEX = re.compile(r"[0-9]+")


def unique_object(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError("Repeated report field: " + key)
        value[key] = item
    return value


class DeferredRecord:
    """Explicit access to a complete record whose native references remain shared."""
    def __init__(self, row, decoder):
        self.row = row
        self.decoder = decoder
        self.materialized = None

    def __getitem__(self, key):
        if key != 'value':
            return self.row[key]
        if self.materialized is None:
            self.materialized = self.decoder.expand(self.row['value'])
        return self.materialized

    def field(self, *path):
        if self.materialized is not None:
            value = self.materialized
            for key in path:
                value = value[key]
            return value
        return self.decoder.expand(self.decoder.field(self.row['value'], path))

    def value_keys(self, *path):
        return set(self.decoder.field(self.row['value'], path))

    def update_digest(self, digest):
        if self.materialized is not None:
            value = {**self.row, 'value': self.materialized}
            digest.update(json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode('utf-8'))
        else:
            for part in self.decoder.canonical_chunks(self.row):
                digest.update(part)
        digest.update(b'\n')


def canonical_update(digest, row):
    if isinstance(row, DeferredRecord):
        row.update_digest(digest)
    else:
        digest.update(json.dumps(row, sort_keys=True, separators=(',', ':'), allow_nan=False).encode('utf-8'))
        digest.update(b'\n')


def field(row, *path):
    if isinstance(row, DeferredRecord):
        return row.field(*path)
    value = row['value']
    for key in path:
        value = value[key]
    return value


def value_keys(row, *path):
    if isinstance(row, DeferredRecord):
        return row.value_keys(*path)
    return set(field(row, *path))


def _parts(row, path):
    if isinstance(row, DeferredRecord) and row.materialized is None:
        value = row.row if path is None else row.decoder.field(row.row['value'], path, resolve_final=False)
        return row.decoder.canonical_chunks(value)
    value = ({**row.row, 'value': row['value']} if isinstance(row, DeferredRecord) else row)
    if path is not None:
        value = value['value']
        for key in path:
            value = value[key]
    return iter([json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode('utf-8')])


def _same_bytes(left, right):
    left, right = iter(left), iter(right)
    a = b = b''
    ai = bi = 0
    while True:
        while a is not None and ai == len(a):
            a = next(left, None)
            ai = 0
        while b is not None and bi == len(b):
            b = next(right, None)
            bi = 0
        if a is None or b is None:
            return a is None and b is None
        size = min(len(a) - ai, len(b) - bi)
        if a[ai:ai + size] != b[bi:bi + size]:
            return False
        ai += size
        bi += size


def record_equal(left, right):
    return left is not None and right is not None and _same_bytes(_parts(left, None), _parts(right, None))


def field_equal(left, left_path, right, right_path):
    return _same_bytes(_parts(left, left_path), _parts(right, right_path))


def reports(path, *, deferred=False):
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))
    decoder = native_artifact_stream.Decoder()
    pending = []
    tables = {}
    with Path(path).open() as source:
        for line in source:
            tag, separator, body = line.rstrip("\r\n").partition(" ")
            if not separator or not TAG.fullmatch(tag):
                continue
            indices = []
            while True:
                first, separator, rest = body.partition(" ")
                if not separator or not rest.strip() or not INDEX.fullmatch(first):
                    break
                indices.append(int(first))
                body = rest
            if decoder.version == 3 and not decoder.finished:
                if tag in [native_artifact_stream.ARTIFACT_TABLE, native_artifact_stream.TERM_TABLE]:
                    if indices or tag in tables:
                        raise ValueError('Repeated or indexed native dictionary table.')
                    tables[tag] = json.loads(body, object_pairs_hook=unique_object)
                elif tag == native_artifact_stream.END:
                    if set(tables) != {native_artifact_stream.ARTIFACT_TABLE, native_artifact_stream.TERM_TABLE}:
                        raise ValueError('Missing complete native dictionary table.')
                    decoder.load_tables(tables[native_artifact_stream.ARTIFACT_TABLE], tables[native_artifact_stream.TERM_TABLE])
                    for i, (old_tag, old_indices, old_body) in enumerate(pending):
                        hook = lambda pairs: decoder.validate_object(unique_object(pairs))
                        value = json.loads(old_body, object_pairs_hook=hook)
                        row = decoder.read({'tag': old_tag, 'indices': old_indices, 'value': value}, expanded=True)
                        if row is None:
                            raise ValueError('Unexpected metadata inside a native report sequence.')
                        pending[i] = row
                    decoder.read({'tag': tag, 'indices': indices, 'value': json.loads(body, object_pairs_hook=unique_object)})
                    tables.clear()
                    for row in pending:
                        yield DeferredRecord(row, decoder) if deferred else {**row, 'value': decoder.expand(row['value'])}
                    pending.clear()
                elif tag in [native_artifact_stream.BEGIN, native_artifact_stream.ENTRY, native_artifact_stream.TERM_ENTRY]:
                    raise ValueError('Mixed native dictionary protocols.')
                else:
                    if tables:
                        raise ValueError('Logical record after native dictionary tables.')
                    pending.append((tag, indices, body))
                continue
            expand = decoder.active and tag not in [native_artifact_stream.BEGIN,
                native_artifact_stream.ENTRY, native_artifact_stream.END]
            postpone = deferred and expand and tag != native_artifact_stream.TERM_ENTRY
            operation = decoder.validate_object if postpone else decoder.object
            hook = (lambda pairs: operation(unique_object(pairs))) if expand else unique_object
            value = json.loads(body, object_pairs_hook=hook)
            row = decoder.read({"tag": tag, "indices": indices, "value": value}, expanded=expand)
            if row is not None:
                yield DeferredRecord(row, decoder) if postpone else row
    decoder.finish()


def boundary(path):
    """Hash every complete report in order, including duplicates and every field."""
    checksum = hashlib.sha256()
    counts = Counter()
    for record in reports(path, deferred=True):
        counts[record["tag"]] += 1
        canonical_update(checksum, record)
    return {"records": sum(counts.values()), "tags": dict(sorted(counts.items())),
            "sha256": checksum.hexdigest()}
