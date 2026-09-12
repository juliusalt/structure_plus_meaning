"""Read complete tagged JSON reports and retain a compact reproduction boundary."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

TAG = re.compile(r"[A-Z][A-Z_0-9]*")
INDEX = re.compile(r"[0-9]+")


def unique_object(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError("Repeated report field: " + key)
        value[key] = item
    return value


def reports(path):
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))
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
            value = json.loads(body, object_pairs_hook=unique_object)
            yield {"tag": tag, "indices": indices, "value": value}


def boundary(path):
    """Hash every complete report in order, including duplicates and every field."""
    checksum = hashlib.sha256()
    counts = Counter()
    for record in reports(path):
        counts[record["tag"]] += 1
        encoded = json.dumps(record, sort_keys=True, separators=(",", ":"), allow_nan=False)
        checksum.update(encoded.encode("utf-8") + b"\n")
    return {"records": sum(counts.values()), "tags": dict(sorted(counts.items())),
            "sha256": checksum.hexdigest()}
