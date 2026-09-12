"""Lossless evidence blobs with distinct stored and decoded identities."""
from __future__ import annotations

import gzip
import hashlib
import json
import os
import tempfile
from pathlib import Path

CHUNK = 1024 * 1024
PACK_THRESHOLD = 32 * CHUNK


def write_json(path, value):
    """Stream complete JSON without depth padding and publish it only after success."""
    path = Path(path)
    fd, temporary = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(value, stream, separators=(",", ":"), allow_nan=False)
            stream.write("\n")
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def digest(path):
    checksum = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(CHUNK), b""):
            checksum.update(block)
    return checksum.hexdigest()


def pack(source, destination, expected):
    checksum, size = hashlib.sha256(), 0
    with Path(source).open("rb") as original, Path(destination).open("wb") as output:
        with gzip.GzipFile(filename="", mode="wb", fileobj=output, mtime=0) as encoded:
            for block in iter(lambda: original.read(CHUNK), b""):
                checksum.update(block)
                size += len(block)
                encoded.write(block)
    assert checksum.hexdigest() == expected, "Evidence changed while being packed."
    encoding = {"codec": "gzip", "sha256": expected, "size": size}
    unpack(destination, encoding)
    return encoding


def unpack(source, encoding, destination=None):
    assert encoding["codec"] == "gzip"
    assert type(encoding["size"]) is int and encoding["size"] >= 0
    checksum, size = hashlib.sha256(), 0
    output = Path(destination).open("wb") if destination is not None else None
    try:
        with gzip.open(source, "rb") as stream:
            for block in iter(lambda: stream.read(CHUNK), b""):
                size += len(block)
                assert size <= encoding["size"], "Decoded evidence exceeds its recorded size."
                checksum.update(block)
                if output is not None:
                    output.write(block)
        assert size == encoding["size"] and checksum.hexdigest() == encoding["sha256"], \
            "Decoded evidence differs from its recorded bytes."
    finally:
        if output is not None:
            output.close()


def decoded_view(base, manifest, references, output):
    """Materialize only selected references; plain archives need no new view."""
    encodings = manifest.get("encodings", {})
    if not encodings:
        return base
    references = set(references) | {"index.json"}
    assert references <= manifest["files"].keys()
    ascent = 0
    for reference in references:
        assert not Path(reference).is_absolute()
        depth = 0
        for part in Path(reference).parts:
            depth += -1 if part == ".." else 1
            ascent = max(ascent, -depth)
    root = Path(output).resolve() / "decoded-evidence"
    view = root.joinpath(*(["anchor"] * (ascent + 1)))
    view.mkdir(parents=True)
    for reference in references:
        source = (base / reference).resolve()
        target = (view / reference).resolve()
        assert target.is_relative_to(root)
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            expected = encodings.get(reference, {}).get("sha256", manifest["files"][reference])
            assert digest(target) == expected
        elif reference in encodings:
            unpack(source, encodings[reference], target)
        else:
            target.symlink_to(source)
    return view
