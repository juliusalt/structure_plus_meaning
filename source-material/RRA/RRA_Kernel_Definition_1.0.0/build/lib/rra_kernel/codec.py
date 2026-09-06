"""Canonical JSON profile for exact records and record references."""

from __future__ import annotations

import hashlib
import json
from typing import Any, Iterable

from .artifact import ExactRecord, RecordRef
from .core import FormationError, Structure
from .data import BagData, FunctionalData, NodeData, NoData, Object

RECORD_PROFILE = "rra-record-json-1"


class CodecError(ValueError):
    """Malformed, unsupported, or noncanonical external input."""


def _hex(value: bytes) -> str:
    return value.hex()


def _unhex(value: Any, field: str) -> bytes:
    if not isinstance(value, str):
        raise CodecError(f"{field} must be a hexadecimal string")
    if value != value.lower() or len(value) % 2 or any(c not in "0123456789abcdef" for c in value):
        raise CodecError(f"{field} must be lowercase even-length hexadecimal")
    return bytes.fromhex(value)


def _keys(obj: Any, expected: set[str], field: str) -> dict[str, Any]:
    if not isinstance(obj, dict) or set(obj) != expected:
        raise CodecError(f"{field} must have exactly the fields {sorted(expected)!r}")
    return obj


def _strict_sorted_unique(values: list[Any], field: str) -> None:
    if values != sorted(values):
        raise CodecError(f"{field} must be sorted")
    try:
        unique = len(set(values)) == len(values)
    except TypeError:
        unique = len({json.dumps(v, sort_keys=True, separators=(",", ":")) for v in values}) == len(values)
    if not unique:
        raise CodecError(f"{field} must not contain duplicates")


def canonical_json_bytes(value: Any) -> bytes:
    try:
        text = json.dumps(
            value,
            ensure_ascii=True,
            allow_nan=False,
            sort_keys=True,
            separators=(",", ":"),
        )
    except (TypeError, ValueError) as exc:
        raise CodecError(str(exc)) from exc
    return text.encode("utf-8")


def record_to_value(record: ExactRecord) -> dict[str, Any]:
    obj = record.object
    positions = sorted(_hex(a) for a in obj.structure.positions)
    incidence = sorted([_hex(r), _hex(p), _hex(x)] for r, p, x in obj.structure.incidence)
    data = obj.data
    if isinstance(data, NoData):
        encoded_data: dict[str, Any] = {"kind": "none"}
    elif isinstance(data, BagData):
        entries = sorted(
            ({"owner": _hex(e.owner), "value": _hex(e.value), "count": e.count} for e in data.entries),
            key=lambda e: (e["owner"], e["value"], e["count"]),
        )
        encoded_data = {"kind": "bag", "entries": entries}
    elif isinstance(data, FunctionalData):
        entries = sorted(
            ({"owner": _hex(e.owner), "value": _hex(e.value)} for e in data.entries),
            key=lambda e: (e["owner"], e["value"]),
        )
        encoded_data = {"kind": "functional", "entries": entries}
    elif isinstance(data, NodeData):
        entries = sorted(
            ({"node": _hex(e.node), "owner": _hex(e.owner), "value": _hex(e.value)} for e in data.entries),
            key=lambda e: (e["node"], e["owner"], e["value"]),
        )
        encoded_data = {"kind": "node", "entries": entries}
    else:  # pragma: no cover - Object formation excludes this case
        raise CodecError("unknown data profile")
    return {
        "format": RECORD_PROFILE,
        "positions": positions,
        "incidence": incidence,
        "data": encoded_data,
    }


def encode_record(record: ExactRecord) -> bytes:
    return canonical_json_bytes(record_to_value(record))


def _parse_data(value: Any):
    if not isinstance(value, dict) or "kind" not in value or not isinstance(value["kind"], str):
        raise CodecError("data must contain a string kind")
    kind = value["kind"]
    if kind == "none":
        _keys(value, {"kind"}, "data")
        return NoData()
    _keys(value, {"kind", "entries"}, "data")
    entries = value["entries"]
    if not isinstance(entries, list):
        raise CodecError("data.entries must be an array")
    if kind == "bag":
        normalized: list[tuple[str, str, int]] = []
        parsed = []
        for i, raw in enumerate(entries):
            e = _keys(raw, {"owner", "value", "count"}, f"data.entries[{i}]")
            count = e["count"]
            if isinstance(count, bool) or not isinstance(count, int) or count <= 0:
                raise CodecError("bag count must be a positive integer")
            normalized.append((e["owner"], e["value"], count))
            parsed.append((_unhex(e["owner"], "owner"), _unhex(e["value"], "value"), count))
        _strict_sorted_unique(normalized, "bag entries")
        return BagData(parsed)
    if kind == "functional":
        normalized = []
        parsed = []
        for i, raw in enumerate(entries):
            e = _keys(raw, {"owner", "value"}, f"data.entries[{i}]")
            normalized.append((e["owner"], e["value"]))
            parsed.append((_unhex(e["owner"], "owner"), _unhex(e["value"], "value")))
        _strict_sorted_unique(normalized, "functional entries")
        return FunctionalData(parsed)
    if kind == "node":
        normalized = []
        parsed = []
        for i, raw in enumerate(entries):
            e = _keys(raw, {"node", "owner", "value"}, f"data.entries[{i}]")
            normalized.append((e["node"], e["owner"], e["value"]))
            parsed.append(
                (
                    _unhex(e["node"], "node"),
                    _unhex(e["owner"], "owner"),
                    _unhex(e["value"], "value"),
                )
            )
        _strict_sorted_unique(normalized, "node entries")
        return NodeData(parsed)
    raise CodecError(f"unsupported data kind: {kind!r}")


def record_from_value(value: Any) -> ExactRecord:
    obj = _keys(value, {"format", "positions", "incidence", "data"}, "record")
    if obj["format"] != RECORD_PROFILE:
        raise CodecError(f"unsupported record format: {obj['format']!r}")
    pos_raw = obj["positions"]
    if not isinstance(pos_raw, list) or not all(isinstance(x, str) for x in pos_raw):
        raise CodecError("positions must be an array of hexadecimal strings")
    _strict_sorted_unique(pos_raw, "positions")
    positions = [_unhex(x, "position") for x in pos_raw]

    inc_raw = obj["incidence"]
    if not isinstance(inc_raw, list):
        raise CodecError("incidence must be an array")
    normalized: list[tuple[str, str, str]] = []
    incidence = []
    for i, row in enumerate(inc_raw):
        if not isinstance(row, list) or len(row) != 3 or not all(isinstance(x, str) for x in row):
            raise CodecError(f"incidence[{i}] must be a three-address array")
        normalized.append((row[0], row[1], row[2]))
        incidence.append(tuple(_unhex(x, f"incidence[{i}]") for x in row))
    _strict_sorted_unique(normalized, "incidence")
    try:
        return ExactRecord(Object(Structure(positions, incidence), _parse_data(obj["data"])))
    except FormationError as exc:
        raise CodecError(str(exc)) from exc


def _load_json(raw: bytes) -> Any:
    if not isinstance(raw, bytes):
        raise CodecError("canonical input must be bytes")

    def no_duplicates(pairs: Iterable[tuple[str, Any]]) -> dict[str, Any]:
        out: dict[str, Any] = {}
        for key, value in pairs:
            if key in out:
                raise CodecError(f"duplicate object key: {key!r}")
            out[key] = value
        return out

    try:
        text = raw.decode("utf-8")
        return json.loads(
            text,
            object_pairs_hook=no_duplicates,
            parse_constant=lambda token: (_ for _ in ()).throw(CodecError(f"invalid number: {token}")),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CodecError(str(exc)) from exc


def decode_record(raw: bytes, *, require_canonical: bool = True) -> ExactRecord:
    record = record_from_value(_load_json(raw))
    if require_canonical and encode_record(record) != raw:
        raise CodecError("record input is not the canonical encoding")
    return record


def reference_for_record(record: ExactRecord) -> RecordRef:
    return RecordRef(RECORD_PROFILE, "sha256", hashlib.sha256(encode_record(record)).digest())


def reference_to_value(reference: RecordRef) -> dict[str, str]:
    return {
        "profile": reference.profile,
        "algorithm": reference.algorithm,
        "digest": reference.digest.hex(),
    }


def reference_from_value(value: Any) -> RecordRef:
    obj = _keys(value, {"profile", "algorithm", "digest"}, "reference")
    if not all(isinstance(obj[k], str) for k in obj):
        raise CodecError("reference fields must be strings")
    return RecordRef(obj["profile"], obj["algorithm"], _unhex(obj["digest"], "digest"))


def validate_record_bytes(raw: bytes, *, require_canonical: bool = True) -> bool:
    try:
        decode_record(raw, require_canonical=require_canonical)
        return True
    except (CodecError, FormationError, TypeError, ValueError):
        return False
