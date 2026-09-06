"""JSON profile for compact exact assembly witnesses."""

from __future__ import annotations

from typing import Any

from .assembly import ExactAssemblyWitness, ExactPiece, Origin
from .codec import CodecError, _keys, _load_json, _unhex, canonical_json_bytes, record_from_value, record_to_value
from .data import DataKind

ASSEMBLY_PROFILE = "rra-assembly-witness-json-1"


def witness_to_value(witness: ExactAssemblyWitness[bytes]) -> dict[str, Any]:
    pieces = sorted(
        ({"slot": p.slot.hex(), "record": record_to_value(p.record)} for p in witness.pieces),
        key=lambda p: p["slot"],
    )
    origins = sorted(
        (
            {"slot": o.slot.hex(), "source": o.source.hex(), "target": o.target.hex()}
            for o in witness.origins
        ),
        key=lambda o: (o["slot"], o["source"], o["target"]),
    )
    return {
        "format": ASSEMBLY_PROFILE,
        "data_kind": witness.kind.value,
        "pieces": pieces,
        "output": record_to_value(witness.output),
        "origins": origins,
    }


def encode_witness(witness: ExactAssemblyWitness[bytes]) -> bytes:
    return canonical_json_bytes(witness_to_value(witness))


def witness_from_value(value: Any) -> ExactAssemblyWitness[bytes]:
    obj = _keys(value, {"format", "data_kind", "pieces", "output", "origins"}, "assembly witness")
    if obj["format"] != ASSEMBLY_PROFILE:
        raise CodecError(f"unsupported assembly format: {obj['format']!r}")
    try:
        kind = DataKind(obj["data_kind"])
    except (TypeError, ValueError) as exc:
        raise CodecError("invalid data_kind") from exc
    if not isinstance(obj["pieces"], list) or not isinstance(obj["origins"], list):
        raise CodecError("pieces and origins must be arrays")
    pieces = []
    seen_slots: set[bytes] = set()
    for i, raw in enumerate(obj["pieces"]):
        item = _keys(raw, {"slot", "record"}, f"pieces[{i}]")
        slot = _unhex(item["slot"], "slot")
        if slot in seen_slots:
            raise CodecError("piece slots must be unique")
        seen_slots.add(slot)
        pieces.append(ExactPiece(slot, record_from_value(item["record"])))
    origins = []
    seen_sources: set[tuple[bytes, bytes]] = set()
    for i, raw in enumerate(obj["origins"]):
        item = _keys(raw, {"slot", "source", "target"}, f"origins[{i}]")
        origin = Origin(
            _unhex(item["slot"], "slot"),
            _unhex(item["source"], "source"),
            _unhex(item["target"], "target"),
        )
        key = (origin.slot, origin.source)
        if key in seen_sources:
            raise CodecError("origin source coordinates must be unique")
        seen_sources.add(key)
        origins.append(origin)
    return ExactAssemblyWitness(kind, pieces, record_from_value(obj["output"]), origins)


def decode_witness(raw: bytes, *, require_canonical: bool = False) -> ExactAssemblyWitness[bytes]:
    witness = witness_from_value(_load_json(raw))
    if require_canonical and encode_witness(witness) != raw:
        raise CodecError("assembly witness input is not canonical")
    return witness


def validate_witness_bytes(raw: bytes, *, require_canonical: bool = False) -> bool:
    from .assembly import verify_witness

    try:
        return verify_witness(decode_witness(raw, require_canonical=require_canonical))
    except (CodecError, TypeError, ValueError):
        return False
