"""Neutral finite quotient assembly and exact witness verification."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from typing import Generic, Hashable, Iterable, Mapping, TypeVar

from .artifact import ExactRecord
from .core import FormationError, Structure
from .data import (
    BagData,
    DataKind,
    FunctionalData,
    NodeData,
    NoData,
    Object,
)

S = TypeVar("S", bound=Hashable)
A = TypeVar("A", bound=Hashable)
B = TypeVar("B", bound=Hashable)


class AssemblyError(ValueError):
    """A piece family, gluing, profile transport, or exact witness is invalid."""


@dataclass(frozen=True, slots=True)
class Piece(Generic[S, A]):
    slot: S
    object: Object[A]


@dataclass(frozen=True, slots=True, order=True)
class Copied(Generic[S, A]):
    slot: S
    position: A


@dataclass(frozen=True, slots=True)
class PieceFamily(Generic[S, A]):
    kind: DataKind
    pieces: frozenset[Piece[S, A]]

    def __init__(self, kind: DataKind | str, pieces: Iterable[Piece[S, A]] = ()) -> None:
        try:
            selected = DataKind(kind)
        except ValueError as exc:
            raise AssemblyError(f"unknown data profile: {kind!r}") from exc
        material = frozenset(pieces)
        slots = [p.slot for p in material]
        if len(set(slots)) != len(slots):
            raise AssemblyError("piece slots must be distinct")
        bad = [p.slot for p in material if p.object.kind != selected]
        if bad:
            raise AssemblyError(f"piece data profile differs from family profile: {bad!r}")
        object.__setattr__(self, "kind", selected)
        object.__setattr__(self, "pieces", material)

    @property
    def copied_positions(self) -> frozenset[Copied[S, A]]:
        return frozenset(Copied(p.slot, u) for p in self.pieces for u in p.object.structure.positions)

    def by_slot(self) -> dict[S, Object[A]]:
        return {p.slot: p.object for p in self.pieces}


@dataclass(frozen=True, slots=True)
class Gluing(Generic[S, A]):
    """An exact partition of the complete copied carrier."""

    blocks: frozenset[frozenset[Copied[S, A]]]

    def __init__(
        self,
        family: PieceFamily[S, A],
        blocks: Iterable[Iterable[Copied[S, A]]],
    ) -> None:
        bs = frozenset(frozenset(block) for block in blocks)
        if any(not block for block in bs):
            raise AssemblyError("gluing blocks must be nonempty")
        flattened = [x for block in bs for x in block]
        if len(set(flattened)) != len(flattened):
            raise AssemblyError("gluing blocks must be disjoint")
        if frozenset(flattened) != family.copied_positions:
            raise AssemblyError("gluing blocks must partition the complete copied carrier")
        object.__setattr__(self, "blocks", bs)

    def class_map(self) -> dict[Copied[S, A], frozenset[Copied[S, A]]]:
        return {x: block for block in self.blocks for x in block}


def discrete_gluing(family: PieceFamily[S, A]) -> Gluing[S, A]:
    return Gluing(family, ({x} for x in family.copied_positions))


def _require_total_map(family: PieceFamily[S, A], mapping: Mapping[Copied[S, A], B]) -> None:
    if frozenset(mapping) != family.copied_positions:
        raise AssemblyError("quotient map domain must be the complete copied carrier")


def _pushforward_data(
    family: PieceFamily[S, A],
    mapping: Mapping[Copied[S, A], B],
):
    if family.kind is DataKind.NONE:
        return NoData()

    if family.kind is DataKind.BAG:
        counts: dict[tuple[B, bytes], int] = defaultdict(int)
        for piece in family.pieces:
            assert isinstance(piece.object.data, BagData)
            for e in piece.object.data.entries:
                counts[(mapping[Copied(piece.slot, e.owner)], e.value)] += e.count
        return BagData((owner, value, count) for (owner, value), count in counts.items())

    if family.kind is DataKind.FUNCTIONAL:
        values: dict[B, bytes] = {}
        for piece in family.pieces:
            assert isinstance(piece.object.data, FunctionalData)
            for e in piece.object.data.entries:
                owner = mapping[Copied(piece.slot, e.owner)]
                old = values.get(owner)
                if old is not None and old != e.value:
                    raise AssemblyError("functional data conflict after gluing")
                values[owner] = e.value
        return FunctionalData(values.items())

    if family.kind is DataKind.NODE:
        values: dict[B, tuple[B, bytes]] = {}
        for piece in family.pieces:
            assert isinstance(piece.object.data, NodeData)
            for e in piece.object.data.entries:
                node = mapping[Copied(piece.slot, e.node)]
                binding = (mapping[Copied(piece.slot, e.owner)], e.value)
                old = values.get(node)
                if old is not None and old != binding:
                    raise AssemblyError("node data conflict after gluing")
                values[node] = binding
        return NodeData((node, owner, value) for node, (owner, value) in values.items())

    raise AssemblyError("unknown data profile")


def pushforward(
    family: PieceFamily[S, A],
    mapping: Mapping[Copied[S, A], B],
) -> Object[B]:
    """Push all and only copied structure and profile data through a total map."""
    _require_total_map(family, mapping)
    output_positions = frozenset(mapping.values())
    output_incidence: set[tuple[B, B, B]] = set()
    for piece in family.pieces:
        for r, p, x in piece.object.structure.incidence:
            output_incidence.add(
                (
                    mapping[Copied(piece.slot, r)],
                    mapping[Copied(piece.slot, p)],
                    mapping[Copied(piece.slot, x)],
                )
            )
    return Object(Structure(output_positions, output_incidence), _pushforward_data(family, mapping))


def quotient(
    family: PieceFamily[S, A],
    gluing: Gluing[S, A],
) -> Object[frozenset[Copied[S, A]]]:
    """Construct the abstract quotient whose atoms are equivalence classes."""
    return pushforward(family, gluing.class_map())


@dataclass(frozen=True, slots=True)
class ExactPiece(Generic[S]):
    slot: S
    record: ExactRecord


@dataclass(frozen=True, slots=True)
class Origin(Generic[S]):
    slot: S
    source: bytes
    target: bytes


@dataclass(frozen=True, slots=True)
class ExactAssemblyWitness(Generic[S]):
    kind: DataKind
    pieces: frozenset[ExactPiece[S]]
    output: ExactRecord
    origins: frozenset[Origin[S]]

    def __init__(
        self,
        kind: DataKind | str,
        pieces: Iterable[ExactPiece[S]],
        output: ExactRecord,
        origins: Iterable[Origin[S]],
    ) -> None:
        object.__setattr__(self, "kind", DataKind(kind))
        object.__setattr__(self, "pieces", frozenset(pieces))
        object.__setattr__(self, "output", output)
        object.__setattr__(self, "origins", frozenset(origins))

    def family(self) -> PieceFamily[S, bytes]:
        return PieceFamily(self.kind, (Piece(p.slot, p.record.object) for p in self.pieces))

    def quotient_map(self) -> dict[Copied[S, bytes], bytes]:
        result: dict[Copied[S, bytes], bytes] = {}
        for origin in self.origins:
            key = Copied(origin.slot, origin.source)
            if key in result:
                raise AssemblyError("origin map must be single-valued")
            result[key] = origin.target
        return result


def require_valid_witness(witness: ExactAssemblyWitness[S]) -> None:
    family = witness.family()
    if witness.output.object.kind != family.kind:
        raise AssemblyError("output data profile differs from family profile")
    mapping = witness.quotient_map()
    expected = pushforward(family, mapping)
    if frozenset(mapping.values()) != witness.output.positions:
        raise AssemblyError("quotient map must be surjective onto the complete output carrier")
    if expected != witness.output.object:
        raise AssemblyError("output is not the exact pushforward of the input family")


def verify_witness(witness: ExactAssemblyWitness[S]) -> bool:
    try:
        require_valid_witness(witness)
        return True
    except (AssemblyError, FormationError, KeyError, TypeError, ValueError):
        return False


def k1(record: ExactRecord) -> bool:
    try:
        ExactRecord(record.object)
        return True
    except (FormationError, TypeError, ValueError):
        return False


def k2(witness: ExactAssemblyWitness[S]) -> bool:
    return verify_witness(witness)
