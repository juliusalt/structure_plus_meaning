"""Optional data profiles over a finite structure."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Generic, Hashable, Iterable, Mapping, TypeVar, Union

from .core import FormationError, Structure, is_isomorphism

A = TypeVar("A", bound=Hashable)
B = TypeVar("B", bound=Hashable)


class DataKind(str, Enum):
    NONE = "none"
    BAG = "bag"
    FUNCTIONAL = "functional"
    NODE = "node"


@dataclass(frozen=True, slots=True)
class NoData:
    kind: DataKind = DataKind.NONE


@dataclass(frozen=True, slots=True, order=True)
class BagEntry(Generic[A]):
    owner: A
    value: bytes
    count: int = 1

    def __post_init__(self) -> None:
        if not isinstance(self.value, bytes):
            raise FormationError("data values must be bytes")
        if isinstance(self.count, bool) or not isinstance(self.count, int) or self.count <= 0:
            raise FormationError("bag multiplicity must be a positive integer")


@dataclass(frozen=True, slots=True)
class BagData(Generic[A]):
    entries: frozenset[BagEntry[A]]
    kind: DataKind = DataKind.BAG

    def __init__(self, entries: Iterable[BagEntry[A] | tuple[A, bytes, int]] = ()) -> None:
        by_key: dict[tuple[A, bytes], int] = {}
        for raw in entries:
            e = raw if isinstance(raw, BagEntry) else BagEntry(*raw)
            key = (e.owner, e.value)
            if key in by_key:
                raise FormationError("bag must contain one multiplicity per owner/value pair")
            by_key[key] = e.count
        object.__setattr__(self, "entries", frozenset(BagEntry(o, v, n) for (o, v), n in by_key.items()))
        object.__setattr__(self, "kind", DataKind.BAG)


@dataclass(frozen=True, slots=True, order=True)
class FunctionalEntry(Generic[A]):
    owner: A
    value: bytes

    def __post_init__(self) -> None:
        if not isinstance(self.value, bytes):
            raise FormationError("data values must be bytes")


@dataclass(frozen=True, slots=True)
class FunctionalData(Generic[A]):
    entries: frozenset[FunctionalEntry[A]]
    kind: DataKind = DataKind.FUNCTIONAL

    def __init__(self, entries: Iterable[FunctionalEntry[A] | tuple[A, bytes]] = ()) -> None:
        by_owner: dict[A, bytes] = {}
        for raw in entries:
            e = raw if isinstance(raw, FunctionalEntry) else FunctionalEntry(*raw)
            if e.owner in by_owner:
                raise FormationError("functional data must have at most one binding per owner")
            by_owner[e.owner] = e.value
        object.__setattr__(self, "entries", frozenset(FunctionalEntry(o, v) for o, v in by_owner.items()))
        object.__setattr__(self, "kind", DataKind.FUNCTIONAL)


@dataclass(frozen=True, slots=True, order=True)
class NodeEntry(Generic[A]):
    node: A
    owner: A
    value: bytes

    def __post_init__(self) -> None:
        if not isinstance(self.value, bytes):
            raise FormationError("data values must be bytes")


@dataclass(frozen=True, slots=True)
class NodeData(Generic[A]):
    entries: frozenset[NodeEntry[A]]
    kind: DataKind = DataKind.NODE

    def __init__(self, entries: Iterable[NodeEntry[A] | tuple[A, A, bytes]] = ()) -> None:
        by_node: dict[A, tuple[A, bytes]] = {}
        for raw in entries:
            e = raw if isinstance(raw, NodeEntry) else NodeEntry(*raw)
            if e.node in by_node:
                raise FormationError("node data must have at most one binding per node")
            by_node[e.node] = (e.owner, e.value)
        object.__setattr__(self, "entries", frozenset(NodeEntry(n, o, v) for n, (o, v) in by_node.items()))
        object.__setattr__(self, "kind", DataKind.NODE)


Data = Union[NoData, BagData[A], FunctionalData[A], NodeData[A]]


@dataclass(frozen=True, slots=True)
class Object(Generic[A]):
    structure: Structure[A]
    data: Data[A] = NoData()

    def __post_init__(self) -> None:
        validate_data(self.structure, self.data)

    @property
    def kind(self) -> DataKind:
        return self.data.kind

    def renamed(self, mapping: Mapping[A, B]) -> "Object[B]":
        return Object(self.structure.renamed(mapping), rename_data(self.data, mapping))


def validate_data(structure: Structure[A], data: Data[A]) -> None:
    ps = structure.positions
    if isinstance(data, NoData):
        return
    if isinstance(data, BagData):
        missing = {e.owner for e in data.entries if e.owner not in ps}
    elif isinstance(data, FunctionalData):
        missing = {e.owner for e in data.entries if e.owner not in ps}
    elif isinstance(data, NodeData):
        missing = {x for e in data.entries for x in (e.node, e.owner) if x not in ps}
    else:
        raise FormationError("unknown data profile")
    if missing:
        raise FormationError(f"data coordinates outside carrier: {missing!r}")


def rename_data(data: Data[A], mapping: Mapping[A, B]) -> Data[B]:
    if isinstance(data, NoData):
        return NoData()
    if isinstance(data, BagData):
        return BagData((mapping[e.owner], e.value, e.count) for e in data.entries)
    if isinstance(data, FunctionalData):
        return FunctionalData((mapping[e.owner], e.value) for e in data.entries)
    if isinstance(data, NodeData):
        return NodeData((mapping[e.node], mapping[e.owner], e.value) for e in data.entries)
    raise FormationError("unknown data profile")


def is_object_isomorphism(left: Object[A], right: Object[B], mapping: Mapping[A, B]) -> bool:
    if left.kind != right.kind or not is_isomorphism(left.structure, right.structure, mapping):
        return False
    try:
        return rename_data(left.data, mapping) == right.data
    except (KeyError, FormationError):
        return False


def empty_data(kind: DataKind) -> Data[Hashable]:
    return {
        DataKind.NONE: NoData(),
        DataKind.BAG: BagData(),
        DataKind.FUNCTIONAL: FunctionalData(),
        DataKind.NODE: NodeData(),
    }[kind]
