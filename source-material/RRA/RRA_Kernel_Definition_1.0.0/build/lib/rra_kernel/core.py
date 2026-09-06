"""Finite one-sorted relational structures."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, Hashable, Iterable, Mapping, TypeVar

A = TypeVar("A", bound=Hashable)
B = TypeVar("B", bound=Hashable)
K = TypeVar("K", bound=Hashable)


class FormationError(ValueError):
    """A supplied finite object does not satisfy its formation equations."""


@dataclass(frozen=True, slots=True)
class Structure(Generic[A]):
    """A finite carrier and a finite ternary incidence relation."""

    positions: frozenset[A]
    incidence: frozenset[tuple[A, A, A]]

    def __init__(
        self,
        positions: Iterable[A] = (),
        incidence: Iterable[tuple[A, A, A]] = (),
    ) -> None:
        ps = frozenset(positions)
        rows: set[tuple[A, A, A]] = set()
        for row in incidence:
            t = tuple(row)
            if len(t) != 3:
                raise FormationError("each incidence row must have arity three")
            rows.add((t[0], t[1], t[2]))
        rel = frozenset(rows)
        missing = {x for row in rel for x in row if x not in ps}
        if missing:
            raise FormationError(f"incidence coordinates outside carrier: {missing!r}")
        object.__setattr__(self, "positions", ps)
        object.__setattr__(self, "incidence", rel)

    def renamed(self, mapping: Mapping[A, B]) -> "Structure[B]":
        """Transport through a supplied carrier bijection."""
        _require_bijection(mapping, self.positions)
        return Structure(
            mapping.values(),
            ((mapping[r], mapping[p], mapping[x]) for r, p, x in self.incidence),
        )


def _require_bijection(mapping: Mapping[A, B], domain: frozenset[A]) -> None:
    if frozenset(mapping) != domain:
        raise FormationError("mapping domain must be the complete carrier")
    values = tuple(mapping.values())
    if len(set(values)) != len(values):
        raise FormationError("mapping must be injective")


def is_isomorphism(left: Structure[A], right: Structure[B], mapping: Mapping[A, B]) -> bool:
    """Check a supplied structure isomorphism, preserving and reflecting incidence."""
    try:
        _require_bijection(mapping, left.positions)
    except FormationError:
        return False
    if frozenset(mapping.values()) != right.positions:
        return False
    image = frozenset((mapping[r], mapping[p], mapping[x]) for r, p, x in left.incidence)
    return image == right.incidence


def is_bounded_isomorphism(
    left: Structure[A],
    right: Structure[B],
    mapping: Mapping[A, B],
    left_boundary: Mapping[K, A],
    right_boundary: Mapping[K, B],
) -> bool:
    """Check an isomorphism and exact agreement of supplied boundary domains."""
    if not is_isomorphism(left, right, mapping):
        return False
    if frozenset(left_boundary) != frozenset(right_boundary):
        return False
    if any(v not in left.positions for v in left_boundary.values()):
        return False
    if any(v not in right.positions for v in right_boundary.values()):
        return False
    return all(mapping[left_boundary[k]] == right_boundary[k] for k in left_boundary)
