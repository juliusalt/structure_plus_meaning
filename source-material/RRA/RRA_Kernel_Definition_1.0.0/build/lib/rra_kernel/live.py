"""Pure finite semantics for live loci, immutable generations, and transactions."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Iterable

from .artifact import RecordRef
from .codec import canonical_json_bytes, reference_to_value
from .core import FormationError

GENERATION_PROFILE = "rra-generation-json-1"


@dataclass(frozen=True, slots=True, order=True)
class LocusRef:
    value: bytes

    def __post_init__(self) -> None:
        if not isinstance(self.value, bytes):
            raise FormationError("locus token must be bytes")


@dataclass(frozen=True, slots=True)
class Generation:
    locus: LocusRef
    predecessors: frozenset[RecordRef]
    payload: RecordRef
    dependencies: frozenset[RecordRef] = frozenset()
    evidence: frozenset[RecordRef] = frozenset()

    def __post_init__(self) -> None:
        for name in ("predecessors", "dependencies", "evidence"):
            values = frozenset(getattr(self, name))
            if not all(isinstance(x, RecordRef) for x in values):
                raise FormationError(f"{name} must contain RecordRef values")
            object.__setattr__(self, name, values)


def _ref_sort_key(ref: RecordRef) -> tuple[str, str, str]:
    return (ref.profile, ref.algorithm, ref.digest.hex())


def generation_to_value(generation: Generation) -> dict:
    return {
        "format": GENERATION_PROFILE,
        "locus": generation.locus.value.hex(),
        "predecessors": [reference_to_value(r) for r in sorted(generation.predecessors, key=_ref_sort_key)],
        "payload": reference_to_value(generation.payload),
        "dependencies": [reference_to_value(r) for r in sorted(generation.dependencies, key=_ref_sort_key)],
        "evidence": [reference_to_value(r) for r in sorted(generation.evidence, key=_ref_sort_key)],
    }


def encode_generation(generation: Generation) -> bytes:
    return canonical_json_bytes(generation_to_value(generation))


def generation_ref(generation: Generation) -> RecordRef:
    return RecordRef(GENERATION_PROFILE, "sha256", hashlib.sha256(encode_generation(generation)).digest())


@dataclass(frozen=True, slots=True)
class Head:
    locus: LocusRef
    generation: RecordRef


@dataclass(frozen=True, slots=True)
class RetainedGeneration:
    reference: RecordRef
    generation: Generation


@dataclass(frozen=True, slots=True)
class LiveState:
    heads: frozenset[Head] = frozenset()
    generations: frozenset[RetainedGeneration] = frozenset()

    def __init__(
        self,
        heads: Iterable[Head] = (),
        generations: Iterable[RetainedGeneration] = (),
    ) -> None:
        hs = frozenset(heads)
        gs = frozenset(generations)
        if len({h.locus for h in hs}) != len(hs):
            raise FormationError("a live state has at most one head per locus")
        if len({g.reference for g in gs}) != len(gs):
            raise FormationError("a retained reference has at most one generation")
        table = {g.reference: g.generation for g in gs}
        for retained in gs:
            if generation_ref(retained.generation) != retained.reference:
                raise FormationError("retained generation reference does not verify")
        for head in hs:
            if head.generation not in table:
                raise FormationError("every head must resolve to a retained generation")
            if table[head.generation].locus != head.locus:
                raise FormationError("head generation must belong to its locus")
        for retained in gs:
            if not retained.generation.predecessors.issubset(table):
                raise FormationError("every predecessor must resolve in the retained state")
        visiting: set[RecordRef] = set()
        finished: set[RecordRef] = set()
        def visit(ref: RecordRef) -> None:
            if ref in finished:
                return
            if ref in visiting:
                raise FormationError("generation predecessor graph must be acyclic")
            visiting.add(ref)
            for parent in table[ref].predecessors:
                visit(parent)
            visiting.remove(ref)
            finished.add(ref)
        for ref in table:
            visit(ref)
        object.__setattr__(self, "heads", hs)
        object.__setattr__(self, "generations", gs)

    def head_map(self) -> dict[LocusRef, RecordRef]:
        return {h.locus: h.generation for h in self.heads}

    def generation_map(self) -> dict[RecordRef, Generation]:
        return {g.reference: g.generation for g in self.generations}


@dataclass(frozen=True, slots=True)
class Compare:
    locus: LocusRef
    expected: RecordRef | None


@dataclass(frozen=True, slots=True)
class NextGeneration:
    payload: RecordRef
    dependencies: frozenset[RecordRef] = frozenset()
    evidence: frozenset[RecordRef] = frozenset()
    additional_predecessors: frozenset[RecordRef] = frozenset()

    def __post_init__(self) -> None:
        for name in ("dependencies", "evidence", "additional_predecessors"):
            values = frozenset(getattr(self, name))
            if not all(isinstance(x, RecordRef) for x in values):
                raise FormationError(f"{name} must contain RecordRef values")
            object.__setattr__(self, name, values)


@dataclass(frozen=True, slots=True)
class Write:
    locus: LocusRef
    next: NextGeneration


@dataclass(frozen=True, slots=True)
class TransactionRequest:
    compare: frozenset[Compare]
    write: frozenset[Write]

    def __init__(self, compare: Iterable[Compare], write: Iterable[Write] = ()) -> None:
        cs = frozenset(compare)
        ws = frozenset(write)
        if len({x.locus for x in cs}) != len(cs):
            raise FormationError("compare map must be single-valued")
        if len({x.locus for x in ws}) != len(ws):
            raise FormationError("write map must be single-valued")
        if not {x.locus for x in ws}.issubset({x.locus for x in cs}):
            raise FormationError("write domain must be a subset of compare domain")
        object.__setattr__(self, "compare", cs)
        object.__setattr__(self, "write", ws)


@dataclass(frozen=True, slots=True)
class Observed:
    locus: LocusRef
    generation: RecordRef | None


@dataclass(frozen=True, slots=True)
class Conflict:
    observed: frozenset[Observed]


@dataclass(frozen=True, slots=True)
class Created:
    locus: LocusRef
    generation: RecordRef


@dataclass(frozen=True, slots=True)
class Committed:
    created: frozenset[Created]


TransactionResult = Conflict | Committed


def transact(state: LiveState, request: TransactionRequest) -> tuple[LiveState, TransactionResult]:
    heads = state.head_map()
    observed = frozenset(Observed(c.locus, heads.get(c.locus)) for c in request.compare)
    expected = {c.locus: c.expected for c in request.compare}
    if any(heads.get(locus) != want for locus, want in expected.items()):
        return state, Conflict(observed)

    retained = state.generation_map()
    writes = {w.locus: w.next for w in request.write}
    created_values: dict[RecordRef, Generation] = {}
    created_heads: dict[LocusRef, RecordRef] = {}
    for locus, spec in writes.items():
        if not spec.additional_predecessors.issubset(retained):
            raise FormationError("additional predecessors must resolve before the transaction")
        predecessors = set(spec.additional_predecessors)
        old = heads.get(locus)
        if old is not None:
            predecessors.add(old)
        generation = Generation(locus, frozenset(predecessors), spec.payload, spec.dependencies, spec.evidence)
        ref = generation_ref(generation)
        existing = retained.get(ref) or created_values.get(ref)
        if existing is not None and existing != generation:
            raise FormationError("generation reference collision")
        created_values[ref] = generation
        created_heads[locus] = ref

    new_heads = dict(heads)
    new_heads.update(created_heads)
    new_retained = dict(retained)
    new_retained.update(created_values)
    new_state = LiveState(
        (Head(l, r) for l, r in new_heads.items()),
        (RetainedGeneration(r, g) for r, g in new_retained.items()),
    )
    return new_state, Committed(frozenset(Created(l, r) for l, r in created_heads.items()))


@dataclass(frozen=True, slots=True)
class PublishedHead:
    locus: LocusRef
    generation: RecordRef


@dataclass(frozen=True, slots=True)
class Publication:
    heads: frozenset[PublishedHead]
    protocols: frozenset[RecordRef] = frozenset()
    executions: frozenset[RecordRef] = frozenset()
    checker_runs: frozenset[RecordRef] = frozenset()
    trust_decisions: frozenset[RecordRef] = frozenset()
    policies: frozenset[RecordRef] = frozenset()
    dependencies: frozenset[RecordRef] = frozenset()
    evidence: frozenset[RecordRef] = frozenset()
    provenance: frozenset[RecordRef] = frozenset()

    def __post_init__(self) -> None:
        heads = frozenset(self.heads)
        if len({h.locus for h in heads}) != len(heads):
            raise FormationError("publication has at most one generation per locus")
        object.__setattr__(self, "heads", heads)
        for name in (
            "protocols", "executions", "checker_runs", "trust_decisions", "policies",
            "dependencies", "evidence", "provenance",
        ):
            values = frozenset(getattr(self, name))
            if not all(isinstance(x, RecordRef) for x in values):
                raise FormationError(f"{name} must contain RecordRef values")
            object.__setattr__(self, name, values)


def publication_from_state(state: LiveState, loci: Iterable[LocusRef], **links) -> Publication:
    heads = state.head_map()
    selected = frozenset(PublishedHead(locus, heads[locus]) for locus in loci)
    return Publication(selected, **links)
