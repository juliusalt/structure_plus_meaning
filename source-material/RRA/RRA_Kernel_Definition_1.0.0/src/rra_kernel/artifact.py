"""Addressed exact records, integrity references, and citations."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Mapping

from .core import FormationError
from .data import Object, is_object_isomorphism


@dataclass(frozen=True, slots=True)
class ExactRecord:
    """A structured object whose local addresses are finite octet strings."""

    object: Object[bytes]

    def __post_init__(self) -> None:
        if any(not isinstance(a, bytes) for a in self.object.structure.positions):
            raise FormationError("every exact-record local address must be bytes")

    @property
    def positions(self) -> frozenset[bytes]:
        return self.object.structure.positions


@dataclass(frozen=True, slots=True)
class RecordRef:
    profile: str
    algorithm: str
    digest: bytes

    def __post_init__(self) -> None:
        if not self.profile or not self.algorithm:
            raise FormationError("reference profile and algorithm must be nonempty")
        if not isinstance(self.digest, bytes) or not self.digest:
            raise FormationError("reference digest must be a nonempty byte string")
        if self.algorithm == "sha256" and len(self.digest) != 32:
            raise FormationError("sha256 digest must contain 32 octets")


@dataclass(frozen=True, slots=True)
class Citation:
    record: RecordRef
    address: bytes

    def __post_init__(self) -> None:
        if not isinstance(self.address, bytes):
            raise FormationError("citation address must be bytes")


def reference_for(record: ExactRecord) -> RecordRef:
    from .codec import reference_for_record

    return reference_for_record(record)


def verifies(reference: RecordRef, record: ExactRecord) -> bool:
    return reference == reference_for(record)


def citation_resolves(citation: Citation, record: ExactRecord) -> bool:
    return verifies(citation.record, record) and citation.address in record.positions


def is_record_isomorphism(
    left: ExactRecord,
    right: ExactRecord,
    mapping: Mapping[bytes, bytes],
) -> bool:
    return is_object_isomorphism(left.object, right.object, mapping)

class ResolverError(LookupError):
    """A reference is absent, mismatched, or would be rebound."""


class MemoryResolver:
    """Small reference resolver enforcing verification and non-rebinding."""

    def __init__(self) -> None:
        self._records: dict[RecordRef, ExactRecord] = {}

    def add(
        self,
        record: ExactRecord,
        reference: RecordRef | None = None,
        verifier: Callable[[RecordRef, ExactRecord], bool] | None = None,
    ) -> RecordRef:
        ref = reference or reference_for(record)
        check = verifier or verifies
        if not check(ref, record):
            raise ResolverError("reference does not verify against the supplied exact record")
        prior = self._records.get(ref)
        if prior is not None and prior != record:
            raise ResolverError("reference is already bound to a different exact record")
        self._records[ref] = record
        return ref

    def resolve(self, reference: RecordRef) -> ExactRecord:
        try:
            return self._records[reference]
        except KeyError as exc:
            raise ResolverError("reference is unresolved") from exc

    def resolve_citation(self, citation: Citation) -> tuple[ExactRecord, bytes]:
        record = self.resolve(citation.record)
        if citation.address not in record.positions:
            raise ResolverError("citation address is absent from the resolved exact record")
        return record, citation.address
