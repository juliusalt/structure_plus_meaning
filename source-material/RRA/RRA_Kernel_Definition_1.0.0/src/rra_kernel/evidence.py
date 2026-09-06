"""Exact-reference envelopes. These classes assign no semantic force."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

from .artifact import RecordRef


def _refs(values: Iterable[RecordRef]) -> frozenset[RecordRef]:
    result = frozenset(values)
    if not all(isinstance(x, RecordRef) for x in result):
        raise TypeError("envelope links must be RecordRef values")
    return result


@dataclass(frozen=True, slots=True)
class ProtocolEnvelope:
    specification: RecordRef
    dependencies: frozenset[RecordRef] = frozenset()
    input_profiles: frozenset[RecordRef] = frozenset()
    output_profiles: frozenset[RecordRef] = frozenset()
    context_profiles: frozenset[RecordRef] = frozenset()
    executors_or_checkers: frozenset[RecordRef] = frozenset()

    def __post_init__(self) -> None:
        for name in ("dependencies", "input_profiles", "output_profiles", "context_profiles", "executors_or_checkers"):
            object.__setattr__(self, name, _refs(getattr(self, name)))


@dataclass(frozen=True, slots=True)
class ClaimEnvelope:
    claim: RecordRef
    protocols: frozenset[RecordRef] = frozenset()
    context: frozenset[RecordRef] = frozenset()
    dependencies: frozenset[RecordRef] = frozenset()
    provenance: frozenset[RecordRef] = frozenset()

    def __post_init__(self) -> None:
        for name in ("protocols", "context", "dependencies", "provenance"):
            object.__setattr__(self, name, _refs(getattr(self, name)))


@dataclass(frozen=True, slots=True)
class ExecutionEnvelope:
    protocol: RecordRef
    executor: RecordRef
    inputs: tuple[RecordRef, ...] = ()
    outputs: tuple[RecordRef, ...] = ()
    context: frozenset[RecordRef] = frozenset()
    correspondences: frozenset[RecordRef] = frozenset()
    residuals: frozenset[RecordRef] = frozenset()
    provenance: frozenset[RecordRef] = frozenset()

    def __post_init__(self) -> None:
        object.__setattr__(self, "inputs", tuple(self.inputs))
        object.__setattr__(self, "outputs", tuple(self.outputs))
        if not all(isinstance(x, RecordRef) for x in self.inputs + self.outputs):
            raise TypeError("execution input and output links must be RecordRef values")
        for name in ("context", "correspondences", "residuals", "provenance"):
            object.__setattr__(self, name, _refs(getattr(self, name)))


@dataclass(frozen=True, slots=True)
class EvidenceEnvelope:
    subjects: frozenset[RecordRef]
    evidence: frozenset[RecordRef] = frozenset()
    sources: frozenset[RecordRef] = frozenset()
    correspondences: frozenset[RecordRef] = frozenset()
    residuals: frozenset[RecordRef] = frozenset()
    provenance: frozenset[RecordRef] = frozenset()

    def __post_init__(self) -> None:
        for name in ("subjects", "evidence", "sources", "correspondences", "residuals", "provenance"):
            object.__setattr__(self, name, _refs(getattr(self, name)))


@dataclass(frozen=True, slots=True)
class CheckerRunEnvelope:
    checker: RecordRef
    subjects: tuple[RecordRef, ...]
    inputs: tuple[RecordRef, ...]
    output: RecordRef
    environment: frozenset[RecordRef] = frozenset()
    provenance: frozenset[RecordRef] = frozenset()

    def __post_init__(self) -> None:
        object.__setattr__(self, "subjects", tuple(self.subjects))
        object.__setattr__(self, "inputs", tuple(self.inputs))
        if not all(isinstance(x, RecordRef) for x in self.subjects + self.inputs):
            raise TypeError("checker links must be RecordRef values")
        object.__setattr__(self, "environment", _refs(self.environment))
        object.__setattr__(self, "provenance", _refs(self.provenance))


@dataclass(frozen=True, slots=True)
class TrustDecisionEnvelope:
    basis: RecordRef
    subject: RecordRef
    purpose: RecordRef
    decision: RecordRef
    evidence: frozenset[RecordRef] = frozenset()
    provenance: frozenset[RecordRef] = frozenset()

    def __post_init__(self) -> None:
        object.__setattr__(self, "evidence", _refs(self.evidence))
        object.__setattr__(self, "provenance", _refs(self.provenance))


@dataclass(frozen=True, slots=True)
class AssessmentEnvelope:
    claims: frozenset[RecordRef] = frozenset()
    executions: frozenset[RecordRef] = frozenset()
    evidence: frozenset[RecordRef] = frozenset()
    checker_runs: frozenset[RecordRef] = frozenset()
    trust_decisions: frozenset[RecordRef] = frozenset()
    results: frozenset[RecordRef] = frozenset()
    residuals: frozenset[RecordRef] = frozenset()
    provenance: frozenset[RecordRef] = frozenset()

    def __post_init__(self) -> None:
        for name in (
            "claims", "executions", "evidence", "checker_runs", "trust_decisions",
            "results", "residuals", "provenance",
        ):
            object.__setattr__(self, name, _refs(getattr(self, name)))
