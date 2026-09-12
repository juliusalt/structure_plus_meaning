"""Retain an explicit executable condition for a reasoning family's known calls.

The caller must separately establish that the condition implies its intended
native calls. Recording its description and source does not establish that
semantic contract. Validation checks each complete supplied call and retains
both the condition's implementation and its declared evidence inputs.
"""
from dataclasses import dataclass
import inspect
from pathlib import Path
from typing import Callable


@dataclass(frozen=True)
class KnownCallContract:
    check: Callable[[int, dict], bool]
    condition: str
    evidence: tuple = ()

    def inputs(self):
        if not callable(self.check) or not isinstance(self.condition, str) or not self.condition.strip():
            raise ValueError('A known-call contract needs an executable check and an explicit condition.')
        source = inspect.getsourcefile(self.check)
        if source is None:
            raise ValueError('The known-call condition needs a retainable implementation source.')
        paths = {Path(__file__).resolve(), Path(source).resolve(), *(Path(p).resolve() for p in self.evidence)}
        if not all(path.is_file() for path in paths):
            raise ValueError('Every declared known-call evidence input must exist as a file.')
        return sorted(paths)

    def record(self):
        return {'condition': self.condition,
                'operation': self.check.__qualname__,
                'inputs': [str(path) for path in self.inputs()],
                'boundary': 'The complete calls are checked by this retained operation. Its implication to native meaning requires the separately established condition contract.'}

    def validate(self, calls):
        for call in calls:
            entry, term = call
            result = self.check(entry, term)
            if type(result) is not bool:
                raise ValueError(('Known-call condition must return a Boolean', call, result))
            if not result:
                raise AssertionError(('Known call does not satisfy its declared condition', self.condition, call))
        return len(calls)
