# RRA Kernel Definition 1.0.0

This package is a self-contained definition and executable reference model of the Relational Record Architecture kernel.

The mandatory module is **Structure**. The remaining modules are explicit profiles and may be adopted independently subject to the dependency graph below.

```text
Structure
└── Data
    ├── Exact Artifact
    │   ├── Evidence Envelopes
    │   ├── Live Trajectories
    │   └── Exact Assembly Realization
    └── Assembly
```

Nothing in this package assigns domain truth, proof validity, type, authority, ownership, or compatibility to a structure. Such meanings require a separately named protocol.

## Contents

- `SPECIFICATION.md` — complete normative definition.
- `src/rra_kernel/` — standard-library Python reference implementation.
- `schemas/` — JSON Schemas for the wire profiles.
- `examples/` — canonical machine-readable examples.
- `tests/` — conformance and regression tests.
- `isabelle/` — definition-only Isabelle/HOL theories.
- `CONFORMANCE.md` — implementation conformance surface.
- `MANIFEST.json` — exact release file hashes.

## Install and use

```bash
python -m pip install dist/rra_kernel-1.0.0-py3-none-any.whl
rra-kernel validate examples/parallel_record.json
rra-kernel ref examples/parallel_record.json
rra-kernel verify-assembly examples/assembly_witness.json
python -m unittest discover -s tests -v
```

Library entry points:

```python
from rra_kernel import Structure, BagData, Object, ExactRecord
from rra_kernel.codec import decode_record, encode_record
from rra_kernel.assembly import verify_witness
```

The Python implementation is a reference implementation of the finite definitions. The mathematical definitions in `SPECIFICATION.md` are authoritative.
