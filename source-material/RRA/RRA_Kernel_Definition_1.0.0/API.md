# Python API

## Structure

```python
Structure(positions, incidence)
is_isomorphism(left, right, mapping)
is_bounded_isomorphism(left, right, mapping, left_boundary, right_boundary)
```

`Structure` accepts any hashable atom. Construction performs the complete formation check.

## Data

```python
Object(structure, NoData())
Object(structure, BagData([(owner, value_bytes, count), ...]))
Object(structure, FunctionalData([(owner, value_bytes), ...]))
Object(structure, NodeData([(node, owner, value_bytes), ...]))
is_object_isomorphism(left, right, mapping)
```

Profile tables are immutable and extensional.

## Exact artifacts

```python
ExactRecord(object_with_byte_addresses)
reference_for(record)
MemoryResolver().add(record)
# A custom reference profile supplies its own verifier when adding an alias.
Citation(reference, address)
```

```python
encode_record(record) -> bytes
decode_record(raw, require_canonical=True) -> ExactRecord
```

## Assembly

```python
family = PieceFamily(kind, [Piece(slot, object), ...])
gluing = Gluing(family, [block, ...])
output = quotient(family, gluing)
```

For exact checking:

```python
witness = ExactAssemblyWitness(kind, pieces, output, origins)
verify_witness(witness) -> bool
encode_witness(witness) -> bytes
decode_witness(raw) -> ExactAssemblyWitness
```

## Evidence and live profiles

Envelope classes are in `rra_kernel.evidence`. Immutable generation and transaction classes are in `rra_kernel.live`; `transact(state, request)` implements the atomic transition relation.
