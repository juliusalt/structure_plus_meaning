from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from rra_kernel import (  # noqa: E402
    BagData,
    Citation,
    Copied,
    DataKind,
    ExactAssemblyWitness,
    ExactPiece,
    ExactRecord,
    FormationError,
    FunctionalData,
    Gluing,
    MemoryResolver,
    NodeData,
    NoData,
    Object,
    Origin,
    Piece,
    PieceFamily,
    Structure,
    citation_resolves,
    discrete_gluing,
    is_bounded_isomorphism,
    is_isomorphism,
    is_object_isomorphism,
    quotient,
    reference_for,
    verify_witness,
)
from rra_kernel.assembly import AssemblyError  # noqa: E402
from rra_kernel.codec import CodecError, decode_record, encode_record  # noqa: E402
from rra_kernel.assembly_codec import decode_witness, encode_witness  # noqa: E402
from rra_kernel.evidence import ClaimEnvelope, ExecutionEnvelope  # noqa: E402
from rra_kernel.live import (  # noqa: E402
    Compare,
    Committed,
    Conflict,
    LiveState,
    LocusRef,
    NextGeneration,
    TransactionRequest,
    Write,
    transact,
)


class StructureTests(unittest.TestCase):
    def test_empty_structure_forms(self):
        self.assertEqual(Structure(), Structure(frozenset(), frozenset()))

    def test_out_of_carrier_rejected(self):
        with self.assertRaises(FormationError):
            Structure({0}, {(0, 0, 1)})

    def test_isolated_position_is_retained(self):
        self.assertNotEqual(Structure(), Structure({0}, set()))

    def test_cycles_and_self_incidence_form(self):
        s = Structure({0}, {(0, 0, 0)})
        self.assertIn((0, 0, 0), s.incidence)

    def test_supplied_isomorphism(self):
        left = Structure({0, 1, 2}, {(0, 1, 2)})
        right = Structure({"r", "p", "x"}, {("r", "p", "x")})
        self.assertTrue(is_isomorphism(left, right, {0: "r", 1: "p", 2: "x"}))
        self.assertFalse(is_isomorphism(left, right, {0: "r", 1: "x", 2: "p"}))

    def test_boundary_requires_same_domain_including_absence(self):
        s = Structure({0})
        self.assertFalse(is_bounded_isomorphism(s, s, {0: 0}, {}, {"k": 0}))
        self.assertTrue(is_bounded_isomorphism(s, s, {0: 0}, {"k": 0}, {"k": 0}))


class DataTests(unittest.TestCase):
    def test_bag_is_extensional_not_ordered(self):
        a = BagData([(0, b"a", 2), (1, b"b", 1)])
        b = BagData([(1, b"b", 1), (0, b"a", 2)])
        self.assertEqual(a, b)

    def test_bag_duplicate_key_rejected(self):
        with self.assertRaises(FormationError):
            BagData([(0, b"a", 1), (0, b"a", 2)])

    def test_functional_duplicate_owner_rejected(self):
        with self.assertRaises(FormationError):
            FunctionalData([(0, b"a"), (0, b"a")])

    def test_node_coordinates_must_be_structural(self):
        with self.assertRaises(FormationError):
            Object(Structure({0}), NodeData([(1, 0, b"x")]))

    def test_payload_preserving_isomorphism(self):
        left = Object(Structure({0}), BagData([(0, b"x", 3)]))
        right = Object(Structure({1}), BagData([(1, b"x", 3)]))
        self.assertTrue(is_object_isomorphism(left, right, {0: 1}))
        wrong = Object(Structure({1}), BagData([(1, b"x", 2)]))
        self.assertFalse(is_object_isomorphism(left, wrong, {0: 1}))


class ArtifactTests(unittest.TestCase):
    def test_record_requires_byte_addresses(self):
        with self.assertRaises(FormationError):
            ExactRecord(Object(Structure({0}), NoData()))

    def test_canonical_round_trip_all_profiles(self):
        records = [
            ExactRecord(Object(Structure(), NoData())),
            ExactRecord(Object(Structure({b"a"}), BagData([(b"a", b"v", 2)]))),
            ExactRecord(Object(Structure({b"a"}), FunctionalData([(b"a", b"v")]))),
            ExactRecord(Object(Structure({b"a", b"d"}), NodeData([(b"d", b"a", b"v")]))),
        ]
        for record in records:
            self.assertEqual(decode_record(encode_record(record)), record)

    def test_noncanonical_input_rejected(self):
        raw = b'{"positions":[],"incidence":[],"format":"rra-record-json-1","data":{"kind":"none"}}'
        with self.assertRaises(CodecError):
            decode_record(raw)
        self.assertEqual(decode_record(raw, require_canonical=False).positions, frozenset())

    def test_duplicate_json_key_rejected(self):
        raw = b'{"data":{"kind":"none"},"format":"rra-record-json-1","format":"rra-record-json-1","incidence":[],"positions":[]}'
        with self.assertRaises(CodecError):
            decode_record(raw, require_canonical=False)

    def test_reference_and_citation(self):
        record = ExactRecord(Object(Structure({b"a"}), NoData()))
        ref = reference_for(record)
        self.assertTrue(citation_resolves(Citation(ref, b"a"), record))
        self.assertFalse(citation_resolves(Citation(ref, b"b"), record))

    def test_memory_resolver_is_non_rebinding(self):
        left = ExactRecord(Object(Structure({b"a"}), NoData()))
        resolver = MemoryResolver()
        ref = resolver.add(left)
        self.assertEqual(resolver.resolve(ref), left)
        self.assertEqual(resolver.resolve_citation(Citation(ref, b"a")), (left, b"a"))
        alias = type(ref)("local-alias", "opaque", b"alias")
        resolver.add(left, alias, lambda supplied, record: supplied == alias)
        self.assertEqual(resolver.resolve(alias), left)
        other = ExactRecord(Object(Structure({b"b"}), NoData()))
        with self.assertRaises(Exception):
            resolver.add(other, alias, lambda supplied, record: True)

    def test_shipped_record_examples_are_canonical(self):
        for path in (ROOT / "examples").glob("*_record.json"):
            raw = path.read_bytes().rstrip(b"\n")
            self.assertEqual(encode_record(decode_record(raw)), raw)


class AssemblyTests(unittest.TestCase):
    def test_discrete_quotient_preserves_two_equal_pieces(self):
        obj = Object(Structure({0}), NoData())
        family = PieceFamily(DataKind.NONE, [Piece("a", obj), Piece("b", obj)])
        out = quotient(family, discrete_gluing(family))
        self.assertEqual(len(out.structure.positions), 2)

    def test_arbitrary_structural_merge(self):
        obj = Object(Structure({0, 1, 2}, {(0, 1, 2)}), NoData())
        family = PieceFamily(DataKind.NONE, [Piece("s", obj)])
        all_positions = family.copied_positions
        out = quotient(family, Gluing(family, [all_positions]))
        self.assertEqual(len(out.structure.positions), 1)
        only = next(iter(out.structure.positions))
        self.assertEqual(out.structure.incidence, frozenset({(only, only, only)}))

    def test_bag_counts_sum_after_merge(self):
        obj = Object(Structure({0, 1}), BagData([(0, b"x", 2), (1, b"x", 3)]))
        family = PieceFamily(DataKind.BAG, [Piece("s", obj)])
        out = quotient(family, Gluing(family, [family.copied_positions]))
        entry = next(iter(out.data.entries))
        self.assertEqual(entry.count, 5)

    def test_functional_conflict_blocks_profile_quotient(self):
        obj = Object(Structure({0, 1}), FunctionalData([(0, b"x"), (1, b"y")]))
        family = PieceFamily(DataKind.FUNCTIONAL, [Piece("s", obj)])
        with self.assertRaises(AssemblyError):
            quotient(family, Gluing(family, [family.copied_positions]))

    def test_node_conflict_blocks_profile_quotient(self):
        obj = Object(
            Structure({0, 1, 2}),
            NodeData([(0, 2, b"x"), (1, 2, b"y")]),
        )
        family = PieceFamily(DataKind.NODE, [Piece("s", obj)])
        gluing = Gluing(family, [{Copied("s", 0), Copied("s", 1)}, {Copied("s", 2)}])
        with self.assertRaises(AssemblyError):
            quotient(family, gluing)

    def test_empty_family_has_explicit_profile(self):
        family = PieceFamily(DataKind.BAG, [])
        out = quotient(family, Gluing(family, []))
        self.assertEqual(out.kind, DataKind.BAG)
        self.assertFalse(out.structure.positions)

    def test_exact_witness(self):
        source = ExactRecord(Object(Structure({b"s"}), NoData()))
        output = ExactRecord(Object(Structure({b"o"}), NoData()))
        witness = ExactAssemblyWitness(
            DataKind.NONE,
            [ExactPiece(b"slot", source)],
            output,
            [Origin(b"slot", b"s", b"o")],
        )
        self.assertTrue(verify_witness(witness))

    def test_missing_origin_rejected(self):
        source = ExactRecord(Object(Structure({b"s"}), NoData()))
        output = ExactRecord(Object(Structure({b"o"}), NoData()))
        witness = ExactAssemblyWitness(DataKind.NONE, [ExactPiece(b"slot", source)], output, [])
        self.assertFalse(verify_witness(witness))

    def test_shipped_assembly_witness_decodes_and_verifies(self):
        witness = decode_witness((ROOT / "examples" / "assembly_witness.json").read_bytes())
        self.assertTrue(verify_witness(witness))
        self.assertEqual(decode_witness(encode_witness(witness), require_canonical=True), witness)

    def test_unexplained_output_position_rejected(self):
        source = ExactRecord(Object(Structure({b"s"}), NoData()))
        output = ExactRecord(Object(Structure({b"o", b"extra"}), NoData()))
        witness = ExactAssemblyWitness(
            DataKind.NONE,
            [ExactPiece(b"slot", source)],
            output,
            [Origin(b"slot", b"s", b"o")],
        )
        self.assertFalse(verify_witness(witness))


class EvidenceAndLiveTests(unittest.TestCase):
    def setUp(self):
        self.payload_record = ExactRecord(Object(Structure(), NoData()))
        self.payload_ref = reference_for(self.payload_record)

    def test_evidence_envelopes_only_link_exact_refs(self):
        claim = ClaimEnvelope(self.payload_ref, protocols={self.payload_ref})
        run = ExecutionEnvelope(self.payload_ref, self.payload_ref, inputs=(claim.claim,), outputs=())
        self.assertEqual(run.protocol, self.payload_ref)

    def test_genesis_transaction(self):
        locus = LocusRef(b"l")
        request = TransactionRequest(
            [Compare(locus, None)],
            [Write(locus, NextGeneration(self.payload_ref))],
        )
        state, result = transact(LiveState(), request)
        self.assertIsInstance(result, Committed)
        self.assertIn(locus, state.head_map())

    def test_conflict_changes_nothing(self):
        locus = LocusRef(b"l")
        request = TransactionRequest([Compare(locus, self.payload_ref)], [])
        original = LiveState()
        state, result = transact(original, request)
        self.assertIs(state, original)
        self.assertIsInstance(result, Conflict)

    def test_return_to_old_payload_creates_new_generation(self):
        locus = LocusRef(b"l")
        state, _ = transact(
            LiveState(),
            TransactionRequest([Compare(locus, None)], [Write(locus, NextGeneration(self.payload_ref))]),
        )
        first = state.head_map()[locus]
        state, _ = transact(
            state,
            TransactionRequest([Compare(locus, first)], [Write(locus, NextGeneration(self.payload_ref))]),
        )
        second = state.head_map()[locus]
        self.assertNotEqual(first, second)


class SchemaTests(unittest.TestCase):
    def test_registry_uses_absolute_ids_and_resolves_local_files(self):
        registry = json.loads((ROOT / "schemas" / "registry.json").read_text())
        self.assertTrue(registry)
        for uri, filename in registry.items():
            self.assertTrue(uri.startswith("https://"))
            schema = json.loads((ROOT / "schemas" / filename).read_text())
            self.assertEqual(schema["$id"], uri)

    def test_all_schemas_are_valid_draft_2020_12(self):
        try:
            from jsonschema import Draft202012Validator
        except ImportError:
            self.skipTest("jsonschema not installed")
        for path in (ROOT / "schemas").glob("*.schema.json"):
            Draft202012Validator.check_schema(json.loads(path.read_text()))

    def test_examples_validate_when_jsonschema_is_available(self):
        try:
            from referencing import Registry, Resource
            from jsonschema import Draft202012Validator
        except ImportError:
            self.skipTest("jsonschema/referencing not installed")
        registry_map = json.loads((ROOT / "schemas" / "registry.json").read_text())
        registry = Registry()
        schemas = {}
        for uri, filename in registry_map.items():
            value = json.loads((ROOT / "schemas" / filename).read_text())
            schemas[filename] = value
            registry = registry.with_resource(uri, Resource.from_contents(value))
        pairs = [
            ("empty_record.json", "record.schema.json"),
            ("parallel_record.json", "record.schema.json"),
            ("functional_record.json", "record.schema.json"),
            ("assembly_witness.json", "assembly.schema.json"),
            ("transaction.json", "live.schema.json"),
            ("evidence_assessment.json", "evidence.schema.json"),
        ]
        for example, schema in pairs:
            instance = json.loads((ROOT / "examples" / example).read_text())
            errors = list(Draft202012Validator(schemas[schema], registry=registry).iter_errors(instance))
            self.assertEqual(errors, [], f"{example}: {errors}")


if __name__ == "__main__":
    unittest.main()
