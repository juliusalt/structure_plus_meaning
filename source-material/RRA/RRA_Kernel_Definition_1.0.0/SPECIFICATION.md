# Relational Record Architecture Kernel

**Version:** 1.0.0  
**Status:** normative definition

## 1. Modules and conformance

The system consists of one mandatory module and five optional profiles.

| Module | Depends on | Public objects and judgments |
|---|---|---|
| Structure | — | finite structures, formation, equality, isomorphism, bounded views |
| Data | Structure | four data profiles and data-preserving isomorphism |
| Exact Artifact | Structure; Data | addressed records, exact identity, references, citations, canonical record profile |
| Assembly | Structure; selected Data profile | piece families, gluing, quotient, exact realization, K2 verification |
| Evidence Envelopes | Exact Artifact | exact linkage records without semantic force |
| Live Trajectories | Exact Artifact | loci, generations, atomic finite transactions, publications |

An implementation states the modules and data profiles it implements. It may add operations, indexes, caches, diagnostics, encodings, or domain protocols, but those additions are not judgments of this specification.

The words **must**, **must not**, **may**, and **exactly** are normative.

## 2. Common conventions

A finite set may be empty. A finite map is single-valued and has an explicit finite domain. A finite bag is a finite map to positive natural-number multiplicities. Octets are values in `0..255`; an octet string is finite.

An atom has equality and no other intrinsic operation. Atom spelling, allocation order, memory identity, serialization order, and host type have no structural meaning.

A relation is extensional: duplicate presentations of the same tuple do not create additional relation tuples. Multiplicity requiring independent occurrence identity is represented by distinct atoms. Multiplicity of opaque attached data is represented by a bag profile.

## 3. Structure module

### 3.1 Structure

A structure is

\[
S=(U,I), \qquad I\subseteq U\times U\times U,
\]

where `U` and `I` are finite.

For `(r,p,x) in I`:

- `r` is the relation occurrence;
- `p` is the participation occurrence in that relation;
- `x` is the reached occurrence.

All three coordinates belong to the same carrier. These readings identify tuple positions only. They do not create disjoint sorts.

A structure is **formed** exactly when every coordinate of every incidence tuple belongs to `U`.

No further formation condition is imposed. In particular, formed structures may contain:

- isolated atoms;
- cycles and self-incidence;
- relation-about-relation;
- repeated targets through distinct participation atoms;
- shared relation, participation, or target atoms;
- any finite incidence pattern.

Direction, role, order, headship, partness, scope, type, compatibility, logical force, authority, and truth are represented only by additional structure or by a separately named protocol.

### 3.2 Equality and structural isomorphism

Literal equality is equality of both finite components:

\[
(U,I)=(U',I') \iff U=U' \land I=I'.
\]

A structural isomorphism from `S` to `S'` is a bijection

\[
f:U\to U'
\]

such that

\[
(r,p,x)\in I \iff (f(r),f(p),f(x))\in I'.
\]

The specification does not choose a canonical representative of an isomorphism class.

### 3.3 Bounded views

A bounded view is `(S,b)` where `b` is a finite map from externally supplied boundary keys to atoms of `S`.

An isomorphism `f:S -> S'` preserves bounded views `(S,b)` and `(S',b')` exactly when

\[
\operatorname{dom}(b)=\operatorname{dom}(b')
\]

and

\[
f(b(k))=b'(k)
\]

for every boundary key `k`. Equal domains are required; an absent boundary key is not equal to a present one.

A boundary key is an argument of the particular view. It is not a stored kind, name, or property of the referenced atom.

## 4. Data module

A structured object is

\[
O=(S,D)
\]

where `S=(U,I)` is formed and `D` is one selected data profile over `U`. The profile is explicit even when `U` is empty.

### 4.1 No-data profile

`D=None`. No data occurrence is present.

### 4.2 Bag profile

`D` is a finite bag over pairs `(u,v)` where `u in U` and `v` is an octet string:

\[
D:U\times\operatorname{Octets}^* \rightharpoonup \mathbb N_{>0}.
\]

The multiplicity belongs to the pair. Individual equal data occurrences are not separately addressable.

### 4.3 Functional profile

`D` is a finite partial function

\[
D:U\rightharpoonup\operatorname{Octets}^*.
\]

At most one octet string is attached to each atom.

### 4.4 Node profile

`D` is a finite partial function

\[
D:U\rightharpoonup U\times\operatorname{Octets}^*.
\]

For `D(d)=(u,v)`, `d` is an individually addressable data-occurrence atom, `u` is its owner, and `v` is its opaque value. Both `d` and `u` belong to the structural carrier.

### 4.5 Data-preserving isomorphism

A structural isomorphism `f:S -> S'` preserves data when:

- no-data maps to no-data;
- bag multiplicities satisfy `D(u,v)=D'(f(u),v)`;
- functional bindings satisfy `D(u)=v` iff `D'(f(u))=v`;
- node bindings satisfy `D(d)=(u,v)` iff `D'(f(d))=(f(u),v)`.

Objects using different profiles are not data-isomorphic under this definition.

## 5. Exact Artifact profile

### 5.1 Addressed records

A local address is a finite octet string. An exact record is a structured object whose carrier atoms are local addresses.

Exact record equality includes exactly:

- the finite address set;
- the finite incidence set;
- the selected data-profile identifier;
- every data binding and multiplicity;
- every octet of every local address and data value.

Structural isomorphism remains a separate relation and may rename local addresses through an explicit bijection.

### 5.2 Exact artifact identity

The mathematical identity of an exact artifact is its complete exact record value. An identifier, digest, file name, storage address, or locator is not a second mathematical identity.

### 5.3 Record references

A record reference is an external token governed by a profile that supplies a resolver

\[
resolve(ref)=R.
\]

A conforming resolver must satisfy:

1. **single result:** a successful resolution returns one exact record;
2. **non-rebinding:** every later successful resolution of the same reference returns that same exact record;
3. **verification:** any digest or integrity field is checked against the complete canonical bytes required by its profile;
4. **explicit failure:** an unresolved or mismatching reference does not resolve to another record.

Several references may resolve to the same exact record.

The supplied `rra-record-json-1/sha256` reference form is an integrity-addressed profile. Exact record comparison remains decisive if a digest collision is alleged.

### 5.4 Citations

A citation is

\[
(ref,a)
\]

where `ref` resolves to exact record `R` and local address `a` belongs to `R`'s carrier.

A citation identifies the exact addressed occurrence in that exact artifact. It does not establish structural equivalence, type, continuity, ownership, authority, or truth.

## 6. Assembly profile

### 6.1 Piece family

A piece occurrence is `(s,O)` where `s` is a request-local slot and `O` is a formed structured object. A piece family is a finite map from distinct slots to objects, together with one explicit selected data profile. Every piece must use that profile.

Two slots remain distinct even when they carry equal objects. Piece-family order has no meaning.

For family `P`, the copied carrier is the disjoint union

\[
C_P=\{(s,u):s\in\operatorname{dom}(P),\ u\in U_{P(s)}\}.
\]

### 6.2 Gluing and quotient

A gluing is an equivalence relation `~` on all of `C_P`.

The abstract output carrier is the set of equivalence classes

\[
U_Q=C_P/{\sim}.
\]

For copied atom `c`, write `[c]` for its class. The quotient incidence is exactly

\[
I_Q=\{([(s,r)],[(s,p)],[(s,x)]):(r,p,x)\in I_{P(s)}\}.
\]

No incidence is added or removed except by extensional collapse after transport.

The selected data profile is transported as follows.

- **No data:** the output has no data.
- **Bag:** every copied `(owner,value)` occurrence is moved to its owner class; multiplicities mapping to the same output pair are summed.
- **Functional:** the quotient is defined exactly when all copied bindings whose owners enter one class carry the same value. That value is attached to the class.
- **Node:** the quotient is defined exactly when all copied node bindings whose node atoms enter one class transport to the same pair `(owner class,value)`. That binding is attached to the node class.

If a selected profile's condition fails, that gluing has no quotient object in that profile. The relational quotient remains defined.

The empty piece family has empty copied carrier, empty gluing, empty output structure, and empty data in its explicitly selected profile.

### 6.3 Exact realization

An exact realization of an abstract quotient is an exact output record `R` and a bijection

\[
\rho:U_Q\to U_R
\]

that transports and reflects the complete incidence and selected data profile. Abstract quotient classes are not local-address octet strings.

### 6.4 Compact assembly witness

A compact exact assembly witness consists of:

- the piece family;
- an exact output record `R` using the selected profile;
- one total map

\[
q:C_P\to U_R.
\]

It is valid exactly when:

1. every input object and `R` is formed;
2. `q` has domain exactly `C_P`;
3. `q` is surjective onto the complete output carrier;
4. the kernel `c ~_q d iff q(c)=q(d)` is the gluing;
5. the output incidence is exactly the pushforward of all copied input incidence along `q`;
6. the output data is exactly the profile-specific pushforward along `q`;
7. no other output atom, incidence, data binding, or data multiplicity is present.

The map `q` is both the compact quotient realization and the exact source-to-output occurrence correspondence. Its output-address spelling has no structural meaning.

### 6.5 K1 and K2

`K1(R)` holds exactly when `R` is a formed exact record under its selected data profile.

`K2(W)` holds exactly when `W` is a valid compact assembly witness under Section 6.4. K2 includes K1 formation checks for its exact-record inputs and output.

K1 and K2 do not check domain type, compatibility, completeness, proof validity, policy, permission, or authority.

## 7. Evidence Envelope profile

This profile records exact links among artifacts. It defines formation only.

### 7.1 Protocol specification envelope

A protocol specification envelope contains:

- one exact specification-artifact reference;
- finite dependency references;
- finite input-, output-, and context-profile references;
- finite executor or checker references.

### 7.2 Claim envelope

A claim envelope contains:

- one exact claim-artifact reference;
- finite protocol references;
- finite context, dependency, and provenance references.

### 7.3 Execution envelope

An execution envelope contains:

- one exact protocol reference;
- one exact executor reference;
- exact ordered input and output reference sequences;
- finite context, correspondence, residual, and provenance references.

It records that an execution is reported. It does not establish conformance.

### 7.4 Evidence, checker, trust, and assessment envelopes

An evidence envelope contains exact subject, evidence, source, correspondence, residual, and provenance references.

A checker-run envelope contains exact checker, subject, input, output, environment, and provenance references.

A trust-decision envelope contains exact basis, subject, purpose, decision-artifact, evidence, and provenance references.

An assessment envelope links finite sets of claim, execution, evidence, checker-run, trust-decision, result, residual, and provenance references.

Exactness of any envelope does not make a claim true, evidence valid, a checker sound, or a trust decision universally binding.

## 8. Live Trajectory profile

### 8.1 Loci and generations

A locus reference is an externally allocated opaque token with equality and non-rebinding identity. It denotes one live trajectory, not its current payload.

A generation is an exact immutable value

\[
G=(locus,predecessors,payload,dependencies,evidence)
\]

where:

- `predecessors` is a finite set of exact generation references;
- an empty predecessor set is a genesis generation;
- `payload` is one exact artifact reference;
- `dependencies` and `evidence` are finite exact-reference sets.

Generation identity is exact generation content. Reusing an earlier payload in a later generation does not reuse the earlier generation.

A live state contains:

- a finite partial map from loci to current generation references;
- an exact map from every locally retained generation reference to its generation value.

Every current head and every predecessor of a retained generation must resolve to its exact retained generation. The finite predecessor graph must be acyclic.

### 8.2 Transaction

A transaction request contains:

- `compare`: a finite map from loci to an expected generation reference or `Absent`;
- `write`: a finite map from loci to next-generation specifications;
- `domain(write) subseteq domain(compare)`.

A next-generation specification contains one payload reference and finite dependency, evidence, and additional-predecessor reference sets.

Transaction semantics are:

1. atomically observe every locus in `domain(compare)`;
2. if any observed head differs from its expectation, return `Conflict` containing the complete observed compare map and make no change;
3. otherwise, for every written locus create one generation whose predecessors are its prior head when present, union its additional predecessors;
4. retain all created generations and atomically replace all written heads;
5. return the exact created-generation references.

All additional predecessors must resolve in the pre-transaction state. A transaction has no partially visible success state.

### 8.3 Publication

A publication is an exact finite snapshot containing selected `(locus,current generation)` pairs and exact references to every protocol, execution, checker run, trust decision, policy, dependency, evidence item, and provenance item selected for that publication.

A publication does not perform ambient live lookup after formation.

## 9. Canonical JSON profiles

### 9.1 General rules

The supplied wire profiles use JSON only for addressed exact artifacts and profile records. Mathematical atoms and abstract quotient classes need not be serializable by this profile.

Canonical bytes are UTF-8 bytes of a JSON value produced with:

1. no insignificant whitespace;
2. object keys sorted lexicographically;
3. the separators `,` and `:` with no following spaces;
4. ASCII JSON escaping;
5. lowercase, even-length hexadecimal strings for every octet string;
6. arrays sorted by the profile-specific tuple order whenever their mathematical meaning is a set or bag;
7. no floating-point numbers;
8. rejection of duplicate object keys, unknown fields, malformed hex, duplicate set entries, unsorted extensional arrays, out-of-domain addresses, and profile mismatch.

A strict canonical parser must parse one complete JSON value, form the corresponding mathematical object, re-encode it canonically, and require byte-for-byte equality with the supplied bytes.

### 9.2 Exact record object

The canonical exact-record object is:

```json
{
  "data": { "kind": "none" },
  "format": "rra-record-json-1",
  "incidence": [],
  "positions": []
}
```

`positions` is a sorted set of hex addresses. `incidence` is a sorted set of three-address arrays. `data` has exactly one of these shapes:

```json
{"kind":"none"}
{"entries":[{"count":1,"owner":"00","value":"ff"}],"kind":"bag"}
{"entries":[{"owner":"00","value":"ff"}],"kind":"functional"}
{"entries":[{"node":"01","owner":"00","value":"ff"}],"kind":"node"}
```

Entries are sorted lexicographically by all non-count fields; bag count is the final comparison field.

### 9.3 Integrity reference

The supplied reference object is:

```json
{
  "algorithm": "sha256",
  "digest": "<64 lowercase hex digits>",
  "profile": "rra-record-json-1"
}
```

Its digest is computed over the canonical exact-record bytes.

### 9.4 Compact assembly-witness object

The `rra-assembly-witness-json-1` object contains exactly `format`, `data_kind`, `pieces`, `output`, and `origins`.

- `pieces` is a set encoded in ascending slot order. Each entry contains one hex slot and one exact-record object.
- `origins` is the complete source-to-output map encoded in ascending `(slot,source,target)` order.
- `output` is one exact-record object.
- `data_kind` equals the profile of every piece and the output.

A strict decoder validates the object shape, constructs the compact witness, and applies K2. Canonical byte acceptance additionally requires exact re-encoding equality.

### 9.5 Generation object

The canonical `rra-generation-json-1` object contains exactly `format`, `locus`, `predecessors`, `payload`, `dependencies`, and `evidence`.

The locus is lowercase hex. Every reference set is encoded in ascending `(profile,algorithm,digest)` order. The payload is one reference object. Canonical generation bytes use the general rules of Section 9.1.

Transaction and publication JSON objects use the schemas in `schemas/live.schema.json`. They are exchange representations of supplied requests and frozen publications; the state transition in Section 8.2 remains authoritative.

## 10. Conformance boundary

A module implementation conforms exactly when every exposed result agrees with the corresponding mathematical definition on every formed finite input in its declared domain.

The following are not conformance outputs unless an additional profile says otherwise:

- storage layout and file names;
- algorithm, traversal, and allocation order;
- cache contents and invalidation sets;
- diagnostics and timing;
- host-language types;
- canonical representatives of structural isomorphism classes;
- protocol meaning, proof validity, trust, or truth.

A private decomposition of a checker is an implementation choice. Only the complete public K1 or K2 result is a judgment of this specification.
