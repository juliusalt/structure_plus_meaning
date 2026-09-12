# Decisions and reasons

The current owner's request governs this reconstruction. Earlier generated
documents supply evidence of direction, including where they attribute words
to the owner; those attributions do not elevate their details above the current
request. Isabelle checks statements relative to definitions. Alignment of those
definitions with the intended system remains a separate review obligation.

The standing owner rule of 2026-09-12 prohibits outside semantics, reasoning,
or anything else anywhere. The owner explicitly preserves Isabelle/HOL's
normative bootstrap role through genesis. Earlier ad hoc outside-reasoning
permissions provide no current exception; the complete instruction and
bootstrap boundary are in DEVELOPMENT_WORKFLOW.md.

Each choice below records its reason and its limits. Proof references are added
only after the corresponding theory is accepted.

The owner corrected the presentation requirement on 2026-09-08. That correction
supersedes every earlier single-grammar or quotation-principality requirement,
including historical expectations recorded below. The active requirement is
exactness of admissible presentations and of their intrinsic relations and
composition throughout the system. Existing proofs of recovery, construction,
and transport remain evidence for their stated classes and boundaries.

## Source and build boundary

The theory source uses Isabelle symbol escapes. This is a source representation
choice, with no mathematical force. The delivered spelling failed to parse in
Isabelle2025-2; normalization exposed further proof errors.

The delivered top-level theories and explanatory files are preserved in
source-material/bootstrap-delivered.zip. They are design provenance, not an
additional active foundation. validation/delivered-sources.sha256 identifies
their original bytes.

tools/build.py records the Isabelle version, command, source hashes, exit code,
and log. A failed invocation cannot produce an accepted receipt. A successful
build does not establish that every requirement of the reconstruction is met.

## Data transport

Counted anonymous attachments and functional attachments have different
transport equations: counts add over a gluing fibre; equal functional values
coalesce, and unequal values conflict. The multiplicity-one encoding must be
tested against transport, not only against static values.

The reconstruction retains the two transport equations. Replacing a functional
attachment by a counted occurrence changes a valid equal-value gluing into a
count of two. Adding payload-occurrence identities would also change the
anonymous bag boundary; adding a merge-mode discriminator would move the same
distinction to a new field. Retaining the two components introduces neither
change. This is a choice over the stated attachment and gluing boundary, not a
claim to have ruled out every possible structural encoding.

The plan's unqualified legacy round-trip requirement also needs a boundary:
deleting the old profile tag maps no-data and the empty functional profile to
the same new basis. The reconstruction preserves recovery within each legacy
view, with that view explicit in the migration account. It does not restore a
profile discriminator inside the new core to preserve this discarded distinction.

## Presentation exactness, including quotation

The owner's correction requires each notion to constrain its admissible
presentations so every admitted member is exact. Required material,
distinctions, and intrinsic relations are preserved; unsupported facts and
semantic rules are not introduced. Presentation structure is permitted and
accounted for. "Notion" is an informal word here, not a primitive kind.

This applies throughout citation, binding, environment, assembly, derivation,
retention, quotation, semantic definition, and the higher system. The
presentation account must also preserve and reflect each intrinsic link.
Individually exact presentations do not supply a composition theorem. Structural
compatibility and the shared boundary must be explicit and proved.

No intrinsically privileged topology or principal grammar is required.
Functional recovery in a declared class and canonical construction remain
useful local properties. Choosing that class and proving those properties
does not establish an exclusive presentation choice. The plan and obligation
ledger now state these amended requirements.

## Assembly output

Pieces and a complete origin map determine the output carrier, incidence, and
data. The output-determination proof therefore licenses making that output a
derived projection of the witness, instead of retaining a duplicated field.
Construction applications still state the exact output being judged and compare
it with the derived value. This removes redundant storage without identifying
the application, its witness, and its result.

## Local structure and exact identity

Agreement on an incident star preserves recognition that reads only that star.
It does not preserve an exact anchor whose artifact component contains additional
structure: changing that exterior changes the exact artifact value. A semantic
locality statement must therefore retain every exact artifact value it observes,
as well as its structural and environment dependencies. The reconstruction keeps
local pattern invariance and exact identity invariance separate. It also states
formation preconditions explicitly when comparing two containing artifacts.

## Underdetermined choices

The current request authorizes reasoned choices with an explicit review record.
It supersedes earlier generated instructions to leave every such choice for
prior owner approval. Choices will be resolved against structurality,
explicitness, non-conflation, irredundancy, and non-nominality, and recorded here.

## Scoped environments

An environment is a finite graph of artifact-use occurrences and outgoing local
slot bindings. Equal artifact values may occupy different uses. Disjoint
composition labels the input uses as separate copies; merging identified uses
requires agreement of both their artifact values and their slot targets. This
extends the assembly discipline to dependency boundaries without making an
artifact's identity depend on its environment.

Environment closure is relative to an explicitly supplied complete demand set.
It checks exact slot coverage and reachability from the supplied roots. The
structural recognizer must derive that demand set; closure of a freely chosen
set alone does not establish semantic closure. Cycles of finite citation
bindings are not prohibited here. Restrictions on meaning recursion belong to
the definition and dependency layers.

Whole-artifact targets are retained alongside occurrence anchors. The empty
formed artifact has no occurrence anchor, so eliminating whole-artifact targets
would exclude a structural value that assembly already produces.

## Citation geometry

The citation grammar uses equality of tuple positions to distinguish local and
external references, with separate whole-artifact and occurrence forms. Local
references reach an atom directly. External references reach a scoped slot, and
an occurrence form also reaches a leaf containing its target address. Roots
have no attached data; address leaves carry exactly one functional value.
Incoming incidence is part of the explicit relative footprint.

These are chosen and stated structural patterns. Their constructor names exist
only in the recovered mathematical projection. Their admission rests on local
self-citation without a self-value, explicit external bindings, representation
of the empty artifact, functional recovery, and complete local data and incidence
boundaries. This does not assert that these conditions uniquely determine every
possible quotation grammar. A shape can participate in different structural
views when a supplied application selects those views; no intrinsic nominal
kind is assigned to an occurrence.

## Record order and family multiplicity

A record's complete field incidence already identifies every socket. A finite
successor path through exactly those sockets determines the first and last.
The reconstruction therefore uses only links between consecutive sockets:
a separate header, numeric position, and terminal marker would store facts
recoverable from the complete path. Empty and singleton records need no order
links. They share their encoding with the corresponding family because there
is no additional order information to represent.

Families expose the socket-to-endpoint relation, rather than only its range.
Distinct sockets reaching one endpoint remain distinct. Field order is recovered
only when successor incidence supplies it. These grammars are explicit admitted
views, with exactness and composition required over their declared boundaries.

## What the representation audit establishes

`RRA_Representation_Audit.recoverable_encodings_need_not_be_isomorphic`
constructs a formed addressed object with every carrier atom exposed at its
boundary. Rotating each incidence triple is reversible on all formed finite
objects. It preserves the complete carrier, every attachment, and every boundary
binding, and has exactly one output incidence per source incidence. The original
and rotated example nevertheless admit no atom isomorphism.

Thus recovery, complete material accounting, and boundary fixity do not force
one presentation topology. Copies preserving each primitive incidence
coordinate and data attachment through an explicit carrier correspondence form
one useful declared class. `RRA_Data.bounded_copies_agree` proves that two such
copies of one bounded object are isomorphic with their boundary preserved.

The owner's correction removes the demand to make this class intrinsically
privileged. Other presentations may preserve the same required content through
different explicit correspondences. Their admissibility depends on exactness
for the represented notion and its intrinsic relations, including composition.
Reversibility alone supplies no theorem about those linked relations.

This result is not reflective adequacy. A compiler between distinct source
languages still needs a meaning-preservation proof, and bootstrap reflection
still needs independently defined public relations and a concrete internal
implementation. No uniqueness of arbitrary record or citation grammars is
claimed.

## Generation values and scoped predecessors

A generation core contains its exact locus, finite set of direct predecessor
cores, exact payload, and exact recorded cause. Direct predecessor membership
has no order or multiplicity: repeating an identical edge adds no fact.
Its structural family therefore must give a bijection from its sockets to those
predecessor cores. This restriction applies to succession; it does not remove
repeated occurrences from general families or premise boundaries.

The recursive reader preserves the use occurrence selected by a predecessor
citation. Projecting first to an artifact value and then choosing any use of
that value would conflate distinct environments. A core is independent of
containing and selecting artifacts once its resolved fields are fixed.
A local whole-artifact citation does observe its container, so changing that
container can change a field; an unconditional invariance claim would be false.

Cause recording establishes a formed exact target and its structural citation.
It does not establish base admission or validate a construction account.
The later cause judgment must make that join. Evidence and adoption are absent
from the core datatype and from generation recovery.

Injective renaming of use occurrences preserves the recursively recovered core.
The map carries every source and target use together while preserving artifact
values and local addresses. Separate finite generation presentations can be
combined using fresh uses in one fixed unbounded carrier. Equal artifact values
do not cause their outgoing scopes to be merged.

## Snapshots, publications, and transactions

A snapshot stores selected generation cores, with at most one per locus. Its
locus graph is derived from the locus already present in each core. A general
selection may contain multiple generations at one locus; snapshot formation
adds the functional selection condition without claiming currentness.

A transaction supplies expected selections, expected absence, proposed
selections, and proposed absence. Expected and proposed locus graphs are
derived, avoiding repeated locus fields for selected cores. Removing a selection
is allowed and does not remove or alter a generation. Every changed locus must
be compared. Conflict returns the complete observed comparison graph and no
output snapshot. Success supplies the complete replacement, with all other
lookups preserved. Succession and cause validity are separate later joins.

A publication view consists of a snapshot and exact dependency and evidence
selections. The view is recovered at a supplied artifact use and root.
Equal views do not identify presentation sites. Evidence selection does not
establish proof validity, and publication formation establishes no adoption.

## The four-relation bridge

The supplied Factor signature is supported by a structural view with five
ordered fields: one complete carrier family and four complete binary-relation
fields. Each relation is the headed incidence at its selected field occurrence.
The carrier family preserves isolated source occurrences. The complete encoding
accounts for every auxiliary socket, every incidence, and all data; this legacy
class has empty attached data because its source signature has none.

The encoding uses disjoint copies for original atoms and construction sockets.
Those copy constructors occur only in the mathematical construction account.
The recognizer does not inspect them: it reads record order and incidence.
Encoding recovery, injectivity on formed sources, and injective transport are
proved. The source's ownership and successor restrictions are retained in a
separate conformance predicate. Other native Factor grammars may use the full
RRA incidence and data basis.

The local matching theorem compares complete incident stars. It requires an
injective correspondence on the declared pattern carrier and fixes every
external pattern atom. Its image may sit in a larger target, but every target
incidence touching the mapped interior must come from the pattern. The encoded
interior includes each source interior atom and its carrier socket. Record
scaffolding remains at the fixed boundary.

This makes explicit a gap in the source package's pointwise matching equation:
checking only tuples whose endpoints lie in the proposed image cannot detect an
extra incoming edge from outside that image. Its prose also requires complete
boundary accounting. The reconstruction adopts that complete-star reading and
proves transport for it, rather than claiming that the weaker pointwise test
already enforces it. The incoming-edge counterexample is checked in
`Factor_Structure`. `four_star_match_transport` proves both directions for every
formed four-relation source and target, including the retained legacy class.

## Reader-specific environment closure

A dependency is required by a structural read, rather than by the mere presence
of a citation-shaped subgraph anywhere in an artifact. RRA_Citation_Closure
derives requested slot bindings and observed uses from complete citation
requests. Its restriction preserves interpretation and scoped locations and is
the least sub-environment supporting those requests.

RRA_Generation_Dependencies supplies a concrete enclosing grammar. It recovers
the four record fields, requests their citations and every predecessor-family
endpoint, and recursively follows the predecessor locations. Locus, payload,
and cause targets are exact data observations; their contents are not
automatically read as further generations. The read sites and requests are
finite. Restriction preserves the exact cores, and reading the restricted
package produces the same sites, requests, and slot demands. Closure is therefore
checked against the restricted package's own grammar-derived boundary.

RRA_Publication_Dependencies applies the same discipline to all three
publication fields. The complete families determine every direct citation;
only snapshot citations start recursive generation reading. The publication
source is retained even when all families are empty. Dependency and evidence
targets retain their exact artifacts without automatically reading their
outgoing bindings. The restriction preserves the complete publication view,
is closed from its source use, and derives the same requests and slots on
rereading. Every included environment that still reads the publication
contains this restriction. The corresponding generation theorem now also
derives leastness from successful generation readings, without asking a caller
to supply their request set.

The generic citation utility does not let a certificate choose a sufficient
subset of requests. Each other public reader must similarly establish its
complete requests. Generation closure is proved; it is not evidence that the
remaining Factor and reflection readers have already been implemented.

Slot renaming moves structural occurrences and their environment keys. Opaque
remote address operands remain fixed, and the corresponding environment slots
must still supply the same exact target artifacts. Structural transport is
proved for all citation forms. External target identity is preserved under that
boundary; local citations instead refer to the readdressed containing artifact.

## The initial term quotation class

Factor_Terms introduces mathematical terms made from exact targets and ordered
pairs, with finite variable scopes for generic patterns. Constants retain the
entire exact target, including any structure and sharing inside its artifact.
Variable renaming fixes those constants. Instantiation, substitution, and an
infinite family of formed future terms are proved independently of truth.

The initial native reader uses external citation leaves and ordered pair
records. External citations keep literal target identity independent of the
artifact carrying the quotation. Its pair interiors are disjoint; this is a
tree quotation class, not a claim that every native RRA graph is a tree.
General RRA citations, including local self-citation, remain available.

The reader uniquely recovers the term, interior, and external slots. Every
formed term has a finite native representation and an environment closed over
exactly those slots. The witness source contains precisely the quotation
interior and the literal slots. Child prefixes choose fresh concrete addresses;
the reader does not test their bytes. Injective position maps preserve the
reading when the used syntax observations and exact external artifact values
agree. A remote occurrence address remains unchanged as an opaque operand.

These results establish this term presentation class and its stated transport
boundary. They do not admit a complete semantic basis or discharge every
intrinsic link. Total representability does not require all presentations of the
same term to have isomorphic complete carriers. The presentation and
candidate-form audit remains a separate obligation.

## Generic positive schemas and finite derivations

The current positive class has finite interfaces, identified clause occurrences,
and identified premise sockets. A schema's complete fields determine its
variable scope and direct callees. A binding assignment produces one conclusion
and one complete premise graph. Distinct sockets remain distinct when their
instantiated calls agree. An interface checks application formation separately
from whether any clause establishes that application.

Meaning is the least fixed point of the positive consequence operator. This is
one explicitly admitted mathematical recursion mechanism; arbitrary circular
truth selection is not supplied. A system with no premise-free instance has
empty meaning. The finite equality example accepts diagonal pairs of all formed
future terms without listing those arguments in the system. Native quotation
covers each such argument, and native package recovery plus a concrete equality
program are proved. General native program construction is supplied by the
closed-package compiler described below.

The set iterated by this operator is the extension of true calls. An argument's
context or resource structure is part of its term and is not that set. The
representation introduces no operation that edits those argument structures.
The full audit of premise topologies and candidate semantic forms is still
required before claiming the intended complete semantic basis.

A finite derivation tree stores a clause occurrence, complete variable
bindings, and complete child bindings. The claimed call is a separate input.
The selected schema and bindings determine each expected child call, so the
certificate does not repeat those calls or the conclusion. Soundness and
completeness against positive meaning are proved independently of artifact
realization and evidence retention. The checker is primitive recursive in the
finite tree; executable checks for every node condition and complete native
realization remain separate obligations. This layer is named Factor_Derivation;
generic replay will additionally require realization and retention.

## Native scopes, schema recovery, and pattern construction

A scoped pattern records a binder-family root and a pattern root. The binder
family is diagonal: each binder occurrence is also its family's endpoint. It
has no headed incidence or data, and the declared set must equal the variables
used by the complete pattern. A schema similarly records its scope, conclusion
pattern, and complete prospective-premise family. A definition records its
scoped interface and complete clause family. These readers recover their
projections uniquely and invoke no truth predicate.

A prospective call resolves its callee through its actual citation and supplied
artifact use. This location is retained in the schema projection. Complete
definition-package recovery must establish that every such location contains
an admitted definition; a formed occurrence citation alone does not establish
that fact. Clause and premise family sockets remain distinct when their
endpoints or recovered values agree. Sharing an endpoint is explicit incidence.

Every formed finite pattern now has a native scoped representation. Construction
assigns binders injectively into fresh positions, copies syntax positions while
fixing those shared binders, and adds a fresh enclosing record and binder family.
The selected byte prefixes are construction coordinates; no reader inspects
them. The complete resulting carrier consists of the recovered interior and
literal slots, and its finite environment is closed over exactly those slots.
The use type in this existence theorem is an unbounded address space, so each
finite package can retain as many distinct exact literal targets as it needs.

## Native positive packages and exact dependency closure

A root citation family selects definition sites. Each site includes its artifact
use and local root. The reader follows every callee in every recovered clause,
and package formation requires a native definition at every reached site.
Reachability is a set used for dependency analysis; the original root, clause,
and premise families keep their distinct socket occurrences.

Structural source uses and interpreted slots are separate derived boundaries.
An empty root family still requires its source artifact even though it requests
no citation. The generic `read_environment` helper therefore takes both source
uses and slots. The native grammar supplies them by traversing all record
fields, family members, pattern leaves, and prospective callees. It does not
scan an artifact collection to select definitions.

The resulting restriction is finite and closed from the package root, recovers
the identical program, and derives the same boundary on rereading. Every
smaller included environment that still reads a valid package must retain all
of this material. A formed extension retaining that restriction recovers the
same interfaces, clauses, and callee sites. Literal target artifacts are exact
data values; their contents are not automatically evaluated as definitions.

Native ground applications recover a definition citation and term argument,
then use the recovered interface for formation. Their positive truth is the
independently defined least fixed point. No proof or evidence field enters it.
Closing the program leaves future argument material in its supplied containing
environment. The program's finite environment does not bound future arguments.

These results concern the admitted positive schema class. They do not yet admit
the other candidate semantic forms, prove complete native presentation
construction, complete the presentation exactness and composition audit, or
implement reflection.


## The positive class does not supply structural observation

Factor_Positive_Parametricity makes a capability boundary explicit. A formed
finite system without material premises contains finitely many exact literal targets. Mapping every
ordinary target operand through a formation-preserving function that fixes those
literals preserves admitted instances and positive truth. An involution gives
equivalence. The proof preserves every binder, definition, clause, and premise
socket occurrence; it does not identify the changed exact artifact values.

For any such program, a fresh address supplies two formed singleton artifacts
with identical carrier and data. One has no incidence; the other has a loop.
Neither is a program literal, and the program gives their whole-artifact terms
the same answer. Thus no finite positive system defines incidence nonemptiness
over all future formed artifacts. This rules out treating positive schemas alone
as the complete structural foundation.

The required addition must expose the actual carrier, incidence, and opaque data
of an ordinary argument through a stated structural equation. A relation-name
dispatcher or arbitrary truth callback would not close this gap. Candidate
view forms still need an admission and representation argument. Direct opaque
payload terms will first extend the quotation domain: a payload leaf uses the
already recognized single functional attachment and has no headed incidence.
This exposes the existing data basis as an ordinary value; it assigns no meaning
to its bytes and introduces no new RRA primitive.


## Complete material equations and direct opaque values

The material observation primitive checks an independently supplied exact
artifact against four complete finite tables. Carrier, incidence, and functional
entries have no duplicates; anonymous attachments retain their exact counts.
The resulting object equals the supplied source in every primitive component.
Existence is proved for every formed exact artifact, including the empty case,
and removing an incidence is rejected. This closes the proved observation gap
without an arbitrary reader or truth callback.

The tables are supplied as explicitly ordered term enumerations. The observation
accepts every ordering with the same complete content. This is a stated rule of
this relation, not an order of the source artifact or a foundation-wide exchange
rule. Each carrier entry links its address as an opaque payload to its exact
occurrence anchor. This bridge is needed to relate an occurrence citation's
address payload to the addressed target. Bytes do not select operations.

Payload terms use the existing single functional-attachment leaf and have no
headed incidence. Target citations, payloads, and pairs have disjoint structural
readings. Their total native constructions, binder-aware pattern constructions,
quotation transport, and environment restriction are proved. This extends the
ordinary argument domain without introducing another RRA data primitive.

Schemas now contain identified call sockets and identified material sockets.
Their domains are disjoint, and the variable scope contains exactly the variables
used by the conclusion and both kinds of premise. Instantiation remains separate
from truth. The same generic consequence operator admits an instance only when
every material equation holds and every cited recursive call is in its argument
set. The operator is still monotone; proof soundness and completeness and
dependency locality remain valid.

One finite schema has truth exactly on whole-artifact terms with nonempty
incidence. The nonempty pair pattern belongs to that schema. Neither meaning nor
the derivation checker contains an incidence-specific branch. The opacity theorem
now explicitly identifies the subclass without material premises. Complete native
premise-family integration is now proved. A 43-occurrence native incidence
program is recovered from a closed finite environment; its native future calls
have exactly the stated meaning and leave that program environment unchanged.
General native program construction remains separate.


## Future arguments preserve existing binding environments

The concrete use carrier is the unbounded type `local_address option`. Each
finite existing environment reserves its actual use occurrences. An imported
finite package has one distinguished boundary use, `None`, carrying the exact
artifact selected at an existing use. It supplies no outgoing binding there.
The existing environment may supply any formed outgoing bindings at that use.
All other imported uses are placed fresh by an injective map. The resulting
merged environment preserves every old artifact and every old binding.

The distinguished optional value and the fresh prefix are construction
coordinates. They are not stored kinds or semantic selectors. Repeated
construction takes the resulting finite environment as its next input, so
later calls receive further fresh use occurrences in the same carrier.

A call package meets this boundary condition: its callee target is at the
distinguished use, while all its bindings belong to the separate call source.
After placement, its actual citation targets the existing callee use and
address. Native application recovery, the original interface, and independent
meaning all commute with this construction. The least closed program
environment is exactly equal before and after extension, not merely equivalent
on one query. This applies to existing programs with outgoing bindings and
closes the limitation of the earlier zero-binding examples.

These are argument extensions. The foundation-transition mechanism and its
authority conditions are still separate unfinished obligations.

## Shared scopes and explicit resource arguments

Finite pattern bodies are composed by injective copies that agree only at silent
binder occurrences. The composition adds no intermediate constructor headers.
Fresh record headers then recover their actual ordered fields, so every added
occurrence contributes to the native record. This gives arbitrary finite pattern
vectors and complete material records; it is not yet a general program compiler.
A material record is relative to the binder boundary supplied by its enclosing
schema. Independent complete scopes must be copied with their private binders
renamed, rather than merged at this shared boundary.

An application may carry a resource structure as an ordinary term. The native
equality program gives formed counterexamples to implicit weakening, contraction,
and exchange of that term, with identical recovered program environments. Hence
there is no foundation-wide rule preserving truth under those edits. The positive
operator still checks all identified call sockets conjunctively; its monotone
semantic approximation is not an application resource context. Particular
definitions may deliberately admit resource edits, and these counterexamples do
not claim universal linearity.

## Copying bodies against the final reference environment

A finite auxiliary use contains one source body and pulls back the destination's
actual bindings along its proposed syntax map. It preserves every existing
artifact and binding. All its external targets are existing uses; local variable
citations acquire the destination use and copied address. This establishes the
complete native transport conditions directly, including when an external call
becomes a self call in the destination. There is no assumed semantic-reader or
truth-preservation callback.

This construction supports a finite mixed list of call and material bodies
under one shared binder scope. Each body's recovered premise, interior, and
slot set is preserved. Separately, exact inverse maps show that binder and
socket renaming both preserves and reflects complete rule instances and
interface acceptance. These results do not yet constitute a general native
program constructor or settle presentation exactness and composition.


## Finite schema construction and its reference boundary

The enclosing schema uses fresh structural record and family positions generated
from the actual finite body carrier. It adds the complete binder declaration and
one premise socket for each body occurrence, including repeated bodies and the
empty family. It preserves all headed reads on the old carrier and all old data.
Construction coordinates do not act as constructor tags.

The native projection is an injective change of binder and socket coordinates
from the source schema. Complete supported rule instances are preserved and
reflected for every support relation and argument, including every material
check. The generated reference tables are finite, functional, disjoint in their
slots, and confined to the source carrier. Their callee range is exactly the
source schema's dependencies. A concrete environment constructor installs those
references at previously unbound slots, with fresh uses for exact literal values.

Every formed finite schema now has an actual native quotation over any formed
environment supplying its callee anchors. Compilation adds a fresh code use and
preserves every artifact and binding at every old use. Callee-free schemas need
no initial package. Whole definition and program construction and presentation
exactness and composition remain separate obligations.

## Independent clause scopes and fixed definition construction roots

Complete schema blocks use ordinary injective copies of every position. The
binder-fixing constructor remains appropriate within one schema, where all its
bodies share a declared scope. It cannot be used to combine separately scoped
clauses or an interface with those clauses. `RRA_Syntax_Forests` proves disjoint
private copies and complete preservation of their structural and data reads.
`Factor_Reference_Forests` gives every copied reference a source and preserves
its literal value or callee site.

The definition constructor fixes its enclosing root at the empty local address.
This permits a future finite program constructor to assign callee sites before
constructing artifact values, including in cycles. The other header coordinates
are construction choices; native recognition still depends on the structural
record and family geometry. `Factor_Definition_Encoding` proves total syntax and
actual-destination recovery for arbitrary formed interfaces and complete clause
lists. It does not yet construct a closed mutually recursive program environment.

Compiler metadata and `schema_code` collect proved facts about concrete syntax
and reference tables. They are used in construction proofs, not stored as extra
native fields. `schema_alpha_variant` requires explicit injective binder and
socket maps and literal structural equality after renaming. Its preservation
of rule instances is proved independently of the native code reader.

## Total closed native compilation and recursive references

Every formed finite positive schema system now has a total compilation to a
closed native package. Definition identities are first moved injectively to
finite native use occurrences with empty local roots. Every callee occurrence
uses that same map. Interface, binder, premise-socket, and clause-family
coordinates are then handled by the existing structural constructors.

All definition artifacts are preallocated before their references are installed.
The finite installation theorem permits self calls and mutual recursion and
preserves earlier reference values. A separately constructed structural citation
family selects the complete source definition set. The existing grammar-derived
dependency restriction produces a canonical closed environment; closure is proved
after actual native recovery.

The finite `definition_code` record is construction metadata: an artifact,
reference requirements, and proved projections used in the existence proof.
The native syntax and environment retain their existing fields. The compiler
does not add projected interface or clause fields to a native artifact.

Independent semantic results compare interface acceptance and complete clause
rule instances. Private renaming leaves the consequence operator equal on every
support relation. Injective definition relocation commutes with that operator
over the complete source definition boundary. Least-fixed-point meaning then
corresponds exactly. These results include every supported complete material
premise; neither derivations nor compiler-produced truth claims are assumed.

`Factor_Compiled_Applications` proves the whole connection for future arguments:
one closed compiled program, actual native call syntax, the source application
boundary, source positive truth, and exact preservation of all existing program
artifacts and bindings. An empty source system is also representable, without
inventing an exported definition or a call.

## Construction accounts and semantic permission

The source boundary separates an ordered list of input occurrences from a finite
functional graph of base entries. Input positions preserve repetition; a base
key is a different source class. A construction stores one source and selected
carrier for each piece occurrence, together with the complete assembly origin
graph. Piece material and output assembly are derived. Supplying a base graph
alone does not prove program permission.

Factor_Construction proves that these complete source accounts are exactly the
K2 assemblies whose pieces have sources at that boundary. Every output atom
has an explicit source occurrence, selected atom, piece occurrence, and origin
edge. RRA_Fragment reconstructs each selected or omitted source. An additional
incidence partition is necessary: the proved three-atom example selects every
atom in separate pieces while omitting their connecting incidence. Carrier
coverage is therefore not used as incidence completeness.

Construction permission is a derived conjunction of structural admissibility
and a positive call on the complete account. The chosen definition and active
program remain explicit semantic inputs; this does not yet supply an authority
or continuation policy. The argument includes ordered inputs, base graph,
selection graph, origin graph, and exact output. Residuals and provenance are
derived, avoiding competing stored accounts.

The former argument used lexicographically sorted ordinary terms for finite
sets and functional tables. The owner identified that Factor programs can
observe this order. The previous claim that sorting added no semantic order was
incorrect: exact recovery does not establish invariance of permission under
another enumeration. Input-list order is intentional and is a separate issue.

Factor_Finite_Presentations now admits every complete enumeration, including
recursive presentations of table values. Factor_Construction_Presentations
covers all base, selection, and origin row orders and all selected atom-set
orders. It proves unique recovery and formation for the entire presentation
class. The sorted functions remain convenient finite construction witnesses.
They do not occur in the definition of factor_constructs.

Interpreting a selected definition as unordered construction permission now
requires its interface acceptance and positive truth to agree on all complete
presentations of each valid account. This requirement is exactly equivalent to
both judgments factoring through the recovered account. It is a derived
admissibility property of the existing program, not another consequence rule.
Under it, any supplied presentation, an existential presentation, and every
presentation give the same permission. Choosing only an existential or only a
universal closure for an order-sensitive program would instead impose a new
policy about which arrangements pass; that choice has not been smuggled into
the construction relation.

Native claim reading now accepts every complete presentation and uniquely
recovers its account and quotation boundaries. Native construction applications
preserve existing artifacts, bindings, and the canonical program environment;
their formation and truth agree across presentations under the explicit
invariance condition. Compilation preserves that condition through its proved
interface and meaning correspondence. A finite output-checking program has a
closed native representation and satisfies it. A finite exact-term recognizer
accepts one ordering of a valid two-base account and rejects another, and is
therefore rejected as unordered permission.

A single derivation of one ordered term does not prove this admissibility
condition. Its native admission-evidence mechanism remains open, together with
the generic replay and retention join. No higher-layer completeness claim rests
on treating that open work as an implicit oracle.

## Finite proof graphs and exact assertions

A derivation graph stores identified inference or assertion occurrences and one
functional socket-to-child discharge graph. It stores no node judgment or
assumption list. The supplied root call and each inference's actual clause and
complete variable bindings determine the prospective premises. A complete
functional reading assigns one call to every node, so all incoming edges to a
shared node require that same call.

Assertions are explicit graph nodes with no supplying proof. A missing discharge
does not assert a premise. The assumption projection keeps assertion identities:
equal calls at two assertion nodes remain two entries. Conditional soundness
requires the projected assertions to be true, while a closed proof has no
assertion. The equality example proves that a formed conditional assertion can
fail to be a closed proof. The recovered node and assumption maps are unique for
the supplied program, graph, and root call.

Closed graph completeness is obtained from the existing tree certificates,
without adding a proof rule. Construction coordinates pair a subtree with its
required call; this prevents an equal subtree used for different calls from
being accidentally merged. The entire reachable closure is finite by strict
certificate-size descent and finite branching. Flattening retains every node
and socket edge, and introduces no assertion.

These construction labels have no interpretation in the graph validator.
Injective readdressing on the actual finite node set transports every recovered
claim and assumption. Thus every positive judgment has a closed graph with
formed local-address coordinates. This remains an abstract certificate result:
native structural realization, complete retained boundaries, and the executable
finite replay checker are still separate obligations.

For native program references, a local clause, binder, or socket coordinate is
paired with the use of its owning definition. This derived program view
preserves the independently fixed positive meaning and all application
boundaries by the existing private-coordinate equivalence theorem. Keeping the
use is necessary: equal artifact values can inhabit distinct semantic
environments. No additional field is attached to native artifacts.

## Native proof records and recovered retention

An inference uses the existing structural record geometry with three fields:
a clause citation, a complete binding table, and a complete premise-link table.
An assertion is an explicit empty record. Recognition distinguishes those forms
by their field structure. It stores neither a conclusion at every node nor an
assumption list. The root call and independently admitted clauses determine
those projections during derivation validation.

A binding row reuses the existing two-field site-and-term application reader.
That reader recognizes syntax without testing call formation or truth. Premise
rows contain two occurrence citations and preserve both target uses and local
addresses. The table accounts for every physical row, requires distinct decoded
keys, and derives its interior and reference slots. Thus two rows with the same
key are rejected even when their values agree. Distinct premise keys may reach
one proved subgraph.

Native graph nodes are actual use-and-address sites. Factor_Realization proves
that their entire node set is exactly the closure of the native premise links
from the supplied root. Their kinds, bindings, and complete discharge graph
recover uniquely. These are recognition and no-extra results for this grammar;
total native construction from arbitrary formed abstract graphs is still open.

The graph's source uses and every locally demanded reference slot determine a
finite closed retained environment. Restriction preserves exact source artifact
values, target uses, the entire recovered graph, and its complete demand set.
Repeating the restriction has no further effect. This boundary covers the proof;
generic replay must also retain the selected program and root call. Retaining
opaque literal values does not silently retain or interpret their outgoing
bindings.

Every premise-link table is already an RRA evidence envelope with the same
complete family of physical link occurrences. Its exact-target projection is
proved from the actual citations. A second stored envelope or a fixed list of
certificate links would repeat that evidence. Factor still uses the located
projection: equal artifact values at different uses can have different bindings,
which the exact-target envelope projection alone does not recover.

## Assertion occurrences preserve premise multiplicity

The v6.1 assumption-boundary discussion exposed a defect in the first graph
formation rule: two different premise sockets could reach one assertion node,
while the assumption projection counted that node only once. Formation now
requires the derived assertion-to-premise-use graph to be functional. Every
non-root assertion has exactly one such origin, and each premise use identifies
at most one assertion. Repeated assumptions therefore require separate explicit
assertion occurrences, even when their calls are equal.

This restriction concerns unproved boundary uses. Proved subgraphs may be shared
by several premise occurrences. The existing closed completeness construction
contains only inference nodes and still satisfies the strengthened formation
rule. Injective node renaming transports the assertion-use graph exactly. No
stored origin field or implicit assumption registry is introduced.


## Observable ordering in finite-field serialization

The owner's inspection exposed a semantic defect in Factor_Finite_Terms and its
former use by Factor_Construction_Claims.factor_constructs. sorted_list_of_set
selects an ordered pair term; the former permission applied directly to it.
A fixed native equality program distinguishes two orders of the same entries.
The set/table injectivity results do not prove representation-independent truth.
The correction now accounts for every complete presentation and proves that an
admitted unordered permission depends only on its complete unordered projection. Merely
changing the enumeration algorithm or recording its name would leave that
obligation open. Ordinary ordered arguments retain their explicit order.


## Complete native metadata table construction

Native proof binding and premise-link tables now have total construction for
every finite functional relation with formed terms and addresses. A complete
family supplies one physical socket per row. Unique row recognition and
injective recovered keys identify every supplied row with the actual decoded
family. Private copying accounts for all interiors and exposed slots; reference
profiles preserve the actual target uses. Empty tables need no extra case tag.
These are syntax-and-recovery results for proof metadata. They do not establish
representation-independent truth for a program given an ordered serialization.

## Complete native proof realization

A valid finite proof graph now has a complete native realization. Every clause
citation, binding key, and premise socket is an actual occurrence in the
selected native program. Graph topology alone does not imply this: the
requirements are derived from the existing derivation checks against the
located program. Assertions require an explicit empty record and no outgoing
premises. Inferences require a clause citation, complete bindings, and complete
premise links. The node stores no conclusion or assumption list.

The constructor places one artifact at each fresh proof-node use, constructs
all node artifacts before installing their references, and preserves every
old artifact and binding. Its injective node map retains sharing and distinct
assertions. All constructed positions belong to an interior or an exposed
reference slot. The native reader recovers exactly the complete graph reached
from the proof root. This placement is an existence construction, not a
restriction requiring every native proof to use one artifact per node.

Physical copying fixes all program sites and term values. A type-variable
collision in the generic table-copy lemma had accidentally restricted table
values to the destination use type; separate type variables now preserve the
intended independence, and both binding and premise-link tables instantiate it.

Every positive native application has a realized proof with no assumptions,
while its selected program environment stays identical. This closes the native
construction gap for the supported positive graph class. The combined
retention/replay boundary is addressed below. Native admission evidence,
general presentation exactness and composition, and the final alignment audit
remain open.

## Generic replay and its exact retained boundary

The program, application, and proof readers now determine a combined finite
source set and every demanded slot. Restriction preserves all three readings
and the exact targets of their references. It is closed from the actual
selected roots, stable on rereading, and included in every retained
subenvironment supporting the same readings. The three semantic roles do not
impose three evidence links: the number and targets of links come from the
actual grammar and may share uses or targets.

Replay is a derived conjunction of native program/application/graph recovery,
independent derivation validity, and closure at this exact demand boundary.
It is generic over the complete application argument. Its assumption boundary
is unique; assertions receive no truth from being retained. Conditional
soundness needs those assertions to hold, and closed replay establishes native
positive truth. Every positive native call has a closed replay preserving its
complete argument and canonical program environment.

Construction certification lives in a separate theory. It adds the complete
construction account and the selected program's presentation-invariance
condition to closed generic replay. The permission judgment is then recovered
by soundness rather than asserted twice. Different proof roots do not alter
account identity, and every admitted presentation receives a retained
certificate. This still requires an explicit admission property: replaying one
ordered argument does not prove invariance over all presentations. Checking
admission evidence inside Factor remains open.

These proofs establish the mathematical joins and total native realization.
They do not establish termination of an executable replay checker. That work
needs complete finite representations of the data, including the counted
attachment function, and an algorithm proved equivalent to these judgments.


## Finite execution values and checking

The abstract data basis contains an arbitrary HOL function constrained to have
finite support. Its formedness does not itself supply an algorithm for
extracting that support or comparing two such functions. Executable checking
therefore receives complete finite values: a multiset for anonymous attachments
and finite sets for functional bindings, carrier occurrences, incidence, and
environment relations. Decoding preserves every count and exact value.
Injectivity proves that equality of these finite values is exactly equality of
the represented records; existence proves coverage of every formed artifact
and environment. Neither a digest nor an isomorphism class replaces identity.

These are implementation representations with proved recovery, not additional
native syntax or semantic primitives. Finite-set and multiset enumeration order
does not enter their equality. This differs from supplying an ordered ordinary
Factor term to a program: the construction-permission invariance obligation
continues to apply there. The mathematical inverse used in coverage proofs is
not exported as a procedure for inspecting arbitrary HOL functions.

Formation and identity checks now compile to SML. Finite targets, terms, and
patterns have exact decoders, and their checks agree with the existing
judgments even on malformed finite inputs. Interface matching gathers the
bindings encountered during structural descent; the functional-binding check
rejects inconsistent repetitions of a variable. The recovered binding relation
is contained in every successful matching witness and has exactly the pattern's
variable domain.

Material observation reads the actual supplied enumeration terms. It checks
source equality, the complete carrier and incidence sets, every anonymous
multiplicity, and every functional binding. Set fields reject repeated entries;
anonymous repetitions retain their counts. All admitted enumeration orders are
checked through the same complete artifact equation. Structural recursion and
finite library operations give total computations, and Isabelle has accepted
both their equivalence proofs and SML compilation checks.

Complete finite schemas and programs now retain every interface, identified
clause, call socket, material socket, and binding. The checker rejects missing
callees, conflicting fields, unused bindings, and incomplete premise domains
under exactly the existing formation and instance judgments. Material terms
are constructed from the supplied finite bindings and literal subterms, with
a proof that every abstract instance occurs among those candidates. This is
finite instance construction; it does not search for positive truth. All these
checks have accepted equivalence proofs and SML compilation checks.

Finite proof-graph formation now checks every node and discharge, complete
root reachability, well-foundedness, and assertion origins. The reachability
computation uses a bound derived from the supplied edge count and is proved
equal to complete transitive closure. Graph decoding is injective, including
every binding. Inference sharing remains allowed; unproved assertions retain
their distinct premise origins. SML compilation and equivalence to the existing
graph-formation judgment are accepted.

Complete graph validity now has an executable check. The identified discharge
links and child claims recover the exact prospective premise relation by a
relational join. Every node is checked against that relation. A finite
transition relation, derived from the actual inference metadata and program
clauses, computes all candidate claims reachable from the supplied root call.
The full reading check then accepts exactly when an abstract reading exists.
The transition index uses the node and definition because the fixed binding
metadata determines its child terms; the correspondence theorem proves this
index sufficient and preserves every complete claim.

The computed table equals the unique reading whenever one exists. Assertions
remain identified occurrences in its derived boundary, and closed checking
requires that boundary to be empty. Validity forces the actual metadata and
claim terms to be formed. Every valid abstract proof graph therefore has an
exact finite representation, with no additional restriction on sharing or
binding values. These equivalence and coverage theorems are accepted, and the
complete graph checker compiles to SML.

Native records, families, and citations now have executable recovery. Record
recovery first checks the actual number of headed incidences against the
grammar's arity. It then tests candidates from precisely those incidences
against the complete successor and data equations. The unique surviving order
is the represented order. Families recover their actual complete socket graph.
Citation candidates come from actual incidence and functional payloads; exact
recognition recovers their interior. Environment lookup separately recovers
complete target values and target use locations, preserving their distinction.
These readers cover every corresponding abstract reading and compile to SML.

Recursive native term and pattern recovery now also compiles to SML. The
reader checks the complete record, child interiors, and external slot boundary
at each pair. Every child interior is a strict subset of its parent interior,
so the actual source carrier supplies a sufficient recursion bound. The
correspondence theorem covers every admitted finite quotation; a separate
chosen depth limit does not determine which terms or patterns have meaning.

Local citations read variables only from the supplied scope. Complete scoped
recovery derives that scope from its actual diagonal family, checks that its
declarations equal the body's variables, and retains the whole declaration,
record, and body interior. Literal targets continue to preserve their exact
external values. Both the recursive readers and the complete scoped wrapper
have accepted uniqueness, coverage, and correspondence proofs.

Ground and prospective native calls now have executable readers with accepted
coverage, uniqueness, and correspondence proofs. Both recover the actual
dependency use and definition position. Their common record join checks the
whole interior and external slots; prospective calls retain the supplied
variable scope. Reading a call remains separate from checking its interface
formation or truth.

Complete native material premises now recover all five ordered operands.
The vector reader preserves each actual field and checks the disjoint syntax
interiors and aggregate external boundary. The enclosing record also checks
its complete frame and variable-scope separation. Every admitted material
reading has a finite representation with exactly the same boundaries. These
call and material readers compile to SML.

Complete native premise and clause families now have executable recovery.
Every actual socket must have a reading, and the recovered relation must have
exactly the actual socket domain. The mixed family is checked as one relation
before its call and material rows are separated. Distinct sockets remain
distinct when their endpoints or recovered values are shared. Empty families
are included. Prospective-call families are the case with no material rows.

Native schema recovery follows the actual three ordered fields and requires
the declared scope to equal all variables used by the conclusion and mixed
premises. Definition recovery joins the complete scoped interface with the
complete identified clause family. These readers preserve the existing native
conditions, cover every admitted reading, return uniquely determined values,
and compile to SML. The generic family correspondence explicitly requires
unique endpoint readings; it does not choose among ambiguous interpretations.

Native package recovery now enumerates only the supplied artifact positions,
recovers every readable definition and prospective dependency, and follows
those dependencies from the actual root citation family. The candidate positions
bound the computation; the roots and recovered callees select the program.
Every reached site must supply a definition, so a failed reading cannot erase
the obligation to read that site. The recovered interfaces and identified
clauses equal the complete native program. Positive dependency cycles and empty
root families are included. Correspondence, coverage, uniqueness, and SML
compilation are proved. Citation use locations remain distinct from exact target
values, and executable recovery does not establish native grammar admission.

Located citation and two-endpoint link readers now compile to SML with exact
correspondence, coverage, and uniqueness. They preserve the actual target use
and position, the whole citation interior, and every external slot. The two
link endpoints may denote one site while their physical interiors remain
distinct. The existing call-record join supplies the link geometry without
adding interface or truth checks. These are the rows needed by complete proof
binding and premise tables.

Complete binding and premise tables now have executable recovery with exact
correspondence, coverage, uniqueness, and SML compilation. The computation
retains all readings at every actual socket, requires a functional row relation
with exactly the actual socket domain, and separately rejects duplicate keys
across distinct row occurrences. Equal values do not excuse duplicate keys.
It checks the pairwise row interiors, the enclosing family frame, and the
complete interior and external slot boundary. The generic correspondence
requires coverage of all abstract rows and injective value decoding; it does
not require a global uniqueness premise that would narrow the native table
judgment. These tables recover metadata for the independent inference check.

Proof-node recovery now uses the explicit empty assertion record and the
three-field inference record. Every inference retains its actual clause site,
complete binding table, and complete premise-link table. The enclosing record,
field interiors, and external slots satisfy exactly the native geometry.
Correspondence, coverage, uniqueness, and SML compilation are proved. Reading
the node metadata remains separate from checking its claim against the program
and its exact premises.

Proof-graph recovery now retains every metadata row at every site reached by
following native premise references back from the selected root. Its complete
node and discharge fields equal those of every native graph at that root.
The existing graph-formation check selects the result; no additional admission
condition is introduced. Missing nodes, cycles, and repeated use of one
assertion occurrence fail that check, while inference sharing remains.
Correspondence, coverage, uniqueness, and SML compilation are proved.

Finite environment closure checks the complete binding graph, root inclusion,
reachable uses, and exact demanded-slot domain. Retention keeps exactly the
structural sources and the targets of demanded bindings. Citation requests
recover their demands from their actual records, including partial inputs.
All three operations have exact correspondence and compile to SML. The grammar
still determines the requests and demands; these operations do not supply them
as an arbitrary validity certificate.

Program-demand traversal now projects the slots from complete pattern, scoped
pattern, call, and material-premise readings. It then follows actual family
endpoints, schema fields and scopes, and definition fields. Partial reads
remain visible when an enclosing schema or definition fails its full formation
conditions, exactly as in the existing dependency relation. The root family
and recursive definition dependencies determine the package's source uses.
Executable sources, demands, and package retention coincide with their
mathematical definitions on all finite inputs and compile to SML.

Executable replay retention now joins the program demands, the application's
complete external slots, and the proof-node demands. Each proof-node demand
must match that graph's exact metadata and premise table. Sources, demands,
and the computed environment coincide with the mathematical replay boundary.
The result preserves all three readers, is closed from their roots, and is
contained in every included environment preserving the same readings. These
results require no derivation or truth premise and compile to SML.

The complete native replay checker now takes the finite environment and the
program, application, and proof roots. It recovers all three structures,
qualifies program coordinates by their owning use, computes the graph's claims
and exact assertion occurrences, and checks grammar-derived closure. Its
output is equivalent to native replay, every native replay on a represented
environment is covered, and the assertion boundary is unique. Closed replay
implies native positive truth. The full computation compiles to SML. It checks
a supplied proof and does not decide arbitrary positive truth or establish
native grammar-admission evidence.

The bounded recursive term and pattern
implementations can repeat work on malformed cyclic records; a finite table
refinement that preserves their coverage remains an identified improvement.


## Extensional families and seeded closure use the existing language

Finite exact tuple families become ordinary premise-free clauses, with one
clause occurrence per source tuple occurrence. The complete family remains
explicit even when different occurrences carry equal tuples. The operator and
meaning are proved to be precisely family membership, and the empty family
retains its interface. This is exact term comparison; it does not identify
distinct exact artifacts by isomorphism. Native compilation constructs one
closed program serving every future formed term.

Finite seed addition uses disjoint clause occurrences and exactly the existing
interfaces. Every seed must satisfy its target's formation boundary. The actual
new consequence operator is the union of the seed calls and old consequences,
so its independently defined meaning is precisely their least closure. A seed
defines a clause in this new program, rather than certifying an old truth.
Already-true seeds give identical meaning. The resulting system also has native
compilation. This reduction covers finite positive schema steps, not an
arbitrary external semantic callback.

The premise-free schema constructor is now polymorphic in unused socket and
callee coordinate types. Those empty fields do not justify a unit-type
restriction or a duplicate constructor. The candidate and dependency verdicts,
including their remaining scope limits, are recorded in ADMISSION.md.

## Incidence queries use complete material equations

One ordinary finite schema now queries a chosen incidence of any future formed
artifact. Every actual incidence can be placed first in a complete enumeration;
conversely, the material equation makes the first entry an actual incidence.
All remaining incidence and data stay in the equation. The existential choice
of a complete enumeration grants no permission to edit an ordinary supplied
argument. The four source relations are observations at their actual ordered
record heads, with exact positive-meaning equations. Their wrapper-depth codes
are therefore unnecessary as primitive observers.

## Views are definitions over explicit existing dependencies

A finite view now adds one fresh definition with its own interface and complete
clause family. Every prospective callee belongs to the old formed system.
Dependency locality proves that all old calls and truth values remain exactly
the same. The new meaning is interface acceptance and one applicable clause
whose entire premise family holds in the old meaning. Material equations and
shared variables use the ordinary schema rules. A singleton prospective family
supplies a fixed projection; larger families supply conjunctions.

This construction has native compilation and exists over an unbounded
coordinate carrier. It adds no privileged view registry or truth dispatcher.
It also does not erase arbitrary source graph material: a branch with a
formation or identity role must retain that role. The source's particular
wrapper grammar is not required to express these capabilities.

## Cause validation keeps the selected reference use

The cause join follows the generation record's actual citation, including its
target use. Choosing an arbitrary use of an equal artifact would discard
meaning-bearing bindings. The cited application must present the complete
construction account, its chosen definition must supply admitted construction
permission, and the exact output must equal the generation payload. Formation
alone does not establish these facts; a closed formed counterexample is proved.

Factor_Certified_Cause adds replay of that same application. It proves the exact
join with independent cause validity, and changing proof roots cannot change
the recovered account. No evidence is added to the generation core.

This exposes an identity boundary: an artifact-and-address target
does not itself contain its outgoing reference bindings. The current cause
judgment therefore states its environment explicitly and claims uniqueness
there. It does not infer global account identity from equal bare application
targets under different environments. The recorded profile below supplies the
whole resolved scope before making that stronger claim.

## Exact values can be quoted without external bindings

Payloads and pairs form an existing sublanguage whose quotation reads no target
citations. Its native construction has exactly its quotation interior and no
external slots. A separate data-list profile uses an empty payload terminator,
because the earlier enumeration profile terminates with a cited empty artifact.
The new profile changes no ordinary term constructor or meaning rule.

Complete artifact data includes all original addresses, ordered incidence
triples, repeated counted attachments, and functional attachments. Every
complete enumeration is admitted and uniquely recovers the exact value.
Environment data includes every artifact-use row and every scoped binding.
Equal artifact values do not merge distinct uses, and binding cycles are finite
data rather than recursive value expansion. Native option-valued use coordinates
are encoded injectively as finite words of natural components; this imposes no
byte restriction on the mathematical use coordinates.

Every formed environment of this native construction class has a complete
self-contained quotation. Its recovered value is independent of the outer
reference environment. Grammar-derived minimality, cause validity, and semantic
invariance across different presentations are further judgments; representation
alone establishes none of them.

## Program-and-call scope is independent of proof retention

Factor_Judgment_Retention combines exactly the program and application readers'
source uses and demanded slots. Its restriction preserves both readers, truth,
and the exact canonical program environment. It is closed from the actual
program and call uses, unchanged by rereading, and included in every retained
subenvironment supporting the same readings. These theorems require no proof
graph or evidence premise.

The application slot and restriction lemmas previously lived in
Factor_Proof_Restriction. They have moved unchanged to
Factor_Application_Retention, whose imports now need only presentation
restriction and future applications. Proof restriction imports that independent
result. This removes an unnecessary dependency from the cause's scope boundary.

## Recorded causes contain their complete minimal scope

Factor_Complete_Data_Quotation restricts standalone data quotations to complete
copies of their payload-and-pair syntax, under every formed injective
readdressing. Its ordinary native reader is derived. This excludes ignored
attachments as well as unused carrier positions. The theorem concerns this data
profile; it does not claim exactness and composition of every other
presentation class.

Factor_Judgment_Values quotes a whole environment and its actual program and
call sites. Factor_Recorded_Cause follows the generation's citation to this
self-contained value, checks the recovered native construction judgment, and
requires the environment to equal its grammar-derived least restriction.
It checks the exact payload and retains all source occurrences and origins.
No proof boundary is included.

Equal recorded cause targets now determine equal scopes and construction
accounts even under different outer environments. Any presentation of the
same generation core preserves recorded cause validity. Different accounts
require different cause targets. Every existing native construction judgment
has a recordable scope with its exact program environment preserved.
Factor_Generation_Construction supplies the actual generation presentation as
a further join.

The complete-data root theorem now removes the cause quotation's separately
stored root coordinate. The recorded profile cites the whole scope artifact;
its structure uniquely recovers the root, full environment, and both inner
sites. This choice applies P-3 over the complete standalone data profile. The
general occurrence-target form and the bare application cause reader still
retain their explicit occurrence boundary: that broader domain does not have
this whole-artifact root-recovery theorem.

The actual generation's citation ensures that the whole cause artifact is
present in its environment. Its complete native data reading requires no
external slots. The encoded inner environment still retains every binding
needed to judge the cause; no enclosing binding is substituted for it. Base
and construction generation witnesses use this whole-value cause profile and
retain their separate certificates. Their invalid-cause counterexample uses
the empty artifact, which cannot carry a complete quotation. Whole-artifact
cause syntax alone no longer supplies the reason for invalidity.

The import audit also exposed a finite-derivation adequacy theorem in the raw
construction-presentation theory. Its statement and proof now live in
Factor_Certified_Construction. The presentation theory imports positive meaning
directly, and Factor_Cause imports only construction presentations, native
meaning, and the generation reader it uses. Raw construction permission and
both recorded cause profiles therefore have no derivation, replay, or evidence
dependency. Their finite derivation and retained certification results remain
available above that boundary.

## Recorded construction certificates preserve the exact scope

Generic replay construction now preserves the exact least program-and-call
environment and includes it in the retained proof environment. Equality of
that scope follows from its leastness under formed environment extension.
The earlier replay results continue to hold.

Factor_Certified_Recorded_Cause reads the stored scope before considering
evidence. It checks the program and call grammar in that scope, retains it in
the separate proof environment, and checks the construction certificate there.
Certification entails the independent recorded cause judgment. Every valid
recorded construction has such a retained certificate. Equal causes determine
equal accounts across different proof contexts and roots, and a new presentation
of the same core preserves its certification.

The admission condition for unordered construction permission remains explicit.
These results do not treat a proof of one serialized call as evidence for that
universal condition.

## Actual generation construction preserves all declared boundaries

RRA_Generation_Frames constructs the four field roles through actual record
incidence and places a complete unordered predecessor family in its second
field. RRA_Generation_Construction installs each predecessor citation at the
supplied existing use and address. Three separate literal bindings provide
the locus, payload, and cause. All old artifacts and bindings are retained.
The choice of finite layout supplies a witness for the existing generation
grammar; it changes neither that grammar nor predecessor identity.

Injective use transport and fresh composition allow every finite predecessor
family to coexist. Induction over the finite core then supplies an actual
presentation for every formed generation, including the empty predecessor
case. The grammar-derived restriction gives a closed presentation of the same
core. This establishes total coverage and unique recovery for the declared
class. The remaining presentation obligation concerns complete exactness and
the generation's intrinsic links to its predecessors, payload, and cause,
under the owner's amended requirements.

Factor_Generation_Construction combines that result with the minimal recorded
scope and separate certificate. Every admitted native construction can be
recorded as an actual generation at a stated formed locus with a stated finite
set of formed predecessor cores. The construction input occurrences, active
semantic dependencies, and historical predecessors keep their own boundaries.
Their admissible relationship is a continuation policy, not an identity
equation imposed by the representation constructor. No adoption or base
admission is inferred from this existence result.

## Base declarations use the existing exact literal form

Factor_Base_Cause interprets a base declaration as a selected native
definition applied to the whole-artifact literal of the payload. The existing
positive meaning supplies admission. No base truth rule or callback is added.
The artifact is supplied directly as an exact target, so this argument needs
no chosen enumeration. Formation and admission agree across all native
quotations recovering that literal under the same program and definition.
The universal admission condition for serialized construction accounts remains
separate and has not been waived.

The generic cause-location reader has moved unchanged from Factor_Cause into
RRA_Generation_Dependencies. Factor_Generation_Scopes now owns exact scope
recovery and the common minimal-scope quotation theorem. Construction recording
uses that theorem as well. The raw base reader has no dependency on construction
validity or evidence theories.

A recorded base declaration uses the same complete minimal scope profile as a
recorded construction. The literal argument and construction account have
different existing structures. Factor_Generation_Causes proves that equal
recorded causes cannot change roles across outer environments; no additional
role field is needed. Its cause-validity relation is the derived union of the
two profiles. A formed generation with an invalid cause remains possible.

Base admission does not impose an equation on historical predecessors. This
choice keeps the source of a payload separate from its historical placement;
the continuation policy must specify the admissible relationship. The empty
predecessor family supplies the initial case. Factor_Base_Programs gives a
concrete finite native policy admitting exactly one selected artifact, with
formed calls for every future formed payload and unchanged program material.
Under an explicitly selected such policy, every formed payload has a certified
initial generation at a stated formed locus.

Factor_Certified_Base_Cause checks separate retained replay while preserving
the recorded scope. Certification entails independently defined base validity
and exists for every valid recorded declaration. This existence does not select
or adopt a policy on behalf of an authority.

## Generation and publication values are complete data

Factor_Target_Values copies the complete exact artifact and its optional
occurrence coordinate. The existing coordinate encoding now lives in
Factor_Coordinate_Values and is shared with environment-use coordinates;
the encoding itself assigns neither role. Whole artifacts and occurrences
remain distinct, and occurrence formation still checks carrier membership.

Factor_Generation_Values recursively quotes all four exact core fields.
Predecessors use the existing finite-collection presentation relation, which
admits every complete order and every permitted member presentation.
Factor_Publication_Values retains the selected snapshot, dependencies, and
evidence targets in the same way. All these values have complete finite native
quotations without external slots and recover their source values uniquely.
Equal publication views do not identify different native presentation sites.

Factor_Site_Values supplies a complete environment-and-site quotation.
Factor_Publication_Scopes applies the publication reader to those recovered
data and requires its complete closure. The stored scope is exactly its own
least publication restriction. The decoded view is derived, not stored again.
Thus an exact quotation fixes the actual publication site, all meaning-bearing
bindings needed to read it, and its view across outer environments. An exact
artifact target alone would omit these bindings; a decoded view alone would
omit the presentation site. The shared finite site-coordinate representation
is also used in existing program-and-call quotations, with the same data
layout as before.

Every formed publication view now has an actual closed native presentation.
The constructor places complete citation families inside an explicit record.
Snapshot citations bind to the existing generation uses, preserving their
recursive reference environments even when artifact values coincide. The
other two families read exact dependency and evidence targets. Finite distinct
lists choose construction layouts only; all selections are recovered through
the existing incidence readers. Empty fields use the same construction.
The grammar-derived restriction removes unrelated environment material and
keeps the complete view. No authority or cause-validity premise enters this
construction.

## Raw adoption and publication-relative currentness

The raw adoption argument contains authority, generation, and purpose. Authority
and purpose are exact targets used in those positions, with no intrinsic force
assigned to their names or coordinates. A supplied ordinary positive definition
decides adoption. Admission of that definition as a policy on these data
requires both interface acceptance and truth to agree across every complete
presentation. This is equivalent to factoring through the exact subject data;
it does not admit a chosen serialization as a semantic distinction.

Adoption can precede or exist without publication. Currentness separately
requires an exact closed publication scope and selection of the adopted
generation at the supplied locus. The actual native program and application
retain the meaning boundary; the publication retains its own environment and
site. The locus is recovered from the selected core. Cause validity, evidence,
and derivation are absent from the raw authority layer's imports and judgments.
Policy-admission evidence checking remains a higher obligation.

The general native compiler preserves this policy admission as well as the
ordinary formation and truth boundaries for every future argument. Its finite
closed package stays fixed when actual future calls are added; all existing
artifacts and bindings stay fixed too. Two premise-free ordinary programs have
broad interfaces and respectively accept or refuse every complete adoption
argument. A third inspects the exact optional occurrence coordinate of the
purpose. That parameter is ordinary explicit policy data, with no privileged
coordinate. All artifact and generation collection presentations have the same
formation and truth.

Actual native applications now exhibit adoption of a generation with an
invalid recorded cause and refusal of an actual certified base generation.
Both kinds of application are formed, and refusal uses a policy whose
presentation invariance is proved. The identical authority, generation, and
purpose can receive opposite decisions under these supplied programs. Cause
and certificate imports enter only the independence theory above the policy
layer. This proves that exact subject equality has no program-independent
adoption force; authorization of cross-foundation interpretations still needs
its own explicit transition judgment.

Adoption scopes now quote the minimal judgment environment and its two sites.
The actual application recovers authority, generation, and purpose; the record
adds no duplicate subject fields. The generic scope-recording theorem belongs
below both generation causes and authority. Exact quotation targets fix the
whole scope independently of any enclosing environment.

The separate certification join requires the admitted policy, complete subject
presentation, and closed generic replay. Replay soundness establishes the
adoption decision. Every adopted call can acquire a retained certificate
preserving both its program environment and its entire minimal judgment
environment, and every complete permitted future presentation has a
certificate. Certified currentness retains the same separate publication
scope and selection. A concrete retained adoption certificate still accepts
an invalid generation cause: the certificate proves this program's decision,
not the subject's cause validity. Native checking of policy-admission evidence
remains open.

Actual publication and policy witnesses now vary currentness independently
while holding the exact generation fixed. The same positive adoption applies
to a closed publication selecting that core and to an actual empty publication;
only the former supplies currentness. Holding one actual selecting publication
fixed, two formed admitted policy applications give opposite currentness
decisions. A retained currentness certificate can select a generation whose
recorded cause is invalid. These joins introduce no new field into the core.

Data quotations supply inspectable material for later judgments. They do
not validate causes or selected evidence, recognize currentness, or authorize
adoption. Their recovery theorems also do not assert that an arbitrary program
ignores presentation order. Any semantic use which claims to depend only on
the represented value must establish that further invariance.

## Complete program and currentness scopes remain inspectable data

A program-scope quotation stores its complete finite environment and selected
site. The native package reader derives the program, and closedness entails
that the stored environment is exactly the minimal program scope. There is no
second stored program field. Every actual package, including an empty one,
has such a quotation. Retaining that scope in a formed future environment
preserves the program and the formation and truth of arbitrary actual future
calls; their arguments need not lie inside the recorded program environment.

A currentness frame has two ordinary data fields: a complete program-and-call
scope and a complete publication scope with its site. The raw value establishes
neither role. The currentness reader checks adoption under the actual program,
selection in the exact closed publication, and the minimal judgment boundary.
Authority, generation, and purpose come from the call; the locus comes from
the generation. They are recovered fields rather than duplicate stored data.
Every currentness judgment has a finite complete frame quotation preserving
its original publication scope. Equal quotation targets fix both environments,
all sites, and the whole subject independently of any enclosing bindings.

These records provide the complete program and currentness data required by a
future predecessor-relative amendment judgment. Their formation and recovery
do not authorize succession, select a universal acceptance program, validate a
transition certificate, or supply a cross-version interpretation bridge.
Those conditions must still be stated and checked by the amendment mechanism.

## Whole program payloads recover their quotation root structurally

The existing base and construction accounts apply to a whole artifact. A
complete program-scope quotation also has a selected quotation root. Treating
address `[]` as an implicit payload root would privilege a coordinate, while
storing another root field would be redundant if the structure determines it.
The complete payload-and-pair syntax does determine it: exactly one carrier
position occurs in neither the second nor the third incidence projection.
That position is the quotation root, and the property is preserved by every
admitted injective readdressing. Equal complete artifacts therefore determine
equal roots and equal recovered data, even when the roots were not supplied
as equal premises. This theorem concerns the complete data profile; it does
not impose tree structure or distinguished roles on arbitrary RRA artifacts.

The chosen generation profile uses the complete program-scope artifact as its
whole payload. Its root, complete minimal environment, actual program site,
and native program are recovered rather than stored again. Identical payloads
recover identical programs even in different formed generation cores. Their
locus, predecessors, and cause remain separate content and still distinguish
those cores. Complete currentness frames recover the selected program through
their generation, keeping the adoption program and selected program distinct.

Every actual native program has such a payload and an actual closed initial
generation admitted by a supplied finite base policy, with separate retained
certification. An existing admitted construction of a program-scope payload
also produces an actual closed generation preserving the complete account and
certificate. Conversely, every actual program can be carried by a formed
generation whose cause is invalid. These joins establish payload identity
and coexistence with the existing cause profiles. They do not choose a
genesis authority, authorize amendment, or validate a transition certificate.

## Continuation keeps structural success and semantic permission separate

The ordinary continuation argument has four positions: the before snapshot,
the structural transaction, an independently claimed after snapshot, and
submitted material as a complete environment with an actual selected site.
The advancement join checks the claimed after snapshot against the structural
comparison and replacement result. Keeping this claim independent lets the
same ordinary judgment inspect a proposal even when comparison fails, without
manufacturing a successful structural transition.

The material position is deliberately grammar-neutral. A policy may inspect
construction accounts, dependency scopes, authority frames, or certificates
there, but must state the corresponding requirements itself. Complete quotation
retains every binding; a bare artifact would omit this information. No evidence
validity callback or built-in amendment protocol is supplied. This is a choice
of a general submission boundary for the underdetermined continuation profile.
Foundation amendment must add its specifically enumerated material and exact
predecessor authority frame in its own higher join.

Snapshots retain complete exact generation cores and their recursive histories.
The transaction keeps its four existing independent fields. All finite
collections admit every complete presentation, and a continuation definition
must preserve both interface acceptance and truth across them. An exact native
call uniquely recovers the whole subject. The active program still comes from
its actual package and dependency environment. Removing required material from
a subenvironment prevents every continuation reading at that package site,
regardless of the histories or other data supplied as arguments. The general leastness theorem is now supplemented by an actual witness. A
nonempty program receives a complete external root selector. An independently
placed generation scope contains a successor and an ancestor whose exact payload
is a definition artifact of that program. An admitted native policy permits
advancement on that history. The compared environment omits exactly one binding
required by the program selector while retaining every artifact, the identical
native call and argument, and the entire history scope with all its bindings.
No program can be read at the stated package site after the omission. Having
the definition artifact available historically therefore cannot reconstruct its
missing semantic reference. The omission is a comparison of two supplied finite
environment values, not an authorized update to a foundation.

Two actual finite pattern policies accept and refuse every complete continuation
argument with formed interfaces and proved invariance. Their native applications
exhibit refusal of structural success and permission on conflict. The latter
still fails the advancement join. These programs are witnesses, not selected
universal policies. Historical predecessors, semantic dependencies, ordered
construction inputs, and authority decisions are never equated by this layer.

One common native application extension theorem now supplies the existing
compilation, construction, adoption, and new continuation results. It preserves
all old artifacts and bindings and the exact canonical program environment.
A fixed finite compilation preserves every continuation argument. Generic scope
quotation records its complete minimal judgment environment without duplicating
the subject. Separate replay certifies every permitted call or complete future
presentation while preserving that program and judgment scope. The submission
inside the argument and the certificate of this judgment remain distinct.
Policy-admission evidence checking and the foundation amendment protocol are
still open.

## SK adequacy uses an ordinary finite program

The active SK program stores three definitions and nine ordinary schemas.
Term membership has the two constant clauses and application closure. One-step
reduction has the K and S clauses and both application contexts. Finite reduction
has reflexivity and a step followed by an already established finite reduction.
Every clause retains its complete binder and premise-socket boundary. Recursive
SK membership is positive meaning; all three declared interfaces accept a
formed Factor term. Thus a query outside the SK argument shapes has a false
answer. This broad interface is an explicit choice, independently of the
proved exact answer relation.

The source encoding uses the opaque payloads `[]` and `[0]` for the two
combinators and an ordinary pair for application. These are explicit literals
in the stored patterns. Their meanings come from the complete clauses, not
from a special interpreter branch. Changing this encoding requires changing
the explicit program and proving its corresponding adequacy. Application's
two positions are ordered in the independent source calculus; no ordering of
an unordered RRA account is chosen here. Source definition, clause, binder,
and socket coordinates remain private projection coordinates. The existing
native compiler relocates them under its proved source correspondence.

`SK_Reduction` defines the external calculus independently. `Factor_SK` proves
that the program's whole least fixed point is exactly the external term,
one-step, and finite-reduction relations. The comparison rejects spurious
calls as well as preserving every actual reduction. Generic meaning imports
neither that external calculus nor its adequacy theorem. The pattern-evaluation
helper is a derived calculation of existing finite instances; its proof
functions are restricted to the actual binder boundary and add no callback.

One finite closed native package serves every future formed argument. Its
definition sites are distinct, and every call extension preserves all existing
artifacts and bindings and the same canonical program environment. Finite
reduction is equivalent to closed native replay with the same recovered program,
argument, syntax boundary, and minimal judgment scope. The generic replay
equivalence proves that statement independently of SK. Composed identity gives
an actual compiled computation over arbitrary future SK arguments. These results
establish SK adequacy and non-vacuity. The separate lambda compilation below
advances the universality obligation without closing source reflection.

## External lambda compilation and its proved boundary

The independent source calculus uses de Bruijn indices, ordered application,
abstraction, and finite captured closure trees. Application passes an
unevaluated argument closure; evaluation stops at an abstraction. Variable
lookup is bounded by the explicit captured environment. Scope preservation
and deterministic results follow from this source relation without importing
SK or Factor.

Bracket abstraction removes index zero and lowers each remaining free index.
Its application law follows from the existing K and S rules. The finite
compiler applies that calculation recursively to lambda terms and captured
closures. An environment-agreement theorem identifies exactly which variable
values can affect the result. The total list lookup uses S outside the supplied
list; a well-scoped term never consults that default, and replacing unused
values does not change its compilation.

Every finite source evaluation now compiles to a finite SK reduction and hence
to generic derivation and closed native replay. One fixed native package serves
all such future computations. The source evaluator and compiler do not add
lambda rules to generic Factor meaning. They are external definitions used in
the adequacy argument.

Church numerals are ordinary closed source lambda terms. Their compiled
application performs every finite number of iterations. The output encoding
uses S for zero and one partial K application for each successor. Each successor
adds one application node. Applying a compiled numeral to K and S produces
exactly this normal output. These are explicit test arguments, with no new
arithmetic clause in SK or generic Factor meaning.

SK confluence is proved through parallel reduction and complete development.
The auxiliary relation has exactly the same finite closure as ordinary SK
reduction; it changes no computation rule. The result proves uniqueness of
normal answers and injectivity of compiled numerals. An arbitrary finite lambda
evaluation returning a numeral now gives exactly that compiled numeric answer,
independently of captured entries unused by the closed numeral. Every total
numeric function with the stated independent lambda evaluator witness has a
finite SK implementation with exact numeric answers and native replay.

The source evaluator stops at an abstraction. A beta-equivalent body need not
already be the literal numeral syntax used by this result theorem. The current
result therefore does not recover every source evaluation from a compiled
reduction or reflect source termination. O-66 remains partial.

The same lambda datatype now also carries capture-avoiding substitution and
full beta reduction, including reduction under abstractions. Substitution and
reduction preserve the declared variable scope. Parallel substitution and
complete development establish beta confluence independently of SK and Factor.
The substitution and confluence proofs adapt the method of Isabelle's
HOL/Proofs/Lambda development, with attribution in the theory text, and are
checked over this repository's source datatype.

SK now has an interpretation in that same source syntax: S and K are their
closed lambda terms and application keeps its ordered arguments. Every SK
step has a finite beta interpretation. Bracket abstraction and compilation
reduce back to the original source syntax after interpretation. For a closed
source, this recovery is independent of unused captured environment entries.

Confluence therefore recovers a normal source result whenever a compiled
reduction has that normal lambda interpretation. The existing numeric output
encoding has such an interpretation: zero is the lambda S term, and successor
adds an unused abstraction. These are distinct beta-normal forms. Every
canonical compiled numeric answer, including one supplied through generic
Factor truth or a checked proof tree, consequently implies the corresponding
source beta observation without assuming a source evaluation first.

This result keeps its exact boundary. It does not identify all beta-equivalent
representations with the same raw SK normal form. Nor does it identify full
beta reduction with closure-evaluator termination or literal numeral results.
The closure evaluator and the full beta relation remain distinct judgments.
Finite substitution of captured environments now turns every formed closure
into a closed source term. Lookup agrees with that substitution, and applying
an abstraction agrees with extending its captured environment. Every finite
closure evaluation therefore directly induces a beta reduction, independently
of SK. An auxiliary evaluator substitutes arguments and stops at abstractions.
Its preservation and reflection theorem establishes agreement with every formed
captured closure, including the exact interpreted result. The reverse proof
uses the evaluation derivation for applications and the finite closure tree
for variable lookups. This is a proved comparison of the two presentations of
evaluation, with no extra rule in Factor meaning.

Application-spine lemmas now locate every beta step in its function, one
argument, or the contraction of its first applied abstraction. They prepare
that standardization argument over the existing source datatype, adapting
Nipkow's ListApplication and ListBeta proofs with attribution. The auxiliary
list relation changes one argument by the existing beta rule; it introduces
no additional source computation rule. Standardization is now proved over
that same datatype, adapting Berghofer's argument with attribution. The
standard relation is equivalent to finite beta reduction. A beta reduction
to an abstraction therefore supplies an actual head-evaluation derivation,
and every formed captured closure terminates exactly under this condition.

The termination observation uses SK heads: S or K with fewer arguments than
their contraction rule requires. It permits unevaluated argument terms, as
the source evaluator permits unevaluated abstraction bodies. Every compiled
abstraction has this shape. Conversely, SK interpretation, source confluence,
and standardization reflect termination of every closed untyped source term
from a finite compiled reduction to such a head. This closes the independent
lambda-calculus encoding obligation. Factor derivations and closed native
replay under one fixed finite package have exactly the same termination
criterion. Replay reflection depends on the recovered package and exact call,
not on the particular locations chosen to realize the proof.

## Validation reports belong to the invocation that produced them

The combined wrapper now receives its build evidence directly from the current
run and includes that evidence in its report. It records a fresh invocation
identifier, source hashes, and wrapper hashes; it checks those hashes again
before acceptance. JSON reports are replaced atomically. Startup writes a
non-accepted current status, so an exception or interruption cannot present
an earlier accepted report as the new result. A standalone build also replaces
the previous combined-check status with an explicit unchecked status.

The POSIX wrappers serialize this workspace's validation invocations. Spawned
commands have separate process groups, which are terminated and reaped on
interruption. Cached session errors are queried only for sessions actually
started by the current build; failure to start the executable or obtain its
version cannot import old session diagnostics. Eleven isolated fixture tests
cover successful evidence capture, both startup failure stages, changed sources
and tools, malformed text, unfinished proofs, incomplete inventory, standalone
builds, interrupt and terminate signals, and child-process cleanup. These are
checks of validation reporting and execution; the mathematical evidence remains
the accepted Isabelle theories and their stated assumptions.

## Payload inequality derives from the complete carrier equation

The finite material observation already exposes each exact carrier address as
an opaque payload alongside its occurrence anchor. Its carrier list has no
repeated entry. Since the exact address and opaque payload carriers are both
formed octet words, every finite distinct payload list can be the complete
carrier of a formed artifact with empty incidence and data.

Factor_Distinct_Payloads expresses this through three ordinary schemas. Two
recursively project the address fields from a carrier enumeration; the third
requires that projection and the complete material equation. The independently
defined positive meaning is exactly every finite list of distinct formed
payloads. Singleton lists recognize payloads, and two-element lists compare
them for inequality. A single closed native compilation preserves this meaning
and its formed-call boundary for every future argument.

The implementation choice is to use that existing capability before extending
the language or changing the data representation. The witness artifact is an
ordinary material operand. Its clauses cannot become active definitions, and
its addresses do not name operations. The projection relation in the comparison
proof is derived from the displayed program, rather than added to the semantic
operator. This supplies a component for native checkers; general reflection,
policy-admission evidence, and foundation amendment remain open.

## Complete data comparison uses ordinary recursive clauses

The payload program now supports two explicit definition extensions. One
recognizes exactly the formed payload-and-pair data terms. The other compares
two such terms for exact inequality. Its five clauses inspect unequal payloads,
a leaf-versus-pair shape, or one differing child. Every remaining child must
still satisfy data formation, so finding one difference cannot admit an
unexamined external target elsewhere in the input.

The existing definition builder has a general formation theorem permitting
self-calls alongside calls into the old program. The nonrecursive view theorem
uses this shared result. Every old interface and complete clause family remains
fixed, and dependency locality proves that all old meanings remain fixed even
when the new definition recurses. The existing positive least fixed point
continues to give recursion its only force.

The rule-instance library now supplies a forward valuation projection for
material programs, an introduction theorem for each ordinary clause inside
such a program, and induction retaining the actual truth of every premise.
These are proof tools over the existing operator and finite binder boundary.
They add no evaluation callback or new language form.

One closed native compilation serves every future formed comparison argument.
The comparison concerns the exact supplied data terms. Two different collection
enumerations can present one exact subject, so this result does not classify
the represented subjects as different or remove the separate presentation
invariance requirement. General data readers, native checking, reflection,
and amendment remain to be completed.

## Collection comparison preserves counts through ordinary rules

Complete data presentations admit every enumeration order. The chosen
comparison therefore removes one matching occurrence from one list for each
element of the other list, ending only when both are empty. A separate ordinary
definition recognizes proper lists of formed payload-and-pair data. Removal
checks the complete retained tail and every skipped element. It may skip an
equal element to remove a later occurrence, so the rules do not introduce a
first-match convention.

Repeated occurrences of one scoped variable supply exact element equality.
The residual list is a variable used in both prospective premises and is
checked as part of their complete arguments. No host function computes an
unchecked residual. Soundness identifies exactly one removed occurrence;
completeness covers every possible position. The bag comparison's independent
positive meaning is equality of every element count. The mathematical multiset
used in that theorem supplies no additional semantic operator or structural
rule for arbitrary premise families.

The artifact comparison has one ordinary clause with four distinct premise
sockets. Each calls the bag program on one pair of corresponding fields.
Carrier, incidence, and functional fields have distinct source entries in the
existing presentation relation, so their bag comparisons recover set equality.
The counted attachment field retains all repetitions. Injectivity of the
existing field encodings recovers exact original addresses, ordered incidence
triples, and opaque values.

The resulting theorem covers every complete presentation of both artifacts
and gives exact artifact identity. It does not identify differently addressed
isomorphic artifacts. Full artifact admission is also separate: other proper
four-field data tuples can satisfy this comparison clause. The theorem states
its artifact-presentation premises explicitly.

All earlier interfaces and meanings remain fixed through the fresh definition
extensions. Native compilation relocates their coordinates and fixes one
closed program for every future argument in each stated comparison domain.
Comparison of generations, general native checking, reflection, and amendment
remain to be completed. Environment comparison is derived below.

## Artifact admission derives from complete observed material

The complete material equation already exposes every artifact table and pairs
each occurrence anchor with its exact original address. Two ordinary lookup
clauses recover that address. A single recursive conversion definition handles
the observation terminator, occurrence anchors, opaque payloads, and pairs.
Incidence and attachment lists use this same definition. Their conversion
theorems retain order, all incidence endpoints, every counted repetition, and
the exact opaque values. The earlier carrier projection supplies the remaining
field.

The implementation choice is to derive artifact admission from this existing
complete equation and the displayed projections. A new mixed clause requires
all four projections and that material observation at five distinct premise
sockets. Its whole-source-to-data relation is exactly the established artifact
presentation relation. One ordinary clause supplies the source through its
complete finite variable assignment, so admission requires no external source
target in the submitted data argument. The source is a material operand; its definitions
receive no authority in the fixed program.

The proof library now gives an exact valuation equation for all schemas,
including every material socket and its five evaluated operands. The mixed
introduction rule requires those actual observations. Ordinary introduction
follows when the selected clause has no material premises. These results
calculate existing finite instances and leave the semantic operator unchanged.

The earlier four-field comparison retains its stated domain and meaning.
Another fresh definition joins two complete admissions with that comparison.
Its truth on every term is exactly a pair of presentations of the same formed
artifact. Malformed lists and data tuples that present no formed artifact
cannot pass this admission boundary. Admission concerns the entire submitted
value; recovery of a particular supplied source uses the separate source-to-data
relation. Different complete enumeration orders remain admissible.

The artifact-admission system has thirteen definitions and twenty-six clauses.
Native compilation gives one closed package with distinct admission and
identity sites, both serving every future formed argument while preserving
the canonical program environment. This closes artifact-data admission as a
component of native checking. It does not close native grammar admission,
derivation checking, reflection, policy-admission evidence, or amendment.

## Environment comparison calls the existing artifact identity definition

A complete environment presentation contains a finite collection of
artifact-use rows and a finite binding relation. The same artifact can have
different valid data presentations, so exact term equality cannot compare
its rows. Each new row comparison shares one exact use-coordinate variable
and calls the existing admitted artifact equality definition on the two
values. The use-data encoding is injective over all option-valued natural
words; it imposes no byte restriction on use coordinates.

The collection program selects one entry through that actual comparison
definition, retains the checked residual, and recurses on the other list.
Its exact meaning matches every occurrence through the callee's independently
defined positive meaning. The proof covers every term and all possible
selection positions. The skip and recursive-step schemas are shared with
the earlier exact bag program, whose formation and meaning theorems remain
unchanged.

The general proof is relative to a formed program with the displayed complete
clause families and explicit data boundaries. It does not require the
comparison definition to be outside the program's positive dependency cycle.
This permits later applications to recursively presented subjects without
adding a host comparison callback. A proof-local decoder establishes that
exact comparison of subjects lifts to exact comparison of their complete
finite collection presentations; the decoder supplies no program operation.

The binding field uses the earlier exact bag comparison. Injectivity of its
source-use, original-slot, and target-use encoding, together with complete
distinct-entry presentations, recovers equality of the entire binding
relation. Binding cycles require no expansion of the use graph. The new
environment theorem therefore gives exact environment identity across every
complete presentation order and every valid child-artifact presentation.

The chosen scope keeps environment admission explicit. The comparison itself
does not enforce single-valued artifact and binding tables, binding-source
slot membership, or target-use existence. These are premises of the current
environment presentation relation and are derived by the separate admission
definition below. The raw comparison equation records exactly
what its existing clauses accept.

All earlier interfaces and meanings are preserved. The complete environment
comparison program has seventeen definitions and thirty-two clauses. Native
compilation fixes one closed program before all future environment operands
and preserves its canonical program environment in every actual application.

## Environment admission checks every row and every scoped binding

The existing environment representation fixes two complete finite tables:
artifact-use rows and source-slot-target bindings. Admission now derives exactly
their formation laws through ordinary definitions. It reuses the artifact
admission program and adds no material observation or semantic primitive.

The natural-component, finite-word, and optional-coordinate definitions follow
their existing data shapes. Every natural component is permitted, including
values outside the byte range. The chosen definition supplies the profile;
a value does not acquire a nominal role from its representation alone. Shared
list schemas traverse the complete list and final tail. Unary element checks
carry no context field. Binding lists carry the actual artifact table into
every element call, and their empty case still checks context formation.

Key absence compares a supplied key with every key in a complete tail using
the earlier data-inequality definition. Its empty case checks the supplied
key through data recognition. Key uniqueness then requires absence from each
tail. Values need only be formed terms here; the row-admission calls enforce
their stronger profiles separately. The mathematical key theorem equates
distinct keys with distinct rows and a single-valued row relation. Shared
finite enumeration and list-witness lemmas now live in Bootstrap_Relations,
so raw data checking does not depend on the native proof-table construction.

A binding clause selects a source row and a target row from the same supplied
artifact table, then selects the exact slot from the source artifact's carrier
field. These are three distinct prospective premise sockets. Its complete
assignment includes the three list remainders and every matched value.
The source pattern needs the carrier field and the complete remaining
artifact value; splitting the other fields again serves no additional purpose.

The binding-query theorem is conditional on a complete admitted artifact-table
presentation. The query alone can accept broader data, which its raw equation
records. The final admission clause separately checks every artifact row and
both key constraints. Its four distinct sockets therefore enforce every
environment formation condition. Empty environments and finite binding cycles
require no special clauses or recursive expansion of the use graph.

A represented artifact can have several valid data presentations. Consequently,
completeness selects an actual row of the supplied table and recovers that row's
carrier presentation. Membership of a represented source does not authorize
substituting a different presentation into the supplied list. The shared
collection-selection theorem preserves this distinction in both directions.

The complete program has twenty-eight definitions and fifty clauses. Admission
accepts exactly the existing presentations of formed environments over the entire
term domain. Admitted identity requires two admissions and the earlier environment
comparison. One fixed closed native package contains distinct sites for both
operations before any future formed argument is supplied; each application
preserves the canonical program environment. This completes environment-data
admission as a checker component. It leaves grammar-derived closure, application
checking, policy authority, reflection, and amendment adoption as separate work.

## The adopted purpose selects the current amendment entry

The currentness frame already determines an exact authority, generation, and
purpose through its actual adoption call and closed publication. The selected
generation's payload already determines a complete closed program scope.
The remaining entry cannot be chosen by an existential search for any true
definition: a permissive auxiliary would then replace the authorized policy.

For this profile, the purpose is a whole-artifact complete quotation of an
exact environment-use and address pair. The complete structure determines
the quotation root, and the program scope comes from the generation payload.
No root marker, second environment copy, or second authority field is stored.
The designation includes the use coordinate because equal artifacts may occur
at differently bound uses. It may select any actual definition of the recovered
package; the existing root family is not restricted to a singleton. This is
a choice of purpose profile, not an intrinsic role attached to all purpose
targets or a new primitive operation.

The amendment argument contains the complete current-frame value, candidate
generation, and certificate target. The frame includes both the minimal adoption
judgment scope and closed publication scope. Its adoption call contains the
predecessor generation and purpose, and that generation's payload contains the
predecessor package. Repeating those fields would serve no independent purpose.
Every complete presentation is admitted, including different internal collection
orders. Formation and truth invariance is an explicit policy admission condition;
the particular outer quotation used to record a frame does not select a preferred
enumeration for the acceptance argument.

Definition closure follows the actual prospective callees. It is least, finite
inside a formed system, and equal to native definition reachability for roots
inside a native package. Every admitted instance inside that closure calls only
members. Complete interfaces and clause families on the closure determine
formation and truth on every argument. Complete package formation still checks
the entire predecessor package. This closure bounds possible recursive calls;
it is not described as the exact set invoked in each derivation.

Raw current acceptance requires the selected program and entry, the exact frame
data, an actual native application, and the invariant policy's positive truth.
Its enclosing environment must retain the predecessor's exact program scope.
The canonical program environment is therefore identical. Future call
construction also preserves every old artifact and binding. The upstream
adoption program keeps its own recorded scope; no theorem silently identifies
it with the program selected by the generation.

The generic singleton-publication construction now lives with the raw
publication constructors. Together with an explicit ordinary adoption policy,
it gives actual current frames for every entry of every closed native program.
A displayed two-entry program has one premise-free variable clause at one
entry and no clauses at the other. Both interfaces admit every formed term.
One compilation preserves both meanings for every future argument. Actual
current frames and calls show acceptance and refusal under the chosen entry;
a true call to the auxiliary entry still cannot serve as current acceptance.
These witnesses do not validate their generated cores' causes.

This batch establishes the acceptance invocation and its locality. It does not
supply the four certificate relations, structurally determined compatibility
domains, the predecessor continuation derivation, the cross-version bridge,
successor adoption, or native admission of the complete amendment mechanism.
Those remain separate connected obligations.

## Compatibility starts from the actual changed rows and affected callers

The comparison boundary is fixed before a transition certificate makes claims.
For the current positive class, a changed definition has a difference in its
complete interface or clause rows. Introduced and removed definitions are
included. The comparison uses the given definition coordinates in the two
recovered programs. It neither identifies their exact environments nor treats
a common coordinate as proof of equal artifact identity.

This is a structural comparison. Private binder or clause relocation can change
these rows while an explicit transport proves semantic preservation. Such a
transport belongs to a separate comparison relation; change detection does not
silently quotient the source structures or claim that every changed row changes
truth. This retains the distinction between migration and semantic preservation.

The affected boundary is the least backward closure of changed definitions
through each program's prospective-callee graph. The ordinary definition closure
follows callees; this closure instead follows their callers. It includes every
definition whose complete prospective dependency closure reaches a changed row.
Recursive cycles require no exception. Outside it, complete interfaces and
clause families agree on a closed set, so every formed-call boundary and every
positive meaning remains equal.

The selected comparison profile takes all actual public roots and all affected
definitions in each program. The native root family supplies the roots. The
current frame determines the predecessor scope, and the candidate generation's
whole program payload determines the other scope. Those exact values uniquely
fix both domains. There is no certificate-provided root list, host registry,
or independently stored change classification.

Finite definition domains do not make their argument domains finite. Comparison
covers every call admitted by the actual interfaces, including every future
argument. A formed pattern always has an instance: assigning an empty payload
to each variable gives a complete formed binding witness. Consequently every
required definition contributes admitted calls. In a native package the domain
is empty exactly when the recovered program has no definitions.

The concrete example adds one premise-free clause at a callee. Its caller keeps
the same complete rows but changes truth on every formed argument. The derived
boundary includes that caller and the changed callee; an independent public
definition keeps its meaning and remains in the public comparison domain.
The resulting call boundary is the three definitions paired with all formed
terms, rather than an enumerated sample.

These results fix the complete comparison obligation for this profile. The four
certificate relations still require their separate domains and coverage rules,
including the interaction of preservation and intentional incompatibility.
Migration, interpretation, preservation, and incompatibility are not made into
a partition here. The predecessor's policy must still check their actual
material, continuation, interpretation bridge, and successor authority decision.

## Complete reporting is distinct from universal preservation

The required comparison domains remain those recovered from the actual current
frame and candidate program. The structural reporting domain consists of their
required definition sites. The judgment reporting domain consists of every call
admitted at those sites, including every future argument. A certificate cannot
supply either domain or silently omit an endpoint.

A correspondence contains its actual pairs and an explicit missing-counterpart
row for each endpoint with no declared partner. These rows are present exactly
at those endpoints. They assert absence in the submitted correspondence, not
impossibility of every other correspondence. Both domains are recovered again
from complete rows. Structural correspondence is a declaration of migration;
coverage alone proves neither an admissible assembly nor semantic preservation.

Judgment reports contain one pair of optional endpoints and two separate
declaration flags. Interpretation is the projection of paired endpoints.
Preservation and intentional incompatibility are separately recovered from the
flags. Every required call appears in a report, and every report contains both
fields. Thus declaring no preservation still requires a complete explicit
account. Requiring the positive preservation relation itself to cover every
required call would rule out the intentional incompatibility allowed by D-9.
The complete reporting obligation is fixed; the positive extension of each
declared relation may differ.

False means that this report makes no declaration of that kind. It does not
prove inequality, failure of interpretation, or a negative semantic judgment.
A preservation claim must relate two formed calls with equal independently
defined positive truth. An absent counterpart must declare intentional
incompatibility. A paired interpretation may make neither further declaration.
The profile imposes no four-way partition or disjointness rule. An intentional
incompatibility declaration is not a proof that the two meanings differ;
a predecessor policy may impose additional requirements on such declarations.

This is an explicit representation choice for the comparison profile. The two
flags state separate claims without storing the judgment pair a second time.
They are represented with existing payload-and-pair data. Definition coordinates
remain relative to their two exact comparison scopes. Equal coordinates across
those scopes do not establish exact artifact or environment identity.

A finite ordinary program may describe an infinite judgment-report relation.
The mathematical set is a derived meaning, not an infinite stored certificate
field or an external truth callback. A no-extra condition requires every positive
output at the report entry to have the complete report form. Domain coverage
then rejects unformed or out-of-bound endpoints. Native compilation preserves
all reports and this no-extra property for all future inputs.

One ordinary pattern with a shared variable covers every formed argument at its
paired endpoints. Either endpoint may instead be explicitly absent. The whole
positive relation is proved from ordinary rules and has one closed native
compilation. Complete comparisons between opposite constant policies fail when
preservation is claimed and pass with declared incompatibility. A unilateral
report covers every old call with an explicit missing counterpart. An actual
current native singleton scope also has a separate complete native reporter
preserving all its calls. That witness compares the same generation on both
sides; it does not claim adoption of a new successor or validity of its cause.

The reporter describes comparison material. Supplying it does not install its
clauses in the predecessor's acceptance package. Its full native data
representation, internal admission of coverage and preservation evidence,
migration evidence, the cross-version bridge, predecessor continuation, and
successor adoption still need the remaining joins. Later accepted policies may
change this profile; it is not an immutable restriction on every successor.

## Continuation roles retain the predecessor's actual adoption policy

The adopted amendment purpose fixes its acceptance entry. A continuation role
may use another entry of the same selected generation, but an arbitrary true
call in that program does not select the role. The companion profile requires
an actual second adoption under the same entry of the same complete adoption
program. Both current frames retain the same authority, exact generation, and
closed publication scope. The two purposes may differ.

The adoption program and the program carried by the selected generation remain
distinct. Each is recovered from its own existing complete scope. Requiring
the same adoption program value or root artifact would be too weak: bindings
and the invoked adoption entry are also fixed. No duplicate authority,
generation, policy, or publication fields are stored by this relation.
Every companion purpose permitted by the original policy has an actual current
frame. This requirement concerns role selection within one predecessor
generation; it does not force a successor to retain that adoption protocol.

Current continuation invokes only its selected entry. Its native proof uses
the exact predecessor program and has no open assumptions. The before snapshot
is the snapshot of the predecessor's actual publication, not a second freely
chosen subject. Structural transaction success remains an additional condition.
The selection component below joins the claimed after snapshot to the
successor's actual publication. The complete mechanism must also validate
the supporting material.

A replay value stores one complete environment and three actual sites:
program, call, and proof. Native readers recover the program, argument, graph,
and assumption boundary. Those derived values are not stored again. The whole
data quotation determines its own root and is readable without external slots.
Every native replay is recordable, and every current continuation has a record
retaining its original program and complete minimal call scope.

The submitted continuation material precedes its proof record. It is not
required to contain a complete quotation of that record, which would create
a circular finite-data obligation. The selection component below binds the
material, selected continuation frame, and separate proof record to predecessor
acceptance and the exact successor frame. Admission of the remaining evidence
is still open; these components do not define complete legitimate succession.

One explicit accepting adoption policy selects two distinct entries of a
single native generation. Both entries admit every formed argument, including
every complete future amendment argument. The continuation entry accepts and
has a closed recorded proof over the actual unchanged publication snapshot. The other entry
refuses every amendment argument. The true continuation call cannot count at
that refusing entry. This exhibits the independence of adoption, structural
success, continuation, replay, and amendment permission with actual finite
programs. Its generation has only a formed cause target; no genesis or
successor validity is asserted.

## Acceptance binds the continuation record and exact successor frame

A continuation envelope contains two complete exact artifact values: the
companion current frame and the recorded closed continuation proof. Each
artifact's complete structure determines its quotation root. The replayed
call already contains the before snapshot, transaction, claimed after, and
complete material scope. Repeating those fields in the envelope would add
an independent consistency obligation without adding information.

The material scope selects a complete data quotation containing the exact
proposed successor frame and one complete supporting scope with an actual
site. This is a staged certificate profile. The supporting scope is the
place where the remaining assembly, dependency, comparison, and interpretation
evidence must be checked; its formation does not check those conditions.

The predecessor's actual amendment call accepts the candidate generation
and the whole envelope as ordinary argument data. The exact binding path is
therefore: accepted envelope, companion frame and continuation record,
replayed call, complete material, exact successor frame. The successor frame
must select that same candidate and its actual publication must have the
proved successful after snapshot. Changing any recovered field cannot leave
the same accepted envelope and call intact.

Only the companion role is constrained to retain the predecessor's original
adoption policy. The successor's authority, locus, purpose, and program may
differ. The accepted material must identify that new frame exactly. Requiring
equality of those successor fields would impose a protected boundary that D-9
does not authorize.

Acceptance itself has a separate closed replay record. Its program site is
the one recovered from the predecessor's current frame, and the actual call
uses that frame's selected entry. Every acceptance can acquire such a record
without changing its complete minimal judgment scope or canonical program
environment. Every permitted complete argument has an actual recorded native
call. Equal whole records determine the candidate and envelope, and through
the envelope the exact proposed successor frame. They do not identify two
different presentation artifacts used to display the same predecessor frame.

The construction is acyclic: proposed material precedes its continuation
proof; that proof precedes the submitted envelope; acceptance of the envelope
precedes the separate acceptance proof. No proof is required to quote itself.
A fixed actual current program gives all these records for every future formed
supporting scope while preserving its selected generation and publication.
Its accepting entry permits every formed argument. This is a concrete witness
for the binding and selection component and demonstrates why it is insufficient
as the complete amendment protocol.

No complete legitimate-succession claim is made by this selection component.
The account and dependency components below add the historical predecessor,
assembly evidence, and complete dependency permission coverage. Comparison
admission, the cross-version interpretation bridge, and internal checking of
the whole protocol remain. The genesis adequacy theorem must prove that a
concrete predecessor policy enforces those conditions; a proof of its positive
call alone cannot establish that property.

## Assembly evidence retains the candidate's exact recorded construction scope

The staged transition profile checks a separately adopted construction purpose
of the predecessor. Like the continuation role, this purpose uses the same
authority, generation, publication, and original adoption-program scope and
entry. Its selected construction entry may differ from the amendment and
continuation entries. This is a concrete protocol choice: it keeps construction
permission under explicit predecessor authority. It is not an immutable rule
for every successor protocol that the predecessor may later authorize.

The construction call already determines the full input list, base entries,
selected pieces, complete origins, and output. Its ordinary permission keeps
structural assembly validity and presentation invariance distinct from the
truth of one serialized call. The retained closed replay must use that actual
selected entry and exact predecessor program. Every permitted complete account
has such an actual native call and proof.

The candidate's recorded cause must quote exactly the minimal program-and-call
scope of that replay. Equality only of its decoded account, program value, or
root artifact would permit a different dependency environment. The proof can
retain additional required proof material, but the recorded cause retains
only its independently derived minimal judgment scope. Every outer
presentation of the same candidate then recovers the existing certified
recorded construction cause. The assembly output must be that candidate's
exact payload.

The supporting material stores the construction frame and whole replay record
once, followed by one complete remaining scope and its actual site. The account
and candidate are recovered through their existing records. The accepted
continuation envelope fixes all these exact fields; a different proof or
remaining scope cannot replace them inside the same accepted target. Data
formation admits every complete presentation without asserting acceptance
invariance across different exact submitted artifacts.

The actual current generation must separately occur in the candidate's direct
predecessor family. This choice follows the required exact predecessor in
proposal §15.5 and plan O-61, while retaining additional direct predecessors.
It does not require the predecessor to occur in the construction input list,
make it a semantic dependency, or equate any of those boundaries. The generation
size theorem proves strict succession. The earlier unchanged-generation
selection witness therefore fails this stronger account profile.

One exact construction proof and recorded cause can accompany two actual closed
generations with different histories. A fixed native output policy also serves
every future valid account presentation and supplies a candidate with the
current generation as a direct predecessor. Its empty assembly is an explicit
instance. These witnesses establish the construction and history joins; they
do not adopt arbitrary output artifacts as successor programs or establish
genesis adequacy.

Given an actual candidate frame, its matching assembly proof, the historical
edge, and a successful transaction between the actual publication snapshots,
a universal current entry constructs the complete account material and both
later proofs for every remaining formed supporting scope. This conditional
construction checks the order of the finite records without assuming that
the candidate's supporting scope contains either later proof.

The dependency component below requires permission evidence for every actual
program definition subject. Comparison and migration admission and exact
cross-version interpretation still need to be checked in the remaining bound
scope. The full protocol must have an ordinary internal definition and a proved
adequacy theorem. None of these component joins establishes policy adequacy
merely from a proof that its acceptance call is true.

## Dependency evidence is complete permission under the predecessor's selected policy

Proposal §15.5 and plan O-61 require evidence for every retained and changed
dependency. They do not specify that evidence's judgment family. This profile
uses an ordinary predecessor permission on an exact environment and definition
site. It does not identify that permission with the definition's meaning or
with truth of every application at that definition. The choice keeps the
dependency decision explicit and open to later authorized protocol changes.

The required subjects are every definition of the predecessor's actual closed
program and every definition of the candidate's actual closed program, each
paired with its complete canonical environment. Both scopes are recovered
before evidence is supplied. Public and affected comparison domains serve a
different obligation and cannot replace this complete dependency boundary.
Every required site has a native definition reading, and the actual current
entry makes the boundary nonempty.

The complete package environment is the site's context in this profile, even
when that definition has a smaller unchanged active closure. This keeps the
decision relative to its exact supplied scope under D-11. A coincident
coordinate in a different environment is a different subject. Identical
environment-and-site pairs are counted once, including when the candidate
retains the whole predecessor program. The separately recovered program roots
are not stored again in each subject.

One companion current purpose selects the permission entry under the original
predecessor adoption policy. It may differ from the amendment, continuation,
and construction entries. Each permission call retains that exact old program
and reads the submitted scope as ordinary complete data. The submitted
dependency's clauses do not become rules of this call. The permission's
formation and truth must agree across all complete presentations of its
environment-and-site subject. One positive proof cannot establish that
invariance condition by itself.

The evidence body stores the companion frame, a finite collection of whole
proof records, and one complete remaining scope with its actual site. Each
record's actual argument already determines its subject, so no duplicate
subject key or quotation root is stored. Every required subject has a record,
and every supplied record must have a valid required subject. An unreadable
record is not silently ignored. The same whole record cannot be reassigned to
another scope or site.

The collection lists exact proof objects. It does not add identifiers for
repeated outer storage occurrences. Identical whole records occur once;
different proofs of the same permission may accumulate. A complete collection
can be constructed in which every record is needed for coverage. Removing its
sole provider fails that required subject, while inserting another valid proof
of a required permission preserves coverage. A valid proof of an unrelated
subject is rejected. Empty collections remain formed data but fail every
actual amendment dependency obligation.

The existing accepted envelope fixes this collection and its remaining scope
through the continuation and assembly material. Selection, construction,
history, and dependency permission remain separate checked relations.
Acceptance and its retained proof keep their original exact program and
minimal judgment environment. Candidate scopes may contain different binding
values as ordinary data; those values do not rebind the active predecessor
environment.

One fixed actual native policy supplies a nonempty complete proof collection
for every future program candidate, with every constructed record needed.
Given the separately supplied actual candidate frame, assembly certificate,
historical edge, and successful publication transaction, it also constructs
the dependency material before the continuation and acceptance records.
This construction works for every remaining formed scope and needs no proof
to quote itself.

A native permission proof also coexists with refusal of every formed call at
its permitted dependency, with all those call interfaces still formed. This
exhibits the distinction between permission and the dependency's own truth.

The example permission entry accepts every formed site argument. Complete
evidence under it therefore does not establish adequate dependency checking.
Comparison and migration admission, exact cross-version interpretation, an
ordinary internal definition of the complete protocol, and its genesis
adequacy theorem remain necessary. The finite coverage theorems are a
component of that work, not a substitute for those semantic obligations.

## Successor components have one finite construction order

The earlier account and dependency totality theorems assumed a candidate
currentness frame, its construction evidence, a historical edge, and a
successful publication transaction. Those assumptions could not establish
that all the ingredients coexist. The empty assembly witness had no program
payload, while the unchanged-selection witness had no strict historical edge.
The new joint construction supplies all these ingredients for every closed
candidate program and actual selected definition.

One piece selects an already supplied source's whole carrier. Its complete
origin map returns every copied atom to the same address and recovers the
exact incidence, anonymous counts, and functional bindings. The concrete
construction account declares one input occurrence and no base sources.
This is a reusable source account with an explicit boundary, not an origin
claim before that source was supplied. Permitting it cannot by itself prove
adequacy of construction or genesis.

The old current program is fixed before future candidate programs are
supplied. A complete quotation of the candidate's closed program scope becomes
that declared input and exact output. The predecessor's construction proof
is obtained next. The candidate then records the proof's minimal call scope
as its cause and the actual old generation as its direct predecessor. The
candidate's definitions supply ordinary data for dependency permission proofs
under the same old program.

The replacement transaction expects exactly the old generation and proposes
the new generation at the same locus. Its comparison boundary contains only
that locus. This choice avoids adding unrelated selections to the expectation
while preserving all of them in the resulting snapshot. A different observed
generation conflicts. The historical edge makes the generation and snapshot
changes strict; transaction success alone would not do so.

The successor publication is constructed after the construction and dependency
records exist. It selects the new generation and cites exactly those complete
proof artifacts in its evidence selection. This gives a concrete instance of
the evidence-citing publication requested in problems §8.4. A separate ordinary
adoption call creates the actual successor currentness frame and retains that
exact publication environment. No truth requirement is placed on the entry
being adopted.

The publication's extra dependency-target selection is empty in this witness.
The complete program payload already retains its scoped definitions, and the
dependency permission subject boundary is separately derived from the old and
new complete program environments. This is an explicit example choice, not
a general rule forbidding additional publication dependencies. The existing
component relation also does not yet make this particular evidence selection
mandatory for every accepted transition.

The same proof objects are referenced in the publication and the supporting
material. Their values and purposes agree; no alternate account or copied
subject key is introduced. The supporting material is then completed, the
continuation record is produced, and finally its whole envelope is accepted.
The successor publication is not required to contain either later proof.
Requiring the publication to contain that acceptance record would feed the
record back through its own complete currentness-frame argument. This
construction needs no such recursive quotation.

One actual permissive native predecessor serves every future closed candidate
program and every remaining formed supporting scope. All original predecessor
program bindings and the exact minimal acceptance scope survive certification.
An explicit one-entry successor program has a formed interface for every
formed term and no clauses, hence no positive calls. It differs from the
two-entry predecessor yet receives the same component evidence and acceptance.
This counterexample makes the limit concrete: joint existence, complete proof
coverage, and actual publication do not establish preservation or adequate
checking of comparison, migration, cross-version interpretation, or genesis.

## Complete comparison data belongs to the accepted envelope

The comparison profile now has an explicit finite submitted representation.
Its structural correspondence is a complete collection of optional definition
coordinate pairs. Every exact row occurs once, with all collection orders
admitted. Absence uses existing payload-and-pair data; no coordinate value
acquires a reserved semantic name. Raw formation permits an empty correspondence
or a row outside the eventual domain. The higher comparison profile rejects
those cases against the actual predecessor and candidate scopes.

The reporter is stored as one complete environment, its package site, and its
selected definition site. Both sites must exist as raw data. The higher reader
requires an actual closed native package and membership of the selected entry.
The environment occurs once, and the recovered program is not stored a second
time. No particular report call is needed to select an entry that describes
all future reports. The reporter has no separate adoption frame: it is proposed
comparison material judged through the predecessor's acceptance of the whole
envelope. This is a representation choice, not an additional source of
authority for its clauses.

The finite structural rows use coordinates relative to the two program scopes
already fixed by the current frame and candidate generation. Those environments
and their public roots are not repeated in each row or supplied as alternative
domain fields. Equal coordinates in different scopes do not identify their
definitions. The potentially infinite judgment-report relation is derived from
the selected ordinary reporter entry. It remains subject to complete coverage,
the complete positive-output condition, and independent preservation soundness.
No infinite report table or semantic truth callback is stored.

The comparison value also retains one complete remaining scope with an actual
site for further migration and interpretation material. It occupies the
previously open scope inside dependency support, which is already inside
assembly support, the continuation material, and the exact accepted envelope.
Whole-value recovery prevents another reporter, entry, correspondence, or
remaining scope from being substituted while that accepted subject is fixed.
The acceptance proof retains the exact predecessor program and minimal call
environment; the reporter does not become an active rule of that program.

Every complete mathematical report profile has an actual finite native data
quotation. A joint witness constructs a strict new generation of a singleton
program and complete preserving reports for all its admitted arguments.
Its program meaning is unchanged, while its generation and selected snapshot
change. The actual construction cause, predecessor edge, dependency evidence,
publication, successor adoption, continuation, and acceptance coexist with
that retained reporter and every supplied remaining formed scope.

These results establish the data and binding of the comparison component.
The witness's ordinary predecessor remains permissive. The complete internal
checker must still establish the grammar and semantic obligations through its
own ordinary rules; native quotation alone does not do so. Migration evidence,
exact cross-version interpretation, and complete genesis adequacy also remain.

## Historical interpretation has ordinary formation and truth entries

A historical call must retain both its original application boundary and its
truth. The bridge therefore exposes two ordinary entry roles. Both query
interfaces accept formed terms; positive truth at the first entry means that
the quoted old call is formed, while truth at the second means that it is
true under the old program. The contract permits the roles to share an entry
when their meanings agree. The uniform construction uses distinct definitions
whose ordinary clauses carry the different checks.

The historical query is the pair of the existing exact definition-site data
and the entire old argument. No new definition-name token or role byte is
introduced. The old program's complete canonical environment and package site
remain available as a whole scope quotation. Those fields fix the historical
context of the coordinates. The bridge does not equate the old environment
with the newly compiled one, and it does not make equal coordinates in other
scopes denote the same definition.

For every old definition, one premise-free clause copies its full interface
pattern behind that exact site value. A separate clause invokes the copied
old definition through one actual prospective premise on the unchanged
argument. Every old definition contributes both clauses, including definitions
that have no true calls. This boundary is the entire old program, not the
smaller comparison domain or a certificate-selected list of calls. Clause
coordinates are chosen injectively from the complete finite definition set.

The old and supplied other programs first receive disjoint definition sites.
Their complete interfaces and clause families are retained, and all prospective
callee occurrences are moved with their owners. Dependency closure and the
independent positive operator prove exact preservation of both programs,
including recursion and complete material equations. Literal targets and
material operands do not change. The two new view entries have fresh sites
and cannot supply additional rules to either retained source definition.

The complete result is then compiled through the existing native compiler.
Its source sum and Boolean coordinates allocate ordinary definition occurrences;
they are erased by the structural compilation and do not select primitive
truth branches. The result contains exactly the two copied definition families
and the two new entries. Its maps are injective and the families and entries
are disjoint. One finite compiled package works for all future arguments,
with exact source call boundaries and exact historical output equations.

This is a family of actual finite constructions, one for each supplied old
program and other program. It is not yet a single generic native interpreter
taking an arbitrary program as argument. No universal truth-equivalence
decision procedure is assumed. The all-argument contracts follow from the
explicit interface clauses, actual old callees, locality, and compilation,
rather than a supplied interpretation or adequacy callback.

Another exact bridge interprets the previous bridge's selected entries.
The complete earlier query is retained as that call's ordinary argument.
The resulting nested query preserves both old formation and old truth, with
no change to the original argument or literal identities. This provides the
exact composition step for retaining an older chain when later definitions
use their own sites.

The construction establishes one sufficient class of exact bridges and its
semantics. It neither imposes copying on every successor nor establishes
successor authority, complete protocol adequacy, or genesis. The following
component binds its selected entries into the accepted transition. Native
checking must still admit finite correctness evidence for this or another
supported bridge class.

## Historical entry selection reuses the exact retained scopes

The current frame already fixes the old program's complete exact environment
and package site. The candidate payload fixes its own complete exact program
scope. The interpretation value therefore retains only two coordinates in
that candidate scope, followed by one complete remaining environment and its
actual selected site. Repeating either program or either scope would create
a second field for a boundary already determined by the accepted subject.

The two coordinates use the existing ordinary site-data representation. Their
positions identify the formation and truth roles within this profile; no new
name, role token, or primitive operation is added. The value admits coincident
coordinates. The higher interpretation contract permits that coincidence only
when one actual entry has both required meanings. Raw coordinate formation
neither asserts candidate membership nor proves semantic correctness.

The semantic profile recovers both exact scopes and checks the two selected
entries in the actual candidate program. Its old domain is every definition
and every admitted argument of the old program. Neither the comparison
correspondence nor a selected public-root list can shrink that domain. The
formation query and truth query remain separate, and both complete output
equations exclude unknown old coordinates and unrelated query shapes.

The value occupies the remaining scope inside comparison support. That value
is already inside dependency support, assembly support, the continuation
material, and the whole accepted envelope. Uniqueness composes through every
layer, fixing both interpreter entries and all remaining fields while the
accepted subject is fixed. All earlier transition components remain required.
The predecessor's exact acceptance program and minimal call environment remain
the ones retained by the final proof. Candidate interpreter clauses are
ordinary submitted data for that acceptance; they cannot authorize adoption.

For every actual current program and supplied formed other program, the
historical construction now also supplies this finite value. Its full maps,
disjointness, definition boundary, and preservation of both source programs
remain in the result. The program and value precede the candidate's history,
cause, and adoption presentation, so they can be placed in future supporting
material without a circular quotation of the final accepted envelope.

A separate retention theorem constructs the complete combined supporting
material given the actual candidate, successful selection, assembly account,
and independently established comparison and interpretation. Its predecessor
policy is explicitly permissive. The theorem does not infer either semantic
obligation from permission, and its conditional statement is not a joint
construction of those obligations from syntax. The following construction
supplies that witness. Native finite correctness admission, migration evidence,
the full internal protocol, and genesis adequacy remain required.

## Complete reports use actual interfaces and actual public roots

A finite ordinary clause family can describe an unbounded call domain. Each
required definition contributes its actual interface pattern. Substituting
that pattern at every present report endpoint preserves the whole argument,
including repeated variables, nested pairs, exact payloads, and literal
targets. The interface binder and each clause's binders retain separate scopes.
The compiler handles their private coordinates. No ground sample, semantic
lookup table, or new observation rule replaces those patterns.

The general family permits overlapping patterns and arbitrary explicit
declaration fields. Its exact output theorem does not silently infer
functional or sound reporting. Those remain requirements of the separate
comparison profile. Empty finite families still have a formed interface and
no positive outputs. Distinct equal-pattern clauses keep their distinct
occurrence coordinates.

For the historical compilation class, the reporting correspondence pairs
every required old definition with its copied definition. Complete interface
agreement covers every admitted argument on both sides of each pair.
Independent truth preservation justifies the preservation declaration.
Every required candidate definition outside that copied image receives an
explicit missing-old-counterpart row and intentional incompatibility. This
includes the interpreter entries, the supplied other program, and any old
copy outside the required old comparison domain.

The missing row states absence from this declared correspondence. It does
not assert that another interpretation is impossible. The two flag
configurations used by this construction impose no partition on the general
comparison profile. Reporting also needs no injectivity assumption on a
supplied copy map; the historical compiler supplies injective maps and
disjoint definition families as a sufficient case.

The existing compiler already constructs a selector for every resulting
definition. The strengthened theorem now exposes that exact fact and proves
that the canonical package restriction preserves the selected roots. The
earlier theorem statements remain available as direct corollaries. The
historical compiler and its finite supporting-value construction carry that
property forward. This describes the constructed packages; it does not
require every possible future program to export all its definitions.

The actual candidate comparison domain therefore includes every candidate
definition. The old domain is still derived from the exact current scope,
changed rows, and affected callers. The reporter cannot select a smaller
boundary. The historical interpreter independently covers the entire old
program, including definitions outside that comparison domain.

The joint construction obtains the copied programs, interpreter, and reporter
from finite program syntax before constructing the candidate's cause and
publication. The same values occur inside dependency and assembly support,
the continuation material, and the final accepted envelope. The actual
candidate has more definitions than the old program and is therefore
different. One fixed permissive native predecessor serves every future formed
program with a selected entry; neither comparison soundness nor interpretation
is an assumed semantic callback in that theorem.

A selected new entry may refuse every call while the historical truth entry
still gives the exact old answers. This distinguishes changing the selected
policy from erasing earlier meaning. The predecessor's exact program and
minimal acceptance environment survive certification. These are joint
existence theorems under an explicitly permissive predecessor. Native
admission of finite correctness evidence, structural migration evidence, the
full internal protocol, reflection, and genesis remain required.

## Headed grammar observations collect every local entry

The chosen admission route uses the existing complete artifact-data relation.
A generic ordinary recursive definition collects values at one exact supplied
key. Repeated pattern variables enforce equality in the keep clause; the
existing data inequality definition justifies the skip clause. Every row and
the final tail are inspected. The collector preserves the supplied order and
every repeated value. It requires formed self-contained keys and formed values,
without imposing uniqueness or a stronger value profile.

A fresh clause separately admits the whole source artifact and selects the
requested address from its actual carrier. Three collector calls recover every
headed incidence, counted attachment, and functional attachment at that address.
Three bag comparisons check the submitted local fields, permitting every complete
order. The complete variable boundary includes the three collected lists and
the carrier-selection remainder; the eight prospective premises retain distinct
socket occurrences.

The exact contract derives distinct incidence and functional entries from the
source's admitted set fields. Counted attachments instead retain their exact
multiplicities. Empty local data and a functional payload leaf recover precisely
the existing structural grammar conditions. Source and output enumeration order
have no semantic authority. The thirty-definition, fifty-four-clause program
compiles once before arbitrary future formed inputs and preserves its canonical
program environment in every actual application.

The complete source stays in the argument. Incoming incidence and material at
other heads remain supplied, although they do not enter the headed projection.
This distinction preserves the relative record, family, and citation grammars;
requiring the source to equal an isolated canonical syntax object would reject
valid shared structures. Headed material is not identified with the complete
relative footprint. Record order still comes from successor incidence. Native
checking of the remaining grammar, finite correctness evidence, reflection, and
the full amendment protocol remains required.

## Family and record admission preserve their different ordering boundaries

Both entries receive the same kind of ordinary argument: a complete artifact
presentation, an exact root address, and complete socket-endpoint rows.
Addresses remain opaque payloads. The root material check admits the source,
selects an actual carrier occurrence, and checks every headed incidence and
both empty local data fields. Thus an empty row list cannot admit an absent
root. The interior is derived from that root and the row keys; no second
interior field or role tag is stored.

The family entry separately checks unique socket keys and uses the existing
context-carrying list profile to check every socket. Each must differ from the
root and have empty headed incidence and local data. Different sockets may
have equal endpoints. The row list presents a finite relation, so every
complete order is accepted and repetition of a row is rejected.

The record entry follows successor incidence through the supplied rows. Its
last socket must have an empty head; every preceding socket has exactly the
one represented successor. A finite deterministic chain cannot revisit a
socket: doing so would give two different tails from the same complete head.
The new structural theorem derives distinct sockets and proves that combining
this chain with the root graph is exactly the existing record relation.
Consequently the record entry has no separate key-uniqueness premise. Its
ordered output is unique, while endpoint repetition remains allowed.

The shared ordinary-entry valuation lemma is a proof calculation for the
unchanged consequence operator, including ordinary entries in programs that
have material premises elsewhere. Existing record-path inversion lemmas move
unchanged into the raw structural theory so both native and executable clients
use the same facts. No executable checker or external grammar predicate becomes
a premise of native truth.

The five new definitions have eight ordinary clauses. The complete program has
thirty-five definitions and sixty-two clauses. It compiles to distinct family and record sites before
arbitrary future formed arguments. Each actual application preserves the
canonical program environment. The exact contracts cover every input term
and every admitted source presentation. Incoming edges and other source
material remain present and do not invalidate relative grammar readings.
This closes these two native grammar components. Citation admission is
developed next; higher grammar, finite correctness evidence, the full internal
transition protocol, reflection, and genesis remain required.

## Target addresses remain opaque through citation admission

An exact occurrence address was previously presented using the natural-word
encoding also used by environment coordinates. That choice was injective, but
it required decomposing an opaque byte operand before native citation rules
could pass it into target data. No such decomposition operation has been
admitted or justified. The occurrence field now uses the ordinary empty or
singleton payload list. Absence remains distinct from a present empty address,
and the artifact still supplies the actual occurrence-membership boundary.
Environment-use coordinates retain their existing natural-component encoding:
their components need not be bytes. This change does not restrict those uses.

Every formed target still has complete data and a finite quotation, and each
presentation uniquely determines its target. The policy that observes an exact
occurrence keeps its original all-coordinate theorem. A coordinate outside the
byte profile cannot occur in
a formed target, so the existing ordinary refusing policy realizes that case.
There is no new test primitive or semantic role attached to the representation.

The citation value has two independent optional operands: a source-local slot
and a target address. Their positions supply their roles; the four constructor
names are not stored. Four ordinary clauses recognize the existing relative
geometry through complete headed material, data inequality, and bag comparison.
The external occurrence form checks the three distinct structural positions,
its two root edges, and the leaf's one functional payload with no counted data.
Local targets may coincide with the root. The complete source remains supplied,
including incoming incidence and unrelated material.

The citation's interior is a separate checked output. Quotation and pattern
composition need it independently of the exposed slot and recovered target.
Its enumeration must contain exactly the actual root and optional address
leaf, with no repeated occurrence and every order permitted. The output adds
no role tag or duplicate target artifact. The raw shape inversion lemmas move
unchanged from the executable theory into the shared structural theory; the
native program calls only ordinary definitions already in its package.

Two target clauses and four citation clauses extend the program to thirty-seven
definitions and sixty-eight clauses. Exactness holds over every input term and
every complete source presentation. One closed native package supplies distinct
target and citation sites before all future formed inputs, preserving the
canonical program environment in every application. The following development
supplies citation interpretation; higher grammar, finite correctness evidence,
reflection, the complete transition protocol, and genesis remain required.

## Environment lookup preserves both exact values and actual uses

The environment under examination is a complete ordinary data argument. Each
lookup first admits both tables and their entire formation boundary. Artifact
lookup selects one actual stored row, then compares its artifact with the
requested output through the existing admitted identity definition. The selected
row supplies a presentation witness; it does not fix the output's enumeration.
Thus every complete output presentation is accepted even when its order differs
from the artifact data stored inside the environment. Binding lookup selects
the exact source use, opaque local slot, and destination use.

An exact target does not determine a destination use. A formed environment may
place the same complete artifact at different uses and bind them differently.
The shared citation result therefore contains both the actual destination use
and complete target data. Its route is derived from the citation's optional
slot: absence selects the source use, and presence selects that source's actual
binding. The displayed route abbreviation adds no primitive or new stored role.

Two ordinary clauses implement those routing cases. Both pass the optional
target address unchanged into target admission. Whole and occurrence targets
therefore share routing while retaining their distinct formation conditions.
The target-value fact formerly local to target admission moves to the shared
value theory; target admission and citation resolution use the same recovery
proof. No target representation or old contract changes in this step.

One ordinary view exposes the target interpretation. Another requires a present
occurrence and exposes the actual use and address. Whole-artifact citations have
no occurrence location. This separation preserves callee locations even when
target artifacts agree. Both views are derived from the shared result, and all
contracts cover arbitrary input terms and every complete environment and target
presentation. No executable reader or externally supplied truth predicate enters
the clause premises.

Five definitions and six ordinary clauses extend the complete program to
forty-two definitions and seventy-four clauses. Every earlier entry preserves
its meaning. One closed native package supplies distinct lookup, resolution,
interpretation, and location sites before all future formed inputs, with its
canonical program environment preserved. Composition with structural citation
and higher readers, finite correctness evidence, the complete internal
transition protocol, reflection, and genesis remain required.

## Structural citation reading remains separate from resolution

The shared reader first recovers the exact source artifact at its actual use
inside the complete supplied environment. It then invokes the existing citation
admission definition on that artifact. The artifact presentation is a shared
internal witness, so the result need not store another copy. The output keeps
the citation and its complete interior enumeration for quotation composition.
Every complete interior order is accepted, and repetition is rejected. The
citation value and interior set are uniquely recovered at the given use and
root. Structural recognition does not require the citation to resolve.

Two further ordinary clauses join this reader to target interpretation and
occurrence location. They derive precisely the existing anchored_at and
located_at judgments. The projected interior is recoverable as a finite
witness, which proves completeness of both views. Whole citations can yield
targets but have no occurrence location. An occurrence location retains the
actual destination use; a different use containing the same artifact cannot be
substituted on the strength of exact target equality alone.

No new observation or truth primitive is added. All three clauses call actual
definitions already in the same package, and all earlier entries preserve their
meaning. Exactness covers every input term and every complete environment and
target presentation. The program now contains forty-five definitions and
seventy-seven clauses. One closed native package provides three distinct reader
sites before arbitrary future formed inputs, with its canonical environment
preserved in every application. Recursive quotation, higher grammar, finite
correctness evidence, the complete transition protocol, reflection, and genesis
remain required.

## Literal target projection and quotation collection operations

A target's data presentation and its literal operand remain separate terms.
Their relation is derived from observations already admitted. Whole targets
call complete artifact projection. For an occurrence, the complete carrier
observation contains a pair of its actual literal and opaque address. An
ordinary lookup selects that pair, while artifact projection uses the same
whole source. This enforces occurrence membership and permits every complete
artifact presentation without another primitive, tagged term encoding, or
external decoding function.

Quotation needs two different ways to combine collections. Concatenation
retains both orders and all repetitions. Inclusion checks each left element
through the existing occurrence-selection definition and explicitly passes
the whole right collection into the next recursive call. This derives set
inclusion without changing the earlier counted-bag comparison. Both operations
check every element and the final empty-payload tail, including the right
operand of each empty case.

Union concatenates its two inputs and checks inclusion against the proposed
output in both directions. Its exact relation permits shared members, every
output order, and repeated output entries. It imposes no separate uniqueness
condition because callers may need membership union independently of a chosen
enumeration profile. Quotation metadata will separately use the existing
distinct-payload entry. Disjointness for those distinct enumerations is derived
by requiring their concatenation to be a distinct payload list. Child
interiors can therefore be separated without forbidding shared external slots.

The five definitions contain eight clauses: seven are ordinary, and occurrence
projection uses the existing complete material equation. They extend the
program to fifty definitions and eighty-five clauses. Every prior entry
preserves its meaning. Exact contracts cover every input term, and one closed
native package supplies five distinct actual sites before all future formed
operands, preserving its canonical environment in every application.
Recursive quotation, higher grammar, finite correctness evidence, the complete
transition protocol, reflection, and genesis remain required.

## Recursive quotation through ordinary native clauses

The existing term grammar is now derived by one recursive definition with
three ordinary clauses. Its argument contains the complete supplied
environment, actual use and root, recovered term, interior enumeration, and
external-slot enumeration. The recovered term uses the existing literal,
payload, and pair operands directly; no further tagged encoding is introduced.
Payload leaves join actual source lookup to the complete headed material
relation. External targets join structural citation reading to interpretation
and the already derived literal-target projection. The shared target data
forces interpretation and literal projection to agree on the exact target.

For a pair, the ordinary record checker supplies both ordered sockets and
child roots. Recursive calls recover the child terms and metadata. Two
concatenations retain the root, sockets, and every child interior occurrence.
The counted comparison then checks the proposed interior, whose distinctness
is required by the final interior/slot separation call. This derives separation
of the record and both child interiors without additional admission clauses.
It also accepts every complete interior order.

External slots use membership union because both children may cite the same
slot. Distinctness is imposed on the proposed complete slot enumeration, and
the final boundary separates that enumeration from the quotation interior.
No separation condition is imposed between the children's slot sets. The
completeness proof chooses finite child enumerations only as internal witnesses
and works for every supplied distinct interior and slot order.

Soundness is proved by induction over the generic positive meaning, and
completeness by induction over the independently defined quotation grammar.
The all-term contract includes input admission; no caller-side formation
assumption can hide a malformed accepted value. Every complete environment
presentation has the same results. The term and metadata sets are unique.
All earlier meanings are preserved, and one closed native reader is fixed
before every future formed operand while preserving its canonical environment.

The program now has fifty-one definitions and eighty-eight clauses. No new
primitive is added. Higher grammar, finite correctness evidence, the complete
transition protocol, reflection, genesis, and the remaining presentation
exactness and composition audit remain required.

## Binder families and complete substitution tables

Four definitions with six ordinary clauses derive the existing binder grammar
and complete finite substitution tables. The two recursive list operations
reuse the existing empty-row clause and inspect every row and final boundary.
No additional observation is introduced.

The key projection preserves the entire key sequence, including multiplicity.
Its keys and values may be arbitrary formed terms. The separate table entry
requires a distinct declared payload scope and compares its multiset with the
projected keys. Thus every declared occurrence has exactly one value, missing
and extra keys are rejected, and the scope and table may be independently
ordered. Functionality follows from counted comparison; a further keyed-list
premise would be redundant. Table values retain the complete term profile,
including literal targets. They are not restricted to self-contained data.

A table is represented by the existing complete list of key/value pairs.
Payload keys carry the actual binder addresses, with no fresh tags or chosen
order. The exact contract is the existing finite functional binding relation
over precisely the declared scope, together with distinct enumerations and
formed address payloads. The singleton theorem covers every formed value.
Every admitted table supplies one unique formed value for each declared key.

The diagonal operation shares a single pattern variable in both fields of
each row. Binder admission joins those rows to the existing complete family
checker. Family admission supplies actual payload addresses, unique sockets,
separation from the root, and empty local material. Each socket's endpoint must
be that same occurrence. Empty scopes still require an admitted family root.
Every complete artifact presentation and distinct scope order is accepted,
and the recovered scope is unique.

All four entries have exact contracts over every input term and preserve every
prior meaning. One closed native program supplies four distinct sites before
arbitrary future formed operands, retaining its canonical environment. The
program has fifty-five definitions and ninety-four clauses. Pattern and schema
admission, finite correctness evidence, the complete transition protocol,
reflection, genesis, and the remaining presentation exactness and composition
audit remain required.

## Pattern instances are read from the actual source and complete scope

Two definitions with four ordinary clauses derive pattern instantiation and
the existing enclosing scoped-pattern judgment. Their operands retain the
complete environment, actual source use and root, complete substitution table,
resulting term, and exact metadata. The relative entry also retains the declared
scope and the set of variables actually used by the body. No new pattern tags,
pattern codec, substitution callback, or material primitive is introduced.

The relative entry has variable, constant, and pair clauses. A local citation
retains its actual binder address and reads the unique value from the admitted
table's complete key fibre. Table admission already supplies precisely one
formed value per declared occurrence. This includes literal targets and arbitrary
formed pairs. The fibre theorem derives singleton lookup from complete collection
and functionality; it does not add an external lookup operation.

A separate theorem proves that term quotation is exactly a quoted pattern with
no variables, instantiated under arbitrary bindings, with its interior outside
the declared scope. The constant clause therefore reuses the existing reader
for all constant branches. Constant pairs can also use the recursive pair
clause. This overlap permits additional derivations of the same judgment; the
exact contract proves that it adds no other results. The constant clause is
needed for leaves, and the pair clause is needed for pairs containing variables.
Reusing the complete reader avoids separate duplicate target and payload logic.

Both recursive pattern calls receive the same complete scope and table. Their
admission supplies the parent table condition, so the pair clause does not
repeat it. Counted concatenation retains every syntax occurrence and rejects
shared interiors. Used-variable and external-slot collections use membership
union: either may be shared across children. Those two sets may also intersect
where the relative grammar permits it. The interior must be separate from the
external slots and the declared scope. The proposed used-variable enumeration
has its own distinctness check.

The enclosing entry reads the actual binder family, applies the body entry,
and compares the complete used-variable and declared-scope collections. This
requires every declaration to be used. The table domain is then exactly the
recovered pattern's variable set. Counted interior composition includes the
outer record, binder root and every binder occurrence, and the entire body.
The final boundary separates all of that material from external slots.

Soundness and completeness hold over every input term and every complete
environment, scope, table, and metadata presentation. Different orders remain
independent. Resulting terms and metadata sets are unique, and every valid
scoped pattern with a complete formed table has one result. The recovered
pattern remains the independently defined structural reading of the source,
not another operand chosen by the caller.

All earlier meanings are preserved. One closed native program contains two
distinct new sites before arbitrary future formed operands and retains its
canonical environment. It now has fifty-seven definitions and ninety-eight
clauses. Schema and package admission, finite correctness evidence, the
complete transition protocol, reflection, genesis, and the remaining
presentation exactness and composition audit remain required.

## Prospective instances retain actual callees and recover ground applications

Two definitions with one ordinary clause each derive prospective-call
instantiation and ground application reading. The first joins the existing
two-field record, structural citation reader, occurrence-location reader,
and pattern instantiator. It receives the complete environment, actual
source use and root, declared scope and substitution table, resolved callee,
substituted argument, and exact used-variable, interior, and slot collections.
The recovered argument pattern remains the independently defined structural
reading of the source; no pattern codec or external substitution callback is
added.

The callee is its actual use and occurrence address. Exact artifact values
do not replace use identity, even when two uses contain equal artifacts.
The location operation already rejects whole-artifact citations, so the
call clause needs no extra constructor test. It does not require the
located occurrence to be a formed definition. Definition recovery, package
membership, interface acceptance, and positive truth retain their separate
judgments, including for a local or self citation.

The body operation already admits the complete table and its declared scope.
The enclosing clause does not repeat that check. Its used-variable collection
is the body's exact set and need not exhaust the declared scope. Counted
concatenation of the record, citation, and body interiors enforces all syntax
separations. Membership union permits shared external slots. The complete
interior is disjoint from both slots and declared variables, while those two
reference sets may intersect where the relative grammar permits it.

A separate theorem proves that an existing ground application is exactly
an empty-scope prospective call instantiated under any binding relation.
An empty scope forces the pattern to be ground, and the earlier constant
quotation theorem recovers the same argument term. This proof preserves
the same record, citation, roots, interior, and slots in both directions.
The native application entry specializes the scope, table, and used-variable
collection to empty values. It introduces no binder node and changes no
existing application geometry.

Both entries have exact contracts over every input term, all complete source
presentations, and independent distinct metadata orders. Prospective instances
are total for valid calls with complete formed bindings. The resolved callee,
substituted argument, and metadata sets are unique. All prior meanings are
preserved, and one fixed closed native program contains two distinct new sites
before arbitrary future formed operands. Its canonical environment remains
unchanged. The program now has fifty-nine definitions and one hundred clauses.
Schema and package admission, finite correctness evidence, the complete
transition protocol, reflection, genesis, and the remaining presentation
exactness and composition audit remain required.

## Ordered field instantiation preserves the independent grammar boundaries

Four definitions with six ordinary clauses derive complete row-value projection,
vector instantiation, record instantiation, and five-field material instantiation.
Row projection preserves every supplied occurrence in its original order. Values
may be any formed term, including literal targets. Applying a payload-and-pair
data recognizer to these results would wrongly restrict ordinary substitutions.

The vector entry instantiates each actual pattern root under the same complete
declared scope and binding table. Counted comparison of the joined interiors
forbids reused syntax occurrences. Membership unions permit shared variables and
external slots; those reference sets may intersect where the relative grammar
permits it. The used-variable enumeration is distinct and complete, independently
of the declared scope. Field order is retained rather than treated as another
unordered metadata presentation.

The empty-vector clause admits the complete environment, use coordinate, and
binding table. It does not require an artifact at that use: the independently
defined empty-vector judgment has no source occurrence. The nonempty clause
obtains actual source reading from its head pattern. Its recursive child calls
supply the complete-table checks, so it adds no separate table premise.

The record entry first reads its actual artifact and record root. Complete key
and value projections recover the ordered sockets and pattern roots from those
same rows. The vector entry checks all fields, including zero fields, while
counted composition includes the record root, every socket, and the entire
vector interior. The whole interior remains separate from external slots and
the declared scope. Empty records therefore retain their actual root check.

The material entry is a one-clause specialization to the existing five-field
record. Its output uses the already defined material tuple, and the recovered
material pattern remains determined by the source. No discriminator, separate
pattern codec, or material truth premise is introduced. Reading and substitution
do not assert satisfaction of the complete material equation; that remains the
separate material observation over the five resulting operands.

All four entries have exact contracts over every term and preserve all previous
meanings. Complete environment presentations and independent scope, table, and
metadata orders are accepted. Vector, record, and material instances have
unique results and are total for valid inputs with complete formed bindings.
One fixed closed native program contains four distinct sites before all future
formed operands and retains its canonical environment. The program now has
sixty-three definitions and one hundred and six clauses. Complete premise,
schema, package, and finite evidence admission, the transition protocol,
reflection, genesis, and the remaining presentation exactness and composition
audit remain required.

## Mixed premise instantiation preserves the complete socket boundary

Two definitions with four ordinary clauses instantiate ordered premise rows and
the actual complete family. The row operation copies each socket to its call or
material output. Calls retain the callee use, address, and actual substituted
argument. Material rows retain the existing five-operand tuple. Their roles are
recovered from the source's two-field and five-field records; no discriminator
or separate pattern encoding is added to the argument data.

The row operation requires formed payload socket keys and shares the complete
scope and binding table across its children. It preserves repeated source rows,
and its used-variable result is a complete distinct membership union. Each
child retains its own existing syntax and slot checks. The family grammar does
not require separation between different premise interiors, so the family
reader adds no global separation check. Shared endpoints and shared syntax
remain admissible wherever the existing relative grammar permits them.

The family entry first selects the actual artifact and admits the complete
family graph. This supplies its finite functional socket boundary, including
an actual root for an empty family. Row traversal then accounts for every
socket exactly once in the corresponding output. Distinct sockets remain
distinct when their endpoints or instantiated values agree. Missing, extra,
and overlapping call/material socket domains cannot pass that boundary.

The mathematical call projection is proved equivalent to the existing schema
premise instance under complete formed bindings. The material projection fixes
one five-operand tuple per material socket. Neither projection asserts callee
truth or satisfaction of a material observation. These remain separate
judgments over the resulting operands.

Call and material output orders are independent. For every pair of complete
distinct output enumerations, a corresponding complete enumeration of the same
actual source family exists. This construction does not use data-only bag
comparison on the instantiated values: those values may contain literal
targets. Within an ordered row traversal, each output part preserves the input's
relative order. The family root has no represented order and admits every such
complete presentation.

Both entries have exact contracts over every term and preserve all previous
meanings. Complete source presentations and independent scope, substitution,
call-row, material-row, and variable-use orders are accepted. Family outputs
are unique up to enumeration and total for valid inputs with complete formed
bindings. One fixed closed native program supplies two distinct sites before
all future formed operands and retains its canonical environment. It has
sixty-five definitions and one hundred and ten clauses. Schema and package
admission, finite evidence checking, the complete transition protocol,
reflection, genesis, and the remaining presentation exactness and composition
audit remain required.

## Whole-schema instantiation and material checking have separate meanings

Four definitions with five clauses extend the admitted reader. Whole-schema
instantiation uses one ordinary clause to read the actual three-field record,
binder family, conclusion, and complete mixed premise family. One complete
binding table accompanies every pattern. The union of all used variables must
equal the actual declared scope. A variable used only in a material operand is
therefore required just as a variable used in the conclusion or a call is.

The disjointness conditions are represented separately because the existing
schema grammar does not specify one aggregate interior. The outer record must
be disjoint from the binder interior, conclusion interior, and family root.
Both the binder root and family root are outside the conclusion interior and
distinct from each other. A family root is not additionally required to be
outside the declared variable set. Nor are different premise interiors required
to be disjoint, or new restrictions imposed on external slots. These choices
preserve the established relative grammar over its full domain. No additional
schema encoding or nominal discriminator is introduced.

The material-observation entry uses the existing material premise and reuses
its existing five-variable pattern. Its argument is the existing five-operand
tuple, and its truth is exactly the complete material equation. The row entry
uses ordinary recursion to check every supplied socket key and operand tuple,
including the final empty tail. It preserves the supplied sequence, including
repeated rows. Its own meaning does not claim that the sequence is a complete
schema family; that boundary belongs to the schema-instantiation entry.

The final ordinary clause joins those separate entries. The equivalence proof
starts from every actual material pattern's instance under the same complete
binding table. It establishes exactly the existing schema material-satisfaction
judgment. Missing, extra, or role-swapped socket domains cannot pass schema
instantiation, even if every supplied material row individually holds. An empty
material list cannot stand in for a nonempty actual material projection.

All four entries have exact contracts over every term and preserve earlier
meanings. Both schema entries permit every complete source presentation and
independent substitution, call-row, and material-row orders. Their conclusions
and projections are unique up to enumeration. Schema instantiation is total for
valid native schemas and complete formed bindings. The combined entry has an
output exactly when the actual material equations hold.

One fixed closed native program supplies four distinct sites before all future
formed operands and retains its canonical environment. It has sixty-nine
definitions and one hundred and fifteen clauses. The complete admitted-schema
instance additionally requires the actual program's head and prospective-call
interfaces. Those checks, definition and package admission, prospective-call
truth, finite evidence checking, the full transition protocol, reflection,
genesis, and the remaining presentation exactness and composition audit remain
required.

## Grammar admission precedes material and prospective-call truth

Four definitions with five ordinary clauses extend the admitted native reader.
Schema admission existentially hides a complete instance under a complete
substitution. Every formed schema has such an instance. The proof uses an
empty-payload value for each variable only to establish inhabitation; the
operation does not store or constrain substitutions to those values. Material
checking is a separate operation. A false material condition or unsupported
prospective call therefore does not make otherwise valid schema syntax unreadable.

The schema-root list reuses the existing context-carrying profile. Its empty
case accepts any formed context, so it alone does not claim that a source was
inspected. The clause-family operation separately reads the actual source and
complete family graph, projects all endpoints in the chosen row order, and
checks every endpoint. It retains the actual root for an empty family. A
complete finite functional schema table is constructed by composing the actual
socket graph with unique native schema readings. Distinct sockets may still
share endpoints or equal schemas. No schema codec, selected subset, or
additional family primitive is introduced.

Definition-interface admission takes the complete source, actual use, actual
root, and supplied operand. One ordinary clause reads the actual two-field
record, instantiates its actual scoped interface, admits its complete clause
family, and checks the existing three separation conditions. The interface's
external slots and the interiors of different clauses acquire no additional
separation requirements. Hidden substitution and metadata witnesses are exact
instances of the existing grammar; they are not new definition fields.

Every valid native definition admits an operand, including a definition with
an empty or unsatisfiable clause family. At an actual reached site of an already
formed package, the operation is equivalent to that program's call formation.
The package and site hypotheses remain explicit: reading one definition does
not establish the complete closure of its prospective callees.

All four entries have exact contracts over every term, preserve earlier
meanings, and permit every complete environment presentation. An unreadable
actual clause cannot be omitted. One fixed closed native program supplies four
distinct sites before all future formed operands and retains its canonical
environment. It has seventy-three definitions and one hundred and twenty
clauses. Native package admission, complete admitted instances, finite evidence
checking, the full transition protocol, reflection, genesis, and general
presentation exactness and composition remain required.

## Finite checked witnesses preserve the actual least package closure

Five definitions with seven ordinary clauses derive package closure over
supplied root-site lists. They reuse complete schema instantiation, row-value
and row-key projection, list inclusion, definition-interface admission, actual
record and family reading, and the existing context-carrying list profile.
The source schema's complete instance has exactly its actual prospective
callees, regardless of substitution or row order. Material truth is not needed
to read those dependencies.

The definition operation admits the actual interface and complete clause
family, rereads that same actual record and graph, and checks every schema
endpoint against one unchanged bound. Unique source and schema recovery
identifies the checked endpoints with precisely the definition's clauses.
Distinct sockets may share endpoints or equal schemas. An independent
empty-list inclusion call checks the complete bound even when there are no
clauses. Every bound element is then checked as an actual definition, including
all of that definition's callees.

The package operation admits the entire source environment and includes every
supplied root in a hidden finite bound. The bound is a witness to successful
closure checking, not an added native field or semantic definition domain.
The proof establishes both directions: every successful bound contains the
existing least root closure, and that finite closure itself provides a
successful bound whenever the raw package is formed. Additional checked
members, repetition, and enumeration order therefore cannot change the
semantic package. An unreadable reached definition cannot be omitted.

This witness choice is not fixed by the supplied material. It is admitted
because it derives the required closure check from existing operations while
preserving the exact raw meaning. Every callee is selected by its actual
prospective citation and then compared with the supplied bound. The witness
does not select a callee, dispatch a definition by a nominal name, scan every
environment position, or replace the actual least closure. Cycles are admitted
under the existing positive semantics without an acyclicity condition, depth
limit, or preselected traversal order.

All five operations have exact contracts over every term and preserve earlier
meanings. Every complete source presentation is permitted. The package entry
accepts every supplied list with the same root set. Its empty-root case still
checks the source environment, even when that environment is empty. One fixed
closed native program supplies five distinct sites before future formed
operands and retains its canonical environment. It has seventy-eight
definitions and one hundred and twenty-seven clauses.

The supplied root-site list is an ordinary argument to this entry. Actual
package-root reading is composed with it below. Joining call admission with
actual reached-site membership, complete admitted instances, finite evidence
checking, the full transition protocol, reflection, genesis, and general
presentation exactness and composition remain required.

## Actual package roots preserve their complete occurrence correspondence

Three definitions with four ordinary clauses compose the existing located
citation, complete list, row projection, actual artifact and family reading,
and supplied-root closure entries. No new grammar form or semantic primitive
is admitted.

The location-list entry carries the same source environment and use into
every reference-destination pair. Its standalone empty case accepts any
formed context. The root-family reader separately reads the actual artifact
and complete family graph, projects every reference endpoint, and constrains
the first projection of one complete located-pair list to that entire
endpoint list. Its second projection supplies the destination list. Both
projections traverse the same pairs, so there is exactly one destination
occurrence per actual socket.

The list presentation is a derived interface choice. Every distinct
enumeration of the actual family and its corresponding destination list is
admitted. Distinct sockets may share a reference endpoint or located
destination. Repeated destinations remain present; equality of destination
sets alone is insufficient for this reader's exact contract. Family formation
already supplies unique socket keys. The proof reconstructs the raw root
family by pairing those keys with the corresponding destinations, proves its
exact domain and range, and uses raw uniqueness to identify every recovered
family. This graph is a proof witness, not a new native field or stored
semantic encoding.

The package entry hides that complete destination list and joins the reader
to the existing closure checker. Its answer is exactly existence of the
native package at the supplied actual root. The original least definition
closure determines the program; neither enumeration order nor a larger
checked closure bound can replace it. Source lookup and actual family
formation remain necessary for empty packages. Every reached definition is
still required, including callees in positive cycles.

All three entries have exact contracts over every term, permit every complete
source presentation, and preserve earlier meanings. One fixed closed native
program has three distinct sites before future formed operands and retains its
canonical environment. It has eighty-one definitions and one hundred and
thirty-one clauses. The following entries join reached-site and interface
admission to complete instances. Finite evidence checking, the full transition
protocol, reflection, genesis, and the remaining presentation exactness and
composition audit remain required.

## Actual clause membership and every call share one package

Seven definitions with nine ordinary clauses derive actual clause selection,
definition edges, package membership, generic call admission, actual
application admission, complete call lists, and admitted schema instances.
They reuse existing grammar, complete instantiation, material checking, row
projection, selection, and context-carrying lists. No semantic primitive is
added.

A clause socket selects its actual row in the actual definition's complete
family. The result retains the unique schema root at that row. Equal schemas
at other roots cannot substitute for it. A shared raw family lemma now
identifies both complete socket coverage and the schema at each actual row;
the previous universal family-property proof reuses that result. Actual
clauses and complete instance projections then expose exactly the existing
prospective definition edges, independently of material and call truth.

Package membership starts from the admitted actual root family and follows
those actual edges by positive recursion. The proof identifies its result
with the existing least reached definition domain in both directions.
Hidden closure bounds cannot supply additional members. An empty package
has no members, and positive dependency cycles require no acyclicity
condition or traversal limit.

The package context groups the complete environment, package use, and package
root, then accompanies a supplied subject. This tuple grouping is a derived
interface choice that permits reuse of the existing context-carrying list
profile. The same context is used for a definition site, a callee-operand
pair, an actual application site, and a complete call list. Each operation
has its own actual fixed native entry; these subject layouts add no native
grammar constructor or nominal dispatcher.

The shared call entry checks both membership in that actual package and
the actual definition interface at the supplied operand. Every reached
definition has some admissible operand. Application admission reuses the
complete application reader and then this same call entry. The list entry
checks every callee and operand against one unchanged package. Operands may
be arbitrary formed terms, including literal targets. Repeated equal calls
remain separate occurrences. Its standalone empty case only admits context
formation; the complete instance entry separately admits its head call and
package even when the call list is empty.

The complete instance entry binds the head and complete substitution to an
actual clause of the actual reached definition. Its material conditions and
every ordinary premise come from the same complete schema instance. It
checks the head interface and all prospective-call interfaces under the
same package. Every material row is read and checked before the hidden
material list is discarded. That list is an existential witness in this view;
the existing admitted-instance relation already has no material-row output
field. Complete binding and call rows remain supplied explicitly.

Acceptance is exactly the existing admitted-instance relation with distinct
complete row presentations. Every admitted instance permits all independent
row orders and every complete source presentation. Given its substitution,
the result is unique up to row enumeration. This does not require an
instance to exist when a clause's interfaces or material equations prevent
one. Missing or extra call sockets, false material conditions, and unformed
prospective callees are rejected. Prospective-call truth remains separate
from their formation.

All seven entries have exact contracts over every term and preserve earlier
meanings. One fixed closed native program has seven distinct sites before
future formed operands and retains its canonical environment. It has
eighty-eight definitions and one hundred and forty clauses. Finite correctness
evidence checking, the full transition protocol, reflection, genesis, and the
remaining presentation exactness and composition audit remain required.

## Native proof metadata preserves actual rows and independent validity

Seven definitions with ten ordinary clauses derive located citation reading,
two-endpoint links, complete binding and premise-link vectors and tables,
and the existing assertion and inference metadata. They compose already
admitted grammar, location, row projection, key uniqueness, and collection
operations. No semantic primitive is added.

The existing binding and discharge table projections and properties move
from Factor_Proof_Metadata to Factor_Table_Metadata. Their definitions and
statements are unchanged. Table admission therefore does not import the
proof-node datatype or derivation. The node reader imports the existing
datatype and raw node grammar to state its exact contract. Its ordinary
clauses contain no graph-validity, derivation, replay, or evidence predicate.

The list profile reuses the existing reading-argument grouping: one context
accompanies the root, result, interior, and external slots. The concrete
readers use the environment and actual source use as that context. The
standalone empty vector only admits context formation. Each table separately
reads its actual artifact and complete family, including when the family is
empty. No dummy source read or hidden empty-table exception is added.

Every physical socket contributes one row result. Both the raw table and
the ordinary checker require injective decoded keys, even when two values
agree. Completeness holds for every distinct output enumeration: the proof
derives a corresponding enumeration of the actual sockets from the raw
table's complete functional reading and key injectivity. That order is a
temporary witness. The table gains no represented order, and arbitrary
formed binding values, including literal targets, pass directly through the
reader. A data-only comparison of row values would have narrowed that
boundary and is not used.

Interior combination preserves counts. The family root and sockets, each
row record, and all child interiors contribute exactly once, enforcing the
existing physical separation conditions. External slots combine by
membership and may be shared. Complete output, interior, and slot orders
remain independent. The common table proof supplies exact recovery,
repeated-key rejection, source-presentation invariance, and uniqueness for
both binding and premise-link tables.

The recovered node value uses the arity already present in the native
grammar. An assertion has the empty value. An inference has three fields:
its actual clause site, complete binding rows keyed by actual variable sites,
and complete premise links keyed by actual socket sites. This is a derived
value-presentation choice; it adds no stored field or constructor tag to the
native grammar. The two finite collections permit every complete order.
Each complete value uniquely recovers the node and its discharge relation,
and every native node has such a value. No conclusion or assumption
collection is duplicated in the node.

Node admission recovers exactly the raw syntax and boundary. It does not
establish that links form a rooted acyclic graph, that assertions have the
required distinct origins, that a selected clause admits the claimed
instance, or that an assumption is true. Those checks belong to the
independent graph and derivation relations and the ordinary finite evidence
checker built above this metadata layer.

All seven entries have exact contracts over every term and preserve all earlier
meanings. One fixed closed native program provides seven distinct sites before
all future formed operands and retains its canonical environment. It has
ninety-five definitions and one hundred and fifty clauses. The following
entries separately derive complete finite graph admission and reachability.
Derivation, replay retention, the full transition protocol, reflection,
genesis, and the remaining presentation exactness and composition audit remain
required.

## Native graph admission retains actual closure and shared nodes

Four definitions with nine ordinary clauses derive complete premise-link
checking, finite node-bound checking, native graph admission, and actual
reached-site membership. They compose existing node reading, complete key
collection, key absence, key uniqueness, data recognition, append, and
selection. No graph, derivation, replay, or evidence predicate occurs in a
program clause.

A list of actual node sites with their complete recovered values is an
internal witness. Each node's premise targets must lie in its strict remaining
tail. This order is a derived interface choice: it witnesses finite acyclicity
without storing a rank, order, or new field in a native proof. Every finite
closed acyclic graph has such an enumeration. Different parents may point
to the same later inference node.

Each premise lookup must return exactly one child value. An empty value
identifies the existing assertion form and contributes its actual target
site paired with its parent and socket. A three-field value identifies the
existing inference form and contributes no assertion origin. The traversal
checks every link and its final boundary. A bound reads every listed value
from the same complete source presentation; the link traversal alone does
not establish native metadata.

The complete origin list follows the chosen node and link enumeration.
Every origin occurs once because bound sites and each node's actual premise
rows are distinct. Ordinary key uniqueness is therefore exactly functional
assertion use. Distinct premise sockets cannot share an assertion, even when
their claims would agree. Shared inference nodes remain permitted. A root
assertion needs no incoming origin and has exactly itself as its graph;
every nonroot assertion in an admitted rooted graph has one origin.

Bound values may contain arbitrary formed literal targets. Key operations
inspect their keys without subjecting their values to data-only comparison.
Only the recovered site-and-origin rows pass through data append. Each node
retains exactly the raw grammar's syntax boundary; there is no additional
global disjointness condition across different nodes.

The standalone empty bound admits any formed context and returns no origins.
Graph admission separately requires actual root membership through the
complete key collector, so that case cannot admit an empty graph or an
unreadable root. A larger checked bound may witness existence, but the graph
is always the actual least root closure with every complete node and premise
relation retained. Its projection is unique. The membership entry starts at
that admitted root and follows actual premise rows; extra bound members
cannot enter its result.

All four entries have exact contracts over every term, admit every complete
source presentation, and preserve earlier meanings. One fixed closed native
program provides four distinct sites before all future formed operands and
retains its canonical environment. It has ninety-nine definitions and one
hundred and fifty-nine clauses. This admits graph structure independently of a
supplied root claim. The following claim-table construction supplies the
complete derivation join. Replay retention remains separate, as do the full
transition protocol, reflection, genesis, and the remaining presentation
exactness and composition audit.

## Complete derivations use one shared claim table

Four definitions with eight ordinary clauses derive row-key qualification,
complete keyed-row joins, checking of all supplied node claims, and native
derivation admission. The derivation entry receives the actual package site,
proof root, supplied call, and complete identified assertion boundary. It
admits exactly the existing graph derivation in that actual package.

The inferred interface choice is one finite functional table from actual
node sites to calls. It is a temporary witness, separate from the native
node fields. Every node is an actual member of the same admitted rooted
graph. Every inference joins all of its actual premise sockets to that same
table. The complete traversal and root lookup force the table to contain
exactly the reachable nodes. One shared node has one call even when several
incoming sockets or definition clause families could otherwise permit
different claims.

Qualification uses the semantic use of the owning definition. A local
definition address is not part of a binder, socket, or clause site. One
ordinary pair construction handles binding keys and premise keys, preserving
all values and their order. The positioned-instance inverse follows from
the exact binding and premise domains and recovers the actual local package
instance, including all material conditions and callee interfaces.

Key uniqueness is checked once at the traversal's empty clause. The complete
table is then shared unchanged by every recursive call and child lookup.
The standalone walker may check a sublist; its exact contract exposes that
sublist and the full table separately. An empty walk retains arbitrary formed
context fields and a checked table. The derivation wrapper traverses the
entire table and requires its root entry, so a witness cannot omit the root
or all native readings. No topological order is required for these claims;
the separate graph admission already establishes finite acyclicity.

Assertions select their complete rows in traversal order. Their output is
constructed directly, preserving arbitrary formed call terms, including
literal targets. Every distinct enumeration of the exact assertion boundary
extends to a complete claim-table enumeration. Equal calls at different
assertion sites remain distinct assumptions. A closed derivation establishes
its supplied call's positive meaning; conditional assertions retain their
independent truth requirement.

The complete program has one hundred and three definitions and one hundred and
sixty-seven clauses. Four distinct sites in one fixed closed native program
precede every future formed operand and preserve its canonical environment. The
replay join must bind an actual application to its derivation and closed
retention. Full transition protocol, reflection, genesis, and the remaining
presentation exactness and composition audit remain open.

## Slot reading exposes existing syntax projections independently of truth

Replay retention needs the references actually read by each selected grammar.
The existing definition and schema slot projections already specify those
references. Preserve their meaning and derive their ordinary reading through
the existing instantiation operations.

Every finite scope has a complete formed substitution. Pattern, prospective,
and material instantiation is total under such a substitution. The slot reader
can therefore hide that table and its resulting values after selecting an
actual member of the complete slot output. This introduces no call-truth or
material-satisfaction premise and requires no additional pattern value format.

The premise entry retains an explicit distinct enumeration of the declared
scope. Schema reading obtains that scope from its actual binder, then reads
either the conclusion or a premise at an actual complete-family endpoint.
Definition reading obtains the actual interface and schema family from its
two-field record. All coordinates retain their existing owning use.

These are exactly the existing partial slot projections. A readable field can
contribute a slot even if another part of its enclosing definition or schema
fails admission. Keeping that distinction is an inferred implementation choice:
whole-role admission belongs at the caller that needs it. In replay retention,
the actual package, application, and graph must establish the global grammar
before coverage by these projections can establish the closed environment.
A supplied collection cannot choose that boundary.

Three entries add six ordinary clauses. Their contracts cover all terms,
preserve every complete source presentation and every distinct scope order,
and prove that every reported slot is bound in the same environment. All old
meanings remain unchanged. One closed native program with one hundred and six
definitions and one hundred and seventy-three clauses fixes three distinct
entry sites before any future formed operand. Replay-retention coverage and
the actual application/derivation join remain open.

## Replay admission composes complete coverage with the actual application

The existing replay value already stores the complete environment once and
three actual sites. Reuse that value. The replay query supplies a complete
assertion-boundary enumeration as its result; no program, call, graph, or
assumption field is added to the stored value.

Under actual package, application, and graph readings, closed retention is
equivalent to two finite inclusions. Every stored binding key must belong to
the grammar's demand set. Every stored use must be a structural source or an
actual binding target. The existing reachability results prove this
equivalence, including passive literal targets and shared uses. Whole artifact
values remain the retention unit.

The source and slot helpers read the role used by their selected branch.
Other context fields need only be formed until the enclosing retention entry
admits all three roles. This is an inferred composition choice: keep the
helpers' exact partial contracts and establish the common formation boundary
at the join. Rechecking every role inside every branch adds no independent
condition. Source coverage alone does not justify a stored binding, and a
binding cycle cannot justify keys that no selected grammar reads.

Two existing row projections recover every key from the actual complete
environment lists. Two ordinary context-list profiles then check all those
keys and the final list boundaries. Private witnesses cannot substitute
smaller coverage lists. Canonical restriction always supplies an admitted
retention value, independently of derivation validity and call truth.

The retention entry also returns the application's actual callee and operand.
The replay clause supplies those same two values, in the same environment, to
derivation admission. This intermediate result is derived and is not stored in
the replay value. Thus a proof of a different call cannot complete the join.
Every distinct enumeration of the exact identified assumptions is admitted;
shared nodes and arbitrary formed call terms retain their existing meanings.

Six entries add fifteen ordinary clauses. All input-term contracts, complete
presentations, assumption orders, earlier meanings, and the fixed native
program before every future formed operand are proved. The complete program has
one hundred and twelve definitions and one hundred and eighty-eight clauses.
Full transition-protocol admission, reflection, genesis, and general
presentation exactness and composition remain open, followed by the requested
final audits.

## Positive meaning is recognized with the supplied program as data

The independent positive meaning already has finite closed graph completeness,
and every such graph has a native realization extending the original complete
environment. Compose those results with ordinary derivation admission. The
result is one fixed native positive interpreter before the program being
queried and its future operands, rather than a new compilation for each query.
No semantic callback is added to the operator.

The query retains every original artifact and binding in a private formed
extension. Its original actual package is admitted before proof checking.
Package locality proves that the extension recovers the same program. The
proof must be closed and have the supplied callee and operand at its root.
Soundness recovers the original least-fixed-point meaning; completeness
constructs the finite witness. Proof existence is a derived characterization
and does not replace the definition of meaning.

Complete environment inclusion needs two different existing comparisons.
Artifact rows use admitted lookup at the exact use so every complete child
presentation is permitted. Exact byte equality of the rows would wrongly
reject different enumerations of one artifact. Binding rows have a fixed
injective encoding, so ordinary data inclusion suffices. Both whole
environments are admitted, including the empty case. The artifact-list helper
keeps the existing partial empty-list contract; the enclosing entry supplies
the environment formation boundary.

Keeping the entire input environment is an inferred choice. A judgment can be
queried in a containing environment with material beyond its minimal scope;
requiring closed replay retention there would impose an unrelated input
restriction. The internal proof extension is not a stored judgment field.
The final entry reads the existing actual application and passes its callee
and operand to the query in the same represented environment. The existing
judgment value already stores exactly the required environment and sites.

Four entries add five ordinary clauses and preserve all earlier meanings. Their
exact contracts cover all input terms and all complete presentations. One
closed native program has one hundred and sixteen definitions and one hundred
and ninety-three clauses. Exact positive recognition does not imply termination
for false queries or prove universal correctness of a submitted historical
interpreter. That correctness, full protocol admission, general reflection,
genesis, presentation exactness and composition, and the final audits remain.

## Formation and meaning reflection share a represented source

The existing formation admission and positive query have the same complete
source-and-call argument. Retain their separate entries in one fixed native
program. Formation remains the independent package-interface relation, and
truth remains the independent least positive fixed point. Neither becomes a
supplied callback. Exactness over every input term establishes the output
boundary as well as agreement on represented calls. Generic equality gives
an infinite family of true reflected calls and a formed false call, so the
reflected domain is neither empty nor a finite sample and formation is not
identified with truth.

A historical interpreter can now use the original program as ordinary data.
The inferred construction choice is to specialize the fixed checker with two
ordinary clauses. Each retains the complete environment and actual package
coordinates through the existing exact-term pattern operation; the conclusion
keeps one arbitrary future operand. One clause calls formation admission and
the other calls the positive query. There is no new quotation encoding,
variable-length family of source-specific active rules, or truth primitive.
The two clauses express different public relations even though their source
constants agree.

The independently specified historical interpretation contract is proved for
every native source package. The whole source environment may contain material
beyond that package. Different complete presentations and formed extensions
produce identical interpretation results for all operands. The constructed
program preserves every earlier checker call and meaning; its exact definition
set is the fixed checker plus the two new entries, transported by compilation.
Every resulting definition is exported as an actual root. Complete supporting
material is available to the current frame before any candidate history,
cause, or adoption presentation is fixed.

The earlier historical construction remains useful because it additionally
preserves direct calls to separately copied old and other programs. The new
construction proves a different sufficient class with one uniform interpreter.
Neither construction admits an arbitrary submitted interpreter's universal
correctness evidence inside the predecessor. That finite evidence profile, full
transition-protocol admission, the remaining reflection strata, genesis,
presentation exactness and composition, and final repository audits remain
open.

## Two complete substitutions determine pattern and schema syntax

The inferred choice is to reuse the existing instantiation readers for finite
syntax evidence. A new tagged pattern codec is unnecessary for this purpose.
One substitution maps each scoped variable injectively to a payload; the other
maps every variable to one target. Constructor separation and structural
induction recover the entire pattern. The target has no distinguished semantic
role: the algebraic theorem permits any target, and native evidence uses the
already formed whole empty artifact. Native binder addresses themselves supply
the injective payloads, with their formation derived from the actual binder.

The schema result retains its conclusion, every prospective socket and callee,
and all five operands at every material socket. Functional source rows align
the two readings at the same socket. Complete material output is necessary:
two different schemas can have identical conclusion and prospective instances
under every substitution while one adds a material condition. Instantiation
continues to make no assertion that that condition is satisfied.

The exact native criteria use the existing source environment, actual use and
root, complete bindings, and complete output metadata. For schemas, the finite
reference outputs are first calculated from the expected syntax. Two admitted
readings at the same actual source then prove that this expected schema is the
one recovered there. Every native schema supplies both readings. The comparison
is relative to the actual binder coordinates; it does not silently identify
renamed syntax or distinct artifact values. Existing presentation and ordering
theorems continue to apply.

No operator definition, ordinary entry, or primitive observation is added. This
grammar result supports finite correctness evidence and says nothing by itself
about agreement of arbitrary programs from finitely many executions.
Whole-program interpreter admission still needs complete structure and actual
semantic dependencies. The remaining presentation exactness and composition
audit, the full transition protocol, remaining reflection strata, genesis, and
final audits remain open.

## Complete scope forwarding from finite native evidence

The existing scope-call schema now has explicit polymorphic binder, socket, and
callee parameters. Its earlier numeric construction remains the instance with
binder and socket zero. The ordinary empty-material schema abbreviation is also
polymorphic. These changes reuse the same fields and clause rather than adding
another native operation for specialization.

The selected sufficient definition profile has a variable interface, exactly
one clause, a variable conclusion, exactly one prospective callee, and no
material conditions. That call retains three fixed scope operands and the
arbitrary future input. Interface and clause binders are independent. Their
actual addresses, the clause socket, and its premise socket are recovered
witnesses; they are not fixed semantic names.

Eight ordinary premises check the entire profile. Existing definition admission
retains its enclosing grammar and separation conditions. Artifact lookup and
the complete record and family readers identify the interface and the sole
schema at their actual roots. Two interface readings and two complete schema
readings determine the expected syntax. Both schema readings return the empty
material relation. The selected callee stays ordinary data throughout this
admission; it is not dynamically invoked to establish the submitted claim.
The checker rejects empty clause families, additional clause sockets, and any
material condition.

The semantic justification uses an additional general locality consequence.
When two formed programs agree on their shared definitions, that intersection
is dependency closed: every shared definition's callee belongs to both
programs. Two native packages in the same environment have precisely that
agreement because an actual definition has one complete reading. Every shared
call therefore has the same formation and truth under either package. This
allows a proven callee to retain its established meaning in a candidate package
without imposing a copy of every unrelated definition or an additional
registry of trusted sites.

Every admitted forwarding entry in a formed package has an equation over all
future terms, including the complete call boundary. Definition admission alone
does not establish membership in such a package. Every formed scope has a native forwarding
definition over an existing anchored callee; installation preserves all prior
artifact values and bindings. Every actual profile admits every complete
environment presentation. One fixed closed native checker serves all later
submitted terms and retains its original scope.

The profile is sufficient and intentionally specific. It does not decide
equivalence of arbitrary programs or establish that an arbitrary chosen callee
is an interpreter. The next historical admission join must fix an independently
proved interpreter before candidates, retain its complete environment, and bind
both checked entries to the actual candidate program. The full transition
protocol, remaining reflection strata, genesis, presentation-class and
intrinsic-link obligations, and final repository audits remain open.

## Whole-interpreter admission with a fixed semantic reference

A finite correctness class now connects the admitted forwarding definitions to
the complete historical interpretation contract. The checker contains the exact
reference environment and its two actual callee coordinates as literal data.
The final existence theorem obtains that reference from the previously proved
universal formation and meaning interpreter before selecting any old source,
candidate, or future argument. Both its reference and checker environments use
the existing optional finite-word use coordinates of the native compiler.
Candidate material cannot choose a different reference or supply a truth
predicate.

Eleven ordinary premises suffice. They admit the old package, require each
selected entry to belong to the actual candidate package, admit each complete
forwarding definition, compare two internal source presentations with the
complete public source in both directions, and retain the reference and
candidate environments in a common formed extension. The selected entries'
complete singleton clauses and empty material relations are checked by the
existing definition admission. No execution of candidate clauses establishes
their correctness.

The common extension is necessary because a candidate's canonical scope can
omit the reference program's root selector while retaining the definitions it
uses. Requiring the entire reference environment to be part of that canonical
candidate would impose irrelevant selector material. Instead, a private finite
extension contains both complete environments and preserves their native
packages. Formation prevents conflicting artifacts or bindings, and shared
definition agreement transfers the reference semantics to the candidate.
The reference remains fixed even though this finite extension is a witness.

The two forwarding entries may retain different complete presentations of the
old source environment. Requiring literal equality with the submitted source
value would make admission depend on collection enumeration. Two existing
inclusion calls in each direction establish equality of the complete recovered
environments. They permit all presentation choices without admitting a smaller
source domain. The old package's actual use and root are shared by both roles.

The construction installs two fresh native definitions over the fixed reference
program, selects all resulting definitions, and takes the canonical closed
restriction. It supplies an admitted candidate for every native source package,
including programs whose active use coordinates conflict with the reference:
the old source is literal data. The resulting program contains exactly the
reference definitions and those two entries. Existing artifacts and outgoing
bindings survive each installation. Both historical call boundaries and both
truth equations hold over all terms; distinct reference entries force distinct
candidate entries.

The ordinary admission equation is exact for this sufficient structural class,
including all complete source, candidate, and reference presentations. Earlier
checker entries keep their meanings. A native compilation fixed before all
future submitted terms supplies actual calls with its original minimal program
scope and every old artifact and binding preserved. This does not require a
decision procedure for arbitrary program equivalence. Complete transition
admission, further reflection strata, genesis, presentation exactness and
composition, and the final repository audits remain open.

## Native admission of minimal package scopes

The existing program-scope value stores a complete environment and its actual
site. A native package can be readable inside a larger environment, so package
formation alone does not admit this recorded scope. The new retention entry
also requires the supplied environment to be exactly the package grammar's
canonical restriction. This is proved equivalent to the existing closure
condition rather than introduced as a second primitive notion.

Three ordinary source clauses account for the root use, reached definition
uses, and actual binding targets. Two slot clauses inspect the root citation
family and every reached definition. They reuse the existing complete readers
and slot-observation results. The partial helpers retain their precise
boundaries: one readable citation does not establish a whole package. Two
instances of the existing generic context-list profile check every stored key,
and the final ordinary clause separately admits the actual package.

The key lists are projected from the complete supplied environment. They are
private witnesses bound by those projections; a chosen subset cannot replace
either list. Actual package formation supplies every required read, and the
two reverse inclusions exclude surplus environment rows. Together they entail
exact equality with the minimal environment. Needed whole artifact values
remain intact, including material outside the read syntax. A binding at a
needed artifact use must still have its own grammatical demand. This preserves
the distinction between retaining an exact value and reading syntax through it.

The context expands to the existing site value, with no additional stored
package value or root marker. An empty root family still requires its actual
artifact and admits exactly one retained use with no bindings. Every formed
package supplies an admitted canonical restriction, including empty packages
and packages with positive dependency cycles. No application, proof graph,
or positive truth premise is imposed on package retention.

The generic program extends the earlier forwarding program at fresh local
coordinates 118 through 122. The separately configured interpreter entry 117
remains in its existing program; package retention needs no fixed-reference
configuration. These numbers locate definitions within each finite source
program and do not acquire global semantic force. All earlier entries of the
extended generic program retain their meanings. Five distinct native entries
are fixed before all future submitted terms, with the original minimal program
scope and every old artifact and outgoing binding preserved.

For a complete data quotation already established independently, the admitted
body is exactly a program-scope quotation. That implication supplies the
package side of the following whole-artifact reading and composition result.
Higher generation and authority readers, complete transition material,
remaining reflection strata, genesis, and the final repository audits remain
to be completed.

## Complete quotation and its stored program scope

The next class uses the existing payload-and-pair quotation profile and its
complete artifact data. Native reading with an empty external-slot boundary
already forces a self-contained term. An additional self-containment premise
would check a fact derived from that boundary, so the ordinary complete-data
entry omits it.

The reverse quotation theorem reconstructs an injective syntax copy on the
actual read interior. It joins the exact pair header with two disjoint child
readings. It permits incoming structure at the boundary of a subterm. When the
interior is the entire artifact carrier, agreement on every headed incidence
and the full data basis entails exact object equality. This proves equivalence
between the existing complete-copy condition and the ordinary whole-carrier
reader, without changing either relation to assume that equivalence.

The ordinary entry derives a one-artifact environment from the complete
supplied artifact value and uses its actual carrier list as the quotation
interior. The existing reader admits that environment and its source data.
The local None use is a coordinate inside this derived environment; it is
not an external authority, caller binding, or global semantic discriminator.
Every complete artifact presentation is accepted. The exact original
addresses, every incidence, and both data components are retained.

The linked scope entry instantiates the general constrained-reading schema.
The first premise reads the whole quotation and returns its actual body; the
second admits that same body as a closed native package scope. A chosen
alternative body representing the same environment cannot replace the stored
body. The root is a private witness because the complete artifact determines
it within this class. The general determined-component construction uses the
independently proved link from environment and program site to the native
program, so no additional program value is stored.

Existential body admission is exactly the existing program-scope quotation
relation. More specifically, the recovered scope preserves and reflects call
formation and positive meaning for every actual future application in any
formed extension retaining it. This proves the intrinsic connection between
artifact data, quotation, environment, package retention, semantic definition,
and application. Exactness of those separate values alone was not used as a
substitute for this composition result.

Fresh local entries 123 and 124 extend the generic package-retention program.
Their clauses use the existing quotation and retention entries; they add no
material primitive or semantic dispatch by a metalevel notion kind. One fixed
native compilation precedes all future formed operands. Every old meaning, the
fixed minimal program scope, and all prior artifact values and bindings are
preserved.

This is an exact admitted presentation class and an explicit linked
composition, not a claim that only this topology is adequate. The owner's
correction also revises D-6, the generation-presentation obligation, the
presentation obligations, the work order, and the delivery gate. Remaining
work must audit the admissible class and intrinsic relations of every
presented notion, then complete higher generation and authority reading,
transition material, reflection, genesis, and the requested final audits.

## Initial general presentation scope and its limits

The owner requires a general presentation theory, used for its own relevant
notions and throughout the system, and expressly leaves its scope to evidence.
The initial scope addressed coverage, admissibility, complete occurrences,
constraints, intermediate presentation recovery, intrinsic relations, and
recursive meaning. The later clarification requires notions to be independent
of uses and guarantees to remain local to them. The assessment below records
why this initial layer was useful but insufficient and derives the added
correspondence and local-contract layer from that clarified direction.

| Evidence in the system | Selected general construction |
|---|---|
| Artifact and environment readers admit complete enumerations, and quotation admits addressed copies | Class coverage and recovery, compatible alternatives, and composition through complete intermediate presentations. |
| Records retain distinct fields; lists and premise families retain occurrences; finite collections admit every enumeration | Product and sequence construction, followed by the explicit distinctness and exact-membership conditions of finite collections. |
| Package, graph, binding, and table readers join facts about a common source | Constraints and joint classes with soundness for every retained presentation and compatible witnesses for every required subject. |
| A complete environment and site determine the actual native program | A functional-link construction that recovers the determined component without storing it again. |
| Identity, interpretation, and other intrinsic relations must survive presentation changes | Presented predicates and relations, with exactness supplied by independent native contracts, and explicit shared arguments and intermediate domains. |
| Ordinary definitions, list readers, and program relocation have positive recursion | Exact transport of the actual consequence operators on a proved closed support domain, followed by least-fixed-point transport. |
| The presentation theory uses actual reader definitions and program scopes | Native compilation of the ordinary composition schema and application of the same class constructors to the reader's own scope. |

The proof locale called presentation_class records subject coverage,
presentation admissibility, and unique recovery of the entire declared
subject. Coverage and recovery alone do not certify a complete physical
account or intrinsic relation. Those facts belong to the independent notion
or intrinsically linked group and its locally established reader contracts.
The typed
parameters introduce no primitive kind of notion and no generic native
predicate callback.

A constraint can have no valid subjects. The general class theorem permits
that empty domain and proves that admissible presentations exist exactly
when subjects exist. Totality therefore prevents an empty class from
representing a required subject. Inhabited application domains still need
constructed witnesses; an empty restriction cannot discharge their adequacy.
This clarifies O-79 without weakening its prohibition on vacuous evidence.

The relation constructions state preservation and reflection over all
representatives of the supplied classes. Their conjunction rule identifies
the recovered subjects at shared arguments. Relational composition additionally
requires a presented intermediate domain. Where physical compatibility narrows
a product, the joint class rule requires both soundness of the retained pairs
and a compatible witness for every required linked pair. A formal example
shows why separate total coverage cannot establish a shared witness.

Products and lists retain their roles and repeated occurrences. A finite
collection separately requires distinct subjects and exact set membership;
its order is a presentation witness. These different subjects are not
identified by using the same data-list constructor. The native list and
context-list profiles instantiate the generic sequence class, including the
same context in every call and its formation in the empty case.

Program relocation now uses the general fixed-point rule. Its previously
proved consequence equation and actual definition boundary discharge the
hypotheses; its public formation and meaning contracts remain unchanged.
The theorem does not infer recursive correctness from separately asserted
component meanings.

The program-scope class is derived through the general functional-link and
quotation constructions. Environment and site retain their own complete
presentation; the native package relation determines the program. Complete
quotation then preserves the exact intermediate body. The native scope
reader is an instance of the generic ordinary constrained-reading schema,
whose two premises inspect that identical body.

The fixed native reader's own scope uses these same class constructions.
Every compatible complete presentation of that scope is admitted by an
actual call to its own compiled reading entry. The original program is fixed
before these operands, and all of its artifacts, bindings, and minimal
environment remain intact. This establishes a concrete self-application
result for the operative theory. It does not establish native presentation
and checking of all presentation contracts and exactness proofs. O-85 keeps
those requirements explicit.

Further generic results must have an independently stated subject and a
reasoned structural or semantic scope. Applications supply evidence of useful
constructions; they do not define the notions or enlarge their semantic
boundaries. Arbitrary joins, quotient identifications, or
universal predicates acquire no force from this framework. The remaining
system-wide presentation work uses these constructions where applicable and
records the reason for any required special case. O-84 tracks that work and
any justified extension of scope; no claim of an exhaustive presentation
calculus or a completed self-contained foundation is made by this batch.

## Complete observations support native reference contracts

The presentation theory's own rules need complete data and native checks.
Existing pattern and schema determination provides concrete evidence for
one further general construction: a complete family of observations can
present its subject when the observation map is proved injective on the
required domain. Presentation_Classes derives this rule through ordinary
class composition. It does not introduce a universal observation primitive.

Factor_Schema_Observations applies the rule to the existing grammar theorem.
Its independent domain requires a formed complete schema and formed binder,
socket, and callee-root coordinates. One complete binder and two full
outputs determine the schema. Each output retains the conclusion, every
prospective occurrence and actual callee, and every five-operand material
tuple. Material truth is a separate judgment. Empty families and schemas
with unsatisfied premises remain eligible.

The report class uses the existing product and collection constructions.
Every collection admits every complete enumeration, independently in each
output part. The native binder traversal obtains both private substitution
tables from the public binder enumeration; the tables are witnesses, not
additional stored fields of the reported schema. Distinctness and complete
variable use are checked by the existing actual-schema instantiation rule.

Factor_Schema_Reading supplies the native intrinsic link between one
complete source site and that reference report. Its three ordinary premises
construct the two tables and check both outputs against the same actual
schema. Generic pair and constraint rules derive the compatible source/report
classes, with coverage for every required linked subject. Accepted reports
identify complete syntax. This supports universal
instance and rule consequences proved for that syntax, without inferring
program behavior from finitely many executions.

Schema identity alone does not establish a definition's complete behavior.
Factor_Single_Clause_Reading therefore checks the entire variable interface
and singleton clause family, then uses the general report reader. This
sufficient profile covers the composition rule and accepts arbitrary ordinary
and material schemas. The complete source site retains its private interface
binder and clause socket, so those coordinates need not be repeated in the
schema report. Extra clauses, changed interfaces, and a changed expected
schema are rejected.

A fixed reference report can be stored as literal pattern data in a fresh
ordinary view. The existing native compiler turns that view into checking
code before every future submitted source. Its all-term contract is exactly
the complete-definition relation for the fixed schema. The expected report
does not authorize an arbitrary mathematical assertion: only an independently
proved rule theorem supplies a semantic consequence of its admission.

Factor_Constrained_Contracts applies these results to the earlier reading
composition. Three variable roles remain independent and both premise
occurrences remain distinct even when their callees coincide. Native
admission already entails socket separation; the meaning theorem does not
add it as a redundant hypothesis. In a formed containing package, both actual
callees are present and the definition has exactly their two linked calls
on the same returned body. This holds for all terms in the independently
defined least positive meaning, including positive dependency cycles.
Construction over supplied callee anchors gives an actual definition and
admitted reports, with injective changes of private coordinates and a rule
equation for every future supporting relation.

The native schema reader is also fixed before reports of its own clauses.
Its compiled program is nonempty, every actual clause has source and report
presentations, and every compatible pair has a true call to that same
reader. Future operands preserve the original scope, all artifact values,
and every old outgoing binding. The stronger general compilation theorem
retains the structural variant and all-future application witnesses together;
the previous compilation contract is preserved as a consequence.

Complete singleton families recur in both native definition construction and
the earlier forwarding proof. A generic schema-family recovery lemma now
serves both. The forwarding theorem's statement is unchanged; its former
case-specific family argument is removed.

These results advance O-84 and O-85 through reusable observation classes,
native reference data, complete definition checks, a proved composition
contract, and operative self-application. Native presentations and checks
for further mathematical contracts and proof records remain open, along
with the higher protocol, reflection, genesis, and the final repository
audit. No single grammar or privileged presentation topology is reinstated.

## Proof presentations retain their actual program and assertion boundary

The complete record of a notion can also present a component derived from
that record. Finite collections already required this: a complete distinct
sequence presents its membership set while retaining its enumeration as
presentation structure. Complete artifact/body records have the same need:
the entire source artifact and its actual quotation present the returned
body. These two existing uses justify the general covered-image rule.
It requires an independently stated target domain and coverage of every
required target. The source record remains exactly recoverable; the image
operation introduces no identification of that record with its subject.

The finite-collection class now follows from the sequence class, a subdomain
restriction, and this image rule. Its previous contract is preserved.
The quoted-body class follows from complete artifact data paired with a term,
the complete quotation relation, and projection to that term. Every formed
self-contained term has a witness. The program-scope reader now also has
the corresponding class over its actual artifact/body argument.

The existing source-reader argument, standalone site value, judgment value,
and replay value retain different pair arrangements. Generic products and
an injective coordinate change derive their classes from the same complete
environment presentation. Subdomains require all selected sites to belong to
that represented environment. The coordinate change imposes no preferred
topology and does not alter any existing reader contract.

A native derivation record contains its source and program site, proof root,
complete root call, and complete collection of identified assertions.
Products and collection classes construct the record class; the independent
native derivation relation supplies its validity constraint. The actual
program, native graph, and complete claim assignment are uniquely determined
by that same record. Functional-link construction recovers those components
without storing another copy of them. Entry 102 admits exactly the resulting
class, and every valid native derivation has an admitted presentation.

A replay context additionally includes the actual application. The source
alone determines its assertion boundary through the native graph reading.
The source class therefore derives that boundary privately. A separate joint
class relates the context to a complete explicit assertion report through
entry 111. Its compatible domain is exactly the existing replay relation.
The richer reading class recovers the actual program, application, syntax
interior and slot boundary, graph, and complete claim assignment together.
The retention theorem proves equality with the actual replay restriction.

Closed replay is the subdomain with an empty assertion boundary. Two generic
ordinary schemas provide projection of a reader result and matching against
a fixed literal result. Their variables, premise socket, actual callee, and
whole rule equations are explicit. The previous reference-contract schema
is a fixed-result instance and keeps its old statement. Complete-definition
admission transfers the two generic meanings, and native construction
preserves every prior artifact and outgoing binding. A generic compilation
lemma recovers admitted reports for actual compiled singleton definitions.

The four replay entries instantiate those two rules and the existing
constrained-reading rule. They check conditional replay sources, closed
sources, and compatible complete quotations of each. Every native replay
has total quotation witnesses. Each source artifact must quote the body
actually supplied to its constraint; changing a body presentation requires
a compatible artifact. All compatible artifact and body presentations are
covered by the same relation equations.

One closed native compilation is fixed before future operands. Its four
actual definitions have complete reference reports checked by the existing
definition reader. Its positive-call domain is inhabited by complete
quotation of the empty payload. Every positive call of the actual compiled
program has a native closed replay preserving that program and the minimal
judgment scope. Proof construction first preserves all existing material;
replay restriction retains the original program. The proof checks all
outgoing bindings at every original program use, since equality of the
canonical package environment alone would not exclude additional bindings
at those uses.

Every compatible complete quotation of each such proof has a positive
application of the original compilation's closed-replay entry. The original
program artifacts and bindings are preserved in that checking application
as well. This checking call is itself among the positive calls covered by
the theorem, with no new program chosen after the proof operand.

Assertions retain their conditional status. A formed false equality call
has an assertion graph, a native conditional replay, and a complete quotation
admitted by the conditional reader. Both closed entries reject that same
context. Presentation, native realization, and retention do not prove the
asserted call.

These results present native proofs of operative reader judgments under the
same general theory used for the rest of this batch. O-85 still requires
native presentations and checks of the remaining mathematical contracts and
exactness proofs with their intrinsic relations. The higher protocol,
reflection, genesis, and final repository audit also remain open.

## Recursive classes retain their actual generation links

The existing generation value is recursive, while its predecessor collection
is a finite set. A separate uniqueness and construction argument for each
recursive profile would repeat the same class reasoning. The new family rule
therefore covers a union of independently stated domains, with agreement on
every shared presentation. Directed inclusion supplies that agreement through
a common class. The earlier two-alternative theorem now follows from this
general rule.

Generation classes are built at finite size bounds using target products,
complete finite-set classes, and injective field observations. The existing
predecessor-size theorem supplies the smaller child bounds. Taking the
directed union covers every formed finite core and every old value
presentation. The size bound is a proof index, not stored information or a
restriction to a fixed finite domain. No representative is selected from the
admitted class.

Finite sets are obtained from the existing complete collection class through
the covered image rule. Its independent domain contains all finite sets of
allowed elements. Every complete order and every permitted member
presentation remains available. Snapshot, publication, and transaction classes
then reuse products, subdomains, and observations. Their original formation
conditions remain intact, including one generation per selected locus, the
two absence boundaries, their disjointness from the respective selections,
and the restriction of changed loci to compared loci. The earlier totality
and recovery statements are retained as consequences of these classes.

A transaction's four fields do not determine an outcome without the supplied
initial snapshot. Their joint context does. The determined-component
construction presents the entire execution result from that context, without
adding an outcome field to the transaction. A successful result retains the
exact update and lookup at every locus. A conflict retains the complete
comparison domain and every observed value, with no output snapshot.

A generation source presentation retains the actual environment and selected
site. The existing native reading uniquely supplies the core. Its covered
image presents every formed core while leaving the complete source context
recoverable from the presentation. A separate report class relates that
source to an independently presented expected core; equality of unrelated
displayed values is not substituted for the actual source reading.

Predecessor rows retain the socket, citation endpoint, actual destination use
and address, and exact child core. Their parent environment is retained by the
source context. Standalone row formation specifies the coordinate and core
domain. The joint report constraint additionally requires exactly the
collection read from the actual source. Its socket domain is complete, and
its rows are in bijection with the predecessor cores. A different site
presenting an equal core is not thereby an actual cited destination. Strict
core descent proves well-foundedness on the recursively read native sites;
the size assignment remains part of the proof.

The generation environment is precisely the existing citation-request
restriction at the selected root. Generation reading is preserved and
reflected for every proposed core under a formed environment. If the source
actually reads a generation, every recursive predecessor row and request is
preserved, and the restriction is closed and idempotent. It fixes an already
closed generation environment and is included in every retained
subenvironment that can still read the root. Its equations account for every
retained artifact and binding. General request-restriction lemmas supply
idempotence and equality under complete use and binding-key coverage.

The whole recorded cause determines its quoted judgment context. Its class
derives that context without duplicating it in the source value. The material
theorem follows the actual cause citation to its local or externally bound
artifact use and reads that artifact's complete body without slots. An
expected context report may use another allowed presentation of the recovered
context. The cause artifact still has to quote its own actual body; the
expected report is not silently treated as that body. The explicit relation
equation preserves this distinction across outer presentations of the same
core.

Every formed context, meaning a formed environment with both actual selected
sites, can be recorded with any formed locus, payload, and finite formed
predecessor collection. The construction supplies an already minimal outer
generation environment. Every recorded scope has complete report and
quotation witnesses. A concrete formed false native equality call also has
such a recorded scope and quotation, while its generation cause is invalid.
Scope recovery therefore establishes neither a true call nor a valid base
or construction role.

The existing ordinary target entry admits the derived target class. This
batch adds no ordinary clause for the remaining recursive generation or
higher protocol relations. Their class constraints refer to the independent
native readings whose links are proved here; those predicates are not new
native primitives. Ordinary admission still requires its own exact program.
The new mathematical class contracts also retain the native proof obligations
under O-85. The wider protocol, reflection, genesis, and final repository
audit remain open.

## Notions own their presentation and implementation contracts

The owner's further clarification is authoritative: define notions and their
intrinsic relations independently of requirements, present them exactly, and
then use or compose them. Locality, compositionality, separation,
specialization, and instantiation are the intended effects. An intrinsically
linked group may own a joint boundary. Requiring every use to reestablish
meaning transport would make that boundary grow with its clients.

The existing machinery was useful but insufficient. The class locale covers
the independently stated subject domain, admits exactly its presentations,
and uniquely recovers every complete subject. Products, collections, images,
constraints, and exact consequence transport already provide reusable proofs.
Presented predicates and relations admit every representative of a class.
However, the existing composition construction recovers the *entire
intermediate presentation*. That is appropriate for quotation. It does not
by itself express conversion between different presentations of the same
underlying subject. The relation-composition theorem also used one common
intermediate class. Text assigning further obligations to each application
left the intended semantic boundary too broad.

Coverage and recovery also leave an interface gap. A class can recover one
unit subject from both boolean presentations while an observation distinguishes
the booleans. Presentation_Contracts proves this counterexample and an exact
factorization criterion. An observation descends to the subject exactly when
it rejects inadmissible inputs and is constant on all presentations of each
subject. This is a diagnostic criterion. The intended predicate and subject
still require an independent definition; a client's desired observation
does not manufacture the notion that justifies it.

The chosen correspondence relates every pair of presentations recovering the
same independently fixed subject. The owner did not prescribe a function,
normal form, or selected representative. The relational choice preserves
every admitted presentation and derives totality in both directions from
each class's own coverage. Recovery proves coherence under identity, reversal,
and composition. It uniformly transports all independently stated predicates
and relations. Relational composition can therefore use different
intermediate classes without a new proof for each pairing. Product, sequence,
set, and least-fixed-point laws extend the same correspondence. Recursive
implementations still establish their actual consequence equations locally.

The subject type, domain, and reading relation remain explicit proof
parameters. No universal datatype or primitive classification of notions is
introduced. A single raw term can have different readings in different
contexts; those contexts are not erased into an ambiguous grammar union.
Specialization selects a subject subdomain and retains every presentation of
its members. Instantiation uses an independently stated map between domains.
Its local contract provides outputs for every admitted input, makes outputs
unique up to recovered subject, and composes with another map through the
same correspondence. A map may identify different source values when its
independent definition says so; it does not thereby identify their source
notion.

Each actual reader establishes its exact relation contract in the module
owning the notion or intrinsic group. Generic adaptation, specialization,
and composition then derive the contracts used by clients. The contract
requires its whole admitted domain, including invalid-input rejection.
This is the selected implementation interface. It avoids a separate semantic
transport obligation for each consumer while preserving explicit proof of
every newly supplied implementation.

Intrinsic links are defined in the complete joint subject domain. A product
presentation includes every pair of component presentations of linked
subjects. Any separately exact physical joint class then covers that whole
domain, so its local contract provides a result for every valid input pair.
This statement permits conversion to an appropriate joint presentation; it
does not assert that arbitrary supplied material can be literally glued.
More general intrinsic groups can be specified together without decomposing
them into a binary product. Material observations remain on the actual
source or occurrence notion whenever its intrinsic relations inspect them.

Artifact and environment identity instantiate the local reader contract.
The quotation example deliberately uses different presentation types. A
direct artifact value can correspond to a quotation storing another complete
value presentation of the same artifact. The source still determines its
exact stored body. A theorem retains both facts when the two bodies differ.
The earlier complete-intermediate quotation construction remains intact.
The new mathematical adapters supply no generic native predicate callback or
executable representative-selection operation.

Counted bags have an independent multiset domain. Their presentation class is
the covered image of complete sequences under the multiset map. This forgets
enumeration order while retaining every multiplicity. It covers all bags of
admitted members and every permitted member presentation. Complete data bags
instantiate this rule, and the existing list and equality readers supply
their native admission and identity contracts. This gives bag meaning before
the artifact comparison uses it. Finite sets instead use distinct subjects;
the same list constructor does not conflate the two notions.

The new positive bag-inequality program has three alternatives: an extra
occurrence after the first list is empty, a head absent from the entire other
list, or inequality after one equal occurrence is removed. Removal preserves
the difference in multiplicities, and every unequal pair has a finite witness.
The absence helper uses the existing complete context-list clauses. In its
empty case only the context's term formation is required; its exact raw
contract states that boundary. The bag checker separately admits the missing
head and every remaining data element. Mathematical complementation occurs
in the soundness and completeness proof, not as a negative native premise.

Artifact inequality admits both complete artifacts and witnesses a difference
in one of their four actual data fields. It exports the local artifact
inequality contract. Target comparison retains the whole independent artifact
and optional occurrence; the latter remains an actual member of that artifact.
A whole target differs from an occurrence at the empty address. The generic
separated-list profile consumes the target inequality contract and derives
complete finite-set admission. Every order and presentation is retained, and
different presentations of the same target cannot appear as distinct members.
The empty collection is admitted. These choices follow the already defined
bag, artifact, target, and finite-set subjects, rather than a later generation
reader's particular requirements.

The draft initially inherited the complete replay program in the bag module
solely to allocate later entry sites. That would unnecessarily enlarge the
low-level construction boundary. The corrected design gives bags their own
program over existing bag operations, composes artifact comparison locally,
and then composes target comparison under its existing admission. A separate
module integrates the resulting target collection program with replay.
Factor_System_Composition proves that formed programs with complete agreement
on shared definitions have a formed ordinary union preserving both programs'
call boundaries and meanings. Its proof uses the existing closed-dependency
locality theorem. Fresh-definition agreement and transitivity keep the
structural reuse proofs separate from the meaning proofs of the readers.
This additional construction is justified by actual reusable program notions
and applies wherever complete definitions are shared.

The seven native entry coordinates remain 132 through 138 so integration
with the accepted replay program is fresh. They are ordinary construction
coordinates, and existing injective relocation and native compilation remove
any significance from those particular numbers. Sixteen ordinary clauses
provide absence, counted and artifact inequality, target identity and
inequality, and the two complete collection traversals. The integrated
program preserves every earlier replay and local comparison meaning. Its
closed native compilation precedes all future formed operands, with distinct
entries and exact preservation of its original scope, artifacts, and bindings
across applications.

The scope of this addition is reasoned rather than claimed exhaustive. It
addresses the general semantic boundary, coherent composition, specialization,
instantiation, intrinsic joint domains, actual program sharing, and concrete
native comparison uses. The remaining audit must apply the local-contract
discipline to the other notions and reconsider inherited scopes wherever they
are broader than their independent dependencies. O-43, O-44, O-80, O-84, and
O-85 remain partial. In particular, mathematical correspondence does not prove
native implementation of arbitrary relations or present all mathematical
contracts and exactness proofs. Native generation source admission, higher
protocol and reflection work, genesis, and the final every-line audit remain.
The following value-program addition closes admission and comparison for the
independently defined recursive core class.

## Generation values own a positive admission and comparison group

The independent generation core already contains exactly a locus, a finite
set of exact predecessor cores, a payload target, and a recorded cause target.
Its formation relation predates this reader. The general presentation theory
already derives the complete recursive value class from those four fields.
This addition implements that existing notion and its identity and inequality
relations, then exports contracts for later clients. Cause validity, source
citation reading, retention, publication, and authority have separate subjects
and boundaries; value admission does not establish those judgments.

The existing representation uses nested pairs for the four roles and a
complete distinct-subject list for the finite predecessor set. The reader
keeps this class because its coverage, recovery, and material boundary are
already proved. It admits every order and every permitted member presentation.
No order is imposed on the predecessor subject. No new tag, duplicated field,
chosen representative, comparison key, or depth limit is introduced. Another
exact presentation of this same core can use the general correspondence and
local-contract laws without requiring each client to repeat this proof.

Admission and comparison are intrinsically linked at the implementation
boundary. A predecessor list must contain distinct cores, which requires core
inequality. Core inequality in turn admits both complete operands before
comparing their fields. Implementing the entries as independently closed
successive views would either miss this recursion or assume a result still
being constructed. The chosen program therefore contains one finite positive
group. Its least meaning is the existing monotone consequence construction;
unsupported cycles cannot supply their own support.

Factor_Recursive_Groups formalizes this construction independently of
generations. Relative formation changes only the allowed dependency domain:
every finite functional interface and clause family, owned head, formed
pattern, and complete schema remains required. An ordinary union with a
formed base closes a group with fresh definition coordinates. The old base
has no new callees, so all its call boundaries and meaning are preserved.
The unclosed group has no claimed separate native meaning. Its external
dependency set is derived from actual prospective callees, rather than
stored as another registry or trusted certificate.

The initial draft inherited the whole target-difference program. Its
accumulated environment and record definitions were not all needed by the
generation notion. Factor_System_Restriction now retains complete definitions
on an actual dependency-closed boundary, with formation, all-call agreement,
and leastness proved generically. The generation base is the least closure
of the group's actual external callees: data admission, data-list admission,
target admission, target identity, and target inequality. The chosen source
is the already formed target program; no malformed source is silently repaired.
Restriction constructs a new program. It does not equate that program's exact
identity or quoted scope with its source, or alter an already adopted scope.

The eight new entries use construction coordinates 139 through 146. The
particular numerals have no semantic role under existing injective relocation
and compilation. Admission has one clause for the four fields. Identity has
one clause requiring complete admission of both cores and identity of all
four fields. Inequality has four alternatives, each retaining complete
admission and witnessing a difference in one field. Two complete-list
traversals check separation and element admission. Selection, bag identity,
and bag inequality supply the remaining positive recursion. These families
contain seventeen ordinary clauses in total.

The bag-difference proof is factored through an independent finite witness
relation. Its three forms are an excess occurrence, a head unequal to every
member of the other list, or a remaining difference after one equal member
has been removed. Under equality and inequality equations on the compared
member presentations, these witnesses hold exactly for unequal multisets.
Multiplicity is retained. The mathematical inverse used in the proof recovers
the unique underlying subject; it does not select or normalize a presentation.

Factor_Related_Difference implements those witnesses through actual ordinary
comparison callees. Its raw all-term contract includes complete data lists,
one-occurrence removal, and the entire remaining boundary. In the missing-head
case an empty other list still requires the head's data admission and the
complete first tail. The shared empty context traversal itself requires only
context formation. The raw helper can therefore have a witness on data that
are not both complete collections of generation cores. Its exported raw
contract states this fact. Whole generation comparison separately admits both
complete cores before using the helper. No negative premise or failed-call
test is added to the positive language.

The proof first derives the exact equations of the actual clauses and shows
that every admitted generation has a complete self-contained data boundary.
It then proves admission, identity, and inequality together by finite term
height. Every presented predecessor is a strict subterm of its enclosing
value. At a bound, the previously established inequality equations admit
exactly distinct predecessor cores; their full set and the three target
fields recover the parent. The new admission equation and the smaller-core
comparisons then establish both comparisons at that bound. Invalid inputs
are included in the admission proof, so soundness does not presuppose a
recovered core. Every finite term lies below some bound.

This local proof uses the exported target comparison contracts and the generic
separation, finite-set, related-bag, and positive-witness results. The helper
definitions take several ordinary positive steps. A one-step consequence
correspondence between an abstract core operator and this expanded program
is therefore not claimed. The finite bounds and temporary presentation
constraints belong only to the proof. They neither limit operative inputs
nor introduce a stored rank. The exported generation contracts have no bound.

The completed generation relation contracts provide all-term exactness,
including rejection of malformed operands, and invariance across every
presentation of the same cores. The generic separated-collection theorem
then consumes the generation notion's own inequality contract and derives
the complete finite-set admission class. Two presentations of the same core
cannot form two distinct predecessors. The empty collection is admitted.
Totality covers every formed core and every finite set of formed cores;
generic base and singleton-successor constructions witness both predecessor
cases without validating the recorded cause.

Factor_Compiled_Applications exports a reusable consequence of its existing
compiler: selected operations with already proved all-term contracts obtain
one fixed native program before future operands. The expected relation is a
proof contract for an actual formed program, not a method of compiling an
arbitrary mathematical predicate. The generation instance fixes eight
distinct sites, preserves its complete original scope, and retains every
artifact and outgoing binding when later operands are constructed.

Factor_Generation_Value_Programs is a separate integration with the existing
comparison and replay program. Complete agreement is proved on their shared
target base before ordinary union is formed. Both programs' calls and meanings
are preserved. The fixed combined compilation offers all fifteen target
comparison and generation operations for future operands. The earlier
Factor_Generation_Programs theory, which preserves quoted program scopes in
generation payloads, is a different relation and remains unchanged.

The choices of a positive group, reuse of the existing value class, least
complete-definition base, finite-subterm proof, and separate reader integration
are justified above. They do not settle every possible implementation of the
notion. Native admission of actual generation sources, cited predecessor rows,
retained environments and recorded scopes, and higher protocol relations
remains. The mathematical contracts and exactness proofs still need native
presentations and checking under O-85. The wider obligation states remain
partial, and the final every-line audit has not begun.

## Actual generation sources own their recursive reading contracts

The generation source notion predates this program. It contains the actual
environment and selected site; the existing recursive reading determines its
core. A core report pairs that source with any value presentation of the core
actually read there. A predecessor report contains every native socket,
citation endpoint, actual destination use and address, and child core. These
existing domains and relations determine the implementation boundary.

The selected program has nine definitions at construction coordinates 147
through 155 and eleven ordinary clauses. The coordinates are incidental under
existing injective relocation. The syntax entry calls the complete four-field
record and family readers. The field entry looks up the source artifact and
reads the locus, payload, and recorded cause in the same environment. A child
row calls actual citation location and the recursive core report, copying its
socket and citation endpoint into the result. Its value projection shares
that same row reading. Core reports admit the complete expected value and
match every produced child occurrence to the expected predecessor collection.
Source admission projects a core report. Complete predecessor reports admit
the parent source and traverse its complete family.

Sequence correspondence is an independent recurring relation. The chosen
Factor_Related_Lists profile has two ordinary clauses and one actual callee;
it keeps the same context in every corresponding pair. Its raw all-term
contract includes both complete list boundaries. Empty lists require only
context formation. No environment or element admission is inferred from that
case. The source and report entries provide their own actual context and
parent checks. A local member-reading theorem transports arbitrary independent
sequence relations after the callee's own meaning equation is established.

The bag proof previously exposed only distinct collections, while the source
reader first produces a sequence whose multiplicity must be established.
Bag_Readings now owns unique member recovery and exact multiset transport.
Factor_Related_Bags exposes the sequence theorem and derives its existing
collection theorem from it. Bag_Difference_Witnesses reuses the same recovery
lemma. Both earlier public theorem statements and all earlier native clauses
are preserved; only the two duplicated recovery proofs are refactored.

RRA_Generation_Lists gives a presentation-independent equation for the original
generation relation. Complete socket enumerations and distinct child sequences
recover its injective socket assignment, and every original reading supplies
such a sequence for every complete enumeration. It changes no generation
field, formation condition, citation meaning, or primitive reading rule.

The program base first joins the existing citation and generation-value
programs only after complete shared-definition agreement. The source group
then retains the least actual dependency closure of eight external callees:
payload recognition, family and record admission, artifact lookup, anchored
target and occurrence location, generation-value admission, and generation
bag identity. Every retained definition keeps its complete interface and
clause family. This constructs a new program and preserves both old meanings;
it does not identify the smaller program with its source or change an adopted
scope. The native clause module depends on these local components. The proof
of the existing source class reuses the pure context data in
Factor_Replay_Values; no replay judgment or higher protocol enters the source
program's meaning boundary.

The recursive proof is joint over the finite expected core. Its already
proved value contract first recovers the complete core. The generic bag
contract establishes all child multiplicities and membership in its expected
predecessor set. Every child is therefore strictly smaller, so the local
induction hypothesis applies at the actual cited site. Generic sequence
transport and the independent socket-enumeration equation recover the native
parent reading. Completeness accepts arbitrary source and value presentations
with independently ordered predecessor lists. The bound is a proof measure;
no rank, limit, chosen representative, negative premise, or external truth
callback is stored in the program. Several helper calls take several positive
steps, so a one-step abstract consequence correspondence is not claimed.

The complete native predecessor relation is in bijection with its socket
projection. A report can therefore use any order: projecting its rows gives a
complete family enumeration in that same order. Each row retains the cited
use and address even when another site presents an equal core. Whole parent
admission enforces distinct predecessor cores. The exported contracts reject
missing, unrelated, and repeated rows, including repeated presentations of the
same row. Empty reports retain the parent and empty-family checks.

The source-to-value operation is proved equal to the general canonical
semantic correspondence between two complete classes of the same core. It
inherits the generic total function contract. The complete predecessor report
also exports a total function contract on actual source subjects. These are
locally owned implementation results; later clients use their adaptation,
instantiation, and composition laws without repeating this recursive proof.
Every formed finite core has an actual admitted source, a core report, and a
complete predecessor report. Base and nonempty predecessor witnesses follow
from that full-domain construction.

Source admission also admits the existing determined retention class: the
source determines the least required environment without another stored
field. Replacing an environment by that restriction preserves native source
admission, every expected-core reading, and every complete-row test. Any
included environment that still passes source admission contains that least
restriction. The earlier closure, idempotence, exact artifact and binding,
and recursive-row and request equations remain the account of its content.
This batch adds no checker for a separately submitted claimed retained
environment or recorded-cause context; those report relations need their own
ordinary clauses. Recording a cause still does not validate it.

One fixed closed native compilation supplies all nine operation sites before
arbitrary future formed operands. Its original complete scope, artifacts, and
outgoing bindings survive those applications. Integration with the broader
reader program can use complete-definition agreement when the later scope
and protocol readers are joined; no broader proof import selects this local
program's operative dependency boundary.

The choices of shared-context sequence clauses, the least complete-definition
base, joint finite-core induction, and reuse of the existing source and report
classes are justified above. Separately submitted retention claims, recorded
scopes, cause validity, higher protocol, reflection, and genesis remain. The
new mathematical contracts and proofs retain the native presentation and
checking obligation under O-85. The wider obligation states remain partial,
and the final every-line audit has not begun.

## Independent context and scope contracts compose through actual quoted bodies

A formed site context consists of a complete environment and one actual
position in it. A formed judgment context contains two such positions in the
same environment. Those notions precede program grammar, application
formation, role, truth, and cause validity. The existing closed program-scope
notion adds a native package and the least environment required to read it.
Its program is already determined by the selected site. The implementation
keeps these independent domains and their existing intrinsic relations.

The four context clauses use actual artifact lookup and occurrence-target
admission, then share one environment between judgment sites. Identity keeps
the coordinate fields and compares complete environments. Equal environments
and unchanged coordinates imply the second context's admission, so a second
admission premise would repeat an established condition. Their least base is
the complete-definition closure of the three actual external callees.

A complete quoted artifact determines its actual data body. The existing
artifact class, determined-component construction, and covered image rule
give this body class without storing the body or its root twice. Every formed
self-contained body has a complete quotation. Composing this class with an
independent context class presents the context through the exact stored body.
This construction is justified by complete quotation itself; it does not
select an exclusive topology for other presentations of the context.

Factor_Transported_Readings supplies one ordinary schema with two actual
premises. The first returns its actual body with a private witness; the second
compares that same body with the expected report. Its complete-family meaning
holds for every input term. Canonical comparison then gives a generic total
function contract from the composed source class to the expected class. Both
judgment and program scope readers consume this one contract. Expected
presentations may vary while the artifact continues to quote its own body.

The existing reader-projection schema is reused for source-only admission.
A complete-family locale now contains its local equation, including grouped
programs and positive cycles. The earlier fresh-view theorem consumes this
locale and retains its original statement and assumptions. All other earlier
statements, native clauses, assumption scopes, and proofs remain unchanged.

The judgment reader retains the least closure of complete quotation and
judgment-context identity. Its formal complete-definition boundary excludes
package admission, application admission, replay admission, positive judgment,
and package retention. The program reader separately uses the existing
closed-package scope class. One scope-identity clause admits the source and
compares its site context; the same complete context determines the second
scope and its program. No duplicate program value or admission is stored.

The existing complete quotation code is shared through complete-definition
agreement. Its legacy proof import chain is broader than the judgment
reader's operative closure. That closure, its preserved complete clauses,
and the exact independent class establish the semantic boundary. Cloning the
quotation code merely to shorten imports would duplicate an implementation.
The broader file-organization audit remains part of the system-wide review.

The actual generation source links to two independent notions: the judgment
context quoted by its whole cause and the closed program scope quoted by its
whole payload. The recorded-scope relation and classes are preserved. The
payload relation composes the already specified actual generation and carried
program relations. Determined components give source classes without another
stored context; linked products give every compatible complete report.

The four generation clauses first consume the complete actual source-to-core
conversion. A report then selects the whole cause or payload field and calls
its local scope reader. The two source admissions project those reports.
Their least base is determined by three actual external callees: complete
generation reporting, judgment artifact reporting, and program artifact
reporting. All private fields occur in actual positive calls. No external
truth callback, failed-call premise, operative bound, or new primitive is
introduced.

The generation owner derives the selected whole artifact from its already
proved value contract. The scope owner derives the subject through complete
quotation and canonical correspondence. Their linked native classes and
relation and function contracts own this result locally. Clients obtain every
compatible output, invariance, and rejection of a different recovered scope
from those contracts. The actual stored body is retained throughout.

Least generation source restriction preserves every scope report and both
source admissions. The material contracts retain the exact native citation,
its local or externally bound artifact use, the complete quote, and the empty
slot boundary. Every formed judgment context can be recorded with any formed
payload and predecessor set. Every closed program scope can be carried with
any formed cause and predecessor set. Independently chosen subjects of the
two classes can coexist in one actual generation whose source environment
is already least. Neither role requires the other.

A formed false native call has an admitted recorded scope and report while
its cause is invalid. Every actual program also has an admitted payload scope
in a generation with an invalid cause. These witnesses preserve the separation
between scope recovery and validity, construction permission, authority,
adoption, or amendment acceptance.

The thirteen native definitions have thirteen ordinary clauses at incidental
construction coordinates 156 through 168. Four serve contexts, five serve
scope identity and quotation reports, and four serve generation scopes.
Three fixed closed native programs supply these entries before any future
formed operand, preserving each entire original scope, artifact, and binding.
Complete-definition agreement preserves all component meanings; it does not
identify the smaller programs with their sources or change an adopted scope.

The choices of one shared transported-reader contract, determined artifact
body class, least dependency bases, and separate context domains are justified
above. Separately submitted claimed retained environments, cause validity,
higher protocol admission, reflection, genesis, and the system-wide audit
remain. Native mathematical-contract and exactness-proof presentations remain
under O-85. All broader obligation states stay partial, and the final
every-line audit has not begun.

## Claimed generation retention follows the actual dependency relation

A complete generation source already determines its least required
environment. A submitted retention report presents that same environment
alongside the source. The source class and its determined-retention class
remain unchanged. A product constrained by this existing intrinsic relation
gives the report class; a subdomain gives closed sources. Complete quotation
composes with both classes, and every formed core has a closed witness.

Closed reading in a claimed environment and inclusion in the original source
are sufficient to recover the source reading and equality with its least
environment. The proof uses the existing leastness and fixed-environment
theorems in both directions. The native report therefore has those two
premises. A second admission of the original source would repeat a result
already entailed by the actual claim.

The dependency program exposes independently specified notions in five
entries. Recursive read sites start from actual source admission and follow
complete predecessor reports. Selection preserves each socket, citation
endpoint, destination use and address, and child core. The positive proof
gives only reachable sites; path induction gives every reachable site.
Neither a stored path nor a depth bound is part of the operation.

Citation-root recognition uses the complete record and predecessor-family
layout. It is available independently of successful generation reading or
citation interpretation. Recursive requests then combine actual read sites
with those roots. Demanded slots come from the complete actual citation
reader. Required uses are read sources or targets of demanded slots, giving
that query its own exact meaning before closure is checked. A stored binding
outside the request set cannot justify its own target.

Two existing generic list profiles traverse the keys projected from both
complete environment tables. Their empty case checks context formation;
closed-source admission supplies the complete generation role. No selected
sublist is supplied by a certificate. Coverage is equivalent to the existing
closed environment and to its being fixed by the least restriction. Keeping
a whole locus, payload, or cause artifact does not continue generation reading
inside it. Actual predecessor citations alone continue that reading.

Each dependency relation owns its presentation contract over the complete
source class. A generic known-source relation law exposes every compatible
output. It applies to partial relations without asserting an output when the
relation has none. The existing function-output proof and all four dependency
contracts consume the law. Its source domain and target relation remain
independently specified; this is not a universal datatype of notions.

Complete environment inclusion now owns its local relation contract. Its
earlier program construction follows replay admission, but its actual clause
dependencies are within ordinary data, lookup, and the two inclusion
definitions. That closed boundary is proved from complete clause families.
Shared-definition agreement joins inclusion with generation source reading,
preserving both complete meanings before the least base is selected.

Nine actual external callees determine that base. The final program has nine
new ordinary definitions and fourteen clauses at incidental construction
coordinates 169 through 177. Its formal dependency boundary excludes replay,
positive-judgment, and scope checkers. The proof import chain includes earlier
results that justify these boundaries and the preservation corollaries; it
does not enlarge the retained program. The wider file-organization audit is
still required.

The native closed-source and report equations cover every input term and
every permitted environment presentation. A total function contract exposes
the least-environment result. Different table orders and complete artifact
presentations remain available. Missing or extra uses and binding slots are
rejected, and exact environment identity also rejects changed stored values
and bindings at unchanged keys. Exact uses and distinct binding aliases remain
part of the retained material.

The report recovers a closed source using its supplied environment
presentation. All recursive dependency queries and existing source,
predecessor, recorded-scope, and payload-scope reports are preserved by
restriction. Retention reports themselves are preserved by idempotence.
Closed-source admission intentionally tests whether the supplied environment
is already least; restriction can change that result from false to true.

Every formed core has admitted closed material and a complete report quotation.
An existing actual invalid-cause witness also has an accepted closed source
and retention report. Retention therefore remains separate from cause
validity, construction permission, authority, adoption, and amendment.
One fixed native program supplies all nine entries before future operands,
preserving the entire original scope, every artifact, and every binding.

The choices to expose the exact dependency sets, use complete table coverage,
derive original-source admission from the claim, and export local relation
and function contracts are justified above. The only changed earlier proof is
the generic function-output proof, whose statement is preserved and now uses
the more general known-source law. All other earlier definitions, statements,
assumption scopes, and proofs are preserved. The earlier source-contract
explanation now points to the implemented scope and retention readers.

Cause validity, authority, higher protocol admission, reflection, genesis, and
the system-wide presentation audit remain. Native mathematical-contract and
exactness-proof presentations remain under O-85. Broader obligation states
are unchanged, and the final every-line audit has not begun.


## Judgment retention owns the exact program and call boundary

The independent notion already exists in Factor_Judgment_Retention: the
complete environment read by one native package and one actual application.
It determines a least source-and-slot restriction independently of any
derivation, replay graph, truth, cause role, or authority. The new native
contract implements this existing notion before recorded cause validation
uses it.

The subject remains the existing judgment context: one complete environment
and its actual program and call sites. Package and raw application reading
constrain that context. Neither callee membership in the package nor
interface acceptance is a condition of raw reading. Positive truth remains
separate as well. The recovered program, callee, operand, interior, and slot
metadata are determined by this source; adding them to its stored value
would duplicate that basis. Generic subdomain, product, and complete
quotation constructions derive source, closed-source, and report classes.
This reuses an established presentation without claiming that its pair
arrangement is intrinsically privileged.

Seven native definitions have thirteen ordinary clauses. Source admission
checks the actual package and application in the same complete environment.
The slot query is the union of both grammars' actual demands. The use query
covers the two roots, every reached definition source, and the actual targets
of those demanded bindings. No stored dependency certificate or guessed
traversal bound is introduced.

The older package source query includes targets of every stored binding.
Its conjunction with the complete binding coverage test is exact for its
existing closed-package judgment. That does not make the broader query an
exact required-use relation on arbitrary readable sources. The new use
query therefore requires an actual demanded slot before following its
binding. An unused binding cannot justify its own target. The earlier query
and its accepted statements remain unchanged.

Two generic list profiles check every key of both complete environment
tables. Their empty case keeps its ordinary formed-context domain.
Closed-source admission separately requires readability and both table
coverage checks. A general fixed-point coverage theorem belongs in
RRA_Read_Environment because it concerns the independently defined
source-and-slot restriction. Its statement holds without a higher grammar
assumption and is used at the judgment boundary.

A retained-environment report checks closed readability at the same two
sites in its claimed environment and checks complete inclusion in the
source. The existing extension theorem then recovers source readability and
equality with its least environment. Requiring a second native check of that
same source would duplicate a derived fact. The report still compares both
complete environments; matching only domains would fail to preserve stored
values and binding targets.

Local relation contracts own exact slot and use queries. A total function
contract owns the least-environment result and exposes every compatible
output presentation. General transport, invariance, and composition are
therefore available without representation-specific proofs at later uses.
Wrong environments, changed use or binding domains, and nonminimal supplied
scopes are rejected.

Accepted reports retain each exact artifact value and every demanded binding
at its actual use and slot. They preserve both complete readings, all
application metadata, call formation, truth, and the independently determined
program scope. Every slot, use, and list query is invariant under least
restriction. Retention reports are idempotent; closed-source admission can
change from false to true when an oversized environment is restricted.

Every readable source has native closed material and complete source and
report quotations. An existing formed false equality call supplies a
non-vacuity witness: its retained scope is admitted, its report is accepted,
and native positive admission still rejects the call. Retention supplies no
truth or cause-validity rule.

The native base is the least complete-definition closure of eight actual
external callees. Complete definition agreement preserves the existing
package, slot, and inclusion contracts. The derived upper boundary excludes
call-formation, proof, replay, truth, scope, and the older broad source
query. Historical theory imports are broader than the operative program;
that organization remains part of the later repository audit. One fixed
native compilation precedes every future operand and preserves its original
program scope, artifacts, and outgoing bindings.

The choices to use the existing context class, expose exact dependency
queries, keep list admission general, and derive original-source admission
from a closed included claim are justified above. All earlier definitions,
statements, assumption scopes, and proofs remain unchanged. The general
coverage theorem is an addition, not a change to the earlier restriction.

Native cause validation, authority, higher protocol admission, reflection,
genesis, and the system-wide presentation audit remain. The new mathematical
contracts and proofs retain O-85. Broader obligation states are unchanged,
and the final every-line audit has not begun.


## Native base validation follows the declaration and its recorded material

The independently defined base judgment is a supplied native definition's
positive application to the exact whole-artifact payload. Recorded base cause
additionally requires that the generation's actual whole cause quote the
complete minimal program-and-call scope and that its actual payload equal
the declared artifact. These definitions precede the new native clauses and
remain unchanged. The reader implements their complete conjunction.

The source classes use the existing complete judgment and generation sources.
The actual application determines the base artifact; the complete recorded
cause determines the recorded artifact. A generic determined-component class
exposes those values without storing a second payload in a source. A report
pairs the source with any complete presentation of that same exact artifact.
Generic products, subdomains, and complete quotation provide these classes.
The chosen report arrangement is an existing presentation construction, not
a privileged topology for base declarations.

Four native definitions have four ordinary clauses. Base reports call the
existing positive-judgment reader, read the actual application, and use the
existing material literal projection. Recorded reports read the actual core
payload, recover the actual recorded judgment through the scope contract,
require its least environment through judgment retention, and apply the base
report contract to that same judgment and payload. The two source admissions
use the generic projection clause.

The repeated source and application readings select already determined
components. They do not introduce a second judgment, a stored proof, an
independent payload declaration, or an externally supplied truth predicate.
Truth has its earlier independent least-positive meaning and exact native
reader. The recorded scope can be presented compatibly when checked, while
the actual whole cause artifact, its stored body, and its actual citation use
remain fixed by the source relation.

Local relation contracts cover all complete contexts and all generation
sources; false or unreadable contexts gain no admission. Determined-output
contracts admit exactly every complete presentation of the payload. Clients
inherit general adaptation and composition. The recorded checker consumes
the base contract at its own boundary rather than repeating its truth or
representation argument. Nonminimal recorded environments, false actual
declarations, and mismatched payloads are rejected. Base admission itself
does not require a minimal supplied environment; least restriction preserves
it. Recorded base cause requires that the environment actually quoted in its
cause already be minimal.

Complete-definition agreement is proved before combining reader programs.
A new general covered-domain union law joins the two component agreements.
A new general definition-group law preserves an existing group when its base
is enlarged by agreeing definitions. Both preserve full interfaces and clause
families, not just meanings at selected arguments. The operative base is the
least complete-definition closure of six actual external callees. The larger
source used to construct that base is not the final operative program.
Historical import breadth remains part of the later organization audit.

Accepted native reports recover the actual whole cause body, the declared
literal and its positive call, exact least retention, and the generation's
actual payload. Every report and source-admission result is preserved under
least source restriction. Equal cause and payload fields preserve recorded
base validity across different outer environments and historical predecessor
families. Neither predecessor emptiness nor a continuation rule is imposed.

Every valid declaration with any formed predecessor family has an actual
closed generation and native source and report material. The earlier explicit
finite base policy supplies witnesses for every formed payload and locus.
Complete source and report quotations are constructed. An actual formed false
declaration supplies readable native scope material while all base reports
and recorded-base validation reject it. One fixed closed native program has
four distinct operation sites before all future formed inputs, preserving
its original program scope, artifacts, and outgoing bindings.

The choices to expose a determined payload source and a separate report,
reuse the existing context classes, compose full shared definitions, and
keep arbitrary formed predecessor families are reasoned above. All earlier
definitions, statements, assumption scopes, and proofs are preserved. The
two general agreement theorems are additions to their owning theories.

Construction permission still requires formation and truth to be invariant
over all compatible presentations of every valid account. Ordinary positive
truth alone does not establish that global condition. Its native realization,
construction-cause validation, authority, the higher transition protocol,
reflection, genesis, and the system-wide presentation audit remain open.
The new mathematical contracts and proofs retain O-85. Broader obligation
states are unchanged, and the final every-line audit has not begun.


## Native fragment operations follow exact source selection

The existing fragment notion is one exact artifact and one finite selected
subset of its carrier. Selected material, omitted addresses, remainder, and
crossing incidence are derived from that basis. Their independent meanings,
formation conditions, partition theorems, and source reconstruction remain
unchanged. Establishing their complete native contracts before using them in
assembly follows the owner's direction to let notions determine their local
boundaries.

A source presents the complete artifact and exact selection through the
general product and observation constructions. It adds no stored material,
omission, boundary, remainder, or correctness proof. Complete payload and
incidence collections derive from the generic finite-set class. Attachment
and incidence element classes derive from ordinary products of opaque bytes.
All addresses retain their exact values. Incidence has three distinct roles;
the same address may occur in several roles. Only whole repeated triples are
excluded from a set enumeration.

The chosen combined report presents the source, selected material, crossing
incidence, and remainder. These three views reconstruct the full artifact.
An additional omission field is unnecessary there because the remainder's
carrier already supplies it. Omitted-address reading is exposed separately
as a derived query. These are presentation and operation choices, not changes
to the fragment basis or claims that every compatible class must use this
arrangement.

Twenty-two ordinary definitions have forty-two clauses. Eight local predicate
entries implement payload membership, attachment membership, wholly selected
incidence, wholly omitted incidence, and their explicit complements. The
complement theorem in the general presentation layer requires both valid
presentation domains. A malformed input therefore cannot pass by failure of
a positive membership call. Native absence uses the existing complete list
of positive inequalities; no negative native premise is introduced.

A single generic three-clause filter follows the actual keep and omit
judgments under the same context. It preserves input order and every retained
occurrence. Its proof concerns actual intermediate term lists. Eight uses
instantiate that proof with the complete local relation contracts. They do
not assert that an arbitrary element class has only one presentation. Final
artifact and finite-collection comparisons supply every compatible output
presentation. This separates the intermediate list algorithm from the full
semantic output contract without requiring an output normalization.

Source admission requires a complete formed artifact and selection, filters
the original carrier, and compares the resulting set with the entire supplied
selection. Thus no selected address can be invented. Material and remainder
filter every incidence, counted attachment, and functional attachment in its
proper role. Every retained counted occurrence remains present. Boundary
reading keeps incidence that is neither wholly selected nor wholly omitted.
The complete outside conditions permit repeated addresses within a triple.

The general encoded-collection comparison proves closure over every output
term. Artifact admission owns the analogous guarded comparison law. The four
fragment functions expose complete locally owned output contracts. The report
consumes those contracts at exactly the same source, accepts every compatible
combination, and recovers the original carrier, incidence, both data components,
and selected carrier. Wrong reports and invalid selections are rejected.

The program base is the least complete-definition closure of six actual
external callees. Existing interfaces, clause families, and meanings remain
complete. New clauses use existing data, comparison, selection, absence, and
artifact admission operations; they add no observation primitive, oracle,
truth parameter, or stored semantic witness. One fixed closed native program
has six distinct public entries before all future formed operands and
preserves its original scope, artifacts, and outgoing bindings.

Every formed fragment has admitted source material, every compatible report,
and complete source and report quotations. The empty and full selections fall
within the same universal contracts. All earlier definitions, statements,
assumption scopes, and proofs remain unchanged. The two earlier theories gain
only the general domain-relative complement and owned admitted-output lemmas.

Structural assembly, its complete origins and gluing conditions, and the
universally invariant construction-permission judgment remain separate work.
A positive permission call does not establish invariance over all accounts
and presentations. Construction-cause validation, authority, higher protocols,
reflection, genesis, and the system-wide presentation audit remain open.
The new mathematical contracts and proofs retain O-85. Broader obligation
states are unchanged, and the final every-line audit has not begun.

## Finite tables own the piece and origin presentation boundary

The independent table is a finite functional relation. Its keys distinguish
rows; its values need not distinguish them. This is already the structure of
piece families and origin maps. Neither a sorted serialization nor an ordered
piece list is substituted for that relation.

The general table class is derived from independent key and value classes:
products retain both row roles, complete collections retain every row exactly
once, and a subdomain restriction requires functionality of the recovered
relation. The class permits several presentations of each key and value.
Every order and every compatible component presentation remains available.
The restriction does not erase repeated values at different keys.

The existing finite-table presentation uses a target term as its empty-list
terminator. The data form uses an empty payload. Both retain their original
readings. Exact retermination recovers the whole intermediate list and derives
the earlier finite-collection class by generic composition. The existing table
class then follows by the same product and subdomain rules. The general
correspondence connects all presentations of the same table, including different
orders and value forms. No new proof of semantic compatibility is required of
a client using those exported classes. Actual physical table sources and their
socket boundaries remain separate observed material.

Piece families keep the existing arbitrary occurrence-key type. Their domain
is the original piece-family formation condition together with the explicit
key-class domain. A class covering every key therefore covers every original
formed piece family. Origins use a product key consisting of the piece slot
and its local address; their values are output addresses. No ordering or
global numbering of piece occurrences is imposed.

The assembly source class uses exactly the existing pieces and origins and
is restricted by the unchanged K2 relation. Its report presents the determined
output. Coverage follows from the original assembly results and the generic
component classes. This accounts jointly for the actual map, full carrier,
incidence, counted attachments, and compatible functional attachments. The
output is not an additional primitive field of the witness.

The native implementation in this batch chooses formed byte addresses as its
key instance. This is a sufficient concrete class, not a restriction on the
independent arbitrary-key assembly notion. It permits direct use of the
existing ordinary key-uniqueness checker. That checker compares the actual
encoded keys, so its exported generic implementation contract explicitly
requires an injective key encoding. It is not claimed to test semantic equality
of arbitrary relational key presentations. Artifact values retain every
complete presentation and need no unique encoding.

Six definitions use eight ordinary clauses: one row rule, two complete-list
rules, and one table rule for each of pieces and origins. Each table rule
has two separate premise sockets for complete row admission and key uniqueness.
The actual external dependencies are exactly payload admission, artifact
admission, and keyed-list admission. The program retains their least closed
base and preserves its complete definitions and meanings. The two public
entries are fixed before every future operand is supplied.

Empty tables are admitted. Equal artifacts at distinct slots remain two piece
occurrences; distinct copied addresses may have the same destination. Duplicate
source keys are rejected even when their values agree. Native table admission
does not assert complete origin coverage or functional-data compatibility.
The explicit empty-origin result shows that a table can be admitted while K2
fails for a nonempty copied carrier. Every formed K2 source nevertheless has
admitted component tables and every compatible complete report quotation.

The concrete key instance, terminator adaptation, and split between row checks
and key uniqueness are reasoned implementation choices. They preserve the
independent notions and use existing ordinary mechanisms. Complete native
gluing and attachment pushforward remain the next implementation boundary;
construction permission and its global invariance remain distinct. This batch
does not close mathematical proof presentation or the final repository audit.


## Higher-order reasoning has a reusable recognition boundary

The owner's clarification is applied before accepting the pending gluing
work. The draft was still isolated, so its structure could be assessed without
changing an accepted assembly notion. This review concerns meaningful depth:
independent notions and relationships that settle whole classes of uses, with
only the remaining conditions left to the next level.

The existing machinery already supports several such levels. Class coverage
and recovery justify semantic correspondence; correspondence and owned relation
contracts justify adaptation and composition; function contracts specialize
relations to determined outputs. Constraints, products, and covered images
then construct several of the current finite classes. The remaining weakness
was that some consumers still reconstructed relationships that those levels
could establish generally. The generation correspondence traversal, for
example, performed its own list induction after the element relationship had
already been established.

The accepted change uses the standard higher-order function relation in
Isabelle to express preservation of related arguments. Its list relator already
transports a relation between element relations to a relation between whole
sequence relations. Factor_Related_Lists now applies that theorem directly.
Its exact statement, locale assumptions, native clauses, and the two existing
generation uses remain unchanged. No parallel hierarchy or new universal
notion type is introduced for a relationship the library already supplies.

Presentation_Contract_Constructions connects that reasoning to complete local
contracts. Agreement on related arguments and a proved admission boundary
characterize an exact implementation contract. The recognition rule separates
the two conditions; a concrete counterexample shows why agreement on valid
arguments alone is insufficient. The subjects and their intended relation are
specified before this recognition test. Passing it does not justify choosing
that relation as the intended notion.

The comparison and identification rules concern relationships between whole
contracts. With complete classes at both boundaries, implication or equality
of the subject relations is equivalent to implication or equality of their
implementations. These rules let a proposed specialization or replacement be
checked at its semantic boundary. They also propagate a semantic counterexample
back to the claimed implementation relationship. Adaptation handles changes
of presentation before this comparison when the classes differ.

List lifting is derived through ordinary relational composition and the
standard list relator. Product lifting combines independently owned contracts.
Function graphs specialize those results; shared-source pairing keeps the
same recovered source in both component operations. The sequence term encoding
then composes with that established list relationship. The native traversal
needs one complete element contract and its actual formed context to export
the whole sequence contract, including all compatible outputs. A consumer
does not repeat the recursive native proof or assume unique presentations.

Each of these rules has a fixed immediate interface. Nested products, lists,
and compositions can grow without enlarging an individual rule's premises to
include all internal proofs. This is the supported local bound. The number of
distinct semantic conditions can still grow, and no theorem asserts that every
requirement admits such a decomposition. Finding an appropriate independent
notion is also not claimed to be a complete automated procedure.

The investigation at this stage was still a prose workflow. The owner's
2026-09-09 correction and the later candidate-development decision below
supersede any suggestion that these instructions alone represented the cycle.
First identify the content and intrinsic relations that must remain distinguished. Compare candidate
general notions at that semantic boundary, using recognition, specialization,
transport, and contract comparison to validate the proposed relationship.
Apply a proved construction rule and record which conditions it discharges.
Investigate the residual conditions in the same way. Keep a further layer only
when it supplies a relationship or proof that subsequent uses can consume
without restating the hidden detail. Counterexamples and failed domain or
coverage conditions remain evidence against the candidate decomposition.

The gluing development provides a separate application of that discipline.
Attachment pushforward is established first for arbitrary finite carrier and
value types and arbitrary maps. Its one count law serves every counted source;
the existing functional compatibility law accounts for the set image. Indexed
piece enumerations specialize those operations through the already independent
piece-family relation. The assembly-specific work is the correspondence between
its occurrence keys, complete origin domain, and four existing output fields.
It does not re-establish finite pushforward for each field or add new primitive
fields to an assembly witness.

Every formed piece family has a complete enumeration in every supplied order
of its slots. Equal artifacts in different slots remain different occurrences.
The finite assembly criterion accepts any complete target enumeration. A
constructive output witness removes duplicates from the carrier, incidence,
and functional lists after mapping; its counted list retains every occurrence.
This is one witness, not a preferred presentation. Shared destinations are
permitted, with functional conflicts excluded by the original target formation.

Choosing these construction and recognition rules is evidence-driven, not a
prescription to use one formal hierarchy everywhere. The broader O-84 audit
must continue looking for reusable relationships and remaining repeated local
arguments. Complete native gluing, global permission invariance, construction
and authority, higher protocols, reflection, genesis, native mathematical proof
presentation, and the final every-line audit remain open. No obligation state
is promoted by this batch.


## Concatenation is a fold over actual terms

Native gluing needs to collect the contributions of every source piece. The
existing correspondence traversal already supplies mapping from one owned
element contract. The remaining list operation is ordinary concatenation.
It has meaning independently of gluing, and it is an append specialization
of the standard right fold. That relationship supplies a reusable recursive
argument instead of a separate recursion for each assembly field.

List_Relation_Folds composes step relations using the library's existing
right fold and relational composition. It permits partial and multivalued
steps. One encoded step equation, a seed boundary, and closure of the state
domain determine an entire encoded fold. The equation does not need an
injective encoding; recovery is separately required when constructing a
complete presentation class. No new truth mechanism is introduced.

Factor_List_Folds gives this operation two ordinary native clauses. The
recursive tail and the actual step callee have distinct premise sockets and
share the same intermediate result. The complete proof permits positive
dependency cycles in the supplied system. Consumers use the exported fold
contract without repeating its native induction.

The empty clause returns its seed literally and checks only its formation.
This exposed a reusable condition on a proposed semantic interpretation.
Literal copying is a complete semantic identity operation exactly when each
subject has one presentation. Presentation_Contract_Constructions proves
both directions and gives a class with two equivalent forms where copying
fails the complete identity contract. This criterion also applies to a
table lookup that returns a stored term. Semantic equality or transport is
needed when a consumer must admit every equivalent output form.

The concatenation instance therefore declares its subject as sequences of
actual formed self-contained data terms. The existing append callee owns
that data boundary. Fixing the seed to the empty list gives ordinary concat,
with all term details and occurrences retained. Empty inner lists contribute
no elements; repeated equal elements still contribute separately. The
accepted contract does not quotient those elements by an unrelated semantic
class. Output artifact comparison will supply that later assembly boundary.

The native instance has two definitions and three clauses. Its sole external
callee is append; the least complete dependency closure determines the base.
The generic recursive-group construction preserves that base's actual
interfaces, clause families, call boundaries, and meanings. One fixed native
operation precedes every future operand and preserves the compiled scope,
artifacts, and bindings.

The mapping-to-concatenation rule now requires only an element equation, its
data boundary, and the owned concatenation equation in the same program.
These discharge traversal, order, and multiplicity. Origin lookup, complete
coverage, and comparison with all four output fields remain assembly work.
The new mathematical results retain O-85; all broader obligation states and
the final every-line audit remain open.


## Table operations retain actual forms before semantic comparison

Native gluing reads the piece and origin tables actually supplied. Existence
of some presentation of a piece would not justify silently replacing its
stored field order. The general correspondence is between a distinct source
list and the values actually related to its entries. List_Relation_Indexing
proves that correspondence once. Functional-row recovery then identifies the
semantic value at each listed key. Factor_Data_Table_Operations composes these
results with the existing complete table class and decomposes both stored
components. Encoded keys are a specialization; relational values retain all
their admitted forms. No new table subject, ordering convention, or identity
field is introduced. Indexing functions outside the listed keys remain proof
choices with no part in the represented table.

The assembly-specific residual condition is that each stored value is an
artifact presentation. The complete value reading supplies its four actual
field lists. The resulting theorem gives exactly a piece-family enumeration
whose encoded rows reconstruct the supplied term. The existing finite copied
carrier, incidence, attachment-count, and functional-image laws now apply to
those same lists. Different slots containing equal artifacts still contribute
separately. No traversal or pushforward law is reproved for this extraction.

Literal table lookup exposes a separate reusable boundary. The existing
selection operation returns a form present in the supplied collection. If
each subject has one form, this is already complete membership. Otherwise a
comparison must connect that stored form to the requested form. The general
transport theorem uses recovery of the selected element's subject to prove
that composition exact. The complete membership contract also includes
whole-source admission, since selecting one row cannot establish a complete
collection boundary. A two-form witness proves that a compatible form need
not itself be literally selectable. This specializes the previously proved
copy criterion and records the remaining condition rather than concealing it
inside an assumed lookup contract.

Origin keys and destinations use exact payload encodings and therefore have
one form. Origin selection and value lookup specialize the unique-form result.
Their complete table premise supplies functionality and coordinate formation;
lookup alone does not admit that table or establish its coverage of a piece
family. The existing row-key and row-value projections preserve actual order
and repetitions. Equal destinations at different source keys are retained.

Gluing also requires a comparison that permits repeated image entries in set
fields. Ordinary list-set comparison is meaningful independently of assembly:
its subjects are actual data lists and its relation is equality of their sets.
One ordinary clause composes the existing inclusion operation in both
directions. The native proof reuses the owned inclusion contract. There are
two premise sockets even when the calls happen to agree. Its sole actual
external callee determines the least closed base, and the existing recursive
group construction exports complete-definition agreement for later joins.

The complete relation contract does not change list identity or count
semantics. A two-occurrence list and a one-occurrence list can compare equal
as sets while bag comparison rejects them. The encoded collection-output law
therefore allows repeated image entries without permitting duplicate entries
in a complete collection presentation. It will apply to merged incidence and
functional images; counted attachments still require bag comparison. A fixed
native set-comparison entry precedes future operands with its package scope,
artifacts, and bindings retained.

This batch settles actual row extraction, the lookup-form boundary, and the
set comparison needed by the assembly composition. It does not add a native
K2 clause or promote an overall obligation state. Complete origin coverage,
native piece transport and their combined output report remain the next
assembly work. Construction permission and its global invariance, higher
protocols, reflection, genesis, native mathematical proof presentation, and
the final every-line repository audit remain open.


## Native assembly composes the existing transports and complete comparisons

The independent subject remains the original piece family and one origin
relation. The output is determined from them. The chosen implementation checks
a complete source-and-output report, then derives source admission by the
existing reader projection. This avoids another primitive output field in the
witness while admitting every compatible output presentation. It is a design
choice: an independently developed source-only compatibility checker could
also establish K2, but would not discharge the report correspondence by itself.

One piece visit computes its four contribution lists together. Occurrence keys
tag every carrier atom and every coordinate used by incidence or attachments.
All lookups consult the identical admitted origin table. The incidence step
has three distinct premise sockets and private selection remainders; counted
and functional attachments share one atom-transport step and copy the opaque
value unchanged. Four applications of the existing complete correspondence
traversal account for all list recursion. A partial-map specialization exposes
the exact remaining lookup domains. The earlier total encoded-map theorem is
its total-domain instance, with its statement unchanged.

The four-field fold is a product of existing append calls. Its empty seed is
the four empty fields. The general relational fold owns the native recursion;
the specialization establishes only componentwise closure and the ordinary
fold equation. Complete piece-table extraction fixes the actual input lists,
so no proof replaces a supplied piece by an arbitrary new enumeration. The
result retains every original counted occurrence, including equal artifacts
at distinct occurrence keys. Temporary tuple and list abbreviations introduce
no additional semantic subject or primitive material field.

Traversal only checks the origin coordinates it uses. Full coverage is a
separate report premise comparing all copied atoms with the origin key list,
including atoms absent from every incidence and attachment. This permits a
noncircular proof: a successful partial traversal determines its actual
contributions; the independent carrier comparison establishes full coverage.
Conversely, full coverage supplies every traversal domain condition through
the artifact enumeration's owned support theorem. Both complete table guards
and output admission remain present when the traversed lists are empty.

The origin value list is compared with output atoms. Incidence and functional
images compare as sets, allowing repeated images after gluing; the counted
field compares as a bag. No destination injectivity is assumed. Formation of
the complete output excludes functional conflicts. The existing finite
assembly criterion accounts for these conditions together, and the original
assembly-relation theorem identifies the determined K2 output. All-term
equivalences therefore support complete native source and report classes.
The exported output function contract supplies client totality, every output
form, adaptation, and composition without reopening the native proof.

Integration exposed repeated reasoning that belongs to more general owners.
Whole-source definition agreement now gives meaning transport directly,
rooted systems export variable calls and member meanings, and finite clause
families give a common formation rule. Existing fragment, table, concatenation,
and set-comparison formation or base proofs reuse these rules with their old
statements intact. Complete ancestor agreements for the actual row program
are established once and composed across the existing table and comparison
groups. The final assembly base is the least closure of its nine actual
external callees. The twelve new definitions contain seventeen ordinary
clauses; two public sites are fixed before all future operands and preserve
the compiled scope, artifacts, and bindings.

These additions use higher-order relationships where they remove repeated
work: clause-family formation, whole-program agreement, partial-list mapping,
and fold specialization. The remaining local details are the intrinsic four
artifact fields and their different observation relations. No layer merely
renames the final assembly claim. Native mathematical presentations and checks
of the new proofs remain under O-85. Construction permission and its global
invariance, higher protocols, reflection, genesis, and the final every-line
audit remain open; no overall obligation state is promoted by this batch.


## Term sequences and complete key lookup precede construction admission

The existing construction claim retains ordered artifact inputs, unordered
functional tables, structural natural indices, and the earlier complete-list
terminator. Input repetitions are meaningful. Whole-artifact references are
formed terms but are not self-contained data terms. Those distinctions make
the earlier data-only selection contract too narrow for direct source lookup.
The account and permission definitions remain unchanged.

The chosen next batch establishes independently useful sequence and table
operations before composing construction admission. The already proved native
right fold supplies all traversal reasoning. One ordinary constructor keeps
each head; another replaces it by the existing empty payload. Their folds
retain arbitrary formed terminal seeds. The existing empty payload and empty
artifact target specialize this operation to the two established list formats.
The same operation relates the established natural encodings. No source-role
tag or replacement account format is introduced.

A list position is the whole sequence with a bounded natural index. The chosen
native implementation reconstructs it from a prefix, selected head, and tail,
and counts that identical prefix. A direct recursive index reader would also
be possible. Reusing the fold instead settles recursive semantics through
existing contracts and leaves only the general prefix equation locally.
Its three premises have distinct sockets. The independent complete-list guard
is necessary: a formed improper suffix passes reconstruction and zero-prefix
counting but fails full admission. No out-of-range default becomes a result.

The element subject is the actual formed term. Generic products, sequence
lifting, and domain restriction give complete classes for folds and positions.
Their function contracts inherit totality, every compatible term output,
invariance, adaptation, and composition. This literal operation does not by
itself supply every presentation of a different element notion. Terminator
conversion likewise retains one actual ordered sequence; semantic identity
between arbitrary finite-table enumerations remains the separate table-class
correspondence. The mathematical pair of fold operands is a presentation of
the two actual call fields, not an extra stored wrapper.

The native key checker already requires self-contained keys and only formed
values. Its generalized relational theorem and the general table-admission
profile now expose precisely that boundary. The earlier data-row results are
stronger-input instances with unchanged statements. Complete functional-table
lookup specializes the existing collector to a singleton fibre. It retains
the supplied literal value, including whole-artifact references. A successful
singleton fibre cannot establish global key uniqueness; a table with duplicate
unrelated keys is a proved counterexample. Whole source admission remains an
explicit premise for subsequent composition.

Five new native definitions contain seven ordinary clauses and no external
callees. Three public operation sites precede all future formed operands and
preserve the compiled program environment, artifacts, and bindings. No native
consequence primitive, canonical table order, or permission policy is added.
These source-lookup contracts prepare complete construction admission and its
recorded cause join. Their global permission condition and O-85 mathematical
proof presentations remain open, as do higher protocols and the final
repository audit. This batch changes no overall obligation state.


## Complete source lookup composes existing boundary notions

The independently defined source context contains an ordered artifact list
and a finite functional base table. Its query also contains an actual input
position or base key. Existing construction, selection, and permission
definitions retain their meanings. This batch makes source availability
native before joining it to fragment selection and complete construction.

Whole-artifact literals have a complete class derived from their injective
existing constructor. The material-projection reader supplies all artifact
data presentations and, by ordinary projection, literal admission. The input
sequence retains order and repeated occurrences. The base table retains all
keys and exact artifact values in every complete row order. General products,
table classes, retermination, and subdomain restriction supply the context
and query classes. No stored result, source-role tag, or canonical table order
is introduced. The existing source function is used only under actual source
membership; its total host-language default is never a successful result.

The chosen implementation admits the whole context before either lookup
branch. An alternative could distribute the guards across the branches, but
one common source contract keeps the complete boundary local and makes unused
members explicit. The existing list-position operation handles input sources.
The existing key collector handles base sources only after whole-table
functionality and every row's formation have been established. Its singleton
result therefore denotes precisely the actual entry. A duplicated unrelated
key still permits singleton collection at another key but is rejected by
source admission. Missing keys and end positions remain outside the query
domain, even if a later fragment would select no atoms.

The original natural and payload constructors separate the two source roles.
Changing the natural representation without a role boundary would conflate
input position zero with the empty base key, so this implementation uses the
already proved exact terminator conversion instead. A witness admits both
roles in one context with independently supplied artifact values. Repeated
input positions remain different queries even when their outputs agree.

Two general additions contain recurring reasoning. Table component restrictions
lift through the complete row relation, and formed values need not be
self-contained. Retermination transports relational key and value classes.
The ordinary two-reader composition profile shares one actual intermediate
term at separate premise sockets; complete contracts with that same class
give a complete composed function contract through the existing relational
composition theorem. Different intermediate classes still need their proved
correspondence. This profile is justified independently by sequential reading
and is instantiated here to convert the exact looked-up literal into every
artifact-data presentation. No representation-specific conversion proof is
carried into that client.

The native lookup pairs the complete query `(context,index)` with its
result. This is the binary relation boundary consumed by the general
composition profile; grouping the existing fields adds no stored value.

Eight definitions contain eleven ordinary clauses over the least closure of
six actual external callees. Complete agreement preserves their original
interfaces, clause families, and meanings. Four public operation sites are
fixed before future operands, preserving the exact native scope and every
original artifact and binding. This establishes source availability, not a
construction policy's permission or global invariance. Complete construction
admission, recorded construction causes, higher protocols, reflection,
genesis, native mathematical-proof presentation, and the final repository
audit remain open. No overall obligation state is promoted.


## Complete construction uses returned witnesses and complete downstream contracts

The current requirement is native structural admission of the independently
defined construction account. Its primitive basis is the complete source
context, selections, and origins. Pieces and output are derived. The existing
five-field claim also states the output it asks to admit; it is checked against
that derived value. This batch preserves every existing theory and introduces
no extra field or canonical enumeration. The original complete claim's
coverage and recovery establish the account class directly.

The source-to-fragment operation uses four existing owned contracts. Actual
source lookup retains the whole input and base boundary. Retermination keeps
the supplied selected-set order, complete set comparison allows every output
set order, and fragment admission checks the selected atoms against the exact
source. The general reader-composition profile then supplies every material
presentation. Empty selection still requires an actual source.

A table value traversal exposed a distinction in the general contracts.
Pointwise traversal retains input row order, so it cannot by itself return
every unordered-table presentation. Restricting the table class to that
particular output order would make its boundary depend on this implementation.
Adding a permutation operation is possible, but the downstream requirement
already has a complete presentation-invariant test. The chosen general notion
therefore specifies a sound total returned witness between two complete
classes. It requires an actual result for every admitted input and the correct
independent value for every returned result. It makes no false claim of raw
output completeness. Literal copying provides an independent example and a
counterexample to conflating this notion with a complete function contract.

A complete following relation consumes any such witness and gives a complete
composite relation. Function graphs and semantic identity give function
composition and output completion. The predicate form requires an exact
observation on the entire target class; an arbitrary raw boolean test fails
that condition. Restrictions preserve their subject boundaries. A presentation
change uses the intermediate class's recovery. Covered subject images transfer
the operation when their maps commute. These are criteria for recognizing and
constructing relationships between contracts, rather than new names for the
details of construction selection.

Independent pair contracts give the product map. Existing sequence lifting
accounts for traversal. Restricting to distinct functional rows and projecting
both sequences to their sets gives table mapping through the general image
criterion. Keeping each actual key makes the map injective on a functional
relation even when its values coincide. Thus value noninjectivity never merges
piece occurrences. The native key checker and whole-context guard supply
separate conditions. An empty table still admits all unused input and base
material. Native retermination retains the original input format.

The final assembly step applies the witness predicate rule. The existing
assembly contract proves the complete observation condition and discharges
row ordering for every construction client. The remaining local obligations
are the original claim's field linkage, its actual origin table, and its
claimed whole-artifact output. Exact all-term admission recovers the complete
valid account, and every permitted presentation supplies accepted native calls.
Tests distinguish equal-material slots, repeated keys, absent sources even
with empty selection, invalid unused material, missing or extra origins, and
wrong outputs. A valid empty construction remains admitted.

Whole-component agreement also has reusable transitivity, union, restriction,
and recursive-group rebasing criteria. Their application retains every actual
source, fragment, and assembly interface and clause family. The new six-site
group has seven ordinary clauses over the least closure of ten external
callees. Three public sites have one native program fixed before future
operands, preserving its exact scope, artifacts, and bindings.

The higher-order direction is applied during this milestone because these
independent contract relationships settle otherwise repeated local work.
Their depth corresponds to different obligations: component relations,
product and sequence construction, restriction and commuting images, and
complete downstream consumption. This is evidence for those relationships,
not a claim that every requirement admits a bounded hierarchy. The wider
notion and presentation audit remains necessary.

The concrete structural checker is invariant on every complete valid claim.
That theorem does not admit an arbitrary supplied permission program or
check its universal formation-and-truth invariance. Those global conditions,
recorded construction causes, higher protocols, reflection, genesis, O-85,
and the final repository audit remain open. No overall obligation state is
promoted in this batch.


## Candidate evaluation and development are themselves represented relationships

The owner's 2026-09-09 comment identifies a real gap. The earlier recognition
and construction theorems supplied reusable components, but the complete
investigation cycle remained a prose instruction to the agent. The construction
milestone was already in validation, so it was completed and delivered before
this related batch. That ordering preserved a reviewable accepted boundary.

The independent notions used here are conditional reduction, inference closure,
method simulation, partial-order comparison, and coverage of a search scope.
They make sense without a particular construction requirement. The choice to
compose these existing mathematical ideas, rather than introduce a universal
datatype of notions or a generated hierarchy, follows the owner's separation
and non-nominality principles. The subject and condition types remain
polymorphic. Their meanings are fixed before proposed reductions are checked.

An obligation family retains an identified occurrence for each condition.
Substitution qualifies child occurrences by their parent; equal conditions at
different places do not merge. A sound reduction states sufficient conditions.
An exact reduction additionally reflects the original requirement. Both have
specialization, substitution, and residual-discharge laws. The domain coverage
and established conditions needed by those laws remain explicit. General
families may be infinite when a quantified schema covers infinitely many uses;
finite executable accounts separately prove a complete finite boundary.

A method supplies inference rules with complete finite functional premise
families. Its least closure gives precisely finite derivability from supplied
assumptions. The rule-soundness condition relates that structure to an
independently stated meaning. No membership flag validates a rule, no absence
of a found proof proves falsehood, and an unsupported cycle contributes
nothing. Existing Factor instances satisfy the same consequence equation, so
the new account connects to the actual language instead of replacing it.

The comparison order is inclusion of conditional capabilities over every
assumption set and conclusion. Its exact local criterion asks whether each
source rule can be established by the target from the same premises. This
criterion, its transitivity, and its residual consequence are reusable proof
results. They distinguish a supplied proposal from evidence that its use
preserves the earlier account. The finite evaluator uses the same closure
and residual definitions for an actual complete table. Standard monotone
iteration supplies termination and leastness; an SML export checks that this
finite specialization has operative code. It is not a new native Factor entry.

The immediate-premise bound establishes a particular locality comparison.
It is insufficient as the justification for a broader depth decision. The
owner's subsequent correction requires the choice of observations and search
scope to be assessed, and the resulting reasons to guide the investigation.
The later depth account below supplies those relationships. In particular,
concatenation preserves the binary method's complete capability at this bound
while improving dependency rounds through an unbounded family. Completeness
for the earlier observable therefore does not settle the relevant comparison.
The establishment of a derived rule remains a separate obligation from its
later use.

Selection is consequently a partial order. A maximal candidate has no
dominating alternative, but incomparable alternatives may remain. Complete
coverage is stronger: every alternative's conditional capability is included.
A smaller inspected frontier supports either claim only after a dominating
cover of the intended scope is proved. A scope generated by allowed development
steps includes all finite paths, including plateaus. The finite-edge theorem
does not establish that a supplied edge table contains all intended moves.
These distinctions prevent stopping from being inferred from an iteration
limit, an empty immediate improvement list, or a finite example catalogue.

Finite conjunction supplies a substantive test of the account. Its meaning is
fixed for arbitrary element predicates and lists of every finite length.
Flat introduction has one premise per occurrence; binary introduction uses
the head and tail, with the same projection relationship. Both methods have
equal unbounded conditional power. With two immediate premises, the binary
method retains all that power and the flat method does not. The small
counterexample only distinguishes the methods; universal characterization
theorems justify the result for the entire domain.

The conjunction stopping claim ranges over every uniformly sound method for
that independently fixed meaning, not just the two exhibited methods.
Semantic completeness proves that none can add a conditional use beyond the
binary method at the stated bound. This closes that particular comparison
question. It does not establish that no other aligned improvement to the
repository exists, nor that a missing element condition has been proved.
Counterexamples separately retain unresolved goals at a complete candidate
and show that an infinite candidate scope need not have a maximal element.

The same account evaluates a candidate that is itself a generalization method.
Method comparison becomes an exact obligation reduction to actual source
rules. Composing comparisons first exposes two conditions, then substitutes
their local evaluations with qualified occurrences. Derived-rule completion,
a transformation on arbitrary methods, enters this same evaluator. Its
remaining conditions are discharged from the original closure, yielding
conservativity. Its unbounded capability is unchanged; any additional claim
about locality or cost still needs evidence. This is ordinary compositional
reasoning about the method, with no self-approval or special privileged level.

Validation exposed an unjustified type generality in the first draft of
derived-rule completion: its result could use a different occurrence type
from its source. A Boolean occurrence type can distinguish two premise
positions; a singleton type cannot hold two distinct conditions in one
functional premise family. For the sole rule deriving 2 from 0 and 1,
completion into singleton-indexed families therefore loses a capability.
The explicit counterexample records this failure. The corrected completion
preserves the source occurrence type and every original premise family.
General method comparison continues to allow different occurrence types,
but changing them requires simulation evidence. This is a recorded correction
to the initial frozen definition, not a proof-only repair or a restriction of
the already accepted language. The revised batch retains the original freeze
and failed diagnostics and freezes the corrected definition before validation.

Presentation transport uses the existing actual-consequence fixed-point law.
Complete recovery then preserves each remaining occurrence domain. The copy
proposal retains its exact representation-uniqueness condition; completion
through the already established witness contract discharges the alternative
without narrowing the class. Factor conditional graphs supply their actual
assertion family to the same residual account. Establishing the root by
additional reasoning does not retroactively replace an assertion by a proof
edge in the old graph.

The changes represent a mathematical evaluation and development cycle and a
terminating finite-table specialization. They do not finish O-84 throughout
the repository or O-85's native presentation of the resulting mathematical
contracts and proofs. Candidate generation, intended semantic-model and scope
choices, other locality observables, arbitrary permission invariance, recorded
construction causes, higher protocols, reflection, genesis, and the final
every-line audit retain their outstanding work. These choices must be
evaluated through the same discipline as their evidence becomes available;
no overall obligation status is promoted by this batch.


## Local invariance is a proved reduction of the existing global requirement

The next construction and cause work must retain the actual supplied permission
program. Its existing formation-and-truth invariance condition is global over
every complete valid account. Replaying one call does not establish that
condition. The recorded cause also fixes the complete minimal program-and-call
environment; replacing its program by a wrapper would change that content.

The independent general relationship is invariance under a relation and its
finite-path closure. The standard function relator states it without a new
primitive notion of predicates. A proposed presentation generator is admissible
only when it preserves the independently fixed subject and covers every pair
of presentations by a path. Under those two obligations, edge observations
are exactly the global invariance requirement. The empty-generator example
rejects a vacuous local check with missing coverage. Refinement uses the same
criterion by simulating every old edge with a path of new ones.

For construction claims, the three unordered fields form a complete product
of presentations of the fixed base, selection, and origin values. Replacing
them in turn gives three actual intermediate claims of that same account.
This proof supplies generator coverage; it is not assumed from a convenient
sample. The existing five-field format and every nested selected-set order
remain admitted. Ordered input occurrences, unused source material, and the
exact claimed output stay fixed. The chosen local boundary is one whole outer
field. Further descent inside a field may refine it through the generic path
simulation criterion; no constant bound on internal condition complexity or
execution cost is claimed by the three-step result.

The candidate enters the existing exact obligation reduction. Each local
condition keeps the observation function and both terms. Separate formation
and truth positions qualify these endpoint occurrences, so equal outcomes do
not merge obligations. The concrete structural admission theorem settles the
whole family. The previously proved order-sensitive program leaves a residual,
which cannot be removed by established true conditions.

Existential completion was also considered because it supplies an invariant
observation for every raw predicate. It is useful as a general mathematical
construction: it is the least invariant extension on a complete class and is
idempotent. It is not a justification for changing the existing permission
policy. Its agreement with the original observation is exactly invariance,
and that agreement is itself evaluated by the same condition family. An
independent intended meaning retains separate soundness and true-subject
coverage requirements. The concrete order counterexample gains a formerly
false answer after completion while its original program remains inadmissible.
Two separately completed tests may also require incompatible presentations;
their conjunction cannot replace a shared existential witness.

The cause specialization keeps its independent original meaning. After actual
scope, package, and application reading, exact reduction exposes five positions:
least environment, exact payload, complete account, global permission admission,
and positive truth. A generic discharge combines local permission evidence with
the other established conditions. Positive truth alone leaves the global
condition; wrong payload and excess scope remain explicit false conditions.
The account stores its original basis, with pieces and output derived. No proof
field, preferred ordering, alternative program, or new consequence rule is added.

All previously accepted theories and repository validation tools remain byte
identical in this batch. The new results are mathematical contracts and exact
reductions. Finiteness of the five-position cause family does not make each
condition decidable. Native admission of global invariance evidence and the
general recorded construction checker remain open, as do higher protocols,
reflection, genesis, native mathematical-proof presentation, and the final
every-line audit. The existing obligations retain their status. This is a
further application of the represented evaluation cycle, not a claim that the
whole foundation has reached a justified stopping point.


## Native correspondence makes a checked permission clause meaningful

The existing global permission condition must remain a property of the actual
program named by a construction or cause. One positive call cannot establish
it. The interpreter-admission work supplies a relevant precedent: whole
definition reading can check a sufficient structural profile, whose universal
meaning is proved against an independently fixed reference. It does not decide
every semantic correctness property of arbitrary programs.

The proposed permission profile uses the already defined existential completion.
Two identified premises share one actual witness: the first compares the
submitted account with that witness and the second applies the actual test to
it. The first requirement is therefore a native complete correspondence
contract, not merely admission or equality of one serialization. The earlier
construction field-generator theorem remains valid; its local global-condition
reduction is separate from this implementation of the full correspondence.

The existing bag-matching proof assumed self-contained data at every element.
Construction bases contain literal whole-artifact values, so that assumption
cannot serve their complete original presentation class. The independent
matching relationship is between occurrences under a supplied element relation.
Its proof needs the corresponding element boundary and formation, but does not
otherwise inspect self-containment. Exposing that parameter supplies the exact
generalization required here. The original related_bags locale and all its
public theorem statements remain unchanged; their proofs now specialize the
general related_occurrences proof. Both ordinary clause families also remain
unchanged. Existing clients continue to receive their original data contract.

Complete conversion changes only a list terminator. A separate ordinary clause
uses two such conversions and the same actual occurrence-comparison callee.
The general collection law then compares every permitted enumeration, including
independent member presentations. Formation remains explicit at every member.
The source does not acquire a preferred sorting or a second stored account.

The construction specialization admits both whole original accounts, compares
every base and origin row literally, and compares selection rows through their
exact key, source coordinate, and complete selected-atom collection. The two
ordered input lists and exact outputs are shared literal fields. Eleven
definitions contain sixteen ordinary clauses; their base is the least closure
of the two actual external callees for conversion and construction admission.
The proof exports the complete identity function contract on accounts and a
closed native correspondence reference before any future policy or operand.

The two-premise permission clause has a rule equation for every supporting
relation. Its witness variables and premise sockets retain distinct roles;
neither is merged even when callees or values coincide. Fresh views preserve
the actual old program. Complete native definition reading inspects the entire
variable interface and singleton clause family, so hidden alternatives and
material conditions cannot enter the claimed equation. Compilation supplies
actual admitted instances over every formed environment with both anchored
callees. The comparison callee's meaning is still independent evidence.

Shared-definition agreement transfers that fixed comparison meaning to the
actual candidate package in a common formed environment. General saturation
then proves formation and truth invariance. The original cause reduction
consumes this result alongside its other four conditions. A larger evidence
environment can retain a reference root omitted by the original minimal
judgment scope; inclusion preserves the original program and does not change
the recorded scope or payload. No cause is silently evaluated under a wrapper.

The example expressly constructs a new completed policy. Its native code has
checked complete-definition evidence and accepts both presentations of the
two-base account. Its own literal test and the earlier order-sensitive program
remain noninvariant. Thus completion is useful as a construction while its
agreement with an original observation still enters the same exact obligation
reduction. This is not a proof that every submitted original policy can be
replaced, or that positive execution proves a universal property.

All 606 other accepted theories and every repository validation tool remain
byte-identical. The matching refactor preserves all previous declarations and
their enclosing assumptions. Validation separately checks those scoped public
contracts, the frozen new declarations, all existing failure fixtures, and the
full theory graph. The obligation statuses remain unchanged. A single native
checker for the whole sufficient profile, general recorded-cause admission,
native mathematical-proof presentation, higher protocols, reflection, genesis,
and the final every-line audit remain open. The present profile is a supplied
candidate evaluated through existing contracts, not a stopping claim for the
whole investigation.

The frozen diagnostics identified reserved spellings used for assumption
labels and an origin-list variable. Replacing those names changes no logical
condition or premise. The import review also removed a forwarding theory
already inherited through the three owning contracts; shared-package meaning
belongs to their existing locality ancestor. The revised freezes record these
syntax and dependency edits separately from proof repairs.

The proof review exposed a remaining dependency in the first draft of the
permission client: freshness still inspected two earlier program layers.
The comparator now owns the bounds of its actual base and complete definition
domain. Its group proof uses the base bound; later extensions use only the
complete comparator bound. These two additional theorems preserve every
existing statement and keep the client's dependency condition local. They
describe construction coordinates for this finite program, not a semantic
privilege of those coordinates after native compilation.


## A native profile check consumes complete syntax and preserved reference meaning

The remaining gap in the preceding sufficient permission construction was a
single operative check of its finite evidence. The chosen independent profile
requires an actual member of the original complete package, a whole variable
interface with exactly the related-witness clause, and a common formed
environment retaining both the candidate and a fixed reference. The reference
program's comparison contract is established independently. No candidate
semantics or positive sample supplies that contract.

The complete schema-observation class already determines syntax. Its report
retains the binder and both entire output families, with the actual prospective
callees and empty material families. A private constructed report orders the two
roles, but covers every permitted native binder and socket coordinate. Complete
binder admission forces the two variables to differ. Functionality of the
prospective rows forces distinct sockets because one argument is a pair and the
other a payload in the determining observation. Additional inequality calls
would repeat consequences of this complete boundary and are therefore omitted.

Four identified ordinary premises suffice: actual package membership, complete
definition reading, and the two environment inclusions. Membership already
admits the complete package. The existing variable-interface and singleton
reader already rejects omitted alternatives and unsupported material. The
common environment is private finite evidence; it cannot change either retained
artifact or any existing interpretation. It may retain a reference root selector
that the candidate's least package scope omits.

The original program-entry value is used without changing its grouping. Its
class follows from the complete site class, a literal site-coordinate class,
and restriction to actual occurrence in the same environment. No duplicate
program is stored. The independent native profile then restricts that complete
context class. Exact all-input admission and presentation invariance preserve
every compatible source and fixed-reference presentation.

Composition requires complete agreement of the reader programs' shared
definitions. The whole-definition reader now owns its all-value equation,
complete base agreement, and definition bound. The combined implementation
retains the least closure of the three actual callees. It adds one definition
with four ordinary premises and one fixed native compilation before future
inputs. Coordinate bounds establish construction freshness; they give the
chosen numbers no semantic privilege after compilation.

The generative obligation also exposed repeated package-selection reasoning.
One general theorem now consumes a closed finite family of actual complete
definition readings and constructs its exact root selector. The earlier
forwarding theorem keeps its complete public statement and uses this theorem.
A second general construction installs any formed ordinary or material clause
whose actual callees belong to an existing package. Its private coordinates may
be renamed, while all original call boundaries, meanings, artifacts, and
outgoing bindings remain unchanged. The related-test candidate construction
specializes those results. This is a reusable construction with multiple
consumers, rather than a profile-specific duplicate of closure and selection.

The independently compiled construction comparator fixes the semantic reference
before the native profile checker and every future candidate. Successful profile
admission entails the existing saturation equation and global formation-and-truth
invariance of the actual submitted program. The same residual mechanism then
discharges its permission family. Recorded construction still separately needs
the original least scope, exact payload, complete account, and positive truth.
Neither evidence nor an alternative policy is inserted into generation identity.

Every compatible package containing both callees has a constructed closed
candidate and every complete context presentation is accepted. The final fixed
native checker has an actual admitted input, independently of whether a chosen
underlying test accepts a construction. The earlier noninvariant policies retain
their meanings; this construction does not justify replacing them. The profile
is exact as a sufficient structural class, not a decision procedure for global
invariance of every positive program. Broader behavior coverage and general
recorded-cause admission remain explicit further work.

All 608 other accepted theories and every repository validation tool remain
byte-identical. The two proof-bearing edits preserve every prior scoped public
contract; the completed-policy theory receives only a corrected progress note.
The two added imports supply actually consumed general agreement and selection
theorems. Frozen review records these dependency additions explicitly. Obligation
statuses are unchanged. Native mathematical-proof presentation, higher protocols,
reflection, genesis, the broader application audit, and the final every-line
review remain open. No stopping claim for the whole foundation is made.

The frozen proof run exposed two missing ownership references. The new clause
package constructor now imports Factor_Program_Scopes for its actual root,
entry, and closed-environment contracts. The new program-entry field theorem
now writes its locally owned site_data_term encoding explicitly; the earlier
unavailable shorthand had been parsed as a free function and was not proved.
This correction avoids importing an unrelated callee-admission program merely
for that shorthand. The revision preserves all previously accepted statements
and every other frozen new declaration and assumption.


## Native invariant completions cover every supplied finite positive test

The preceding sufficient profile admitted only candidates already sharing the
fixed comparison reference. The next independent requirement is coverage:
construct an admitted invariant completion for every actual native test, then
use native program compilation to cover every entry of every formed finite
positive program. This does not require deciding the original test's global
invariance. It requires a construction whose exact meaning is established
independently and whose agreement condition is evaluated explicitly.

The existing universal positive query already receives the original complete
environment, package site, entry, and arbitrary operand as ordinary data. A new
one-premise clause fixes that source data and forwards the future operand to
the actual query callee. The original source's private uses need not coexist
with the reference's uses. No candidate-selected truth predicate is installed
as operative code. The new test's positive truth equals the original test's
truth at every operand, including when the source contains material clauses.

The account comparator and positive query need one shared reference before
future tests. Their common definitions are actual identical row operations.
Two general composition laws propagate overlap agreement through rooted
restriction and through an independent recursive group. Applying these laws
twice retains both original programs. The final native reference is their
least actual two-entry dependency closure. It does not duplicate shared helpers
merely to avoid accounting for their common material.

Argument construction is a justified common abstraction: fixed-result checking,
fixed-scope forwarding, and the supplied program test each use one actual callee
and one identified premise with a fixed argument pattern. The pattern's only
variable is the future operand, which may be repeated or omitted. The general
rule preserves arbitrary formed literals and all-support meaning. Formation
of the operand remains required even when the pattern omits it. The existing
two rules keep their complete public statements and consume this rule.
The generic single-clause package compiler supplies native syntax and its
private coordinate variants, then preserves every old call and meaning.

The related-test package constructor previously exposed a profile and preserved
old meanings, but its public result did not identify which supplied test drove
the new entry. The stronger construction contract now exposes that exact
two-callee equation and the new entry's call boundary. The previous totality
theorem is a corollary with its original complete statement. This makes the
universal completion proof consume the constructor's contract directly.

The completion has exactly two fresh definitions beyond the fixed reference:
the test and the related-witness permission. They remain distinct from each
other and from every old reference entry. The test retains the original source
truth; the permission is its independently defined least invariant completion.
The reference's old interfaces and meanings remain unchanged. The same native
profile checker admits every complete context presentation of this candidate.
Its native code is fixed before all future source programs, and each such
presentation has an actual formed positive application retaining the checker
scope, artifacts, and outgoing bindings.

The exact criterion for agreement with the original decisions is the existing
observation reduction. Soundly settled facts remove only their established
obligation occurrences. Completion agrees with the boundary-restricted original
truth exactly when that truth is invariant on the complete account class.
Every globally invariant original permission therefore has an admitted policy
with the same decisions on complete accounts. Completion remains false outside
that class. A variable interface in the new code is not asserted to preserve
an arbitrary original interface, even when its positive truth is invariant.

This evaluates a supplied construction candidate through the existing complete
meaning and residual mechanisms. It does not use a successful construction as
a stopping claim for arbitrary-code admission, reflection, or the whole system.
Empty positive meanings are covered. An empty program supplies no actual entry;
the theorem's entry premise reflects that boundary. Earlier constructed
positive and noninvariant examples remain unchanged, and completion still
does not authorize replacing their programs or their recorded causes.

Two ownership repairs accompany the construction. Actual anchored targets in
a formed environment already lie in its finite position family, so root and
complete-definition selection now derive finiteness internally. Existing
finite-premise statements remain corollaries. The complete environment-inclusion
agreements, positive-query base agreement, and construction row agreement now
belong to their component owners. Later clients compose those facts instead
of reopening the earlier native reader implementations.

All 605 other accepted theories and every repository validation tool remain
byte-identical. Every earlier public declaration and its enclosing assumptions
is preserved. The explicit import changes retain all earlier ancestors; the
fixed-result theory reaches its previous parents through the new common rule
owner. Frozen declarations, scopes, imports, source identities, existing failure
fixtures, and the full session are checked together. Obligation statuses remain
unchanged. General recorded-construction admission, native mathematical-proof
checking, higher protocols, reflection, genesis, and the final every-line audit
remain open.

The frozen proof run exposed a coordinate boundary in the first completion
proof: its source theorem permits arbitrary use types, whereas complete
environment quotation uses native option-address coordinates. The general
source contract is retained. A new shared program_test_completion theorem
uses the existing injective program compiler once, then quotes that exact
native representation. Both the original native-source theorem and the
abstract-program theorem consume this stronger construction directly. No
existing declaration or assumption is narrowed, and no double compilation
is required. The explicit revision adds this one general theorem; the other
diagnostic repairs change only binder, formation, and account witness proofs.


## Recorded construction classes, exact reader joins, and actual material

The next independent subject is the original construction judgment and its
recorded cause. Completing an arbitrary source program does not validate or
replace that original cause. A sufficient profile must concern the exact entry
of the program recovered from the actual recorded application. Its account,
payload, and least judgment scope remain separate conditions.

The actual permission profile therefore constrains the existing judgments.
The new source classes derive the account through the original functional
reading; they store no second program, call, or account. Complete report classes
pair that source with every allowed presentation of the same account. Their
domain is stated independently before the reader-composition theorem. The
original global permission requirement is retained.

Two recurring class proofs exposed duplicated boundary reasoning. A general
determined-component subdomain theorem combines functional recovery with an
explicit source boundary. A general pair-subdomain theorem combines complete
component classes with the actual relation boundary. These are consequences
of the existing presentation rules, with no new semantic or structural
primitive. Eight earlier base, recorded-scope, and payload-scope class proofs
now consume them with their original complete statements and assumptions.
The four new construction classes use the same rules.

The proposed construction reader joins four actual ordinary calls: native
positive judgment, the actual application reading, the complete permission
profile, and full account comparison. The application fixes the entry checked
by permission admission and the operand compared with the proposed report.
Account comparison preserves every permitted nested table order and the exact
input and output boundary. No preferred enumeration is selected.

The recorded reader adds the actual generation report, its quoted judgment
scope, least-scope admission, and the artifact projection of the report's
output field. This ties the payload to the same account as the actual call.
The account owner exposes that field shape. Local relation and function
contracts then provide complete outputs, invariance, restriction of the outer
source, and rejection of wrong payloads or nonminimal recorded scopes.

The global permission proof belongs to the native profile itself. Its existing
native presentation-admission theorem now consumes that stronger owner-level
contract. The profile also survives restriction to an included environment
recovering the identical program. Its reference evidence remains separate
from the minimal recorded scope and does not become part of cause identity.

Future application construction requires care about compatibility. A profile
provides a common formed environment containing both the reference and the
candidate. The construction first selects that witness, then extends it with
the future application. An arbitrary extension of the candidate alone need
not remain compatible with the reference. No such universal preservation
claim is made. The resulting program is the same actual native program.

Each admitted source call has an actual closed generation recording its exact
least program-and-call scope. All complete outer source presentations and all
account reports satisfy the joined relation. Separately, the existing universal
completion constructor yields one native policy accepting exactly the whole
construction-account class. It supplies recordings for every complete account,
every formed locus, and every finite formed predecessor family. This is
constructed coverage over the full stated domain, not a finite list of examples
or an inference of inhabitance from an empty constrained class.

The exact join is presently a mathematical relation over existing ordinary
reader meanings. Physical composition of the readers is a remaining condition,
including agreement on their common bag-difference definitions as well as
ordinary row helpers. The batch establishes the independent domain, exact
relation, compatible outputs, and material coverage needed to assess that
composition. It does not claim that the combined reader is already installed
in one native program. The next composition must consume these local contracts
and account for all actual shared definitions before native compilation.

All 615 other accepted theories and every validation tool remain byte-identical.
Every previous public declaration and enclosing assumption is preserved. The
three new theories, eight edited theories, documentation, frozen declarations,
scope checks, existing failure fixtures, and full session are validated as one
batch. Obligation statuses remain unchanged. Arbitrary original-program
invariance, native mathematical-proof checking, higher protocols, reflection,
genesis, and the final every-line audit remain open.


The first combined proof run required quoting the reserved fact label
`output` in one new theorem. Its name, premise, and conclusion are unchanged;
the correction supplies Isabelle's required lexical form. The frozen batch
was archived and renewed explicitly for that syntax correction. Other repairs
instantiate the declared relation and provide its actual witnesses without
changing any statement, definition, scope, or import.


## Depth investigation retains reasons and governs its own observations and scope

The owner's further 2026-09-09 correction concerns the effectiveness of the
complete development process. A weak depth decision can prevent useful
general notions from being used where they matter most. Reasons must expose
what is missing and direct the choice of search goals, transformations, and
comparisons. Merely replacing one scalar by several unchecked scores would
leave the same problem.

The recorded-construction milestone was already applied, reviewed, and in its
full-session check. It was validated and delivered first, preserving a complete
accepted boundary. Investigation of this correction then took priority over
physical composition of the construction readers. That composition remains
open and will consume the resulting discipline.

The existing selection theorems already accept arbitrary capability sets.
The missing relationship was between the independently intended comparison,
the observations selected to assess it, and the search that consumes the
assessment. The new account reuses those selection and reduction theorems.
It introduces no primitive notion kind, privileged method level, or externally
trusted decision flag.

### The comparison question precedes its observations

An observation profile retains a facet and an actual witnessed use. Its two
directed differences expose both gains and losses. A preservation claim must
account for the whole current profile; a new use with a loss elsewhere remains
an explicit tradeoff. No arbitrary weighted ranking resolves incomparable
cases.

The intended comparison is specified from the independent subject and its
relevant uses before observations are selected. An observation basis must
preserve and reflect that comparison on the stated candidate domain. Its
failure retains the actual pair of candidates. When an adequate larger family
is available, the failure identifies an omitted facet and distinguishing use.
Adding that facet strictly improves the observation method's discrimination.
If even the whole proposed observation language misses the distinction, the
counterexample remains a condition for further development.

This makes observational adequacy an evaluated claim, rather than an inference
from choosing a measurable feature. A general down-set construction proves
that preorders have observation bases; it does not make their arbitrary
semantics executable. Finite candidate domains have finite bases when the
whole observation family is adequate. Neither existence theorem establishes
that a finite candidate domain covers all relevant future developments.
Essential-facet witnesses separately justify irredundancy.

### Reasons determine further work

A missing use determines an attainment goal that also retains the current
profile. Available inference rules expose their complete premise families;
backward demand preserves the actual rule and each identified use of a
condition. Established evidence ends its own expansion. Alternatives remain
separate rules and their premises remain conjunctive. Restricting inference
to that complete demand preserves every original answer and residual for the
requested goals. An unsupported reachable cycle still supplies no proof.

The target also determines a relation of development steps. Its completeness
theorem preserves every path to the requested result, including plateaus and
intermediate states that do not themselves improve a measure. The theorem is
relative to the actual supplied development relation. Its intended coverage
requires separate evidence; a finite edge list does not certify that coverage.

A covering method names the representative for every alternative in the
intended candidate scope. Its membership and preservation claims have their
own complete condition family. The same evaluator assesses observation
selection, the covering method, and the final frontier comparisons. The
combined stopping theorem consumes their separate rule-soundness and
established-evidence accounts. It retains the reasons for closing the stated
comparison question and cannot use the frontier as its own coverage proof.

### Evidence for the chosen facets and constructions

The choices are justified by existing relationships in the package:

| Choice | Evidence and resulting use |
|---|---|
| Retain dependency rounds as well as logical consequences | Inference has actual finite premise dependencies. The union of all rounds is exactly the earlier closure, while local round preservation has its own exact simulation criterion. Thus rounds add a justified distinction and their projection recovers conditional capability. |
| Investigate concatenation after binary conjunction is width-complete | Concatenation is an independent list relationship and head-tail introduction is its specialization. Balanced construction covers arbitrary finite lists. A repeated list of length two to the n needs only n concatenation rounds, while the binary method from singleton seeds cannot exceed length n plus one in those rounds. The strict gain persists for every n at least two, despite equal complete two-premise capability. |
| Compare every compatible reader output | The existing function contract quantifies every permitted output presentation. All sound total identity witnesses already have the same input coverage. Input-only observations are adequate for their whole comparison exactly when presentations are unique. Otherwise, two actual presentations expose the missing use and direct the existing completion construction. |
| Remove weaker observations already determined by stronger ones | Round observations already retain conditional capability. Complete output observations already determine input availability. The stronger basis therefore need not duplicate the weaker facet in these cases. The same candidate evaluator justifies the observation selection. |
| Include establishment size and reuse scope when that is the question | A finite shared body, its copied occurrences, and client interfaces give explicit structural counts. Sharing reduces size for repeated uses, while an unused established body still contributes size. The workload is part of the comparison domain. These counts are not elapsed time or evidence that the body is valid. |
| Keep setup proof obligations separate from later interface depth | Derived-rule completion is conservative, but an installed shortcut can expose a one-round use whose establishment in the source needs two rounds. The round comparison reduction retains that extra condition instead of treating the shortcut as free. |

The reader application supplies an explicit cover of the entire sound total
witness class, not only the two exhibited implementations. The conjunction
application preserves the earlier infinite-class completeness theorem and
exhibits a further relevant distinction that it cannot settle. These two cases
also differ in when depth is needed: presentation uniqueness makes the weaker
reader observation adequate, while nonuniqueness yields a constructive reason
to develop it.

### Operative finite accounts and remaining work

The finite implementation returns all observation-basis mismatches, candidate
losses, demanded conditions, and the full rule and premise occurrence behind
each reason. It is proved equal to the general account. Guided evaluation
preserves the original evaluator exactly and still rejects unused malformed
rules by checking the complete original table. A submitted finite observation
table must separately be related to the independently meaningful observations.
Its SML export checks operative code without turning a table entry into a
proof of semantic adequacy.

All 626 accepted theories and every validation tool remain byte-identical.
The eight new theories, revised explanation, admission and obligation records,
frozen declarations and contexts, failure fixtures, and full session are
validated together. The older immediate-premise paragraph is corrected
directly; the new account does not rely on its disclaimers as a justification.

The selected comparison meanings and observation families are explicit choices
for review. Their alignment is supported here by actual dependency structure,
complete presentation contracts, preservation, and structural reuse. Other
case-specific meanings can enter the same typed reduction and investigation
account, including proposals about the comparison method itself. Native
checking of these mathematical soundness, basis, and coverage proofs, wider
application throughout the repository, physical construction-reader composition,
and the final every-line alignment audit remain open.


## Composition investigation derives the relevant structural comparison boundary

The next recorded-construction milestone physically joins independently owned
reader programs. The intended operation retains their actual complete
definitions at shared heads. The depth investigation therefore examines
whether the proposed observations justify that operation and which reusable
relationships can discharge its conditions.

The first result is a limitation of the evaluation representation itself.
An exact profile-inclusion basis entails reflexivity and transitivity on the
candidate domain. Together with the existing down-set construction, these
laws identify the order boundary of that representation. They are necessary
conditions on the independently intended relation, not extra assumptions
silently attached to a desired answer.

Agreement on each pair's overlap changes the comparison boundary with its
arguments. A formed program with one variable interface agrees on its overlap
with the empty program, and that empty program agrees with a program having
a differently bound variable interface at the same head. The first and third
programs disagree on their shared definition. Thus compatibility on changing
overlaps is not transitive even when all programs are formed. No observation
language can make it an exact profile-inclusion order on that whole domain.
The result prevents an invalid use of the general candidate machinery.

The relevant repair follows from the actual composition obligation. Fix the
definition boundary being inspected, retain its complete interface fibres and
identified clause families, and compare those observations. This supplies an
exact basis for agreement on that boundary. Empty fibres are observable; a
partial lookup with an unspecified value at a missing head would lose this
property. The same qualified profile reduction reports the exact definition
and material responsible for each directed loss.

The choice is supported by two distinct failures of weaker evidence:

| Available evidence | What still fails | Consequence for investigation |
|---|---|---|
| Equal complete call boundaries, consequence operators, and least positive meanings | Two different variable interfaces at one head can make their union nonfunctional. | Semantic observations alone cannot certify physical sharing of the interfaces. |
| Equal call boundaries, consequence operators, and meanings, with a formed union | The same schema at different clause coordinates changes the complete recorded family. | Union formation and meaning preservation do not entail retention of the actual clause occurrences. |

The second result also limits the claim in the other direction. Literal
whole-definition agreement is a sufficient condition for the required
preserving composition. It is not asserted to characterize every formed
union or every union that preserves meaning. Semantic correspondence and
private renaming retain their own existing contracts and uses.

The missing boundary evidence determines the useful generalization. A common
component can transfer agreement between two programs only when its definition
domain covers every shared head. Neither target needs to retain the entire
common component. This permits later rooted programs to reuse the same rule.
Agreement with a union follows from agreement with each formed component on
its own overlap. This agreement theorem does not itself assert that the union
is formed; that requires the existing separate compatibility condition.

These laws are used immediately. Construction's sequence and bag comparison
components share their covered bag ancestor. Related-test admission shares
the covered definition-call ancestor. Recorded base-cause composition consumes
the two generation and scope overlap contracts through the new union rule.
All three keep their original exported mathematical statements. The changes
make the reusable reasoning operative before the larger native reader join.

This is a justified next step in the owner's requested depth investigation:
the case exposes an inadequate observation language, a relation outside the
candidate-order representation, and the exact missing coverage conditions.
Those reasons determine the observation domain and the reusable proof search.
They do not supply a universal depth oracle. Physical installation of the
complete construction-cause reader, native checking of the mathematical
contracts, remaining strata, and the final every-line audit remain open.


## The recorded-construction join becomes one actual native program

The preceding composition investigation identifies the conditions that the
physical join must preserve: complete interfaces and identified clause
families at every shared definition. Applying those conditions reveals two
different dependency paths. The ordinary lower overlap is covered by the
whole row component. Counted bag difference is also used by the generation
reader, but that reader retains only actual rooted dependencies. Treating it
as retaining the whole comparison program would assert an unjustified boundary.

The target comparison owner now proves preservation of its whole counted bag
difference component. The base-cause owner carries the required overlap through
the generation target restriction, value and source groups, scope restrictions,
and retention group. The construction program's successive groups use the
same generic overlap laws, with their actual freshness conditions. The fixed
permission program shares a covered definition-call ancestor and its configured
entry is fresh. Every ordinary union is formed only after these complete
shared-definition agreements have been established. No copied namespace is
needed and no semantic-equivalence claim substitutes for material agreement.

The resulting source retains all eight actual external callees of the new
clauses. Its implementation base is exactly their least complete-definition
dependency closure. The existing finite-family formation theorem closes the
new group, and the ordinary projection profile supplies both source entries.
The two report clauses have these precise roles:

| Report | Actual linked conditions |
|---|---|
| Construction profile | Positive judgment, application reading, whole permission profile at that application's entry, and correspondence between its operand and the complete reported account. |
| Recorded construction | Actual generation fields and payload, the cause's quoted judgment, least judgment scope, the construction-profile report on that same judgment and account, and literal projection equating its output with the actual payload. |

Both all-term equations are proved from every valuation of the actual complete
singleton clause families. Every variable's formation is derived from a
successful ordinary callee, including auxiliary generation fields and all
five account fields. The equations realize the two independently specified
reader joins before any class, relation, or compilation contract is exported.

Four native presentation classes admit exactly the complete independently
specified source and report domains. Owned relation and determined-output
contracts admit every compatible account presentation and supply the existing
adaptation and composition laws. Outer source invariance, least source
retention, wrong-payload rejection, and nonminimal quoted-scope rejection are
transferred to actual native calls without extra assumptions.

One closed finite native program is fixed before every future formed argument
at all four distinct entries. Its canonical program scope, existing artifacts,
and outgoing bindings are retained. The previous original-program recording
construction now yields reports admitted by this reader. The same witnesses
cover every complete account and every formed locus and finite formed
predecessor family. No recorded program or application is replaced.

This closes the physical native join left open by the preceding milestones.
It implements the complete sufficient permission profile of the original
construction judgment. It does not decide global invariance of arbitrary
original code. The new component, valuation, class, and exactness proofs
remain subject to O-85's native mathematical-proof presentation and checking.
Broader obligation states remain unchanged; further strata and the final
owner-alignment and every-line audits still require work.


## Actual execution exposes both computational and observational limits

The earlier SML checks established that the finite functions could be generated
and compiled. They did not establish practical execution on project questions.
A repeatable command now supplies that missing use: its list interface has
proved projections to the original finite relations, and the command executes
the actual Isabelle-exported functions. Rules and observations are finite input
data; their independently intended meanings remain explicit conditions.

The first project case asked which exact proof contexts remained for four
proposed permission deliverables. Its complete local closure contained 411
theories. The accepted source receipt supplied 386 exact contexts; 25 still
required local checking or changed parent contexts. Eleven of those 25 had
unchanged local text. Comparing only a file's own digest would have incorrectly
reused their old context evidence. The rules retain each local proof check and
every actual parent as separate premises. They describe conditional readiness,
not derivation of mathematical truth from an import edge. One accepted session
can establish many of these local conditions together.

That 93-edge case initially exceeded 60 seconds. Profiling located duplicated
recursive calls in finite path closure, repeated closure across roots, and
repeated demand inside report filters. The fix is stated and proved as code
equations. Each recursive prefix is computed once; a finite root family shares
one complete transition closure; reports and guided selection share demand.
The original definitions, path bound, all old contracts, labelled outputs,
cycles, and whole-table formation remain intact. The repeatable runner returned
all 93 reasons in about 0.41 seconds of evaluator time in the development run.
This observation demonstrates the improvement on that case; it is not a
complexity bound or a performance guarantee for arbitrary finite input.

The second case examines linked semantic subjects. Candidate 0 pairs identity
with identity, and candidate 1 pairs identity with negation. Their common
presentation class contains all Boolean presentations of one unit subject.
The independent comparison asks whether joint completion feasibility is
preserved. Every observation is computed through the existing existential
completion definition, with a proved exact observation table and relation.

| Selected evidence | Executed result | Consequence |
|---|---|---|
| Each component has some successful witness | Both candidates have the same profile, but comparison `(0, 1)` fails. | Separate completion loses compatibility of the witnesses. |
| Both components have one common successful witness | The full directed comparison is preserved and reflected. | The joint facet is an adequate basis on this domain. |
| No selected facet | Comparison `(0, 1)` fails again. | The remaining joint facet is essential. |

The two weaker facets add no distinction for this particular comparison and
need not be duplicated. Their separate values can still matter for a different
question. The result supports joint investigation when the intended use shares
a witness. It does not license replacing a completed conjunction by a
conjunction of separate completions, nor does it enumerate all permissions or
all possible development methods. The existing candidate, observation, and
completion structures already express this case; no primitive joint kind is
needed.

Execution itself has an explicit evidence boundary. The command snapshots the
complete engine import closure, identifies its source and tool bytes, and
requires a successful Isabelle session before extracting any generated module.
A blob left by a failed session is never a success criterion. The runtime
program encodes only checked natural identifiers and quoted paths. Natural
numbers remain unbounded private identifiers, and tuple conversion respects
Isabelle's right-associated products. Input, engine, tool, runtime, and proof
receipt bytes are checked again after execution. Each invocation writes a fresh
atomic receipt and a complete log; timeout and interruption terminate spawned
process groups. Diagnostic extraction retains errors even when the extractor
itself returns a nonzero status.

The runner's fixtures exercise startup, proof and export failure, changed
sources, tools, cases and generated modules, malformed results and identifiers,
whole-input rejection, timeouts, interruption, child termination, tuple
conversion, and changed import contexts. Actual exported executions separately
retain repeated premise uses and goal occurrences, leave an unsupported
conjunctive cycle unresolved, reject an unused malformed rule, and preserve a
large natural identifier with a nonzero observed value. These runtime checks
complement the arbitrary-input projection theorems and the complete repository
proof session.

This milestone makes the existing investigation machinery usable immediately
while preserving the stronger unfinished work. The permission generalization
continues to require its own proof acceptance. Global invariance of arbitrary
original programs, native presentation and checking of mathematical contracts,
higher strata, and the final alignment and every-line audits remain open.


## Permission families share a contract while their complete subjects remain distinct

Five existing invariance definitions repeat the same observations of the actual
selected program: call formation and positive truth. Their complete arguments
differ. Exact equations to those original definitions justify generalizing
the observations without erasing the independent subject boundaries.

| Permission role | Complete subject retained |
|---|---|
| Construction | Ordered inputs, complete bases, selections and origins of a valid account; its exact assembled output is derived. |
| Adoption | Authority target, complete generation core, and purpose target. |
| Continuation | Independent before snapshot, transaction, claimed after snapshot, and submitted environment and site. |
| Amendment | The complete current frame, candidate generation, and supplied certificate target. |
| Site | The supplied complete environment and exact use and address. |

Products of existing classes supply the four newly grouped argument classes.
Their field equations recover the original value relations. No derived program,
permission, currentness, transaction result, or validity evidence is stored.
Construction retains its assembly and coordinate boundary. The current frame
keeps both actual scopes; a claimed after snapshot remains an independent input.

The observation theorem works for any value type. Invariance on a presentation
fibre is equivalent to existence of a factor through the subject. Class totality
makes that factor unique on the independent domain. Mathematical choice in the
proof selects no operative representation. The paired specialization keeps
formation and truth. Existence of some factor does not establish agreement with
a separately intended meaning.

The same exact reduction supplies qualified conditions for both observations
and every compared pair. Each original permission inherits those laws.
Construction's three-field generator and exported residual theorem retain their
statements. Another class's proposed generator still requires its own
preservation and complete-path coverage proofs.

## Executed comparison preserves refusals as well as successful calls

The comparison asks whether a program's decisions are preserved on its supplied
argument domain. A positive-use set alone loses an original refusal when a new
successful call is added. Each observation therefore retains its Boolean
outcome. Inclusion of these complete graphs is exactly decision agreement,
giving an exact basis for the independently specified comparison.

Actual formed programs justify both facets. An empty-payload interface with no
clauses and a variable interface with no clauses have equal empty meanings but
different call boundaries. The latter and a variable-interface recognizer have
equal call boundaries but opposite truth. Each pair supplies the omitted facet
and a concrete lost outcome. The general theorem rules out every proper subset
of the two facets over all formed program entries.

The finite execution uses these three programs and two arguments: an empty
payload and a pair of empty payloads. Proved equations compute their actual
interfaces and positive-meaning observations. The complete table and intended
comparison have independent exactness contracts. The existing evaluator returns:

| Selected facets | Failed directed pairs | Consequence for search |
|---|---|---|
| Formation | `(1, 2)` and `(2, 1)` | Equal interfaces leave opposite truth unobserved. |
| Truth | `(0, 1)` and `(1, 0)` | Equal empty truth leaves different call boundaries unobserved. |
| Both | None | The basis preserves every decision in this finite scope. |

The first exploratory run used a proposed table and explicitly left its semantic
link unproved. The reproducible permission command now computes the table from
the actual program definitions using proved equations. It requires successful
checking of its own complete dependency session before export. Results include
the computed table, comparison, profiles, and losses. The finite case exercises
the evaluator; the separate general proof establishes the wider facet claim.
Neither result introduces a native negative premise or a general decision
procedure for nonmembership in arbitrary positive meanings.

## A shared native profile supplies construction and adoption permissions

The complete related-test profile already depended on construction only through
its comparison reference. The general contract now owns that dependency:
a complete class, formation of its values, and an independently proved native
comparator precede every candidate. The existing ordinary checker retains the
actual candidate, complete definition, both callees, and a common formed
environment containing the fixed reference. Mathematical conditions on that
reference are not installed as native predicate callbacks.

An admitted profile has a variable interface and exactly the invariant
saturation of its actual test. Compatible callees have a constructed fresh
policy, admission of every complete source presentation, and preservation of
all original call boundaries and meanings. Construction's admission and
completion interfaces consume these general proofs without changes to their
statements or enclosing assumptions.

Completion additionally requires the universal query in the actual reference.
It quotes a source environment in the established presentation coordinates and
its entry directly. The abstract constructor compiles its source once and
delegates to that construction. The generic native wrapper retains arbitrary
source-use types through the abstract path. The locale's subject type is
explicitly independent of the source program's binder and occurrence types.
New-test truth preserves source truth, and the new permission is its saturation.
Both new interfaces are variable. Truth agreement requires truth invariance;
formation agreement remains a separate condition. No recorded cause receives
a replacement source program through this construction.

Adoption supplies a second independent native instance. Two ordinary
three-premise definitions admit and compare authority, generation, and purpose.
Their least base follows the four actual target and generation callees.
Generic pair identity lifting consumes existing component contracts, so the
client does not repeat target enumeration or generation recursion. Every
complete field presentation is admitted; correspondence is equality of the
three independent values.

One fixed native checker entails the original adoption invariance condition
for each admitted actual program. The native adoption join retains its package,
entry, application, and subject. Under that admission, closed replay is exactly
the remaining certificate condition for the particular call. A constructed
policy accepts the whole raw adoption domain and has certified calls for every
complete presentation. It establishes neither generation-cause validity nor
publication or currentness.

Two independent native comparators now instantiate the admission contract,
and all five original families instantiate its semantic contract. Construction
also has the query required for arbitrary-source completion. Adoption currently
has comparison and raw-domain admission; its query join remains separate work.
An exact basis for decision agreement settles neither physical program
retention, native availability, proof-establishment cost, nor wider search
coverage. Those remain distinct questions for further investigation. Arbitrary
original-program invariance, native mathematical-proof checking, higher strata,
and the final alignment and every-line audits remain open. No broader obligation
status is changed by this milestone.

## Complete substitution supplies a finite native step with a universal rule consequence

The next correctness task needs a way to relate complete schematic clauses.
The existing native derivation reader checks individual instantiated calls.
Its success does not by itself establish a clause relationship for every
future valuation. The earlier two-observation theorem already determines the
entire finite pattern grammar, including every material operand. That evidence
supports extending its existing readers to substitution between schemas.

The intended transformation is fixed first. A substituted clause must retain
every identified prospective socket, its callee, every material socket, and
all five material patterns. The head alone is insufficient. The earlier
counterexample proves that even all ordinary instances can conceal an omitted
material condition. Private marker assignments therefore recover material
operands without demanding that their material equations hold at those markers.

The substitution operation is shared by the head, all prospective arguments,
and all material fields. Its variable set is exactly the union of variables
in the used replacements. Identity, composition, formation, and valuation
commutation follow from the existing pattern operation. Existing injective
coordinate renaming is its variable-only specialization. No occurrence,
material field, or callee is discarded when replacement values coincide.

Commutation gives one semantic inclusion for every support relation and later
valuation: every substituted rule instance is an original rule instance.
Replacing a variable by one literal can lose other original instances.
Complete valuation coverage is a sufficient reverse condition; injective
variable renaming supplies it. It is not asserted to be necessary for every
particular rule. This distinction is required by the executed permission
example: increasing positive truth alone can lose an original refusal.
Whole-program equivalence also retains each interface and the interpretations
of actual callees in their respective contexts.

The observation experiment specifies equality of the five actual substituted
patterns before choosing observations. Its replacements are variables 0 and 1,
payloads `[0]` and `[1]`, and one fixed target. Each replaces both occurrences
of a unit variable in a pair. The exported code performs the substitution and
evaluation. The numeric output map is proved injective on the complete output
scope of this case, and the comparison is linked to actual pattern equality.

| Evidence selected | Failed directed comparisons | What the failure requires |
|---|---|---|
| Distinct payload markers | 0/2 and 1/3, in both directions | A second constructor family distinguishes variables from matching payload literals. |
| One constant target marker | Every distinct pair among 0, 1, and 4 | Distinct payload markers retain variable identity and distinguish a target literal. |
| Both probes | None | The full basis determines all five substituted patterns in this scope. |
| Both probes with collapsed payload markers | 0/1 in both directions | Merely retaining two probes is insufficient; the marker assignment must preserve distinct binders. |

These are actual exported evaluations, with per-invocation proof acceptance,
complete source and tool snapshots, computed observations and comparison,
profiles, and every directed loss. An invalid facet is rejected by whole-table
formation. The earlier proposed table was exploratory evidence; these executions
link the results to actual substitutions. Their finite domain does not replace
the general pattern induction or establish arbitrary program equivalence.

The failures determine the native composition. An existing pattern record
holds pairs of a literal source-variable address and its replacement pattern.
Two readings of that same record produce complete binding tables for the
original schema. The constant-target reading forces each actual field to have
the literal-key shape; complete functional bindings force every source binder
to appear once. The replacement function outside that finite binder has no role.

The target schema supplies the complete remaining variable scope. Its two
canonical tables are also used to read the replacement record. Two original
schema readings and two target schema readings share the entire conclusion,
prospective, and material outputs. Together with the marker-table traversal,
these are seven calls to existing native operations. One ordinary clause
composes them, with exactness for all input terms and a fixed closed native
checker before future inputs. Actual environments, uses, roots, field order,
private positions, and external slots remain accounted for by the owned readers.

The source, replacement, and target sites form an intrinsic joint relation.
Their complete class derives from the existing site classes, two products,
and a subdomain. The checker preserves and reflects that independent relation
on every compatible presentation. The replacement record is interpreted in
the target binder; a function from the record alone to a target is not claimed.
Every actual substitution has the seven readings. A ground schema's existing
empty binder also has the existing empty-record shape and supplies identity
substitution without changing any source artifact. Native schema compilation
then constructs an admitted input, so the new check has an established use.

This bounded extension is useful now because it connects existing finite
syntax admission to a law about every future valuation. It jointly develops
the pattern, material, schema, and native source boundaries using their existing
operations. A new general mathematical-proof grammar would require its own
independent subject and exactness account; this step does not assume one.
Native checking of these mathematical proofs, wider schematic proof coverage,
higher strata, and both final audits remain open. The finite executions and
native compilation do not close those obligations.

## Uniform proof structure follows from the limits of call observations

Two determining syntax probes do not establish an arbitrary program's meaning.
The comparison is fixed independently as formation and truth agreement on
every formed term. The existing finite-relation program containing the payload
and target markers and the existing variable-pattern family both admit every
formed call and prove those markers. Their pair call has opposite truth.

The exported evaluator actually computes these observations from proved
program equations. Selecting both markers leaves both directed comparisons.
Including the pair removes both; the pair alone also separates this two-program
family. Invalid facets are rejected. The complete outcome code distinguishes
formation and truth, including refusal. The finite result has an independent
coverage argument for these two programs.

The wider obstruction is proved using the existing finite-relation semantics
and the previously established infinite formed-term domain. Any formed finite
literal family agrees with the universal recognizer on every term it contains
and differs at a further formed term. This identifies where additional depth
is valuable: complete proof structure can justify future valuations, whereas
another finite collection of positive answers supplies no general coverage
argument. The existing pattern-family and finite-relation constructions remain
the program subjects; their meanings are not supplied as truth callbacks.

The scheme relation retains the actual clause at every inference, its complete
replacement relation, every prospective socket and callee, and the complete
claim reading. Each actual interface has its own finite substitution witness.
The proof consumes the local instance obligation at every node, so retaining
only the root's choice would leave the child obligations unaccounted for.
The literal program's two marker proofs have different clause origins.

Graph geometry is shared through one binding-value parameter. The old ground
node and graph types remain aliases of their ground specialization. All old
ground checking conditions remain; four clients only follow the generated
datatype and record theorem names. Node renaming now works for every binding
value type. Evaluation preserves nodes, clauses, discharges, and assertion
uses even when binding values become equal. There is no second scheme-specific
graph geometry and no relaxation of the assertion-use condition.

Material conditions are derived from the selected source clauses and pattern
replacements. Each retains its inference occurrence, material socket, and all
five operands. They are conditions on later valuations, rather than assumed
truth at the private syntax markers. Evaluation reconstructs the existing
admitted instances and checked graph. Its exact assertion boundary supplies
conditional soundness through the existing graph theorem.

Two existing programs exercise the distinction. The universal recognizer has
one closed scheme before every future term. The incidence rule retains all six
variables and its full material condition, including variables absent from the
root. A formed payload valuation refutes erasing that condition. For a scheme
with no material or assertion assumptions, a separate theorem extends any
root-pattern valuation by formed terms on the remaining variables. This proves
coverage of every root instance without assuming an existential material
witness for arbitrary root arguments. Assertion-only schemes retain their
identified root claim as an assumption.

Use also exposed a runner ownership boundary. Each built-in case now has one
registry entry containing its source theory, export, and independent scope.
Dispatch, input formation, output checks, and command registration use it.
A raw JSON proposal cannot replace that case's reported scope or choose an
unregistered export. Its original description remains in the saved input.
Both a fixture and actual exported execution exercise this boundary, and the
three earlier cases retain their observations and results.

The executed source-readiness case follows the graph change through complete
dependent contexts. Before proof acceptance, its three selected goals retain
54 demanded conditions and 55 complete reasons, including 23 unresolved local
checks in 209 input contexts. This supplies the affected proof boundary for the
batch; source presence does not establish those checks. Whole-session proof
acceptance and the subsequent complete repository check discharge their own
exact contexts.

This advances one sufficient uniform proof class. Native presentation and
checking of symbolic schemes, broader uniform methods, higher strata, and the
alignment and every-line repository audits remain open. The new mathematical
proofs also retain their native proof-presentation obligation. No broader
obligation status is changed by this milestone.

## Symbolic call admission uses the actual unique interface

The next proof-scheme boundary is formation of every instance of a claim
pattern. The existing derivation checker additionally requires material truth
at each ground instance; applying it at private syntax markers would exclude
valid conditional schemes. Call formation has its own interface and can be
checked independently before the graph and its assumptions.

The existing pattern determination theorem supplies the needed distinction.
Payload markers retain each target variable's identity, while a target marker
separates variables from payload literals. Given two instances of one actual
interface, structural induction recovers a common replacement at every source
variable. Repeated uses agree by joint determination. The resulting finite
witness is exactly the existing symbolic call definition, and it is equivalent
to formation of every future root-pattern instance. This establishes a
necessary as well as sufficient criterion for this interface boundary.

One ordinary clause composes the existing reference-binding entry, two scoped
pattern instances, and two program-call admissions. Both readings use the same
actual pattern source and package. Their complete source environments may
differ. The compiled program joins the existing substitution and package
readers only after proving equality of every shared definition; their original
meanings remain available. Actual source-root, coordinate, and site classes
supply the joint presentation contract. The source-root representation is the
existing left-associated package input, while the scoped-pattern source uses
its existing site representation. These remain connected through their exact
local contracts.

Every formed finite source program is compiled once before its future claim
patterns. Arbitrary symbolic calls then have native scoped presentations with
injective private coordinates, including variable scopes and arbitrary depth.
The new checker is independently compiled once before future input values.
The original finite substitution and proof-probe investigations exercise why
the marker conditions matter and why this result concerns call formation.
The finite literal program still fails on a pair after proving both markers,
even though its variable claim has a uniform call boundary.

The five new theories leave every earlier theory and tool unchanged. Complete
native proof-scheme admission still requires graph formation, actual clause
origins, complete symbolic bindings, prospective discharges, and both material
and assertion boundaries. Native checking of the new mathematical proofs,
higher strata, and both repository audits remain open.

## Whole rule boundaries retain material assumptions and actual clause origins

The symbolic-call checker reads a standalone pattern whose binder is exactly
that pattern's variables. A complete rule can contain additional variables
only in its prospective premises or material operands. The schema's existing
binder already supplies the complete scope. The next boundary therefore uses
the entire schema and its existing determining report. It does not add another
table geometry, pattern grammar, or two-valuation implementation.

The complete schema report, symbolic-call program, and package call-list
program share actual definitions. Two shared-definition unions preserve their
old meanings. The new schema boundary entry checks both heads and every
prospective call under the same actual package. All material output rows stay
in the report. The mathematical criterion is exact at every formed valuation;
material truth is not used to classify the call boundary.

The clause specialization entry then composes three operations: actual clause
root selection, complete substitution, and the target schema boundary. The
source clause is selected by both its definition/use and clause socket. The
replacement and target schema retain independent explicit environments.
Callee coordinates in the submitted target schema are interpreted by the
supplied package. They acquire no implicit meaning from the target syntax's
source environment.

One complete replacement relation retains every prospective socket, callee,
and material operand. Evaluating it yields an admitted ordinary source-clause
instance precisely when the target material conditions hold. The existing
scheme node checks imply this local relation, and their material occurrences
keep the exact node/socket keys. The original pattern-call checker's clause
has seven premise-only variables; the existing native incidence clause has
five additional variables in its material condition. These actual subjects
rule out choosing scope from the head alone.

The joint classes reuse the existing source-root, site, and coordinate
presentations. Intrinsic subdomains impose the links, and exact admission
covers every input term and every compatible presentation. One compiled
native program precedes future inputs for both entries. At the schema
boundary, a fixed actual package also precedes all future submitted rules;
construction explicitly renames binders and sockets and preserves every old
artifact and outgoing binding.

The distinction between schema-boundary presentation and clause-specialization
presentation remains explicit. The latter must preserve the source clause's
socket identities and replacement links, so arbitrary schema compilation with
fresh socket names does not establish that coverage. The current ground case
uses the actual empty source binder. Compiling the existing finite-relation
program gives an explicit accepted clause-specialization input. Full symbolic
graph presentation still
needs shared target-variable identity across actual sites, all discharges,
and its assertion boundary.

The finite readiness investigation was executed on the six-theory source
snapshot before the final product-class theory. It retained 232 exact contexts,
six unresolved local checks, 20 demanded conditions, and 19 complete reasons.
Independent review of source hashes, closure, demand, and every reason directed
one complete dependency-session check. This is evidence about proof-source
readiness; it is not a proof of the draft semantic statements. Final acceptance
requires the complete repository session and evidence for the final sources.

The seven new theories preserve all 667 earlier theories and every tool.
Native mathematical-proof checking, broader uniform proof methods, higher
strata, and the final alignment and every-line repository audits remain open.

## Prescribed coordinates retain exact clause specializations

The existing schema compiler preserves complete rule meaning up to injective
binder and socket changes. An actual clause specialization additionally
retains the source socket coordinates. Its replacement record must use the
same explicit target-variable correspondence as the whole target schema.

Finite prescribed address maps supply the missing construction boundary.
Their prescribed part is injective and formed; the remaining finite positions
are placed outside a supplied finite set. Extending that finite assignment
to a complete injection discharges the existing native copy requirements.
The schema compiler now exposes the disjointness and carrier inclusion of
the boundary it already constructs. Its previous guarantees remain intact.
The new constructor accepts binder and socket maps as inputs and proves
pointwise agreement on that boundary. Existing literal values and external
callee targets are preserved by the existing copy and reference contracts.

The identity socket map becomes available by choosing binder coordinates
away from the source socket set. Every complete specialization of every
actual clause in a fixed encoded package then has an accepted native input.
Source-variable row keys remain literal source coordinates. The same
injective target-variable map is used in every replacement and the entire
target schema. The target environment preserves all old artifacts and
outgoing bindings.

These readings retain their separately supplied environments and uses.
The displayed variable correspondence does not identify physical positions
across unrelated uses. A complete symbolic graph still needs an actual
shared binder, complete discharges, and its assertion boundary.

The construction drafts were initially developed through source inspection.
The subsequent executed comparison confirmed their missing-coordinate
diagnosis; it did not originally discover those drafts. Its actual subjects
are the existing native incidence schema and its material-socket variant.
Their full rule-instance relations agree, and every valuation gives the
same unkeyed material operand values. Exact substitution still distinguishes
the socket coordinates.

| Selected observations | Executed residual | Consequence for this scope |
|---|---|---|
| Complete head and all unkeyed material values | Both directed cross-comparisons | These observations miss the required socket identity. |
| Those observations plus the material socket | Empty | The available socket distinction settles both comparisons. |
| Material socket alone | Empty | The two invariant observations add no distinction here. |

The last run directs the exact selection criterion: a valid selection is
complete precisely when it retains the socket facet. This finite result
does not remove any check from the general native schema reader. Its
arbitrary-schema scope still requires the complete determining report.

The owner's requested development loop is stronger than occasional checks.
Reports must direct the next proposals and revisions, and repeated reasoning
used in making those decisions should itself enter the reusable account.
The present report exposes complete observations and failed comparisons,
but selecting the next repair still requires external analysis. Executing
the existing repair-witness reasoning is a concrete remaining improvement.
The investigation evaluator is proved exported code; native checking of
its mathematical evidence, higher strata, and both final audits remain open.

## A readiness timeout directs exact reuse in the evaluator

The actual source case contains 345 conditions, 129 established contexts,
108 affected context rules, and two goals. Its exported evaluator exceeded
60 seconds. The supplied demand relation has 288 edges; the old path-bound
implementation therefore computes 287 expansions. Independent examination
of that same relation finds its first unchanged expansion at step 58, with
11,238 path pairs. The generated code also repeats forward evaluation within
individual goal tests and reevaluates the report while checking its formation.

The change exposes bounded iteration with an explicit unchanged-state stop.
Its exactness theorem holds for every update function and supplied bound.
The edge-closure code uses that theorem with its existing bound; every
mathematical definition and complete reachability guarantee is retained.
The goal residual shares a computed forward result and keeps its empty-goal
case. A second exact equation checks the whole original rule table and the
complete goal family directly, using the established equivalence with the
original guided evaluator. It does not omit unused malformed rules.

The identical input and source evidence were rerun with separately checked
code. The run completed in 18.1 seconds. Independent review checked every
source-context comparison, the complete forward closure and backward demand,
all 260 demanded conditions, all 288 reasons with their whole premise
families and qualified occurrences, and both remaining goals. This is an
execution improvement on that fixed case, not acceptance of its unresolved
theory snapshot or a universal performance bound.

A second actual run adds one unused rule with a duplicated premise occurrence
assigned two distinct conditions. It is rejected. Its demand list has a
different enumeration because the supplied atom list has additional
occurrences; the represented demand set, every complete reason, and the
residual goals are unchanged. The report contract concerns that finite set,
so list order must not be mistaken for an additional obligation.

This failure and replay extend the content-level development loop to the
machinery itself. Native mathematical-proof checking remains further work;
the available-repair operation is developed below. The host still schedules related reads,
changes, validation, and reports in batches.

## Repair reports guide the next selection and expose the language boundary

The prior loop returned failed comparisons and left the choice of the next
facet to external reasoning. That repeated step now has an explicit general
account. An available facet is sound only if it preserves every valid
comparison in the stated domain. For each missing pair, the repair relation
retains every unselected sound facet and every actual lost observation.
A distinction useful at one pair can be unsound elsewhere, so a local witness
alone is insufficient permission to add its facet.

Two different obstructions determine whether extension can succeed. A selected
loss along a valid comparison persists under every addition. A missing pair
under the whole sound available language prevents every basis in that
language. Their simultaneous absence is equivalent to the existence of an
adequate extension of the selected facets. No whole-language adequacy premise
is assumed to conceal either obstruction.

The exported evaluator computes both obstructions and the complete repair
relation. Initial executions identify a unique added facet in the completion,
socket, permission, pattern, and program-probe cases. The next executions use
those actual returned facets and settle every residual. The collapsed-marker
case instead returns an empty repair relation and two unavoidable comparisons.
Using the existing distinct marker assignment settles them in a further run;
this is a change of the observation language, beyond adding a selected facet.

Those runs reveal another repeated step: turn the witnessed repair relation
into a complete selection. Its derived extension retains the old selection
and every reported facet. A general theorem proves that this particular
extension is adequate exactly when any available extension is possible. Its
list operation is now exported, so subsequent runs use the returned extension
directly. This gives a complete candidate without ranking identifiers or
asserting that all alternative facets are jointly necessary. Smaller adequate
selections remain candidates under the existing observation-method comparison.

The finite contracts retain whole-domain comparison, every witness, and the
original input formation checks. Exhaustive execution review covers all
1,024 two-candidate, two-facet, one-witness tables, relations, and selections;
further cases check reordering, duplication, and injective identifier changes.
For each input, independent enumeration of every available extension checks
the claimed possibility criterion. These runtime checks supplement the
universal proofs; they do not supply native mathematical-proof admission.
The wider presentation, higher-stratum, and every-line audits remain open.


## Native computation witnesses complete the observation result classes

The list interface presents finite relations, so complete classes must include
every displayed order and repeated identical row. The existing sequence-image
construction supplies these classes without changing counted subjects or the
earlier distinct-member presentation convention. Datum, pair, and product
classes retain the whole facet list, table, query context, and output value.

The ordinary profile computation preserves its input order. An initial
execution on ordered, reversed, and repeated presentations of the same profile
returned four conflicts for that computation's public decision. Adding every
sound available facet retained the conflicts. Keeping only set comparison
settled the scope, but the empty selection did too. The actual outputs therefore
directed two changes: a private computation witness followed by complete set
comparison, and an expanded subject scope containing a different output.

The private-result schema is a general native construction with two actual
premise calls. Both the profile and directed-loss operations instantiate it.
The earlier computation supplies a sound total witness in the complete result
class. The comparison has an exact local contract at each such value, so general
witness completion yields every presentation of the result. Its larger global
input domain does not need to be narrowed to the particular result-row type.

Both complementary filter branches admit all supplied fields. Empty traversals
still admit their context. The loss operation shares the same whole facet and
table inputs in both profile calls. Structural agreement on the actual common
collection definitions precedes the program join. Thirteen definitions contain
nineteen ordinary clauses, and one fixed closed package covers every future
argument with exact program scope, artifacts, and bindings.

The expanded execution compares three complete presentations and a result
missing one row. The ordered observation has four persistent conflicts and
four witnessed missing comparisons. Its returned extension preserves the
conflicts. The complete-result observation alone is adequate. Empty selection
has six missing comparisons, and its returned extension is adequate. Every
reported profile, loss, repair, obstruction, and possible facet selection is
checked independently for the stated scope.

Execution of the native profile and loss equations also covers every
two-candidate, two-facet, one-value table and selection against all output
lists of length at most three, followed by reordered and repeated inputs,
multiple values, malformed octets, and formed references in unused input
fields or empty contexts. Those equations refer to the actual native calls.
All 17,764 executed decisions agree with independent expected results,
including ten formed-reference probes. These checks supplement the universal
contracts; they do not
establish native checking of the mathematical proofs or admission of the whole
investigation report. The wider development and every-line audits remain open.

## Empty table reports direct explicit native context admission

The original finite evaluation admits only observation rows within the declared
candidate and facet sets, with selected facets contained in the available set.
The native profile and loss operations have a smaller, independently useful
query boundary. Their input domains therefore remain unchanged. A separate
native predicate supplies the complete declared scope for investigation uses.

The candidate, available-facet, selected-facet, and table values use the existing
complete finite-set and product classes. Restricting that record by its original
scope conditions derives the complete admission class. Every displayed order
and repeated member remains available, and both admission outcomes are invariant
at all presentations of the same record. No new primitive or preferred
enumeration is introduced.

A contextual row traversal alone cannot validate unused context fields on an
empty table. The initial actual execution compared seven complete inputs by
their independently specified admission outcomes. It returned 12 conflicts,
12 missing distinctions, and 20 comparisons beyond its entire sound available
language. Its reported extension and the empty selection were executed again;
neither supplied an adequate basis.

Those outputs directed a general ordinary context-admission clause. Its two
premise sockets call the actual context and contextual operation definitions
in the same program. Its list specialization derives complete context admission
even when there are no element calls. Here the context definition uses the
existing data-list check for the candidates and the existing complete subset
check for the selected and available facets. The existing row traversal then
checks all table rows. Four new definitions contain five ordinary clauses, with
the least dependency closure derived from their actual callees.

The revised execution adds that complete native decision to the same seven
subjects. The row-only observation still has 12 conflicts. The report retains
12 repair witnesses; its exported extension adds the complete context
observation while preserving those conflicts. The complete
context observation alone is the only adequate selection in the stated
two-facet language. Empty selection has 20 witnessed missing distinctions; its
exported extension selects the complete observation, and its rerun is adequate.
Every profile, loss, conflict, repair, obstruction, and possible selection was
checked independently for this scope.

The native scope predicate has an exact contract on every argument term, full
data quotation, and a single fixed closed package before every future input.
Its exported equations also passed 48,930 admission decisions and ten separate
call-formation checks in 5.71 seconds. The finite execution covers all tables
on two candidates, two facets, and two witness values, every candidate/facet
scope and selection within those labels, reversals and repeated members,
invalid unused fields, and formed references in each input role. The expected
results were computed independently from data domains and finite membership.

The comparison relation, complete report, and mathematical evidence remain
separate boundaries. This scope predicate introduces no condition on a supplied
comparison relation. Native report construction and mathematical-proof checking,
the wider application audit, and the final every-line repository audit remain
open.

## Nested collection reports direct native comparison through member contracts

A complete observation profile has several displayed orders and repetitions.
A collection containing that profile therefore needs the inner reading as
well as the outer one. The existing finite-set comparison checks literal data
members. Matching counted occurrences would impose a different subject boundary.

The first executed case keeps seven nested presentations, including a result
with one observation missing. Both source profiles are results of the existing
native computation. The independent comparison takes the outer finite set of
candidate and inner-finite-set pairs. Literal outer comparison produced 18
conflicts and six missing distinctions. Its reported extension kept all 24
failures. Removing it left 12 missing distinctions and no adequate selection
in the available language.

Those outputs directed ordinary clauses for membership through a comparison
and for two complete traversals. Every displayed member has a counterpart in
the other list. Both traversals retain the element comparison's left operand;
the general construction requires no symmetry assumption. Complete membership
already supplies both data boundaries, including the empty-list cases, so the
final clause needs no further admission premise.

The element comparison retains an admitted exact key and calls the existing
finite-set comparison on its values. Six definitions contain eight ordinary
clauses over the least closure of the actual data, membership, and comparison
dependencies. The original definitions retain their complete meanings. The
independent subject is a finite set of pairs of data keys and finite data sets.
Distinct values at one key remain distinct rows; no finite-map condition is
introduced.

The datum presentation now uses a shared general data-term class. The existing
native set comparator receives a derived complete finite-set identity contract.
Product and finite-set contracts supply the whole keyed-set class, retaining
all inner and outer presentations, and a fixed native package before every
future argument. Candidate and ordered-candidate-pair observation rows consume
the same contracts. Injective encoding retains every key distinction. Literal
key retention supplies no general claim about arbitrary alternative key
presentations.

The revised case adds the complete native comparison while preserving the
subjects and independent criterion. Six repair witnesses select the new
observation; rerunning the exported extension retains the 18 conflicts from
the literal observation. The new observation alone is adequate. Empty selection
has 12 witnessed missing distinctions; its exported extension selects the new
observation, and that rerun has no residuals. Every available facet selection
and every reported observation, profile, loss, conflict, repair, obstruction,
and extension was checked independently. This Boolean reference probe has two
semantic classes in its stated scope; one such observation does not identify
all possible nested collections.

The native equations passed 364,133 comparison decisions and 10 separate
call-formation checks in 48.69 seconds. The finite cases include all 65,536
pairs of scalar row collections over two keys and two values; all 83,521 pairs
of partial function graphs from two candidate keys to subsets of four
observation values; and all 83,521 pairs from two ordered candidate-pair keys
to those subsets. Further
executions vary both presentation levels and check malformed octets, formed
references, empty collections, and distinct rows sharing a key. These graphs
supply comparison inputs; their values are not thereby certified as results
for a particular observation table.

At that stage, computing the complete tables from one declared scope,
assembling the whole native investigation report, and native checking of the
mathematical evidence remained separate obligations. The following construction
supplies the first of those links.


## Complete key scopes direct native profile and loss table calculation

The first investigation asks whether the existing native diagonal operation
can observe complete ordered-pair coverage. Its own self-pair meaning is
correct. Seven supplied outputs instead require every pair of two declared
candidates, with every order and repetition admitted and foreign pairs
excluded. The initial actual run has four conflicts and 16 missing
distinctions. Its reported extension leaves all 20 failures; the remaining
empty sound language misses 24 distinctions.

Those results direct an ordinary independently admitted pair constructor,
two existing related list maps, a context transposition, and flattening.
Admission checks both complete input lists when either is empty. The ordered
witness retains all occurrences; the public finite-set comparison admits
every presentation of exactly the Cartesian set. Eight definitions contain
ten ordinary clauses over the least closure of the actual data, list,
flattening, and comparison callees. The diagonal operation is unchanged.

The revised seven-subject case adds the actual complete Cartesian call.
Sixteen witnessed repairs select it. Rerunning that exported extension leaves
the four persistent conflicts from the diagonal observation. The new
observation alone is the only adequate selection. Empty selection yields 24
repairs; its exported extension has no residuals on the actual rerun.

A second actual investigation examines complete profile and directed-loss
tables together. Its query has three candidates, one selected available
facet, and three observation rows. Two candidates have nonempty profiles;
the third has an empty one. The independent criterion requires all three
profile keys and all nine ordered-pair loss keys, with their exact finite
values. Eight subjects include complete and sparse tables, changes of both
presentation levels, a missing empty profile, a missing self-loss row, a
foreign empty row, and a wrong nonempty loss.

The initial observation compares supplied rows with sparse references using
the actual native nested comparator. Separate proofs identify all retained
reference values as results of the native profile and loss computations.
The actual report has eight conflicts and 24 missing distinctions; its
extension leaves all 32 failures. Empty sound selection still misses 30
comparisons. Keeping only nonempty calculated rows cannot express complete
scope, even when every retained value is correct.

The new finite subjects are complete graphs over the declared candidates and
their Cartesian product. Every key receives its existing profile or loss;
functionality and empty self-loss rows follow. A general native clause retains
a selected key beside its calculated value. Its complete row-presentation
contract consumes the key and value classes for the whole enumeration.
Both table calculations use that clause and the existing list map. The
loss table first obtains its complete keys from the new Cartesian operation.

Repeated reconstruction from arbitrary list arguments is now one all-term
contract of the existing related map. Pair construction and both table
calculations use owned traversal contracts. A shared scope-witness theorem
consumes whole-input admission, the computation on every enumeration, and the
returned value's class. A binary private-result schema then compares the
whole computed witness with the supplied output through the existing nested
comparison. These clauses and contracts make recurring reasoning reusable.

The input remains the original complete scope record, with its available and
selected facets and every observation row. No dummy argument or additional
canonical-input condition is introduced. The output classes remain the
existing complete collections of candidate and ordered-pair rows. Different
values at one key remain distinct collection rows; they fail as outputs when
they disagree with the uniquely calculated graph. Every admitted inner and
outer order and repetition is retained. Literal data keys can be structured
terms; the native contract is not limited to the numeric test interface.

The program join first proves structural agreement of the actual shared
collection and flattening definitions. Existing product, scope, and keyed
groups are rebased through their whole original boundaries. Complete agreement
and generic group contracts preserve every original definition; equality of
selected meanings alone is not used to identify source definitions. The ten
new table definitions have twelve ordinary clauses and use the least closure
of their five actual external callees. All-term exactness, complete function
contracts, input and output invariance for both outcomes, full data quotation,
and one fixed package before every future argument are proved.

The revised eight-subject case adds both actual native table calculations.
Its exported extension repairs the 24 missing distinctions and retains the
eight conflicts of the sparse-reference observation. The new observation
alone is the only adequate selection. Empty selection supplies 30 repair
witnesses; its exported extension is rerun and has no residuals. Every
observation, profile, loss, residual, conflict, repair, obstruction, extension,
and available facet subset is independently checked in both investigations.
These Boolean probes settle complete admission in their finite scopes; they
do not identify every different incomplete table or pair set.

The Cartesian equations passed 115,607 native decisions and seven separate
formation checks. The table equations passed 1,896,079 native decisions and
12 formation predicates, each checking both calls. The latter matrix contains
all 1,260 formed scopes over two candidates, two facets, and two values,
crossed with all 289 partial profile graphs and all 1,156 partial loss graphs
whose self rows are empty or absent and whose cross values are arbitrary
subsets of four observations. A further 75,278 cases vary presentations,
insert different values at shared keys, add foreign empty rows, and test
every nonempty self-loss value set in an otherwise correct graph. Seventy-three
additional octet-boundary cases, 12 reference inputs, and four structured-data
decisions retain the distinction between empty data, structured keys,
missing rows, and formed references. The checked code equations refer to the
actual fixed native operations; the execution interface is not an interpreter
for arbitrary native programs. Exact source, generated-code, case, driver,
and runtime identities are recorded with these bounded results.

Complete native investigation-report construction, native repair and
extension computation, native checking of the mathematical proofs, the
remaining application audit, and the final every-line repository audit
remain open. These operations are a further component of that work.

## Observe actual problems and compose their compatible binding evidence

The owner identifies the missing structural boundary of the earlier indexed
observation adapters. A digest proves which description accompanied a run;
it does not prove that the observation function computes that description.
New observations therefore map indices to actual complete subject objects and
have an exact equation for the condition computed on those same objects.
Functional maps permit repeated identical presentations and reject an index
with different subjects. Externally supplied tables retain their conditional
meaning until a separate subject contract is established.

The application comparison uses complete schemas, ordered premise
enumerations, available calls, requested heads, and explicitly required
applications. Its candidates are the actual former and proposed operations.
The three conditions compute complete-instance and material validity,
inclusion of the former application relation, and inclusion of the required
relation. The required relation is supplied independently of the candidate
result. Its finite selection justifies proceeding on those problems; universal
preservation remains a separate proof requirement.

The complete comparison is executed before changing guided construction.
The missing required-application condition appears in both repair witnesses;
following that revision leaves no residual and makes the joined operation the
only eligible candidate. The same comparison is executed after integration.
The proposed grouping is admitted because whole recovered fragments are
compatible; partial agreement within a conflicting fragment cannot supply an
application. A pool may contain conflicting alternatives, while a mandatory
group must retain every submitted observation. Neither makes possible premise
calls true.

Complete scope is checked after joining. The schema consumer derives its
source roles from the actual original fields, reconstructs every ordinary
premise, and retains all five material predicates. Complete supporting
observations recover every value of the produced binding together. The
universal preservation theorems include both complete application sources and
the existing guided closure, with their original formation and known-evidence
requirements.

The two pattern enumerators and the two complete-premise enumerators have
unrestricted equality proofs. Their clients now share the existing operations
and exact contracts. Generic finite unions, matching formation, and complete
scope arguments are owned below those consumers. Independent host assessment
enumerates valuations and requires coverage by whole compatible fragments,
providing a check distinct from the exported compatible-union recursion.

The full 826-theory session, 50 tooling tests, and complete new and regression
execution families pass. The [retained review](https://github.com/juliusalt/structure_plus_meaning/blob/393213d603e5dc728cdb15a37c1d091c10a26417/validation/generalization-review-2026-09-11/structural-observations/README.md)
keeps the failed proposals, complete decision results, raw proof contexts,
original source objects, and execution differences. It does not establish
the missing structural boundaries of older adapters or close the whole
derivation, native mathematical-proof, and final repository audits.


## Make the fixed observation interfaces present their actual computations

The indexed interfaces are retained because they already execute the native
operations and have useful finite contracts. Their descriptions are accompanied
by functional maps to the actual objects and an exact observation equation.
Each owner supplies its complete candidate values, actual operation or condition
functions, and typed results or workloads. Its independent comparison is
stated on those same subjects. Existing native formation, truth, comparison,
and finite codec theorems supply the computational boundary.

The native expression is defined once on the complete subject. The existing
numeric entry point applies it to the mapped value. Complete-input and
complete-table predicates follow the same rule. Shared function-graph and
list-membership lemmas establish each table before specializing concrete
cases; the client proofs instantiate that content.

The exported contract comes from the checked basis definition and theorem
objects. Complete application equality prevents a specialized pattern equation
from standing in for a call with another argument. The same map expressions
occur in the functionality theorem. Full typed propositions, reachable kernel
definitions and remaining context constants accompany the execution. Candidate
and facet indices are extracted from the calculation itself. The host runtime
uses those facet indices for repairs and revision.

The independent complete-program comparison guides that runtime choice. Label
changes affect neither generator in the 98 original cases. A different facet
dictionary changes all 98 original programs, while the structural generator
preserves each complete program. Following the returned revision selects the
distinguishing observation and leaves only the structural generator eligible
under the full requirements. This bounded host result complements the subject
proofs; it does not prove their meanings or arbitrary Python semantics.

Integration follows the accepted complete source context, exact preservation
of all 98 original reports and assessments, five exporter rejection controls,
60 tooling tests, and successful replay of all ten archived stages and
investigations. The [evidence](https://github.com/juliusalt/structure_plus_meaning/blob/393213d603e5dc728cdb15a37c1d091c10a26417/validation/generalization-review-2026-09-11/indexed-subject-contracts/README.md)
retains the complete original problem, failed attempts, concrete proposals,
actual operation inputs and outputs, and their critical assessments. These
fixed subject contracts do not close native mathematical-proof checking or
the remaining whole-system audit.

The existing generated-input consumer proof now unfolds the shared complete
subject as well. Its original statement and executable definitions are
preserved. The actual failed full-session context and accepted 197-theory
dependency context supply the prospective repair comparison; the failed
receipt supplies no reused proof context. After following the returned repair,
the full 827-theory session passes with matching source, tool and log evidence.
The [delivery record](https://github.com/juliusalt/structure_plus_meaning/blob/393213d603e5dc728cdb15a37c1d091c10a26417/validation/generalization-review-2026-09-11/indexed-subject-contracts-delivery/README.md)
retains both attempts and their complete decision inputs and results.

## Complete the local child reader and replace generated retention

The local child reader is completed before the development-protocol repair,
as permitted by the owner's `problems.txt`. Its original symbolic meaning is
fixed independently. Complete claim tables, actual discharges and two jointly
determining observations provide the native comparison. Both views retain
callees; payload observations alone do not determine the complete pattern call.
The one-premise example retains its separate asserted child and supplies no
closed-proof claim.

The development choices in that milestone were recorded as external judgments
because an applicable internal condition contract was missing. The owner's
subsequent standing rule withdraws that exception. Such missing accounts remain
unmet requirements and cannot authorize continued outside reasoning, candidate
construction, criticism, or decision-making. The historical record does not
grant a current operating permission.

New validation retains repository sources, the exact source fixture, executable
recipe, required toolchain and complete report comparison boundary. A cold run
has rebuilt proof, code and all native results from that boundary. Subsequent
reconstruction instantiates this common recipe; supplied-export rechecking is
explicitly distinguished from reconstruction of proof and code.

The owner permits previous validation archives to remain recoverable from
GitHub history. Their exact committed identity is verified on remote `main`
before removing their current-tree copies. Historical links are pinned to that
commit. This authorization avoids reconstructing each obsolete historical
development environment as part of this milestone. New results use the
source-only recipe and are not attributed to the historical archive.

## Standing prohibition on outside semantics and reasoning

The owner's explicit instruction of 2026-09-12 is:

> No outside semantics or reasoning or anything else is allowed anywhere. Make this a standing rule.

It applies to the entire system and development process. All subjects,
requirements, observations, candidates, operations, evidence interpretations,
inferences, decisions, and acceptance judgments require complete RRA accounts
and Factor meaning. The rule governs implementation, validation, storage,
execution, and the internal account established during bootstrap. Earlier
ad hoc external-judgment and candidate-generation permissions are superseded.

The repository does not yet meet this requirement throughout. Missing native
representations, operations, proofs, and process integration remain defects to
repair. They supply no exception. Recording the standing rule is not a claim
that those defects have been resolved.

The owner then clarified that Isabelle's normative bootstrap role remains in
force through genesis. My withdrawal of that role was an overextension of the
standing rule and is reversed. Isabelle establishes the receiving foundation's
adequacy and transition account before the normative handoff; a receiving
system's verdict cannot create its own authority. Native operations may already
be used within an Isabelle-established scope before genesis. Whether a broader
earlier handoff can meet its complete obligations is not settled by these edits;
the existing D-9 boundary remains in force.

## Requirement construction and artifact admission

The construction request consists of the complete original goal family and
initial allocation counter, governed by the actual source definition domain.
The native checker establishes support and allocation before its computed
plan is admitted. The installed guard has the exact same-subject conjunction
meaning under the Isabelle-established bootstrap contract.

An existing interface pattern fixes the original request. The artifact reader
must recover its complete body from the actual literal artifact before applying
that request's checker. This avoids a separate supplied body or satisfaction
table. The complete program join preserves both readers' original meanings.

The closed native cause program precedes future payloads. Recorded generations
and extensions through existing predecessor uses preserve that program and
keep replay evidence separate. They establish neither a continuation policy
nor a cost bound. These are implemented parts of the structural-development
repair; the six conditions in `problems.txt` remain the milestone boundary.

The previous and new reconstruction recipes now instantiate one host runner.
Only sources, required fixtures, toolchain requirements and complete-report
comparison boundaries are retained for new reconstruction. The runner supplies
execution provenance and reproducibility, without adding semantic authority.
