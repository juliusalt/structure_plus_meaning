# Decisions and reasons

The current owner's request governs this reconstruction. Earlier generated
documents supply evidence of direction, including where they attribute words
to the owner; those attributions do not elevate their details above the current
request. Isabelle checks statements relative to definitions. Alignment of those
definitions with the intended system remains a separate review obligation.

Each choice below records its reason and its limits. Proof references are added
only after the corresponding theory is accepted.

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

## Quotation

The plan asks for determination of a quotation grammar from completeness,
recovery, no-extra structure, and fixed boundaries. These conditions must be
tested independently of a selected grammar. Uniqueness within a grammar will
not be reported as determination of the grammar.

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
views; their principality among arbitrary encodings is not assumed.

## What quotation determination requires

`RRA_Representation_Audit.recoverable_encodings_need_not_be_isomorphic`
constructs a formed addressed object with every carrier atom exposed at its
boundary. Rotating each incidence triple is reversible on all formed finite
objects. It preserves the complete carrier, every attachment, and every boundary
binding, and has exactly one output incidence per source incidence. The original
and rotated example nevertheless admit no atom isomorphism.

Thus recovery, complete material accounting, and boundary fixity do not force
primitive orientation. The reconstruction chooses quotation that preserves each
primitive incidence coordinate and each data attachment through an explicit
carrier correspondence. This strengthens the quotation boundary. It is justified
by retaining the already declared RRA primitives, and is stated separately from
the weaker conditions in the plan. `RRA_Data.bounded_copies_agree` proves that two
such copies of one bounded object are isomorphic with their boundary preserved.

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

These results do not establish general principality or admit a complete
semantic basis. In particular, total representability is not a proof that all
presentations of the same term have isomorphic complete carriers. The
presentation and candidate-form audit remains a separate obligation.

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
construction, establish general quotation principality, or implement reflection.


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

This construction supports a finite mixed list of call and material bodies under
one shared binder scope. Each body's recovered premise, interior, and slot set
is preserved. Separately, exact inverse maps show that binder and socket
renaming both preserves and reflects complete rule instances and interface
acceptance. These results do not yet constitute a general native program
constructor or settle quotation principality.


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
no initial package. Whole definition and program construction and quotation
principality remain separate obligations.

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
retention/replay boundary is addressed below. Native admission evidence, general
quotation principality, and the final alignment audit remain open.

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
attachments as well as unused carrier positions. The theorem concerns this
data profile; it does not claim general native quotation principality.

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
core. This establishes existence and unique recovery; canonical quotation up
to bounded structural isomorphism remains a separate obligation.

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
