# Reconstruction plan

## 0. Status, authority, and governing principles

### 0.1 Precedence

$$
\boxed{
\text{explicit owner statements}
\succ
\text{intent necessarily implied by them}
\succ
\text{broad RRA and Factor architecture}
\succ
\text{individual package details}
\succ
\text{previous assistant output}
}
$$

The owner's correction of 2026-09-08 supersedes all earlier single-grammar and
quotation-principality requirements, including their formulations of D-6,
O-44, O-79, and O-80. It governs every notion that needs a presentation.
Admissible presentations must preserve all required content and intrinsic
relations and introduce no unsupported facts. Their own presentation structure
is accounted for explicitly. Separate exactness results do not establish
compatibility or composition of intrinsically linked notions.

The owner also requires a general presentation theory, used both for its own
relevant notions and for the rest of the system. Its scope is determined by
evidence and may extend beyond composition. Repeated presentation work must
use justified general constructions instead of accumulating independent
definitions and proofs for each new case.

### 0.2 Status of every decision in this document

An earlier draft of this plan labelled eleven items "owner decisions" and gave
them all the highest authority. That was itself a breach of the relation above.
The owner's answers in this session were composed with LLM assistance and are
*broadly* representative of intent. The rule the owner applied to the supplied
RRA and Factor packages therefore applies to them too:

$$
\boxed{
\text{the endorsed direction is authoritative;}
\quad
\text{the generated formulation is not automatically normative}
}
$$

Every decision below carries one of four statuses, and every claim of entailment
states its reason.

| Status | Meaning |
|---|---|
| **Explicit** | text the owner wrote directly |
| **Endorsed** | a direction the owner selected; its detailed formulation is generated and remains subject to the admission test |
| **Entailed** | required by an Explicit or Endorsed commitment, with the entailment stated |
| **Open** | materially underdetermined; carried in §12, not resolved here |

This is not metadata. It is what stops a generated proposal detail from
acquiring the standing of a commitment.

### 0.3 Governing principles

**P-1 — Structural dependence.** *(Explicit: "everything needs to be explicit —
every choice, every rule, every mechanism".)*

$$
\boxed{
\begin{aligned}
&\text{every meaning-affecting choice is present in the complete RRA boundary}\\
&\text{and receives force through an explicit Factor definition;}\\[0.3em]
&\text{no semantic rule arises solely from the host representation}\\
&\text{chosen to formalize it.}
\end{aligned}
}
$$

A rule carried by RRA structure is *stated* — that is how this system is meant
to work. The failure is a rule carried by the metalevel carrier without being
represented in the object structure: a HOL set of premises introducing
extensionality and losing multiplicity, a list introducing order, an option
introducing an absent/present distinction, a datatype constructor selecting
semantics, a predicate named for completeness establishing connectivity, a
topology selecting a reduction rule whose content is elsewhere.

**P-2 — Non-conflation.** *(Explicit: "maximally disjoint — derivation is not
the same as realization is not the same as retention".)*

$$
\boxed{
\text{distinct judgments are not definitionally identified without a recovery theorem}
}
$$

A conjunction is not an identification. An alias is not an argument. Two
relations may be identified only after a theorem shows each uniquely recoverable
from the other over the complete intended domain.

**P-3 — Irredundancy.** *(Explicit, from the proposal's admission test.)*

$$
\boxed{
\text{when one judgment is uniquely derivable from another over the complete domain,}
\quad
\text{only the necessary basis remains primitive}
}
$$

P-2 and P-3 are a pair and are enforced together. P-2 alone would multiply
primitives; P-3 alone would collapse distinctions. Distinctness is preserved at
the level of *judgments*; whether a judgment is primitive or derived is settled
by P-3. Nothing in P-2 licenses a new primitive relation merely to keep two
facts apart on paper.

**P-4 — Exact presentation classes and intrinsic relations.** *(Explicit,
owner correction of 2026-09-08.)*

For each notion, state its required content, distinctions, and intrinsic
relations independently of a proposed presentation. Constrain its admissible
presentations by explicit structural criteria, then prove that every admitted
presentation preserves that content and those relations exactly. Nothing
required is lost and nothing unsupported acquires force. Presentations have
structure; the account must distinguish that structure from additional facts
about the presented notion.

Citation, binding, environment, assembly, derivation, retention, quotation,
and semantic definition are all subject to this requirement. Their intrinsic
links belong to the exactness account. Where presentations compose, prove
preservation and reflection of the linked relation over their complete shared
boundary and state the structural compatibility conditions. Individual
exactness alone supplies no composition theorem.

"Notion" is an informal word for what is being presented, not a new primitive
kind. No unique quotation topology, unique grammar, or universal isomorphism
between adequate presentations is required. Functional recovery within a
specified class and a convenient canonical witness remain useful proved
properties; neither establishes that the class is intrinsically privileged.

Develop reusable theory where recurring obligations justify it. Current
evidence includes constraints and coverage, complete products and occurrence
families, changes of presentation, intrinsic relations, shared context,
determined components, jointly determining observations, and positive
recursion. The theory must supply the hypotheses under which these constructions preserve the required distinctions.
Its own operative structures, definitions, and proof claims receive
presentations and intrinsic-link checks under the same discipline.

### 0.4 What this plan is

This plan establishes nothing. It records defects, the authority that governs
each repair, the change, and the obligation that closes it. A repair is closed
only by a proof that Isabelle has accepted.

---

## 1. What was checked, and how

Three kinds of statement are kept apart. They are not interchangeable.

| Kind | Meaning |
|---|---|
| **built** | Isabelle accepted or rejected it in this session |
| **read** | established by reading the delivered theory source |
| **reported** | taken from `problems.txt` and not independently confirmed here |

### 1.1 Built

`isabelle build -D .` was run against the delivered session with Isabelle2025-2.
It fails at `theories/Bootstrap_Relations.thy:5` with `Malformed command
syntax`.

What was established: this Isabelle installation rejects UTF-8 symbol
characters — first the cartouche delimiters `‹ ›`, and after those are replaced,
`×` and `⇒` inside type expressions — while a minimal theory written with
`\<open>…\<close>` builds successfully.

What was **not** established is where responsibility lies. An earlier draft said
the failure is "not a defect of this repository". That assigns responsibility,
and doing so presumes a declared input representation for the source, which this
repository does not declare. The defensible statement is narrower: the delivered
source has not built in the recorded environment, and a successful build under a
declared input representation is still owed.

The consequence is the fact that matters:

$$
\boxed{
\text{no successful Isabelle build of this session is on record,}
\quad
\text{here or in the reviewed archive}
}
$$

Type correctness and proof correctness of the nineteen theories are therefore
**unestablished**. This is prior to every substantive defect below, because a
defect list assumes the text is at least well-formed.

`README.md` and `THEORY_MAP.md` have been corrected to say so.

### 1.2 Read

| Defect | Location |
|---|---|
| The import graph is one total chain, `Bootstrap_Relations` → `Bootstrap_Audit` | every `imports` clause |
| `anchor_family_at`, a generic anchor utility, is defined in the trajectory theory and used by Factor meaning | `RRA_Trajectory.thy:14`, `Factor_Semantics.thy:71,117` |
| the data profile is a four-way selected primitive, with a separate formation, restriction, pushforward, and assembly component for each | `RRA_Data.thy:12,18,41,61,89`, `RRA_Assembly.thy:39–128` |
| `Node_Data` binds a triple spanning two carrier atoms | `RRA_Data.thy:12` |
| `factor_holds` is a ground Horn closure disjoined with a hard-wired SK relation | `Factor_Semantics.thy:198`, `168` |
| `clause_premises` is a set of anchors | `Factor_Semantics.thy:67` |
| `foundation_dependencies` is checked for anchor formation and used nowhere else | `Factor_Semantics.thy:98`, `152` |
| `factor_constructs` never relates assembly pieces to `construction_inputs` | `Factor_Construction.thy:42` |
| `exact_fragment` is used by no other theory | `RRA_Fragment.thy:13` |
| `fragment_boundary` records crossing incidence only, not crossing data | `RRA_Fragment.thy:28` |
| `family_has_profile` is vacuously true of every profile on an empty family | `RRA_Assembly.thy:130` |
| `function_like` compares `rra_isomorphic` on structure alone | `Factor_Construction.thy:85` |
| `factor_replays` is a literal alias for `factor_certifies` | `Factor_Evidence.thy:61` |
| `required_certificate_links` requires three links | `Factor_Evidence.thy:17` |
| `external_truth` is a supplied record field and the adequacy result is a conjunct of the definition that consumes it | `Foundation_Reflection.thy:61`, `87` |
| `resolver_non_rebinding` quantifies over one resolver | `RRA_Exact.thy:48` |
| `generation_identity` is a citation into the containing trajectory artifact | `RRA_Trajectory.thy:66` |
| `trajectory_formed` does not require predecessors to resolve to generations | `RRA_Trajectory.thy:79` |
| `factor_advances` equates the union of predecessors and dependencies with the input list | `Factor_Authority.thy:68` |
| `foundation_successor` requires only that the successor publication be formed | `Foundation_Genesis.thy:95` |
| `sk_program_complete` quantifies over terms already quoted through one finite resolver | `Foundation_Computational_Sufficiency.thy:22` |
| `rooted_complete` means root membership plus connectivity, and is used wherever "complete" and "no extra" are claimed | `RRA_Core.thy:143` |
| `quotation_geometry` is an external function pair; the transport theorem reduces to $B(x) \leftrightarrow B(x)$ | `RRA_Structural_Syntax.thy:139`, `Foundation_Reflection.thy:27` |
| `RRA_Exact.thy.tmp`, an empty file, was delivered in `theories/` | removed |

### 1.3 Not carried forward

`problems.txt` §12 concerns `check_static.sh`, `check_lines.sh`, and
`FINAL_LINE_AUDIT.md`. Those files are not in this repository. The finding that
a lexical scan cannot establish a mathematical property is carried into §11; the
specific script defects are not.

---

## 2. Decisions

**D-1 — Factor semantic core.** *(Endorsed.)*
Re-express v6.1's generic semantic-definition mechanism over RRA, simplify it
under the irredundancy constraints, and prove that it retains its genericity and
locality properties.
*Detail not normative:* which presentation forms and clause rows survive the
simplification. The clause "simplify under the irredundancy constraints" is part
of the direction, so treating v6.1's catalogue as fixed would contradict D-1
itself.

**D-2 — Exact identity and references.** *(Endorsed, amended by D-11.)*
Normative anchors are extensional exact occurrences: an exact artifact value
paired with one local occurrence address. Reference spelling is not part of
identity and never influences a semantic judgment merely by differing. External
reference profiles may supply content-derived identifiers and resolvers;
successful resolution produces an exact artifact and verifies the profile's
integrity conditions. Multiple references may identify one artifact; their
difference is provenance, not semantic identity. Internal reflective judgments
contain exact anchors and require no ambient resolver.
*Amended:* D-2 did not say how a finite retained artifact *presents* an anchor.
D-11 supplies that and supersedes the earlier draft's cross-profile resolution
theorem, which was wrong.

**D-3 — Structural transactions.** *(Endorsed.)*
Restore a semantically neutral Structural Transaction profile; do not restore
normative liveness. A selection snapshot is an exact immutable finite value with
no intrinsic currentness. $\operatorname{Transact}(H,\tau,H',r)$ is a pure
finite relation fixing exact compare, conflict, multi-locus update, and no-extra
behavior between snapshots. Trajectory remains the sole account of succession;
Factor publication and authority the sole account of recognized currentness.
Locks, compare-and-swap, databases, consensus, storage mutation, and execution
order are nonnormative realization mechanisms.

**D-4 — Generation identity.** *(Endorsed, narrowed by owner amendment.)*
Generation identity is exact generation content, independent of containment.
Trajectory artifacts, manifests, publications, and batches may select generation
identities but never contribute to them. Adding a successor creates a new
generation; no predecessor is copied, rewritten, or re-identified. Every
admissible generation presentation recovers the exact generation content under
D-6. Predecessors resolve to exact formed generations, and acyclicity is over
the predecessor relation itself.

*Amendment (owner, this session).* The principle is kept and *generation
content* is narrowed:

$$
\boxed{
G=(\ell,\ \mathit{Pred},\ \mathit{Payload},\ \mathit{Cause})
}
$$

where $\mathit{Cause}$ is an exact base-admission declaration or an exact
construction account relating the predecessors and inputs to the payload.
Evidence, proof retention, later provenance, publications, trust decisions, and
authority are separate exact artifacts *referring to* the generation and never
alter its identity.

The reason is P-2. With retained evidence inside identity, obtaining a second
proof about an existing generation forces a new generation, and evidence
accumulation becomes trajectory succession — the exact conflation P-2 forbids.
The governing test is: *could this fact legitimately be discovered or supplied
after the generation already exists?* If yes, it does not constitute identity.
Authority is excluded for a second and independent reason: publications select
generations, so an authority reference inside generation identity creates a
circular exact-identity dependency.

$$
\text{identity captures what happened}
\quad\ne\quad
\text{evidence captures why we believe it}
\quad\ne\quad
\text{authority captures who accepts it}
$$

**D-5 — Derivation, realization, replay.** *(Endorsed.)*
Three independent relations. Derivation determines proof validity independently
of retention. RRA Evidence supplies exact retained structure and citation. A
separate realization relation proves a complete, no-extra correspondence between
the abstract derivation and the retained evidence, preserving exact identity,
sharing, assumptions, and external anchors. Replay combines derivation validity,
realization, and an explicit retention boundary. No abbreviation identifies
replay with certification without a recovery theorem.

**D-6 — Exact presentations, including quotation.** *(Explicit, owner
correction of 2026-09-08.)*

The requirement is exactness of admissible presentation classes. Each notion
constrains the presentations that can represent it: every admitted member
preserves all required material, distinctions, and intrinsically linked
relations, and adds no unsupported fact or semantic rule. Presentation
structure is permitted and must be accounted for. Exactness includes the
composition of presentations of intrinsically related notions.

Quotation obeys this same discipline. Structural quotation readers and their
ordinary definitions must recover the represented content and its full
dependency boundary, with total witnesses over their stated domains and
explicit compatibility with linked readers. Multiple topologies may satisfy
these requirements. Choosing a grammar and proving uniqueness within it
establishes no intrinsic privilege for that grammar. Alternative presentations
need the exactness and composition results appropriate to their boundaries;
an arbitrary external decoder or an assumed behavioral equivalence supplies
neither.

This supersedes the former selection of one structural grammar and the
quotation-principality and universal-isomorphism obligations built on it.
Existing totality, recovery, locality, and transport theorems retain their
stated domains. Their usefulness does not depend on proving that no other
adequate presentation exists.

Use a general presentation theory to obtain these classes and their compatible
relations. Its scope follows concrete needs in this system and in the theory
itself; composition is a required part, not an exhaustive scope declaration.
The application must identify the independent subject, the structural
admission conditions, and the general construction used. A new definition
for each case is justified only when an existing construction does not
faithfully express the needed boundary.

**D-7 — Premise structure.** *(Endorsed.)*
Premises are not a set of judgments. A schema or rule instance exposes a finite
complete family of individually identified premise places, each projecting
exactly one prospective formed judgment. Distinct places stay distinct when
their projected judgments are equal. Ordering is premise structure only where
explicit RRA incidence represents it. Complete, no-extra formation accounts for
every socket. No foundation-wide contraction, exchange, or weakening principle
is inferred from the host representation.

**D-8 — Data basis.** *(Endorsed, with φ subject to the admission test.)*
Replace the four selected profiles with one general opaque-data basis:
anonymous bag attachments preserving multiplicity without occurrence identity,
and functional payload attachments to exact RRA atoms. No-data is the empty
basis. Node data becomes an addressable atom carrying a functional payload whose
ownership is ordinary RRA incidence. Legacy profiles survive as derived
conformance views. Prove faithfulness, isomorphism, K2-pushforward, and boundary
equivalence before deleting the old definitions.

*Owner ruling, this session.* Naming a two-component structure "one basis" does
not discharge P-3. The functional component $\varphi$ is subject to the
admission test: if it is faithfully representable as a bag attachment
constrained by $\sum_v \beta(u,v)\le 1$ over the complete intended domain, it
becomes a derived view and the primitive basis is $\beta$ alone. If it is not,
the plan must exhibit the exact structural case the constrained encoding cannot
preserve.

**D-9 — Internally closed predecessor-authorized amendment.** *(Endorsed.)*
Isabelle/HOL is normative only through genesis, where it proves the adequacy of
$\Phi_0$ including a general structural foundation-transition mechanism.
Thereafter a successor is legitimate only through an exact transition accepted
under its predecessor. The transition may alter any component of the successor,
including the amendment protocol itself, provided the predecessor's current
amendment semantics accepts the certificate. No successor may justify its own
adoption under rules introduced only by itself. Old foundations and judgments
retain their exact original meanings permanently. Certificates explicitly state
preservation, interpretation, migration, or intentional incompatibility.
*Detail not normative:* the earlier draft's rendering of those four as one
pairwise-disjoint, jointly exhaustive partition. D-9 says "or", not "partition",
and §6.18 corrects it.

**D-10 — Factor structural recovery.** *(Endorsed, this session. Settles the
proposal's TODO F.)*
Factor retains no primitive or independently stored $\operatorname{Own}$,
$\operatorname{End}$, $\operatorname{Next}$, or $\operatorname{Bind}$. They are
derived projections of one complete recognized Factor-structure pattern over
RRA:

$$
\boxed{
\text{RRA incidence is primitive; Factor structural relations are uniquely
recovered views of it}
}
$$

No raw coordinate of RRA incidence is identified definitionally with a Factor
relation by its tuple position. Open positions, endpoints, multiplicity,
ordering, aliasing, sharing, and binding are represented by explicit RRA
topology.

*Owner reason:* a privileged reading of a coordinate is a loss of structurality
and a hiding of semantics. *Supporting entailment:* the naive projection fails
on its own terms — an owned position may be open, so $\operatorname{Own}(a,p)$
can hold while no $x$ has $\operatorname{End}(p,x)$, and a raw triple $(a,p,x)$
cannot represent that without supplying an $x$.

During bootstrap the recognizers are **Isabelle-defined over RRA**, using only
carrier, incidence, exact identity, and bounded structure — never
`factor_holds`. The dependency is
RRA $\to$ Factor structural view $\to$ Factor definitions $\to$ Factor truth,
with no cycle. A later theorem may show a recovered relation simplifies
extensionally to a direct projection; such simplification is derived, not
foundational.

**D-11 — Citations, anchors, and the artifact environment.** *(Endorsed, this
session. Completes D-2.)*

$$
\boxed{
\text{anchors are absolute values; citations are finite relative structures}
\text{ that recover those values under an explicit exact boundary}
}
$$

An anchor remains extensionally (exact artifact value, local address). A
retained artifact does not contain that pair literally. It contains a citation:
a position in the same artifact, or an exposed environment slot together with a
local address. Semantic evaluation receives an exact finite artifact environment
$\mathcal{E}$ as part of its complete boundary, mapping slots to exact artifact
values:

$$
\llbracket \mathit{Local}(a)\rrbracket_{R,\mathcal{E}} = (R,a),
\qquad
\llbracket \mathit{External}(k,a)\rrbracket_{R,\mathcal{E}} = (\mathcal{E}(k),a)
$$

*Owner constraint:* no ambient resolutions and no non-structural notions.
Three consequences follow and are requirements, not options.

1. $\mathcal{E}$ is an explicit argument of the judgment, never ambient
   infrastructure. Two evaluations agreeing on $R,\mathcal{E},\Phi,J$ cannot
   differ because one machine resolved a token differently. Resolution is
   normative *as a finite boundary relation*; how an implementation finds the
   bytes is not.
2. $\mathcal{E}$ maps *structural slots* to *artifact values*, never reference
   tokens to artifacts. Slot keys carry boundary-local identity only. This is
   the bounded-view discipline already in `RRA_Core` applied at artifact scale —
   keys belong to the external statement of the view, do not become stored
   properties, are fixed when comparing that view, and are replaced by a
   structurally represented interface when reflected. No new primitive is
   introduced.
3. $\mathit{Local}$ and $\mathit{External}$ are names for two complete RRA
   patterns, not host constructors. A stored tag distinguishing them would be
   the exact failure P-1 forbids.

Self-reference is a local citation. A reflected foundation referring to its own
positions contains no self-hash, no self-value, and no self-identity object, so
neither recursive embedding nor circular content-addressing arises. Aliasing
resolves: two slots bound to one artifact yield one anchor, while the difference
in retrieval path remains separate provenance evidence.

The exact foundation is therefore a *package*:

$$
(\Phi_0,\ \mathcal{E}_0)
$$

a root exact artifact together with its complete finite dependency environment —
not one recursively nested artifact and not a graph of mutable references.

---

## 3. What is retained

* the minimal RRA carrier and ternary incidence, with no primitive sorts;
* exact equality distinct from structural isomorphism distinct from semantic
  equivalence;
* bounded views as external argument selections that assign no stored kind —
  now also the basis of D-11's environment;
* the internal core of `K2` and its no-unexplained-output theorem;
* generic evidence links carrying no envelope kind and no semantic force;
* currentness relative to an exact authority, publication, locus, generation,
  purpose, and foundation, with no ambient form;
* SK as an external adequacy target;
* Isabelle/HOL as the sole normative source through genesis;
* the prohibition on deriving semantic force from implementation.

---

## 4. The invariants

$$
\boxed{
\begin{array}{c}
\text{RRA completely accounts for what structure is present,}\\
\text{Factor alone determines what that structure means,}\\
\text{every dependency is present in the exact boundary,}\\
\text{and no distinction is added or collapsed without necessity.}
\end{array}
}
$$

| Principle | Repairs that instantiate it |
|---|---|
| Completeness | §6.2 footprints, §6.5 fragments, §6.14 construction provenance, §6.15 realization |
| P-1 structural dependence | §6.3 citations, §6.6 assembly, §6.11 premise sockets, §6.12 dependency audit, §6.13 quotation, §6.19 SK out of truth |
| P-2 non-conflation | §6.8 generation core, §6.15 derivation/realization/retention, §6.16 predecessor/dependency/input, §6.17 adoption/validity, §6.18 certificate relations |
| P-3 irredundancy | §6.1 data basis, §6.10 no second Factor signature, §6.11 catalogue admission, §6.14 removal of `function_like` |
| P-4 presentation exactness and intrinsic relations | Every presentation stratum; explicit compatibility and composition at each intrinsic link, including §6.13 quotation |

---

## 5. The dependency structure

An Isabelle import is a logical dependency. Two rules govern the graph:

$$
\boxed{
\begin{aligned}
&\text{no theory imports a later semantic layer;}\\
&\text{no theory imports an earlier one it does not use.}
\end{aligned}
}
$$

The second is the one that fails today. The following table, not a diagram, is
the specification. A picture with annotations beside it would put the meaning in
the annotations.

| Theory | Imports exactly | Introduces | Must not import |
|---|---|---|---|
| `Bootstrap_Relations` | `Main` | finite relation utilities | — |
| `RRA_Core` | `Bootstrap_Relations` | carrier, ternary incidence, isomorphism, bounded views, connectivity | anything Factor |
| `RRA_Data` | `RRA_Core` | the opaque data basis (D-8) | — |
| `RRA_Data_Views` | `RRA_Data` | derived legacy Bag/Functional/Node views | — |
| `RRA_Footprint` | `RRA_Data` | interior, incident star, boundary, exterior; locality | — |
| `RRA_Exact` | `RRA_Footprint` | exact artifacts, exact identity, anchors as values | any resolver |
| `RRA_Environment` | `RRA_Exact` | citations, artifact environments, interpretation (D-11) | any reference token |
| `RRA_Reference` | `RRA_Environment` | external reference profiles, retrieval, integrity verification | — |
| `RRA_Structural_Syntax` | `RRA_Environment` | record and family geometry, anchor recognition, `anchor_family_at` | `RRA_Reference` |
| `RRA_Fragment` | `RRA_Structural_Syntax` | exact selection, crossing boundary, omission | — |
| `RRA_Assembly` | `RRA_Fragment` | pieces, copied carrier, $q$, `K2` | `RRA_Evidence`, `RRA_Generation` |
| `RRA_Evidence` | `RRA_Structural_Syntax` | generic anchor/link envelopes | `RRA_Assembly`, `RRA_Generation` |
| `RRA_Generation` | `RRA_Structural_Syntax` | generation core, predecessors, acyclicity (D-4) | `RRA_Evidence`, `RRA_Assembly` |
| `RRA_Selection` | `RRA_Generation` | selection snapshots | — |
| `RRA_Publication` | `RRA_Selection` | publications with dependency and evidence selections | — |
| `RRA_Transaction` | `RRA_Selection` | `Transact`, compare, conflict, multi-locus update (D-3) | `RRA_Publication` |
| `Factor_Structure` | `RRA_Structural_Syntax` | the recognized Factor-structure pattern and its projections (D-10) | `RRA_Evidence`, `RRA_Assembly`, `RRA_Generation` |
| `Factor_Quotation` | `Factor_Structure` | structural quotation classes, exact recovery and linked presentation boundaries (D-6) | anything semantic |
| `Factor_Presentation` | `Factor_Quotation` | candidate definition presentations (D-1) | — |
| `Factor_Application` | `Factor_Presentation` | formation, application boundary, target | — |
| `Factor_Dependency` | `Factor_Application` | the finite meaning-dependency audit | — |
| `Factor_Meaning` | `Factor_Dependency` | $\Phi\models J$ | `RRA_Evidence`, `RRA_Generation`, `RRA_Assembly`, any SK |
| `Factor_Schema` | `Factor_Meaning` | parametric rules, premise sockets, admissibility (D-7) | — |
| `Factor_Derivation` | `Factor_Schema` | finite derivations, soundness | `Factor_Construction`, `RRA_Evidence` |
| `Factor_Construction` | `Factor_Meaning`, `RRA_Fragment`, `RRA_Assembly` | the provenance chain, `K2` join | `Factor_Derivation`, `RRA_Evidence` |
| `Factor_SK` | `Factor_Construction`, `Factor_Derivation` | SK as a Factor program | `Factor_Amendment`, any `Foundation_*` |
| `Factor_Computational_Sufficiency` | `Factor_SK` | representation, one-step and multi-step adequacy, universality | any `Foundation_*` |
| `Factor_Realization` | `Factor_Derivation`, `RRA_Evidence` | the realization correspondence (D-5) | — |
| `Factor_Replay` | `Factor_Realization`, `RRA_Publication` | generic replay: derivation, realization, retention (D-5) | `Factor_Construction` |
| `Factor_Certified_Construction` | `Factor_Replay`, `Factor_Construction` | replay joined to a construction judgment; the construction-specific certificate projection | — |
| `Factor_Cause` | `Factor_Construction`, `RRA_Generation` | validity of a recorded cause: that it accounts for the payload | `RRA_Evidence` |
| `Factor_Authority` | `Factor_Meaning`, `RRA_Publication` | raw adoption, publication-relative currentness | `RRA_Evidence`, `Factor_Derivation` |
| `Factor_Continuation` | `Factor_Cause`, `RRA_Transaction` | `Advance`, with structural transition and certified continuation kept apart | `RRA_Evidence` |
| `Factor_Amendment` | `Factor_Certified_Construction`, `Factor_Authority`, `Factor_Continuation`, `Factor_Dependency` | transition certificates, acceptance (D-9) | any `Foundation_*` |
| `Foundation_Bootstrap_Judgments` | the theories whose judgments it states | the HOL-side public relations, stratum by stratum | any reflected representation |
| `Foundation_Quotation` | `Factor_Quotation`, the theories whose families are quoted | concrete quotation of each judgment family | — |
| `Foundation_Reflection` | `Foundation_Quotation`, `Foundation_Bootstrap_Judgments`, `Factor_Meaning` | stratified adequacy | — |
| `Foundation_Genesis` | `Foundation_Reflection`, `Factor_Computational_Sufficiency`, `Factor_Amendment` | concrete $(\Phi_0,\mathcal{E}_0)$, complete genesis | — |
| `Bootstrap_Audit` | `Foundation_Genesis` | exposed boundaries | — |

Nine separations are the point of the table.

1. **Assembly, Evidence, and Generation are siblings** over structural syntax.
   None uses a concept of another.
2. **Factor structure and meaning sit over structural syntax alone.** They reach
   neither evidence, nor trajectory, nor derivation. "Meaning precedes evidence"
   becomes a fact about imports.
3. **Construction and Derivation are siblings** over meaning; neither imports the
   other.
4. **Quotation is split.** `Factor_Quotation` is the general grammar and is
   needed by SK adequacy, which quantifies over quoted terms; the earlier draft
   placed the whole of quotation after computational sufficiency, which was
   circular. `Foundation_Quotation` is the concrete quotation of bootstrap
   judgment families and precedes reflection.
5. **SK adequacy branches from construction and derivation, not from amendment.**
   The earlier draft placed `Factor_SK` under `Factor_Amendment`, which made
   computational adequacy depend on foundation succession for no reason.
6. **`RRA_Reference` is a leaf.** External reference profiles are imported by
   nothing that makes a semantic judgment. Under D-11 they build and verify an
   environment; they do not enter one.
7. **Amendment is below genesis.** Under D-9 the mechanism is a component of
   $\Phi_0$ whose adequacy Isabelle proves, so it cannot be introduced after the
   foundation it governs.
8. **Generic replay does not reach construction.** A proof about equality or
   formation has no program inputs and no assembly. `Factor_Replay` is therefore
   forbidden from importing `Factor_Construction`, and the construction-specific
   certificate lives one level up in `Factor_Certified_Construction`.
9. **Cause validity has a home.** `RRA_Generation` records a cause and cannot
   validate it, since it may not import Assembly. `Factor_Cause` is where the
   recorded cause is proved to account for the payload, and `Factor_Continuation`
   reaches construction only through it.

The number of theories is a granularity judgment. The separations are forced.
Whether `Factor_Quotation` and `Factor_Presentation` are one relation or two is
itself a P-3 question, since a definition's RRA representation and the grammar
that recognizes it may be one thing; §12 carries it.

---

## 6. Repairs, in dependency order

### 6.1 The opaque data basis — `RRA_Data`, `RRA_Data_Views`

**Defect.** `rra_data` (`RRA_Data.thy:12`) is a four-way datatype with a
four-way selector (`:18`), a per-profile formation clause (`:41`), restriction
(`:61`), pushforward (`:89`), and assembly component
(`RRA_Assembly.thy:39–128`). `family_has_profile` (`:130`) is vacuously true of
every profile on an empty family. `Node_Data` binds a triple spanning two
carrier atoms, so a data item can straddle a fragment selection while
`fragment_boundary` records only crossing incidence.

**Warrant.** **D-8**, under **P-3**. *Not* P-1: an explicit profile field is not
a hidden rule, and the earlier draft's appeal to P-1 here was a misapplication.
The question is whether four profiles are mutually irreducible and necessary —
an admission test, not a philosophical objection to selectors.

**Change.** One basis over the carrier:

$$
D=(\beta,\varphi),
\qquad
\beta:U\times\mathrm{Octets}^{\ast}\rightharpoonup\mathbb{N}_{>0},
\qquad
\varphi:U\rightharpoonup\mathrm{Octets}^{\ast}
$$

with $\varphi$ subject to the admission test per the owner's ruling: if
faithfully representable as $\beta$ constrained by $\sum_v\beta(u,v)\le 1$, it is
a derived view and $\beta$ alone is primitive. No-data is the empty basis.
Legacy node data $D(d)=(u,v)$ becomes the addressable atom $d$ with payload $v$
and ownership $d\mapsto u$ as ordinary RRA incidence.

The structural consequence is why the change is worth making:

$$
\boxed{
\text{every data item attaches to exactly one carrier atom;}
\quad
\text{all multi-atom structure is incidence}
}
$$

Two delivered defects dissolve rather than being patched. Restriction drops a
data item exactly when its one carrier atom is unselected, so no data item can
cross a selection boundary. And an empty piece family determines the empty basis
and nothing else.

**Migration is a translation, not an identity.** The earlier draft read D-8's
"exact-identity equivalence" as literal equality across the migration. That is
impossible: encoding node ownership as incidence *changes the incidence*, so a
legacy node object and its translation are not the same exact artifact. The
correct obligation is faithfulness — $\mathit{Decode}(\mathit{Encode}(O))=O$
together with a boundary-preserving correspondence — with exact identity defined
*within* each basis.

Legacy views live in `RRA_Data_Views`, imported by no normative theory.

**Obligations.**
**O-1** every data item of a formed basis attaches to exactly one carrier atom.
**O-2** exact identity within the basis is equality of carrier, incidence, and basis.
**O-3** faithfulness: $\mathit{Decode}\circ\mathit{Encode}=\mathrm{id}$ on legacy objects, with a boundary-preserving correspondence.
**O-4** data-preserving isomorphism over the basis, agreeing with the legacy condition on every object with a legacy view.
**O-5** a total finite compatibility check on candidate gluings, together with a uniquely determined pushforward on the compatible domain — $\beta$ summing multiplicities over the fibre, $\varphi$ single-valued — including on the empty family. An earlier draft asked one pushforward to be both total on all candidate gluings and undefined where functional values conflict, which is not satisfiable.
**O-6** boundary equivalence: every legacy crossing-data case corresponds to a crossing incidence.
**O-7** the P-3 verdict on $\varphi$, as a commuting square rather than a
statement about values:

$$
\operatorname{Encode}(q_{\ast}D)
\ \cong\
\widehat{q}_{\ast}\operatorname{Encode}(D)
$$

with the translated witness $\widehat q$ defined, and with preservation *and
reflection* of whether the assembly is formed.

**The naive encoding already fails, and the counterexample is a result, not a
worry.** It was checked against the delivered definitions: `expected_bag`
(`RRA_Assembly.thy:119`) sums multiplicities over the $q$-fibre, while
`expected_functional` (`:105`) is a set image and therefore merges equal
payloads idempotently. Take two pieces with equal payloads,
$\varphi_1(x)=v$ and $\varphi_2(y)=v$, glued by
$q(s_1,x)=q(s_2,y)=z$. The functional assembly is valid with
$\varphi_Q(z)=v$. Encoding each binding at multiplicity one gives
$\beta_1(x,v)=1$, $\beta_2(y,v)=1$, and the bag pushforward yields
$\beta_Q(z,v)=2$, so $\sum_w \beta_Q(z,w)=2>1$ and the result has left the
constrained-bag domain.

$$
\boxed{
\text{representable as a restricted bag value}
\ \ne\
\text{reducible to bag attachment with the same assembly behavior}
}
$$

This settles that multiplicity-one encoding does not commute with the specified
pushforward. It does **not** settle that two primitive attachment channels are
necessary: another structural encoding, or a derived view with explicitly
represented transport conditions, may still work. What it forbids is closing the
question by silently replacing bag summation with idempotent merging.

### 6.2 Footprints — `RRA_Footprint` (new)

**Defect.** `rooted_complete` (`RRA_Core.thy:143`) means root membership plus
connectivity, and stands wherever completeness or no-extra structure is claimed.

**Warrant.** Completeness invariant; **P-1**.

**Change.** A footprint is **relative**, not globally closed. The earlier draft
required that "no other position, incidence, or data item occurs", which read
absolutely would forbid embedding a recognized structure in a larger artifact
and destroy sharing and reuse — the very things assembly exists for. The
condition is:

$$
\boxed{
\text{no unaccounted incidence or data may touch the footprint's interior}
}
$$

A footprint distinguishes five things: interior; exact incident star; explicit
boundary crossings; fixed external endpoints; unconstrained exterior. The
locality theorem is that changes wholly outside the closure affect neither
recognition nor judgment. `rooted_complete` survives only under a name that says
connectivity.

**Obligations.**
**O-8** footprint completeness and no-extra, relative to the interior and its star.
**O-9** locality: agreement on the closure implies agreement on recognition and on every judgment over it.

### 6.3 Citations, anchors, environments — `RRA_Exact`, `RRA_Environment`, `RRA_Reference`

**Defect.** `resolver_non_rebinding` (`RRA_Exact.thy:48`) proves single-valuedness
within one supplied $\rho$; under two resolvers one reference may denote
different artifacts, and two references to one artifact are unequal anchors.
Nearly every predicate carries $\rho$.

**Warrant.** **D-2** as completed by **D-11**.

**Change.** Anchors become extensional values; `artifact_resolver` leaves every
normative signature. Citations become the two RRA patterns of D-11, interpreted
against an exact finite environment supplied as part of the judgment's complete
boundary. Whole-artifact and occurrence citation forms are both retained pending
the P-3 test of §12.

The earlier draft's replacement theorem —
$\operatorname{resolve}_{\pi}(i)=R \wedge \operatorname{resolve}_{\pi'}(i)=R'
\Rightarrow R=R'$ for all admissible profiles — was **wrong** and is withdrawn.
One raw identifier may legitimately inhabit different profile namespaces; an
exact reference contains the profile, $(\pi,i)$. Under D-11 the theorem is not
needed in that form: reference profiles are pre-semantic, and what must be
functional is citation interpretation given $(R,\mathcal{E})$.

**Obligations.**
**O-10** no normative judgment takes a resolver argument.
**O-11** citation interpretation is functional given the artifact and environment.
**O-12** local self-citation: $\llbracket \mathit{Local}(a)\rrbracket_{R,\mathcal{E}}=(R,a)$, with no self-hash, self-value, or self-identity object anywhere in $R$.
**O-13** alias invariance: $\mathcal{E}(k_1)=\mathcal{E}(k_2)$ implies the citations agree.
**O-14** environment locality: agreement of $\mathcal{E}$ on the dependency closure of $R$ implies identical citation interpretation and identical semantic judgments.
**O-15** slot-key renaming invariance, per the bounded-view discipline.
**O-16** environment closure $\mathit{EnvClosed}(\mathcal{E},R)$: every reachable external slot is assigned exactly one artifact, recursively, with no omitted and no unrelated dependency.
**O-17** $\mathit{Local}$ and $\mathit{External}$ are recognized RRA patterns, not stored tags.

**The composition boundary.** D-11 fixes what a citation denotes under one
environment. It does not yet say how environments compose, and three
consequences must be discharged before the definitions above can be used
together. An earlier disposition called D-11 "resolved"; it resolves the
*direction* of the anchor problem, not its composition.

*Structural occurrence is not closed semantic use.* One artifact $R$ containing
$\mathit{External}(k,a)$ is the same exact artifact under $\mathcal{E}_1(k)=A$
and $\mathcal{E}_2(k)=B$, while the citation denotes different anchors. That is
not a defect — it is the structure/semantics separation working — but it forbids
an inference:

$$
\boxed{
\text{same presenting artifact and citation}
\ \not\Rightarrow\
\text{same closed semantic use}
}
$$

The same discipline applies to imported definitions, program applications,
retained derivations, and any generation whose fields contain citations.

*Slots follow the assembly discipline.* Two independently formed packages may
expose slots whose spellings coincide without identifying the slots, and one
artifact reused twice under different bindings must not accidentally share one
environment merely because its value is equal. This is the rule assembly already
states for pieces — independent boundary occurrences stay distinct until an
explicit correspondence identifies them — applied at the environment boundary.
It introduces no namespace primitive.

*The foundation is fixed; arguments are not.* $\mathcal{E}_0$ fixes the
foundation's dependencies. It must not become a finite universe from which every
future argument is drawn, or the archive's finite-ground limitation returns
through the environment instead of through the clause set:

$$
\boxed{
\text{the foundation is fixed;}
\quad
\text{formed finite argument packages remain unbounded in variety}
}
$$

Since D-11 makes $\mathcal{E}$ a per-judgment boundary argument, an application
carries its own closed environment and the composition rule above governs how it
meets the foundation's. A single flat environment would fail the repeated-reuse
case, so the composition rule determines the representation.

**O-74** exact anchor equality does not imply equality of environment-dependent semantic use unless the relevant bindings agree; the converse non-inference is stated and proved, not assumed.
**O-75** environment composition: combining packages preserves or explicitly transports citation interpretation — fixed external anchors stay fixed, copied local occurrences follow the declared assembly correspondence, unrelated slot namespaces do not collide, explicitly identified interfaces agree on their bindings, and one artifact used twice under different bindings keeps two distinct environments.
**O-76** conservative extension: a formed application may supply arguments outside $\mathcal{E}_0$, and doing so changes no judgment that does not depend on them.

### 6.4 Structural syntax — `RRA_Structural_Syntax`

**Defect.** `anchor_family_at` is defined in `RRA_Trajectory.thy:14` and used by
Factor meaning. Anchor recognition goes through `functional_payload` (`:97`);
`field_code` (`:19`) assigns field position by incidence-chain length.

**Warrant.** §5's second rule for the misplaced utility; **D-6** for the rest.

**Change.** Move `anchor_family_at` here. State the admitted record, family,
and citation patterns and prove exact recognition over their full boundaries.
Their field order and data roles are presentation structure with explicit
readers. No proof of intrinsic uniqueness of those patterns is required.
Their links to targets, bindings, environments, and higher presented notions
must satisfy the common exactness and composition obligations.

**Obligation.** **O-18** anchor recognition is structural, functional, complete,
and no-extra over its declared admissible class, with explicit target and
environment dependencies and no unstated encoding convention.

### 6.5 Fragments — `RRA_Fragment`

**Defect.** `fragment_boundary` (`:28`) records crossing incidence only; under
the legacy node profile a data tuple can cross unrecorded.

**Warrant.** Completeness invariant.

**Change.** Under D-8 the defect has no instance. The repair is to *prove* the
boundary complete — a theorem about the basis — and to state omission and
remainder for data as for the carrier.

**Obligation.** **O-19** source, selected material, crossing incidence, and
omitted remainder including data are simultaneously recoverable from one
fragment witness, and no data item crosses.

### 6.6 Assembly — `RRA_Assembly`

**Defect.** `family_has_profile` is vacuous on an empty family.

**Warrant.** **D-8**; sufficiency.

**Change.** No profile to select. `family_has_profile`, `assembled_data`, and
the per-profile copied and expected components collapse into one pushforward.
The rule that gluing may not produce a multi-valued functional component becomes
a formation condition rather than a downstream check. `K2` is otherwise retained;
its defect is at the Factor join.

**Obligation.** **O-20** the output basis is determined by the witness for every
piece family, including the empty one.

### 6.7 Evidence — `RRA_Evidence`

**Defect.** Imports `RRA_Assembly`, uses no assembly concept.

**Change.** Import `RRA_Structural_Syntax`. Envelope definitions unchanged.

### 6.8 Generations — `RRA_Generation` (new)

**Defect.** `generation_identity` (`RRA_Trajectory.thy:66`) cites into the
containing trajectory artifact, so a copied generation is re-identified and an
unreplaced trajectory cannot hold later generations. `trajectory_formed` (`:79`)
admits any anchor as a predecessor.

**Warrant.** **D-4** as amended.

**Change.** The generation core is $(\ell,\mathit{Pred},\mathit{Payload},
\mathit{Cause})$ and its identity is that exact content. Evidence, publication,
authority, and trust become separate relations *about* a generation:

$$
\mathit{EvidenceFor}(E,G),
\quad
\mathit{Certifies}_{\Phi}(E,G,J),
\quad
\mathit{Adopts}_{\Phi}(A,G),
\quad
\mathit{Published}(P,G)
$$

Predecessors resolve to exact formed generations. Acyclicity is over the
predecessor relation.

Including $\mathit{Cause}$ does not conflate assembly origin with trajectory
succession — they remain distinct relations with distinct boundaries; the
generation record cites one. Whether two constructions reaching one payload are
two historical events follows from what the construction judgment's boundary
contains, and is settled in §12 rather than asserted here; an earlier draft
asserted it unconditionally while simultaneously listing it as undecided.

**Two things the theory must keep apart.**

*Presenting artifact versus resolved core.* If a generation representation
contains an external predecessor citation, the same representation under two
environments selects different predecessors — and $\mathit{Pred}$ is
identity-bearing. So the exact artifact presenting a generation is not the exact
generation core, and changing a relevant binding changes the core while the
presenting artifact is unchanged. Changing an unrelated binding must change
neither. This is where D-4 and D-11 meet, and neither states it alone.

*Recording a cause versus the cause being valid.* `RRA_Generation` cannot import
Assembly, so generation formation records and structurally recognizes the cause
reference and nothing more. It does not establish that the cause is a valid `K2`
witness, uses admissible pieces, constructs the stated payload, or satisfies a
Factor application. Those are later judgments and need a stated location:

$$
\text{a formed generation records this cause}
\quad\ne\quad
\text{this cause validly accounts for the payload}
$$

**Obligations.**
**O-21** every formed generation core has an admitted presentation and each admitted presentation recovers exactly one core, including its exact locus, predecessor relation, payload, and recorded cause. The intrinsic links to predecessor resolution, cause recording, and the relevant retained environment are preserved and reflected. Different adequate presentations need not be isomorphic. Any canonical construction or transport theorem states its own class and boundary; it establishes no exclusive presentation choice.
**O-22** every predecessor resolves to an exact formed generation.
**O-23** acyclicity over the predecessor relation, on the retained boundary.
**O-24** identity is invariant under every change to a containing or selecting artifact.
**O-25** noninterference: $\mathit{EvidenceFor}(E,G)$, adoption, and publication may all change while $G$ remains the same exact generation.
**O-26** no circular exact-identity dependency between generations, publications, and authorities.
**O-77** the resolved generation core is a function of the presenting artifact *and* the environment restricted to its dependency closure; unrelated bindings change neither the artifact nor the core.
**O-78** cause validity is a separate judgment from cause recording, proved where construction is available (§6.10a), and generation formation claims only the latter.

### 6.9 Selections, publications, transactions

**Warrant.** **D-3**, **D-4**.

**Change.** A trajectory is a *view* selecting generation identities. A snapshot
is an exact immutable value with no intrinsic currentness. A publication is a
snapshot with exact dependency and evidence selections. `Transact` is a pure
finite relation between snapshots.

**Obligations.**
**O-27** `Transact` has no valid partial-success result.
**O-28** the conflict case returns the complete observed comparison boundary.
**O-29** no snapshot, publication, or transaction predicate asserts currentness.

### 6.10 Factor structure over RRA — `Factor_Structure` (new)

**Defect.** No faithful projection from RRA to the Factor primitive signature
exists; `Factor_Semantics` works directly on anchor records.

**Warrant.** **D-10**.

**Change.** One recognition relation $\mathit{FactorStructure}(S,F)$ holding
exactly when $S$ contains the RRA topology exposing the four structural
relations with all occurrences, multiplicity, sharing, order, open positions,
and boundary incidence accounted for. $F$ is not a stored graph; its components
are the unique projections of that recognized structure. There are no
independent Factor tables:

$$
\text{RRA structure}\ \longrightarrow\ \text{unique Factor structural view}
\qquad\text{rather than}\qquad
\text{RRA structure} + \text{Factor structure}
$$

Recognition is Isabelle-defined over RRA and never mentions `factor_holds`.

**The bridge theorem, and its limit.** This is what turns D-1's "re-express over
RRA" from a claim into a result. For every valid v6.1 finite structural model
$G=(U,\mathit{Own},\mathit{End},\mathit{Next},\mathit{Bind})$ construct
$\mathit{Encode}_F(G)=S$ and prove $\mathit{FactorStructure}(S,F)$ with each
projection equal to its source relation, and prove that encoded structures decode
uniquely back.

The limit matters as much as the theorem. It says *the retained v6.1 structures
are faithfully representable as one supported class of RRA structures*. It does
**not** say the integrated foundation is correct only if its structural domain
and restrictions coincide with v6.1's. An earlier draft required that every
formed canonical representation decode to a v6.1 model, which would have made an
LLM-produced package's incidental restrictions normative for the new foundation
— the exact standing §0.2 denies it. Transport of complete structural matching
is proved on the supported class:

$$
\mathit{ExactMatch}_{\text{v6.1}}(K,\eta)
\iff
\mathit{ExactMatch}_{\mathrm{RRA}}(\mathit{Encode}(K),\mathit{Encode}(\eta))
$$

**Obligations.**
**O-30** recognition is functional up to permitted internal renaming; disagreement between complete matches makes the structure unformed.
**O-31** complete rejection of malformed or multiply-interpreted structures.
**O-32** preservation and reflection of multiplicity, identity, aliasing, sharing, order, open positions, and boundary incidence.
**O-33** renaming invariance; no nominal discriminator; no duplicated authoritative fact.
**O-34** the encode/decode and `ExactMatch` transport theorems above, stated over the supported class and not as a bijection with the whole formed domain.

### 6.11 Presentation, application, meaning

**Defect.** `factor_holds` (`Factor_Semantics.thy:198`) is a finite ground Horn
closure disjoined with a hard-wired SK relation: no binders, variables,
substitution, application schemas, quantified rules, local matching, or
definition-specific formation boundaries. A generic identity program cannot be
defined without pre-listing every instance. `clause_premises` as a set licenses
contraction, exchange, and monotone accumulation.

**Warrant.** **D-1**, **D-7**, **P-1**.

**Change.** Recover the *capabilities* v6.1 evidences, then admit only the
structurally necessary basis. The earlier draft listed exactly three presentation
shapes and exactly eight clause rows as the change; those are generated details
of an LLM-produced package, and D-1's own clause "simplify under the
irredundancy constraints" forbids treating them as fixed.

Required capabilities, which *are* authoritative evidence of intent:

* semantic definitions are structurally selected, never nominally dispatched;
* applications have complete boundaries with no truth, proof, or implementation
  footprint;
* definitions are generic over unboundedly many future arguments;
* meaning dependencies are explicit;
* proof does not determine meaning.

v6.1's view/extensional/closure presentations, its eight-row clause table, and
its `Wrap`/`Branch` topologies enter as **candidate decompositions**. Each is put
to five questions: is it required to distinguish an intended meaning; is it
derivable from another admitted form; is its formation boundary sufficient; does
its topology introduce an unintended rule; can generic future applications be
expressed without it and without a nominal dispatcher.

Premises become D-7's sockets: distinct RRA occurrences, each exposing one
prospective premise. Multiplicity comes from occurrence identity; order only
from explicit incidence. No host collection carries a structural rule.

**Obligations.**
**O-35** functional recovery of a presentation from its RRA structure.
**O-36** complete rejection of malformed representations.
**O-37** renaming invariance and dependency locality.
**O-38** genericity: one definition determines judgments over unboundedly many future formed arguments.
**O-39** no foundation-wide contraction, exchange, or weakening derivable from the representation.
**O-40** the admission verdict for every candidate form, with its reason.

### 6.12 The dependency audit — `Factor_Dependency` (new)

**Defect.** `foundation_dependencies` (`Factor_Semantics.thy:98`) is checked for
anchor formation and used by nothing.

**Warrant.** **P-3**; **D-1**.

**Change.** Re-express v6.1's finite audit: root carrier, structural definition
occurrence, occurrence carrier, audit carrier; the edge $x\to y$ added exactly
when the formation or truth clause of $x$ invokes that of $y$; agreement of all
clauses projecting one occurrence; no graph scan, key lookup, registry, or
ambient relation set selecting a target.

This theory carries §6.18: D-9's non-self-justification condition is a statement
about a dependency boundary, and nothing else in the system can state it.

The same admission discipline as §6.11 applies here. v6.1's audit machinery is
detail from the same generated package; each component enters as a candidate and
must earn admission. §6.11 applied this to presentation forms and the earlier
draft did not apply it here, which was an inconsistency in the plan rather than a
considered exception.

**Obligations.**
**O-41** the dependency boundary is finite, explicit, and a formation precondition of meaning.
**O-42** direct circularity letting a definition select its own truth is unformed, outside one separately defined well-founded or monotone construction.
**O-83** the admission verdict for every imported audit component, with its reason.

### 6.13 General presentation theory and quotation — `Presentation_Classes`, `Presentation_Relations`, `Presentation_Closure`, `Factor_Presentation_Classes`

**Defect.** The archived `quotation_geometry` was an external function pair,
and its purported transport theorem reduced to $B(x)\leftrightarrow B(x)$.
The previous plan also required one intrinsically determined quotation
grammar. The owner has superseded that requirement: restricting the considered
grammars and proving uniqueness among them is not the desired result.

**Warrant.** **P-4** and the amended **D-6** apply throughout the system.

**Change.** Develop a reusable presentation theory, with its scope justified
by the system's actual requirements. Use its constructions for the theory's
own relevant notions and throughout the system. State required content and
intrinsic relations independently, constrain the admissible presentations,
and prove exactness for every admitted member. Concrete quotation grammars
and compilers instantiate this theory under the same discipline as citations,
bindings, environments, assemblies, derivations, retention boundaries, and
semantic definitions.

The current scope has the following evidence and proof boundaries:

| Recurring requirement | General result needed |
|---|---|
| Complete values admit different enumerations and physical copies | Coverage, admissibility, unique recovery of the entire subject, compatible alternatives, and changes of presentation. Recovery alone does not establish a material account or intrinsic-link exactness. |
| Records, lists, premise families, and tables combine components | Products, complete sequences, and finite collections with explicit roles, positions, multiplicity, and distinctness conditions appropriate to the subject. |
| A package or derivation uses a common environment, scope, or occurrence | Constrained and joint classes with soundness for every retained presentation and jointly available witnesses for every required subject. |
| A complete environment and site determine a native program | A derived-component rule based on the independently proved functional link, retaining both judgments without storing a duplicate program value. |
| Semantic observations must survive changes of presentation | Preservation and reflection of the independently stated predicates and relations, with explicit shared arguments and intermediate domains. |
| Definitions and readers may be positively recursive | Exact consequence transport on a proved closed support domain before taking least fixed points. |
| Complete finite syntax is determined by several readings together | Observation classes derived from a complete presented record and an observation map proved injective on the required subject domain. Every conclusion, call occurrence, callee, and material operand remains present. |
| The presentation theory has operative definitions and rules of its own | Ordinary native schemas and programs, exact presentations of their scopes and complete schema reports, native checks against fixed reference data, and applications of those readers to every compatible presentation of their own clauses. |

Jointly determining observations now supply exact schema reports through
these general constructions. The report retains one complete binder and
two complete output records, including every call occurrence and all five
operands of each material premise. An ordinary reader compares the report
with the actual schema at its source site. A further reader checks the
whole variable interface and singleton clause family of a definition.
The compatible source/report classes are derived by constraining the generic
pair class with the independently proved native relation. Their joint
coverage is explicit. An expected report can be stored as literal data in
ordinary checking code before future submitted definitions.

For the reading-composition rule, native admission recovers the complete
expected clause, its variable interface, and its actual callees. In a formed
package, the admitted definition has exactly the two-call meaning on the
same returned body. The schema reader also checks compatible reports of all
of its own compiled clauses. These are finite syntax contracts with proved
semantic consequences. Full native presentations and checks of the remaining
mathematical contracts and proof records stay within O-85.

These results are justified by existing collection, table, quotation, scope,
and program machinery. Their proof parameters are typed relations, not a
universal datatype of notions. An arbitrary mathematical relation is not
thereby a native definition. Operative admission and composition use actual
ordinary callees whose contracts have been proved. The scope remains open to
further justified needs; a speculative catalogue of operators supplies no
additional obligation or semantic primitive.

The proof must account for every required field, distinction, dependency, and
occurrence. It must also show that presentation structure introduces no
unsupported fact or rule of the presented notion. Structural order or sharing
may be meaningful, or may serve a stated representation role; neither is
silently inferred from the host formalization. A clause declaring an encoding
"exact" is not evidence of exactness.

For every intrinsic relation, give the corresponding structural compatibility
conditions and prove preservation and reflection of the relation through the
linked presentations. A citation must reach the same exact target through its
binding and environment; a presented derivation must use the recovered rule,
premise occurrences, and retained interpretation; a stored program scope must
determine the actual definitions and meaning of calls in that scope. These
are joint obligations, not consequences of separate recovery theorems alone.

Require total representability over each independently stated domain and
constructed witnesses wherever inhabitance is claimed. A constraint may have
no valid subjects; that empty case cannot establish adequacy for a larger
inhabited domain. Totality forces an admissible presentation for every required
subject while allowing several topologies. Functional recovery, a canonical
constructor, or uniqueness of a root within one complete profile does not
require every presentation of the notion to have the same topology. Claimed
independence, renaming, or transport properties are proved only with their
actual boundaries.

The general term and definition classes support computation and program
formation. Concrete presentations of bootstrap judgments and their intrinsic
links precede the corresponding reflection strata. No generic metalevel
datatype of "notions" is added.

**Obligations.**
**O-43** each structural reader admits exactly its declared presentation class, recovers all required content and boundaries, and rejects unsupported material or claimed fields within that account.
**O-44** every member of each admissible presentation class is exact for the presented notion. The class constraints and the independently stated content establish the result; uniqueness of a selected topology is not a requirement.
**O-45** presented semantic definitions recover their actual rules, interfaces, premise occurrences, and dependencies, and preserve and reflect their applications and meaning through the linked presentations.
**O-79** each claimed presentation domain has total finite representability, with constructed witnesses for every claimed inhabited domain. An empty constrained domain cannot establish adequacy for a larger inhabited domain. A generic intended domain is not reduced to finitely enumerated ground examples.
**O-80** intrinsic relations between presented notions are preserved and reflected by the jointly admissible presentations. Explicit composition theorems account for shared material, exact targets, binding scopes, occurrence identity, and dependencies wherever relevant. Separate exactness does not discharge this obligation.
**O-84** develop and apply a general presentation theory whose scope is justified by recurring requirements. Each construction states and proves the conditions needed for exactness, joint coverage, and native interpretation where required. Existing and new presentations use these results wherever applicable; residual special cases state the boundary that requires separate treatment.
**O-85** the presentation theory's own relevant structures, definitions, contracts, and proofs receive exact presentations and explicit intrinsic-link results under the same discipline. Native self-application of an operative reader is one result within this obligation; it does not by itself establish native checking of all presentation contracts or exactness proofs.

O-44 and O-80 govern every presentation stratum. The ledger must identify the
class, represented domain, intrinsic links, admitted structural criteria,
accepted theorems, and any remaining compatibility or composition work.
Historical requests for quotation principality are superseded rather than
retained as additional delivery conditions.

### 6.14 First join: construction — `Factor_Construction`

**Defect.** `factor_constructs` (`Factor_Construction.thy:42`) never ties pieces
to `construction_inputs`. With $B$ the cited output, a witness may use $B$ as its
sole piece mapped identically to $B$. `exact_fragment` is used by no other
theory, so restricted material loses its record of selection.

**Warrant.** Completeness invariant; intent already fixed.

**Change.**

$$
\boxed{
\text{declared input occurrence}
\to
\text{selected fragment occurrence}
\to
\text{assembly piece}
\to
q
\to
\text{output occurrence}
}
$$

A piece is a fragment of a declared input or an explicitly admitted constructor,
template, literal, or base artifact. Source and selection determine the piece
material. Omitted source structure stays visible as omitted.

`function_like` (`:85`) is removed under **P-3**: it substitutes isomorphism for
exact identity without a theorem and is not necessary.

**Obligations.**
**O-46** every piece has an admissible origin in the declared inputs or authorized constructors.
**O-47** adequacy in both directions between construction and admissible `K2` assembly.
**O-48** complete treatment of omitted source structure.

### 6.15 Second join: realization and replay

**Defect.** `required_certificate_links` (`Factor_Evidence.thy:17`) requires
three links; `factor_replays` (`:61`) is an alias for `factor_certifies`.

**Warrant.** **D-5**, **P-2**.

**Change.**

$$
\boxed{
\begin{aligned}
\operatorname{Replay}_{\Phi}(J,d,E)
\iff{}&
\operatorname{EvidenceFormed}(E)
\wedge
\operatorname{Derives}_{\Phi}(J,d)\\
&\wedge
\operatorname{Realizes}_{\Phi}(E,J,d)
\wedge
\operatorname{RetentionBoundary}_{\Phi}(E)
\end{aligned}
}
$$

Realization preserves exact identity, sharing, assumptions, and external
anchors.

**Replay is generic; certification is a further join.** An earlier draft required
the certificate projection to be complete over program, declared inputs, output
boundary, and assembly-piece justification — but not every Factor judgment is a
construction judgment. A proof about equality, formation, or a semantic property
has no program inputs and no assembly, and requiring those fields would make
generic replay construction-specific.

$$
\begin{aligned}
\text{generic replay}
&=
\text{derivation}+\text{realization}+\text{retention}\\
\text{certified construction}
&=
\text{generic replay}+\text{the corresponding construction judgment}
\end{aligned}
$$

The second needs no new primitive — it is a derived conjunction, or later an
adequacy theorem — but it needs a location, since it reaches `Factor_Construction`
and generic replay does not. Its complete projection over program, declared
inputs, output boundary, assembly-piece justification, residuals, and provenance
belongs there and nowhere below it.

**Obligations.**
**O-49** derivation soundness independent of retention.
**O-50** realization completeness and no-extra.
**O-51** exact assumption projection.
**O-52** evidence retention cannot create validity.
**O-53** replay checking terminates on complete finite inputs, implying nothing about decidability of truth or existence of a derivation.
**O-81** certified construction is a distinct relation with its own complete certificate projection; generic replay carries no construction-specific field.

### 6.16 Third join: continuation — `Factor_Continuation`

**Defect.** `factor_advances` (`Factor_Authority.thy:68`) equates the union of
predecessors and dependencies with the input list, erasing three distinctions
plus order and repetition.

**Warrant.** **P-2**.

**Change.** Each relation keeps its own boundary; the union equation is removed.

$$
\operatorname{Advance}_{\Phi}(H,\tau,H',E)
\iff
\operatorname{RRAAdvance}(H,\tau,H')
\wedge
\operatorname{Continuation}_{\Phi}(H,\tau,H',E)
$$

**Obligation.** **O-54** historical ancestry cannot reconstruct an omitted
semantic dependency or authority edge.

### 6.17 Authority — `Factor_Authority`

**Defect.** Raw adoption and currentness depend transitively on evidence and
proof through the import of `Factor_Evidence`.

**Change.** Raw adoption and currentness depend on meaning and publication only;
certified uses live above evidence.

**Obligation.** **O-55** adoption does not prove its subject, validity does not
compel adoption, structural correspondence does not authorize an interpretation.

### 6.18 Amendment — `Factor_Amendment` (new)

**Defect.** `foundation_successor` (`Foundation_Genesis.thy:95`) requires only
formed foundations, one `factor_advances`, output agreement, and a formed
publication. There is no amendment protocol. Its prose asserts that a change
outside the continuation relation needs a fresh Isabelle handoff, which D-9
denies.

**Warrant.** **D-9**.

**Change.** Isabelle is normative through genesis only; its final obligation is
the adequacy of $\Phi_0$ including the transition mechanism. Thereafter:

$$
\boxed{
\Phi_{n+1}\ \text{is legitimate}
\iff
\Phi_{n}\models\operatorname{Accepts}(\ulcorner c\urcorner,\Phi_{n+1})
}
$$

evaluated under the predecessor's *current* amendment semantics — "current" in
the sense of §6.17, relative to an exact authority, publication, locus,
generation, and purpose.

**Non-self-justification, correctly stated.** An earlier draft required

$$
\operatorname{AuditCarrier}
\bigl(\operatorname{Accepts}(\ulcorner c\urcorner,\Phi_{n+1})\bigr)
\subseteq
\Phi_{n}
$$

which is wrong. Acceptance must *inspect* the candidate successor and the
certificate; those are ordinary arguments and need not belong to the predecessor.
Under that condition the successor could not be examined at all. What must be
predecessor-grounded is the semantic authority used to judge, not every datum
appearing in the judgment:

$$
\boxed{
\text{successor clauses may be inspected as data;}
\quad
\text{they may not authorize their own acceptance as rules}
}
$$

With $\mathcal{F}_n=(\Phi_n,\mathcal{E}_n)$ the predecessor package, the
condition falls on the *active* dependencies — the definitions whose formation or
truth clauses are invoked, which §6.12's audit already distinguishes from
ordinary arguments:

$$
\operatorname{ActiveSemanticDependencies}
\bigl(\operatorname{Accepts}_{\mathcal{F}_n}(c,\mathcal{F}')\bigr)
\subseteq
\operatorname{DefinitionClosure}(\mathcal{F}_n)
$$

Containment is in the predecessor's closed definition *package*, not its root
artifact alone: D-11 puts foundational dependencies in $\mathcal{E}_n$. The
complete ordinary argument boundary meanwhile includes the predecessor package,
the candidate successor package, the certificate, and the exact authority and
publication frame the predecessor's acceptance relation requires.

This is the statement `genesis_is_not_self_authorized` should have had, and it
needs no new primitive — only the correct projection from the audit of §6.12.

**Permanence covers the environment, not just the root.** Old foundations and
judgments retain their exact original meanings permanently, and every semantic
artifact carries its exact foundation package. Holding $\Phi_n$ fixed while
rebinding a meaning-bearing slot of $\mathcal{E}_n$ is not preservation of the
same foundation — under D-11 meaning depends on both — so permanence is stated
over $(\Phi_n,\mathcal{E}_n)$.

**The certificate: four orthogonal relations, not a partition.** The earlier
draft required preservation, interpretation, migration, and intentional
incompatibility to be pairwise disjoint and jointly exhaustive. That was an
over-formalization — D-9 says "or", not "partition" — and it is wrong on the
subject matter: a transition may migrate a structure *and* preserve its meaning
*and* supply an interpretation bridge at once. Migration concerns structure;
preservation and interpretation concern judgments and meanings; incompatibility
classifies a refusal of preservation.

$$
M_S\ \text{structural migration},
\quad
M_J\ \text{semantic interpretation},
\quad
P\ \text{preservation over } M_J,
\quad
I\ \text{declared incompatibility}
$$

Each carries its own declared domain and its own completeness condition.

**The domain cannot be self-chosen.** If a certificate declares its own
compatibility domain it can pick an empty one and be trivially complete — the
same vacuity as the empty reflection domain. The domain is determined
structurally: the changed definition boundary, the exported public interfaces,
and the exact affected-dependency closure.

**Cross-version bridge.** A successor may replace the identity and quotation
rules, but the transition itself is interpreted under the *predecessor's* rules.
A predecessor-relative transition substrate therefore survives every amendment,
and later successors need an explicit bridge to cite or interpret the older
chain. No foundational layer disappears without leaving that boundary.

**Obligations.**
**O-56** acceptance locality: the *active semantic dependencies* of $\operatorname{Accepts}$ lie in the predecessor's closed definition package, while successor and certificate remain inspectable as ordinary arguments.
**O-57** permanence: meaning relative to $(\Phi_n,\mathcal{E}_n)$ invariant under successor formation.
**O-82** predecessor environment immutability: no admissible transition rebinds a meaning-bearing slot of $\mathcal{E}_n$.
**O-58** the declared domain is structurally determined, not certificate-chosen.
**O-59** completeness of each of $M_S,M_J,P,I$ over its own domain.
**O-60** the cross-version interpretation bridge exists and is exact.
**O-61** succession requires the enumerated material: predecessor, assembly account, evidence for retained and changed dependencies, derivation under the predecessor's continuation rules, authority decision.
**O-62** the mechanism is a component of $\Phi_0$, covered by §6.20's adequacy.

### 6.19 Computational sufficiency — `Factor_SK`, `Factor_Computational_Sufficiency`

**Defect.** `sk_step` sits inside `factor_holds`; the recognized $[S,K]$ topology
selects a rule stated elsewhere; `sk_program_complete`
(`Foundation_Computational_Sufficiency.thy:22`) quantifies only over terms
already quoted through one finite resolver, so the completeness clause is
satisfiable with no nontrivial reduction; the obligation sits inside the
definition and later lemmas assume it.

**Warrant.** SK is settled as the adequacy target. **P-1** determines that an
adequacy witness may not define truth and a topology may not select a rule whose
content is elsewhere.

**Change.**

$$
\text{general Factor semantics}
\to
\text{Factor definition of SK}
\to
\text{adequacy theorem}
$$

The earlier draft's obligations — no `sk_step` in truth, uniformity, one
concrete reduction — establish neither multi-step adequacy nor universality. The
full set:

**Obligations.**
**O-63** representation: every finite SK term has a formed quotation.
**O-64** one-step soundness *and* completeness: $t\to_{\mathrm{SK}}u \iff \operatorname{FactorStep}(\ulcorner t\urcorner,\ulcorner u\urcorner)$.
**O-65** multi-step adequacy: $t\to^{*}_{\mathrm{SK}}u \iff \exists d.\ \operatorname{FactorDerivesReduction}(\ulcorner t\urcorner,\ulcorner u\urcorner,d)$.
**O-66** universality: a machine or lambda-calculus encoding into SK proved in Isabelle, or imported from a precisely fixed development with its assumptions explicitly discharged.
**O-67** non-vacuity: concrete reductions and at least one nontrivial compiled computation.
**O-68** `factor_holds` contains no reference to `sk_step`.

### 6.20 Reflection and genesis

**Defect.** `external_truth` (`Foundation_Reflection.thy:61`) is a supplied
field and `reflection_valid` (`:87`) contains the intended result as its own
conjunct. Both sides of the "external/internal" agreement already inhabit the
internal representation. Nothing forbids an empty domain, which makes the
adequacy clause and the evidence obligation vacuous. No concrete $\Phi_0$ or
$G_0$ exists and no complete genesis is proved.
`genesis_is_not_self_authorized` extracts a conjunct.

**Warrant.** Intent already fixed, with **D-9** adding the transition mechanism
to the domain and making this Isabelle's last obligation.

**Change.** Define the HOL-side public relations in their own theory,
independently of any internal representation, and remove `external_truth`.

**Stratify, do not flatten.** A single untyped $j$ over every judgment family
would reintroduce nominal dispatch on a sum datatype at the Isabelle level, and
would ask one truth relation to establish its own unrestricted truth. Adequacy
is developed along the same DAG as the foundation:

$$
\text{RRA adequacy}
\to
\text{Factor-formation adequacy}
\to
\text{Factor-meaning adequacy}
\to
\text{construction / derivation / authority adequacy}
\to
\text{reflection and amendment adequacy}
$$

and combined into one genesis theorem at the end.

**The domain is generic, not enumerated.** The earlier draft's "enumerated
domain" was ambiguous and could be read as a finite list of known ground
applications — which would readmit the archive's finite-ground limitation in
another form. The domain is characterized by a condition covering *arbitrary
formed finite applications* of the reflected generic definitions.

The result:

$$
\boxed{
\operatorname{BootstrapHolds}_{\mathrm{HOL}}(j)
\iff
\operatorname{FactorHolds}_{(\Phi_0,\mathcal{E}_0)}(\ulcorner j\urcorner)
}
$$

followed by an actual complete genesis over the package $(\Phi_0,\mathcal{E}_0)$
of D-11.

**Obligations.**
**O-69** the domain covers arbitrary formed finite applications of the reflected generic definitions, and is nonempty and non-ground.
**O-70** the adequacy theorem relates two independently defined relations, neither supplied as a premise of the other.
**O-71** stratum-wise adequacy along the dependency DAG, combined only at the end.
**O-72** formation preservation and reflection, exact-boundary preservation, soundness of reflected derivations, completeness over the claimed domain, checker agreement, no hidden external arguments.
**O-73** a concrete complete genesis exists, is proved, includes the D-9 mechanism, and its environment satisfies **O-16**.

---

## 7. What is removed

| Removed | Why |
|---|---|
| `sk_step` inside `factor_holds`; `combinator_construction_holds` as a primitive | an adequacy witness may not define truth |
| `factor_replays` as an alias | **D-5**, **P-2** |
| `function_like` | **P-3**; substitutes isomorphism for exact identity without a theorem |
| `external_truth` | the result to be proved may not be a supplied field |
| `quotation_geometry`, `faithful_geometry`, `requote`, `reflexive_geometry`, and the behavioral-equivalence theorem | Their supplied decoder and tautological equivalence prove neither presentation exactness nor composition; amended **D-6** permits adequately justified alternatives |
| `artifact_resolver` in normative signatures | **D-2** |
| the predecessor–dependency union equation | **P-2** |
| evidence, publication, authority, and trust fields from generation identity | **D-4** as amended; retention is not succession |
| the claim that a change outside the continuation relation needs a fresh Isabelle handoff | **D-9** |
| the cross-profile resolution theorem of the earlier draft | wrong; superseded by **D-11** |
| the four-way disjoint-exhaustive certificate partition of the earlier draft | over-formalized; **D-9** says "or" |
| `RRA_Exact.thy.tmp` | already removed |

Removed **only after** O-2 … O-6 are proved, per D-8's migration order: the four
`rra_data` constructors, `data_profile_kind`, `profile_kind`, the three
functionality predicates, the four-case `data_formed`, `restrict_data`, and
`push_data`, and the eight per-profile assembly components.

Retained but renamed: `rooted_complete`, to a name that says connectivity.

---

## 8. Naming discipline

$$
\boxed{
\text{a name may claim no more than its statement establishes}
}
$$

`genesis_is_not_self_authorized`,
`audit_reflection_is_external_internal_agreement`,
`complete_genesis_has_reflection_and_computation`, and
`genesis_has_external_internal_agreement` restate conjuncts of the definitions
that supply them. Unfolding a definition is legitimate exposition; presenting it
as evidence that a constitutional property holds is not. Every theorem whose
name asserts non-circularity, completeness, sufficiency, adequacy, or exactness
is restated so its conclusion carries that content, or renamed. `Bootstrap_Audit`
exposes boundaries; it does not stand in for results.

---

## 9. Obligations by stratum

| Stratum | Obligations |
|---|---|
| Data basis | O-1 … O-7 |
| Footprints | O-8, O-9 |
| Citations, anchors, environments | O-10 … O-17, O-74 … O-76 |
| Structural syntax | O-18 |
| Fragments | O-19 |
| Assembly | O-20 |
| Generations, selections, transactions | O-21 … O-29, O-77, O-78 |
| Factor structure | O-30 … O-34 |
| Presentation, application, meaning | O-35 … O-40 |
| Dependency audit | O-41, O-42, O-83 |
| General presentation theory and quotation; O-44 and O-80 apply throughout | O-43, O-44, O-45, O-79, O-80, O-84, O-85 |
| Construction | O-46, O-47, O-48 |
| Realization, replay, certified construction | O-49 … O-53, O-81 |
| Continuation and authority | O-54, O-55 |
| Amendment | O-56 … O-62, O-82 |
| Computational sufficiency | O-63 … O-68 |
| Reflection and genesis | O-69 … O-73 |

---

## 10. Order of work

1. **Make the session build.** Prior to everything and independent of it.
2. **Rebuild the theory graph** to the table in §5, before substantive proofs.
3. **The data basis** (§6.1), including the P-3 verdict on $\varphi$, then the
   migration proofs, then deletion. First among substantive repairs because
   §6.5 and §6.6 are consequences of it.
4. **Footprints** (§6.2), then **citations and environments** (§6.3). Both
   mechanical and pervasive.
5. **Fragments, assembly, evidence, generations, selections, transactions**
   (§6.5 – §6.9), parallel once step 3 lands.
6. **Factor structure and its bridge theorem** (§6.10). D-10 makes this the hinge:
   until it closes, "Factor over RRA" is a claim.
7. **General presentation theory, its own presentations, and quotation
   exactness** (§6.13). Derive the scope from concrete requirements, establish
   reusable constructions and explicit compatibility at intrinsic links, and
   use them throughout later presentation strata.
8. **Presentation, application, dependency audit, meaning** (§6.11, §6.12),
   with the candidate admission verdicts.
9. **The three joins** (§6.14 – §6.17).
10. **SK and computational sufficiency** (§6.19), then **amendment** (§6.18).
11. **Bootstrap judgments, concrete quotation, stratified reflection, genesis**
    (§6.20).

Steps 6, 8, and 11 are where the development either becomes the intended system
or does not. The rest are prerequisites, not progress toward them.

---

## 11. Delivery gate

* Isabelle accepts the session, reproducibly, from recorded theory-source
  identities and a stated Isabelle version and base session.
* No `sorry`, `oops`, `axiomatization`, or equivalent escape.
* Every obligation in §9 closed by an accepted theorem.
* Every admitted presentation class accounts for its notion's content and
  intrinsic relations, with accepted compatibility and composition results.
  No single-grammar or quotation-principality condition is imposed.
* The general presentation theory has a scope justified by evidence and is used
  for its own relevant notions and throughout the system. Each operative native
  instance has actual clauses and proved contracts; proof-language predicates
  do not acquire native force merely by being parameters of a theorem.
* Every existence claim discharged by a construction, not a predicate named for
  the property.
* Explicit non-vacuity: adequacy for an intended inhabited domain is not
  discharged by an empty or ground-only restriction. Claimed inhabitance has
  constructed witnesses, and empty constrained cases remain explicit.
* Audit tooling fails on tool error rather than reporting a pass, and no lexical
  scan is presented as establishing a mathematical property.

---

## 12. Open

### 12.1 Requiring an owner decision

**Open-1 — the exact minimal data basis.** D-8 fixes the direction and the owner
has ruled that $\varphi$ faces the admission test. If **O-7** returns that
$\varphi$ is *not* representable as constrained $\beta$, the basis has two
primitive attachment modes and the alternatives the earlier review raised —
fully structural data occurrences, a minimal opaque external-payload relation —
have not been compared. That comparison needs a decision if it arises.

**Open-2 — what `Cause` cites.** *(Now Entailed; recorded here so it can be
overturned.)* D-4 as amended makes the construction account identity-bearing, and
the earlier draft left it undecided whether $\mathit{Cause}$ cites the
construction *judgment* or the assembly *witness*. The question resolves once it
is asked precisely: **does the construction judgment identify one exact
construction account, or merely assert that some account exists?**

§6.14 requires the application boundary to determine the complete family of
contributing pieces and the whole provenance chain. So the judgment's boundary
*contains* the pieces and $q$; it does not existentially abstract over them.
Therefore $\mathit{Cause}$ cites the construction judgment, and that citation
already distinguishes distinct construction accounts.

The consequence settles the other half. Two witnesses for one judgment are then
two *proofs* of one exact construction, and making them identity-bearing would
reintroduce exactly the evidence/identity conflation D-4 was amended to remove.
So $W_1\ne W_2$ for a single judgment does **not** yield distinct generations,
while genuinely different construction accounts do.

This depends on §6.14 keeping the pieces inside the boundary. If that changes,
Open-2 reopens.

### 12.2 Settled by proof, not by decision

**Q-1** whether both anchor forms are primitive (**P-3** on §6.3).
**Q-2** whether selection and publication are one notion or two (**P-3** on §6.9).
**Q-3** which incidence pattern carries data-atom ownership. The earlier draft
said this "falls out of" the quotation grammar; that coupled opaque data
representation to foundation quotation without justification and is withdrawn.
It is decided in §6.1 on its own merits, and named explicitly there per P-1.
**Q-4** whether `Factor_Quotation` and `Factor_Presentation` are one relation or
two, since a definition's RRA representation and the grammar recognizing it may
be the same thing (**P-3** on §5).
**Q-5** which v6.1 presentation forms and clause rows survive **O-40**.
**Q-6** whether any recovered Factor relation simplifies extensionally to a
direct incidence projection (**D-10**'s allowance; derived, never foundational).
**Q-7** which structural compatibility conditions and composition theorems
discharge **O-80** at each intrinsic link. The former choice between two
quotation-determination arguments is superseded by the owner's correction.
**Q-8** whether `Factor_Cause` and `Factor_Certified_Construction` are two
theories or one (**P-3** on §5); they were separated because their imports
differ, which is evidence but not proof.

---

## 13. Disposition of the external review

| Recommendation | Disposition |
|---|---|
| 1. Correct the authority classification | **Accepted in full.** §0.2. Reinforced by the owner's statement that the answers were LLM-composed and broadly representative. |
| 2. Replace P-1 and P-2 | **Accepted.** P-1 restated as structural dependence; P-2 split into non-conflation and P-3 irredundancy, enforced as a pair. |
| 3. Restore the two-path quotation requirement | **Superseded by the owner on 2026-09-08.** Amended D-6 requires exact admissible presentation classes and exact intrinsic relations throughout the system. No unique topology or principal grammar is required. |
| 4. Demote the data basis | **Partly accepted.** D-8's direction stands; $\varphi$ faces the admission test by owner ruling; the migration obligation is corrected from exact identity to faithfulness; node ownership is decoupled from quotation. |
| 5. Closed-anchor TODO; fix cross-profile theorem | **Accepted.** The theorem is withdrawn as wrong; D-11 supplies citations, environments, and self-reference. Calling this "resolved" overstated it: D-11 settles the *direction* of the anchor problem, not its composition. See the second review, row C-1. |
| 6. Footprints relative, not globally closed | **Accepted in full.** §6.2. |
| 7. v6.1 forms as candidates | **Accepted in full.** §6.11; D-1's own "simplify under irredundancy" required it. |
| 8. Exact import table; fix SK, quotation, amendment, references | **Accepted in full.** §5. All four ordering errors were real. |
| 9. Separate generation identity from evidence | **Accepted, by owner amendment.** §6.8, D-4. |
| 10. Certificates as orthogonal relations | **Accepted in full.** §6.18, plus the structurally determined domain and the cross-version bridge. |
| 11. Strengthen SK adequacy | **Accepted in full.** O-63 … O-68. |
| 12. Stratify reflection; generic domain | **Accepted in full.** §6.20. |
| "D-2, D-4, D-8, D-9 are not owner decisions" | **Rejected as stated.** They are owner-endorsed directions taken in this session, which the reviewer could not see. Their *formulations* are provisional, which is the reviewer's point and is now §0.2. |

### 13.2 Second review — composition of the new boundaries

Its finding was that several individually sound definitions were treated as
though their compatibility were automatic. That is correct, and it is the class
of defect this pass repairs.

| Finding | Disposition |
|---|---|
| **C-1** environments must compose: structural occurrence is not closed semantic use; slots need a scoping rule under repeated reuse; $\mathcal{E}_0$ must not bound future arguments | **Accepted in full.** §6.3, O-74 … O-76. The third is the sharpest: without it the archive's finite-ground limitation returns through the environment instead of the clause set. |
| **C-2** counterexample to the naive elimination of $\varphi$ | **Accepted, and verified independently** against `RRA_Assembly.thy:119` and `:105`. Bag pushforward sums over the fibre; functional pushforward is a set image and merges idempotently. O-7 is now a commuting square, not a statement about values. |
| **C-3** O-5 was not satisfiable as written | **Accepted.** A pushforward cannot be total on all candidate gluings and undefined on conflict. Replaced by a total compatibility check plus a determined pushforward on the compatible domain. |
| **C-4** principality needs an existence obligation, and must not presuppose the geometry it justifies | **Principality superseded by the owner on 2026-09-08.** Non-vacuous construction remains in O-79. O-44 and O-80 now require presentation exactness and explicit composition for intrinsic links; assumed adequacy or compatibility cannot count as its own proof. |
| **C-5** "injective and canonical" does not follow from uniqueness up to $\cong_{\partial}$ | **Naming correction retained; presentation requirement amended.** O-21 requires exact core recovery and intrinsic links, without requiring all adequate generation presentations to be isomorphic. |
| **C-6** generation formation cannot validate a cause; the join has no location | **Accepted in full.** §6.8, `Factor_Cause`, O-78. |
| **C-7** generic replay must not be construction-specific | **Accepted in full.** §6.15, `Factor_Certified_Construction`, O-81. |
| **C-8** §6.8 and Open-2 were both unconditional | **Accepted.** The internal contradiction was real. Open-2 is now resolved as Entailed, with the reviewer's sharpening — does the judgment identify one account or assert that one exists — supplying the argument. |
| **C-9** $\operatorname{AuditCarrier}\subseteq\Phi_n$ is the wrong non-self-justification condition | **Accepted in full.** It would have forbidden inspecting the successor at all. Replaced by active semantic dependencies within the predecessor's closed package. O-56, O-82. |
| **C-10** the build attribution over-assigns responsibility | **Accepted.** §1.1 now separates what was established from where responsibility lies. |
| **C-11** the v6.1 bridge must not make v6.1's restrictions normative | **Accepted in full.** §6.10; the converse direction is now stated over the supported class, not the whole formed domain. The same admission discipline is extended to the audit machinery in §6.12, which the plan had inconsistently exempted. |
