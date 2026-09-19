# Handoff

The history of every rotation is in git and in `.build/handoff-archive/` (the last long form:
`HANDOFF-impl30-20260919.md`); what is settled is in native_control_plan.md, DECISIONS.md and THEORY_MAP.md. The
owner's directions and open questions are in `.claude/orchestration/owner-ledger.md`. Each batch records what it
settles once, where it is read (DEVELOPMENT_WORKFLOW.md): its decisions as an entry of DECISIONS.md, a theory's reuse
in its THEORY_MAP.md row, the evidence also in its commit message, what remains in the graph; the plan changes only
with its structure, the stages' standing or the direction of the work.

## Graph

Two lines, and the owner's two directions of 2026-09-19 order them.

**The engine line (5, 6, 7, 8).** T2 measured a native definition whose argument is a whole state: it re-verifies
the context every call carries — the machinery's reach at 171.8 s natively against 0.99 s in HOL (DECISIONS.md, "A
native definition over a state re-verifies its context in every call"). Every remaining notion of the Q7 order is a
definition of that shape, so the cost is on the critical path of the owner's direction that native definitions are
normative, and of condition 5a; the owner's standing direction is that such a cost is fixed now at its cause. #5
finalizes the first of the two decided refinements (constructed applications; after it, seed evaluation 0.403 s from
1.224, machinery reach about 44 s from 171.8); #7 is the second (evaluate over the positions of the demanded calls,
against a bound of 5 s). A third — the store search taking its store before its key — is a task only if #7's
measurement finds key comparisons dominant; #8 judges that against the probe, not against #7's report.

**The Q7 line (9, 11, 10, then the further builds).** #3 designed the verdict of a kind as a native definition over
structural rows and is delivered; it folded the paused structural-Isabelle-state work in by demand and left nothing
of it that the verdict needs. #9 designs the development notions themselves as structure — problems, requests,
answers, packets — the octet direction's task 3, promoted because three build lines need it: the decomposition's
schema matches on problems, and the verdict and request construction read them. #11 briefs the verdict's build from
#3's entry; #10 briefs the decomposition's build. Both briefs wait on #9 so that no build fixes a presentation of a
development notion that #9 then decides differently.

**#4** (efficiency as structure, the octet direction's task 5) is running, independent of both lines; its instances
are the refinements imported through `Native_Execution_Refinements` together with #5's and #7's — six, past first
use. It blocks nothing, and every further refinement is another instance, so it stands last and loses nothing by it.

Order (queue `5 6 7 8 9 11 10 4`): the owner's latest directions first, then dependency, then what can change other
tasks, then size. The engine line leads because it bounds what every native definition over a state costs. #9 leads
the Q7 line's remainder because both briefs rest on it. #11 precedes #10: the verdict is the Q7 order's next notion,
and its build establishes the presentation relation with its key and invariance lemmas, which the decomposition's
schema over problems then reuses rather than re-deciding. Neither brief is blocked on #8 — #3's build order puts
`unreached`, the one field that composes the reach, last, so only that build task waits for the measurement.

## Decisions

Taken by the planning episodes, where they are not entries of DECISIONS.md:

- **The Q7 order stands provisionally, with the engine's cost before its second step.** Basis: T2's measurement and
  the owner's 2026-09-18 direction on inevitable costs. An owner answer to Q7 reorders the whole graph.
- **Order is the queue's; a blocker records a dependency on an artifact, not a wish about order.** A design is not
  blocked on a measurement it does not consume: what #3 had to respect is that the verdict is a definition over a
  whole state, not the number. The number decides whether its *build* can follow.
- **The verdict's build is not blocked on the engine measurement; only its `unreached` field is.** #3's build order
  is by what of the state a field demands, and `unreached` alone composes the reach and carries its cost. Every other
  field is built and checked before #8 reports. Basis: #3's entry, which splits the closure assessment for exactly
  this reason.
- **The structural state the verdict demands is the verdict's build's first step, not a task of its own.** What is
  demanded is the relational skeleton — constants as atoms, rows in families by kind, three citation relations, the
  statement inert — with its presentation relation and the key and invariance lemmas; it is smaller than the paused
  task 2 by the whole of the term structure, and separating it would split one contract from its only consumer.
  Basis: #3's entry and its second planner question.
- **The incremental assessment of an edited state is planned after the verdict's build.** #3 found that a *stage* of
  judgments is not affordable at either measured figure (224 answer states at about four reaches each, of the order
  of 4,500 s against 22.4 s for the HOL stage) and named the structural remedy: read an edited state's reach and
  declaredness from the state's own assessment and the edit. It is additive — a second definition with its own
  contract — and not a prerequisite of a native *judgment*, and the verdict's build supplies both its subject and the
  measured cost that says how much it must save.
- **No new native definition of a development notion is built over the tagged-tree presentation.** The decomposition
  entry presupposes the presentation its schema ranges over and does not define it; building over the present one
  would put a new use of octets as structure into new code, against the owner's direction of 2026-09-19 07:34. Hence
  #9 before #10 and #11. The verdict itself is clear of this: #3's rows are structure and its statement is carried
  inert, which the owner's direction expressly permits where no structure is used.
- **Q2 is extended rather than split.** The decomposition raises three policy criteria of Q2's own family; they are
  recorded in the ledger under Q2 with their provisional choices, not asked as a new question.
- **#9, #11 and #10 before #4, and any later refinement after #4.** #4 unlocks nothing and grows richer with every
  further instance. Its one constraint: a refinement written after #4's entry must apply its notion, so the
  conditional store-search task (if #7's measurement makes it one) follows #4 rather than adding a seventh
  un-factored instance.
- **No task rests on reasoning not yet written.** Request construction, native problems and the translation wait for
  #9's entry and #11's tasks; the third engine refinement waits for #7's measurement.

Watch: store absence in `Native_Path_Stores` (inside the verdict's build) and the refusal that cannot tell an absent
certified generation from an unavailable input (Not yet planned, item 5) are two instances of one library rule —
an empty result and a failed one are kept apart. A third instance is a first-use factoring problem, not a third fix.

Settled and written elsewhere: DECISIONS.md holds every batch's decisions in order, 192 entries; the newest are "The
verdict of a kind is a native definition over a state's rows" (#3), "A problem is decomposed through the constants
its answer needs" (#2), "A native definition over a state re-verifies its context in every call", "The reach of a
state is a native definition".

## Delivered

- **#1 (brief)** produced the engine line, #5 through #8.
- **#2 (design), accepted and committed 2026-09-20 as `0ac9502e`** — DECISIONS.md, 191st entry, 157 lines. A
  decomposition is a row of the development library that is an obligation reduction of the parent's contract to its
  subproblems', presented as an application of one Factor schema over the native presentation of problems; `L` was
  merely empty and `development_loop_issue` already takes it. Composition is `obligation_reduction_discharge`,
  `inference_sound` with `inference_closure_sound`, `obligation_reduction_compose` with `obligation_substitution` for
  depth, and `schema_graph_development_complete` for the tree. Soundness is the schema's, proved once and consumed by
  every application. It corrected its own brief: `development_request_context_least` proves no decomposition shrinks
  a one-constant request, so an oversized context decomposes the problem instead. The answer frame's one-equation
  limit stays unlifted by design. Its six follow-ups are #10's subject. Verdict: `.build/tasks/2/verdict.md`.
- **#3 (design), accepted 2026-09-20, uncommitted** — DECISIONS.md, 192nd entry, 163 lines, no theory changes.
  What later work needs from it: a kind is **the family that holds a row**, never a datum it carries, so no octet
  distinguishes a definition from a code equation and the refinement and definition verdicts stay instances of one
  definition at their family selections. The verdict reads five things of an entity — kind, declared constant,
  subjects, mentions, identity — and nothing inside a statement, so it demands the **relational skeleton** of a state
  and no more, the statement carried inert as its local presentation (`isabelle_local_entities`, invariant by
  `isabelle_local_entities_renamed`). A row's key is determined by its identity and the two presentations share one
  key assignment, so `isabelle_state_embedding` never appears in the decision. **Acceptance is positive and needs no
  absence** — every field an `every` or a `some` with membership decided by a search, "removed implies permitted"
  written as a disjunction — and absence is built only for the witnesses, neither side the other's negation. The line
  it draws: reading which constant a term is an equation of is *presentation* of Isabelle content, whose fidelity
  Isabelle verifies; whether mentions lie in the support, whether a removal was permitted, whether the state is
  closed is the *decision*, and is native. Nine fields as native programs, the contract against
  `development_verdict_accepted (development_constant_verdict replaceable demanded S r S')` in the shape of
  `native_development_ready`, a build order smallest-first, and three conditions named with their owner rather than
  assumed (distinct names, the vacuity of unknown positions, the reduction of an edit). Not built, and demanded by
  translation and installation instead: terms as citation graphs, base constants as cited anchors,
  `.build/impl22/t2/Finite_Structural_Graphs.thy` (stays uninstalled). Verdict: `.build/tasks/3/verdict.md`.

## Open

The owner's questions, each with the provisional choice that stands meanwhile, are in the ledger; where each bites now:

- **Q1** the admission rule of a bootstrap adoption and OD-2. Bites when an admitted native answer is installed as
  Isabelle material — the request class the Q7 order names last.
- **Q2** authority of the first loop's problems and its selection criterion, extended 2026-09-20 with the
  decomposition's three policy criteria (which decomposition when several apply; when one is demanded rather than
  applicable; whether a derived subproblem inherits its parent's authority). Bites in #10's builds and in any
  selection beyond readiness.
- **Q3** what Isabelle establishes about adequacy. Bites when DEVELOPMENT_WORKFLOW.md and plan.md §0.1 are next
  touched; unplanned.
- **Q4** an agent executor confined to its packet. Bites at the plan's stage 3 gate; unplanned.
- **Q5** how far the native residual record reaches. Bites in #9, which grows the structural notions by demand on the
  same principle #3 used for the state's rows.
- **Q7** the order of work under the direction that native definitions are normative. It orders this whole graph; an
  answer reorders it.

Not yet planned, in the order they are expected to be planned:

1. **The incremental assessment of an edited state** — its reach and declaredness read from the state's own
   assessment and the edit, with a contract against the assessment of the edited state. #3 measured why: one native
   judgment is affordable and a verification stage is not (224 answer states at about four reaches each is of the
   order of 4,500 s at the engine's bound, against 22.4 s for the HOL stage). Until it exists the loop judges one
   answer natively and cannot run a stage natively — which is condition 5a's path. After #11's tasks land, so that
   its subject and the measured cost of a judgment are both in.
2. **Request construction** natively over the verdict's rows (support as the constants the refined entities mention,
   and the least context), the Q7 order's step after the verdict; contract against `development_refinement_request`.
   After #9 and #11's tasks (same rows, same presentation).
3. Problems whose subjects are native definitions, answered natively, and the translation of admitted native content
   into Isabelle material — the owner's direction of 2026-09-19 06:21 and the last step of the Q7 order (the old T10).
4. A proof request class, and with it the decomposition of a proof problem, which the decomposition entry names and
   leaves undesigned for want of it (refinement and definition problems are requested and judged; a proof problem is
   not). It needs request construction (item 2) for its support and least context, and its first question is what the
   native content of a proof answer is: the library holds native derivations, certificates and replay for calls of
   native programs, while a contract proved against a HOL counterpart is Isabelle material by nature. That question is
   the owner's direction of 2026-09-19 06:21 met head-on, and it is where Q1 bites.
5. The refusal that an absent certified generation cannot tell from an unavailable input: an empty result and a
   failed one are kept apart everywhere else in the library, and not here. One instance of the same rule as store
   absence, which the verdict's build carries.
6. A persistent native published state for the refinement layer: without one, an adoption records the transaction of
   its judgment rather than one against a history, and a later selection cannot supersede an earlier one.
7. The octet direction's task 6 (transport: packets and answers travelling as the complete data of their artifacts,
   the word inert carriage) — unless #9 settles it, which is #9's to say.
8. The plan's stages 4 (policy extended from owner directions) and 5 (the machinery improving itself through the
   process), not begun beyond the machinery's notions posed as residual problems; the harness, the adoption tool and
   the checks still have no notion in the state.

## Now

- **#3 is accepted and uncommitted.** Its entry is appended to DECISIONS.md; the entry is the whole deliverable and
  no theory changed. It goes in with whatever commit next takes DECISIONS.md, after #5's.
- **#5 is under way and owns the working tree**, and has been parked since before plan-4. Its own entry, "A formed
  call's applications are constructed, not verified again", is already appended to DECISIONS.md; what remains is its
  check, review and commit. Uncommitted with it: `ROOT`, `THEORY_MAP.md`,
  `theories/Factor_Constructed_Program_Applications.thy`, `theories/Native_Execution_Refinements.thy`. Nothing else
  in the engine line can move meanwhile; if it does not resume, split it over what exists or re-plan it.
- **#4 is running** (efficiency as structure). **#9 is ready** and unblocked by #3's acceptance; when its entry lands,
  read whether it settles the octet direction's task 6 (transport) — that is #9's to say, and it decides whether
  "Not yet planned" item 7 stands.
- `tools/__pycache__/build.cpython-314.pyc` is tracked and shows as modified. It is a generated build artifact, it
  belongs to no task, and it should be untracked by the next commit that touches `tools/`; it is not a question for
  the owner. `.claude/orchestration/base_pack.py` is the orchestration's own and belongs to whatever changed it.
- plan-5 handled its only event (#3 finished), accepted it, created #11 and left nothing unhandled.
