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

**The Q7 line (3, 9, 10, then the builds).** #3 designs the verdict of a kind as a native definition over structural
rows, folding in the paused structural-Isabelle-state work by demand. #9 designs the development notions themselves
as structure — problems, requests, answers, packets — which is the octet direction's task 3, promoted because two
build lines need it: the decomposition's schema matches on problems, and the verdict and request construction read
them. #10 briefs the decomposition's build.

**#4** (efficiency as structure, the octet direction's task 5) is ready and independent of both lines; its instances
are the refinements imported through `Native_Execution_Refinements` together with #5's and #7's — six, past first
use. It blocks nothing, and every further refinement is another instance, so it stands last and loses nothing by it.

Order (queue `5 6 7 8 3 9 10 4`): the owner's latest directions first, then dependency, then what can change other
tasks, then size. The engine line leads because both design lines rest on its measurement for their builds; #9 waits
on #3 so that it inherits the row treatment rather than deciding it twice; #10 waits on #9 and #8. #9 and #10 precede
#4 (plan-4, reordering the tail the appending of #9 and #10 had left).

## Decisions

Taken by the planning episodes, where they are not entries of DECISIONS.md:

- **The Q7 order stands provisionally, with the engine's cost before its second step.** Basis: T2's measurement and
  the owner's 2026-09-18 direction on inevitable costs. An owner answer to Q7 reorders the whole graph.
- **Order is the queue's; a blocker records a dependency on an artifact, not a wish about order.** A design is not
  blocked on a measurement it does not consume: what #3 must respect is that the verdict is a definition over a whole
  state, not the number. The number decides whether its *build* can follow.
- **No new native definition of a development notion is built over the tagged-tree presentation.** The decomposition
  entry presupposes the presentation its schema ranges over and does not define it; building over the present one
  would put a new use of octets as structure into new code, against the owner's direction of 2026-09-19 07:34. Hence
  #9 before #10.
- **Q2 is extended rather than split.** The decomposition raises three policy criteria of Q2's own family; they are
  recorded in the ledger under Q2 with their provisional choices, not asked as a new question.
- **#9 and #10 before #4, and any later refinement after #4.** #9 is the prerequisite of the decomposition's build
  and of the verdict's and request construction's builds; #10 creates that build's tasks; #4 unlocks nothing and
  grows richer with every further instance. The reverse order was an artifact of appending #9 and #10 to the tail,
  not a decision. Its one constraint: a refinement written after #4's entry must apply its notion, so the conditional
  store-search task (if #7's measurement makes it one) follows #4 rather than adding a seventh un-factored instance.
- **No task rests on reasoning not yet written.** The verdict's build, request construction, native problems and the
  translation wait for #3's and #9's entries; the third engine refinement waits for #7's measurement.

Settled and written elsewhere: DECISIONS.md holds every batch's decisions in order, 191 entries; the newest are "A
problem is decomposed through the constants its answer needs" (the decomposition design, #2), "A native definition
over a state re-verifies its context in every call", "The reach of a state is a native definition", "Calls are keyed
where they differ".

## Delivered

- **#1 (brief)** produced the engine line, #5 through #8.
- **#2 (design), accepted and committed 2026-09-20 as `0ac9502e`** — DECISIONS.md, 191st entry, 157 lines. A decomposition is a row of the
  development library that is an obligation reduction of the parent's contract to its subproblems', presented as an
  application of one Factor schema over the native presentation of problems; `L` was merely empty and
  `development_loop_issue` already takes it. Composition is `obligation_reduction_discharge`, `inference_sound` with
  `inference_closure_sound`, `obligation_reduction_compose` with `obligation_substitution` for depth, and
  `schema_graph_development_complete` for the tree. Soundness is the schema's, proved once and consumed by every
  application. It corrected its own brief: `development_request_context_least` proves no decomposition shrinks a
  one-constant request, so an oversized context decomposes the problem instead. The answer frame's one-equation limit
  stays unlifted by design. Its six follow-ups are #10's subject. Verdict: `.build/tasks/2/verdict.md`.

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
- **Q5** how far the native residual record reaches. Bites in #3 and #9, which grow the structural state and the
  structural notions by demand on the same principle.
- **Q7** the order of work under the direction that native definitions are normative. It orders this whole graph; an
  answer reorders it.

Not yet planned, in the order they are expected to be planned:

1. The verdict's build and request construction (after #3's and #9's entries; the old T7-T9).
2. Problems whose subjects are native definitions, answered natively, and the translation of admitted native content
   into Isabelle material — the owner's direction of 2026-09-19 06:21 and the last step of the Q7 order (the old T10).
3. A proof request class, and with it the decomposition of a proof problem, which the decomposition entry names and
   leaves undesigned for want of it (refinement and definition problems are requested and judged; a proof problem is
   not). It needs request construction (item 1) for its support and least context, and its first question is what the
   native content of a proof answer is: the library holds native derivations, certificates and replay for calls of
   native programs, while a contract proved against a HOL counterpart is Isabelle material by nature. That question is
   the owner's direction of 2026-09-19 06:21 met head-on, and it is where Q1 bites.
4. The refusal that an absent certified generation cannot tell from an unavailable input: an empty result and a
   failed one are kept apart everywhere else in the library, and not here.
5. A persistent native published state for the refinement layer: without one, an adoption records the transaction of
   its judgment rather than one against a history, and a later selection cannot supersede an earlier one.
6. The octet direction's task 6 (transport: packets and answers travelling as the complete data of their artifacts,
   the word inert carriage) — unless #9 settles it, which is #9's to say.
7. The plan's stages 4 (policy extended from owner directions) and 5 (the machinery improving itself through the
   process), not begun beyond the machinery's notions posed as residual problems; the harness, the adoption tool and
   the checks still have no notion in the state.

## Now

- **#5 is under way and owns the working tree**, parked (13 minutes at plan-4's start, while #3 produces). The
  uncommitted content it finalizes: `ROOT`, `THEORY_MAP.md`, `theories/Factor_Constructed_Program_Applications.thy`,
  `theories/Native_Execution_Refinements.thy`. Nothing else in the engine line can move meanwhile; if it does not
  resume, split it over what exists or re-plan it.
- **#3 is running** (the verdict over structural rows). #9 is blocked on its entry; when it lands, read whether its
  row treatment is stated generally enough for #9 to consume, or only for the state's entities.
- `tools/__pycache__/build.cpython-314.pyc` is tracked and shows as modified. It is a generated build artifact, it
  belongs to no task, and it should be untracked by the next commit that touches `tools/`; it is not a question for
  the owner. `.claude/orchestration/base_pack.py` is the orchestration's own and belongs to whatever changed it.
- plan-4 handled its only event (#2's commit), reordered the queue tail, and left nothing unhandled.
