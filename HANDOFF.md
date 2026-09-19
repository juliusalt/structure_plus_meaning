# Handoff

The planner's state: the graph and why it has this shape, the decisions, what each finished task delivered, the
open questions, and what an episode left unhandled. What is settled is in DECISIONS.md, native_control_plan.md,
THEORY_MAP.md and REASONING_REUSE.md; the owner's directions and the questions that are the owner's are in
`.claude/orchestration/owner-ledger.md`; the history of every rotation is in git and in `.build/handoff-archive/`
(the last long form: `HANDOFF-impl30-20260919.md`).

## Graph

The orchestration's first planning episode (plan-1, 2026-09-20) built this graph from the plan's "Where the stages
stand" and "The direction of the work", DECISIONS.md, the owner's directions of 2026-09-19, the commit history since
the plan's base `c4dfad1`, and the last implementer's work order, which it re-formed.

**Why this shape.** Two owner directions of 2026-09-19 set the work. Native definitions are normative and Isabelle
verifies them, which ordered the loop's notions as native definitions — readiness, the verdict of a kind, request
construction, then problems whose subjects are native definitions, then translation into Isabelle (Q7). And structure
is explicit while octets are inert, six tasks of which the audit and its criterion are done. Between the development
and both directions stands one measured obstacle: a native definition whose argument is a whole state re-verifies the
context every call carries, measured at 171.8 s against 0.99 s in HOL. The verdict and request construction are
exactly such definitions, and condition 5a — real development at acceptable observed cost — has no answer while it
stands. So the engine's cost is first, and the verdict's design waits on its measurement.

Four tasks:

- **#1 the engine (brief, unblocked).** The installed applications theory finalized, then the evaluation over the
  positions of the demanded calls, with the measurement that decides whether a third refinement follows. It owns the
  working tree, which holds that installed theory.
- **#2 decomposition (design, unblocked, parallel to #1).** The loop has no decomposition, so every problem is a leaf
  and depth — the owner's stated method — is unmet; the same gap appears from the answer's side as the frame that
  states one equation. It depends on nothing in the engine line, so it runs alongside it.
- **#3 the verdict (design, after #1).** The Q7 order's next notion, with the state's rows made structure by demand,
  which is where the octet direction bites.
- **#4 efficiency as structure (design, after #1).** The octet direction's task 5, overdue by the repository's own
  first-use rule at the third refinement of one engine.

**Order** (`v2.py queue 1 5 6 7 8 2 3 4`). #1 first: the owner's standing direction that a cost the finished package must pay
is fixed now at its cause, the uncommitted work it holds, and the measurement every later task's affordability rests
on. #2 second because it is the only task independent of that measurement and the owner's method requires it. #3
third: the Q7 order's next step, the owner's latest direction. #4 fourth: the same direction's task 5.

**Departures from the superseded queue** (the last implementer's T3–T10; git and `.build/handoff-archive/` keep it):

- T3 and T4 become one brief (#1): one line of engine work, one detailing, with the measurement returning to the
  planner.
- T5 (the store search taking its store before its key) is not created: it is conditional on #1's measurement, and
  creating it now would presume that measurement.
- T6 becomes #3, strengthened: the state's rows as structure, that is, the paused octet-direction task 2 folded in by
  demand rather than built ahead, reusing the worked design that was handed off before it was paused.
- T7–T10 are not created: they rest on #3's entry, which will be their input as an artifact. Creating them now would
  rest them on reasoning not yet written. The next episode plans them from #3's entry and #1's measurement.
- Added #2 (decomposition) and #4 (efficiency as structure), which the queue did not hold; both answer owner
  directions the queue left uncarried.

**plan-2 (2026-09-20)** kept that shape and detailed #1: #5 finalizes the installed applications theory, #6 reviews it,
#7 evaluates a native program over the positions of its demanded calls, #8 reviews that; each review is blocked by its
build, #7 by both. Two premises plan-1 wrote above are corrected. Order is the queue's, not the blockers': #3 and #4
stay blocked by #1 alone, because the queue already puts them after #8, so #7's measurement reaches them in fact, and a
blocker would say falsely that a design cannot be written if the engine line is dropped or re-ordered. And #4 does not
need a third engine refinement as its third instance: the refinements imported through `Native_Execution_Refinements`
-- linked record candidates, investigation basis sharing, invariant evaluation sharing, formation-once readings -- with
#5's and #7's make six, which is past first use rather than short of it.

## Decisions

- **The Q7 order stands provisionally, with the engine's cost taken before its second step.** Basis: every remaining
  notion of that order is a native definition over a whole state, and at 171.8 s that shape is unusable; the owner's
  direction of 2026-09-18 makes such a cost one that is fixed now at its cause. The order itself is the ledger's Q7,
  unanswered. (plan-1, 2026-09-20)
- **The stage-2 open items the old queue dropped are not dropped.** Decomposition is #2. The refusal that an absent
  certified generation cannot tell from an unavailable input, and the absence of a persistent published development
  state for the refinement layer, are recorded under Open and take their turn after #3. (plan-1, 2026-09-20)
- **Nothing is planned that rests on reasoning not yet written.** A task's inputs are artifacts; a decision that a
  later task must respect is an entry of DECISIONS.md written by a design task, not a predecessor's reasoning.
  (plan-1, 2026-09-20)
- **Order is the queue's; a blocker records a dependency on an artifact.** A task is blocked when it needs something
  that must first exist, not when it should merely come later. Ordering lives in `v2.py queue`, which re-orders freely,
  while a blocker encoding order would misstate what a task can be written from. (plan-2, 2026-09-20)
- **The third engine refinement -- the store search taking its store before its key -- is not a task until #7's
  measurement.** #7 brings the measurement and the share of key comparisons to the planner, #8 judges both against the
  probe rather than against #7's report, and the task is created then if that share is dominant. (plan-2, 2026-09-20)
- **The decomposition's build is ordered after the engine measurement, not with its design.** design-2 found that the
  schema's applications are generated by a native question over the problems and the state, so its argument is a whole
  state and the 171.8 s bounds it exactly as it bounds the verdict's. #2 finishes as a design; the build's brief is
  blocked by #2's accepted entry and by #8. (plan-2, 2026-09-20)
- Settled decisions are entries of DECISIONS.md; a theory's reuse is its THEORY_MAP.md row; the plan changes only
  with its structure, the stages' standing or the direction of the work (DEVELOPMENT_WORKFLOW.md).

## Delivered

- **T2 (commit `c11eea1e`).** Calls keyed where they differ; the reach of a state defined natively. It measured every
  native definition whose argument is a whole state: the machinery's reach at 171.8 s natively against 0.99 s in HOL,
  closure 3.8 s, evaluation over 640 s. Its decision is DECISIONS.md's "A native definition over a state re-verifies
  its context in every call"; that measurement is the reason for #1 and the bound for #3's affordability.
- **T3, installed and not finalized.** `theories/Factor_Constructed_Program_Applications.thy` with its `ROOT` entry
  after `Listed_Set_Unions`, its import in `theories/Native_Execution_Refinements.thy` and its `THEORY_MAP.md` row;
  every proof loads on a serial probe. Measured (probe `.build/probe-impl31-d`, log `probe.log`; source copy
  `.build/impl31/t3/`): seed closure 0.014 s (was 0.063), seed evaluation 0.403 s (was 1.224) and equal to HOL,
  machinery closure 0.784 s (was 3.83), machinery evaluation 43.812 s with 217 results and equal to HOL. #1 finalizes
  it: check with every recipe word equal, answers replayed, its DECISIONS entry and THEORY_MAP row.
- **#1 (brief).** Tasks #5-#8: #5 finalizes the installed applications theory with its check, DECISIONS entry,
  THEORY_MAP row and commit; #6 reviews that finalization; #7 evaluates a native program over the positions of its
  demanded calls; #8 reviews it and its measurement. No task for the third refinement: it is the planner's, on #7's
  measurement.
- Everything committed before that is in DECISIONS.md, whose entries carry each batch's decisions, evidence and
  limits in order; the condensation of 2026-09-19 (`b1ded6c2`) moved the plan's dated sections there and the
  per-theory reuse rows into THEORY_MAP.md.

## Open

The owner's questions, each with the provisional choice that stands meanwhile, are in the ledger; where each bites now:

- **Q1** the admission rule of a bootstrap adoption and OD-2. Bites when an admitted native answer is installed as
  Isabelle material — the request class the Q7 order names last.
- **Q2** authority of the first loop's problems and its selection criterion. Bites in #2, which must say what
  requirements a decomposed problem meets, and in any selection beyond readiness.
- **Q3** what Isabelle establishes about adequacy. Bites when DEVELOPMENT_WORKFLOW.md and plan.md §0.1 are next
  touched; unplanned.
- **Q4** an agent executor confined to its packet. Bites at the plan's stage 3 gate; unplanned.
- **Q5** how far the native residual record reaches. Bites in #3, which grows the structural state by demand on the
  same principle.
- **Q7** the order of work under the direction that native definitions are normative. It orders this whole graph; an
  answer reorders it.

Not yet planned, in the order they are expected to be planned:

1. The decomposition's build (after #2's accepted entry and #8). Its three known parts, from design-2: the schema and
   the native presentation of problems it ranges over; the repair's derived definition problems recorded as a row of
   the library rather than as empty-premise rows answered in the same breath, so that the loop's only computed
   decomposition comes out as an application of the general schema -- this part is not additive-only and its review
   checks that preservation; and the request and packet changes the decomposition forces, namely a request named by its
   problem's locus rather than by its subject constant (`development_named_request` otherwise finds several and answers
   none) and a packet stating the kind and the declared form. The Isabelle frame reading its demanded part by the kind
   waits for the installation request class, and the one-equation limit of a refinement's contract stays unlifted by
   design, because the decomposition makes a multi-constant refinement never reach an executor.
2. The verdict's build and request construction (after #3's entry; the old T7-T9).
3. Problems whose subjects are native definitions, answered natively, and the translation of admitted native content
   into Isabelle material -- the owner's direction of 2026-09-19 06:21 and the last step of the Q7 order (the old T10).
4. The refusal that an absent certified generation cannot tell from an unavailable input: an empty result and a
   failed one are kept apart everywhere else in the library, and not here.
5. A persistent native published state for the refinement layer: without one, an adoption records the transaction of
   its judgment rather than one against a history, and a later selection cannot supersede an earlier one.
6. The octet direction's tasks 3 (structural development notions) and 6 (transport), after the notions of task 4 are
   native.
7. The plan's stages 4 (policy extended from owner directions) and 5 (the machinery improving itself through the
   process), not begun beyond the machinery's notions posed as residual problems; the harness, the adoption tool and
   the checks still have no notion in the state.

## Now

- #5 is under way and owns the working tree. The uncommitted content it finalizes: `ROOT`, `THEORY_MAP.md`,
  `theories/Factor_Constructed_Program_Applications.thy`, `theories/Native_Execution_Refinements.thy`.
- #2 is running. When it finishes, judge it (`v2.py verdict 2`) and read whether its entry says which native
  presentation of problems its schema ranges over: plan-2 asked for that in answering its finding. If the entry leaves
  it to the octet direction's task 3, that presentation is the decomposition build's first prerequisite.
- `tools/__pycache__/build.cpython-314.pyc` is tracked and shows as modified. It is a generated build artifact, it
  belongs to no task, and it should be untracked by the next commit that touches `tools/`; it is not a question for
  the owner. `.claude/orchestration/base_pack.py` is the orchestration's own and belongs to whatever changed it.
- plan-2 answered both questions it was given -- q1 on #3's and #4's blockers and on the third refinement, q2 on the
  decomposition's cost and on what its entry must state -- and left nothing else unhandled.
