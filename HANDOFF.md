# Handoff

The history of every rotation is in git and in `.build/handoff-archive/` (the last long form:
`HANDOFF-impl30-20260919.md`); what is settled is in native_control_plan.md, REASONING_REUSE.md, DECISIONS.md and
THEORY_MAP.md. The owner's directions and open questions are in `.claude/orchestration/owner-ledger.md`.

## Work order

- Task: T2 Attribute the cost of a native definition over a whole state and decide its refinement (design)
- Serves: the open items of the plan sections "Calls are keyed where they differ" and "The reach of a state is a
  native definition": every native definition over a whole state (the verdict's closedness, request construction)
  pays the context in every call; the machinery reach takes 171.8 s natively against 0.99 s in HOL. A cost the end
  package must pay is fixed now at its cause (owner 2026-09-18).
- Deliverable: a plan section (and a DECISIONS.md entry if a choice between presentations is made) stating the
  measured cause of the per-call cost of the machinery reach (calls, and per call: formation of the values bound and
  of the call terms, instance checks comparing constructed terms with bound values, set operations comparing calls
  left first, the store search, the rounds of the evaluation) and the refinement decided, with its contract, where it
  is applied, its expected effect and the bound T3 must meet. Candidates: formation checked once for calls demanded
  from formed requests; applications constructed by matching accepted without re-verifying what construction
  guarantees; every set of calls keyed; semi-naive evaluation; or a state's rows installed as ground clauses so that
  calls carry keys, not the table.
- Acceptance: the attribution rests on a profile and stage timings taken on base ao (not on reasoning alone); the
  decision says which cost each refinement removes and why it is at the cause; the section records the choice as a
  residual.
- Inputs: `.build/impl30/reachprof/P30_Reach_Measure.thy` (prepared: `ML_Profiling.profile_time` of the machinery
  reach closure; run it with `tools/probe_theories.py --parallel-proofs 0`, one probe per directory, tight timeout);
  `theories/Native_Table_Reach.thy`, `theories/Isabelle_Native_Reach.thy`, `theories/Keyed_Native_Evaluation.thy`,
  `theories/Keyed_Demanded_Sites.thy`; the evaluation's code: `finite_program_applications`
  (Factor_Finite_Program_Applications), `finite_admitted_schema_instance`, `finite_requested_schema_applications`,
  `keyed_program_evaluation`.
- State: T1 committed and pushed ("Key calls where they differ and define the reach of a state natively"); the
  active base is `.build/check-20260919ao/proof`, retained. T2 not started; nothing runs.

## Queue

- T3 Build the refinement T2 decides. Deliverable: proved code equations (or the decided presentation) in
  theories/, a check with every recipe word equal, the machinery reach measured against the bound T2 states,
  committed. Inputs: T2's section. Follows T2, its only input.
- T4 Design the verdict of a kind as a native definition (design). Deliverable: a plan section: the rows of a
  state the verdict reads (kind status, declared constant, subjects and mentions as structure; the statement inert,
  as its local presentation, so rows compare across the request and answer states by equality), each field of the
  verdict as a native program over request and answer rows (what may not change persists, additions are permitted,
  the demanded statement exists, the support bounds the answer's equations, the answer state is closed by the native
  reach and keeps the roots), and its contract against `development_verdict_accepted` of the HOL verdict. Inputs:
  Development_Refinement_Verification, Native_Table_Reach, impl-28's design note (archived handoff, lines 195-202).
  Follows T1 (reach) and T2 (how rows are presented). Why here: the next native definition of the Q7 order
  (provisional; basis: the owner's direction of 2026-09-19 and the ledger's Q7).
- T5 The closure assessment of a state as native programs. Deliverable: native programs over T4's entity rows for
  reached entities (a declaration's constant reached, or some subject reached, via the native reach), undeclared
  constants, malformed entities and unknown positions, with contracts against `isabelle_context_assessment`, checked
  and committed. Inputs: T4's section, Native_Table_Reach. Follows T4; the smallest part of the verdict's reading.
- T6 The verdict of a kind as a native definition. Deliverable: the verdict's fields as native programs with the
  contract of T4, the native judgment of native answers consuming it, recipe words re-recorded, checked, committed.
  Inputs: T4, T5. Follows T5.
- T7 Request construction as a native definition. Deliverable: support (the constants the refined entities
  mention) and the least context as native programs over the same rows, contract against
  `development_refinement_request`, checked, committed. Inputs: T4-T6. Follows T6 (same rows and reach); the last
  loop notion the Q7 order names before native problems.
- T8 Design problems whose subjects are native definitions, answered natively (design). Deliverable: a plan section:
  how the loop poses a problem about a native definition, what its packet carries, how a native answer is judged by
  native programs, and where translation into Isabelle enters (only to verify). Inputs: the plan sections "Native
  definitions are normative" and "Answers are native content"; the owner's answer to Q7 if given. Follows T7
  (provisional, Q7 order); an owner answer to Q7 can move it forward.

## Open

- Q1 Is Isabelle's acceptance of an answer's checked context, judged by the predecessor-built verdict, the admission rule for adoptions before genesis (OD-2)?
- Q2 Are the measured paused candidates authorized as first-loop problems, and is a cost criterion authorized for selection?
- Q3 Should the workflow document read Isabelle as establishing truth and formal adequacy only, adequacy to intent being a current basis under the owner?
- Q4 May the harness run a model as an inert executor on packets, with no tools and nothing but the packet as input?
- Q5 How far should the native residual record reach: the loop's notions by demand, every constant since c4dfad1, or the whole workspace?
- Q7 Is the order native readiness, verdict, request construction, native problems, translation the intended one, and should the loop keep posing problems about HOL constants?
