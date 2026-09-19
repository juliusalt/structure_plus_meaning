# Handoff

The history of every rotation is in git and in `.build/handoff-archive/` (the last long form:
`HANDOFF-impl30-20260919.md`); what is settled is in native_control_plan.md, REASONING_REUSE.md, DECISIONS.md and
THEORY_MAP.md. The owner's directions and open questions are in `.claude/orchestration/owner-ledger.md`.

## The condensation (2026-09-19, the owner with orchestration session 212840df)

The plan's 39 dated sections, the per-batch record of every decision since 2026-09-18 (T2's included), are entries
of DECISIONS.md now, whole, in order, each closing with its date and commit; the plan keeps its structure, the
owner's directions (those of 2026-09-19 quoted verbatim), where the stages stand, and the direction of the work.
REASONING_REUSE.md's per-theory rows are in their theories' THEORY_MAP.md rows (what the row already said left out).
From now on each batch records what it settles once, where it is read (DEVELOPMENT_WORKFLOW.md): its decisions as an
entry of DECISIONS.md, a theory's reuse in its THEORY_MAP.md row, the evidence also in its commit message, what
remains in the graph; the plan changes only with its structure, the stages' standing or the direction of the work.
Uncommitted, beside T3's edits: native_control_plan.md, DECISIONS.md, REASONING_REUSE.md, THEORY_MAP.md,
DEVELOPMENT_WORKFLOW.md, this file. Commit the condensation on its own before T3's commit, so that T3's commit takes
only T3's changes (T3's THEORY_MAP.md row, the Factor_Constructed_Program_Applications line, is T3's: stage
THEORY_MAP.md without it).

## Work order

- Task: T3 Construct a formed call's applications, list a demand's applications and read premise functionality by rows
- Serves: the first step of T2's decision "A native definition over a state re-verifies its context in every call"
  (an entry of DECISIONS.md since the condensation, uncommitted until T3's commit): every native definition over a
  whole state pays the re-verification of the context each call carries.
- Deliverable: a theory (proposed `Factor_Constructed_Program_Applications`, imported by Native_Execution_Refinements)
  with: `finite_pattern_fits` (the shape of a pattern: pairs and literal leaves); its contracts
  (`finite_pattern_instance (finite_matching_bindings p t) p t` iff fits; acceptance of a formed term iff fits and
  `relation_rows_functional` of the match's rows; bound values of a formed term are formed; instances of formed
  patterns with formed values are formed); the per-clause characterization of `finite_requested_schema_applications`
  and of `finite_admitted_schema_instance` for formed calls (via `finite_requested_instance_reading` and
  `schema_instance_exists`); `finite_constructed_applications P d t` equal to `finite_program_applications P {|(d,t)|}`
  for a formed program and call; the code equation `fset (finite_program_applications P D)` as the listed image union
  over D (formed calls constructed, unformed ones empty; an unformed program empty); and `finite_premise_functional`
  executed as `finite_relation_functional` (rows).
- Acceptance: serial probe loads every proof; on the probe the seed's and the machinery's reach return the same
  constants and their times are recorded against T2's table (closure 3.8 s, evaluation >640 s on the machinery);
  `incremental_check.py check --advance-base` accepted with every recipe word equal (pure refinement), retained;
  answers replayed; T3's entry in DECISIONS.md (T2's is already there); its THEORY_MAP row with its reuse; commit
  and push.
- Inputs: T2's decision (DECISIONS.md); `theories/Factor_Finite_Program_Applications.thy`, `Factor_Requested_Applications.thy`,
  `Factor_Requested_Application_Readings.thy`, `Factor_Instantiated_Premises.thy`, `Factor_Executable_Matching.thy`,
  `Finite_Relation_Functionality_Execution.thy`, `Listed_Set_Unions.thy`; the probe
  `.build/impl31/t2/P31_Engine_Profile.thy` (machinery and seed reach; drop its `applications_of`, whose `fcard`
  compares all applications pairwise).
- State: T2 done; its decision is an entry of DECISIONS.md (uncommitted). T3 INSTALLED, UNCOMMITTED: `theories/Factor_Constructed_Program_Applications.thy`
  (every proof loads on a serial probe), ROOT (after Listed_Set_Unions), Native_Execution_Refinements import, THEORY_MAP row;
  source copy `.build/impl31/t3/`. Measured (probe `.build/probe-impl31-d`, P31_T3_Measure): seed closure 0.014 s (was 0.063),
  seed evaluation 0.403 s (was 1.224), equal to HOL; machinery closure 0.784 s (was 3.83); machinery evaluation: machinery evaluation seconds 43.812 result 217;machinery equal true; (log `.build/probe-impl31-d/probe.log`). Probe `.build/probe-impl31-e`
  (seed evaluation profile on the new code, for T4) was running (`.build/impl31/probe-e.out`). NEXT: `python3 -B
  tools/incremental_check.py check --advance-base --output .build/check-20260919ap` in the background (every recipe word
  must be equal), `retain`, replay (`tools/replay_development_answers.py --output .build/impl31/replay-b`), fill EVIDENCE
  in `.build/impl31/docs/t3-plan.md` and append it to DECISIONS.md as an entry (its heading without the date, closing
  "Recorded 2026-09-19, commit `…`." as the moved entries do); put what `t3-rr.md` states beyond T3's THEORY_MAP row
  into that row; write the commit message (style of c11eea1e), commit, push. Never wait with `pgrep -f PATTERN` inside a command containing PATTERN.

## Queue

- T4 Evaluate over the positions of the demanded calls. Deliverable: the keyed evaluation's rule table renamed by
  the injective map (demanded call to its position through the ordered tree of the demand's keys, any other call to
  itself), contract by `finite_inference_result_renaming`, as code equations of the stage and evidence evaluations;
  a check with every word equal; the machinery reach measured against T2's bound (5 s) and the share of key
  comparisons recorded, deciding whether the store search takes its store before its key (T5). Inputs: T2's
  decision (DECISIONS.md), T3's theory. Follows T3 (the rule table it renames is T3's listed table).
- T5 (only if T4 finds key comparisons dominant) The store search takes its store before its key. Deliverable:
  Native_Path_Stores' search rules and the readiness and reach programs re-stated with their contracts, recipe
  words re-recorded, checked, committed. Inputs: T4's measurement. Follows T4, which decides whether it is needed.
- T6 Design the verdict of a kind as a native definition (design). Deliverable: a DECISIONS.md entry: the rows of a
  state the verdict reads (kind status, declared constant, subjects and mentions as structure; the statement inert,
  as its local presentation, so rows compare across the request and answer states by equality), each field of the
  verdict as a native program over request and answer rows (what may not change persists, additions are permitted,
  the demanded statement exists, the support bounds the answer's equations, the answer state is closed by the native
  reach and keeps the roots), and its contract against `development_verdict_accepted` of the HOL verdict. Inputs:
  Development_Refinement_Verification, Native_Table_Reach, impl-28's design note (archived handoff, lines 195-202).
  Follows T4 (native definitions over states usable). Why here: the next native definition of the Q7 order
  (provisional; basis: the owner's direction of 2026-09-19 and the ledger's Q7).
- T7 The closure assessment of a state as native programs. Deliverable: native programs over T6's entity rows for
  reached entities (a declaration's constant reached, or some subject reached, via the native reach), undeclared
  constants, malformed entities and unknown positions, with contracts against `isabelle_context_assessment`, checked
  and committed. Inputs: T6's entry, Native_Table_Reach. Follows T6; the smallest part of the verdict's reading.
- T8 The verdict of a kind as a native definition. Deliverable: the verdict's fields as native programs with the
  contract of T6, the native judgment of native answers consuming it, recipe words re-recorded, checked, committed.
  Inputs: T6, T7. Follows T7.
- T9 Request construction as a native definition. Deliverable: support (the constants the refined entities
  mention) and the least context as native programs over the same rows, contract against
  `development_refinement_request`, checked, committed. Inputs: T6-T8. Follows T8 (same rows and reach); the last
  loop notion the Q7 order names before native problems.
- T10 Design problems whose subjects are native definitions, answered natively (design). Deliverable: a DECISIONS.md
  entry:
  how the loop poses a problem about a native definition, what its packet carries, how a native answer is judged by
  native programs, and where translation into Isabelle enters (only to verify). Inputs: the DECISIONS.md entries "Native
  definitions are normative; Isabelle verifies them" and "Answers are native content, judged natively", and the plan's
  direction of the work; the owner's answer to Q7 if given. Follows T9
  (provisional, Q7 order); an owner answer to Q7 can move it forward.

## Open

- Q1 Is Isabelle's acceptance of an answer's checked context, judged by the predecessor-built verdict, the admission rule for adoptions before genesis (OD-2)?
- Q2 Are the measured paused candidates authorized as first-loop problems, and is a cost criterion authorized for selection?
- Q3 Should the workflow document read Isabelle as establishing truth and formal adequacy only, adequacy to intent being a current basis under the owner?
- Q4 May the harness run a model as an inert executor on packets, with no tools and nothing but the packet as input?
- Q5 How far should the native residual record reach: the loop's notions by demand, every constant since c4dfad1, or the whole workspace?
- Q7 Is the order native readiness, verdict, request construction, native problems, translation the intended one, and should the loop keep posing problems about HOL constants?
