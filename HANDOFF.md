# Handoff — the native loop verifies, repairs, admits and issues; adoption open

Checkpoint: 2026-09-18, second session of the day. Read [AGENTS.md](AGENTS.md) and
[DEVELOPMENT_WORKFLOW.md](DEVELOPMENT_WORKFLOW.md) first. The owner's current goal is implementing
[native_control_plan.md](native_control_plan.md) (the plan is broad structure, not source of truth);
its last three sections record what this session established and what is open. Do not drift into
optimizing validation fixtures: the owner stopped that twice; work on plan items directly.

## State at this checkpoint

Everything below is committed and validated by the repository check `.build/check-20260918m`
(accepted, heapless, 41 s: every recipe word as recorded, 165 tool tests and 35 kernel tests). The
active base (`/tmp/structural-active-context.json`) is `.build/check-20260918k/proof`, a chain of
nine levels back to `.build/overnight-20260918/proof`; stop advancing it on routine checks and reset
it with a complete proof when the chain's cost shows.

- Native questions settle through ordered keys (`Keyed_Native_Evaluation` over the source-shared
  workflow equations; `Ordered_Member_Trees` is the one member index): a decision over sixteen
  candidates fell from 7.2 to 4.8 s. What remains is attributed: the scope-review stage settles a
  product demand of 14,289 calls for 4,765 settled ones; nothing else is large.
- The verifier: `Isabelle_State_Difference` (two states through the names they share),
  `Development_Refinement_Verification` (verdict and local contract), `Development_Refinement_Repair`
  (a refused answer's extension, revised request, definition problems, conservativity verdict).
- The loop: `Development_Decomposition` (library rules apart from prerequisites; issuing only
  leaves; broad requests refused), `Development_Successor` (admission as a generation under the first
  loop's policy, whose converse `development_policy_admits_member` is now proved; successor with
  transported readiness; history of selection, issue, answer and repair records; concurrent
  admission of independent answers; re-evaluation of absence readings), `Development_Request_Packets`
  (the executor's packet as the exporter's inverse reading).
- The seed recipe presents the verification controls and the recorded selection, issuing (empty
  library and a cyclic control library), re-evaluation and succession.
- Tools: `tools/development_answer.py packet --state S --subject C --output DIR` presents a request's
  packet; `... answer --answer FILE --output DIR` judges an answer (states `development_seed` and
  `refinement_layer`, the latter deriving a request on demand for any constant of the refinement
  layer); `tools/development_executor.py` answers from a packet alone;
  `tools/replay_development_answers.py --output DIR` reconstructs every retained answer. Seven
  answers are retained in [validation/development-answers](validation/development-answers/README.md).

## Next

1. Adoption: carry an accepted answer into its layer as a repository theory, check that every
   affected report word is unchanged and rank its measured cost; the successor state must then equal
   the adopted state (the replay of the same answer becomes an unchanged answer).
2. Derived decomposition in the library: turn a repair's definition problems into prerequisites
   issued as their own requests (definition requests), instead of answering them with the refused
   answer's text.
3. The native record of residual choices (stage 1/5 gate), owner-authorized policy extension
   (stage 4, needs the owner), agent isolation beyond the deterministic executor (stage 3), and the
   stage-1 provenance and locality items.
4. Pitfalls met this session: never wait or kill with a pattern contained in the command's own
   command line (`pgrep`/`pkill -f`); Isar keywords as labels or variables (`premises`, `context`,
   `record`, `done`) fail far from the cause; `blast`/`auto` on existential goals can run for minutes
   in this heap, so give witnesses; keep a check's inputs fixed while it runs.

## Committed work and validation boundary

53 theories are integrated into `theories/` and `ROOT`, byte-identical to their
accepted overnight providers. The [inventory](validation/overnight-20260918/integration.json)
binds each theory to its original source and provider. A fresh Isabelle/HOL build
checked their entire 1,080-theory closure with zero project theories reused in
311.491 seconds including startup, without session errors. This is a **partial
scope**, not a successful build of the whole `ROOT` session.

Fresh exports match the overnight modules byte for byte. Both the certificate
and material replays match their complete original assessments and native words.
The cleanup retains complete report identities and a source-only reconstruction
boundary. Generated output is rebuilt when needed.

[validation/overnight-20260918](validation/overnight-20260918/README.md) retains
the source closure, native requests, expected complete-report identities, compact
verification and the retirement record. Unique diagnostics/candidates are explicit
source files under `unfinished/`, outside ROOT. Full historical logs, generated
outputs and superseded snapshots remain recoverable from commit `d85a02e`; none is
a current reconstruction input. No old `/tmp` provider or active pointer is needed.

Segment 10 proposed application-result selection and source-reader staging but
left no implemented theory candidate for them.
The missing argument to `Development_Refinement` in `Development_Seed` is repaired
below; the seed recipe's expected reports are still empty placeholders.

## Latest native results

The actual subject is the checked rooted context and complete proposition for
`Original_Union`, with the universally quantified `finite_syntax_join` refinement.
`Native_Control_Syntax_Statements` checks theorem propositions and absence of
hypotheses. This covers neither arbitrary theorems nor every paused refinement.

The admitted root application retains the original quoted guard, four bindings
and all three sockets. Native observation selects `Observed_Parts` under both
original facets. An application is not a root proof.

The certificate review retains all original full/leaf demands and both
`Requested_Certificates` and `Checked_Certificates`. Full children, projection
and quotation have no original two-facet choice. The natural body leaf has a
singleton complete proof-set result, preserved under reversal and duplication.
All absent reports refuse. One quotation control with only
`Requested_Certificates` accepts the supplied original-body report; exact question
equality remains unknown. Do not claim every wrong-report control refused.

The material review, completed after the older handoff, finished quotation and
both body clauses. Projection timed out at 90 seconds and is unresolved. All
15 completed method choices return `None`; multiple satisfactory methods do not
select a unique method. Complete application-value equality is still unknown.
All 15 absent/wrong-body report controls refuse. Timeout supplies no negative
semantic observation.

Guard installation proves source existence and definition-coordinate transport
under its installation premise. Actual source execution timed out: no complete
returned source record was accepted. Definition-site injection does not transport
clause, variable or socket proof coordinates. Certificate/policy continuation
retains actual original proof checking, literal replay and aligned policy/history
premises. No installed guard certificate, replay or governing cause exists.

## The seeded refinement contracts — 2026-09-18

`Development_Seed` applied `Development_Refinement` to no argument, so the theory did not
load and the complete repository check stopped there. That argument is now chosen by
readings computed on the actual seeded state, and the state itself is no longer defined
twice: the theory instantiates the accepted `Native_Control_Seed_Subject` instead of
repeating its exporter.

Three reusable theories carry the account. `Isabelle_Code_Equations` reads the executable
content of an entity, which the existing subject reading cannot distinguish from a kernel
definition. `Filtered_Native_Questions` holds the native question over actual subjects with
a computed condition, extracted from its first use in `Native_Control_Syntax_Candidate`,
which now instantiates it; `Faceted_Native_Questions` was already a second user through the
import chain. `Development_Refinement_Contracts` keeps two readings apart: the scope of a
constant is what the state presents about it, and the demand selects what a refinement must
establish inside that scope. The contract is the single demanded statement under the
existing `list_singleton_option` reading, so a repeated presentation is still one statement
and several distinct statements are refused rather than resolved by position.

Executed on the seeded state inside the checked context: every root constant has a scope of
exactly two entities, its kernel definition and its code equation, and exactly one is
demanded. `native_development_admission` admits exactly the computed demand for all ten
roots. Every root therefore has a contract and none is retained as unstated. The demanded
statements mention no other root, so every computed premise set is empty and the ten
problems are independent; the grouping into three measured candidates asserted a dependency
structure the state's statements do not supply, and the kernel definitions carry a different
relation. Two of the three groupings cover more than one constant and are retained as an
obstruction: the equations are Pure equalities and the table holds no `HOL.Trueprop`, so the
state states no single refinement of several constants.

Scoping the question is also what makes it affordable. Ranging the candidates over all
eighty entities conflates what a problem is about with what its answer must establish, and
that question had not returned after 243 seconds; the scoped question and its admission for
all ten roots complete in 11 seconds including the load. The four new or rewritten theories
check in 3.2 seconds on the accepted base heap.

The contract, scope, demand and dependencies are computed. Selecting these ten root
constants from the measured candidates remains a residual generated outside the process,
and every seeded problem records that origin and generated authority. Nothing here
establishes that an answer satisfies a demanded statement, that these roots are adequate to
the measured candidates, or that any refinement work has been done.

## The seed presentations complete — acceptance consumes its contract

The seed recipe's five rooted-state presentations had each reached the 1200-second timeout,
and their Isabelle processes kept running after it: the runner stopped only the wrapper it
started. Attributed on samples, the whole cost was the acceptance decision. The context term
forms in 0.3 seconds; `isabelle_demand_acceptance` over the 80 entities did not return in
2,281 seconds, and within it only compiling the ground definition was slow (not returned in
1,363 seconds). Clause by clause the compile is quadratic in the term (43.2 seconds for the 80
clauses alone, 13.6 for the largest), and the compiled forest then joins 124,800 carrier
addresses through member-by-member unions of listed sets.

The decision now consumes the notion's contract. `Factor_Finite_Ground_Evaluation` proves
that native evaluation answers every entry demand of an installed ground source, so
`isabelle_demand_acceptance` is total, and `isabelle_demand_acceptance_members` (demanded
entities split by membership in the supplied ones) is its code equation. The seed's
acceptance computes in 0.001 seconds; all seven presentations complete in about 2.2 seconds,
and their boundaries are recorded from that accepted run. The quadratic compile remains a
measured machinery problem for the process (see [REASONING_REUSE.md](REASONING_REUSE.md)).

The first execution also falsified one control. Moving `HOL.eq` observed nothing, because
every definition and code equation of the state is a Pure equality. The controls are now
derived from the reader's `isabelle_equality_names`: without `Pure.eq` twenty entities lose
their subjects and are malformed and seventy are no longer reached; without `HOL.eq` nothing
changes. Timeouts in the recipe, report, execution, check and probe runners now stop the
whole process session (`build.run_session`), and the probe tool resolves a child context's
parent sessions.

## The first loop's selection, group and requests — native and reconstructed

Stage 2 has begun. `Development_Requests` states selection as the filtered native question on
computed readiness, proves admitted problems pairwise independent, and constructs a
refinement request with its demanded statement, support and least context (exact, closed,
least). `Development_Seed_Loop` executes the seed's ten contract decisions and its selection
as native packets and presents them with the admitted group and the ten requests; the seed
recipe reconstructs that report in 9.2 seconds. Settlement in `Development_Problems` was
corrected so that a dependency row fires only for an answered problem, and the generic
admitted-subject consumers moved from `Native_Control_Admitted_Selection` into
`Filtered_Native_Questions`. The repository check of this batch was accepted (145 seconds of
proof for 53 rebuilt theories, one recipe re-executed) and retained. Requests are not issued
yet: the verifier of a refinement answer and the leafhood account come next. A native
question over sixteen candidates costs about 13 seconds; that cost is being removed.

## Rebuild without overnight temporary files

Use Python 3.14 and Isabelle2025-2 (`isabelle` on PATH; the existing runtime helper
expects Poly/ML under `/opt/isabelle`). This is the normative bootstrap toolchain.
Heaps are generated caches. Each output directory must be fresh. Current proof
and replay reconstruction reads only current repository inputs and the toolchain.

```sh
python3 -B tools/materialize_source_boundary.py --project . --manifest validation/overnight-20260918/sources.json --output .build/next-native-source
python3 -B tools/reconstruct_overnight.py prove --output .build/next-native-proof
python3 -B tools/reconstruct_overnight.py export --context .build/next-native-proof --output .build/next-native-exports
python3 -B tools/reconstruct_overnight.py replay certificates --exports .build/next-native-exports --output .build/next-certificates
python3 -B tools/reconstruct_overnight.py replay materials --exports .build/next-native-exports --output .build/next-materials
```

Proof builds directly from HOL without the active-context pointer. Export
verifies/adopts only the new context. Replay loads unchanged historical
request/assessment function ASTs with fresh paths and compares complete
assessment boundaries and native word identities. Material timeout outcomes can change;
review a difference rather than force it to match. Concurrent JVM jobs must
share a process namespace: separate sandbox namespaces can collide in shared
`hsperfdata`. Native per-subject material preparation remains parallel.

The fresh proof can supply `tools/prove_context.py --parent-project` for covered
theories; do not activate it as a full repository context. Useful unaccepted
source is directly inspectable in
[unfinished/](validation/overnight-20260918/unfinished/README.md). It is not part
of the accepted theory scope. No archive extractor or historical heap is needed.

## Remaining obligations and next content batch

1. Submit the application-result-selection gap and source/material bottlenecks
   through the native/bootstrap process. Instantiate faceted/singleton contracts
   with complete values and both original facets; establish their equality and
   observation equations. Expose source-reader/material substages without changing
   the operations. No optimization is selected by this storage consolidation.
2. Construct/check projection and quotation certificates and the full child
   family. Establish natural-to-installed clause/variable/socket proof transport
   or an independently checked native-source construction. Then construct the
   root proof, literal replay and aligned policy cause/history.
3. Preserve every `finite_program_evaluation_ready` premise: formed source,
   coverage of **every** clause at demanded definitions and demand closure.
   The guard lacks head variables `{1,2,3}`; projection needs material variables.
   Source existence or one leaf cannot discharge these premises. Do not increase
   timeouts or weaken checks to bypass the missing account.
4. Establish owner-authorized governing requirements, fixed policy/source/entry,
   authority/current basis, derived support and least contexts, dependency/absence/
   invalidation, recursively admitted selection/scheduling/requests, inert
   executors, predecessor-admitted amendments and first-use factoring.
5. The seed's contract choice is repaired through its native account and its report
   boundaries are recorded from an accepted run, both described above; the complete
   repository check on this workspace is the remaining validation of the item. Conditions 1–4, practical 5a and 6 remain open; theoretical 5b is
   deferred. O-73 stays Open, O-85 Partial, and genesis absent. This checkpoint retains
   reconstruction boundaries; the broader native retention/workflow account is still open.

The old segment-9 retention job and several interrupted/timed-out descendants
lack positive exit evidence in their original PID namespaces. Their records are
preserved; current numeric PIDs are not identities. Current reconstruction does not
depend on them. The owner-requested cleanup removed verified duplicate validation
trees without signalling processes or claiming exit evidence. Original temporary
provider caches remain untouched; their historical paths are not build inputs.
