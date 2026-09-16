# Making native development and validation fast

Updated 2026-09-17 from the accepted incremental cycle and the five-family
shared-presentation batch. Historical measurements remain labeled by their
actual source and execution boundaries.

## Current result

**Five history families now transport their complete presented reports through
shared artifact words, with both the word and original comparison validated on
the same exports. Words range from 160 KB to 552 KB instead of repeating hundreds
of megabytes of artifact data. The accepted incremental validation took 289.87 s;
this excludes the separate probe measurements and the first failed integration
attempt. Digit replay and decision replay remain the main cycle bottlenecks.
The speedup objective is unfinished.**
The previous delivered commit is `4becc454be0d9b7c94d71fff0fe280a4833ee3c3`
(`Remove repeated native execution work across validation families`). Local commits `92cad1e` and `233c1a0` established the incremental cycle and
the required-history presentation pilot. The current batch extends the native
presentation transport to five history families.

The [measurement ledger](validation/reconstruction/native-speedup-observations.json)
retains the latest stage timings, reported outcomes, source identities, cold-suite
logs and readiness failures. It records physical observations, not semantic
admission; its per-recipe entries predate this batch. The
[last complete recipe review](validation/reconstruction/current-verified.json)
and [incremental check receipt](validation/incremental-check.json) describe this
current 1,602-theory workspace.

| Boundary | Latest evidence | What it establishes |
|---|---|---|
| Delivered commit | 1,554 theories accepted; 158 host tests and 95 subtests passed, two optional-dependency skips; all 50 recipes and 5,883 complete records accepted | Proof and complete report reconstruction for `4becc45`; their committed source/tool/log identities were checked against Git contents before push. |
| Accepted base | Complete check accepted **1,589 theories** in the fixed base directory, with source and tool identities equal to the committed build receipt | The proof base for incremental checks; the current workspace is checked by 107 rebuilt contexts and 1,495 reused contexts. |
| Recipe executions | **All 50 recipe boundaries and 5,888 records retained**; five affected recipes executed in this batch; 125 tool tests and 35 kernel tests passed, two optional-dependency skips | The two lost workflow contract registrations are restored in `Native_Workflow_Execution`; `native-workflow` completes. |
| Retained manifests | All 50 source manifests regenerated from the validated workspace | Each recipe's retained verification now binds the exact inputs it was executed with. |
| Incremental validation | `tools/incremental_check.py` validated the incremental-check batch in 831 s, the initial presentation batch in 80 s and the five-family shared-word batch in 290 s against a fixed accepted base | See [Development cycle structure](#development-cycle-structure); the complete build is not part of an ordinary cycle. |
| Presented report | Required, digit, known, quoted and constructed histories retain their complete presented report words beside the unchanged comparisons on the same exports | See [Native report presentation](#native-report-presentation); 45 families still need presented report stages; the five migrated families retain their old comparison stages pending removal. |
| Whole development workflow | Conditions 1, 6 and practical-usefulness gate 5a remain open | Faster native packets and successful fixtures do not establish native-driven refinement selection or acceptable real development throughput. Gate 5b remains deferred until after genesis. |

## Where the time goes

| Measured or recorded boundary | Time | Interpretation |
|---|---:|---|
| Full check for delivered revision, 12 threads | **673.91 s — 11 min 14 s** | 1,554 theories, 14:46:21–14:57:35 UTC. |
| Full check after export-theory split, 16 threads | **625.14 s — 10 min 25 s** | 1,589 theories, 15:23:17–15:33:42 UTC. Source reorganization did not deliver validation in seconds. Different thread/source boundaries prevent treating the difference as a controlled speedup ratio. |
| Export all 50 recipe modules from accepted main build | About **1–2 s** | Reuses the already accepted proof. Export itself is not the multi-minute bottleneck. |
| Earlier split digit-replay check | **997.93 s — 16 min 38 s** | Historical execution/checking stage; four workers. The later shared-tool cycle recorded about 774 s after host corrections. |
| Earlier plain source-only suite | **1,470 s — 24 min 30 s** | 40 recipes accepted on an earlier source revision. |
| Earlier compressed source-only suite | **1,598 s — 26 min 38 s** | 10 recipes attempted; digit replay failed. Together those two suites accepted 49/50, not a complete current cold run. |
| Final delivered check start to commit creation | **35 min 49 s clock span** | 14:46:21–15:22:10 UTC: proof, executions, retries, evidence integration and intervening work. This is not a measurement of the Git commit command. |
| Earlier split check start to last recipe receipt | **About 32 min 22 s observed interval** | Historical interval, 15:23:17–15:55:39 UTC, ending with a missing-contract failure subsequently repaired. |

The cold suites materialized declared source/fixture inputs and rebuilt their
project proofs from HOL without a supplied project heap. This is a source-only
reconstruction boundary, not evidence of an empty operating-system cache or a
fresh Pure/HOL installation. They preceded the final formation/stack fixes;
acceptance of the later main-build exports does not retroactively validate a
current cold reconstruction. The two suite times must not be added as serial
wall time when their work overlapped.

A previous packet-only profile reported complete steering at about **4.9 s**.
The split-era complete steering checker took **27.02 s**, its request roundtrip
**45.10 s**, and its empty-scope check **13.30 s**, under the recorded concurrent
recipe schedule. That source-development check took **38.67 s** and its request
roundtrip **53.04 s**. Native computation, startup, transport, comparison, proof
and final retention are distinct costs. The empty-scope time makes the need to
measure the surrounding process concrete; it does not by itself attribute that
cost to one operation.

There is no isolated timing of Git commit/push or a complete per-phase latency
and peak-memory account for the entire development loop. Those gaps remain
explicit. Native packet ratios cannot stand in for edit-to-accepted-commit time.

## Development cycle structure

The owner requirement is an edit-to-accepted-commit cycle in single-digit
minutes. A complete build (about 600 s) cannot be part of every cycle.

**Measured cycle, this batch.** `tools/incremental_check.py check` validated the
committed workspace against the accepted base in **831 s**: base and impact
0.6 s, incremental proof of 95 changed and dependent theories over 1,495
reused theories 50.3 s, recipe impact 4.1 s, exports 1.3 s, all 50 recipes and
both host test suites 774.4 s. The change touched shared tools and the
refinement bundle, so every recipe was executed. Digit replay (774 s) and
decision replay (399 s) set the recipe phase; every other recipe finished
within 192 s under eight concurrent jobs.

**Complete build profile.** The latest complete build recorded 543 s elapsed
and 3,569 s CPU on 16 threads. Proof methods took 2,099 command-seconds,
`export_code` 1,292 and theory setup 259; HOL-Library theories re-checked inside
the session took 139; two single proofs took 163 s each.

**Host verification.** Before this batch, host verification after the native
process took about 1,100 s across the suite. Each correction reproduces every
retained report boundary exactly:

| Cost | Correction | Effect |
|---|---|---|
| The dictionary reader deep-copied every referenced artifact for each occurrence | Packet and ordered-subject assessments read deferred records whose digests use each dictionary entry's retained encoding; eager readers copy an occurrence by parsing its exact encoding | Known history 147 s to 1.1 s; quoted 101 s to 1.2 s; constructed 171 s to 1.3 s; digit replay 261 s to 6.4 s; history index, digit history, certified causes, required history and certificate replay 0.2-1.7 s |
| `json.dump` streams through the pure-Python encoder | `write_json` encodes with the C encoder and writes identical text | 125 s of native-child reasoning |
| `freeze` rebuilt the same large terms 84,824 times | Results are shared under a lossless `marshal` key | Up to 144 s of native-child reasoning |

**Incremental proof over one accepted base.** Isabelle pairs every session
source hash with its absolute path (`Sessions.sources_shasum`), so an accepted
heap is current only for the directory where it was built. The base therefore
lives in one fixed directory (`/tmp/structural-accepted`).
`incremental_check.py establish` replaces changed files there and runs the
complete check; it is not part of an ordinary cycle. `check` refuses unless the
base heap and database are those recorded at establishment, proves only changed
theories and their dependents through `prove_context.py`, executes every recipe
whose complete source manifest changed together with the host tests, and keeps
retained verification for unchanged manifests; it propagates every failure.
`retain` records executed recipes and `validation/incremental-check.json`. The
dependent closures of the last fifteen commits cost 49-443 command-seconds, and
the whole refinement closure of 95 theories took 50 s.

**Correction: copying a base rebuilt the session.** A dry
`isabelle build -n -d copy` did not report copied sources as unfinished, but a
check inside the copy rebuilt the session and deleted the accepted heap. The dry
run is not a currency check. The base now records its heap and database
identity and refuses a changed heap instead of rebuilding it.

**Native cost after host fixes.** Digit replay is dominated by one context:
contexts 0-5 take 2.6 s together, context 6 takes 687 s single-threaded and the
remaining 17 contexts 179 s. Its profile is dominated by reading joins.
`Factor_Join_Reading_Conditions` decides join admissibility by twelve pairwise
disjointness checks and preserves every result list; it is exact but did not
change digit replay's cost. The refined profile shows the remaining cost is
duplicate elimination while accumulating join results: list-set insertion
compares each new result triple with every accumulated one. Decision replay's
assessments take 78 s for four contexts; its investigation cycles dominate.

**Host transport outside presentation classes.** Reports printed code-generator
representations through host ML and recipes compared those bytes, which fixed the
stored order of finite sets and forbade the ordered or indexed set representations
that would remove the digit replay cost above. The correction is under way; see
[Native report presentation](#native-report-presentation).

## Native report presentation

**Construction.** Presentations name their notions and compose through the
existing pair, sequence, finite-collection and optional-value classes. Coordinates,
goals, generations, proof trees, contexts and investigation packets reuse those
presentations. Stores are identified by their original views, not by a new
identity of their internal layout. Octets, addresses and indices remain distinct
notions even when their HOL carriers coincide; there is no type-class dispatch
for their meanings. Collection ordering supplies an admissible enumeration and
an identifying word, not an invariance claim about programs observing that word.

**Shared artifact words.** Artifacts and targets occur as native target terms.
An environment presents its use/artifact members and binding members. The word
starts with the complete rows of each distinct artifact in first-occurrence
order, then presents target leaves by their table indices and any anchors.
`Complete_Value_References` supplies the exact index contract. The generalized
term-word cancellation lemma consumes that contract on the actual target family;
`finite_term_shared_word_injective` and `finite_term_shared_word_fold_exact`
establish identification and exact streaming of the complete word. Malformed
values and every optional failure level are retained.

The previous unshared digit and known history words were 572.6 MB and 611.6 MB.
The new words below retain the complete presented subjects through direct target
terms and the shared table. These size changes are not timing speedup ratios.

| Family | Complete word bytes | Probe execution (s) | Recipe comparison (s) | Recipe presentation (s) |
|---|---:|---:|---:|---:|
| required-history | 159,908 | 22.06 | 98.58 | 88.24 |
| digit-history | 418,306 | 114.79 | 162.30 | 193.76 |
| known-history | 449,531 | 117.83 | 169.42 | 201.59 |
| quoted-history | 483,348 | 121.46 | 168.75 | 205.84 |
| constructed-history | 551,708 | 126.55 | 175.51 | 212.48 |

Probe executions used two host jobs and sixteen workers per job. The complete
cycle used eight recipe jobs with each recipe's original internal scheduling;
its proof took 70.28 s and its execution/test phase 213.81 s. These overlap with
independent proof preparation and are observed resource boundaries, not isolated
comparative timings. Both host suites passed (125 tools; 35 kernel, two skips).
All five presented words from the real exports matched their probe boundaries,
and every original JSON comparison remained equal. The five added word records
bring the retained inventory to 5,888 records.

The first integration exposed a distinction between exporting theory and emitted
ML structure: known, quoted and constructed histories emit the shared
`Digit_History_Execution` structure. `check_presented_report.py` now records and
checks `--theory` separately from `--module`; all three callers were corrected
as a group. A named probe module did not exercise that actual client boundary.

[Presented history measurements](validation/reconstruction/presented-history-measurements.json)
retain the complete sizes, digests, source identities and validation phases.
The generic host checker packs the native bits and retains their byte boundary;
it does not inspect generated representations or supply semantic verdicts.

**Remaining migration.**

1. Remove the old comparison stages for the five families whose paired stages
   are now accepted. Keep any old renderer modules still imported by other
   families until those callers migrate.
2. Present digit replay next, including every seed, previous source, prepared
   operation, cause diagnostic and source correspondence. Decision replay and
   the history index follow. Reuse complete program, graph, proof and generation
   notions; do not flatten the report into a new host schema.
3. After a family is validated through its presented word, refine the set
   representation that its old JSON order had constrained. Digit replay context
   6 and its reading-join accumulation remain the first major target.
4. Extend presentation to the remaining families and complete the non-recipe
   coverage audit. Profiling may justify preparing term-order keys or complete
   artifact rows once; preserve the existing word by an exact equation whenever
   that is the intended refinement.

## Implementation record and corrections

These changes are delivered in `4becc45`; they are no longer proposed work.

| Implemented mechanism | Preserved contract and effect |
|---|---|
| Shared Eval runtime and controlled output | `native_execution_runtime.py` suppresses ML toplevel printing of bound packets while retaining explicit tagged reports. The earlier scope-repair/literal-replay printing regression is fixed. The long silent packet binding was not reliable evidence of native computation time. |
| Successor-chain record construction | `RRA_Linked_Record_Candidates` constructs candidates from actual record incidences, retaining the original complete record filter instead of enumerating every arity-length list. Formation is established once per read. |
| Ordered investigation rows and shared basis | `Ordered_Finite_Rows` and `Finite_Investigation_Basis_Sharing` preserve exact last-occurrence order, membership, complete profiles, comparisons, repairs and retention while removing repeated quadratic work. |
| Invariant evaluation and prepared reading | `Factor_Invariant_Evaluation_Sharing`, `Factor_Formation_Once_Readings`, and the existing finite judgment-reading refinement share invariant rule families and established formation premises across traversals. All original outputs and refusal levels remain. |
| Constructed development and source admission | The development/workflow/source sharing theories and `Factor_Constructed_Development_Execution` reuse complete actual constructor results under universal equations. Arbitrary or modified submitted reports retain the original independent admission requirements. |
| Complete-value transport and comparison | Artifact/term dictionaries, streamed footer transport, linear term rendering and deferred complete-byte comparison reduce physical repetition. Complete records, order, multiplicity, malformed inputs and reference-integrity failures remain checked. Hashes do not replace semantic or whole-result comparison. |
| Broad export/runtime integration | `Native_Execution_Refinements`, the shared runtime, accepted-main export, explicit worker routing and reusable heaps reach the executable families. Generated code and real executions, not import presence alone, establish application. |
| Digit-replay memory correction | The checker uses four workers; the runtime removes its worker stack cap. This fixes the observed failure, but the complete check still takes over sixteen minutes. Raising every process to sixteen workers is not a remedy. |

The earlier paired native profiles showed large gains across many families.
Intermediate C/L/G/H timings and the original unimplemented-remedy tables are
superseded here by current complete execution data. Historical proofs, report
boundaries and the earlier replay/history performance record remain in Git and
`validation/reconstruction`; they are not deleted merely because their timings
are no longer current.

## What the last split actually achieved

Thirty-five theories mixed reusable definitions/proofs with file exports and
imported the common refinement bundle. The local change moves their content
into `*_Base` theories and leaves export wrappers, redirecting content imports.
The original export-theory names are retained.

At the export-theory split, the source graph had **1,589 theories, 402 theories containing
`export_code`, 86 file-export theories and 50 reconstruction recipes**. The
refinement import closure shrank from the previously measured 296 theories to
**94 including the bundle itself**: 86 exports, five sharing refinements, two
execution bases, and the bundle. The earlier description omitted the bundle
when explaining the total.

This is a dependency-graph improvement. `ROOT` still declares **one Isabelle
session**, `RRA_Factor_Structural_Bootstrap`. That full build took
625 seconds. The fixed-base incremental checker now avoids it in ordinary
cycles; a separate execution session or persistent interactive proof service
has not been implemented.

The earlier split defects were repaired in `92cad1e`: both workflow
registrations are restored, the proof base has its own fixed accepted directory,
recipe impact compares complete manifests, and failed recipes or host tests make
the incremental check fail. Non-recipe entry points remain outside that recipe
check. Current evidence is `validation/incremental-check.json`; the measurement
ledger's earlier 49/50 table is historical and does not describe this batch.

## Remaining work, in useful batches

The immediate priority is the complete validation and commit path. The following
continues the existing plan and owner requirement; it is not native admission of
these candidates. Decisions and corrections still require the applicable native
subjects, computed observations, reusable reasoning and independent criticism.

| Work group | Required outcome and evidence |
|---|---|
| Maintain the repaired split and validation orchestration | Preserve every exported contract and original client entry point; propagate actual failures; demonstrate changed-source, unchanged-source, tool/fixture and missing-input cases. Reuse accepted unchanged inputs and rerun the complete affected checks. Regenerate manifests only for the actual final validated source state. |
| Make proof invalidation follow real dependencies | Establish reusable accepted base contexts and separate execution-layer proof/code work where the dependency boundary permits. The proposed execution session requires distinct theory directories and a shared theory-path/session resolver across `build.py`, `prove_context.py`, `export_proved_code.py`, `proved_code.py`, `investigate.py` and `reconstruction_sources.py`; they currently assume one session and/or `theories/<name>.thy`. A directory split alone is not a validated solution. Preserve normative bootstrap and exact source/tool invalidation. |
| Extend the working incremental development path | Keep an immutable accepted parent distinct from the changed workspace; rebuild changed subjects and actual dependents, export affected modules and execute every affected client. Store exact source/tool/fixture dependencies and complete receipts so unchanged results can be reused soundly. Exercise realistic repeated edits and refusal/repair cycles, not only a no-change fixture. |
| Reduce full and cold validation cost | Build the combined required proof closure once, then reuse its accepted exports across the complete recipe set. Preserve a separate source-only release reconstruction with complete fixture and manifest checks. Remove redundant proofs across storage modes where one actual proof is applicable, without claiming warm reuse is a cold run. Cold/full costs remain optimization targets; moving them out of the inner loop does not meet the whole objective by itself. |
| Remove remaining expensive native/host work | Start from the current costly families: digit replay, decision replay, constructed/digit/known/quoted histories, native-child reasoning, history index and certificate replay. Separate native stages, serialization, parsing, direct comparison and retention before choosing refinements. Remaining source-level leads include repeated family/schema/scoped-reader formation, `finite_join_readings` footprint unions, and grounding/evaluation unions. A refinement that changes finite-set order requires the family's reports to be compared through presented words first; see [Native report presentation](#native-report-presentation). |
| Schedule and retain one complete batch efficiently | Budget native workers across simultaneous recipes and their nested execution groups. Eight outer jobs can launch further processes with their own workers; thread-count settings alone do not establish useful concurrency. Start independent heavy jobs when dependencies allow, overlap independent work with fixed checks, aggregate diagnostics, and retain one reconstructible boundary instead of recopying/rechecking bulk for commit. |
| Demonstrate actual useful development | Measure a real edit through native construction, criticism, admission, installation, subsequent use, proof/export, complete validation and commit preparation. Record latency, memory, storage and failure/repair cost. Routine edits should have a demonstrated seconds-scale feedback path; complete/cold work also needs acceptable observed cost, not just faster packet profiles. |

Do not narrow coverage to the easiest passing recipes. The 50 recipes are not
an audit of every exported operation, all 13 built-in investigations, all direct
check/run/roundtrip clients, or their growth with realistic source/graph/history
sizes. Keep that non-recipe complement explicit. Future mechanisms in
[native_control_plan.md](native_control_plan.md) must enter the same boundary.

## Semantic and validation requirements

[DEVELOPMENT_WORKFLOW.md](DEVELOPMENT_WORKFLOW.md) remains binding: no outside
semantics or reasoning; Isabelle/HOL retains its normative bootstrap role
through genesis. A profile, host table, digest, metadata record or timing does
not establish a native subject condition. The batch review explicitly records
that refinement choices came from host profiles/timings, not a native contract
connecting those observations and candidates to selection. That gap under
conditions 1 and 6 remains; the new documentation does not repair it.

Use `Factor_Development_Cycle`, `Factor_Development_Steering`,
`Factor_Steered_Development` and the source-development cycle for covered native
questions. Scope extensions need actual subjects and computed criticism. For
history producer candidates, reuse `Factor_Digit_History_Result_Candidates` and
its complete original-reference boundary. Factor reusable arguments at first use;
retain all applicable premises and every unresolved native-account obligation.

Each adopted refinement must preserve complete results and independent evidence
checks on original and expanded inputs, including malformed/empty values,
repeated keys and occurrences, changed bindings, missing evidence, stale caches,
miss/eviction, ambiguous choices, deep structures and deliberately defective
controls. Preserve all candidates, facets, refusals, witnesses, ordered ledgers
and optional failure levels. A cached constructor result cannot admit an
arbitrary changed report. Complete reference dictionaries must retain every
original value and reject incomplete transport.

Measure distinct boundaries for proof/build, export/startup, native computation,
reporting, host verification, retention, repeated requests, and edit-to-commit.
Record exact inputs, revisions, worker and concurrent-job settings, warm/cold
state, wall/CPU/GC time, peak memory and bytes where measured. Do not invent
missing phase attribution, add overlapping times as elapsed time, compare
unmatched resource boundaries, or treat timeout as a semantic refusal. Review
combined proof, code, metadata, execution, diagnostics and performance evidence
before adoption. Preserve reconstructible evidence before removing obsolete bulk.

Condition 5a still requires useful real development with quality at acceptable
observed cost. Condition 5b is deferred until after genesis. O-85, historical
permission, broader adequacy and genesis are not closed by this performance work.

## Current validation inventory

`validation/reconstruction/current-verified.json` and each family's source and
verification records are the current inventory. The last accepted check covers
1,602 theories, executes all five affected history recipes with their paired
stages, retains the other 45 unchanged recipe boundaries, and records 5,888
complete report records in total. It does not claim that every non-recipe entry
point was exercised or that all 50 recipes were rerun in this cycle.

The older delivered/local-split timing table and its resolved workflow failure
are removed from this live plan. Their raw observations remain in
`validation/reconstruction/native-speedup-observations.json`. Current native
presentation measurements are retained separately, with their actual source and
execution boundaries. None of these records closes conditions 1, 6 or 5a.
