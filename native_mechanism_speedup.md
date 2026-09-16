# Making native development and validation fast

Updated 2026-09-16 from the committed speedup batch and the subsequent local
export-theory split. This replaces the original proposal, interim timing
inventory, and completed work presented as future tasks.

## Current result

**An ordinary commit cycle now runs without a complete build. A change confined
to one family was validated in 80 s; a change to shared tools or the refinement
bundle was validated in 831 s, because digit replay and decision replay still
keep a cycle that touches every recipe above single-digit minutes. Reports can
now be transported through the presentation classes of their notions; one
family uses that transport so far. The speedup objective is unfinished.**
The previous delivered commit is `4becc454be0d9b7c94d71fff0fe280a4833ee3c3`
(`Remove repeated native execution work across validation families`). This batch
commits the export-theory split, the incremental check and the host verification
corrections.

The [measurement ledger](validation/reconstruction/native-speedup-observations.json)
retains the latest stage timings, reported outcomes, source identities, cold-suite
logs and readiness failures. It records physical observations, not semantic
admission; its per-recipe entries predate this batch. The
[last complete recipe review](validation/reconstruction/current-verified.json)
and [incremental check receipt](validation/incremental-check.json) describe this
batch's 1,590-theory workspace.

| Boundary | Latest evidence | What it establishes |
|---|---|---|
| Delivered commit | 1,554 theories accepted; 158 host tests and 95 subtests passed, two optional-dependency skips; all 50 recipes and 5,883 complete records accepted | Proof and complete report reconstruction for `4becc45`; their committed source/tool/log identities were checked against Git contents before push. |
| Accepted base | Complete check accepted **1,589 theories** in the fixed base directory, with source and tool identities equal to the committed build receipt | The proof base for incremental checks; this batch's workspace adds one theory, proved incrementally with its 94 dependents. |
| Recipe executions | **All 50 recipes and 5,883 complete records accepted**; 125 tool tests and 35 kernel tests passed, two optional-dependency skips | The two lost workflow contract registrations are restored in `Native_Workflow_Execution`; `native-workflow` completes. |
| Retained manifests | All 50 source manifests regenerated from the validated workspace | Each recipe's retained verification now binds the exact inputs it was executed with. |
| Incremental validation | `tools/incremental_check.py` validated the incremental-check batch in 831 s and the presentation batch in 80 s against a fixed accepted base | See [Development cycle structure](#development-cycle-structure); the complete build is not part of an ordinary cycle. |
| Presented report | The required-history recipe retains the digit word of its complete presented report beside the unchanged report comparison on the same export | See [Native report presentation](#native-report-presentation); 49 recipes still use host renderers. |
| Whole development workflow | Conditions 1, 6 and practical-usefulness gate 5a remain open | Faster native packets and successful fixtures do not establish native-driven refinement selection or acceptable real development throughput. Gate 5b remains deferred until after genesis. |

## Where the time goes

| Measured or recorded boundary | Time | Interpretation |
|---|---:|---|
| Full check for delivered revision, 12 threads | **673.91 s — 11 min 14 s** | 1,554 theories, 14:46:21–14:57:35 UTC. |
| Full check after export-theory split, 16 threads | **625.14 s — 10 min 25 s** | 1,589 theories, 15:23:17–15:33:42 UTC. Source reorganization did not deliver validation in seconds. Different thread/source boundaries prevent treating the difference as a controlled speedup ratio. |
| Export all 50 recipe modules from accepted main build | About **1–2 s** | Reuses the already accepted proof. Export itself is not the multi-minute bottleneck. |
| Current streamed digit-replay check | **997.93 s — 16 min 38 s** | One execution/checking stage, after the shared build; four native workers. Delivered revision: 990.29 s. |
| Earlier plain source-only suite | **1,470 s — 24 min 30 s** | 40 recipes accepted on an earlier source revision. |
| Earlier compressed source-only suite | **1,598 s — 26 min 38 s** | 10 recipes attempted; digit replay failed. Together those two suites accepted 49/50, not a complete current cold run. |
| Final delivered check start to commit creation | **35 min 49 s clock span** | 14:46:21–15:22:10 UTC: proof, executions, retries, evidence integration and intervening work. This is not a measurement of the Git commit command. |
| Latest local check start to last recipe receipt | **About 32 min 22 s observed interval** | 15:23:17–15:55:39 UTC, ending at the receipt file timestamp. The batch still failed one recipe. |

The cold suites materialized declared source/fixture inputs and rebuilt their
project proofs from HOL without a supplied project heap. This is a source-only
reconstruction boundary, not evidence of an empty operating-system cache or a
fresh Pure/HOL installation. They preceded the final formation/stack fixes;
acceptance of the later main-build exports does not retroactively validate a
current cold reconstruction. The two suite times must not be added as serial
wall time when their work overlapped.

A previous packet-only profile reported complete steering at about **4.9 s**.
The current complete steering checker takes **27.02 s**, its request roundtrip
**45.10 s**, and its empty-scope check **13.30 s**, under the recorded concurrent
recipe schedule. Source-development checking takes **38.67 s** and its request
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

**Design.** A report subject is presented by composing the executable
presentations of its notions, each decoding into the notion's existing data term
or class: natural and truth-value data, uses, sites and calls, goals, complete
artifact rows and environment values, and the native target class. Pairs,
sequences, finite collections and options decode into the generic classes, and
generations and proofs reuse the collection presentation. Every presentation is
injective whenever its components are. Context tables, subject comparisons and
investigation cycles share one packet presentation across families. Counted
digit words compose the natural and address digit paths into a prefix-free word
of every executable term, delivered by a fold. Presentation names its notion
instead of dispatching on HOL types, because octets, local addresses and index
lists share one type. A collection's canonical order is one admissible
enumeration; the word boundary relies only on injectivity.

**Pilot, required history.** Theories: `Ordered_Finite_Terms`,
`Finite_Presented_Collections`, `Finite_Presented_Coordinates`,
`Finite_Presented_Structures`, `Finite_Presented_Investigations`,
`Finite_Presented_Histories`, `Finite_Term_Words` and
`Required_History_Presentation`; together they built in about eight seconds over
the accepted base. `tools/check_presented_report.py` streams the word of an
exported report value into bytes and records its size and SHA-256 as one tagged
record, so the existing boundary, recipe and retention code applies unchanged.

| Measured boundary, 16 workers | Time |
|---|---:|
| Required-history packet | 13.2-13.4 s |
| Presentation of the complete packet | 0.6-0.7 s |
| Digit word of the report, 34.4 MB | 2.4 s |
| Presentation stage, standalone | 18.4 s |
| Presentation stage beside the report comparison stage in the recipe | 22.6 s (comparison 23.5 s) |
| Complete cycle: 103 theories proved, one recipe, host tests | 80.1 s |

The word is large because shared environments and artifacts are presented at
every occurrence. Two runs produced identical bytes, and the recipe's export
produced the digest established from a separate probe export.

**Migration.**

1. Present the remaining history families (digit, known, quoted and constructed
   histories and the history index) through the existing store projections
   `digit_history_state_view`, `digit_allocated_view` and the indexed member
   view, then digit replay and decision replay.
2. Run each family's presented stage beside its report comparison once; after
   both are accepted on the same export, remove the comparison stage and its
   host renderer.
3. Once a family is compared only by presented words, refine its set
   representations; the reading-join accumulation of digit replay is the first
   target.
4. Compute each collection element's key once, and share repeated environments
   and artifacts in the word, if their measured cost warrants it.

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

The current source graph has **1,589 theories, 402 theories containing
`export_code`, 86 file-export theories and 50 reconstruction recipes**. The
refinement import closure shrank from the previously measured 296 theories to
**94 including the bundle itself**: 86 exports, five sharing refinements, two
execution bases, and the bundle. The earlier description omitted the bundle
when explaining the total.

This is a dependency-graph improvement. `ROOT` still declares **one Isabelle
session**, `RRA_Factor_Structural_Bootstrap`. Its latest full build still took
625 seconds. There is no implemented separate execution session, persistent
interactive proof service, or measured seconds-scale edit validation.

Three readiness defects were found in the split and are resolved or bounded in this batch:

1. `Native_Workflow_Execution.thy` lost the exports of
   `required_workflow_investigation` and
   `required_workflow_scope_investigation`. The latest `native-workflow`
   requirements step fails `assert len(contracts) == 1` after 0.16 s; the
   ordinary workflow step passed, but the rest of the complete recipe did not.
   A successful theory build did not detect this client contract omission.
   *Resolved:* a regular expression consumed the line boundary shared by
   adjacent registrations; both registrations are restored and the recipe passes.
2. `incremental_check.py` calls `accepted_parent(ROOT)` before computing changed
   theories. That function requires the current source bytes to equal the
   accepted receipt. A changed workspace fails that prerequisite; an unchanged
   workspace produces no changes to check. The draft also does not establish
   impact coverage for changed tools/fixtures, deleted inputs or non-recipe
   entry points. Its claimed changed-workspace behavior has not been validated.
   *Resolved for recipes:* the base is a separate fixed directory accepted by
   its own complete check, recipe impact compares complete source manifests
   (theories, tools, fixtures and expected reports), and the tool validated this
   batch. Non-recipe entry points remain outside the check.
3. The scratch `fast_validate.sh` reports `FASTDONE` and can exit zero after
   a failed child/export because it does not propagate aggregate failure.
   The latest task did exactly that while `native-workflow` failed. A shell
   completion marker is not recipe acceptance. Final commit readiness must
   inspect the complete receipts and their exact inputs.
   *Resolved:* `incremental_check.py` accepts only when every executed recipe
   receipt and both host test suites are accepted, and exits non-zero otherwise.

The latest 49 accepted recipe runs were checked against their current module
proof receipt hashes. Their observations are retained in the measurement ledger;
they have not been substituted into a falsely accepted 50-recipe manifest set.
The split remains local until its full applicable contract, source-manifest,
execution and retention boundaries are repaired and checked.

## Remaining work, in useful batches

The immediate priority is the complete validation and commit path. The following
continues the existing plan and owner requirement; it is not native admission of
these candidates. Decisions and corrections still require the applicable native
subjects, computed observations, reusable reasoning and independent criticism.

| Work group | Required outcome and evidence |
|---|---|
| Repair the current split and validation orchestration | Preserve every exported contract and original client entry point; propagate actual failures; demonstrate changed-source, unchanged-source, tool/fixture and missing-input cases. Reuse accepted unchanged inputs and rerun the complete affected checks. Regenerate manifests only for the actual final validated source state. |
| Make proof invalidation follow real dependencies | Establish reusable accepted base contexts and separate execution-layer proof/code work where the dependency boundary permits. The proposed execution session requires distinct theory directories and a shared theory-path/session resolver across `build.py`, `prove_context.py`, `export_proved_code.py`, `proved_code.py`, `investigate.py` and `reconstruction_sources.py`; they currently assume one session and/or `theories/<name>.thy`. A directory split alone is not a validated solution. Preserve normative bootstrap and exact source/tool invalidation. |
| Provide a working incremental development path | Keep an immutable accepted parent distinct from the changed workspace; rebuild changed subjects and actual dependents, export affected modules and execute every affected client. Store exact source/tool/fixture dependencies and complete receipts so unchanged results can be reused soundly. Exercise realistic repeated edits and refusal/repair cycles, not only a no-change fixture. |
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

## Complete current recipe inventory

Each number below is **the sum of recorded execution-step wall seconds** for a
recipe, including checker startup, native work, reporting and host checking.
Some stages and recipes overlap: these sums are neither elapsed suite time nor
CPU time, and exclude shared proof/export and outer recipe coordination.
The ledger retains individual stage names, times, worker settings and outcomes.

The linked repository receipts describe the delivered `4becc45` boundary. The
right column comes from the latest local split executions, retained separately
in the measurement ledger. Resource contention and changed build boundaries
prevent interpreting each column difference as a controlled speedup ratio.

| Recipe | Delivered step sum (s) | Latest local split step sum (s) |
|---|---:|---:|
| [allocated-environments](validation/reconstruction/allocated-environments-verified.json) | 2.32 | 2.37 |
| [artifact-lookup](validation/reconstruction/artifact-lookup-verified.json) | 1.92 | 1.97 |
| [cached-grafts](validation/reconstruction/cached-grafts-verified.json) | 2.87 | 2.77 |
| [certificate-coverage](validation/reconstruction/certificate-coverage-verified.json) | 8.28 | 8.33 |
| [certificate-development](validation/reconstruction/certificate-development-verified.json) | 8.03 | 8.28 |
| [certificate-input-development](validation/reconstruction/certificate-input-development-verified.json) | 10.24 | 10.98 |
| [certificate-scope-repair](validation/reconstruction/certificate-scope-repair-verified.json) | 7.33 | 7.43 |
| [certified-causes](validation/reconstruction/certified-causes-verified.json) | 110.53 | 109.91 |
| [concurrent-history](validation/reconstruction/concurrent-history-verified.json) | 25.42 | 51.33 |
| [concurrent-replay](validation/reconstruction/concurrent-replay-verified.json) | 78.29 | 149.96 |
| [constructed-history](validation/reconstruction/constructed-history-verified.json) | 320.31 | 323.08 |
| [data-reading](validation/reconstruction/data-reading-verified.json) | 3.97 | 3.87 |
| [decision-replay](validation/reconstruction/decision-replay-verified.json) | 368.54 | 374.86 |
| [digit-allocation](validation/reconstruction/digit-allocation-verified.json) | 2.92 | 2.97 |
| [digit-generation](validation/reconstruction/digit-generation-verified.json) | 8.30 | 7.95 |
| [digit-history](validation/reconstruction/digit-history-verified.json) | 265.15 | 259.08 |
| [digit-replay](validation/reconstruction/digit-replay-verified.json) | 990.29 | 997.93 |
| [encoded-environments](validation/reconstruction/encoded-environments-verified.json) | 8.30 | 9.15 |
| [environment-grafts](validation/reconstruction/environment-grafts-verified.json) | 9.44 | 8.97 |
| [environment-updates](validation/reconstruction/environment-updates-verified.json) | 9.66 | 10.01 |
| [generation-records](validation/reconstruction/generation-records-verified.json) | 13.96 | 14.33 |
| [graft-admission](validation/reconstruction/graft-admission-verified.json) | 8.98 | 10.27 |
| [history-index](validation/reconstruction/history-index-verified.json) | 174.27 | 165.38 |
| [indexed-generation](validation/reconstruction/indexed-generation-verified.json) | 13.95 | 14.50 |
| [known-history](validation/reconstruction/known-history-verified.json) | 258.26 | 267.08 |
| [literal-replay](validation/reconstruction/literal-replay-verified.json) | 12.76 | 13.33 |
| [native-admission](validation/reconstruction/native-admission-verified.json) | 85.17 | 86.54 |
| [native-certificate-replay](validation/reconstruction/native-certificate-replay-verified.json) | 135.50 | 137.81 |
| [native-certificates](validation/reconstruction/native-certificates-verified.json) | 10.39 | 9.43 |
| [native-child](validation/reconstruction/native-child-verified.json) | 222.76 | 225.21 |
| [native-derivations](validation/reconstruction/native-derivations-verified.json) | 8.03 | 8.08 |
| [native-development](validation/reconstruction/native-development-verified.json) | 23.97 | 24.16 |
| [native-evaluation](validation/reconstruction/native-evaluation-verified.json) | 6.54 | 6.29 |
| [native-extensions](validation/reconstruction/native-extensions-verified.json) | 2.72 | 2.62 |
| [native-graphs](validation/reconstruction/native-graphs-verified.json) | 22.46 | 24.09 |
| [native-histories](validation/reconstruction/native-histories-verified.json) | 7.33 | 11.10 |
| [native-nodes](validation/reconstruction/native-nodes-verified.json) | 3.97 | 4.52 |
| [native-requirements](validation/reconstruction/native-requirements-verified.json) | 41.86 | 41.20 |
| [native-sources](validation/reconstruction/native-sources-verified.json) | 7.69 | 17.78 |
| [native-steering](validation/reconstruction/native-steering-verified.json) | 119.52 | 105.23 |
| [native-workflow](validation/reconstruction/native-workflow-verified.json) | 134.62 | **failed at requirements** |
| [quoted-history](validation/reconstruction/quoted-history-verified.json) | 197.60 | 197.08 |
| [required-causes](validation/reconstruction/required-causes-verified.json) | 18.26 | 18.68 |
| [required-history](validation/reconstruction/required-history-verified.json) | 30.12 | 39.08 |
| [requirement-decisions](validation/reconstruction/requirement-decisions-verified.json) | 9.84 | 14.65 |
| [requirement-plans](validation/reconstruction/requirement-plans-verified.json) | 1.97 | 1.72 |
| [requirement-sources](validation/reconstruction/requirement-sources-verified.json) | 9.33 | 9.08 |
| [source-development](validation/reconstruction/source-development-verified.json) | 109.62 | 113.28 |
| [use-allocation](validation/reconstruction/use-allocation-verified.json) | 2.17 | 2.22 |
| [use-codecs](validation/reconstruction/use-codecs-verified.json) | 2.02 | 2.32 |

The failed workflow is incomplete, not a faster result. Its later stages remain
unvalidated. The older original-baseline table, interim probe timeouts, resolved
streaming failures and completed five-batch proposal have been removed from this
current plan; underlying historical evidence remains available in version control.
