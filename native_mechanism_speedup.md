# Making native development and validation fast

Updated 2026-09-17 from accepted cause/word refinements, three further paired
presentations and the completed full-source proof. Historical observations retain
their own execution boundaries.

## Current result

**Digit replay now passes its complete native word in 279.14 s. Its earlier
all-recipe execution took 825.47 s. Actual returned cause targets are shared
across candidate assessments and independent target reads execute in parallel.
The artifact-word refinement also removes repeated row conversions. That runtime-refinement
validation took 365.58 s (6 min 6 s), including proof and host tests.
These are observed runs under different concurrent schedules, not a controlled
whole-cycle speedup ratio. The broader speedup objective remains unfinished.**

The accepted workspace has 1,624 theories, 131 rebuilt over 1,493 reused contexts.
The latest generation/history-index batch passed in 152.10 s, executing three
affected paired recipes and retaining 47 unchanged inputs. Fourteen families now
have native words: eleven use words only, and the three newly paired families
are ready for legacy-stage removal. Thirty-six families still need migration.
The 50 retained boundaries contain 3,821 physical records, including the three
new words; each retains its complete presented report.

| Boundary | Current accepted evidence |
|---|---|
| Proof base | 1,589 theories at fixed `/tmp/structural-accepted`; accepted heap/database identities preserved. |
| Latest incremental proof | 74.76 s for all 131 changed/dependent theories; no missing, unlisted or escaped proofs. |
| Latest execution and tests | Three paired recipes in 71.97 s; 125 tool tests and 35 kernel tests passed, with two optional skips. The preceding digit recipe passed in 279.14 s. |
| Complete recipe inventory | All 50 recipes passed the preceding 909.51 s cycle. Subsequent scoped cycles retained unchanged complete manifests and reran every affected recipe. |
| Native presentation | Fourteen accepted words; eleven presentation-only recipes and three paired migrations. Shared renderers remain for their existing callers. |
| Same-report word comparison | Old encoder 96.260 s, object lookup 25.986 s on the same computed report; all 20,519,284 bytes match. Old encoder ran first, so this is not a cold-cache comparison. |
| Full source proof | All 1,620 frozen theories rebuilt from HOL with no project parent in 542.886 s; sixteen threads, parallel_proofs=0. The four later presentation theories are outside this snapshot. Full rebuild cost remains substantial. |
| Whole workflow | Native selection/criticism under conditions 1 and 6 and practical gate 5a remain open. Gate 5b is deferred until after genesis. |

The [current inventory](validation/reconstruction/current-verified.json),
[incremental receipt](validation/incremental-check.json),
[cause-preparation measurements](validation/reconstruction/prepared-cause-measurements.json)
and [word measurements](validation/reconstruction/object-word-measurements.json)
bind the runtime refinement. [Generation presentation measurements](validation/reconstruction/generation-presentation-measurements.json)
and [full-source measurements](validation/reconstruction/cold-source-proof-measurements.json)
record the latest extensions. [Retirement measurements](validation/reconstruction/native-retirement-measurements.json)
and the preceding [all-recipe measurements](validation/reconstruction/native-presentation-cycle-measurements.json)
retain their actual validation boundaries.

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

**Measured cycles.** The latest three-family batch took 152.10 s: proof 74.76 s,
export 0.77 s, execution/tests 71.97 s, with the other 47 manifests unchanged.
The preceding cause/word batch had base/impact 0.65 s, proof
80.34 s, recipe impact 4.65 s, export 0.77 s and digit replay plus host tests
279.14 s; total 365.58 s. Other recipe inputs were unchanged. The four renderer
retirements separately passed in 106.14 s: proof 82.75 s and execution/tests
18.30 s. The unchanged deltas still rebuild against the older fixed base;
promoting accepted incremental contexts is not implemented.

The preceding complete affected batch ran all 50 recipes in 909.51 s, with
digit replay at 825.47 s and decision replay around 376 s. A current all-recipe
cycle after these changes has not been measured. Probe measurements and the
independent full-source proof overlapped validation; their times are not serial
parts to add to the reported cycle.

**Full-build proof work.** An earlier complete build recorded 543 s elapsed
and 3,569 s CPU: 2,099 command-seconds in proof methods, 1,292 in code exports
and 259 in theory setup. The accepted base records 177.871 s for
`ordered_object_formed_exact` and 155.672 s for the revision-quality conflict
equivalence. The first now factors `listed_fields_subset` and separately proves
incidence, counted-data and binding coverage. The second directly composes the
existing list-empty, conflict and soundness equations instead of metis search.
The original statements, premises and defined computations are unchanged.
The combined replacement probe built in 5.44 s, and full affected integration
passed. This does not license subtracting 333 s from a concurrent full build;
a comparable end-to-end ratio is not established. The new complete frozen
1,620-theory source proof passed in 542.886 s, with no project parent reused.
Its session reports 524 s elapsed and 3,318 s CPU. Source count, proof scheduling
and concurrent work differ from older full checks. Remaining long commands
include child-source code simplification (96 s), generation retention proofs
(41–56 s), source-entry installation (46 s) and steering (45 s). Full and cold
reconstruction cost remains an open target.

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

**Native cost after host fixes.** Earlier measurements localized digit replay
to context 6 (687 s single-threaded), versus 2.6 s for contexts 0–5 and 179 s
for the remaining contexts. Current time-limited profiles of context 6 show
list equality, join conditions, filtering and duplicate removal dominating.
Do not infer that this is many distinct completed term readings:
`finite_term_readings_unique` proves uniqueness of the term and both footprints.
The precise remaining attribution needs actual operation evidence.

A footprint-keyed result collector reproduced the complete word but took
982.13 s, with no gain. A broader collector proved but emitted unavailable
reading-function bodies and failed at module loading. Ordered footprint
membership/unions were stopped after 939.55 s without a completed presentation.
Their bounded profile moved substantial work to list ordering. None was adopted.
A separate raw-artifact word lookup has an exact proof but no successful full
execution measurement yet. Raising thread counts does not resolve these costs.

Existing known-source and constructed-source caches were tested, but neither
bounded probe completed the difficult case. Guessing a source reconstruction was
therefore not adopted. The successful preparation instead collects **actual
returned targets**. The native diagnostic found sixteen distinct method/target
pairs but four targets for context 6. Each prepared subject carries its own
result function, avoiding an invented equality on opaque digit stores. Generic
computed caches evaluate actual values, preserve the original function on its
entire domain, and execute the original computation on an unprepared key.

`Prepared_Digit_Cause_Assessments` prepares complete target scopes once per
context, then reuses them in every original cause assessment. Generation presence,
payload, policy/package/application/replay readings and all verdicts remain
computed. `Prepared_Digit_Replay_Packets` instantiates the existing prepared
context-table contract. Generated Eval code builds the cache before the returned
method function and uses `Par_List.map` for distinct inputs. The complete probe
matched every baseline byte: 216.236 s presentation, 97.734 s word, 321.401 s
total. After the exact word refinement, the real recipe passed in 279.14 s.

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

| Family | Complete word bytes | Last accepted presentation (s) |
|---|---:|---:|
| required-history | 159,908 | 20.30 |
| digit-history | 418,306 | 186.76 |
| known-history | 449,531 | 193.05 |
| quoted-history | 483,348 | 192.69 |
| constructed-history | 551,708 | 204.16 |
| digit-replay | 20,519,284 | 279.14 |
| decision-replay | 1,296,760 | 375.85 |
| native-nodes | 341,007 | 3.42 |
| native-graphs | 1,000,741 | 18.25 |
| native-derivations | 648,713 | 6.28 |
| native-certificates | 890,378 | 6.53 |
| history-index | 316,651 | 71.17 |
| indexed-generation | 550,833 | 2.52 |
| digit-generation | 743,867 | 3.02 |

The first eleven use words only; the final three passed paired stages. These
latest timings come from the linked distinct
cycles and are not additive or a controlled ranking. Every word boundary is
unchanged. Exporting theory and ML structure remain separate inputs: three
history theories emit `Digit_History_Execution`.

**Four additional native families.** Node and graph reports retain complete
source environments, metadata, target/discharge relations, returned environments,
correspondences and every independent reading. Derivation and certificate reports
retain original demands, source evaluations, complete proof trees, exact paths,
coordinate maps, original graphs and all inspection details. Their quality rows
are computed from the actual returned assessments. The common scoped report
composer is injective whenever its complete packet composer is; individual
families keep their own packet shapes and optional failure levels.

**Replay content.** Reusable presenters now cover complete programs, graphs,
proof nodes, replay results, cause reports, original requirement decisions and
all inspection details. Digit replay retains every seed, previous source family,
packet, computed quality and original/projected source correspondence. Decision
replay retains the complete packet and its actual nineteen-facet inspections.
`assessment_truth_rows` computes values from actual assessment cells, retaining
order and multiplicity; its exact indexing law supplies no satisfaction premise
without the inspector's original-subject contract. Digit stores retain their
established original views.

**Streaming correction.** The first digit presentation finished in 696.40 s,
then failed while emitting the word with an exhausted stack. The new counted
fold and explicit term worklists have universal exact equations to the same
word and avoid constructing the whole artifact-header bit list. The successful
probe took 792.44 s: presentation 684.56 s and word delivery 100.30 s, plus startup
and retention. This fixes the failure; it is not yet an acceptable runtime.

The [replay measurements](validation/reconstruction/replay-presentation-measurements.json)
retain the accepted migration, stack repair and unsuccessful runtime candidates.
The [new native measurements](validation/reconstruction/native-construction-presentation-measurements.json)
and [certificate measurements](validation/reconstruction/native-certificate-presentation-measurements.json)
retain the four accepted paired transitions. The generic host only packs native
bits and records their complete byte boundary; it does not inspect generated
report representations or supply semantic verdicts.

**History-index and generation content.** The indexed-history presentation keeps
both the full original history and actual indexed membership, including typed
and unguarded result views, coverage and original source projections. Indexed
generation keeps the full query sequence separately from its original-source
projection. Digit generation retains allocation counters and views, every
original assessment and its computed nine-facet inspection, original and
projected inputs and chain lengths. All three complete native words matched
their probes beside unchanged original comparisons on the same actual exports.

**Object-table word emission.** `Finite_Term_Object_Words` stores complete
artifacts for reference lookup and converts each distinct table entry to rows
once. Existing injective identity-map laws prove exactly the old indices, row
table and word. The paired measurement ran both encoders on one actual report:
96.260 s then 25.986 s, with complete byte equality. This refinement is currently
applied to the large digit-replay word. No word boundary was reset.

**Remaining migration and dominant work.**

1. Retire the three newly accepted legacy stages after auditing renderer imports.
   Continue the remaining thirty-six families with the same native notions.
2. Reduce decision-replay cost and remaining native computation. Reuse complete
   computed-input sharing, with actual dependencies and independent criticism;
   availability of a cache is not evidence of its effective use.
3. Reduce the measured full-source cost and ordinary proof invalidation while
   preserving exact accepted contexts. Ordinary checks still reprove the whole
   delta against the original fixed base.
4. Complete the non-recipe audit and demonstrate native-driven real development
   at acceptable cost. Faster fixtures do not establish the complete workflow.

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

The retained inventory covers 1,624 theories and 50 recipe boundaries with 3,821
complete physical records. The latest cycle executed three paired recipes and
retained 47 unchanged inputs; both host suites passed. Fourteen families have
native words, eleven without their old stages. The separate 1,620-theory frozen
source proof from HOL also passed in 542.886 s. It precedes the four new
presentation theories and does not rerun every recipe from cold sources.

Obsolete expanded history-cycle copies were replaced by verified reconstructible
archives, reducing about 1.1 GB to 250 MB. Archive identities and restore commands
are in [the temporary archive record](validation/reconstruction/native-temporary-archives.json).
The accepted base and complete digit comparison word were preserved.

Conditions 1, 6 and practical gate 5a remain open; theoretical 5b stays deferred.
