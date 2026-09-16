# Making the whole native development machinery efficient

## Objective and evidence boundary

The owner's objective is to remove native execution as a development bottleneck,
reusing the replay/history speedup across the remaining mechanisms and seeking
orders-of-magnitude improvement. This plan covers the complete current executable
inventory and the missing measurement coverage, not only the newest dispatcher.
It proposes implementation and validation; it does not claim those speedups have
already been obtained or that every suspected hotspot has been measured.

The inspected baseline is `f460a9a34d2f5e70444bb8044a22d539af49ffd5`.
The relevant performance commit is
`0ff553f9db580b05f426397966a166f627bc0b17`, committed on 2026-09-16 at
01:38:12 +03:00: **Share complete native packets and execute independent stages
in parallel**. Identify it by its content and hash rather than “yesterday”.

The review inspected that commit's 55 theory files, its execution/transport
tools, the current dependency graph, all 50 reconstruction recipes and their
retained timing evidence. Every file in all 50 source manifests matches the
current repository bytes. Some current verification files refer to an earlier
receipt at `eba0edc`; those Git objects were read and their recorded SHA-256
identities checked before extracting timings. The inventory at the end records
every family, including the already fast and previously optimized ones.

The previous plan-review delay was a fresh Isabelle reconstruction that rebuilt
Pure/HOL before entering the project session. It was interrupted without an
accepted project proof or a native execution. That delay is evidence about
bootstrap/build overhead, not a native-function profile. The retained execution
records provide independent evidence that several native paths are also slow.
No expensive reconstruction was launched merely to write this plan.

This remains a candidate decomposition under
[DEVELOPMENT_WORKFLOW.md](DEVELOPMENT_WORKFLOW.md). The actual optimization
choices and their criticism must enter the existing native development cycle
on represented subjects before adoption. This prose inventory and host timing
extraction supply no native admission of the plan. Missing subject/measurement
adapters remain explicit work, with no outside-reasoning fallback. Isabelle/HOL
retains its established normative bootstrap role through genesis.

## Implementation record and corrections

This section records the executed batch. The remaining sections keep the
original inventory and proposals; where they conflict with the measurements
below, the measurements govern.

**Correction: the dominant regression was toplevel printing, not native work.**
Every file export was moved to the Eval target and runs in Pure `ML_process`.
That toplevel echoes each bound value; drivers bind whole packets (for example
`val (table,(comparison,cycles)) = N.certificate_scope_repair_packet ...`).
The same baseline literal-replay packet ran in 0.09 s under standalone Poly/ML
and did not finish printing in four minutes under `ML_process`. The shared
runtime ([native_execution_runtime.py](tools/native_execution_runtime.py)) now
sets the ML print depth to zero; tagged reports are printed explicitly as
before. On the accepted L exports with unchanged record boundaries, certificate
scope repair fell from 1,262.4 s to 99.1 s. Steering, source development and
certificate coverage were unchanged, because their drivers did not print packets.

**Correction: choose refinements from native profiles of complete packets.**
A profile sweep of every family driver, with printing suppressed, exposed three
generic costs shared by most families. Each now has one exact code equation at
its single use site, imported through
[Native_Execution_Refinements](theories/Native_Execution_Refinements.thy):

| Refinement | Replaced cost | Contract |
|---|---|---|
| [RRA_Linked_Record_Candidates](theories/RRA_Linked_Record_Candidates.thy) | Every syntax reader enumerated all arity-length lists over the headed incidence (256 lists for four fields, with quadratic deduplication), rechecking whole-object formation for each list. | Candidates follow actual successor incidences from each headed row; the original record filter is unchanged, every exact record is constructed, and formation is checked once per read. |
| [Ordered_Finite_Rows](theories/Ordered_Finite_Rows.thy) with [Finite_Investigation_Basis_Sharing](theories/Finite_Investigation_Basis_Sharing.thy) | Investigation basis, repairs and retention deduplicated all observation and candidate-pair loss rows quadratically, recomputing each candidate profile per pair. | Each profile is computed once; ordered indexes return exactly the original last-occurrence list and membership. Basis, repairs and retention are equal on every input. |
| [Factor_Finite_Judgment_Reading_Sharing](theories/Factor_Finite_Judgment_Reading_Sharing.thy) in the bundle | Whole judgment readings visited every carrier position without the prepared formation-once data reader. | The existing proved equation now reaches every export. |

Native packet times, identical drivers and inputs, old accepted C export beside
the refined export, two threads each, measured concurrently:

| Family | Before (s) | After (s) | Ratio |
|---|---:|---:|---:|
| encoded-environments | 53.05 | 0.85 | 63× |
| cached-grafts | 7.56 | 0.14 | 55× |
| generation-records | 53.97 | 1.46 | 37× |
| native-nodes | 34.48 | 1.15 | 30× |
| graft-admission | 3.70 | 0.13 | 29× |
| digit-allocation, allocated-environments, use-allocation, use-codecs, environment-grafts, environment-updates | 1.1–6.0 | 0.05–0.28 | 21–24× |
| certificate-coverage | 319.69 | 26.90 | 11.9× |
| native-histories | 201.43 | 17.30 | 11.6× |
| certificate-scope-repair | 66.97 | 6.80 | 9.8× |
| requirement-decisions | 51.19 | 33.28 | 1.5× |
| certified-causes, required-history, native-certificate-replay, native-requirements, required-causes, native-admission | 15.7–467.3 | 14.1–412.6 | 1.07–1.19× |

The refined native-certificates, native-derivations and native-graphs packets
finished in 18.9 s, 14.5 s and 44.0 s; their concurrent old runs were stopped
before completion, so no ratio is claimed. Steering on the L export was
unchanged (357.8 s old, 350.9 s refined, contended).

**Loop-invariant evaluation.** After those refinements, a one-question steering
profile spent 68% in four-level tuple equality. The cause was
`finite_inference_witnesses`, which recomputed the whole enabled-rule family
for every candidate witness in every history round, together with similar
recomputation in material satisfaction, premise joins, system formation, head
coverage and candidate profiles.
[Factor_Invariant_Evaluation_Sharing](theories/Factor_Invariant_Evaluation_Sharing.thy)
computes each invariant set once and tests a witness directly against the
enabling condition. Every filter order and result is unchanged. One-question
steering fell from 60.8 s to 12.2 s with the same inputs.

**Formation established once.** For one development question, construction and
admission then performed 30 native source reads, which took 87% of their time,
with about 15,000 environment and 72,000 artifact formation checks. Every
guarded reader re-checked formation of the whole environment at each recursive
step, and every citation choice re-checked its artifact.
[Factor_Formation_Once_Readings](theories/Factor_Formation_Once_Readings.thy)
checks environment formation once at the entry of bounded term and pattern
readings and definition rows. Artifacts of a formed environment are formed, so
the recursions use formation-free record, citation, payload and variable bodies.
Citation choices share one object formation per root. On the same inputs,
construction fell from 0.48 s to 0.14 s, admission from 0.48 s to 0.14 s,
one-question steering from 11.3 s to 3.3 s and the complete eight-question
steering computation from 14.2 s to 4.9 s. That computation took 123.7 s before
this batch.

**Runtime memory.** Streamed digit replay was interrupted in the Eval runtime
("Unable to increase stack"). Removing Isabelle's worker stack cap with
`threads_stack_limit=0` did not change that; sixteen deep-recursion workers
exhaust the compact Poly/ML address space for this packet. Its checker now uses
four workers and completes; the uncapped stack setting remains, matching
standalone execution.

**Correction: validation repeated the same proofs.** A validation round ran the
whole-project build from HOL and then two storage-matched source-only suites,
each proving the same theories from HOL again, so most wall time was waiting on
duplicated proof work. The inner loop now builds the main workspace once, exports
every recipe module from that accepted build with
`export_proved_code.py --main-project`, and runs all recipes against those
exports in parallel with their complete report comparisons. Cold source-only
reconstruction remains a release check of manifest completeness, not a step of
every change.

**Remaining costs.** Family, schema and scoped-pattern readers still check
environment formation per call; certified causes spend most of their time in
list-set footprint unions of `finite_join_readings`; grounding and footprint
unions reach reports through raw finite-set list order (`elements` in
[native_program_json.py](tools/native_program_json.py)), so a representation-
changing refinement also needs a presentation-invariant rendering.

## What the successful commit actually changed

The [performance record](validation/reconstruction/concurrent-performance.json)
reports complete execution and retention, not just a selected inner function:

| Workload | Earlier run | Optimized run | Observed ratio |
|---|---:|---:|---:|
| Replay | 5,731.722 s | 78.564 s | 72.956× |
| History | 2,131.231 s | 33.444 s | 63.725× |

All 934 original native reports were preserved. The original comparison accounts
explicitly for permitted finite-set presentation bijections; ordered ledgers
remain unchanged. The final warm and cold packets were directly equal. Different
cold-suite executions took 100.9 s and 51.5 s with a different resource boundary;
do not mix those figures with the 16-worker measurements to calculate speedups.

The change was a composition of reusable exact refinements:

| Technique | Existing reusable content | What its contract permits |
|---|---|---|
| Compute invariant context once | [Prepared_Assessment_Functions](theories/Prepared_Assessment_Functions.thy), `Factor_Prepared_Replay_Assessments`, `Factor_Prepared_Cause_Scope_Reports` | Prepare an actual assessment function before traversing candidates; return the same complete ordered table. |
| Memoize actual complete computations | [Memoized_Function_Sequences](theories/Memoized_Function_Sequences.thy), `Prepared_Computed_Functions`, `Optional_Constructed_Caches`, `Exact_Cache_Readings` | Cache actual evaluations under exact keys; prove every hit and execute the original operation on a miss. The entire optional result is preserved. |
| Reuse constructor knowledge and successful results | [Optional_Success_Reuse](theories/Optional_Success_Reuse.thy), `Factor_Known_Cause_Reports`, `Factor_Known_History_Control_Construction`, `Factor_Success_Shared_History` | Consume established invariants and complete-result equations. A failed checked result still runs the omitted-guard control unless a separate theorem covers that failure. |
| Share original producer/reference work | `Factor_Shared_Replay_Construction`, `Factor_Shared_History_Construction`, `Factor_Constructed_Original_History_Execution` | Derive original views from actual constructed results under their correspondence theorems; retain every distinct control and refusal. |
| Prepare equality and inspections once | `Nested_Artifact_Value_Identity`, `Generation_Identity_Maps`, `Factor_Nested_Replay_Identity`, `Factor_Nested_History_Identity`, `Finite_Prepared_Reader_Inspections`, `Finite_Shared_Inspection_Rows` | Compare injective complete structural representations and prepare inspection before the facet loop. No field or optional level is discarded. |
| Improve finite collection operations | `Finite_Sorted_Set_Execution`, `Finite_Ordered_Relation_Checks`, `Finite_Relation_Functionality_Execution`, `Finite_Collection_Equality_Execution`, `RRA_Ordered_Artifact_Formation` | Sort then remove adjacent set duplicates, scan ordered subsets, avoid unnecessary self/reverse comparisons, and use exact equality fast paths. Set laws do not apply to counted data or premise occurrences. |
| Construct syntax without repeatedly rebuilding prefixes | `Factor_Finite_Syntax_Accumulation`, [Factor_Finite_Accumulated_Data_Syntax](theories/Factor_Finite_Accumulated_Data_Syntax.thy) | Place rows at final addresses and accumulate them once, with the original complete optional syntax result. |
| Reuse observations and revisions already computed | `Finite_Assessed_Observation_Readings`, `Context_Source_Projections`, `Factor_Packet_Observation_Readings`, [Finite_Investigation_Execution_Sharing](theories/Finite_Investigation_Execution_Sharing.thy), [Shared_Investigation_Cycles](theories/Shared_Investigation_Cycles.thy) | Read actual constructed cells; share relation, selected values and followed basis. Changed facet lists still receive their required computations. |
| Expose independent computations | [Parallel_Assessment_Execution](theories/Parallel_Assessment_Execution.thy), `Factor_Packet_Stages`, `Factor_Parallel_Packet_Cycles` | Preserve complete ordered maps while independently executing contexts, inspections and selection cycles through Isabelle's Eval/Pure runtime. |
| Share full output values and reconstruct occurrences | [Complete_Value_References](theories/Complete_Value_References.thy), `Complete_Object_References`, `Value_Reference_Identity_Maps`, `Ordered_Environment_Artifact_Objects`, [shared_artifact_reports.py](tools/shared_artifact_reports.py) | Retain a complete dictionary and exact occurrence references. Decode to the entire original report, including malformed values and multiplicities. |

There was no deletion of inconvenient methods, subjects, checks or results.
Neither a new thread count nor compression alone explains the improvement.
The reference dictionary reduced replay's uncompressed output from about
6.77 GB to 65.45 MB, and history's from 2.25 GB to 3.32 MB, without changing
the decoded original records.

The optimized paths still have measurable costs. Replay spends 26.494 s in
table construction, 5.867 s in cycles and 33.817 s reporting; history spends
14.095 s in cycles and 8.371 s reporting. Reporting is about 43% of replay's
measured total; history cycles are about 42% of its total. The history packet
timer encloses sub-stages, so it must not be added to them. Average observed CPU
use was only about 3.13 and 3.41 cores, including startup and retention. These
are starting measurements, not evidence that another fixed ratio is achievable.

## The scope is larger than the two optimized exports

At this baseline there are 1,537 theories, 394 theories containing `export_code`,
86 with file exports, 50 reconstruction recipes and 13 built-in investigations
in [investigate.py](tools/investigate.py). Recipe dependency closures cover 1,255
theories. The remaining 282 require classification as proof-only, unexercised
executable content, or content reached through another harness; absence from a
recipe is not evidence of low cost.

The source graph exposes a particularly actionable integration gap:

| Refinement available in the recipe's import closure | Families |
|---|---:|
| `Parallel_Assessment_Execution` | 6/50 |
| `Shared_Investigation_Cycles` | 2/50 |
| `Finite_Investigation_Execution_Sharing` | 2/50 |
| `Prepared_Computed_Functions` | 1/50 |
| `Complete_Object_References` | 2/50 |
| `Finite_Sorted_Set_Execution` | 2/50 |
| `Finite_Ordered_Relation_Checks` | 2/50 |
| `Finite_Relation_Functionality_Execution` | 2/50 |
| `Factor_Finite_Accumulated_Data_Syntax` | 2/50 |

The six parallel families are concurrent replay/history, workflow, development,
steering and source development. Of these nine sampled refinements, the four
new development families import only parallel assessment. The other 44 recipes
run through standalone execution paths. This is an import/runtime coverage
finding, not proof that every absent refinement applies or that an imported
code equation is active in the generated program. Inspect generated code and
measure its effect before claiming physical reuse.

Fifteen exporting theories are outside every recipe's dependency closure:
`Factor_Data_Product_Execution`, `Factor_Keyed_Set_Execution`,
`Factor_Observation_Collection_Investigation`, `Factor_Observation_Investigation`,
`Factor_Observation_Scope_Investigation`, `Factor_Observation_Table_Controls`,
`Factor_Observation_Table_Execution`, `Factor_Observation_Table_Investigation`,
`Factor_Pair_Scope_Investigation`, `Factor_Reasoning_Method_Investigation`,
`Factor_Schema_Socket_Investigation`, `Factor_Substitution_Investigation`,
`Finite_Directed_Execution`, `Observation_Revision_Investigation`, and
`Presentation_Completion_Investigation`. Include their original subjects and
callers in the measurement matrix. The 36 file-exporting theories that are not
direct recipe roots also need an entry-point audit: being imported does not
establish that each exported operation was exercised.

Maintain coverage over actual operations and their source dependencies, not
over names containing “Native”. Include every built-in investigation, callable
`check_*`, `run_*`, roundtrip and comparison client, and the source/contract,
proof/export, transport and retention paths they depend on. Future native agenda,
provenance and mathematical-proof mechanisms from
[native_control_plan.md](native_control_plan.md) have no present runtime to
measure; their first implementation must enter this same coverage boundary.

## Remaining bottlenecks and candidate remedies

**Measured** below means a complete retained execution boundary. **Source evidence**
identifies repeated work or an algorithmic expansion in definitions; it does not
attribute a measured percentage without a profile. Keep these claims separate.

| Mechanism and evidence | Substantial candidate batch | Contract and measurement needed |
|---|---|---|
| **Closed development and admission.** Measured producers 256.0 s; question roundtrip 100.7 s. [Factor_Development_Cycle](theories/Factor_Development_Cycle.thy) constructs compiled conditions and then compiles them again through `execute_development_condition`; comparison is repeated through revision, and admission mentions regeneration, compilation, comparison and revision repeatedly. | Prepare one complete question context; share generation, compilation and expected comparison/revision results across construction and admission. Extend the generic prepared-function and cycle laws instead of creating per-producer caches. | An equation for the complete original packet and an admission equation for arbitrary submitted reports. Still inspect the submitted evidence. A constructor's own result or a cached success bit cannot certify a corrupted report. Measure actual call counts after code generation. |
| **Steering.** Measured full scope 405.2 s and roundtrip 439.4 s. Context construction already shares the original report and independent reference per question. `development_producer_cell` still supplies admission of the original report per method, and assessment checks the actual report's admission. | Preserve the existing context sharing; extend preparation to repeated actual admissions, original-question encodings and exact repeated scopes. Reuse a whole policy result only when its complete inputs and applicability contract agree. | Keep the independent original-goal reference, all ten producers, all five facets, the ambiguous and empty scopes, and renewed admission for subsequent requests. No reuse keyed only by a method number or output count. |
| **Source development.** Measured full run 1,168.7 s and roundtrip 1,178.2 s. [Factor_Source_Development_Cycle](theories/Factor_Source_Development_Cycle.thy) rederives proposals, observations, question, steered execution and installation during admission. Source observations already share the generation-coverage Boolean. | Prepare the original source/request once; reuse proved complete proposal, question, installation and query contexts. Share source/program readings across compatible targets and source-preserving stages under actual equality/extension premises. | Preserve the original proposal family, distinct/equal target behavior, every observation, installed environment, query scope and ordered answers. Recheck arbitrary report mutations. The policy is already computed once for the request batch; do not invent a duplicate-policy defect. |
| **Requirement and native-source construction.** Requirements 476.6 s; admission 260.4 s; source extensions 79.6 s. Recursive guards repeatedly depend on native package reading, allocation and source installation. | Share recovered source and supported goal/guard plans; construct a batch of dependent clauses with one justified installation where its contract permits. Apply accumulated syntax and known-constructor reading refinements. | Same original goal conjunction and full target meaning, complete source agreement and freshness. Empty/repeated goals, absent definitions, changed old bindings and malformed sources retain their original outcomes. |
| **Certificates, graphs, histories and replay consumers.** Graphs 925.3 s; derivations/certificates about 549 s; decision replay 732.6 s; several certificate workflows 200–298 s. | Share whole inference histories, installed graph components, source readings, exact nested identity views and computed inspections. Apply constructor-derived premises to redundant re-reading. | Preserve every node, assertion origin, binding, premise socket, material operand and rejected control. Independent checker conditions remain; derivation, realization, graph installation and replay are distinct. Profile construction, checking, equality and reporting separately. |
| **Earlier persistent-store/history entry points.** History index 1,209.5 s; digit, known and quoted histories about 1,819–1,873 s. Earlier constructed history is 2,131.2 s. | Route applicable production consumers through the already proved shared/known-history refinements; retain and accelerate the complete comparisons of old and new methods. Prepare closed-state invariants, membership and lookup structures once. | Same whole states, order, cache relation, failed steps and original controls. Preserve historical baseline source boundaries; a faster sibling export does not automatically accelerate the old entry points. |
| **Structural reading, equality, sets, relations and allocation.** Data reading 92.9 s; encoded environments 95.9 s. Several other fixtures are under 16 s but may grow with larger inputs. | Propagate applicable sort/scan, injective nested equality, prepared source lookup, final-address accumulation and complete-value sharing. Profile list `map_of`, repeated sorting, deep equality, environment traversal and allocation as source size grows. | Universal result equations over malformed and differently presented inputs as well as formed values. Sort only under an established order/encoding contract. Keep counted multiplicity and original occurrence order. |
| **Inference, matching, guided reasoning and candidate assembly.** Native-child reasoning 147.8 s. [Factor_Schema_Generation](theories/Factor_Schema_Generation.thy) scans possible calls during premise joins; [Finite_Inference_Development](theories/Finite_Inference_Development.thy) repeatedly computes whole rounds; guided investigations obtain related states at successive depths; `finite_candidate_assemblies` filters `fPow parts`. | Index calls by structural callee/pattern conditions; share complete matching fragments and successive states; evaluate dependency-triggered increments with an exact closure/history equation. Instantiate existing demand and directed-contribution machinery before proposing a new search engine. | Preserve all compatible bindings, original premise occurrences, material checks, candidates and residual reasons. Replacing powerset enumeration by finding one sufficient candidate changes the result contract unless an established caller needs only that result. Do not prune by arbitrary depth, score or unsupported “no progress”. |
| **Observation, comparison and revision across every family.** Even optimized history spends 14.095 s in cycles. `subject_investigation_selected` recomputes a relation in its unrefined definition; assessed observations and repeated relation membership can revisit large row lists. | Reuse the shared cycle and investigation laws broadly. Prepare the actual observation relation once; consider exact indexed rows/sets and batch all independent initial selections. | Preserve all comparison pairs, selected/adequate candidates, withdrawals, repair witnesses and followed residuals, including repeated indices. A supplied Boolean matrix has no new subject authority. |
| **Reporting and host verification.** Optimized replay reporting alone is 33.817 s. The newer workflow serializers recursively print whole sources/stages/reports. `Complete_Value_References` itself uses linear lookup and append; `shared_artifact_reports.read_transport` materializes all records, and compressed checks make multiple passes. | Apply complete artifact references to the workflow/development/certificate families; factor a generic codec. Profile native dictionary construction, field conversion, string construction, compression, parsing, reconstruction and comparison. If needed, refine exact dictionary lookup and use bounded streaming/chunking. | Decode every original ordered record exactly. Keep reference integrity, end-of-stream/truncation failures and whole-record checks. Hashes identify storage bytes, not semantic equality. Streaming and compression must not hide partial or omitted reports. |
| **Bootstrap, proofs, exports, startup and evidence copying.** Current shared proof steps take about 349–380 s, diagnostics 20–31 s, and exports around 1 s; the previous cold start also rebuilt HOL. | Reuse accepted exact source contexts through `proved_context_partition` and checked exports; share dependency proofs and runtime startup across appropriate batches. Profile repeated input hashing/archive copies and parser passes. Keep a bounded, verified reusable build cache instead of repeatedly discarding useful base heaps. | Changed import contexts invalidate reuse. A warm proof/export is never reported as a fresh reconstruction. Preserve independent cold reconstruction as a release check, not the inner edit loop. Native execution optimization and host scheduling remain separate claims. |

These rows cover measured family costs and shared algorithmic dependencies.
They do not pretend to be an exhaustive per-function profile. Every unmeasured
entry stays in the coverage ledger until profiled or given an explicit justified
non-executable status. A fast small fixture does not exempt its mechanism from
scale testing.

## Principles and admissible optimization

Use the owner's directions and corrections in
[plan.md §0](plan.md#0-status-authority-and-governing-principles),
[REASONING_REUSE.md](REASONING_REUSE.md), and the workflow. Their implications for
this work are concrete:

| Direction | Required discipline |
|---|---|
| Structurality and explicitness | Identify the complete function input, source/authority context, result and observation contract. Make cache keys, applicability guards, preparation boundaries, schedule dependencies and measured workload explicit. No host representation supplies semantics. |
| Non-conflation | Keep performance, semantic equality, scope adequacy, proof validity, evidence retention and adoption separate. A successful process exit, a faster fixture or a matching hash cannot replace native admission. |
| Irredundancy and first-use factoring | Prove one reusable complete-result refinement, instantiate it with its actual prerequisites, and remove redundant computation at those uses. Avoid a separate optimization framework for each family. Keep logically distinct judgments even when their computation is shared. |
| Non-nominality | No special truth path for familiar method IDs, source names or fixture cases. Fast paths recognize actual structure or proved invariant premises and have an exact fallback. References must recover complete values; pointer identity or a digest alone is insufficient. |
| Exact presentations and intrinsic links | Prove injectivity/recovery and composition for new representations. Permitted changes of unordered presentation need an explicit correspondence; ordered queries, ledgers, sockets and counted data retain their required distinctions. |
| Independent notions and meaningful abstraction | State the original operation independently of the optimization. Preparation, caching, indexing, syntax accumulation, parallel maps and codecs become reusable contracts that reduce work without redefining what counts as success. |
| Completeness and criticism | Preserve whole contributors, all controls, all original observations and residual evidence. Independently criticize the benchmark scope and optimized checker as well as the implementation. Small-input equivalence is not a universal proof or a scale result. |
| Self-application and predecessor authority | Use the native workflow to construct and compare covered optimization candidates and follow its residuals. Its own optimization is judged under the established predecessor contracts; it cannot lower its admission conditions to make itself fast. |
| Practical usefulness with quality | Measure useful complete development, not just inner loops. Maintain batching and actual concurrency on 16 cores/32 threads, bounded memory/storage, recoverable failures and reconstructible evidence. Preserve problems conditions 1–6; theoretical accumulated-process bounds under 5b remain deferred until after genesis. |

The primary refinement target is `optimized input = original input` for the
whole result, on the declared complete domain. Where a representation changes,
state the exact decode/transport equation instead. A fast path conditional on
an invariant must retain its evidence and the original fallback outside that
boundary. Cache eviction may change cost; it must not change answers or remove
the independently sufficient evidence boundary.

Timing is physical observation. To use a timing result as a development
criterion, connect the actual run, complete input, resource boundary and
measurement operation to that criterion. Do not submit an authored “fast” facet
or let the host clock establish semantic adequacy. New profile/selection adapters
must enter the same internal-account workflow as the operations they assess.

## Implementation batches

### 1. Expose complete stages and prepare the first executable batch

Start from the inventory and actual high-cost source-development, steering,
requirement and certificate/graph subjects. Prepare their stage decomposition,
sharing candidates, generic-refinement imports and complete-reference reporting
together. Stage boundaries should separate source reading, generation, guard
construction, evaluation, evidence checking, inspection, comparison, revision,
installation, query and reporting. Instantiate the packet-stage equation pattern
so the staged operation reconstructs the original complete result.

Reuse [parallel_packet_execution.py](tools/parallel_packet_execution.py)'s timers
and [isabelle_native_execution.py](tools/isabelle_native_execution.py)'s runtime
and input tracking through a shared adapter. Do not maintain family-specific
string replacement as the general architecture. Record native timings/counters
separately from startup, proof/export, parsing, retention and roundtrip overhead.

Exercise the complete first batch promptly on original subjects and representative
real requests; collect failures and repair them in groups. Use already accepted
unchanged exports where available. If absent, build one combined needed source
closure, retain that usable checked context, and avoid repeated clean builds.
Initial scale/cost probes can be bounded, but bounds and incomplete runs must
remain visible and cannot replace the final complete workload.

**Gate:** every measured stage belongs to the complete original operation,
all original conditions and reports are available, and the resulting native
criticism determines the next refinement rather than merely confirming a
preselected implementation. Missing subject or cost-observation contracts remain
development obligations; no retrospective investigation repairs an outside choice.

### 2. Reuse the established refinements across covered exports

Factor a reusable execution-refinement import layer where dependencies and types
permit. Instantiate shared comparisons/cycles, prepared inspections, accumulated
syntax, structural equality and complete reference transport across the first
batch, then every applicable inventory family. Keep family-specific correctness
theorems local and consume them through the generic contracts.

Check generated code for the actual selected equations, preparation occurring
outside inner loops, delayed fallback branches and actual parallel calls. Merely
adding an import or a `let` binding does not establish that the compiler avoids
duplicate work. Prevent conflicting code equations and import cycles; perform
one joint proof/export/diagnostic review for the affected group.

Where independent computation exists, run the Eval export through Isabelle's
Pure runtime. Standalone SML and a high thread setting do not activate the same
parallel behavior. Batch independent contexts, inspections, conditions where
independent, and revision selections, preserving output order and duplicates.
Join dependent work before admission or reporting. Budget workers across nested
maps and simultaneous processes rather than assigning sixteen to every process.

**Gate:** complete-result proofs, generated-code inspection and full differential
results establish the refinement; controlled timings show its actual benefit.
No family receives a blanket “optimized” status from importing the layer.

### 3. Remove repeated source work and refine growing algorithms

Use the measured results to develop generic prepared source, compiled-condition,
admission and installation contexts. Reuse actual complete computations across
control variants only when their conditions match the existing successful-result
or constructor-invariant laws. Cache keys include every semantically read source,
binding, site, goal, scope and policy dependency, or have a theorem justifying
each omitted component. Avoid large linear caches whose lookup/deep-key equality
cost recreates the original bottleneck.

In parallel, where profiles justify it, prepare exact indexing/delta candidates
for inference rounds, joins, matching, directed construction, relation lookup
and reference dictionaries. Existing demand and application-construction laws
are the first reuse points. Prove closure and complete-output equivalence, with
original history/diagnostic order where the interface exposes it. If output
itself is necessarily large, sharing or reconstructible presentation can reduce
physical repetition; dropping required alternatives is not a speedup.

**Gate:** parameter sweeps show improvements at realistic source, candidate,
binding, graph and history sizes. Preserve failures, unavailable results and
language obstructions. If an operation remains dominant, keep it open and
continue refinement; do not stop after easier microbenchmarks pass.

### 4. Finish transport, build reuse and inventory coverage

Carry the same proven packet/codec/refinement pattern through all remaining
families and the uncovered exporting theories and built-in investigations.
Separate reusable native values from their serialized occurrences. Keep complete
decoding and independent reference comparison while reducing repeated conversion,
copying, parsing and whole-log materialization. Retain the original inputs,
contracts, source closures, recipes and compact measurement records, not expanded
bulk. Keep a bounded cache of useful validated build/runtime artifacts; obsolete
failed copies are removed after their diagnostic evidence is retained.

Use isolated working copies, fixed validation inputs and background checks.
One worker performs the development, as required by the repository; process and
native computation parallelism remain available. While a batch validates,
continue independent next work. Review combined proof, execution, diagnostic,
transport and performance results before dependent integration.

**Gate:** every current recipe and other operative entry point has an explicit
coverage/result status, and no omitted slow family is hidden behind an aggregate
speedup. Reconstruct accepted output independently from source at the combined
integration boundary and run the applicable repository checks.

### 5. Demonstrate the whole development path is usable

Run real required work through the closed native workflow and computed dispatcher,
including candidate construction, independent criticism, repair, admission,
source installation, subsequent query and retention where applicable. Use the
same original requirements before and after refinement. Measure complete accepted
and subsequently consumed work, repeated-use cost, refusal and repair latency,
memory/storage pressure and failures, including production of the next request.

Seek the requested orders-of-magnitude gains for the dominant multi-minute paths
and for the complete workload. This is a target to demonstrate, not a theorem
inferred from the prior two cases. Parallelism on sixteen cores alone cannot
provide arbitrary hundredfold speedups. Measure the remaining serial fraction,
startup/output floors and unavoidable output size; use those results to direct
additional sharing and algorithmic work. Already sub-second cases still need
scale coverage, without inventing a claim that each primitive can improve 100×.

**Gate:** the whole machinery meets acceptable observed cost for actual repeated
development with the complete quality requirements intact. Preserve both
per-family and end-to-end results so one spectacular ratio cannot mask another
remaining bottleneck. Unmet cost or coverage conditions stay open. This is the
live usefulness gate under problems condition 5a, not the deferred global cost
theory or a claim of genesis.

## Validation and performance evidence

For each batch retain the original problem, applicable general refinement,
instantiated premises, actual candidates, computed observations, independent
criticism, full results, reasons and residuals. Route covered questions through
`Factor_Development_Cycle`, `Factor_Development_Steering` and
`Factor_Steered_Development`; use `Factor_Source_Development_Cycle` for admitted
source changes. The ten-producer fixtures do not judge arbitrary optimization
methods without actual subjects and corresponding contracts.

For history refinements, instantiate the existing
[Factor_Digit_History_Result_Candidates](theories/Factor_Digit_History_Result_Candidates.thy)
framework: it computes additional producers on complete original subjects,
keeps every earlier method, and assesses against the original reference without
assuming that a proposed producer is correct. Reuse that construction pattern
for other operation families through their own subject equations, including
deliberately defective candidates. Keep semantic comparison, independent evidence
checks and the separately established physical-cost observation as distinct
requirements; a fast but incomplete producer must remain inadequate.

Prove universal complete-result or presentation-transport equations, then compare
complete actual results on original and expanded subjects. Include empty and
malformed inputs, conflicting/repeated keys, equal values at distinct occurrences,
changed bindings, absent evidence, all optional failure levels, stale caches,
cache miss/eviction, ambiguous choices, deep graphs and large shared artifacts.
Exercise controls that omit individual gates and require their original failures.
Preserve independent reference computations and their original condition meaning.
Hash equality alone is not the whole-result comparison.

Measure at least these separate boundaries: cold proof/build, accepted-export
startup, native stages, reporting/transport, independent verification, warm
repeated request and complete development cycle. Record exact source/toolchain,
inputs and cardinalities, worker settings, concurrent jobs, wall/user/system/GC
time, peak memory, bytes and storage cost. Benchmark baseline and candidate under
comparable resource conditions; repeat noisy measurements and report variation.
Use one-worker and multi-worker runs to distinguish sharing gains from concurrency.
Do not add overlapping stage timers or compare a warm inner loop with a cold
end-to-end baseline. Timeouts are incomplete observations, not negative answers.

Derive scope-sensitive budgets from actual development needs before acceptance;
do not move them after seeing a candidate's result. Report the speedup ratio for
each equal-workload boundary, the absolute remaining time and the work actually
offloaded. Universal semantic proofs and executable equality checks do not prove
physical speed; physical speed does not discharge those proofs. Theoretical
dependence on accumulated process remains explicitly deferred under condition 5b.

## Complete current recipe inventory

Times below are retained successful **execution-step wall seconds**, excluding
the separately recorded proof, diagnostics and export steps but including each
step's own startup, native work, transport and checks. They are profiling leads,
not normalized per-request costs or exclusive inner-function timings. Workload
sizes and contention differ. “Earlier receipt” means the current verification
boundary explicitly reuses the checked receipt at `eba0edc`; all current source
manifests were checked unchanged. E means Eval/Pure, S means standalone execution.
Each family links to its authoritative current verification record, which names
its source and report boundaries and, where needed, the earlier receipt.

| Family | Runtime | Execution steps (seconds) | Timing source |
|---|:---:|---|---|
| [allocated-environments](validation/reconstruction/allocated-environments-verified.json) | S | comparison 3.1 | Current receipt |
| [artifact-lookup](validation/reconstruction/artifact-lookup-verified.json) | S | comparison 0.7 | Current receipt |
| [cached-grafts](validation/reconstruction/cached-grafts-verified.json) | S | comparison 15.3 | Current receipt |
| [certificate-coverage](validation/reconstruction/certificate-coverage-verified.json) | S | comparison 298.1 | Earlier receipt |
| [certificate-development](validation/reconstruction/certificate-development-verified.json) | S | comparison 235.3 | Earlier receipt |
| [certificate-input-development](validation/reconstruction/certificate-input-development-verified.json) | S | comparison 293.9 | Earlier receipt |
| [certificate-scope-repair](validation/reconstruction/certificate-scope-repair-verified.json) | S | comparison 97.5 | Earlier receipt |
| [certified-causes](validation/reconstruction/certified-causes-verified.json) | S | comparison 298.2 | Current receipt |
| [concurrent-history](validation/reconstruction/concurrent-history-verified.json) | E | comparison 51.5 | Current receipt |
| [concurrent-replay](validation/reconstruction/concurrent-replay-verified.json) | E | comparison 100.9 | Current receipt |
| [constructed-history](validation/reconstruction/constructed-history-verified.json) | S | comparison 2131.2 | Current receipt |
| [data-reading](validation/reconstruction/data-reading-verified.json) | S | comparison 92.9 | Earlier receipt |
| [decision-replay](validation/reconstruction/decision-replay-verified.json) | S | comparison 732.6 | Earlier receipt |
| [digit-allocation](validation/reconstruction/digit-allocation-verified.json) | S | comparison 3.2 | Current receipt |
| [digit-generation](validation/reconstruction/digit-generation-verified.json) | S | comparison 28.7 | Current receipt |
| [digit-history](validation/reconstruction/digit-history-verified.json) | S | comparison 1873.5 | Current receipt |
| [digit-replay](validation/reconstruction/digit-replay-verified.json) | S | comparison 5731.7 | Current receipt |
| [encoded-environments](validation/reconstruction/encoded-environments-verified.json) | S | comparison 95.9 | Current receipt |
| [environment-grafts](validation/reconstruction/environment-grafts-verified.json) | S | comparison 12.2 | Current receipt |
| [environment-updates](validation/reconstruction/environment-updates-verified.json) | S | comparison 3.2 | Current receipt |
| [generation-records](validation/reconstruction/generation-records-verified.json) | S | comparison 106.8 | Earlier receipt |
| [graft-admission](validation/reconstruction/graft-admission-verified.json) | S | comparison 7.6 | Current receipt |
| [history-index](validation/reconstruction/history-index-verified.json) | S | comparison 1209.5 | Current receipt |
| [indexed-generation](validation/reconstruction/indexed-generation-verified.json) | S | comparison 23.8 | Current receipt |
| [known-history](validation/reconstruction/known-history-verified.json) | S | comparison 1819.2 | Current receipt |
| [literal-replay](validation/reconstruction/literal-replay-verified.json) | S | comparison 4.8 | Earlier receipt |
| [native-admission](validation/reconstruction/native-admission-verified.json) | S | comparison 260.4 | Earlier receipt |
| [native-certificate-replay](validation/reconstruction/native-certificate-replay-verified.json) | S | comparison 200.6 | Earlier receipt |
| [native-certificates](validation/reconstruction/native-certificates-verified.json) | S | comparison 549.0 | Earlier receipt |
| [native-child](validation/reconstruction/native-child-verified.json) | S | baseline 1.7; catalog 1.3; inputs 2.6; reasoning 147.8 | Earlier receipt |
| [native-derivations](validation/reconstruction/native-derivations-verified.json) | S | comparison 548.5 | Earlier receipt |
| [native-development](validation/reconstruction/native-development-verified.json) | E | producers 256.0; questions 100.7 | Current receipt |
| [native-evaluation](validation/reconstruction/native-evaluation-verified.json) | S | comparison 2.4; native 60.1 | Earlier receipt |
| [native-extensions](validation/reconstruction/native-extensions-verified.json) | S | extensions 19.5 | Earlier receipt |
| [native-graphs](validation/reconstruction/native-graphs-verified.json) | S | comparison 925.3 | Earlier receipt |
| [native-histories](validation/reconstruction/native-histories-verified.json) | S | comparison 242.3 | Earlier receipt |
| [native-nodes](validation/reconstruction/native-nodes-verified.json) | S | comparison 69.9 | Earlier receipt |
| [native-requirements](validation/reconstruction/native-requirements-verified.json) | S | comparison 476.6 | Current receipt |
| [native-sources](validation/reconstruction/native-sources-verified.json) | S | observations 1.8; extensions 79.6 | Earlier receipt |
| [native-steering](validation/reconstruction/native-steering-verified.json) | E | subjects 405.2; empty 12.7; first 188.3; questions 439.4 | Current receipt |
| [native-workflow](validation/reconstruction/native-workflow-verified.json) | E | workflow 39.7; requirements 51.2; input-scope 4.0; expanded 77.2; requests 16.7; expanded-requests 31.5 | Current receipt |
| [quoted-history](validation/reconstruction/quoted-history-verified.json) | S | comparison 1831.4 | Current receipt |
| [required-causes](validation/reconstruction/required-causes-verified.json) | S | comparison 38.5 | Current receipt |
| [required-history](validation/reconstruction/required-history-verified.json) | S | comparison 176.3 | Current receipt |
| [requirement-decisions](validation/reconstruction/requirement-decisions-verified.json) | S | comparison 57.8 | Earlier receipt |
| [requirement-plans](validation/reconstruction/requirement-plans-verified.json) | S | requirements 1.6 | Earlier receipt |
| [requirement-sources](validation/reconstruction/requirement-sources-verified.json) | S | source-boundary 1.2; retained-clauses 1.4; native-meanings 1.1; native-plans 1.2 | Earlier receipt |
| [source-development](validation/reconstruction/source-development-verified.json) | E | sources 1168.7; empty 14.1; first 191.4; requests 1178.2 | Current receipt |
| [use-allocation](validation/reconstruction/use-allocation-verified.json) | S | comparison 7.7 | Current receipt |
| [use-codecs](validation/reconstruction/use-codecs-verified.json) | S | comparison 6.5 | Current receipt |

The census used `reconstruction_sources.recipe_inputs` on every
`tools/reconstruct_*.py`, `investigate.source_graph` and `import_context` on every
current theory, and the recipes' local Python import closures to identify the
runtime adapters. It inspected every current `*-sources.json` and corresponding
`*-verified.json`; indirections were followed through local Git with their recorded
byte identities. Import coverage establishes availability only. These physical
and dependency observations do not supply an observation-satisfaction table or
prove semantic applicability of a proposed optimization.

Completion of this plan's implementation requires the whole inventory and its
non-recipe complement, all applicable semantic gates, controlled comparative
measurements and actual development usefulness. A document, a profile, a green
build, or two optimized families alone does not meet that objective.
