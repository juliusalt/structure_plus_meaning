# Making native development and validation fast

Updated 2026-09-17 after the native computation refinements, linear lineage
verification, heapless checks, a repeated complete source proof and a
resource-utilization review. By the owner's direction, optimization now pauses and
work moves on to actually using the machinery (remaining work, item 4).
Superseded measurements remain historical evidence in their retained files.

## Current result

**An edit that changes executed native code is validated in about 70 seconds.**
Every recipe still executes only proved report presentations: 50 recipe boundaries
with 57 retained report words over **1,677 theories**, 155 tool tests and 35 kernel
tests (two optional skips). All words below were identical to their accepted
boundaries in every cycle.

| Accepted cycle | Proof | Export | Recipes and host tests | Total |
|---|---:|---:|---:|---:|
| Start of this work (structural term comparison) | 63.54 | 7.02 | 126.83 (48 recipes) | 227.88 |
| Canonical listings, ordered functionality, field-wise target equality, shared policy scopes, keyed word table | 65.65 | 8.13 | 117.06 | 226.47 |
| One-pass three-outcome row, artifact and term comparisons | 69.80 | 9.33 | 88.56 | 207.83 |
| Formation checked once per guarded definition, pattern, call and vector reading | 82.22 | 10.93 | 58.29 (34 recipes) | 196.45 |
| Sized word reference keys computed in parallel | 75.35 | 12.58 | 62.08 | 201.82 |
| Linear lineage verification, complete data walks, duplicate exports retired | 65.90 | 3.82 | 55.84 | **135.07** |
| Heapless check on the complete-proof base, ordered unreferenced positions | **36.94** | 2.32 | 47.64 (11 executed, 39 reused) | **93.20** |
| Generation checks compare targets and predecessors as values | 36.34 | 2.32 | **28.55** (3 executed, 47 reused) | **73.56** |
| Final state: eight jobs, default heaps, digit replay with 16 workers | 36.79 | 1.77 | **24.25** (digit replay executed) | **67.65** |

Base and impact analysis fell from 8.55 to 0.23 seconds and recipe impact from 5.27
to 0.31 seconds. The sum of all fifty recipe times fell from 692.5 to 331.6 seconds;
digit replay from 126.83 to 28.6 seconds, certified causes from 35.37 to 21.3 seconds
and the five history families from 46–57 to 12–22 seconds. With every recipe
executing at once, digit replay still takes about 46 seconds and bounds that phase. Schedules and concurrency
differ between cycles, so these are observed costs, not controlled ratios.

A **complete source proof** of all 1,675 theories from HOL took **470 seconds**
(454 session seconds, 3,060 CPU seconds, 16 threads) instead of the previous 830
seconds (815 session seconds, 4,940 CPU seconds). It is the active one-level base.

The [refinement cycle measurements](validation/reconstruction/native-computation-refinement-measurements.json)
record every cycle, its phases and per-recipe times, together with the lineage,
session-overhead, export, runtime-option and attribution diagnostics. The
[current inventory](validation/reconstruction/current-verified.json) and
[incremental receipt](validation/incremental-check.json) bind the accepted result;
the [migration](validation/reconstruction/native-presentation-migration-measurements.json),
[execution reuse cycle](validation/reconstruction/execution-reuse-cycle-measurements.json),
[storage cycle](validation/reconstruction/storage-current-cycle-measurements.json),
[staged digit comparison](validation/reconstruction/staged-digit-reuse-measurements.json),
[direct proof](validation/reconstruction/direct-bootstrap-proof-measurements.json)
and [earlier full-source](validation/reconstruction/storage-cold-proof-measurements.json)
measurements retain their scopes. Practical gate 5a, complete edit-to-commit
attribution, remaining coverage and actual native-driven development remain open.

## Reusing accepted executions

A recipe execution reads its exported module, the subject contracts exported with
it, its own Python closure, declared fixtures, the expected report boundaries and
the Isabelle/Poly/ML runtime. Theory sources reach it only through that export;
the accepted proof context separately establishes that the export belongs to the
current sources. `incremental_check.py` records exactly these digests as the
**execution boundary** of every accepted execution.

After export, a recipe whose manifest changed but whose complete execution boundary
equals its retained accepted boundary is **reused**: its complete report boundaries
apply without repeating the computation. Any difference in module, contract,
execution tool, fixture, expected reports, toolchain or runtime file executes the
recipe again. Proof-stage tools such as `prove_context.py` belong to recipe manifests
but not to execution boundaries, because they only produce the export. Failed,
unequal or boundary-free records are never reused. `--all-recipes` still executes
everything. Retention records the new manifest, the current proof and context
receipts and the reused module digest beside the original execution record; the
native runtime digests are rechecked at completion and at retention.

The 38 boundaries of the preceding cycle's executions were recorded from evidence,
not assumed. Their archived stage receipts in the verified cleanup archive record
the same exported module that the current proof context generates for every
recipe, and all 1,425 recorded tool, fixture, report, contract and runtime digests
equal the recorded boundaries. Isabelle therefore regenerated byte-identical code
across different proof contexts. The remaining 12 recipes had no archived receipt
in the current archive and executed once. Five tests cover the boundary contents,
theory-only edits, changed exports, contracts, tools and runtime, failed records,
and retention of a reused execution.

The concurrent-replay recipe was retired. Its report value and selections were
defined as those of digit replay, both exports used the same parallel stage code
equations, and both retained complete 20,519,284-byte words were identical.
Digit replay retains that boundary; the unused aliases and export theory were removed.

## Proof cost

**Inline code checks.** 364 `export_code … checking SML` commands each started a
separate Poly/ML process and compiled their code closure on the theory's
sequential path. In the previous complete proof they took 1,378.8 command seconds;
in the preceding cycle's 219 rebuilt contexts, 70 checks took 460 of 892 seconds.
327 checks named only constants that accepted recipe exports compile and execute;
they were removed. 36 checks name constants no recipe executes or use quoted term
syntax, and remain; one more went with the retired concurrent-replay aliases.
The Eval exports that recipes consume are unchanged, as the 38 identical module
digests show.

**Forked proofs and thread count.** `prove_context.py` uses Isabelle's default
`parallel_proofs=1`. The option carries only Isabelle's `build` tag, so it is not
part of session content and does not change heap currency. The repeated complete
source proof under this setting and the reduced code checks took 454 session
seconds instead of 815. Ready tasks waited in 93 % of its statistics samples, so
the build is CPU-bound, but its heap peaked at 15.8 GB of the 16 GB address space of
the compact 32-bit Poly/ML heap: memory, not threads, bounds a complete proof, and it
keeps 16 threads. An incremental proof of 99 theories took 32 session seconds with
16 threads and 32 seconds with 32 threads (260 and 398 CPU seconds); its critical
path of export commands bounds it, so checks keep 16 threads.

**Code exports.** `export_code` commands take 200–280 of the 250–330 CPU seconds
of an incremental proof of the execution theories. Code generation is not shared
between export commands, even for identical constant lists in one theory
(3.6 seconds each), and exporting only the report value, selections, scope and word
fold instead of the recorded constants saves about five percent. Two export
theories duplicated recipe exports without any consumer and were retired.

**Stored heaps.** A child session that stores its heap shares common data over the
whole loaded heap and saves the child: on the former eleven-level lineage a trivial
child cost 11 session seconds, on a one-level base 7 seconds, and without a stored
heap 1 second; an incremental proof of 99 theories spent about 26 of its 57
session seconds outside theory processing.

## Reusing accepted proofs across edits

`proof_contexts.py` records the actual provider session and qualified theory for
each complete unchanged import context. A changed ancestor invalidates its old
dependents even when their own text is unchanged. A new child supplies rebuilt
contexts; independent contexts continue to come from their original providers.
`export_proved_code.py --context` exports from those actual sessions, including
mixed parent/child requests. It does not infer a provider from a theory basename.

**Checks store no heap.** Rebuilt execution and presentation theories are consumed
through their code exports, which the session database holds; import contexts are
needed only from the base. `incremental_check.py check` therefore rebuilds every
theory changed since the accepted base into a session without a stored heap
(`prove_context.py --without-heap`). Such a context records `stored_heap: false`,
which must agree with its build command; it is identified by its database, checked
for currency without `-b`, supplies exports, and is refused as a parent or as the
active base. The base stays selected, so the lineage never grows. `check
--advance-base` stores the heap of the rebuilt theories and selects that check as
the next base when later edits should reuse its import contexts; a complete source
proof adopted with `adopt` resets the base to one level.

**Lineage verification is linear.** Verifying an accepted lineage re-read every
ancestor input, including every ancestor heap, at every level, and recomputed import
closures per theory: 126,331 digests for 17,712 distinct inputs and 9.46 seconds at
ten levels, repeated about six times per check. One verification pass now reads each
distinct input once, scans each retained theory text once per name and digest, and
decides import contexts once per theory, giving the identical verified context in
1.37 seconds; one check shares its verified lineage between base selection,
adoption and activation. Recipe manifests are projections of the one source graph
already read and digested, and their inputs are checked once when the check
completes.

Accepted source directories are immutable because Isabelle includes absolute
paths in session currency. The active pointer `/tmp/structural-active-context.json`
selects the accepted base. Explicit `adopt` accepts an already proved immutable
context with a stored heap after validation. Original sources, rewritten import
headers, helper sources, session configuration, heaps and databases remain checked;
requalification changes imports but not theorem bodies.

Retention refuses a partial recipe inventory, missing or changed inputs,
conflicting input versions and invented host-test counts. Each distinct input is
rechecked before final acceptance and retention, including unchanged recipes.

```sh
python -B tools/incremental_check.py check --output /tmp/NEW-UNIQUE-DIR --jobs 8 --threads 16
python -B tools/incremental_check.py retain --output /tmp/NEW-UNIQUE-DIR
```

`establish` is a rare full-base operation, not a routine cycle. Never relocate an
accepted context or rebuild its named session from a copied directory. Keep
active check inputs fixed.

**Probing candidates on the accepted base heap.** A theory the base does not contain can
be loaded directly onto its stored heap, with every unchanged import resolved from the
heap session, so a first pass over new sources costs their own load instead of a
repository build:

```sh
python -B tools/probe_theories.py --work /tmp/NEW-UNIQUE-DIR [--theory NAME]
```

One probe per directory; `DIR/probe.log` streams while it runs. Registration is not proof
checking: with forked proofs the loader returns once a theory is registered and its
theorems are stated, so only the probe's own completion marker, reported as `loaded`,
says that the proofs were checked. `--parallel-proofs 0` checks each proof in place and
attributes the elapsed time to the command that does not return. A theory the base already holds is resolved
from the heap and reported, because the heap holds its dependents built against the
accepted text; `--prelude` supplies a theory stating added content on top of the heap and
`--substitute` resolves a changed base theory to it. The probe observes that candidate
sources load against accepted content and nothing about the dependents of a changed base
theory, so it selects work for the check rather than replacing it.

**Temporary storage is retired against the repository.**
`python -B tools/retire_temporary_storage.py --manifest FILE [--apply]` hashes every file
of each declared path, reports those byte-identical to a blob reachable in history, and
refuses the retirement unless the rest fall under a disposition whose replacement it can
check: retained evidence must be tracked at the recorded commit, a regenerable path must
name the command that rebuilds it. The record it writes,
[validation/temporary-cleanup.json](validation/temporary-cleanup.json), also lists the
kept paths with the same justification, so what remains under `/tmp` is stated to be
discardable and restorable.

## Native computation

**Refinements of this work.** Poly/ML time profiles attributed most native time to
canonical sorting, re-established formation and recomputed artifact rows, and call
counters located the operations. Each refinement is an exact code equation over
existing contracts; every affected word is unchanged.

- `Finite_Sorted_Set_Execution` recognizes an already canonical set or counted
  listing in one adjacent pass; `Finite_Ordered_Relation_Checks` and
  `RRA_Ordered_Artifact_Formation` decide functionality and formation from canonical
  keys without re-sorting; `Factor_Ordered_Target_Equality` compares artifact fields
  in row order and stops at the first difference.
- `Linear_Comparisons`, `Ordered_Artifact_Comparison` and `Ordered_Term_Comparison`
  compare rows, artifacts and terms in one pass with three outcomes, exactly in the
  order of their prefix keys; `Keyed_Value_References` and `Indexed_Term_Words` find
  first-occurrence word references through sized ordered keys computed in parallel.
- `Factor_Policy_Scope_Sharing` reads a policy cause's judgment scopes once for both
  existential checks; `Factor_Formation_Once_Definitions` lets definition, schema,
  pattern, premise, material, call and vector readings consume formation-free bodies
  so that each guarded entry checks formation once. Admission fell from 36.9 to 10.9
  seconds and native requirements from 23.8 to 6.8 seconds in that cycle.
- `Factor_Complete_Data_Walks`: in a formed artifact each node has at most one payload
  leaf value or one two-field record, so a complete data reading is one walk whose
  listing is compared once with the canonical carrier instead of joining interiors at
  every record. `Finite_Ordered_Set_Difference` subtracts canonical listings in one
  merge pass and computes unreferenced positions that way. Certified causes fell from
  36.85 to 21.3 seconds and its standalone report stage from 13.0 to 9.1 seconds.

`Factor_Formation_Once_Readings`, `Factor_Recovered_Graph_Sharing`,
`Parallel_History_Source_Rows` and `Parallel_Presented_Investigations` from the
preceding cycles establish formation once per bounded traversal, recover proof
graphs with one closure and compute independent source, assessment and truth rows
through exact parallel map equations.

**Generation checks by value.** Digit replay's export also imported an earlier
refinement that checked generations through complete words: at every node of every
recursive check it encoded the read and supplied locus, payload and cause artifacts
and every predecessor subtree as framed words. Call counters attributed 87.5 of
114.6 instrumented report seconds to 11,094 target encodings. Replacing only the
target comparison by field-wise target equality while keeping predecessor words
brought the word encoding into every export and slowed the history families by
25–48 %: their exports had always used the original equations, whose value
equality of generations and targets is cheaper. `Factor_Ordered_Generation_Checking`
therefore makes the original check and readiness equations the executable ones for
every export. Digit replay fell from 47.6 to 28.6 seconds in the check, and every
other affected export became byte-identical to its accepted execution, which was
reused.

**Measured remaining costs.** Digit replay's standalone report stage is 14 seconds,
dominated by canonical listing comparisons and artifact rows used as nested replay
identity keys (`Factor_Nested_Replay_Identity`), the same encode-to-compare pattern.
Formation guards are re-established at every guarded reading entry (141,819
artifact formation checks over 33 distinct artifacts before the generation change);
the digit store type already carries formation (`digit_allocated_environment_formed`)
with formation-free lookup readings. The remaining certified-cause cost is the data
walk's per-node scans of all incidence rows, bindings and the carrier, which an index
of the artifact built once per walk removes.

**Machine resources.** The machine has 16 cores (32 threads) and 64 GB. Load stays
far below 32 for structural reasons measured in this review:

- Memory, not processors, binds concurrency. Every native execution and Isabelle
  session is a Poly/ML process with its own heap (plus an Isabelle JVM launcher per
  execution). Twelve concurrent recipes with 3 GB initial heaps used 59.9 GB with
  1.9 GB available while the load stayed at 17.8; recipe times inflated from 331.6 to
  500.3 seconds. A single compact 32-bit Poly/ML heap is limited to 16 GB, and the
  complete proof peaked at 15.8 GB.
- Allocation and stop-the-world garbage collection limit parallel speedup inside a
  process: collection took 12–39 % of native time, and digit replay gained only 9 %
  from 4 to 16 workers.
- The computations are largely sequential: an incremental proof is bounded by its
  critical path of dependent export commands (32 threads used 398 instead of 260 CPU
  seconds for the same 32 seconds), and digit replay builds one packet and one word
  with a global artifact table.
- Concurrent Poly/ML processes slow each other through parallel collection and
  memory traffic even below full load: with eight jobs, default heaps and 28.8 GB
  peak memory (load at most 14.2), digit replay took 45.7 seconds instead of 28.6
  seconds beside two other recipes.

Checks therefore keep 16 proof threads, eight recipe jobs and default heaps; digit
replay uses 16 workers. Using the whole machine requires structural reductions of
per-process allocation and memory or independent smaller processes, not thread or
heap settings.

**Existing refinements.** `Parallel_Inspection_Caches` prepares actual distinct
reader keys under the complete computed-function contract and retains the original
finite inspection rows; `Parallel_Replay_Readers` applies it to both replay cache
families. `Parallel_Computed_Preparation` evaluates distinct complete keys in
parallel under exact-cache contracts and shares actual returned cause targets;
misses execute the original function. Ordinary digit replay uses the proved
parallel packet stages and complete prepared scope reports. `Finite_Term_Object_Words`
converts each distinct artifact table entry to rows once, with injective identity
laws preserving the prior indices, table and word. Exact counted folds and worklists
avoid stack exhaustion without dropping content. Earlier equality, prepared-order,
footprint, index, union and source-prediction candidates did not demonstrate a
benefit; their [decision](validation/reconstruction/decision-replay-cost-measurements.json)
and [replay](validation/reconstruction/replay-presentation-measurements.json)
evidence prevents repeating them without new evidence.

## Complete report words

Each notion has an independently defined presentation class whose local contract is
injectivity (`injective_presentation_class`); a composite presentation uses only the
contracts of its parts, and each report theorem only the composite's contract. Any
presentation may therefore be replaced by another member of its class without
changing any other proof. Presentations compose parameterized generic notions and
specialize them: indexed rows, subject reports, subject assessment and development
cycle packets and investigation outcomes in `Finite_Presented_Investigations`;
collection differences, observation comparisons, partial result and evidence
assessments and iteration and witness reviews in `Finite_Presented_Reviews`;
decision rows, families, contexts and investigation packets in
`Finite_Presented_Decision_Families`; native source problems, answers, evaluations
and evidenced results in `Finite_Presented_Native_Programs`; coordinate-parameterized
calls, applications, rules and readings in `Finite_Presented_Evaluations`; record
views in `Finite_Viewed_Values`; and workflow and reasoning notions in
`Finite_Presented_Workflows` and `Finite_Presented_Reasoning`. Earlier presentations
that are instances of these layers are defined through them with identical terms,
so their words are unchanged. No new presentation computes an observation of its
subject; report contents are defined by the presented report.

All fifty recipes have native words. The nineteen families migrated in this batch
were paired with their unchanged original comparisons in one accepted cycle before
their comparisons, request roundtrips and host fixtures were retired. The native
child controls, projections and guided constructions are definitions over the
existing child example; its native summaries equal the former host stages' results.

| Family | Word bytes | Standalone word seconds | Word-only recipe seconds | Preceding host recipe seconds |
|---|---:|---:|---:|---:|
| builtin-investigations | 25,624 | 1.27 | 2.37 | 8.68 |
| certificate-coverage | 28,258 | 3.97 | 4.57 | 6.68 |
| certificate-development | 564,443 | 3.12 | 3.97 | 8.68 |
| certificate-input-development | 758,086 | 4.07 | 4.67 | 11.68 |
| certificate-scope-repair | 50,342 | 3.37 | 4.12 | 7.02 |
| literal-replay | 52,715 | 3.32 | 4.22 | 7.47 |
| native-admission | 922,585 | 31.32 | 60.19 | 41.79 |
| native-child | 7,569,375 | 6.63 | 6.88 | reused |
| native-development | 30,692,955 | 17.59 | 42.86 | 28.06 |
| native-evaluation | 49,659 | 2.52 | 3.82 | 3.53 |
| native-extensions | 14,139 | 2.02 | 3.17 | 2.32 |
| native-histories | 410,973 | 3.82 | 4.32 | 7.33 |
| native-requirements | 2,033,835 | 13.99 | 42.69 | 17.90 |
| native-sources | 19,257 | 2.67 | 4.17 | 3.62 |
| native-steering | 45,803,794 | 42.63 | 50.76 | 66.38 |
| native-workflow | 2,619,325 | 15.28 | 13.22 | 53.65 |
| requirement-plans | 38,991 | 1.42 | 2.07 | reused |
| requirement-sources | 6,235 | 1.62 | 2.47 | 2.32 |
| source-development | 68,887,703 | 48.54 | 69.08 | 113.30 |

Standalone seconds are single word probes outside the cycles; recipe seconds ran
with six concurrent jobs. Several large development and requirement words take
longer than their former host stages: presenting multi-megabyte reports is now the
dominant cost there, which the presentation contracts allow to be optimized freely.
Earlier families keep their recorded words; accepted presentations that attach
computed row inspections (`Finite_Inspected_Values`, `Finite_Derived_Values`) remain
until their words are re-established.

## Investigation feedback

One accepted export serves all thirteen built-in investigations and 56 complete
cases; actual CLI requests took roughly 1.6–2.3 s. `investigate.py --proof` uses
that export and the requested operation's exact checked contract; wrong-operation
and missing contracts and changed sources fail before runtime. These modes retain
their finite subject contracts and do not admit arbitrary development plans or
establish native control. `execution_support.py` holds the shared source, evidence
and ML-literal operations, so CLI-only edits affect two recipes rather than all.

## Remaining work and adoption requirements

Prepare substantial independent candidates and checks together; expose actual
parallel computations and review combined results before dependent integration.
The measured speed work above is adopted. The useful remaining groups are:

1. Paused by the owner in favour of item 4: carry established formation through
   replay and history states, as the digit store type already does; index an
   artifact once per complete data walk; compare replay values without nested row
   keys; reduce per-process allocation so concurrent executions use the machine.
   Require a completed beneficial execution with identical words.
2. Optimize presentation implementations under their contracts: remove the derived
   observations still computed inside storage and decision presenters
   (`Finite_Derived_Values`, `Finite_Inspected_Values`, for example the formation
   Boolean of `finite_formed_environment_value`) by making them report content where
   a report needs them, deepen the remaining flat earlier presentations, and replace
   slow presentations of large reports (source development 68.9 MB, steering 45.8 MB)
   by faster members of the same classes, re-establishing each changed word once.
3. Complete the non-recipe coverage audit and its executions. The
   [syntactic inventory](validation/reconstruction/validation-entrypoint-inventory.json)
   lists CLI tools and modes without direct recipe execution; about thirty export
   commands outside recipes still run on every rebuild of their theories.
4. Demonstrate real development under native control, as revised with the owner in
   [native_control_plan.md](native_control_plan.md): every problem, including which
   problem to solve, scheduling, what an executor receives and improving the machinery,
   goes through one process; Isabelle theory and tool changes are admitted generations
   over a native development state read from Isabelle's theory export; problems are
   decomposed in depth so inert executors answer only narrow requests with their least
   context. Its first stages seed that state and carry one measured refinement from
   item 1 through the process.
   Faster fixture execution alone does not close that requirement.

[DEVELOPMENT_WORKFLOW.md](DEVELOPMENT_WORKFLOW.md) remains binding. Isabelle/HOL
retains its normative bootstrap role through genesis. Physical timings, host
metadata and hashes identify execution boundaries; they do not establish native
selection, criticism, original-subject satisfaction or authority. Reusing an
accepted execution establishes that an identical program already produced the
retained reports; it adds no new semantic claim. Preserve all candidates, facets,
refusals, witnesses, ordered ledgers, optional levels and complete original
evidence. Exercise changed bindings, stale caches, missing evidence, repeats,
empty or malformed inputs and defective controls.

The [cleanup record](validation/reconstruction/storage-temporary-cleanup.json)
identifies the verified local archive under `.git/native-speedup-evidence`, which
also supplied the archived receipts for the recorded execution boundaries.

Conditions 1 and 6, practical gate 5a, O-85, broader coverage and genesis remain
open. Theoretical cost gate 5b remains deferred until after genesis.
