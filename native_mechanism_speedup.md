# Making native development and validation fast

Updated 2026-09-17 from the accepted storage-presentation, staged-replay and
full-source proof batch. Superseded measurements remain historical evidence.

## Current result

**The current batch passed in 663.11 s.** It covers **1,649 theories** and all
**51 recipe boundaries**: 39 affected recipes executed and 12 complete input
manifests remained unchanged. The proof rebuilt 219 contexts and reused 1,430
workspace contexts. Both host suites passed: 147 tool tests and 35 kernel tests
(two optional skips). The inventory retains **2,604 physical report records**.

**The complete source proof passed in 830.44 s**, rebuilding all 1,649 project
theories from the installed HOL with zero project proof contexts reused.
The session itself reports 815 s elapsed and 4,940 s CPU. It overlapped integration;
it is neither an empty OS cache nor a cold execution of every recipe. Full-source
cost remains large. The prior 1,620-theory proof took 542.886 s under a different
source and scheduling boundary; the current batch does not establish a cold
speedup.

Thirty-two families now have native words: **20 use words alone and 12 passed
original comparisons and new words together**. Six previously accepted paired
stages were retired without resetting their complete native boundaries. The
original CLI checkers remain available. Nineteen recipe families still need
native words, including built-in investigations.

Ordinary digit replay now uses the already proved parallel packet stages and
complete prepared scope reports. Its standalone export matched every one of the
original 20,519,284 bytes in **130.31 s**; the integrated recipe took **322.78 s**
while other checks and the full-source proof ran. A new complete-cause-key cache
also proved and matched the full word but took 213.41 s in its probe and was not
adopted. These schedules do not support a controlled speedup ratio.

| Current measured boundary | Result |
|---|---|
| Complete affected validation | 663.11 s; 39 executed recipes, 12 unchanged complete manifests and both host suites. Six outer jobs. |
| Base and dependency checks | 4.21 s. |
| Incremental proof | 128.24 s; 219 rebuilt contexts. The actual proof closure imported 932 parent contexts. |
| Recipe input comparison | 5.42 s. |
| Export | 10.09 s; actual provider sessions and explicit client proof roots. |
| Recipe execution and host suites | 487.63 s. |
| Twelve-word prototype batch | 7.384 s; four jobs/four workers each, after the exact codec repair. |
| Staged digit probe | 130.309 s; presentation 94.991 s, word emission 27.754 s, eight workers. |
| Direct-proof probe | 51.378 s; 21 rebuilt contexts over 493 reused contexts. |
| Full source proof | 830.440 s; all 1,649 project theories from HOL, sixteen threads, parallel_proofs=0. |

The [current inventory](validation/reconstruction/current-verified.json),
[incremental receipt](validation/incremental-check.json) and
[current cycle measurements](validation/reconstruction/storage-current-cycle-measurements.json)
bind the accepted result. The [storage presentations](validation/reconstruction/storage-presentation-measurements.json),
[staged digit comparison](validation/reconstruction/staged-digit-reuse-measurements.json),
[direct proof measurements](validation/reconstruction/direct-bootstrap-proof-measurements.json)
and [full-source measurements](validation/reconstruction/storage-cold-proof-measurements.json)
retain their actual scopes, failures and repairs. Practical gate 5a, complete
edit-to-commit attribution, peak memory, remaining coverage and actual native-driven
development remain open.

The previously accepted shared investigation export still covers thirteen modes
and 56 complete cases; actual CLI requests took roughly 1.6–2.3 s. Those modes
retain their original finite contracts and do not admit arbitrary development
plans or establish native control.

## Reusing accepted proofs across edits

`proof_contexts.py` records the actual provider session and qualified theory for
each complete unchanged import context. A changed ancestor invalidates its old
dependents even when their own text is unchanged. A new child supplies rebuilt
contexts; independent contexts continue to come from their original providers.
`export_proved_code.py --context` exports from those actual sessions, including
mixed parent/child requests. It does not infer a provider from a theory basename.

Accepted source directories are immutable because Isabelle includes absolute
paths in session currency. The complete current proof is retained at
`/tmp/native-cold-storage-proof-1789621295299849636`; it supplies all 1,649
contexts directly from HOL. Its snapshot matches the current ROOT and every
original source hash. It passed the existing read-only currency and heap checks
before becoming the active context. Earlier provider chains and working copies
are recoverable from the [verified cleanup archive](validation/reconstruction/storage-temporary-cleanup.json).

Original sources, rewritten import headers, helper sources, session configuration,
heaps and databases remain checked. Requalification may change imports but not
theorem bodies. New proofs preserve the original project ROOT before execution
and verify that it and the checked inputs remain unchanged through completion.

**Correction to the old dry-run claim:** an underspecified
`isabelle build -n -d copy` was not a sufficient currency check. Explicitly
selecting the session with `-n -b`, all ancestor directories and the saved build
options checks the required stored heap without building it. The actual cold
context passed in 3.323 s with unchanged heap/database hashes. A relocated
fixture was refused and left the original heap unchanged. Heap payload identity
is also matched to Isabelle's successful session database entry.

An active pointer at `/tmp/structural-active-context.json` selects the accepted
context. Complete successful checks retain their child context for the next
edit. Partial or failed recipe checks do not advance it automatically. Explicit
`adopt` accepts an already proved immutable context after validation; it is proof
reuse, not admission of a native development transition.

The regression exercise changed only an ancestor's definition. Its unchanged
dependent theorem then failed, and the failed proof could not be adopted.
Repairing the theorem produced a new child; real exports from that child and
an independent ancestor executed with values 2 and 7. Unit controls also refuse
changed sources, helpers, providers, heaps, project configuration and incomplete
proof inventories. Optimized Python cannot bypass assertion-based adoption.

Retention now refuses a partial recipe inventory, missing or changed inputs,
conflicting input versions and invented host-test counts. It derives test counts
from the actual check. Each distinct source/tool/fixture input is rechecked
before final acceptance and retention, including unchanged recipes. The final
check also binds ROOT and its orchestration tools, refusing later changes.

Ordinary use:

```sh
python -B tools/incremental_check.py check --output /tmp/NEW-UNIQUE-DIR --jobs 6 --threads 16
python -B tools/incremental_check.py retain --output /tmp/NEW-UNIQUE-DIR
```

`establish` is a rare full-base operation, not a routine cycle. Never relocate
an accepted context or rebuild its named session from a copied directory.
Keep active check inputs fixed. Context-chain storage and selection of useful
older ancestors remain future work; this implementation does not prove a
bound independent of accumulated process.

## Investigation feedback and dependency boundaries

Eleven built-in registrations still pointed to export-wrapper theories after
those definitions had moved into `*_Base` theories. The fixed registrations name
the actual typed definition owners; contract identity checks were not weakened.
One shared accepted export retains all thirteen operations and their original
subject contracts. The 56-case recipe covers empty, partial, complete and
repeated selections, including distinct and collapsed pattern presentations.
All 56 inputs were formed; all complete native results were reviewed.

`investigate.py --proof` uses the existing accepted export and the requested
operation's exact checked contract. It retains original source, tool, case,
engine, runtime and contract evidence, without claiming a new proof in that
invocation. Wrong-operation and missing contracts and changed sources fail
before runtime. Omitting `--poly` now asks Isabelle's actual `ML_Settings` for
its executable; raw shell `ML_HOME` is unset on this installation.

```
python -B tools/investigate.py --proof /path/to/builtin_investigations.proof.json --threads 4 --output /tmp/NEW-REQUEST observation-scope --selected 0 1
```

The older source-building route remains available when no accepted export is
supplied. The new route is exercised through the actual CLI, not just an export
fixture. Its native observations retain their declared finite subject scopes;
it does not admit arbitrary prose questions or select the current development plan.

`execution_support.py` now holds thirteen shared source, evidence and ML-literal
operations. Their AST bodies are identical to the previous implementations;
67 clients use that module directly. The investigation CLI re-exports the public
helpers for compatibility. Actual import closure now makes **49 of 51 recipes
independent of CLI-only edits**; built-in investigations and native-child still
consume it. This avoids revalidating the whole suite for an unrelated CLI change.

Export receipts retain each module's complete import closure and its explicit
client proof roots, rather than every compatible theory in the workspace.
An unrelated edit does not invalidate that module; a changed required context
still does. The audit exposed additional proof requirements in native-child and
requirement-sources; those roots are now explicit in both export and source-only
recipe boundaries. Tests cover unrelated edits, retained extra roots and changes
to those roots during export.

## Native computation and complete report words

`Parallel_Inspection_Caches` prepares actual distinct reader keys through the
existing complete computed-function contract, then retains the original finite
inspection rows. Its list-cache counterpart preserves the exact original key
order. `Parallel_Replay_Readers` applies those equations to both replay cache
families. The generated code prepares `Par_List.map` results before dependent
lookup. Misses retain the original computation; no result or condition is supplied.

The bounded diagnostic isolated context 15's reader-cache preparation. Thirteen
completed graph reads consumed 83.475 s before the 100-second outer limit;
reference and source reads were much smaller. Other context construction and
candidate cells were also measured separately. These are physical diagnostics;
timeout supplies no semantic refusal or proof of global cost.

The earlier large adopted runtime change shares **actual returned cause targets**
across digit candidate assessments. `Parallel_Computed_Preparation` evaluates
distinct complete keys in parallel under the existing exact-cache contracts;
misses execute the original function. Each actual digit subject carries its own
prepared result function, avoiding equality on opaque stores or functions.
Generation presence, payload, source, package/application/replay readings and
all verdicts remain computed. Context 6 supplied sixteen method/target pairs
but only four distinct targets. The actual digit recipe improved from the
previous recorded 825.47 s to 279.14 s under different schedules.

`Finite_Term_Object_Words` retains complete artifacts for lookup and converts
each distinct table entry to rows once. Existing injective identity-map laws
preserve exactly the prior indices, table and word. Exact counted folds and
worklists avoid the earlier stack failure without dropping any content.
Other accepted structural changes and their contracts are recorded in
[REASONING_REUSE.md](REASONING_REUSE.md) and the retained measurement files;
completed mechanisms are not presented as proposed work.

Presentations compose named notions through existing pair, sequence, finite
collection and optional-value contracts. Stores use their original views.
Coordinates, addresses and indices retain distinct meanings. Canonical ordering
identifies a presentation; it is not invariance of programs that observe order.
Every source/result field, query occurrence, assessment, failure level and
malformed value remains accounted for. Shared artifact tables retain complete
values, and the host only packs native bits and checks the complete boundary.

| Family | Complete word bytes | Current batch recipe seconds |
|---|---:|---:|
| required-history | 159,908 | 29.20 |
| digit-history | 418,306 | 185.05 |
| known-history | 449,531 | 217.38 |
| quoted-history | 483,348 | 167.62 |
| constructed-history | 551,708 | 238.16 |
| digit-replay | 20,519,284 | 322.78 |
| decision-replay | 1,296,760 | 143.27 |
| native-nodes | 341,007 | 3.37 |
| native-graphs | 1,000,741 | 33.96 |
| native-derivations | 648,713 | 8.18 |
| native-certificates | 890,378 | 6.43 |
| history-index | 316,651 | 123.28 |
| indexed-generation | 550,833 | 3.07 |
| digit-generation | 743,867 | 3.57 |
| native-certificate-replay | 722,239 | 133.67 |
| requirement-decisions | 494,768 | 11.31 |
| required-causes | 495,123 | 15.61 |
| certified-causes | 5,538,773 | 57.30 |
| concurrent-history | 555,495 | 211.84 |
| concurrent-replay | 20,519,284 | 295.65 |
| artifact-lookup | 20,000 | 2.57 |
| environment-updates | 165,530 | 3.57 |
| allocated-environments | 203,706 | 3.42 |
| use-allocation | 376,332 | 3.02 |
| environment-grafts | 158,937 | 3.77 |
| graft-admission | 177,251 | 3.77 |
| cached-grafts | 407,523 | 4.62 |
| digit-allocation | 346,069 | 3.97 |
| use-codecs | 178,732 | 3.67 |
| generation-records | 350,679 | 5.97 |
| encoded-environments | 691,705 | 5.78 |
| data-reading | 104,639 | 4.77 |

The first twenty use words alone. The final twelve include both original
comparisons and new native words; their times are whole recipe times.
The twelve new presenters preserve complete original source/reference/result
values, actual inspections, all optional levels, counted paths, chain growth,
raw formation, codec budgets and additional original comparisons. Opaque stores
retain their original views and allocation counters with explicit identity laws.
`finite_derived_value` factors the common complete-value/derived-field contract
before its reuse by these families.

Use-codec initially exhausted the stack because large decoded natural coordinates
were expanded as unary terms. Flattening bit paths alone was insufficient.
The accepted repair uses the existing exact binary natural and digit-use
encoders, with proved identity equivalence to the original natural/use notions.
Every natural, path, optional level and refusal remains; there is no magnitude
cutoff or truncated report. All twelve final words passed beside unchanged
original comparisons.

Three bootstrap proof searches now instantiate existing facts directly: the
actual image witness in steering, the existing per-clause generation formation
law, and the relevant conjuncts of the complete source-installation run theorem.
Statements, definitions and premises are unchanged. In the isolated probe,
steering and installation commands took 0.002 s and 0.014 s; generation schema
formation still took 36.152 s. The new full-source run remains expensive: its
largest commands include child-source simplification (183.543 s), inference-claim
compilation (87.399 s), inference clauses (80.480 s), and generation schema
formation (72.344 s). Concurrent command times cannot be subtracted from total
build elapsed time.

**Earlier equality and prepared-order experiments did not demonstrate a useful gain.** Exact
fieldwise target equality completed in 268.31 s; adding proved prepared-key term
ordering completed in 265.32 s. Both matched all 1,296,760 baseline bytes, but
the earlier baseline probe took 260.76 s under another schedule. Neither
candidate is adopted. Presentation accounted for 265.566/261.691 s and word
emission only 0.133/0.218 s. A bounded profile showed sorting/list comparison;
it did not isolate the originating semantic operation. A packet-only diagnostic
hit its outer limit without counters and is incomplete evidence, not refusal.
See [the decision measurements](validation/reconstruction/decision-replay-cost-measurements.json).

Existing decision reader caching and shared investigation cycles are already
active. Earlier footprint/index/union experiments and source-prediction caches
also failed to demonstrate benefit; their [retained replay evidence](validation/reconstruction/replay-presentation-measurements.json)
prevents repeating those directions without new evidence.

## Remaining work and adoption requirements

Prepare substantial independent candidates and checks together; expose actual
parallel computations and review combined results before dependent integration.
The useful remaining groups are:

1. Finish native presentation for the remaining nineteen families, reusing existing
   notion contracts. Preserve complete old/new comparisons before retiring stages.
2. Reduce the measured dominant native computation and full-source proof costs.
   Use the current full-source command measurements above; the old installation
   and steering searches have already been replaced. Reuse existing exact
   mechanisms and require a completed beneficial execution.
3. Complete the non-recipe coverage audit and its executions. The
   [syntactic inventory](validation/reconstruction/validation-entrypoint-inventory.json)
   finds 74 check/run/roundtrip CLI tools, 50 directly called execution scripts
   and 24 tools without a direct recipe call. The new recipe exercises all
   thirteen built-ins through their common checker. Some remaining tools are
   shared helpers; other modes still need direct execution coverage. Direct calls, imports and proofs do not establish
   coverage of every mode, custom input, empty scope, roundtrip or growth case.
4. Demonstrate real development through native construction, criticism,
   admission, installation and subsequent use, with complete latency and
   failure/repair evidence. Then continue the native-control work in
   [native_control_plan.md](native_control_plan.md). Faster fixture execution
   alone does not close that requirement.

[DEVELOPMENT_WORKFLOW.md](DEVELOPMENT_WORKFLOW.md) remains binding. Isabelle/HOL
retains its normative bootstrap role through genesis. Physical timings, host
metadata and hashes identify execution boundaries; they do not establish native
selection, criticism, original-subject satisfaction or authority. Use the closed
native workflow for covered questions and retain missing operations as explicit
requirements. The current physical refinements do not supply the missing native
selection account.

Preserve all candidates, facets, refusals, witnesses, ordered ledgers, optional
levels and complete original evidence. Exercise changed bindings, stale caches,
missing evidence, repeats, empty/malformed inputs and defective controls. Cached
construction does not admit arbitrary modified reports.

The [cleanup record](validation/reconstruction/storage-temporary-cleanup.json)
identifies the verified local archive under `.git/native-speedup-evidence`.
It retains the exact source, proof, execution, diagnostic and earlier archive
contents. Cleanup removed 77 work directories and 187 standalone files/old heap
artifacts after full verification: 17.31 GB of expanded data became a 3.70 GB
archive. The [post-cleanup check](validation/reconstruction/storage-cleanup-verification.json)
confirms every retained input still matches and the current proof remains current. These
large historical artifacts are local, not part of the Git commit; tracked
measurements and reproducible source/recipe boundaries remain in the repository.
The current full-source proof, its Pure/HOL runtime and active pointer stay at
their original paths for immediate proof reuse. Earlier absolute temporary
paths in historical receipts are archive restoration paths, not live providers.

Conditions 1 and 6, practical gate 5a, O-85, broader coverage and genesis remain
open. Theoretical cost gate 5b remains deferred until after genesis.
