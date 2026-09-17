# Making native development and validation fast

Updated 2026-09-17 from the complete parallel-reader, presentation and investigation
batch. Superseded measurements remain in their retained evidence files and Git.

## Current result

**All 51 recipes and both host suites passed in 481.87 s.** The workspace
has **1,635 theories**, with all contexts reused in the final cycle; 147 tool
tests and 35 kernel tests passed (two optional skips). The preceding substantive
integration proved nine changed contexts over 1,625 reused contexts and passed
all seven affected recipes in 325.01 s. The shared built-in export then added one
proved theory. The inventory retains **3,637 physical records**.

Twenty families now have native words: fourteen use words alone and six passed
old/new stages together. All original comparison boundaries remain unchanged.
The new fifty-first recipe covers all thirteen registered built-in investigations
with 56 complete cases. It restores execution coverage beyond the old recipe set;
it does not establish general native control or practical gate 5a.

**Decision replay's complete parallel-reader probe took 102.01 s**, versus the
earlier 260.76-second probe. Certificate replay's complete native word took
55.78 s. Every decompressed byte matched. Independent complete graph reads now
run in parallel; the earlier code prepared them sequentially within each context.
The schedules differ, so these are observed improvements, not controlled ratios.

**All thirteen investigation CLI modes now reuse one accepted export in roughly
1.6–2.3 s per request.** Their complete results match the shared 56-case execution.
A default-executable invocation passed in 2.88 s. The unchanged whole-workspace
validation observation from the previous batch remains 11.30 s; this batch does
not claim that figure as its new complete execution time.

| Current measured boundary | Result |
|---|---|
| Complete affected validation | 481.87 s; 51 recipes and both host suites. Six outer jobs, with existing nested groups and recorded worker settings. |
| Base and dependency checks | 3.59 s. |
| Recipe input comparison | 4.17 s. |
| Export | 7.13 s; actual provider sessions and per-client proof roots. |
| Recipe execution and host suites | 462.86 s. |
| Seven-recipe integration | 325.01 s; 1,634 theories, nine rebuilt and 1,625 reused; every original/new pair passed. |
| Shared built-in proof | One new export theory, 462 imported contexts reused; 21.61 s in the isolated exercise. |
| Built-in execution and CLI | 56 cases passed in 5.94 s; thirteen separate CLI modes matched their complete results in a 7.20-second concurrent batch. |
| Full source proof | The retained 1,620-theory frozen source proof still costs 542.886 s, rebuilding all project contexts from HOL. Later additions are outside that snapshot. |
| Prior unchanged validation | 11.30 s with all 50 then-current results and 1,624 proof contexts reused, both host suites executed. |

Different workloads, source boundaries and concurrent schedules must not be
turned into controlled whole-cycle speedup ratios. The built-in proof and
isolated checks overlapped independent validation. A pre-separation 51-recipe
cycle took 617.38 s with four outer jobs and explicit Poly paths; it did not test
default executable discovery. The final cycle above includes the corrected
shared utility boundary. Verified archiving of earlier generated recipe copies
also overlapped it. Full and cold cost, complete edit-to-commit attribution,
peak memory, remaining client coverage and actual native-driven work remain open.

The [current inventory](validation/reconstruction/current-verified.json),
[incremental receipt](validation/incremental-check.json) and
[complete cycle measurements](validation/reconstruction/native-current-cycle-measurements.json)
bind the latest accepted result. The [parallel-reader measurements](validation/reconstruction/parallel-replay-reader-measurements.json),
[six-family presentations](validation/reconstruction/cause-family-presentation-measurements.json),
[investigation reuse](validation/reconstruction/builtin-investigation-reuse-measurements.json)
and [utility dependency measurements](validation/reconstruction/execution-support-measurements.json)
retain the independent probes, failures, negative controls and actual scopes.

## Reusing accepted proofs across edits

`proof_contexts.py` records the actual provider session and qualified theory for
each complete unchanged import context. A changed ancestor invalidates its old
dependents even when their own text is unchanged. A new child supplies rebuilt
contexts; independent contexts continue to come from their original providers.
`export_proved_code.py --context` exports from those actual sessions, including
mixed parent/child requests. It does not infer a provider from a theory basename.

Accepted source directories are immutable because Isabelle includes absolute
paths in session currency. The original 1,589-theory base remains at
`/tmp/structural-accepted`. The completed cold proof and its seven-theory child
supplied the earlier 1,624 contexts; subsequent immutable children now supply
all 1,635 current contexts. Their original sources, rewritten import
headers, manifests, helper sources, session configuration, heaps and databases
are checked. Requalification may change imports but not theorem bodies.
New proofs preserve the original project ROOT before execution and verify that
it and the checked inputs remain unchanged through completion.

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

| Family | Complete word bytes | Latest complete-batch recipe seconds |
|---|---:|---:|
| required-history | 159,908 | 21.25 |
| digit-history | 418,306 | 137.49 |
| known-history | 449,531 | 216.62 |
| quoted-history | 483,348 | 152.58 |
| constructed-history | 551,708 | 225.43 |
| digit-replay | 20,519,284 | 394.94 |
| decision-replay | 1,296,760 | 114.70 |
| native-nodes | 341,007 | 2.57 |
| native-graphs | 1,000,741 | 22.90 |
| native-derivations | 648,713 | 5.08 |
| native-certificates | 890,378 | 4.97 |
| history-index | 316,651 | 89.04 |
| indexed-generation | 550,833 | 2.52 |
| digit-generation | 743,867 | 3.02 |
| native-certificate-replay | 722,239 | 135.93 |
| requirement-decisions | 494,768 | 13.94 |
| required-causes | 495,123 | 11.93 |
| certified-causes | 5,538,773 | 49.94 |
| concurrent-history | 555,495 | 199.50 |
| concurrent-replay | 20,519,284 | 294.35 |

The first fourteen use words alone. The final six include both original
comparisons and new native words in this batch; those paired times are not
presentation-only times. The shared inspected-value composer retains complete
subjects and all actual facet occurrences. Boolean-family reports preserve
coverage, optional rows, original and selected verdicts and each row inspection.
Concurrent clients retain their established exact stages and original source
views. Thirty original recipe families, plus the new built-in family, still
require word migration. Remaining shared renderers keep their existing callers.

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

1. Finish native presentation for the other thirty-one families, reusing existing
   notion contracts. Preserve complete old/new comparisons before retiring stages.
2. Reduce the measured dominant native computation and full-source proof costs.
   Remaining cold commands include child-source simplification (96 s), generation
   retention (41–56 s), source-entry installation (46 s) and steering (45 s).
   Reuse existing exact mechanisms and require a completed beneficial execution.
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
construction does not admit arbitrary modified reports. Retain reproducible
sources and contracts before removing obsolete bulk; preserve the accepted
contexts and full digit comparison word. Existing [verified temporary archives](validation/reconstruction/native-temporary-archives.json)
replace obsolete expanded copies. The latest
[verified recipe archive](validation/reconstruction/native-final-temporary-archive.json)
replaces 3.31 GB of generated files with 0.79 GB. The
[preceding batch archives](validation/reconstruction/parallel-previous-temporary-archives.json)
retain their complete earlier evidence. Accepted contexts and current exports
remain in place.

Conditions 1 and 6, practical gate 5a, O-85, broader coverage and genesis remain
open. Theoretical cost gate 5b remains deferred until after genesis.
