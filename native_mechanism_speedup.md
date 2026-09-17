# Making native development and validation fast

Updated 2026-09-17 from the complete proof-context reuse batch. Superseded
implementation claims and old timing tables have been removed. Historical
measurements remain in their evidence files and Git history.

## Current result

**All 50 recipes passed in 403.75 s, reusing all 1,624 theory contexts
without a proof rebuild.** The batch includes 143 tool tests and 35
kernel tests (2 optional skips). Fourteen report families now use native
words alone; the three remaining paired legacy stages have been retired after
accepted pairing and importer checks. The complete inventory contains 3,575
physical report records. Native word size and complete report content are
unchanged; fewer physical records do not mean less semantic coverage.

The final unchanged-workspace check passed in **11.30 s**, retaining all 50
unchanged recipe manifests, reusing all 1,624 proofs, and running **144 tool
tests plus 35 kernel tests (two optional skips)**. This is the current retained
inventory; the 403.75-second batch is the last actual execution of all recipes.

The new proof-context path removes the repeated 75–83-second proof of the whole
delta against the old base. A two-recipe check already demonstrated 9.77-second
feedback with no proof work. A real seven-theory extension of the cold proof
took 34.93 s including its selected recipe and host suites. Those partial checks
are separate observations, not complete-suite or edit-to-commit measurements.

The speedup objective remains unfinished. Full source proof still costs about
nine minutes, costly native recipes still take minutes, non-recipe coverage is
incomplete, and native-driven development and practical gate 5a remain open.

| Current measured boundary | Result |
|---|---|
| Unchanged complete validation | 11.30 s; all 50 results and 1,624 contexts reused, both host suites run. |
| Complete affected validation | 403.75 s; 50 recipes, all 1,624 contexts reused, no proof phase. Six configured outer jobs; recipes keep their actual nested groups and worker settings. |
| Base and dependency checks | 1.39 s in the complete batch. |
| Recipe input comparison | 4.28 s in the complete batch. Shared proof/export tools changed, so every recipe was affected. |
| Export | 3.57 s, using the actual provider session for each module. |
| Recipe execution and host suites | 392.64 s in the complete batch. |
| Two-recipe proof reuse | 9.77 s total: node export from the cold parent and indexed-generation export from its child; all 1,624 contexts reused. |
| Seven-theory extension | 34.93 s total, proof 20.95 s; 1,617 contexts reused. Selected indexed-generation recipe and host suites passed. |
| Full source proof | 1,620 frozen theories rebuilt from HOL, zero project parent contexts reused, 542.886 s; sixteen threads and parallel_proofs=0. It predates four presentation theories. |
| Same-report digit word encoding | Old 96.260 s, complete-object lookup 25.986 s; every one of the 20,519,284 bytes matched. Old encoder ran first. |

These are different workloads and concurrent schedules, not controlled whole-cycle
speedup ratios. The independent lineage exercise overlapped the complete batch. Its shared
worker pool could run seven recipes after the host-test task finished despite
six configured jobs. The final checker separates those pools so `--jobs` is
the actual outer recipe limit; the unchanged check launched no recipes.
The full source proof reused the installed Pure/HOL bootstrap and does not claim
an empty OS cache or a cold execution of all recipes. Git commit/push time,
complete edit-to-commit latency, CPU/GC attribution and peak memory have not all
been isolated.

The [current inventory](validation/reconstruction/current-verified.json) and
[incremental receipt](validation/incremental-check.json) bind the accepted batch.
[Proof-context measurements](validation/reconstruction/proof-context-reuse-measurements.json)
retain the complete and partial runs, native currency observation, dependency
failure/repair and reproduction program. Earlier [cause](validation/reconstruction/prepared-cause-measurements.json),
[object-word](validation/reconstruction/object-word-measurements.json),
[generation](validation/reconstruction/generation-presentation-measurements.json)
and [cold-source](validation/reconstruction/cold-source-proof-measurements.json)
measurements retain their original boundaries.

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
now supply all 1,624 current contexts. Their original sources, rewritten import
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

## Native computation and complete report words

The largest adopted runtime change shares **actual returned cause targets**
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
| required-history | 159,908 | 32.08 |
| digit-history | 418,306 | 188.28 |
| known-history | 449,531 | 194.98 |
| quoted-history | 483,348 | 195.28 |
| constructed-history | 551,708 | 207.90 |
| digit-replay | 20,519,284 | 390.42 |
| decision-replay | 1,296,760 | 369.54 |
| native-nodes | 341,007 | 2.62 |
| native-graphs | 1,000,741 | 20.99 |
| native-derivations | 648,713 | 4.62 |
| native-certificates | 890,378 | 4.37 |
| history-index | 316,651 | 86.36 |
| indexed-generation | 550,833 | 2.62 |
| digit-generation | 743,867 | 3.52 |

All fourteen now use native words only. The last three removals were
history-index, indexed-generation and digit-generation. Their old/new pairing
is retained in the generation measurement file. Shared renderers still needed
by other clients remain. Thirty-six recipe families still require migration.

**Decision replay experiments did not demonstrate a useful gain.** Exact
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

1. Finish native presentation for the other thirty-six families, reusing existing
   notion contracts. Preserve complete old/new comparisons before retiring stages.
2. Reduce the measured dominant native computation and full-source proof costs.
   Remaining cold commands include child-source simplification (96 s), generation
   retention (41–56 s), source-entry installation (46 s) and steering (45 s).
   Reuse existing exact mechanisms and require a completed beneficial execution.
3. Complete the non-recipe coverage audit and its executions. The
   [syntactic inventory](validation/reconstruction/validation-entrypoint-inventory.json)
   finds 74 check/run/roundtrip CLI tools, 49 directly called execution scripts,
   25 tools without a direct recipe call, and 13 built-in investigations. Some
   tools remain shared helpers. Direct calls, imports and proofs do not establish
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
replace obsolete expanded copies. The new complete batch’s
[verified recipe archive](validation/reconstruction/proof-context-temporary-archive.json)
replaces 3.68 GB of generated files with 0.88 GB; accepted contexts and current
exports remain in place.

Conditions 1 and 6, practical gate 5a, O-85, broader coverage and genesis remain
open. Theoretical cost gate 5b remains deferred until after genesis.
