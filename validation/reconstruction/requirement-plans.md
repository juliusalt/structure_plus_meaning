# Reconstruct requirement construction and artifact admission

The boundary contains 487 theory sources, 16 Python modules and one complete
report comparison file. The source fixture is defined in the execution
theories: it contains actual goals, counters, table operands and complete
candidate artifacts. No saved proof, generated code or result log is an input.

With Isabelle 2025-2 on `PATH` and Python 3.14, materialize the exact boundary
and use its reconstruction entry point:

```sh
python3 -B tools/materialize_source_boundary.py \
  --manifest validation/reconstruction/requirement-plans-sources.json \
  --output /tmp/requirement-plan-sources
python3 -B /tmp/requirement-plan-sources/tools/reconstruct_requirement_plans.py \
  --poly /opt/isabelle/contrib/polyml-5.9.2-2/x86_64-linux/poly \
  --session Requirement_Plan_Source_Reconstruction \
  --output /tmp/requirement-plan-results
```

Use fresh output directories and a fresh session name. The source manifest
records the required Poly/ML executable hash. The recipe rebuilds the complete
dependency proof from HOL, recovers all proof diagnostics, exports the accepted
module and executes all controls. It fails on a failed or missing stage,
changed recipe bytes or any difference in the complete native reports.

[requirement-plans-sources.json](requirement-plans-sources.json) identifies all
504 inputs. [requirement-plans-reports.json](requirement-plans-reports.json)
retains the exact comparison boundary. The
[verified reconstruction](requirement-plans-verified.json) and
[materialization receipt](requirement-plans-materialization.json) record the
source-only run. The optional `--proof` argument rechecks a supplied accepted
export and explicitly records that proof and code were not reconstructed.

| Report family | Complete reports | Actual subjects and results |
|---|---:|---|
| Requirement plans | 7 | Original goal sequences, initial counters, result entries, final counters and all instructions. |
| Source domain | 1 | The complete definition domain of the existing data-recognition program. |
| Checked requests | 14 | Computed candidates, native source-support and allocation checks, complete-plan admission and optional checked output. |
| Portable tables | 36 | Nine complete table pairs at four counters, seven computed observations, original table identity and the generated guard's result. |
| Candidate artifacts | 17 | Original requests, all carrier and incidence entries, every counted and functional attachment, formation, expected plans and native artifact admission. |

The report comparison preserves every JSON field, index, record order and
duplicate occurrence. An unchanged hash identifies a complete reproduction;
the Isabelle-established contracts determine its meaning.

The ordinary sequence constructor is native entry 361. Entries 362–367 check
the complete actual source domain, every requested leaf and allocation before
admitting the constructed sequence. Installation preserves the source and
adds a predicate equivalent to all original goals on the same formed subject.

The installed interface at 368 fixes the original request before future
candidates. Entry 369 projects the actual whole-artifact literal, recovers
its complete data body and applies that fixed request check. The executable
finite reader has the same all-input contract. Valid empty, pair, collection
and multiple-requirement constructions pass. Changed requests, entries,
counters or instructions fail, as do a malformed payload, an extra counted
attachment and an extra isolated carrier atom. Unsupported leaves and occupied
counters remain failures even when the candidate artifact is formed.

The generation proofs establish an actual closed native cause program before
future payloads, and recorded generations retain that same program scope with
separate replay evidence. A further construction extends an existing generation
environment through its predecessor uses. The finite runtime here executes
plan construction and artifact admission; generation and replay construction
are established by the separate constructive theorems.

This is a local contribution to the six conditions in `problems.txt`.
Complete problem and approach selection, independent criticism, workflow
coverage, historical acceptance, and the overall cost account remain open.
The plan record retains the source domain. The full development account must
also bind the exact source program and the actual installed native program;
programs with equal definition domains may have different predicate meanings.
In particular, predecessor-reference extension alone supplies no bound on
allocation, lookup, replay or the complete development process. Isabelle's
normative bootstrap role remains in force through genesis.
