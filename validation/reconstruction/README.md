# Reconstruct the native child-claim validation

The retained boundary contains repository theories and Python sources, the
original finite source fixture, the toolchain requirements, and the expected
complete native report comparison. Generated proof snapshots, code exports,
diagnostic databases, runtime inputs and result logs are produced by the recipe.

From the repository root, with Isabelle 2025-2 on `PATH` and its matching
Poly/ML binary, use a fresh output directory:

```sh
python3 -B tools/reconstruct_native_child.py \
  --poly /opt/isabelle/contrib/polyml-5.9.2-2/x86_64-linux/poly \
  --output /tmp/native-child-reconstruction
```

The recipe checks the complete dependency proof from HOL, obtains full proof
diagnostics, exports accepted code, constructs baseline source operands,
checks primitive projections and compiled clauses, checks child operands,
and executes the reasoning family. It fails if a stage fails, complete reports
change, or its checked inputs change. The optional `--proof` mode rechecks an
existing accepted export and records `sources_rebuilt: false`.

[native-child-sources.json](native-child-sources.json) lists the exact 554 source
and fixture files sufficient for the completed cold run, including 524 theory
sources and 28 Python modules. To materialize that boundary independently:

```sh
python3 -B tools/materialize_source_boundary.py \
  --manifest validation/reconstruction/native-child-sources.json \
  --output /tmp/native-child-sources
python3 -B /tmp/native-child-sources/tools/reconstruct_native_child.py \
  --poly /opt/isabelle/contrib/polyml-5.9.2-2/x86_64-linux/poly \
  --session Native_Child_Source_Reconstruction \
  --output /tmp/native-child-source-results
```

The materializer rejects changed bytes and paths outside the source repository.
It copies only declared inputs. Update the manifest and repeat verification
when those inputs change. The usual repository build is independent:
`python3 -B tools/check.py --timeout 1800` checks every registered theory.

[native-child-verified.json](native-child-verified.json) records the successful
cold reconstruction. The [materialization receipt](native-child-materialization.json)
identifies its source manifest. [native-child-reports.json](native-child-reports.json)
contains the complete comparison boundary:

| Stage | Complete native reports | Scope |
|---|---:|---|
| Baseline | 8 | Constructed source and application values, original source recovery and key fibres. |
| Catalog | 31 | Three complete compiled libraries, 27 projection cases and the original eight source call occurrences. |
| Inputs | 18 | Complete constructed child operands, nine table controls, source values and fibres. |
| Reasoning | 128 | Eighteen reasoning cases, compiled clauses, initial-input checks and 86 guided states. |

Comparison retains every complete JSON field, all leading indices, record
order and duplicate occurrences. It rejects repeated JSON object fields. Native
report values in this family contain no clocks; no result fields are omitted.
The compact checks identify an expected reproduction. The actual operations
and proved semantic contracts determine what those results mean.

The universal local correspondence is
`Factor_Inference_Claim_Correspondence.inference_claim_on_symbolic_sources`.
It keeps actual source environments, package, graph, inference, target,
complete claim domain, replacement, report, discharges and four support lists.
Whole-table formation and unique keys remain explicit. The concrete example
uses one inference premise and a separate assertion child.

Complete, reordered and extra-formed-row local checks settle both 350 and 359.
The extra row does not establish the exact whole-graph claim domain. Missing
or incorrect children, duplicate keys, a wrong parent and a malformed unused
row leave 359 unresolved. The malformed input still permits the valid source
subgoal 350 to settle. Withheld source or child operations and insufficient
construction depth retain residual conditions. Neither goal is initial evidence.

The assertion child remains an assumption. These results establish neither
whole symbolic-graph admission nor native mathematical-proof checking. The six
development-protocol conditions in `problems.txt` remain the next milestone.
Older generated validation is recoverable from the pinned GitHub commit in
[the historical recovery record](../history.json), under the owner's explicit
authorization to remove those current-tree copies.
