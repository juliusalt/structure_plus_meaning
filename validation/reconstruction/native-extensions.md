# Reconstruct executed native package extensions

The finite constructor receives complete ordinary source and target programs
and the existing source coordinate map. It computes fresh positions for every
new definition, preserves every old position, and relocates all definition
owners and callee occurrences together. Formation and complete old-field
agreement are checked before compilation.

Each selected definition compiler consumes its actual interface and complete
keyed clause family. A strict traversal fails when any selected compilation
fails. All code artifacts are installed before their literal and callee
references, so recursive peers can refer to one another. A final citation
family selects every target definition.

`Factor_Finite_Mapped_Extensions.finite_mapped_native_extension.correct`
connects each actual successful result to a native program with the complete
target meaning. Every original artifact and outgoing binding remains unchanged,
and the original native package remains readable at its existing address.
The source coordinate map must be injective on the complete source definition
set. Its whole-program correspondence concerns that actual native package.
The concrete source models establish it from their complete native
readings. General native admission of an arbitrary source correspondence
remains open.

The recipe executes eighteen complete reports:

| Family | Reports | Scope |
|---|---:|---|
| Checked requirements | 4 | Both actual source clauses combined with recursive collection and paired-collection plans; complete constructed environments and recovered programs. |
| Constructor controls | 14 | No added definitions, empty clauses, self and peer recursion, a seeded peer cycle, whole and anchored literals, all five material operands, altered or missing old fields, absent callees, conflicting clause values and malformed unused clauses. |

Every successful report contains the complete returned artifact and binding
tables, all recovered interfaces and clauses, and its actual coordinates.
Formation and both original-source comparisons are computed from the returned
environment. Controls also retain the complete candidate and its computed
formation and old-field agreement. Material operands remain part of each
rule application's semantic obligations.

The [source manifest](native-extensions-sources.json) contains 383 theory
sources, 18 Python modules and the complete-report comparison: 402 files.
With the declared Isabelle, Python and Poly/ML toolchain, use fresh directories
and a fresh session:

```sh
python3 -B tools/materialize_source_boundary.py \
  --manifest validation/reconstruction/native-extensions-sources.json \
  --output /tmp/native-extension-sources
python3 -B /tmp/native-extension-sources/tools/reconstruct_native_extensions.py \
  --poly /opt/isabelle/contrib/polyml-5.9.2-2/x86_64-linux/poly \
  --session Native_Extension_Independent_Run \
  --timeout 900 \
  --output /tmp/native-extension-results
```

The common runner rebuilds the proof from HOL, obtains complete diagnostics,
exports the accepted code and executes every case. The result must match
[all complete reports](native-extensions-reports.json), including every field,
index, order and repeated occurrence. The
[verified reconstruction](native-extensions-verified.json) and
[materialization receipt](native-extensions-materialization.json) record this
source-only boundary. Generated proofs, modules and result logs are outputs.

The source collector derives the original theory closure and local Python
imports from the same literal recipe used by the runner. Fixtures are declared
in that recipe. Refresh a changed boundary with:

```sh
python3 -B tools/reconstruction_sources.py \
  --recipe tools/reconstruct_native_extensions.py \
  --poly /opt/isabelle/contrib/polyml-5.9.2-2/x86_64-linux/poly \
  --output validation/reconstruction/native-extensions-sources.json
```

Dependency collection and report comparison establish reproduction. The
Isabelle-established construction, decoding and native-reading contracts
establish the results' meaning. The complete source, correspondence, request
and installed-program development record still needs native admission.
Problem selection, independent criticism, workflow coverage, historical
permission, the complete cost account and genesis remain open.
