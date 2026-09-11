# Construction reuse investigation

The problem is whether a constructed native call can supply a premise for a
later construction, while retaining the original evidence requirements.

The [before stage](before/adequacy.json) retains the nine-case investigation
that exposed the limitation. Its original generator constructs one list step
but leaves a two-step goal unresolved. The independent native converter
establishes that goal. Supplying the intermediate call only as a possible
premise allows the existing inference closure to finish. Withholding evidence
leaves it conditional.

The generated module, proof receipt, complete cases, execution program,
checker, case generator, results, and replay are retained. Every theory digest
in the original proof receipt matches source commit 6b7e27b. The original
receipts are preserved; their paths refer to the original runs.

Run replay.py with --stage before, --project pointing to a matching checkout,
--poly pointing to Poly/ML, and --output naming a new directory. The checkout
must contain the exact theory bytes in the proof receipt. Runtime and source
digests are checked again for each replay.

The [after stage](after/adequacy.json) checks 64 complete reports, 84
intermediate frontiers, nine computed native seeds, and the native list
comparison. Bounded construction rounds now generate the intermediate calls
themselves. Known facts remain unchanged; insufficient depth, missing
evidence, and false requested outputs remain unresolved. Original malformed
inputs reject the report. Thirty-eight earlier generic controls also check
the equivalent frontier interface at zero extra rounds.

The operative native wrapper uses its own proved list-step library. A
separate frontier probe receives the explicit finite specification, and every
schema and premise in the operative wrapper's complete report is checked
against it. The original failed trace-harness run is retained separately.
It supplied no accepted semantic result.

The complete 787-theory main build and check receipts are included. The
source-runs directory retains ten investigations and their independent
reconstruction. Its evidence map resolves shared bytes through the earlier
archive and retains all newly changed source bytes locally. The two requested
roots and all nineteen new or modified theory roots have no remaining source
conditions after the accepted main build.

The investigation concerns a specific composition requirement. It does not
establish complete construction search, native mathematical-proof admission,
or coverage of every development decision required by the workflow.
