# Overnight source and reconstruction boundary

This checkpoint retains inputs, compact verification records and useful unfinished
source. Generated proofs, exports, native words, execution archives and full
diagnostic dumps are not current repository inputs. The previous bulk checkpoint
remains recoverable from commit `d85a02e`; no reconstruction reads it.

[HANDOFF.md](../../HANDOFF.md) states the original semantic scope, results, open
obligations and commands. The 53 accepted theory texts are unchanged. The complete
repository still has the Development_Seed contract-argument defect.

| Retained file | Why it is needed |
| --- | --- |
| `integration.json` | Accepted theory roots and original source/provider identities. |
| `sources.json` | Complete theory/Python input closure and fixtures in the existing source-boundary format. |
| `requests/` | Original executable native requests and diagnostic presenter; the historical driver mains are not run. |
| `requests.json` | Original requirements and timeouts, driver identities, expected complete-report and native-word boundaries. |
| `verified.json` | Compact records of proof/export/replay validation, warning counts and unresolved historical process identities. |
| `unfinished/` | Nine distinct diagnostic/candidate theories, explicitly outside the accepted ROOT scope. |
| `retirement.json` | What was removed, where its source/evidence is retained, and how generated outputs are rebuilt. |

The expected assessment boundary hashes the same complete stable assessment that
the prior checkpoint compared directly. It omits only the same timings, display
scope and physical-completion fields as that comparison. Every result and control
is covered; native word sizes/digests are retained separately. These identify
reconstructed bytes; the original proved contracts establish their meaning.
No supplied satisfaction table or new native admission rule is introduced.

Use the existing materializer to check the full input closure independently:

```sh
python3 -B tools/materialize_source_boundary.py --project . --manifest validation/overnight-20260918/sources.json --output .build/overnight-source
```

Then use the prove/export/replay commands in HANDOFF.md. Neither the archive nor
old temporary providers are needed. Sources execution and projection preparation
remain unresolved operations; a timeout is not a negative semantic result.

The cleanup removes the nine ignored original validation trees after verifying
every file against the prior checkpoint. Their blanket ignore rules are removed.
Original `/tmp` providers remain untouched because historical PID-namespace exit
evidence is incomplete; these optional caches are not reconstruction inputs.
Historical bulk stays in Git history, consistent with earlier retirements.
