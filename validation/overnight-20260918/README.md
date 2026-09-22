# Overnight source and reconstruction boundary

This checkpoint retains inputs, compact verification records and useful unfinished
source. Generated proofs, exports, native words, execution archives and full
diagnostic dumps are not current repository inputs. The previous bulk checkpoint
remains recoverable from commit `d85a02e`; no reconstruction reads it.

This boundary is historical: it reproduces the sources at commit `aa946a22`, the
last commit that recorded its reproduction, and no check runs it. Its closure
(`sources.json`) changed in every later commit touching `ROOT` or its theories:
52 first-parent commits up to `7379cfc7`, the first being `d0b70ea2`, and 25 of
the 53 roots of `integration.json` changed since. Everything else this README
says describes the boundary as of `aa946a22`. The commits whose changes were
traced are these three:

- `d0b70ea2` (verify, repair, admit and issue development answers natively)
  changes `ROOT` and theories of its closure, among them `Development_Problems`,
  `Isabelle_Acceptance`, `Isabelle_Entity_Export`, `Native_Control_Seed_Subject`,
  `Native_Control_Admitted_Selection`, `Native_Control_Context_Execution`,
  `Native_Control_Syntax_Candidate` and `Native_Execution_Refinements`, and the
  tools `build.py`, `check_presented_report.py` and `proved_code.py`; its message
  names no report family of this boundary.
- `5c26b791` (hold each type of an exported state once) changes `ROOT`,
  `Isabelle_Terms`, `Isabelle_Entities`, `Isabelle_Entity_Export`,
  `Isabelle_Renaming`, `Native_Control_Refinement_Composition` and
  `Native_Control_Syntax_Statements`; its message names no report family of this
  boundary.
- `7379cfc7` (task 90, the switch of the overnight questions to keyed candidates)
  changes the certificate reports (through `cause_certificate_choice`), the
  material reports (through `cause_child_application_choice`) and the source
  reports (through `admitted_guard_requests`, the judgment-artifact and
  guard-representation choices and the judgment bridge).

To reproduce the boundary, run `tools/reconstruct_overnight.py` in a worktree of
`aa946a22`; in a later tree its expected words are not those of the current
sources.

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
