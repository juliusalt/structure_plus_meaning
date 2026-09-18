# Handoff — overnight work consolidated; native-control goal open

Checkpoint: 2026-09-18. Read [AGENTS.md](AGENTS.md) and
[DEVELOPMENT_WORKFLOW.md](DEVELOPMENT_WORKFLOW.md) first. This supersedes the
stage-1 seed handoff and segment-9 recovery handoff. The owner's current request
was consolidation, preservation, repository-only reconstruction and a commit;
the native-control plan and genesis are not complete.

## Committed work and validation boundary

53 theories are integrated into `theories/` and `ROOT`, byte-identical to their
accepted overnight providers. The [inventory](validation/overnight-20260918/integration.json)
binds each theory to its original source and provider. A fresh Isabelle/HOL build
checked their entire 1,080-theory closure with zero project theories reused in
311.491 seconds including startup, without session errors. This is a **partial
scope**, not a successful build of the whole `ROOT` session.

Fresh exports match the overnight modules byte for byte. Both the certificate
and material replays match their complete original assessments and native words.
The cleanup retains complete report identities and a source-only reconstruction
boundary. Generated output is rebuilt when needed.

[validation/overnight-20260918](validation/overnight-20260918/README.md) retains
the source closure, native requests, expected complete-report identities, compact
verification and the retirement record. Unique diagnostics/candidates are explicit
source files under `unfinished/`, outside ROOT. Full historical logs, generated
outputs and superseded snapshots remain recoverable from commit `d85a02e`; none is
a current reconstruction input. No old `/tmp` provider or active pointer is needed.

Segment 10 proposed application-result selection and source-reader staging but
left no implemented theory candidate for them.
The ordinary whole-session check still encounters the earlier missing argument
to `Development_Refinement` in `Development_Seed`. Choosing that argument remains
a semantic development problem; its expected recipe reports are placeholders.

## Latest native results

The actual subject is the checked rooted context and complete proposition for
`Original_Union`, with the universally quantified `finite_syntax_join` refinement.
`Native_Control_Syntax_Statements` checks theorem propositions and absence of
hypotheses. This covers neither arbitrary theorems nor every paused refinement.

The admitted root application retains the original quoted guard, four bindings
and all three sockets. Native observation selects `Observed_Parts` under both
original facets. An application is not a root proof.

The certificate review retains all original full/leaf demands and both
`Requested_Certificates` and `Checked_Certificates`. Full children, projection
and quotation have no original two-facet choice. The natural body leaf has a
singleton complete proof-set result, preserved under reversal and duplication.
All absent reports refuse. One quotation control with only
`Requested_Certificates` accepts the supplied original-body report; exact question
equality remains unknown. Do not claim every wrong-report control refused.

The material review, completed after the older handoff, finished quotation and
both body clauses. Projection timed out at 90 seconds and is unresolved. All
15 completed method choices return `None`; multiple satisfactory methods do not
select a unique method. Complete application-value equality is still unknown.
All 15 absent/wrong-body report controls refuse. Timeout supplies no negative
semantic observation.

Guard installation proves source existence and definition-coordinate transport
under its installation premise. Actual source execution timed out: no complete
returned source record was accepted. Definition-site injection does not transport
clause, variable or socket proof coordinates. Certificate/policy continuation
retains actual original proof checking, literal replay and aligned policy/history
premises. No installed guard certificate, replay or governing cause exists.

## Rebuild without overnight temporary files

Use Python 3.14 and Isabelle2025-2 (`isabelle` on PATH; the existing runtime helper
expects Poly/ML under `/opt/isabelle`). This is the normative bootstrap toolchain.
Heaps are generated caches. Each output directory must be fresh. Current proof
and replay reconstruction reads only current repository inputs and the toolchain.

```sh
python3 -B tools/materialize_source_boundary.py --project . --manifest validation/overnight-20260918/sources.json --output .build/next-native-source
python3 -B tools/reconstruct_overnight.py prove --output .build/next-native-proof
python3 -B tools/reconstruct_overnight.py export --context .build/next-native-proof --output .build/next-native-exports
python3 -B tools/reconstruct_overnight.py replay certificates --exports .build/next-native-exports --output .build/next-certificates
python3 -B tools/reconstruct_overnight.py replay materials --exports .build/next-native-exports --output .build/next-materials
```

Proof builds directly from HOL without the active-context pointer. Export
verifies/adopts only the new context. Replay loads unchanged historical
request/assessment function ASTs with fresh paths and compares complete
assessment boundaries and native word identities. Material timeout outcomes can change;
review a difference rather than force it to match. Concurrent JVM jobs must
share a process namespace: separate sandbox namespaces can collide in shared
`hsperfdata`. Native per-subject material preparation remains parallel.

The fresh proof can supply `tools/prove_context.py --parent-project` for covered
theories; do not activate it as a full repository context. Useful unaccepted
source is directly inspectable in
[unfinished/](validation/overnight-20260918/unfinished/README.md). It is not part
of the accepted theory scope. No archive extractor or historical heap is needed.

## Remaining obligations and next content batch

1. Submit the application-result-selection gap and source/material bottlenecks
   through the native/bootstrap process. Instantiate faceted/singleton contracts
   with complete values and both original facets; establish their equality and
   observation equations. Expose source-reader/material substages without changing
   the operations. No optimization is selected by this storage consolidation.
2. Construct/check projection and quotation certificates and the full child
   family. Establish natural-to-installed clause/variable/socket proof transport
   or an independently checked native-source construction. Then construct the
   root proof, literal replay and aligned policy cause/history.
3. Preserve every `finite_program_evaluation_ready` premise: formed source,
   coverage of **every** clause at demanded definitions and demand closure.
   The guard lacks head variables `{1,2,3}`; projection needs material variables.
   Source existence or one leaf cannot discharge these premises. Do not increase
   timeouts or weaken checks to bypass the missing account.
4. Establish owner-authorized governing requirements, fixed policy/source/entry,
   authority/current basis, derived support and least contexts, dependency/absence/
   invalidation, recursively admitted selection/scheduling/requests, inert
   executors, predecessor-admitted amendments and first-use factoring.
5. Repair the seed's actual contract choice through its native account, run the
   complete repository check and reconstruct the placeholder recipe. Conditions
   1–4, practical 5a and 6 remain open; theoretical 5b is deferred. O-73 stays Open,
   O-85 Partial, and genesis absent. This checkpoint now retains reconstruction
   boundaries; the broader native retention/workflow account is still open.

The old segment-9 retention job and several interrupted/timed-out descendants
lack positive exit evidence in their original PID namespaces. Their records are
preserved; current numeric PIDs are not identities. Current reconstruction does not
depend on them. The owner-requested cleanup removed verified duplicate validation
trees without signalling processes or claiming exit evidence. Original temporary
provider caches remain untouched; their historical paths are not build inputs.
