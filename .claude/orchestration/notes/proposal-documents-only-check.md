# Proposal: the finalizer's own check for a documents-only commit (not built; the owner, 2026-09-22 ~12:30: "write it down, we come back to it")

## What was seen

- design-171 (2026-09-22 11:32–12:07) changed DECISIONS.md alone and spent 2 of its 46 requests (0.16M) finding an
  acceptance check to hand over: it searched earlier tasks' finalize commands, then assembled
  `check.source_checks()` + `investigate.source_graph(…)` in `python3 -c`, and got its own assertion wrong once
  (`r['refusals']==0` on a list).
- The finalizer requires `--check CMD`, and every designer and investigator invents one. Design and investigation
  tasks were about 10 of the tasks of the sixteen hours before (95, 135, 136, 138, 66, 171; 82, 86, 134, 143).
- A task in its own tree whose landing finds main moved runs `LANDING_CHECK` (`tools/incremental_check.py check`),
  about 5 minutes on a heavy machine slot, and waits for that slot while main is let go
  (finalize.MACHINE, 2026-09-22). For a documents-only commit that run checks nothing the commit can change: the
  incremental check reads ROOT, the theories, the tools and the recipes, not DECISIONS.md.

## The proposal

1. **Documents-only, decided by the finalizer from `--files`:** every file is a Markdown document (`*.md`) outside
   `theories/`, `tools/` and `validation/`. ROOT and any code are never documents. The session declares nothing.
2. **`--check` optional for such a commit.** Left out, the finalizer runs its documents check; given, the session's
   check runs as now. The documents check, about a second, no Isabelle:
   - the repository's structural source checks (`tools/check.py source_checks()`): every theory ROOT declares
     exists, none is undeclared, no proof escapes;
   - every row of THEORY_MAP.md names a theory that exists (and none is doubled — the union merge's failure);
   - no conflict marker (`<<<<<<< `, `>>>>>>> `) stands in a committed document.
3. **No heavy slot:** it waits for no measurement, landing or check (`wait_for_isabelle` is not entered).
4. **At its landing, main moved:** the merge as now (rows agreed, receipts, marked drafts on a conflict), then the
   same documents check instead of `LANDING_CHECK`.
5. **Protocols** (designer, investigator, `_finishing.md`): "a decision that changes documents only hands over without
   `--check`: the finalizer checks the documents and the sources."

## To decide when we come back

- Whether the documents check belongs in `tools/check.py` (the project's, a task's to add, e.g. `--documents`) or in
  finalize.py (the harness's, calling `source_checks()`); the second needs no task, the first is reusable by sessions.
- Whether a design that also changes `native_control_plan.md` or `REASONING_REUSE.md` counts (they are documents by
  the rule above), and whether the planner's HANDOFF.md, committed with a task's change, keeps a commit
  documents-only (it is a document).
- What a failure of the documents check does: a quick fix as a failed check does now (likely), with the check's own
  list of what failed.

## Tests and mutation cases it will need

- A documents-only hand-over without `--check` is prepared; with code in `--files` it is refused as now.
- The documents check fails on a THEORY_MAP.md row naming a theory that does not exist, and on a conflict marker.
- Its landing with main moved runs the documents check and not `LANDING_CHECK`, and takes no heavy slot.
