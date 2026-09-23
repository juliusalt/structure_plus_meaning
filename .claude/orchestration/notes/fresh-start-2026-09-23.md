The harness changed while the run was stopped (2026-09-22 22:37 until this start). What bears on planning:

- **What the worker bases hold is chosen by use** (`.claude/orchestration/notes/plan-bases-upgrade.md`). The founding
  theories that no implementer, fixer or middle role used over a week are no longer in the high and xhigh bases; each
  still has its line in the theory map's index (high) and in a founding index (xhigh), and a session that needs one
  reads it. The working frontier is chosen at every layer refresh from what the last 60 sessions of the base's roles
  used, ranked by use per token, within the owner's target of 530K (high holds 71 theories, xhigh 55).
- **xhigh runs on a delta, as high does**: its roles fork the delta and are told only what changed after it. A layer
  is refreshed when what its delta has cost the forks that carried it reaches what a refresh costs.
- **What a session is given and told** (`.claude/orchestration/notes/plan-orchestrator-concepts.md`). A build's,
  fix's, design's, investigation's and brief task's session is given, in its first message, the statements of the
  facts and definitions its brief's Inputs and Decided name, as its tree holds them: name each fact a task consumes
  exactly (`Theory.name`). A change that writes a theory is told what the source checks and the import graph say of it
  (your standing last step, now the harness's at every change), what it adds that the library already has — a specific
  name, a statement word for word, a definition's body — and what its row still offers that it took out; its reviewer
  reads the same over the whole change. THEORY_MAP.md rows and ROOT lines are written by the theory's name, the
  imports column read from the theory. The commit states the harness's own record of the session's probes beside its
  check, so a Validation paragraph holds what no record does: briefs need not ask for the standing step, a probe's
  flags or runs restated. And a task need not bring main in before its hand-over for the check's sake: batches and
  trains check the work merged onto main as it stands, so a lagging tree rebuilds nothing more (HANDOFF's working rule
  came from the landing check in the task's own tree, #124, before batches and trains); it brings main in when told
  its lines meet main's. In a task's own tree the hand-over is `v2.py finalize ID` alone — its files, the repository's
  check, its commit.md — so a brief's Acceptance may say "the repository's check" without its command, and names a
  command only for another check.
- **A task's passing state is shown, not kept.** The graph gives each open task's stage with a parked task's reason
  and since when and a rejected task's rounds, and your status the landings of the last three hours with their
  commits: HANDOFF.md names a task and what it is for, never where it stands (the planners of 09-21/22 spent 405 of
  their 908 edits of it on such words, a mirror stale between edits).
- **138 of THEORY_MAP.md's 1,812 rows name imports their theory no longer has** (the Investigation theories now
  importing their `_Base`, and others); `=== row THEORY` alone reads a row's imports again from its theory, so one
  small task could set them all right — a row's imports column is what a reader of the map takes a theory to stand on.
- **Four things stand twice in HEAD** (found by replaying the restatement hints over the 68 landed changes of
  09-21/22; each named to its writer from now on): `Development_Request_Citations.predecessor_check_rule` defines what
  `Native_Collection_Programs.native_member_later` defines, and so does `native_some_rest` beside it;
  `Native_Collection_Programs.native_context_call_rule` what `Development_Verdict_Mentions.store_found_rule` does;
  `Development_Verdict_Statements.keys_term` what `Development_Rows.development_row_family` does; and
  `Factor_Indexed_Readings.reading_heads_indexed` (with its values and counted siblings) states what
  `Development_Answer_0ccf746fe2cf.indexed_heads_exact` states. Whether each pair is one notion, and so one
  consolidation of the kind the fixes from #100 on made, is yours to judge.
- **Q9's file can go now.** `tools/__pycache__/build.cpython-314.pyc` is still tracked (and rewritten in the working
  tree by every run of the tools); the finalizer stages the removal of a tracked path that .gitignore matches since
  09-21 (finalize.stage, after task 48's attempts were refused), so a task handing over its deletion commits it.
- **A reviewer corrects words itself, and a follow-up's brief can be begun for you.** A review that finds the work sound
  and only its commit message, its result or a theory's THEORY_MAP.md row misstating it corrects them and accepts,
  naming each under `## Corrected` (your commit event says "Corrected by its review: …"); about 12 of the 31
  rejections of 09-21/22 were such words, each a fix round. A reviewer writes nothing else, so a finding about a
  theory, code or a decision entry is still a rejection. `.claude/orchestration/v2.py follow-up TASK:ITEM,ITEM…`
  (several reviews' in one, `272:1 247:1,2,3`) drafts a task's brief from reviews' follow-ups under your drafts: the
  follow-ups verbatim, the review and the names they give among its Inputs, and the parts that are yours marked
  `<<PLANNER: …>>` (why now, the files, what shows it done, Decided, Plan, Size), which a placement refuses while one
  is left; `v2.py edit` creates and rewrites now take `"continues": "N"`.
- **An accepted task left in review is committed by the watchdog.** Tasks 128 and 147 were accepted and checked but
  stood in review for eight hours with nothing to commit them; they are committed, and land in the next train, once
  your order releases the graph.

In flight — each session's cache is gone, so each task continues in a new session, in its own tree:

- task 44 (implement-44, interrupted as its measurement ended): 5 files changed in `.build/trees/44` — DECISIONS.md,
  ROOT, THEORY_MAP.md, `Development_Verdict_Mentions.thy`, `Native_Path_Stores.thy` — and one new,
  `Development_Verdict_Witnesses.thy`;
- task 278 (fix-278, interrupted as a measurement began): 2 files in `.build/trees/278`;
- tasks 192 and 279 (parked; their probes' outputs came back at 22:36:09 and were not read): 192 has one new theory in
  its tree (`Development_Incremental_Verdict.thy`), 279 two changed files (THEORY_MAP.md,
  `Isabelle_Entity_Export.thy`);
- task 276 (its check passed at 22:36:43; its review has not started): 8 files in `.build/trees/276`.

Trees whose tasks are not running: `.build/trees/143` (task done; 1 modified file) and `.build/trees/176` (task
deleted; one commit and a modified THEORY_MAP.md that never landed) — carry them or say why they are superseded.
`check-a`, `check-b` and `train-a` are the harness's own integration trees.
