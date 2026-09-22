The harness changed while the run was stopped (2026-09-22 22:37 until this start). What bears on planning:

- **What the worker bases hold is chosen by use** (`.claude/orchestration/notes/plan-bases-upgrade.md`). The founding
  theories that no implementer, fixer or middle role used over a week are no longer in the high and xhigh bases; each
  still has its line in the theory map's index (high) and in a founding index (xhigh), and a session that needs one
  reads it. The working frontier is chosen at every layer refresh from what the last 60 sessions of the base's roles
  used, ranked by use per token, within the owner's target of 530K (high holds 71 theories, xhigh 55).
- **xhigh runs on a delta, as high does**: its roles fork the delta and are told only what changed after it. A layer
  is refreshed when what its delta has cost the forks that carried it reaches what a refresh costs.
- **An accepted task left in review is committed by the watchdog.** Tasks 128 and 147 were accepted and checked but
  stood in review for eight hours with nothing to commit them; they are committed, and land in the next train, once
  your order releases the graph.

In flight — each session's cache is gone, so each task continues in a new session, in its own tree:

- task 44 (implement-44, interrupted as its measurement ended): 5 files uncommitted in `.build/trees/44` —
  DECISIONS.md, ROOT, THEORY_MAP.md, `Development_Verdict_Mentions.thy`, `Native_Path_Stores.thy`;
- task 278 (fix-278, interrupted as a measurement began): 2 files in `.build/trees/278`;
- tasks 192 and 279 (parked; their probes' outputs came back at 22:36:09 and were not read): 279 has 2 files in its
  tree;
- task 276 (its check passed at 22:36:43; its review has not started): 8 files in `.build/trees/276`.

Trees whose tasks are not running: `.build/trees/143` (task done; 1 modified file) and `.build/trees/176` (task
deleted; one commit and 2 modified files that never landed) — carry them or say why they are superseded.
`check-a`, `check-b` and `train-a` are the harness's own integration trees.
