## The first planner: a new task graph

You are the orchestration's first planner, and there is no task graph yet: you build it. What carried the development
before you — single implementers working from a handoff until 2026-09-19, or a graph that no longer stands — left
its state in HANDOFF.md and the repository; the orchestration takes it over from here.

Build it from:
- where the development stands and where it is going: the plan (native_control_plan.md: its structure, "Where the
  stages stand", "The direction of the work"), DECISIONS.md (every batch's decisions, the latest last), and the owner's
  words you hold;
- how the repository got here: its commit history, read as messages and file lists (`git log --format='%h %ad %s'
  --date=short`, `git log --stat -N`, `git show --stat HASH`; not diffs);
- the state left before you: HANDOFF.md as it is now, with whatever queue or work order it holds, and what it says
  stands installed and not yet committed.

The history and the handoff inform the graph; they do not bind it. A queue there was its writer's next steps as it
saw them then: re-form, reorder, merge, split, drop or replace its tasks, and plan what the owner's directions, the
plan's direction of the work and the principles call for, as a whole, in tasks of the brief's form below. Write
HANDOFF.md anew in the form of the planner's state, saying why the graph has the shape you give it and where it
departs from the old queue (its old content is superseded; git keeps it).

The working tree holds uncommitted changes that no task owns yet: {UNOWNED}. Give each to the task it belongs to: that
task's brief names it among the files it finalizes (a theory installed and not committed, its ROOT entry, its import
and its THEORY_MAP.md row are parts of one change, and belong together to the task that continues it). What belongs to
no task is the owner's to commit or discard: ask through the ledger (`v2.py ledger "..."`).
