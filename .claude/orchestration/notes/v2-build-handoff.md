# Handoff: orchestration v2 (sessions de86de45, f4318413 and 212840df, 2026-09-19)

Read this, then `notes/orchestration-v2-plan.md` (the design with every owner decision, in order, at its end), then
`README.md` (how it works now). The owner's standing rules for this work: nothing about the orchestration goes into
the project memory (notes go in `notes/`); nothing said in orchestrator sessions goes into the owner ledger
(`extract_owner_directions.py` leaves such sessions out; do not undo that); commit only when the owner says so; the
base rebuild is the owner's (the orchestration only tells when it is due).

## Where it stands

- Built and tested against a fake `claude` (`fakes.py`; 132 tests, run by name: `python3 -m pytest -q test_*.py` in
  this directory): the knowledge base (`kb-N`) and planning episodes as its forks; designer, task designer,
  investigator, reviewer, implementer, fixer, consultations; one producing and one supporting slot; brief and review
  tasks planned by the same machinery as implementer tasks; review before commit without cycles; efficiency
  escalation with a 3-hour hold; structural gathers (`v2.py step`); consultation by forks of warm sealed sessions;
  the knowledge base limited by its episodes' and consultations' room (rebuilt at 757K; a designer, 230K, forks it
  while it leaves that, the planner's base with HANDOFF.md otherwise; design tasks at most 230K); file
  locks for finalizations in flight; Isabelle limits (two runs, exclusive for base-advancing checks); no session
  stopped while its own background jobs run.
- Not committed. Not run live: the daemon is stopped; impl-31 is still listed idle (stop it before going live).
- The v1 files are deleted (copies were in session f4318413's scratchpad, which may be gone).
- HANDOFF.md still holds impl-31's work order: T3 installed but uncommitted (its NEXT is an `--advance-base` check),
  queue T4-T8. The first planning episode re-forms it.

## What the owner asked next (2026-09-19, the last message of session f4318413)

1. Simulate the whole run end to end and fix what it finds: done in f4318413 (the file locks, the Isabelle limits,
   the background-job rule, queue last, the owner-episode timeout came from it). Still worth doing again after any
   change: walk `start.sh` → kb-1 → plan-1 → brief task → implementer + review tasks → check → verdicts → commit.
2. Begin the base work with the planner/knowledge-base base (the `max` base), aimed at about 500K: look at what its
   context actually is (the pack under `state/base-pack-*`, `base-load.txt`, `implementer-prompt.md` as its system
   prompt), judge whether it does what the planner, the knowledge base and the designers need, and propose
   improvements and what must be updated or integrated before the next run. The owner added: the order in which the
   base presents its material matters (recent tokens weigh more): put what should steer last.
3. The base rebuild itself is the owner's.

## Open points to raise with the owner

- `base.sh` handles only `max`; `xhigh` and `high` need it when those bases are built.
- Unverified live: a fork of the knowledge base reading its cache with planner-settings.json's task-list variable;
  resuming a sealed non-base session and keeping it warm by forked pings; a fork of a sealed fork (a layer, the
  knowledge base) reading its cache; CLAUDE_CODE_SESSION_ID in background sessions' commands (the binary sets it for
  every tool subprocess).

## The bases (sessions f4318413 and 212840df)

`notes/bases-design.md` is the base work, revised in session 212840df after the owner's answers to its nine
decisions (recorded in its section 12). It corrects the first version (sizes were 6% too high: the pack's estimate
is already calibrated; base reads cost 0.1 of the base per request, 6.7M per implementer session at 560K, not 0.67M;
forks of a layer do not keep the stable base warm), measures the decided designs with real packs (A″ 462K, 404K with
the plan and REASONING_REUSE.md condensed; B 581K, 523K condensed; C″ 536K with the founding theories at signatures),
and answers the owner's questions 5 to 8 (sections 7 to 10: signatures alone suffice; the layered bases are economical
while a run is active and keep steering last by moving the direction tiers into the layer; what the system prompt is
and the options for the scheduling sentences; the condensation's mapping, part by part, with its measured shares).

Built in session 212840df (not committed): `base_pack.py` shortens `(* equations omitted: N lines *)` and its legend
names `[signatures]`; `select_base_load.refresh_indexes` (the theory names, the decision index, and the theory map
index without the theories the list holds) runs in `base.sh` before a new pack is frozen; the three drafts
(`base-load-max.txt`, `base-load-xhigh.txt`, `base-load-high.txt`) at the decided designs, each packed and
verified; `library-prompt.md` for all three bases, with option (b) for the scheduling sentences;
`protocols/_brief.md`'s rule that a build or fix brief states what of the plan and the reasoning it rests on; the
README. 132 tests pass (`python3 -m pytest -q test_*.py` in this directory).

## Continue here

The owner's sixth round (2026-09-19): a performance problem is reported (`v2.py escalate --efficiency`) and the work goes
on; no producing session waits holding the producing slot: with nothing productive left it parks (`v2.py park
run|fix|tree|answer`), the slot goes to the next task, and it is resumed first when its wait is over (drafting if the
tree is still held; its changes come back when it is free). The Stop hook lets a producing session end its turn only with
its result recorded or parked. The prompt's addition and the protocols say so. Earlier: the owner's words recorded
mechanically (UserPromptSubmit hook); one owner of the working tree; the first episode's brief. 152 tests pass. Not
committed.

Still to build when the owner says: the layered bases (`notes/bases-design.md` section 8); then a whole run against
the fake. Still the owner's: committing the condensation (HANDOFF.md, "The condensation"); the base rebuild.
