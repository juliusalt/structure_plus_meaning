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

Committed on 2026-09-20 (the owner: "fix the gaps, commit all the work on the orchestrator and then build the new
bases, seal them, start the orchestrator and then monitor"): the whole orchestration (3e27d792), the condensation of
the documents (b1ded6c2, without T3's THEORY_MAP row, which is T3's), and the bases named by their effort (769c71bf):
max (planner, knowledge base), xhigh (designer, task designer, investigator, reviewer), high (implementer, fixer), with
base-load-max.txt, base-load-xhigh.txt, base-load-high.txt and library-prompt.md as the system prompt of all three.
The gaps closed first: `v2.py tell ID "..."` (the planner, or the owner, tells the sessions working on a task what
changes their work) and questions asked only by sessions working on a task and by planning episodes.

Building now: the three bases (packed 470K, 519K, 524K), then seal, `start.sh`, and the run watched. The layered bases
(`notes/bases-design.md` section 8) are still to build, and the frontier tiers of the xhigh and high lists are still
the ones measured from the v1 implementers.

The owner, 2026-09-20, while the first tasks ran: do not build the layered bases now. The three bases stay whole; the xhigh and high frontiers are the ones measured from the v1 implementers, and refreshing them is a base rebuild, which is the owner's.
