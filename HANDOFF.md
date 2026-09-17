# Handoff — native control plan, stage 1 seeded

Checkpoint: 2026-09-18. This continues the sessions that committed the native speedup
batch (`c4dfad1`); the owner paused optimization, so the work since then implements
stage 1 of [native_control_plan.md](native_control_plan.md#stage-1--seed-the-native-development-state).
Read [DEVELOPMENT_WORKFLOW.md](DEVELOPMENT_WORKFLOW.md) and [AGENTS.md](AGENTS.md) first;
this file records only the current state, the evidence that exists, and what is open.

## What is committed

The stage-1 theories are in `theories/` and listed in `ROOT`; what each one states is in
its [THEORY_MAP.md](THEORY_MAP.md) row and is not repeated here. In dependency order:
`Isabelle_Constant_Closure`, `Isabelle_Terms`, `Isabelle_Entities`, `Isabelle_Renaming`,
`Isabelle_Acceptance`, `Isabelle_Entity_Export`, `Development_Problems`,
`Development_Seed`, `Native_Development_Seed`, `Development_Policy`. Four shared base
theories gained reused content: `Finite_Presented_Collections`,
`Finite_Presented_Coordinates` (definitions moved up from
`Finite_Presented_Storage_Notions`), `Finite_Observation_Contracts` (now instantiating
`Isabelle_Constant_Closure`) and `Inference_Embeddings` (the finite rule-table embedding).

`tools/reconstruct_native_development_seed.py` adds the recipe that reconstructs the
seeded state from the checked context, and `tools/probe_theories.py` and
`tools/retire_temporary_storage.py` are the two host tools this work needed.

## What the evidence covers, and what it does not

- **The batch does not load yet.** With every proof checked in place, one probe loads it
  in 9.1 s and stops at a type error in `Development_Seed`: `development_seed_candidate`
  and `development_seed_leaf` apply `Development_Refinement` with no argument, while
  `Development_Problems` gives every contract the term its answer must establish. Nothing
  after that definition has been loaded, so further errors may follow it.
- **The proof that hid this is repaired.** No probe had ever completed before this session.
  With forked proofs the loader returns once a theory is registered and its theorems are
  stated, and `isabelle_term_rename_injective` had not returned after 413 s: its induction
  hypotheses were handed to the simplifier, which turns each into a conditional rewrite of
  an arbitrary equation between components. Instantiated at the components the case
  analysis supplies, `Isabelle_Renaming` loads in 0.6 s with every proof checked in place.
  The refused check of 2026-09-17 (`*** Timeout` after 1,209 s, 517 of 1,686 theories
  rebuilt against a 1,200 s session timeout) is very likely that same proof: rebuild volume
  does not account for it, since a complete proof of 1,677 theories from HOL took 470 s.
- **Everything the seed stands on loads.** `Isabelle_Constant_Closure`, `Isabelle_Terms`,
  `Isabelle_Entities`, `Isabelle_Renaming`, `Isabelle_Acceptance`, `Isabelle_Entity_Export`,
  `Development_Problems` and `Development_Policy` load with no error and with their proofs
  checked in place, against the accepted base session `Native_Complete_1789647297`
  (1,675 accepted theories, adopted 2026-09-17 15:24). A probe observes nothing about the
  517 dependents of the changed base theories and is not a repository check.
- **The recipe's expected reports are a placeholder.**
  `validation/reconstruction/native-development-seed-reports.json` holds zero records and
  empty digests; until an accepted run supplies the boundaries, that recipe cannot report
  `reports_equal`.
- **The plan's own basis** is `validation/native-control-plan-trace.json`: the trace of the
  existing contracts this plan revision reuses, with its own boundary statement. It claims
  no satisfaction table, no native admission of the plan and no condition-5a use.

## First actions

1. **Decide what a seeded problem's contract states, then repair `Development_Seed`.**
   `Development_Problems` says the contract is the term the answer must establish. The
   structure already fixes part of the answer: a candidate's subject is the head constants
   of its roots and it is decomposed into one leaf per constant of that subject, so each
   leaf corresponds to exactly one root term while a candidate covers several. Whether a
   candidate over several roots is one problem or one problem per root, and which term each
   carries, is a decision for the process — not a term chosen to make the file typecheck.
   The probe below gives a 9 s cycle on it, and `Native_Development_Seed` and the recipe
   scopes `development_seed_unanswered` and `development_seed_replay_answered` follow from
   the same decision.
2. **Re-establish the base.** It lived in `/tmp` by design — Isabelle binds an accepted
   heap to the absolute path of its sources, so an accepted context is never relocated or
   copied. Nothing unique is lost when `/tmp` is discarded
   (`validation/temporary-cleanup.json` records this), but a discarded base costs one
   complete build to restore:

   ```sh
   python -B tools/incremental_check.py establish --base /tmp/structural-accepted --threads 16 --timeout 3600
   ```

   That accepts the committed sources in one fixed directory, so a change to the four
   shared base theories of this batch is rebuilt once inside the base instead of inside
   every later check. Never point `--base` at a copy of an existing accepted directory.
3. **Check and retain.** With a current base:

   ```sh
   python -B tools/incremental_check.py check --output /tmp/NEW-UNIQUE-DIR --jobs 8 --threads 16
   python -B tools/incremental_check.py retain --output /tmp/NEW-UNIQUE-DIR
   ```

   The first accepted run of the `native-development-seed` recipe supplies the report
   boundaries that replace the placeholder file; write them from that run, not by hand.
4. **Continue stage 1.** Open gate items, in the order their subjects exist:
   - `Development_Policy` states and proves the first loop's one original requirement
     (an admitted payload is the presentation of an accepted entity) and the refusal of an
     absent entity. Still to state: supported goals, compiled guards and the fixed
     source/entry bindings, and the control in which a substituted permissive policy is
     refused.
   - Basis elements with their authority; owner-level elements exactly those the owner
     stated. Problems already carry authority and none is owner-level.
   - Locality: the read-state difference caused by a theory change lies within that
     theory's entities and their dependents.
   - Provenance: an entity from a failed, stale or different-context build is not admitted.

## Cycle and pitfalls measured here

- **Probe cycle.** `python -B tools/probe_theories.py --work DIR` loads every workspace
  theory that the base does not contain, resolving unchanged imports from the heap. One
  probe per directory, and read `DIR/probe.log` while it runs. `--parallel-proofs 0`
  attributes elapsed time to one failing proof; leave it unset for a pass/fail probe.
  A changed *base* theory is taken from the heap and reported, or supplied by a
  `--prelude` theory that states the added content on top of the heap and is named in a
  `--substitute`. Once the base is re-established from the committed sources, no prelude
  is needed for this batch.
- **Proof search over quantified facts is not cheap here.** Against a heap of this size,
  `blast`/`auto` over a universally quantified iff, and `auto ... split:` over definitions
  that unfold into nested cases, ran for ten minutes where explicit instantiation and
  `simp only:` load in seconds. Every proof in these theories is written that way, and the
  receiving proofs consume one plain equation (`isabelle_acceptance_membership`) instead of
  re-deriving the connection.
- **A theory or constant named after an Isar keyword silently truncates the proof** that
  follows it; the parser cut the proof and the next command began enumerating.
- Run every tool with `python -B`: a run without it leaves `tools/__pycache__` behind.
