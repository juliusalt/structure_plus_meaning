# Plan: landing trains, and the documents-only check (the owner, 2026-09-22 ~12:40: "this is what needs to be
# addressed together with the plan for 4 — they are part of one main current bottleneck"; "if it falls back to linear
# it becomes the same problem — do not allow that"). Not built yet.

## 1. The bottleneck, measured (2026-09-21 20:00 – 2026-09-22 12:30)

- Main moves by one landing at a time (the landing lock), and a task in its own tree whose landing finds main moved is
  checked together with what landed (`finalize.land` → `recheck`, `tools/incremental_check.py check`). Every landing
  moves main, so nearly every landing after another rechecks: 38 rechecks, median 302 s, mean 273 s, max 397 s,
  each a heavy machine slot.
- 37 of the 38 passed. The combination of accepted tasks is almost always fine; what costs is doing it one at a time.
- Landings reached 1–5 an hour. At 12:30 six tasks were committing at once (108, 128, 149, 171, 173, 175): about
  30–50 minutes of rechecks in a row before any machine wait, and from 11:24 to 12:23 one landing held main while it
  waited for a heavy slot (fixed at 12:30: `finalize.MACHINE`, main let go while waiting), and 147 and 132 were refused
  behind it.
- Designs and investigations change documents only, still invent an acceptance check (design-171: 2 requests), and
  still take the 5-minute recheck at landing, which checks nothing a document can change
  (notes/proposal-documents-only-check.md).

## 1a. Why so many heavy runs at all (the owner, 12:45: "before implementing, tackle the problem further")

Seventeen hours to 12:40: 235 heavy runs, about 20 slot-hours — 80 started by sessions (69 repository checks, 7
replays, 4 retains), 116 finalizer checks for 67 tasks, 39 landing rechecks.

- **Every check pays for the distance of main from the base, not for its task's change.** Its time is 61% proof
  (median 186 theories rebuilt of ~1,820) and 37% recipes (median 35 of 52 re-executed). Right after base d
  (09:33) a check rebuilt 0 theories in 0–8 s; after task 124 landed (an import every recipe's closure reaches) every
  check rebuilt ~155 theories and re-ran 35 recipes, ~330 s; a task changing a widely imported theory rebuilds
  1,200–1,650 theories, 11–15 minutes. The base and the receipts move only when the planner places an advance or a
  retention task (#119 at 09:37; #144 waiting), so between two advances every check, the sessions' own included,
  rebuilds everything that landed since. Base d's own advance checked 15 theories and stored its heap in 37 s.
- **The same tree is checked twice:** 24 of the 116 finalizer checks re-ran what the session had just checked, nothing
  in theories/, tools/ or ROOT changed after.
- **A task's journey is three full checks:** its session's (to know it passes before handing over), the finalizer's
  (the same, mostly), and its landing recheck (serial, one per landing: sections 3–7).

The levers, largest first:

1. **The base and the receipts follow main.** The landing check of exactly the tree that becomes main runs with
   `--advance-base` (its heap stored), is adopted as the base when it lands, and its receipts are retained and
   committed with it. Every later check then rebuilds only what changed since the last landing — mostly its own
   task's theories and their dependents — and re-executes only the recipes its change reaches. With trains, one
   advance per train. What it needs: an advancing check no longer taking the whole machine (it does today because the
   base heap is under every running probe — kept instead until no run uses it, old bases removed when unused: 2.1 GB
   each, 903 GB free); a harness commit of the receipts per landing; the lineage's depth watched (each advance is a
   level; a complete proof resets it, #142).
2. **The finalizer takes the session's own accepted check** when the tree is the one it checked (its report records
   its inputs' hashes): no second run of the same tree.
3. **Landing trains** (sections 3–7): one recheck per train.

Expected: with 1, a typical check from ~330 s to the rebuild of its own change (tens of seconds to a few minutes);
with 2 and 3, about 235 runs to ~150 and 20 slot-hours to perhaps 4–6.

The owner, 12:55: the finalizer takes the base and the receipts over (lever 1), and a harness commit of the receipts per
landing is fine. The lineage's depth is decided by data: every check's report names its base and the base's level;
the finalizer records per check its level and its base-load and proof seconds, and a complete proof (the lineage
reset to one level) is placed when the measured cost of the depth passes what a reset costs — measured, not assumed.

## 1b. Every task checks on its own — batched instead (the owner, 12:55: "can we tackle the fundamental reason … every
## task having to do its checks on its own, maybe they could be batched too?")

Measured (seventeen hours to 12:50): a task's check is run by its session (69, of which 27 were refused by the guard
for the machine and tried again, and 42 ran in the background while the session parked), again by the finalizer (116,
24 of them on a tree the session had just checked), and again at its landing (39). Checks pass: 144 of 155 finalizer
checks since 2026-09-21 19:40 passed (93%); of the reports still on disk 30 of 34 checks and 12 of 12 landings. What
each task pays is mostly waiting for, running and reading a check that passes.

The same idea as the train, one step earlier: **the repository's check becomes the harness's, run for every task that
is ready at once.**

1. **Sessions check with probes** (light, parallel, seconds: the theories they change, on the base heap) and do not
   run the repository's check themselves. Its runs, refusals, parks and readings leave the sessions: about four
   requests a check.
2. **A check queue:** a task's hand-over (`v2.py finalize`) queues its check, and a session that wants one before
   handing over asks for it (`v2.py check`, parked until its result comes, resumed with it — as `park run` now, but
   for a check the harness runs).
3. **A check batch:** when a heavy slot is free, the harness takes every queued check as one batch in an integration
   tree — main (the base, which follows main: lever 1) with each member's branch merged, in the planner's order; a
   member whose lines conflict is checked alone — and runs one `incremental_check.py check`. Shared dependents are
   rebuilt once and every recipe runs once for all.
4. **Attribution, as for a train (3.5):** the report's failed theories, recipes and host tests are matched to the
   members whose changes reach them; the others pass. Ambiguous suspects are bisected on the two heavy slots, never
   one by one. A member that fails is told its own errors: its quick fix, or the session that asked, resumed with them.
5. **Then as now:** a member that passed goes to its review, and after it to the landing train (3–7); with the base at
   main, the train's check rebuilds only the train's own changes.

Soundness: a batch that passes says the members stand together on main; a member that passed only beside another is
caught by its landing train, which checks exactly what lands (section 2). The landing check stays the one gate of main.

What it removes, on the day measured: the sessions' 69 runs (and their 27 refused tries), the finalizer's second run of
the same tree, and one run per task becomes one per batch — about 116 finalizer checks to some 25–35 batch runs. With
lever 1 each run is also smaller. Heavy runs: ~235 → ~40–50.

Open: whether a review may come before the check (review, then one check that also lands — the batch and the train
become one): it saves the separate check entirely, at the price of reviewing work not yet checked and a re-review when
the landing check fails (7% of the time). Not in this plan unless wanted.

## 2. What must hold (unchanged)

- Main only ever moves to a state that was checked as it will stand: the combination is what is checked.
- Each task's work is its own commit on its own branch, reviewed before it lands; the history keeps one "Take up the
  work of task N" merge per task.
- A conflict of lines is reported and resolved by the task's session (bring-main, marked drafts), never behind it.
- The machine goes in the planner's order; nothing lands that its review did not accept.
- No step falls back to landing tasks one by one: a failed combination is resolved by attribution and parallel
  bisection, and those that did not fail land without waiting on the one that did.

## 3. The design

### 3.1 The landing queue

A finalizer's commit of a task in its own tree commits on the task's branch as now (`commit_and_land` up to the
branch commit), then enters the landing queue — `state/landing-queue.json`, under its own lock: task, branch head,
files, the kind (code or documents, 3.6), when queued — and waits for its entry to be decided. It does not land itself.

A task in the one tree (no tree of its own) lands as now; it takes the landing lock and is one landing between trains.

### 3.2 The lander

One at a time, under the landing lock, a lander takes the queue as it stands — every entry not yet decided — as one
train. The lander is whichever finalizer takes the lock first; the others, waiting for their entries, find them decided
(landed, or refused and why) and end with that result. A finalizer whose budget ends while its entry is still queued
leaves it queued (it is landed by the next train) rather than refusing it; the watchdog starts a lander
(`finalize.py land-queue`) when entries wait and no finalizer is alive — as `lands_when_free` does for `lands_again`.

### 3.3 Assembling a train

In the planner's order (the machine's order), in one integration tree kept for it (`.build/trees/train`, a worktree
at main, reset for each train):

1. Merge each member's branch (`git merge --no-ff`, "Take up the work of task N"), with what the landing does now —
   imports merged as a list (`imports_agreed`), index rows agreed (`rows_agreed`, both sides changed only), receipts
   put back. A member whose lines conflict with main or with a member before it leaves the train: its marked files are
   kept for its session (`keep_marked`, from the integration merge) and it goes back as a merge refusal does now; the
   others go on. The train is the members that merged.
2. The combination's trouble (`new_trouble` of the integration HEAD against main): trouble attributable to one member
   by the files it names (ROOT lines, imports) takes that member out; trouble not attributable goes to 3.5.
3. A train of one lands as a single landing does now (its recheck unchanged).

### 3.4 One check of the combination

- Every member documents-only: the documents check (3.6), seconds, no machine.
- Otherwise one `LANDING_CHECK` of the integration tree. It waits for a heavy slot with main let go (as
  `finalize.MACHINE` now): the lander lets go of the landing lock, waits, takes it again and assembles the train again
  from the queue as it then stands — later arrivals join, and nothing is checked twice for waiting.
- Passed, and main unmoved: main moves once, to the integration HEAD (a fast-forward of the one tree; what stands
  uncommitted there over the train's files is waited for first, as now). Every member is committed: its outcome, its
  tree taken away, its sessions released, one push.
- Main moved outside the finalizer meanwhile (the owner's commit): the train is assembled again on it and checked again.

### 3.5 A combination that fails — resolved without one-by-one

1. **Attribution** from the check's own report (`incremental.json`: `failed_recipes`, the theories whose proof failed,
   the host tests that failed). A failed recipe reads the files its sources manifest names
   (`validation/reconstruction/<recipe>-sources.json`, `files`); a failed theory depends on its import closure
   (`tools/execution_support.source_graph`). The suspects are the members whose changed files are in what failed;
   the rest are cleared.
2. **The cleared land at once, after one check:** `main + cleared` is checked (one run); passed, they land. At the same
   time, on the second heavy slot, the suspects are bisected on top of it (speculatively, `main + cleared + half`), so
   the rounds overlap.
3. **Bisection among the suspects**, two halves checked side by side on the two heavy slots each round: log2(k) rounds
   for k suspects, never k. A half that passes lands (after its base has landed); a single member that fails is the
   one: it goes to its quick fix exactly as a landing check that failed does now (`landing_failed`: its tree holds main
   with what landed, the fix is made where it is checked again), with the check's own error list.
4. Attribution that finds no suspect (a failure of the combination as such, or of what landed before): the whole train
   is bisected, the same way.
5. Two halves that each pass when the whole failed (an interaction between them, not a fault of either alone): the
   first half lands, and the second is checked on top of it in the next round — what fails there is the member that
   does not stand with what landed, and it goes to its quick fix as in 3. The interaction costs one round more, and
   only its own members wait for it.
   With 37 of 38 rechecks passing, a failed train is rare; when it happens it costs one or two runs more, not one per
   member.

### 3.6 Documents-only commits (notes/proposal-documents-only-check.md, folded in)

- A commit is documents-only when every file it takes is a Markdown document outside `theories/`, `tools/` and
  `validation/` (ROOT and code never), read by the finalizer from `--files`; HANDOFF.md, committed with any task, is a
  document.
- `--check` is optional for it: left out, the finalizer's check is the documents check; given, the session's runs.
- The documents check (about a second, no Isabelle, no heavy slot): the structural source checks
  (`tools/check.py` `source_checks()`: theories declared and present, no proof escapes); every THEORY_MAP.md row names
  a theory that exists, none doubled; no conflict marker in a committed document.
- In a train: documents-only members need no heavy check of their own; a train of documents only is checked by the
  documents check; a mixed train's one heavy check covers them.

## 4. What changes for the sessions and the planner

- Nothing in what a session does, but the designer's and investigator's hand-over: "a decision that changes documents
  only hands over without `--check`".
- The planner is told once per train: "Tasks 108, 128, 149 landed together as <ref> (one check of the three with main,
  5 min)", each with its summary's first sentence and its follow-ups; a member taken out is told as now, with why.
- `lands_again` (main held past a budget) becomes "left queued": it lands with the next train.

## 5. Where it can go wrong, and what then

- A lander dies mid-train: the integration tree is reset by the next; the queue's entries stay undecided until a
  lander decides them; main moved only by a completed fast-forward (atomic in git).
- The integration tree's merge differs from what each member's own tree would make: the train's merges are the ones
  that land; a member taken out lands later by its own tree's merge as now.
- Two landers: the landing lock stays the one mutual exclusion; the queue has its own lock for entries.
- The watchdog's FINAL_MAX: a lander's budget covers one train (assembly, one check, a bisection round); a longer
  resolution is carried on by the next lander from the queue's state (decided members, suspects, round).

## 6. Tests and mutation cases

- Three accepted tasks in their trees, main moved: one check, main moves once, three "Take up" merges, each outcome.
- A member conflicting with an earlier one leaves the train with its marked files; the others land.
- A failing combination with the failure attributable to one member: the cleared land after one check, the member goes
  to its quick fix; the number of checks run is 2, not 3.
- Not attributable: bisection, two checks per round side by side; never one run per member.
- Documents-only: hand-over without `--check`; the documents check fails on a THEORY_MAP row naming no theory and on a
  conflict marker; an all-documents train takes no heavy slot; a mixed train one check.
- A finalizer whose budget ends with its entry queued leaves it queued; the watchdog starts a lander.
- Main moved by the owner during the check: the train is assembled again.

## 7. Expected effect

On the day measured: 38 rechecks of 5 minutes in a row → one check per train. With trains of 3–6, about 8–12 checks,
some 2–2.5 hours of heavy machine time a day freed for the tasks' own checks, and a landing waits for at most the
train before it, not every landing before it. The documents-only commits (about 10 a day) take no heavy slot at all.

## 8. Order of work

1. The documents-only check (3.6): the smallest, independent, and used by the train.
2. The queue and the lander (3.1–3.2) with trains that pass (3.3–3.4).
3. Attribution and parallel bisection (3.5).
4. The planner's one message per train (4); README, handoff, protocols; deploy with no landing in flight.

## Open for the owner

- The documents check in `tools/check.py` (a `--documents` mode, the project's, a task's to add) or in finalize.py (the
  harness's, calling `source_checks()`): the second needs no task; the first is usable by sessions too.
- Speculative pipelining beyond 3.5 — checking train k+1 on top of train k while k's check runs, on the second heavy
  slot — would keep landings continuous; it doubles the machine a landing takes while it runs. Not in this plan unless
  wanted.
