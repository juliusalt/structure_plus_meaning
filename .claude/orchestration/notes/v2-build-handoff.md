# Handoff: orchestration v2 (sessions de86de45, f4318413 and 212840df, 2026-09-19)

> The sections run in time order; **the latest handoff is the last section** ("Handoff, 2026-09-21 ~18:30"). Start
> there.

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

---

# Handoff, 2026-09-20 16:15 — the day the machinery was fixed, and what is left

## Where it stands

The orchestration is **stopped** (`v2.py stop`: inactive, every session sealed, nothing running). `start.sh` resumes
it. The daemon is up and pings only the bases. All three bases were refreshed by hand at 16:09–16:10 and answered
**OK** (99% reads); their miss counters are cleared. The working tree is consistent (`v2.tree_trouble()` → none).
Everything of the harness is committed and pushed (`20f8ca98`, `173a025d`, `75fc63bf`, `b4a86baa`, `584ae4fc`,
`cfc90eab`, `cc6087c6`, `c55eea9a`, `0ab7b7c8`); **188 tests pass** (`python3 -m pytest -q test_*.py` here).

The tasks' own work is **uncommitted in the main tree** and whole: tasks 7, 22, 46, 48, 50. Task 7's batch is
complete and wants only its acceptance check. 35 tasks are open, 15 of 50 done. Four commits of content landed today
(`9bb1dd7a`, `6227819a`, `2edcabd3`, `91979be0`).

## What changed, in one line each

- **Nothing is taken out of the working tree.** `shelve`, `base_holds` and the ROOT-line surgery are gone; a task
  that stops leaves its change whole. This closed the family that caused every blocking failure of the day.
- **A tree invariant** (`v2.tree_trouble`) states what the checks refuse on — undeclared theory, declaration with no
  theory, dangling import, merge markers, duplicates, a base advanced with a theory the tree lacks — reported where
  it breaks, read by the finalizer before it spends a check, and shown by `health.py`.
- **A worktree per producing task** (`ORCH_TREES=1`, on). Measured: a check inside one reused all 1,797 theories in
  172.88 s. `.build` is linked; the link is excluded in `.git/info/exclude`. Index files merge by union
  (`.gitattributes`), and what union gets wrong the invariant reports. A task whose work already stands in the one
  tree keeps working there.
- **Rate**: `ORCH_WORKERS=1` (every slot), episodes batched at 900 s with a 300 s floor, briefs held at a backlog of
  six, base pings every 40 min against a 55-min entry.
- Smaller: a stopped or stale background job no longer holds a session for ever; a check that cannot run costs no
  round; a commit refuses another task's file or a draft's stand-in and closes the entry before it; an exclusive
  claim names what holds it; a timing run takes the machine (`v2.py measuring`); an answer to an ended session is
  written where the work reads it and `v2.py carried` clears it; `v2.py after … none` takes a dependency back;
  mail survives a failed resume and is named when it reaches nobody; `manifest.py changed` answers about the
  session's own tree; a blocker that is not in the task list is named.

## What to do first

1. `start.sh`. Watch `health.py` — it now states each base's last verdict, the trees standing, the build backlog and
   any answer that reached nobody.
2. The five tasks with work in the tree resume **in the one tree** (by design). Only new tasks get worktrees. When
   they have landed, every producing task will have its own tree.
3. Task 7 needs its acceptance check and nothing else.

## What is not done

- **`ORCH_WORKERS=1` gates every slot**, so while one session produces, no review, no episode and no consultation
  starts. Not a stall — they run when it parks or ends — but a finished task waits to be reviewed. `ORCH_WORKERS=2`
  restores a supporting session without undoing the episode batching.
- **The worktree path has never run live.** It is tested (three tests) and measured, but no real task has worked in
  one. Watch the first: its fork's cwd, its check, its commit-on-branch, and its merge.
- **Union merges can resurrect a line one side deleted** — the invariant reports it, nothing prevents it.
- **`.woken`, `state/base-pack-*`** are swept hourly; `state/mail/*.jsonl` of dead sessions are not.
- A finalization holds its files while it checks, fixes and commits, and not while it is reviewed; an append in
  flight at commit time is waited for (10 min) and only then refused.

## Found after the handoff was first written (16:15–16:40)

Four more, by the same method — asking where a shape lives rather than waiting to meet it. All fixed, all tested
(190 pass), all pushed (`0ab7b7c8`, `b95a7453`).

- **A blocker that is not in the task list blocks its dependents for ever.** `deps_done` waits for
  `status == "completed"`, and a dropped or never-written task never has one. Task 6 waited on the dropped task 18
  that way today. Now named to the planner, hourly, while it stands; the task still waits, because whether that work
  was done elsewhere is the planner's to say.
- **One finalization at a time is no longer needed** when tasks hold their own trees — that rule existed because a
  second check would see the first's uncommitted files. A base-advancing check still runs alone, by its own claim.
- **A knowledge base that never replies INTEGRATED stayed integrating for ever**, and while it does, no planning
  episode and no consultation can fork it: the deliberative half stops, silently and permanently. Bounded at twenty
  minutes, then given up with an ATTENTION line and an event, and another built. Its notes stand in
  `state/<kb>-notes.md`, and what they hold that HANDOFF.md does not is lost to the next one.
- **A knowledge base that never finishes loading** is the same shape — no second load starts while one is recorded.
  Bounded at an hour.

The first and the last two are the shape that cost the day: something waits on a word that may never come, and
nothing bounds the wait. If you look for one more thing, look for that.

## How the search was done, and what is unsearched

By failure *class*, not by incident: predicates wrong at their edges (a parked session counted as ended; `.hit`
meaning "pinged" not "warm"); state that outlives its subject (markers, claims, shelves, mailboxes, worktrees);
messages that lie; operations with no undo; things with no timeout or the wrong one. Unsearched: the guard's read
limits and batching rules, the knowledge base's growth and condensation, the review protocol itself, and anything
that only shows under real concurrency (`ORCH_WORKERS>1`), which nothing has exercised since the rate was set to one.

---

# 2026-09-20 16:40–17:00 — the base taken out of a task's directory, and the ping's verdict made true

The owner: do the two things below, commit nothing until told, and do not start.

## The keep-warm ping's verdict is recorded where health reads it

`base.sh WHO warm` only **echoed** its verdict; `warm.log` learned it solely because the daemon redirected its
output. A ping run by hand therefore left no line, and `health.py`, which reads that log, reported the last
*daemon* verdict instead. That is why it said "base max: was COLD and was rewritten at 15:19:51" at 16:39, fifty
minutes after all three bases had been refreshed by hand at 16:09–16:10 and answered OK. Same class as `.hit`
meaning "pinged" rather than "warm": an instrument that reports a state nobody holds any more.

`base.sh` now writes the verdict to `warm.log` itself and prints it as before; the daemon redirects only stderr
(`>/dev/null 2>> warm.log`), so nothing is written twice. `warm_daemon.sh` was restarted for the change to take
(a running `/bin/sh` holds its loop in memory; the old daemon would have kept the old redirection and the file's
offsets shift under it). Verified live at 16:50–16:51: the restarted daemon pinged all three, each answered
**OK, 99% reads**, each verdict stands once in `warm.log`, and `health.py` now says `warm at 16:50:57` and so on.

Two tests (`test_base_warm.py`): a ping run by hand is recorded where health reads it, end to end through
`health.bases_and_trees`; and the daemon's redirection does not write the verdict twice. Both fail without the
change. base.sh's own PROJECT is this repository, so that world fakes HOME and the state directory around the real
tree rather than using `fakes.World`.

## The base no longer stands in a task's directory

The accepted base stood in `.build/tasks/7/check2/proof`. Two things were learned while moving it:

- **A check cannot move the base by being run again.** `validate` sets `export_context = proof if proof is not None
  else base`: with nothing rebuilt there is no new proof context, and `--advance-base` re-activates the base where
  it already stands. A check run at 16:45 from that base reused all 1800 theories and left it exactly where it was.
- **A proof context cannot be moved on disk.** `load_parent` re-derives `directories` as
  `[*parent['directories'], str(directory)]` and asserts it equals what the receipt saved, so a copy at another path
  is refused: `Context claim changed: directories`. (The heap itself is not in the directory — it is in
  `~/.isabelle/*/heaps/*/<session>`, named by the receipt with its digest.)

So the base moves only when a check **rebuilds** something, and it lands wherever that check's `--output` is. It was
re-seated by re-proving task 7's 63 theories from the last repository-level base:

    python3 -B tools/incremental_check.py check --base .build/check-20260920a/proof \
        --advance-base --output .build/check-20260920c

accepted in 332 s (proof 141 s, recipes and host tests 177 s), 1737 of 1800 reused, no failed recipe, both host test
suites green. The base is now `.build/check-20260920c/proof`; its lineage is eight directories, every one of them
under `.build/` directly, and `v2.base_at_risk()` is empty. The whole chain re-verifies (`load_parent`: 1801
theories, stored heap). `.build/check-20260920b`, the 16:45 check that proved nothing new, was removed (3.1 G).
`.build/tasks/7/check2/` and `.build/tasks/7/final-check/` are now ordinary run output of task 7 and nothing chains
from them.

## And the rule that keeps it out

Re-seating alone does not hold: the next final check with `--advance-base --output .build/tasks/{ID}/...` puts the
base straight back, and only the protocol asked sessions not to. It is now refused at both ends —
`v2.base_would_stand_in_a_task(check)` names the task paths a base-advancing check mentions (`--advance-base` or
`adopt`, `--output`, `--proof`, `--base`, relative or absolute):

- `v2.py finalize` refuses to record such a job, and says what to give it instead;
- `finalize.py check` refuses to run one recorded before the rule, writes why into `finalize.log`, and costs the
  task no round — the same shape as the tree-invariant refusal beside it.

`protocols/_production.md` states the refusal. Task 7's own `finalize.json` still names
`.build/tasks/7/final-check`, which is harmless: its check has already passed and `finalize.py commit` never reads
the check again. If it is ever re-finalized, the session is refused and records a fresh command.

## Where it stands

**197 tests pass.** Nothing is committed — `main` is still ahead of `origin/main` by one (`7a0018cc`), and
uncommitted in `.claude/orchestration/` are the previous session's base-at-risk detection plus this session's:
`v2.py`, `finalize.py`, `health.py`, `base.sh`, `warm_daemon.sh`, `protocols/_production.md`, `test_v2.py`,
`test_finalize.py`, `test_base_warm.py`. The orchestration is still inactive; the daemon is up (new pid) and pings
only the bases, all three warm.

---

# 2026-09-20 17:00–17:50 — the planner made one long-lived session, and what the day's record showed

The owner: search again for problems and fix them; then go through the prompts and the information the tasks and the
planner were given, then the scheduling of the day's tasks, then the communication; then make the planner a
long-lived session that integrates into the knowledge base when its context forces it to end, and send its messages
immediately without aggregation. Commit nothing until told.

**209 tests pass.** Nothing is committed.

## The planner

One session now lives across its events instead of one session per batch of them.

- **`plan()`** delivers every event to the planner that lives, each as its own message, at the dispatch that follows
  it; `EPISODE_GAP`, `URGENT_GAP` and the thirty-second burst wait are gone. A new planner is forked only when none
  lives, and then, as before, only from a knowledge base that holds the last one's notes.
- **The planner is not a worker** (`working()`). Gating it behind `ORCH_WORKERS` would have made it answer an event
  only in a producer's gap, which is what the owner asked to end. It is one session with short turns, so it neither
  waits for production nor holds it up.
- **Between events it is `idle`**: its turn may end (`ctx_gauge.may_end`) once its mail is taken, the watchdog seals
  it and clears the events it was given (by ending its turn it says it handled them), `held()` keeps it warm for ever
  and `deliver`/`resume` wake it. One that goes cold there is lost — `v2.resume` refuses a cold session, so an event
  delivered to it would sit in a box nobody opens — and what it had not handled goes to the next.
- **It ends once, when its window is full**: the notice asks for HANDOFF.md and the notes, which are now what it has
  settled, aggregated, with what has since been answered or superseded left out, rather than a log of the batch.
  A planner lost before that is named to the next one, with what that costs.
- `talk.sh` joins the planner that lives (waking it) instead of opening a second; the owner leaving no longer ends
  it, it goes back to its events. `v2.py who planner`, `status` and `health.py` find it between events.

Why: **28 of the 59 sessions started on 2026-09-20 were planning episodes**, each a fork of the knowledge base at
about 510K, each followed by one of the 28 knowledge-base integrations.

## What the day's record showed, and what was done about it

- **Six and a half hours of standstill** (01:34–03:35, 04:49–07:24, 07:24–09:38), each beginning right after a
  knowledge-base integration: nothing worked, nothing in the queue could start, two sessions sat parked until their
  three-hour hold woke them, and only `health.py` said so, to nobody. Only the planner can move the graph, and the
  planner is woken by events — of which there were none. `v2.standstill()` now names it to the planner, with what is
  parked and for what, what is ready but blocked, and what came back and has not been re-planned, and names it again
  every thirty minutes while it lasts. (Two tasks stand parked "after ?" right now — 22 and 50, three and a half
  hours — which is exactly what it is for.)
- **Answers waited 4 to 13 minutes, and two waited 84**; six of nineteen came to a session that had already ended
  and had to be carried by the planner. The wait was the batching, which is gone. A session that records its result
  with a question still open is now told so, and where its answer will go, so that what it assumed is in its result.
- **A dropped task stays pending in the list**, so its dependents waited on it with nothing able to complete it and
  nothing saying so — the same shape as the blocker that is not in the list at all, which was named yesterday while
  this was not. `deps_done` now names it hourly, and `v2.py drop` says at once what the drop leaves waiting.

## The prompts

- **Every role was told it had a git worktree of its own** (`.build/trees/{ID}`, branch `task/{ID}`). The planner,
  the task designer, the reviewer and consultations never have one, and a producing task whose work already stands in
  the one tree keeps working there. The working-tree text is now `protocols/_tree.md`, given only to the roles that
  write the tree, and `{TREE}` (`v2.tree_text`) says which of the two is true for that session.
- **`_inherited.md` and `_held.md` held the same sentence**, and every role but the consultant included both: the
  same line, with the same value, twice in one first message. `_held.md` is gone. A test now refuses two shared parts
  with the same text, and a role that includes one part twice.
- **The checks-and-parking text** went to the planner and the task designer, which run no checks and cannot park. It
  is `protocols/_checks.md` now, for the roles that do. The planner's message no longer mentions a tree, a park or an
  Isabelle limit.
- `test_every_role_has_a_protocol_with_nothing_left_unfilled` was writing its warnings into the **live** `v2.log`; it
  runs in its own state now and asserts that nothing was left out at all.

## Two more of the day's own class

- **`resume()` never looked at whether the resume worked.** It returned True whatever the CLI did, so a failed wake
  left the session recorded as working while nothing ran, and — because the mail is taken out of the box before the
  resume — the message it carried was lost. Every caller reads that answer to decide whether to keep the message; one
  of them starts a fixer instead. It now returns the truth.
- **Mail that a failed resume could not carry went back as one message from the harness**, with its senders buried
  inside it, so the next read said the harness had said what a reviewer or the planner had. `unread`/`keep_mail` put
  each message back with its own sender. Mailboxes of sessions the archive has taken away, and empty ones of sessions
  that read nothing ever again, are now swept with the rest.

## What is not done

- `ORCH_WORKERS=1` still gates the producing and supporting slots against each other: a finished task waits to be
  reviewed while something produces. The planner is now outside that gate; the two slots are not. That is the
  owner's rate.
- The graph is nearly one serial chain: 28 of the 35 queued tasks wait on a predecessor, so the queue offers about
  one startable task at a time whatever the rate is.
- The long-lived planner has never run live. Watch the first: that its turn ends and it is sealed rather than nagged,
  that the next event wakes it warm, that its notes at the end of its window are aggregated and not a log.

---

# 2026-09-20 18:40 — what links sessions, and what it was reaching

The owner saw sessions seeing each other's changes. It is one setting: `CLAUDE_CODE_TASK_LIST_ID:
"orchestration-graph"` in `planner-settings.json`. Every session started with that file joins one named task list —
the graph — and Claude Code injects the list's state into each of them as a system reminder when it changes.

**Measured across the day's 39 sessions.** Each session on the shared list took 1 to 5 injections of about 816
characters (~270 tokens). Every other session's task list is **its own**, named by its own session id: ten worker
lists on disk, one per worker, none shared, and the three bases have none at all. So the workers — implementers,
fixers, designers, investigators, reviewers — were never linked; their reminders (196 to 337 characters) are their
own step plans, which their protocol asks them to keep.

**Where it was wrong: the knowledge base.** It was on the shared list, it may not edit the graph (`work_meter`
refuses it), it has no use for the state, and — the part that compounds — *everything injected into it is inherited
by every session forked from it*. The sealed kb-1 carries three such injections, about 800 tokens, in the 538K prefix
that every planner and every consultation reads. It is now started with `worker-settings.json`, which is
`planner-settings.json` without that one variable and identical in everything else; a consultation of it inherits
that and is off the list too. A test asserts the invariant: a role is on the shared list exactly when it may edit the
graph, and the two files differ in nothing else.

The current kb-1 keeps what it already holds — it is sealed, and a bare resume keeps its settings — so those 800
tokens stay until the next knowledge base is built, which happens on its own.

**Turning it off entirely** would mean dropping the variable from `planner-settings.json`. That is not advisable:
the graph *is* that list (`~/.claude/tasks/orchestration-graph`, read directly by `v2.read_task` and `all_tasks`),
and it is how the planner and the task designers hand work to each other and to the harness. Without it each of them
would write into a private list nobody else could read.

## The rate, 2026-09-20: ORCH_WORKERS 1 → 2

The owner's choice, made after measuring what the rate actually gates. It caps the sum of the producing, supporting
and consultation slots; a quick fix starts whatever it says, and the planner and the knowledge base are outside it.

It is **not** what limits production. `produce()` takes one producing session whatever the rate is, so at any setting
exactly one designer, investigator, implementer or fixer runs; a parked one frees the slot for another task. What 1
cost was the other two slots: a finished task waited to be reviewed while something produced, and a question to the
knowledge base or to an author waited for a gap. 2 buys those back at no cost in Isabelle or memory.

Past 2 nothing more is available without changing `produce()`, and then the machine binds: two Isabelle runs, three
having reached 59 of 60 GiB, and a base-advancing check running alone. Measured the same day, the task graph itself
admits 7 tasks at its head — five already in flight — and 1 or 2 for 17 of its 20 levels, so a wider rate would buy
nothing until the planner draws tasks that can run side by side.

## Independence in the graph, 2026-09-20 (the owner)

The planner and the task designer now prefer tasks that can run beside each other, where the work admits it. The
rule is written in both protocols, because the planner draws the design and brief tasks and the task designer draws
most of the build and fix tasks:

- a dependency is written only where it is **real** — the task's inputs are another's artifacts, or its brief rests
  on a decision another takes. Order is not dependency and tidiness is none; a review task depends on the task it
  reviews and on nothing else;
- what makes a task independent is the rule the brief form already carries: its inputs are artifacts, never a
  predecessor's reasoning, and the reasoning it needs is in it;
- and never at the cost of the work: no splitting a piece of reasoning that belongs together, no two tasks
  establishing the same notion (its contract is proved once and consumed), no task left short of what it needs to
  decide. A task that must ask before it can begin is worse than one that waits.

In the order, independence sits after uncertainty and before size: of tasks otherwise equal, queue first the ones
that can run beside what is already running, so that a park hands the producing slot to something ready.

**The rule is measured, not only asked for.** `v2.startable()` is the width of the graph as it was drawn — the
queued tasks that are ready with every blocker completed — and `v2.py status` prints it, so it reaches the planner in
every message. At one it says so plainly. The graph as it stands today is 20 deep and 1 or 2 wide for 17 of those
levels, and on 2026-09-20 the orchestration stood still for six and a half hours for want of anything independent to
run when the task holding the slot parked.

## `start.sh --fresh`, 2026-09-20 (the owner)

The owner, for the next run: reset the knowledge base, have the planner fork the clean one, and make its first piece
of work the taking of stock — integrate what has been produced, drop the tasks that only exist because of faults now
fixed, and rethink the structure against the architecture as it now is.

Built as a repeatable capability rather than a one-off, because a reset is wanted whenever the knowledge base is
rebuilt. `v2.py start --fresh` (and `start.sh --fresh`):

1. **releases the planner that lives**, so the next one forks the new knowledge base rather than carrying the old;
2. **leaves the knowledge base behind** — `kb` and `kb_building` cleared, pending notes dropped with it — so
   `kb_care` builds a new one, which loads HANDOFF.md, the owner ledger and the owner's new words, and nothing any
   planner accumulated;
3. **charges the first planner** with an event from the owner (`v2.FRESH_CHARGE`): what has been produced and is not
   yet carried into HANDOFF.md; what the graph no longer needs and why (a task dropped without a reason comes back);
   and what the structure should now be, given that the planner lives across its events, that two sessions work at
   once, that a park hands the slot to anything independent, and that its status line says how many tasks could
   start at all. Only then does it queue.

The graph is **not** touched by the harness: the owner asked for the planner to discard what is useless, and that
judgement is the planner's. The charge reaches it in its first message, and a planner lost before it acts gets the
charge back with its other events.

**What a reset costs, and why it is safe here.** The old knowledge base's notes (`state/kb-1-notes.md`, 149K) are
not read by the next one; only HANDOFF.md, the ledger and the owner's words are. HANDOFF.md stands at 799 lines with
all five sections and a `## Now` current as of the last planner of the day, so the state carries. Anything wanted
from those notes must be in HANDOFF.md before the fresh start.

## The state, the log, and what DECISIONS.md takes (2026-09-20, the owner)

**HANDOFF.md accumulated and nothing pushed back.** Measured over its whole history: 51,860 → 153,947 characters on
09-19 with four condensations totalling −303 against +102,390 added; then a manual wipe to 6,486 at the v1→v2
transition; then 6,486 → 81,482 on 09-20 with two condensations of −2,792 and −2,616 against ~80,000 added. The only
real reduction in two days was done by hand. `## Decisions` is 47% of it — the section the protocol says should hold
references.

Three changes, at the owner's direction:

1. **A log of its own.** `PLANNING_LOG.md`: what was done and how — the course the work took, what was tried and
   abandoned, what a task cost — appended as work lands and never rewritten. No base holds it (`select_base_load.NEVER`),
   nothing reads it to plan from, nothing bounds it, and it is exempt from working-tree ownership like HANDOFF.md;
   only the planner may write it (`work_meter.write_guard`). It is what makes the rest possible: HANDOFF.md can stay
   a state because the log has somewhere else to be.
2. **The bound raised to 60K tokens** (`ORCH_HANDOFF_MAX`), from the 10K first set. A state may hold a great deal:
   the knowledge base carries it beside a 472K base and stays far inside its limit, and a designer reads it whole in
   a gather, which is free of the read limits. It is not a budget but the point past which it is a log — and the log
   now has its file. `v2.py status` prints the size and the largest section in every message the planner reads, and
   `health.py` raises it.
3. **What DECISIONS.md takes.** The owner: content decisions only, never task planning, scheduling or anything else
   operational. Audited: 199 entries, essentially all of them decisions of the development — notions, native
   definitions, semantics, what proofs establish. One intruder, at line 9881 ("An acceptance step's cost is within
   the machine's limit as its command is written"), about a tool's worker default against this machine's Isabelle
   limit; it is in the decisions index and so carried by the max and xhigh bases into every planner, designer, task
   designer, investigator and reviewer, and serves none of them. It was left in place — DECISIONS.md is the
   development's record and an entry is the development's to remove — and named for the first planner's taking of
   stock. The hole was closed at the cause instead: `DEVELOPMENT_WORKFLOW.md` and `protocols/_finishing.md` both said
   "its decisions" unqualified, which is how it got in, and both now say which decisions and why.

Also: `--fresh` now refuses while the orchestration is active. It begins a run; it does not rejoin one, and under a
run in progress it would take the context of whatever is deliberating with the knowledge base and planner it leaves.

### The move itself (the owner: "rename the current handoff to the log, because it is one")

`HANDOFF.md`'s 81,271 characters are now the first entry of `PLANNING_LOG.md`, kept whole and dated, under a line
saying what it was and why it moved. `HANDOFF.md` is 1,427 characters: the five sections of the planner's state, each
empty and saying what belongs in it, a header naming where each kind of thing now goes, and a `## Now` that charges
the first planner to write the state from the graph, the log, the working tree and the history.

`v2.planner_state_problems` passes on it (it requires the five headings, not their content), the status reads
`HANDOFF.md: 0K tokens of at most 60K`, and the knowledge base's own load drops by about 27K tokens — HANDOFF.md now
costs a knowledge base 479 tokens instead of 27,090, and a designer's first gather the same.

Still open, if the owner wants it: `state/kb-1-notes.md` (149K) is the knowledge base's accumulated integration
notes, which are log material too. They were left where they are — appending them unread would bury the log's first
entry — and they die with the knowledge base at the fresh start unless moved.

## The hold, 2026-09-20 — nothing starts a session by accident

Three times in one pass I started real sessions while checking the machinery: `v2.py start` (which is not a dry run:
it built a knowledge base and a reviewer), `base.sh WHO layer` piped to `head` (which rewrote the frontier and would
have loaded a layer), and a test that invoked `base.sh WHO layer` for real (which loaded two). Each of those is a
cold write of a base or a layer. The owner: never again.

`state/no-launch` is the switch. While the file exists:

- `v2.claude()` refuses any `--bg` call and logs it, so the dispatch, the watchdog and every role start nothing;
- `base.sh build`, `build-packed`, `build-files`, `layer` and `extend` refuse;
- `v2.py start` refuses and names the file;
- `health.py` says so at the top.

A **keep-warm ping goes through** (`claude(..., warm_ping=True)`, and `base.sh WHO warm` is not held): it keeps what
exists alive rather than spending anything, and holding it would let the bases go cold, which is the very cost being
guarded against.

The file holds its own reason, which every refusal quotes. It is set now, and the owner takes it off when the bases
are built and the run is to begin: `rm .claude/orchestration/state/no-launch`.

**Rule for anyone working on this machinery: a check that starts a session is not a check.** Ask the question the
command would ask — `manifest.has_layer()` rather than `base.sh WHO layer`, the status rather than `start` — and let
the tests do the same; the one that caused this ran `base.sh WHO layer` inside a unit test.

---

# Handoff, 2026-09-20 20:20 — the run is live on layered bases and one planner

Read this, then `README.md` (how it works now) and `notes/bases-design.md` sections 13–17 (the bases as they were
built). The owner's standing rules for this work are unchanged: nothing about the orchestration goes into the project
memory (notes go in `notes/`); nothing said in orchestrator sessions goes into the owner ledger; the base rebuild is
the owner's (the orchestration only tells when it is due).

## Where it stands

**The orchestration is running.** Six base parts built and sealed at 20:02–20:03, `start.sh --fresh` at 20:04.

| base | stable | with its layer | room a fork has |
|---|---:|---:|---:|
| max | 348,004 | 478,130 | 428K |
| xhigh | 274,147 | 503,712 | 403K |
| high | 274,258 | 523,233 | 383K |

`kb-3` holds the knowledge at 485,374 (its own load is ~7K now HANDOFF.md is 479 tokens). `plan-29` is the planner,
idle between its events and held warm, charged by the owner to take stock before it queues anything. Task 7 was
reviewed, accepted and committed as `44738c20` in the first ten minutes. Everything of the harness is committed and
pushed through `504cc34d`; **239 tests pass** (`python3 -m pytest -q test_*.py` in `.claude/orchestration`).

Uncommitted in the working tree: the in-flight work of tasks 22, 46, 48 and 50, which is theirs and not to be
committed on their behalf — the planner's charge is to take stock of it.

## What changed today, in one line each

- **The planner is one long-lived session.** Events reach it as they happen, each its own message; it is not a
  worker, so the rate never holds one back. Between events it is `idle`: sealed, held warm, woken by the next. It
  ends once, when its window is full, and writes then the notes the knowledge base takes up.
- **The bases are layered.** A `# === layer ===` line splits each list into a stable reference the owner builds and
  a frontier layer the harness refreshes. Every role forks the layer; a fork of a layer reads the base under it from
  cache, so one ping serves both. A refresh writes 112K–234K instead of rebuilding 473K–518K.
- **HANDOFF.md is the state, `PLANNING_LOG.md` is the log.** The old 81K HANDOFF.md is the log's first entry.
- **`ORCH_WORKERS=2`**: a reviewer or task designer runs beside the producer. One producing session at a time
  regardless — that is `produce()`, not the rate.
- Repairs: a failed resume says so; mail goes back with its senders; a standstill is named to the planner; a check
  that would leave the base in a task's directory is refused; each role is told where it really works and given only
  the protocol parts that hold for it; `state/no-launch` stops anything starting a session.

## What to watch first

1. **`plan-29`'s taking of stock.** It has the owner's charge and eleven events. Watch that it drops what the graph
   no longer needs, writes HANDOFF.md as a state, and puts what was done into `PLANNING_LOG.md`. `claude attach` it,
   or `attach.sh planner`.
2. **The layers' first refresh.** All three are 0% stale. The rule fires at 20%; watch that `base.sh WHO layer` runs
   to a seal, that the old layer is stopped and not removed, and that a session forked before it is told what changed
   against the load it actually holds.
3. **`health.py`.** It now names each layer's stale share, the trees standing, the hold, the planner between events,
   and HANDOFF.md's size.

## What is not done, and what to be careful of

- **Worktrees are off** (`ORCH_TREES=0`). A session started with its cwd in a worktree is invisible to the harness:
  `session_row.py` matches by cwd and `v2.TRANSCRIPTS` resolves through `PROJECT`, so the listing, the gauge, the
  meter, `running_jobs` and the fork check all miss it. On the first live run two sessions ran that way unseen.
  Turning them on again means making session discovery and transcript resolution follow the session, not the project.
- **`.build/trees/46` and `.build/trees/49`** still hold a minute's work from those two sessions, named by
  `health.py`. The planner has been told and it is its call.
- **A check that starts a session is not a check.** Three times in one afternoon a command run to *test* something
  started real sessions — `v2.py start` is not a dry run, `base.sh WHO layer` builds one, and a unit test that
  invokes either does too. Ask the question the command would ask (`manifest.has_layer()`, the status), and set
  `state/no-launch` while working on the machinery.
- Unsearched still: the guard's read limits and batching rules, the knowledge base's growth and condensation, the
  review protocol itself, and anything that only shows under real concurrency.

---

# 2026-09-20 20:26 — the guard was never wired to the tools that write

The owner stopped the run ("something is completely wrong; only leave the warmth daemon") while the first live run's
state was being read. What the reading had found by then is below; whether it is what the owner saw is not settled.

## The stop

`stop.sh` was **not** used: it kills the warm daemon first, and the daemon was to stay. Instead `v2.py stop` alone
(sealed `plan-29`, `implement-46.4` and `implement-22.4`; the orchestration inactive; what was interrupted recorded as
an event for the next episode), then `state/stopped` written by hand so the watchdog is inert on both of its
conditions, and `state/no-launch` set with its reason. The daemon lives (pid 2940345), all three bases warm, all three
layers 0% stale, no check running, no poly or java process left. `start.sh` resumes; `rm state/no-launch` releases.

## What was wrong

The PreToolUse matcher of `planner-settings.json` and `worker-settings.json` was
`Read|Bash|Grep|Glob|Agent|TaskOutput|TaskCreate|TaskUpdate`. **`Write`, `Edit`, `MultiEdit` and `NotebookEdit` were
not in it**, though `kind()`'s first branch is exactly those four. So `work_meter.py guard` never ran for the tool the
roles actually write with, for the whole run, and with it neither of the two things that branch does:

- `write_guard` — HANDOFF.md and `PLANNING_LOG.md` being the planner's alone, a finalization's locked files, and a
  tree another task holds — was unenforced against every Write and Edit. Only writes named inside a Bash command were
  ever guarded.
- `v2.own` recorded nothing, so the tree's ownership was built from the words of Bash commands alone.

Measured on the live state before it was repaired: `state/tree-owners.json` held **123 entries, 7 of which named
anything that exists** (four of those seven directories), and **not one named a path that had changed**. So
`tree_writer` was `None`, `tree_holder` was `None`, and `in_main_tree` was False for tasks 46, 22, 48 and 50 — the
harness believed nobody owned the uncommitted work of four tasks. That is why task 46 was handed a worktree at
20:11:56 with its work standing in the one tree, which is the incident that ended with `.build/trees/46` and
`.build/trees/49` discarded.

**Why no test saw it.** Every test calls the guard directly (`self.guard("Write", …)`), which is past the matcher that
decides whether it runs. `test_writes_to_the_working_tree_are_attributed_to_the_task` and `test_handoff_is_the_planners`
both passed throughout, testing logic that was never reached. This is the day's own class once more — a thing tested
past the gate that governs it — and it is the second time the gate itself was the fault, after `.hit` meaning
"pinged" rather than "warm".

## What was done

- The matcher in both settings files now names the four write tools first. The two files still differ in nothing but
  `CLAUDE_CODE_TASK_LIST_ID` (its test still passes).
- `work_meter.GUARDED_TOOLS` and `UNGUARDED_TOOLS` say which tools the guard acts on and which it deliberately does
  not (`ToolSearch`: matching it would change nothing). Two tests in `HookWiringTests`: the matcher of both files
  matches every guarded tool, and the tool names `kind()` and `session_guard()` themselves contain are exactly those
  two tuples — so a tool given a branch cannot be left out of the matcher again. The first fails against the old
  matcher, on `Write`, in both files.
- **`state/tree-owners.json` rebuilt** from each task's own `finalize.json` (46, 22, 50) and result (48, which has
  written none): the nine paths standing changed, the 123 old entries dropped. `tree_writer` is now 46, the other
  three serialize behind it — the designed mechanism — `in_main_tree` is True for all four, and `leave` reports what
  a task leaves. The old file is not kept; `git diff` and the tasks' records are its source.
- **Isabelle cartouches are no longer read as redirections.** `\<open>a row \<exists>q.` yielded `['a', 'q.']`:
  `ISABELLE_SYMBOL` is stripped in `shell_syntax` now, since `\<` is no shell syntax and the `>` closing one is no
  redirection. That is where 116 of the 123 entries came from — theory text reaching the parser outside a heredoc it
  could strip, an indented delimiter being enough. One test, which fails without it.
- `v2.NO_LAUNCH`'s comment said the hold stops a keep-warm ping. The code three lines below says the opposite and is
  right; the comment is corrected.
- The README's hook paragraph now states that the matcher must name every tool of `GUARDED_TOOLS`, and why.

**242 tests pass** (`python3 -m pytest -q test_*.py` here). Nothing is committed — the standing rule.

## What is not verified, and what to watch

- **The fix is verified by test and by reading, never live.** Nothing has run under the new matcher: the run is
  stopped and `no-launch` is on, and starting a session to check it would be the thing the hold exists to prevent.
  On the first restart, watch that a worker's Write of a working-tree file appears in `state/tree-owners.json` under
  its task. That single line is the whole verification.
- **Sessions already sealed keep the old settings**; a bare resume does not re-read them. `plan-29`, `kb-3` and the
  two implementers were started before the change, so the guard still will not see their writes. Only sessions
  started after it are covered — and a knowledge base is only rebuilt on its own or by `--fresh`.
- Tools reaching `kind()`'s `other` branch are still outside the matcher, so they cost no round at the moment they
  are used. This is deliberate and not the same defect: `rounds_since` counts from the transcript and not from hook
  calls, so the count is right and only the moment of enforcement moves — the next matched tool refuses on the true
  figure. Adding them would tighten the meter past what its limits were measured against, which is the owner's call.
- Unsearched still, and now with one more reason to look: every other place where a predicate is tested past the
  thing that gates it.

---

# 2026-09-20 21:00 — four things the owner named, and what the record actually showed

The owner, after the stop: the orchestrator worker's message about the worktrees never reached the planner; the
messages the planner did get may have contained false information; a fresh start should not run the old graph before
the planner activates it; and why did the notice about dead tasks come so late. The run is stopped, `no-launch` is on,
only the warm daemon runs. **250 tests pass.** Nothing is committed.

## 1. The worktree message — it did arrive, and the path it took has no guarantee

Corrected: at 20:14:59 the orchestrator worker wrote it with `v2.event(st, "the harness", "Two producing sessions
were started in working trees of their own…")`; it reached `plan-29` at 20:15:34 as a **PostToolUse hook
attachment**, and the planner acted on it — that paragraph is in HANDOFF.md and is where "Their trees are discarded"
comes from. It is invisible as a message, which is why it looked lost: it is not one of the eight `[harness] Message
from…` turns in the transcript.

It arrived by luck. `plan()` finds the planner busy, so it only `post()`s and leaves the hooks to show it; the hooks
do not run again after the turn's last tool call; the planner is then sealed, and **nothing opens that box again** —
`plan()` returns at once while no new event has come, and `care()` is reached only for `LIVE` sessions, which `idle`
is not. So a message to the planner waited for the *next* message, and with none it waited for ever. Here the next
message was the standstill a minute later.

`watchdog.planner_mail()` now wakes a sealed planner that has mail; cold, `holds()` loses it and its events go back.
Two tests, both failing without it — and the first version of them passed against the unfixed code, because a
standstill was supplying the next event: the test needs something working for the hole to show.

## 2. The messages it did get — three were false, and they were most of what it was told

`plan-29` received eight messages in its life: four prompts, then

- **the standstill (20:16:44)**, which said tasks 5, 9, 18 and 21 "came back and have not been re-planned". **All
  four were false**: 5, 9 and 18 are committed and `completed` in the graph, 21 was dropped and is not in the task
  list at all. `st["tasks"][id]["stage"]` is the harness's own bookkeeping and nothing clears it when a task finishes
  or is dropped elsewhere. `with_the_planner()` now asks the graph, and both readers use it.
- **q20 from implement-46.4 (20:20:52)** — honest: it said which tree it had run in.
- **two identical notices (20:24, 20:25)**: "The working tree is inconsistent … ROOT declares Development_Loci, which
  is not in theories/ … Every task's check refuses on this". The shared tree held the file and was consistent
  throughout (`tree_trouble()` → none, then and now). The trouble was task 46's **own worktree**, branched from a
  HEAD that declares a theory whose file is untracked. `tree_checked()` now names which tree, scopes the claim to
  that tree's own checks, and does not repeat the same trouble within `TREE_TOLD`.

And in the planner's **first message**: `startable now: 21 14`. Task 21 was not in the list, and `startable()` read
its blockers off a record that was not there — an empty list of blockers made it ready for ever. `startable()` and
`produce()` now skip a queued id with no task record.

So of everything `plan-29` was told about the state of the work, the larger part was wrong.

## 3. A fresh start no longer runs the graph it inherited

`--fresh` charged the planner to take stock and dispatched the old queue in the same breath: task 7 was started,
checked, reviewed and committed within ten minutes, before the planner had said what of the graph still stood.
`state/graph-held` now holds it: `produce()`, `support()` and `quick_fix()` start nothing while it exists — the
planner, the knowledge base and consultations are untouched, since taking stock is what the hold is for. The
planner's own order (`v2.py queue ID …`) lifts it. The status, `health.py` and the standstill all say it is held and
what lifts it, so the hold cannot be silent.

**It is set now.** This run began `--fresh` and `plan-29` was stopped while still taking stock, so the graph standing
here is the old run's and no planner has accepted it.

## 4. Why the dead-task notice came late — it did not, and that is the fault

It was not a timer. The dead-task lines exist **only** inside `standstill()`, which is suppressed while anything
works and while the planner deliberates. `plan-29` deliberated from 20:05:07 to 20:16:44, and the standstill fired in
the same second its turn ended. `deps_done()` names such a task only to a queued dependent, hourly, and only if one
exists — no queued task named 5, 9, 18 or 21, so it never fired at all (no `blocker-*` markers were written).

So with work in flight it would not have been said at all. `returned_tasks()` now names a task that has stood with
the planner for `ORCH_RETURNED_AFTER` (30 min) on its own, every dispatch, independent of whether the orchestration
has anything to do — and, through `with_the_planner()`, only when the graph agrees the task is still pending.

## What to watch

- **None of this is verified live** — the run is stopped and `no-launch` is on. On the first restart: that the
  planner is woken with what is in its box while something else works; that the graph stays held until it queues;
  that nothing says a completed task is the planner's.
- `planner_mail()` runs before `holds()` on purpose: a warm planner is woken, a cold one is lost in the same pass.
- The graph hold has no timeout by design — it ends when the planner says the order. If the planner never queues,
  the standstill names the hold every 30 minutes and the status carries it in every first message.

---

# 2026-09-20 21:15 — the warmth is the layer's, and the hold now reminds

Two questions from the owner on the state as it stands.

## Why only xhigh looked refreshed, and what is actually kept warm

Nothing was wrong. `base.sh WHO warm` forks **the layer** when there is one — "what the roles fork is what must stay
warm, and a fork of a layer reads the whole prefix under it" — so the 20:52 ping of xhigh was of layer `cc8f0c3b` at
503,712 tokens, which is the xhigh layer built at 20:02:58, not the 274K stable base. One ping keeps both alive.

The three looked different because the daemon pings a base only when its `<who>-base.hit` mark is older than
`ORCH_WARM_EVERY` (2400 s), and **a live fork's tool calls touch that mark through the gauge hook**. `plan-29` forks
max and the two implementers fork high, and they were still working at 20:24–20:25, so max and high were marked hit
then and were not due until ~21:04. xhigh had no fork after the 20:02 rebuild, aged past 2400, and was pinged at
20:51. Confirmed live at 21:14: max and high came due and `warm-high` was busy pinging.

The one defect was the label. `health.py` said "base xhigh: warm at …" of a ping that had refreshed the layer — the
same class as `.hit` meaning "pinged" rather than "warm". It now says `layer xhigh (with the base under it)` when a
layer exists, and `base xhigh` only when none does.

**Worth knowing, and not fixed here:** with the run stopped, the daemon is the only thing keeping the layers alive
and it does so on that 2400 s cycle, which is the intended behaviour. But `layers()` — the staleness refresh — runs
in the watchdog, which is inert while stopped, so a layer whose files have moved is not rebuilt until the run is
started again. That is right, and it means the first minutes after a restart may rebuild a layer.

## The graph hold now tells the planner, repeatedly, and says what lifts it

The hold ends on the planner's word alone, so it must not depend on `standstill()` — that answers a different
question and is suppressed while anything works, while the planner deliberates, and while it has events waiting. A
planner that dropped what the graph no longer needed and then forgot to give the order would have had nothing tell
it that the run was standing on its word.

Four places now carry it, and they say the same thing:

- **`protocols/planner.md`**, so it is in every planner's context from its first message: while the graph is held
  nothing of it starts, dropping does not lift it, re-planning does not lift it, the order does.
- **`FRESH_CHARGE`**, which carries the first telling on a fresh start (and sets `graph-held.told`, so the reminder
  does not also fire in the same breath).
- **`v2.status`**, which the planner reads in its first message: `THE GRAPH IS HELD: …`.
- **`held_graph()`**, a dispatch part of its own: every `ORCH_GRAPH_HELD_EVERY` (30 min) while the hold stands, as
  its own event, naming how many tasks are waiting and which, and that **dropping alone does not lift it**. It stops
  the moment the hold is lifted, and clears its marker so a later hold starts afresh.

`standstill()` also names the hold instead of telling the planner to queue what it cannot.

**251 tests pass.** The reminder's test checks all three: silent at the start (the charge has said it), silent at the
next dispatch, said again once it has stood that long, and stopped when the hold goes.

---

# 2026-09-20 21:30 — the graph was append-only by accident, and four messages told the planner otherwise

The second live run was stopped after ten minutes. It had hit a wall, and the wall was not in the work.

## What plan-30 met

At 21:15:49 it said *"I need to know whether a blocker can be removed, since TaskUpdate only adds"*, grepped `v2.py`,
was refused the body by its own read guard, and concluded *"The edges stand — a planner cannot remove a blocker with
the tools it has. I'll record that and work with it."* It was right:

- Claude Code's `TaskUpdate` offers `addBlockedBy`/`addBlocks` and no way back;
- `v2.py` exposed `queue`, `after`, `drop` — none of which touches a blocker;
- `update_task(tid, blockedBy=…)` existed and `fix_deadlock()` used it, with no route to it for the planner.

**No rationale for this was written anywhere** — not in the protocols, the README or the plan. It was not a boundary
anyone chose; it was the shape of the tool's API. And the planner already had the *more* destructive power:
`graph=True` lets it delete a task outright, so withholding the lesser one only pushed it toward deleting and
recreating, which loses a task's id and its history.

The cost was the whole point of the fresh start. The charge says *re-plan the inherited chain as work that can run
side by side*; the graph is **20 levels deep and one task wide for 14 of them**. It could not move one edge.

**Four messages told it to do what it could not**: `cmd_drop` ("re-point them"), `deps_done` twice ("re-point its
blocker"), and `standstill` — which named `v2.py after ID none`, the efficiency-fix relation, so a planner following
that advice would have changed nothing and been told nothing.

## What was done

- **`v2.py blockers ID ID…|none`** sets what a task waits on, whole, for the planner and the task designer (both
  hold `graph`). It refuses a task not in the list, a blocker not in the list, a self-wait, and a cycle — naming the
  task that already waits on this one — and says what it took out and what it added.
- The four messages now name it, and the standstill distinguishes a graph blocker from a task waiting on its fix.
- **`protocols/planner.md` and `protocols/task-designer.md` state the contract**: `addBlockedBy` only adds; set the
  whole list to take one out; the graph is yours to shape, not only to grow.

## Three more from the same ten minutes

- **`dropped nothing`** was what `cmd_drop` said when the drop had worked. It reported the *sessions* it stopped, and
  with none live that read as a refusal, followed by a sentence describing everything it had just done. It now says
  what became of the task first, and whether anything was working on it.
- **The graph tools are deferred.** `TaskCreate` and `TaskUpdate` are not loaded when a session starts; the planner
  spent a call on `ToolSearch` to reach the instrument its whole role turns on, and learned the add-only limit by
  reading the schema it fetched. Both protocols now tell it to load them in its first response.
- **A stage of `planner` that the list does not agree with now heals.** The planner completes a task in the list and
  the harness's own stage never follows, which is why tasks 5, 9 and 18 read as the planner's long after they were
  committed. `returned_tasks()` sets those to `done` each dispatch. Only `completed` is healed: a task with no record
  at all may be one a session has yet to write, and the readers already leave it out.

## Also this session

`returned_tasks()` now says when the task that came back **holds the working tree** — naming the paths and the
sessions already waiting. plan-30 dropped task 46 while `theories/Development_State_Rows.thy` stood in the tree, so
`tree_writer` still returned 46: every other producing task would have been refused the tree and parked for a task
nothing moves. That is the blocker-not-in-the-list shape over the tree, and nothing said it.

**256 tests pass.** The monitoring audit (`audit.py`, in the job's scratch) checks the harness's claims against the
graph rather than trusting them: every message *sent* to the planner, "task N is yours" against the list, "startable
now" against each task's blockers, tree claims against the tree actually named, queue phantoms, stage/list
disagreement, sessions running under a hold, unread mail, and the guard's refusals. It found nothing false in this
run.

---

# 2026-09-20 21:55 — the graph is admitted by its shape, not by a count

The owner, on why plan-30 created work that could never start: *"It added brief tasks which will never get executed
as we added a limit to the number of tasks … that is clearly flawed also because one brief can make 10s of tasks
which clearly are likely to be linearly dependent which would kill concurrency."*

## What the old limit did

`BRIEF_BACKLOG = 6` counted open build and fix tasks. Measured on the graph as it stood:

| | |
|---|---:|
| open tasks | 33 |
| width (every blocker completed — what can run) | 8 |
| depth (longest open chain) | 20 |
| build/fix open | 17 |
| build/fix that could **start** | 5 |
| slots | 2 |

Seventeen tasks that *exist* detained every brief while **five** could run, and the chain was 20 long and one task
wide for 14 of its levels. A brief is what *widens* a graph, so counting what exists suppressed the cure and measured
the symptom. The planner was given the number (`16 open of at most 6`) and it told it nothing it could act on:
"finish 11 more" is not an action when those eleven are a chain.

## The rule now, as the owner set it

**`graph_shape()`** gives width, depth and the count, over open tasks. The chain is walked over *every* open task and
counted over the kinds asked for — filtering the walk by kind cuts it at every review task and calls a chain of 19 a
chain of 3.

- **A brief is admitted while what can start is below the slots** (`GRAPH_WIDTH`, 0 = the slots), and detained once
  there is already as much independent work as there are slots to take it. `BRIEF_BACKLOG` survives only as a plain
  ceiling (60) against unbounded growth.
- **Depth has no maximum for work added at the start** of the scheduling chain — a task waiting on nothing open,
  which is what widens the graph.
- **Adding to the end is unlimited for a brief that began under `GRAPH_DEPTH`** (6). The depth is taken once, in
  `start_brief`, so a brief is never halted half-drawn.
- **A brief that began above it may not add to the end at all.** A task waiting only on the brief's own new tasks is
  *inside the group*, not the end — which is how a review task waits on the build it reviews.
- **The planner is never refused.** It may add work that runs first and re-point any edge whenever it judges what it
  planned before to be wrong.

## Rejected outright, and the planner resolves

The owner: *"The key is not to ask it to do what it does not want to do, but rather if what it needs to do is illegal
to reject it outright and ask the planner to resolve it."*

So the task designer is **not** told to re-shape. A detailing bent to satisfy the harness is worse than one that
waits, and the brief is not wrong for needing the work it needs — the graph is what has to give. `cmd_briefed`
refuses, says so plainly (*"do not re-shape the detailing to fit it, and do not split what belongs together"*), and
hands it to the planner with its tasks left standing in the list, unqueued. `protocols/task-designer.md` says the
same before it starts: brief the work as the work is.

The status carries the whole shape, so the planner reads the rule rather than a number:

    graph: 5 build and fix tasks can start, 2 slots to take them; the chain is 19 deep (at most 6 before a brief may
    add only at its start); 17 open of at most 60; no brief is detailed while there is already as much independent
    work as there are slots — one is admitted again when the slots have taken what can start, and a brief is what
    widens a graph rather than what drains it; a brief that starts now may add work that runs first and not more
    work hung off the end, and is returned to you if it does

**262 tests pass**, the three new rules checked against the unrepaired code. The old detention test now expresses the
new rule rather than the count.

## Watch on the next run

- A width rule admits briefs for ever if the graph is permanently narrow; the ceiling is what stops that, and 60 is a
  guess.
- `GRAPH_DEPTH = 6` is the number the owner had already chosen for the backlog. The live chain is 19, so every brief
  that starts now is in the add-at-the-start-only case — which is the intent, and worth seeing happen once.
- A brief rejected this way costs a whole task-designer session. That is accepted: the alternative is a contorted
  detailing.

## 2026-09-20 22:10 — detail is not a further goal

The owner, on the rule above: *"it is not right to not allow adding in the middle because adding more detail to a
task graph is fine adding further goals is not fine."*

The first cut measured the wrong thing. It flagged any new task waiting on open work that was already there, which
catches a task **spliced into** the graph exactly as it catches one **hung past** it — and splicing is what a brief
is for. A brief exists to make planned work concrete, so it necessarily writes tasks inside the span of what was
planned; a detailing bent to keep a chain short is worse than a long one.

`further_goals(bid, new)` now separates them:

- **detail** — something that was already in the graph waits on it, through the group. The plan expressed more
  finely, not reaching past where it already ended. **Admitted at any depth.**
- **a further goal** — it waits on open work already in the graph and *nothing* already there waits on it: the
  graph growing outward rather than finer. **This is what GRAPH_DEPTH bounds.**
- **the start** — waits on nothing open. Always admitted; it is what widens the graph.
- Inside the group — waiting only on the brief's own tasks or on the brief task itself — is neither: that is how a
  review task waits on the build it reviews, and how a brief's first task waits on the brief. The group is read
  whole, so a task deep inside it is still detail when anything pre-existing waits on the group at all.

Measured on a fixture: a task spliced between two existing ones → `[]`; one that runs now → `[]`; one hung past the
frontier → flagged. One tightening came with it: a blocker that is **not in the task list** is not "work already in
the graph", so it no longer makes a task read as a further goal.

**263 tests pass.** The messages, the status and both protocols now say detail and goal rather than middle and end.

**Left open:** brief 11 wrote task 32 waiting on 30, 31, 27 — work from brief 16, which brief 11's own task did not
wait on. Under this rule that is a further goal and would be refused today. It was a real finding (the seam), and by
the owner's rule it is exactly the case to refuse outright and let the planner resolve. Worth watching that the
refusal reads as a finding handed over and not as a fault.

## 2026-09-20 22:35 — the designer proposes, the planner writes

The owner: *"the brief should first consider where its generated tasks will be added and then reject further work if
it thinks that they will be added illegally. In general we should make it so that only planner can actually edit the
task graph while the task designer proposes the tasks and how to place them and the planner then decides. The limit
on depth should be 10 and the limit on the total should be unlimited."*

**`GRAPH_DEPTH` 6 → 10. `BRIEF_BACKLOG` → 0, meaning no ceiling** on the number of open tasks; the width against the
slots is the whole admission rule now, and the status says `17 open, no ceiling`.

**The task designer no longer edits the graph.** It held `graph=True` and wrote straight into the Claude Code task
list, which *is* the graph. It is now off that flag and off the shared task list with every other role that cannot
edit it (the invariant test holds). `work_meter`'s refusal names the new route.

- **`v2.py propose ID FILE`** — the designer writes each task once, in full, as JSON: a local `key`, the subject, the
  brief text, `why`, `blockedBy` (local keys or existing ids), and `feeds` — existing tasks that should wait on this
  one instead, which is how work is **spliced into** the graph rather than hung off it. The harness checks form
  (every build or fix with its review, every reference resolving) and placement, records it, and tells the planner
  what is proposed and where.
- **`v2.py accept ID`** — the planner places them. The harness allocates the ids, resolves local keys to them, wires
  `feeds`, sets the review relations, and queues them after the brief task. The designer never re-authors its text
  and the planner never re-types it.
- `cmd_briefed` is gone: with the designer unable to create a task, it was unreachable.

**The judgement moved before the writing.** The designer's message now carries `{DEPTH}`, `{GRAPH_DEPTH}`, `{WIDTH}`
and `{SLOTS}`, and its protocol says: detail is always admitted however deep the graph; what is bounded is a further
goal; if the chain is past the limit and your detailing needs one, **do not write it and do not bend the detailing to
avoid it** — say so and record your result, and it is the planner's to resolve. A proposal that needs one is refused
whole, so deciding first is what saves the work. The refusal remains as the backstop, and now costs a file rather
than a graph to unpick.

**264 tests pass.** The tests that drove `briefed` now drive the proposal; the two that only restated the depth cases
were dropped for the two that exercise the new path end to end.

**Unverified live.** Nothing has proposed or been placed. The first brief to run is the test of all of it: that its
message carries the numbers, that it judges placement before writing, that `accept` produces a graph the planner
recognises as what it asked for, and that the ids the harness allocates do not collide with Claude Code's own.

## 2026-09-20 23:00 — auditing what was just built, and what it was hiding

The owner asked for coherence and adequacy of the machinery of the last hours. Eight faults, all in work written
today, several of them the same classes this file has been recording all day.

**1. The owner's rule was implemented twice and the weaker copy was in force.** `further_goals` walked the real
graph transitively; `proposed_further_goals` took the designer's `feeds` on trust and did not close over the group's
own edges. `cmd_propose` called the second. The first was dead — and `test_detail_spliced_into_the_graph_is_not_a_
further_goal` covered the dead one and passed. A green test proving nothing about live behaviour, which is exactly
the fault of the morning's matcher. One `further_goals(group)` now serves the proposal and anything written, and the
test drives it through `propose` instead of calling the predicate.

**2. `feeds` was the whole of what made a task detail, and was unchecked.** A `feeds` naming a task that does not
exist exempted the task from the depth rule and then silently did not wire. Now checked for existence, for being
open, and for not naming a task of the same proposal.

**3. `feeds` was wired backwards.** `feeds` on a member names the existing tasks that will wait on **it**, so the
member is the one fed — I had seeded the fed set with the task it names, which made every splice read as a further
goal. The rule the owner asked for did not work at all, and only driving `propose` in the test found it.

**4. A deadlock in the width.** `graph_shape` counted a task with every blocker completed whatever its stage, so a
task that came back to the planner counted as concurrency though no slot can take it. Two of those hold the width at
the slots for ever, detaining every brief, with only the planner able to move them. `skip` now leaves them out of the
width while still walking them for the depth; the live figure fell from 5 to 3.

**5. A proposal nobody placed was chased by nothing.** Stage `proposed` is not in FINISHING, no slot takes it, its
session has ended. `proposals_waiting()` names it to the planner every `RETURNED_AFTER`, and `health.py` shows it.

**6. `cmd_accept` trusted the file and the graph.** It now refuses a proposal it cannot read and re-checks form
against the graph as it stands, which may have moved since the brief proposed.

**7. A proposal key could shadow a task id**, so nothing could say which one a `blockedBy` meant. Refused.

**8. The planner was never told how to place a proposal.** The event named `v2.py accept`; its protocol did not.
It does now, with what `accept` does and what to do if the placement is wrong.

And one self-inflicted: a range delete meant to remove the duplicate rule took `create_task` and `proposal_problems`
with it. `import v2` still succeeded — they are only resolved at call time — and the suite caught it.

**267 tests pass.**

## 2026-09-20 22:30 — the third fresh start, and two false things it was still being told

`start.sh --fresh`: kb-4 released, **kb-5** at 492,851 tokens, **plan-31** forked from it, graph held, nothing of the
old queue started. Three of the day's repairs proved themselves in the first second of the dispatch:

    22:26:23 the stage of 18, 5, 9 followed the task list: they are completed
    22:26:23 task 22 has stood with the planner for 77 min
    22:26:23 task 46 has stood with the planner for 71 min; it holds the working tree

The stale stages healed, so the new planner is not told to re-plan three committed tasks; the two dropped tasks were
named; and the tree-holding notice fired, which is the deadlock found while monitoring the second run.

Its first message (43,207 characters) carries the shape line, `v2.py accept`, `v2.py blockers`, the hold, and the
detail-versus-goal rule.

**But the audit of what it was told found two things wrong, both from events carried across runs.**

- **Two false notices, still being delivered.** The events of 20:24:21 and 20:25:41 — *"The working tree is
  inconsistent … Every task's check refuses on this"* — were false about the shared tree when written (the trouble
  was `.build/trees/46`) and are false now. `tree_checked` was repaired hours ago, but the events already in the
  queue are re-delivered to every new planner, unhandled, for ever. plan-31 read them as its first two messages.
- **The fresh charge twice**, for two different runs: the 21:08:54 one that plan-30 never handled, and this run's at
  22:26:21. Identical text, two copies.

`fresh_sweep` now drops, at a fresh start only, the events that start supersedes: a prior fresh charge, and a
tree-trouble notice whose tree is no longer in trouble (`event(..., kind=...)` carries the class and the tree).
Nothing else is touched — what the planner has not handled it still needs. One test, checked against the unrepaired
code.

**plan-31 was sent a correction** naming both notices, saying what was actually inconsistent and that the shared tree
needs no repair. It is live and has read them, so the harness's repair alone would have left it acting on a false
premise.

**267 tests pass.** Still unexercised: `propose` → `accept`. Briefs are detained (width 3, 2 slots), so the first one
may not run for a while, and the id-allocation question stands until it does.

---

# 2026-09-20 22:50 — the loop that could not be stopped, and its root

The owner: *"It was looping not allowed to be stopped."* The session wrote the whole account itself, in
`.build/trees/49/.build/tasks/49/obstruction.md`, and it is one fault with three faces.

## What happened

`fix-49.2` was started on task 49 and **captured into `.build/trees/49`** — a worktree left behind by the aborted
first run of the day. `worktree_of()` read the directory alone and never consulted `TREES`, so with worktrees turned
off a stale directory still took the session. `tree_text`, which does consult `TREES`, told it in the same message
that it worked in the one tree.

**A worktree is a checkout of the repository, so it carries its own `.claude/orchestration` — and `state/` is
gitignored.** The session therefore ran a *parallel harness against a parallel state*: `.build/trees/49/.claude/
orchestration/state/v2.json` exists, holds task 49 with its own `stage`, `spec_errors` and `fix_text`, and has no
sessions at all. Everything it did — `finalize`, `result`, its commit message — went there.

The real harness saw none of it. No `result of task 49` line was ever logged. The watchdog found the session
unlisted (`session_row` matches by cwd) and declared it gone, handing task 49 back to the planner while the session
was alive and working.

And it could not end. `v2.py result 49` answered *"recorded. End your turn now."*; the Stop hook blocked the turn,
because `may_end` returns False for a producing role unless the session record says otherwise — and the record
saying so was in the other state. `ask`, `escalate` and `park` each refuse a session the harness treats as closed.
It recorded its result twice, at 22:41 and 22:47, and was blocked each time.

**The two notices telling the planner "the working tree is inconsistent" came from the same root**: `finalize.py`
reads `tree_trouble(worktree_of(tid))`, so it inspected `.build/trees/46`, which lacks the untracked theories. It
also **runs the check and makes the commit** in `worktree_of(tid)` — so a task would have been checked and committed
from a stale branch. I had patched that message to name its tree; the cause was one function below.

## Fixed

- **`worktree_of` respects `TREES`.** A tree left on disk cannot capture its task while worktrees are off.
- **`_one_tree()` resolves `PROJECT` and `STATE` to the main worktree** even when the harness copy sits inside a
  linked one — a worktree's `.git` is a file naming the real one, so it costs a stat, not a git call. A captured
  session now acts on the one state whatever else goes wrong.
- **`may_end` takes the task's stage as a second witness**: once the harness has taken the work on (checking,
  reviewing, committing, done, planner) the session may end, so the way out does not rest on one piece of
  bookkeeping.

Three tests, each checked against the unrepaired code. **273 pass.**

## And a false alarm I should own

I stopped the run believing the dispatch could start a task the planner had completed. It cannot: `task_state()`
already sets a queued task's stage to `done` from the list before `produce()` reads it, and an unqueued task is never
read at all. I proved it by running the unrepaired code — the completed task was not dispatched. What my change does
add is real but smaller: `reconcile_stages` covers *unqueued* tasks, which is why 48 and 50 showed stale in the
audit, and it names a completed task that is still running, which `task_state` does not.

---

# 2026-09-21 00:30 — the loop's root, and a day's worth of what it was hiding

Working through every facet with the run stopped. What follows is what was found, in the order it was found.

## The loop the owner saw

`fix-49.2` was captured into `.build/trees/49` because `worktree_of()` read the directory alone and never consulted
`TREES`. **Correction to what this note first said:** I wrote that `tree_text` had told it, in the same message, that
it worked in the one tree, and that the two disagreed. They did not. `tree_text` keys off the same directory and
never consulted `TREES` either, so the session was told it had a tree of its own and was started in one — consistent,
and both wrong. My reading came from calling `tree_text` with a session record where it wants a task id, so the path
did not exist and it fell to the other branch. Both now consult `TREES`. A worktree carries its own `.claude/orchestration`, and `state/` is gitignored, so it ran **a parallel
harness against a parallel state**. The real harness saw nothing of its finalize or its result, declared it gone,
handed task 49 back to the planner — and it sat blocked by the worktree's own stop hook, recording its result twice
and never able to end. Its own `obstruction.md` records the loop. The same root produced the two false "the working
tree is inconsistent" notices, and would have made `finalize.py` **check and commit from a stale branch**.

Three repairs: `worktree_of` respects `TREES`; `_one_tree()` resolves `PROJECT` and `STATE` to the main worktree even
from a copy inside a linked one; `may_end` takes the task's stage as a second witness so the way out never rests on
one piece of bookkeeping.

## What else was wrong

- **The task designer could not produce at all.** Taking its graph rights away left its production defined as
  TaskCreate/TaskUpdate, which are refused to it, and a proposal is JSON, which `PRODUCED` excludes. It would have
  been cut off after three requests with its proposal unwritten. Its deliverable is the proposal, named.
- **`ctx_gauge`'s end-of-window instruction told it to run `v2.py briefed`**, gone — at the one moment a session
  cannot afford a refusal. A test now asserts no message anywhere names a command that is not one.
- **`task-designer.md` told it to run `v2.py blockers`**, which its own lost graph rights refuse. A test asserts a
  role without graph rights is never told to run a graph command.
- **Task ids were allocated above the files and not above `.highwatermark`**, which Claude Code allocates from — the
  mark stood at 51 with task 52 written, so the next id would have been handed out twice and a task overwritten.
- **`cmd_accept` was not atomic**: a failure part way left tasks with no edges, and placing again would write every
  one a second time. It takes back what it wrote.
- **A brief whose form is wrong was told once and never again**, and the standstill does not list an unformed task.
- **A review whose subject finished without being reviewed can never start** — `pending_reviews` only offers one
  whose subject is `reviewing`. Tasks 23 and 47 stand exactly so in the live graph, reviews of 22 and 46 which the
  planner completed on taking stock, and a ready task with no open blocker is not in the standstill either.
- `fill_pending_commit` joined `tree` into a path one line before defaulting it.
- The two false tree notices were still being delivered to every new planner; `fresh_sweep` drops a superseded
  charge and a tree-trouble notice whose tree is clean.

The three conditions only the planner can clear — a task given back, a proposal not placed, a brief not in form —
became one notice on one period, and the orphaned review is the fourth.

## Searched and found sound

`state()` is an exclusive flock around read-modify-write, writing nothing on an exception. The knowledge base bounds
its load, its integration, its growth and a rebase, and puts its notes back when a resume fails. The finalizer waits
for another task's append and then refuses rather than carrying it. propose → accept was driven against a sandboxed
copy of the real 29-task graph: refusal for a further goal, admission when spliced, ids above the mark, local keys
resolved, `feeds` wired. The whole-run walk now carries a brief through propose and accept.

**279 tests pass.** The one dispatch fault the run was stopped for does not exist: `task_state` already healed a
queued task's stage before `produce()` read it, proven by running the unrepaired code.

## Where the state stands

Stopped, daemon down, `no-launch` set. `.build/trees/46` and `/49` are gone and fix-49.2's stranded deliverable is
back in the one tree, owned by task 49 — which therefore **holds the working tree while being with the planner**, so
the first producing session after a restart parks until the planner deals with it. It is named after thirty minutes.
Task 52 stands `unformed`; 23 and 47 are the orphaned reviews.

## 2026-09-21 01:00 — what the stop found, and how it was found

Continuing with the run stopped. Beyond the worktree root cause above:

**Silent wrong answers.** Twenty-four handlers return an empty value on error; twenty are honest, because an absent
file means nothing. Four were not, and each reads as "nothing to do":

- `git_out` returned `None` on failure and `changed_paths` turned that into "no paths" — a clean tree, from which
  `tree_writer` finds no owner and `leave()` tells a task nothing about the work it is leaving. One git error away.
- **`work_meter`'s guard catches every exception and lets the call through**, which is right, and did it in silence,
  which is not: a crashing guard is every read limit, every refusal and the write guard switched off with nothing to
  show for it — the PreToolUse matcher's fault in another form. Said now, at most once every `ORCH_GUARD_QUIET`,
  because it runs on every tool call of every session.
- `rounds_since` returned 0 when a transcript could not be read, so nothing counted and the limits never bit.
- `stale_share` returned 0.0 when the measurement failed, so a wholly stale layer reads as 0% and is never
  refreshed.

**Dead code.** Three functions were defined and named nowhere — the fault that had the detail-versus-goal rule
written twice with the dead copy under test. `trees_tidied` sweeps a worktree holding nothing and was never called
from the sweep it was written for. `path_like` was written to keep prose out of the write targets and never wired:
wiring it drops `ROOT` and every file not yet made, so it is removed and `write_targets` says where the protection
actually lives. `kb_context` named nothing. No function in the harness is now defined and never named, and no
constant either.

**The mutation check.** Every repair of today was verified by hand as it was written, but a later edit can make a
test pass for the wrong reason. Twenty-one mutations, one per repair, each run against the test meant to catch it:
three were missed. One was the harness's own `-k` filter. Two were real — nothing tested that `v2.py blockers`
refuses a role without graph rights, and `graph_shape`'s `skip`, the fix for the width deadlock, had no test at all.
A fourth exposed a branch nothing could reach: the orphaned-review condition read both the stage and the list, and
`reconcile_stages` runs first and guarantees the stage. All twenty-one are caught now, in one run, with the working
tree clean afterwards.

**The methods that kept working**, for whoever comes next:

1. *Do the pair that must agree, agree?* `worktree_of` and `tree_text` both decided whether a task has its own tree,
   from the directory alone; repairing one left them contradicting each other. `startable` named what `produce`
   would refuse. `task_state` and `reconcile_stages` hold one rule at two scopes.
2. *What would a restart actually do?* Asking it of the live graph found the two orphaned reviews, which no stage,
   no blocker and no standstill would ever have named.
3. *Break it and see whether a test notices.* Three of today's repairs were not held by anything.
4. *Is this code reached at all?* Twice today the answer was no, and both times a green test covered it.

**283 tests pass.**

## 2026-09-21 01:30 — where it stands, and what a restart meets

**285 tests pass.** Everything of the harness is committed and pushed.

Found after the section above, all by asking whether two readings of one thing agree:

- **The status, the roles' messages and the depth rule read three different figures.** The status showed the build
  and fix depth (10) while `start_brief` records and `cmd_propose` compares the *whole* graph's (11), so the planner
  was told a brief could still add a further goal while the rule would have refused it; and the task designer was
  told a width of 2 against the status's 1, its message not skipping what no slot can take. `graph_figures()` is the
  one definition now, and a test pins the agreement rather than the figures.
- **The depth limit refused at its own value.** `depth >= GRAPH_DEPTH` against "at most 10" everywhere in words, and
  the owner's rule is *above* the limit. The live chain stands at 10 for build and fix and 11 whole, so this was
  about to matter.
- **`startable` named the two orphaned reviews**, which `pending_reviews` will never offer: the figure the planner
  reads as its graph's width was wider than anything would take.

**The state a restart meets.** Stopped, daemon down, `no-launch` set, `state/stopped` written, nothing live. `kb-5`
sealed. The graph is **not** held — plan-31 queued before it was stopped, so a restart runs the graph it accepted.

    width 1, depth 11, limit 10, slots 2 | queue 29 | startable 14, 10, 13 (the three brief tasks)

- **Task 49 holds the working tree and is with the planner.** Its deliverable — `native_control_plan.md`, the work
  fix-49.2 did in the stale worktree — stands in the one tree, owned by it. Until the planner re-plans or finalizes
  it, the first producing session is refused the tree and parks. It is named after thirty minutes, with the paths
  and whoever waits.
- **Task 52 stands `unformed`**, and 23 and 47 are the orphaned reviews. All three are named on the same period.
- A brief would be admitted (width 1 of 2 slots) and, at depth 11 against a limit of 10, may add detail and work
  that runs first but not a further goal. That is the first live exercise of `propose` → `accept`, which has run
  only in the fake world and against a sandboxed copy of the real graph.
- The max layer is 22% stale and the xhigh 12%: both refresh on the first watchdog pass.

**A latent idiom, left alone deliberately.** Nine places read `(age_of(mark) or N + 1) > N`. An age of exactly `0.0`
is falsy, so a marker written in the same instant reads as never written and the notice repeats. The probability is
effectively nil and touching nine call sites to chase it is more risk than the fault; `tree_checked` uses the
explicit form and the rest do not, which is the one inconsistency knowingly left in place.

## 2026-09-21, after the stop: what a second sweep found

The run is still stopped and `no-launch` still set; nothing here started a session. The method was the one that had
been productive: take a pair that must agree and check that it does, ask what a restart would actually do, break a
repair and see whether a test notices, and read every statement the harness makes as a claim that can be false.

**What the owner reads.** `health.py` returned after "stopped at …", so the queue, the parked tasks, the proposals
nobody placed and the reviews left orphaned — the state a restart meets — were visible nowhere while the run stood
still. That block is `standing()` now and prints for a stopped and an inactive run too. Reading it found three
statements of its own that could not be checked: "layer max: warm at 21:59:00" read at 01:17 (it says how long ago
and that the entry has expired since), "— it is refreshed" of a stale layer (the watchdog does nothing while the run
is stopped or its daemon is down, so it names what will do it, or that nothing will), and "daemon: alive", which
rested on the pid alone — a daemon that dies without clearing `warm.pid` leaves a number the system hands to
something else, and `warm_daemon.sh --ensure` read it the same way, so one stale number would have stopped the
keep-warm pings for good while the report called them alive.

**Figures and rules that did not match.** The width counted every open build or fix task whose blockers were done,
including work already in flight and work only the planner can move: it told the planner "1 build and fix tasks can
start" of task 52, whose brief is not in form and which nothing can start at all. The rule the planner and the task
designer are given — "a brief is admitted again when the slots have taken what can start" — could not be satisfied
under that count, because the figure only fell when a task *finished*. The suite passed either way: no test made a
slot take work and then read the figure. One does now.

**Messages that were true of an older design.** `planner.md` said a refused proposal comes back "its tasks left
standing and unqueued" and `task-designer.md` that "what you wrote stands in the list" — both from before
propose/accept, when the designer wrote tasks itself. The held-graph notice said "Two things end it, and only you
can do either" and then that one of the two does not end it. The README's roles table said a designer forks the
knowledge base at max while `ROLES` has it fork the middle base — its own prose two pages down said the middle base.

**Turns that could not end.** The Stop hook told every blocked session that its turn ends "while you wait on a
question of your own"; for a producing session `may_end` frees the turn for a park and for nothing else, so a
session that asked its question and tried to end was blocked with no move it believed in. The watchdog's message to
a stalled session carried the same sentence. Both are role-aware now, and a turn blocked twelve times in a row
without an end in between is named in the log — the hard mark is the backstop, a whole window of requests away, and
a session that calls no tool between turns never reaches it at all.

**Refusals at the moment the way out was needed.** `OWN` matched only `.claude/orchestration/v2.py`, while the
protocols give `v2.py park run` as well: the short form counted as reading, so `park`, `ask` and `result` were
refused once a session's budget was spent — the three commands that end a turn, refused while the Stop hook was
telling it to run them. It is the command position that decides now, so a mention in `grep v2.py HANDOFF.md` still
reads. `session-flags` gives every session WebFetch and WebSearch and neither was in the guard's matcher: a read
that never reached the meter cost nothing against the budget every other read is held to.

**Silence where there was a fault.** `read_task` turned any `OSError` into "the task is not in the list", which
every caller reads as the planner having taken it out — including the conflict notice added the same day. `state()`
and `owners()` turned any read failure into `{}` and wrote it back, which would have replaced the sessions, tasks
and queue, or the working tree's ownership, with emptiness under the lock meant to protect them. A file that is not
there is still `{}`; one that is there and cannot be read raises, and nothing writes over it. A resume that fails
puts a session's mail back in its box and nothing tries again: eight boxes stood unread from 2026-09-20, two of them
the planner's corrections to fix-48 about the order of the working tree, and `release()` now names what is left.

**Work the graph calls done that the repository does not hold.** A path belongs to the task that wrote it until its
finalizer commits it. Every uncommitted path in the working tree belongs to a task the planner completed — the
theories of 22 and 46, the tools of 48 and 50 — and nothing named it. health.py says it.

**What was checked and found sound.** Seven older repairs (own_task's refusal, the placeholder and foreign-work
refusals in the finalizer, HANDOFF.md's owner, a blocker not in the list, both parks) were each broken in turn
against the whole suite: every one was caught. No function and no constant in any harness file is unreferenced; no
state key is written and never read. The 34 mutation cases in `notes/mutation-check.py` all fail their tests.

**Left alone, knowingly.** `session-flags` gives every session the Agent tool, which `session_guard` denies outright:
the flags are part of the cached prefix, so taking it out costs a rebuild of every base, and the denial is correct
and told. `.build` holds 26G, 18 check directories of it; the repository retires temporary storage through
`tools/retire_temporary_storage.py`, which is the owner's and declaration-driven, and 1TB is free. The nine
`(age_of(mark) or N + 1) > N` call sites stand as before.

### The same sweep, continued

**Files the harness keeps, read as empty when they could not be read.** `state()` and `owners()` each turned any
read failure into `{}` and wrote it back under the lock that was meant to protect them — the sessions, the tasks and
the queue, or which task owns every change in the working tree. The owner ledger did the same with a fresh header:
every direction the owner has ever given, replaced by the one entry being written. A file that is not there is still
empty, which is how a run begins; one that is there and cannot be read now raises, or is left alone with its words
kept in the log. The two holds (`no-launch`, `graph-held`) had the mirror fault: they read a failure as "no such
file" and so as "nothing is held", which is the one thing the owner's own switch exists to prevent.

**Turns and budgets.** `OWN` matched only the long form of the harness's own commands, so a session that wrote
`v2.py park run` had `park`, `ask` and `result` counted as reading and refused once its budget was spent — the three
commands that end a turn, refused while the Stop hook told it to run them. The Stop hook and the watchdog both told
a producing session its turn ends "while you wait on a question of your own", which `may_end` frees only for the
supporting roles. A turn blocked twelve times in a row is now named in the log.

**What a run leaves.** A resume that fails puts a session's mail back in its box and nothing tries again: eight
boxes stood unread from 2026-09-20. `release()` names what is left, once, where the box is emptied. A session
stopped by the account's usage limit keeps its mail rather than spending its resume on a turn that hits the limit
again. Every uncommitted path in the working tree belongs to a task the planner completed — work the graph calls
done that the repository does not hold — which health.py now says.

**The queue as the planner's word.** `done` is terminal bookkeeping that `task_state` never re-reads, so that a task
its review accepted is not started twice in the window before the planner completes it in the list. A task the
planner puts back to pending and then names in its order is one it means to run, and nothing would ever start it:
`v2.py queue` reads such a task afresh, and only when the list no longer calls it completed.

**Measured rather than guessed.** A coverage run that follows the subprocesses the tests actually run (they are
nearly all subprocesses: a plain run reads 30%, this one 84%, `v2.py` 89%) named three live paths no test entered —
a gather over a finished task's artifacts, `talk.sh`'s join of a live planner, and health's line on each live
session — and the finalizer's refusal to run a check while the tree refuses every check. All four are held now. What
else it names is the shelf machinery, inert since 2026-09-20, and error branches of the base tools.

    COVERAGE_PROCESS_START=<rc> PYTHONPATH=<dir with sitecustomize calling coverage.process_startup()> \
      python3 -m coverage run --rcfile=<rc> -m pytest -q test_*.py && python3 -m coverage combine --rcfile=<rc>

**Reading the record.** Running a whole task from queue to commit in the fake world, and a failing check to its
quick fix, and a rejection to a second rejection, and `--fresh` against a graph shaped like the live one, and then
reading the log and every message as the owner would: the loop is coherent, and it caught one notice crying wolf
(a transcript not yet written read as one that could not be read) and one that contradicted another (a lost
session's mail said to be kept where the release had just emptied it). A walk that goes right now asserts that its
log carries no ATTENTION at all.

### What the sweep found last

**Promises kept only in part.** Placing a proposal is "all of it or none", and the tasks it wrote were taken back on
a failure — but not the edges it had already moved: a splice re-points work already in the graph onto the new task,
so an existing task was left waiting on an id that had just been deleted. It is put back now.

**What waits on the planner.** `returned_tasks` named four kinds of task only the planner can move; a fifth was
missing — a finished design or investigation waiting for the planner's own verdict, which no reviewer is ever
started for. It was said once, in the event when the work finished, and never again.

**What a role is held to and never told.** The task designer's whole production is briefs and its protocol never
stated a brief's form, nor that every build and fix needs its own review task: both are enforced by `propose`, which
refuses a proposal whole, and a refused proposal costs a session. `_checks.md` says subagents and waiting are
refused and only the roles that run checks are given it, so the planner and the task designer — the two with the
most reason to reach for a subagent, and both holding the tool — were never told. Every form the harness checks is
now asserted to stand in the protocol of whoever writes it.

**Stale by a day.** `v2.py blockers` refused every role without graph rights by naming the task designer as one that
has them, which it stopped having when it began proposing rather than writing; the usage banner offered it the same
command. A test now holds every message and protocol to `ROLES`.

**Thresholds read against each other.** The finalizer may wait an hour for the machine and run for an hour, and the
watchdog gives it 130 minutes; the soft mark is below the hard one and both below what the API has accepted; the
daemon pings at 2400 s against a 3300 s entry; `FIX_MINUTES` and the grace the watchdog allows agree. Nothing was
found out of order here.

**Left as it is, with reasons.** `unshelve`, `root_lines_back` and `cmd_unshelve` serve shelves made before
2026-09-20; every shelf under .build/tasks/*/shelf/ is already restored (`manifest.restored.json`), so the branches
are inert rather than wrong. `exclusive_claim` returns "no claim" when its file cannot be read at all: failing
closed there would stop every check for ever, and a corrupt file is cleared by the liveness rule already. A
producing session's start is not made under the state lock (the launch takes seconds, and every hook would block on
it); the window between reading a task's stage and starting its session is the one race the design accepts.

### Every door round an invariant

The harness states its rules in the messages it sends; each was read as a promise and asked what else reaches it.

- "Stop everything" was the dispatch's rule, and `v2.py talk` does not go through the dispatch: run while everything
  was stopped it would have forked the knowledge base for a planner, with the daemon down and nothing to carry it.
  Every background start reads the marker now; a keep-warm ping still goes, and start.sh takes it off first.
- "The task graph is the planner's alone to edit" was held over TaskCreate and TaskUpdate, and the list is a
  directory of JSON files a Write, an Edit or a redirection reaches as easily — past Claude Code's lock on the task
  and past the id allocation.
- `.claude/` is exempt from the working tree's ownership, so a session that edited v2.py, a protocol or the owner's
  own switches (`state/no-launch`, `state/graph-held`, `state/stopped`) would have changed the rules it runs under,
  and nothing would have recorded it.
- "A session starts no subagents" was held over the Agent tool, and `claude --bg` is the same thing by another door:
  a session outside every slot, every limit and every record. And Monitor was outside the matcher altogether — it
  is waiting, and a command under it reads a file through its events, unmetered.

`GIT_MUTATE` still misses a list-form `subprocess.run(["git", "commit", …])`: tightening it means matching words
that `shell_syntax` drops to keep prose out, and the finalizer refuses a commit that finds nothing to commit, so the
backstop is there. Left as it is, knowingly.

**Tried and backed out.** A line in the dispatch when the keep-warm daemon is gone: health.py already says it where
the owner looks, and the notice fires in every legitimate dispatch-without-a-daemon — which is what the fake world
is, and the walk that asserts a clean run leaves no ATTENTION caught it at once. The test was right and the notice
was noise.

### Against the CLI, and what reaches the knowledge base

**The listing the harness reads.** Claude Code is still 2.1.273, the version everything here was verified against,
and `claude agents --json` gives `status` (busy or idle) only while the supervisor holds a session. A row carrying
only the coarser `state` — `blocked`, a process it no longer runs — stays in the listing; one such row stands there
now, left by another project. The watchdog counted any row as seen, and `gone` is consulted only when there is no
row at all, so a session in that state would have held its slot for ever with nothing said. It is given the same
three checks and then lost. (`session_row.py` already read status-or-state, so nothing else in the listing's shape
had drifted.)

**What every knowledge base loads.** `extract_owner_directions.py --new` collects the owner's typed words since the
curated ones, and leaves out the sessions that work on the orchestration itself — which is why nothing said in this
session reaches it. Two of the eight it would have loaded were "a" and "ls": a stray keystroke and a shell command
typed into the wrong window. Out of the session it was typed in, a single short word decides nothing; the
interruption marks and the slash commands were already left out, and these join them.

**What a repeating failure costs.** The dispatch runs every minute and every start is a fork of a loaded base — the
most expensive thing the harness does. `produce()` held the producing slot to ten minutes after a start nobody
confirmed and said so to the planner; every other role had nothing, so a planner, a knowledge base, a review, a
brief or a consultation that could not be confirmed would have been forked again every minute. The floor is in
`launch()` now, keyed by what is being started rather than by what it would be called (the planner's and the
knowledge base's key is a counter that rises with each attempt), and the hold and a stop do not arm it: they refuse
a start on purpose.

Left as it is: `v2.ping` waits up to ninety turns for its throwaway fork to go idle, and several held sessions could
in principle spend the watchdog's whole 600 s budget. The daemon kills a watchdog that overruns and says so in the
log, and every ping seen in the live run returned in seconds; shortening the wait would weaken the verdict the ping
records, which is what makes a missed cache entry visible at all.

### The day's repairs read against each other

A repair can make a neighbour lie. `read_task` telling an unreadable file from a missing one was one of the day's
own fixes, and the statements built on its `None` had not moved with it: the conflict notice would have told the
planner a task was "not in the task list at all", a dependent would have been told its blocker was dropped,
`v2.py blockers` would have refused, and a whole proposal would have been refused — each of them for an I/O fault.
Where the statement is made, `in_list()` decides now. The other pairs were read and agree: `release` and `lost` name
unread mail once, between them; the stopped guard leaves the keep-warm ping alone; the new start backoff and
`produce`'s own say the same ten minutes; the width and the brief rule are one figure.

`archive()` was the one action that takes things out of the state and said nothing: "every action is a line in
state/v2.log" is the claim, and a day later a session the owner remembered was simply gone. It names what it took.

### Where it stands at the end of 2026-09-21

Nothing has been started since the owner's stop: the run is inactive, `state/stopped` is written, `no-launch` holds,
and the daemon is down. 322 tests and 51 mutations, all green, and the four flows (a task from queue to commit, a
failing check to its quick fix, a rejection to a second rejection, and `--fresh` against a graph shaped like this
one) leave no ATTENTION in their logs.

    width 0, depth 11, limit 10, slots 2 | queue 29 | startable 14, 10, 13 (the briefs) | 13 build and fix open

What a restart meets, in the order it will meet it: `kb-5` is cold, so a knowledge base is built anew (the first
cost); the graph is *not* held, so the queue the last planner gave stands, and with no build or fix able to start, a
task designer is what begins — brief 14. Task 49 is with the planner and holds the working tree (its deliverable,
`native_control_plan.md`, stands there); 52's brief is not in form; 23 and 47 are reviews of tasks already finished.
All four are named to the planner half an hour in, and the first planner sees them in the graph at once. Tasks 21
and 51 are records of tasks the planner took out of the list: inert, read by nothing, and named for what they are in
health.py. Every uncommitted path in the tree belongs to a task the planner completed — work the graph calls done
that the repository does not hold, which health.py now says and which is the owner's or the planner's to resolve.
The max layer is 22% stale and refreshes on the first watchdog pass; xhigh is at 12%, high at 0%.

**The first rehearsal of propose → accept at the live shape.** The path had run only in the fake world. Against a
copy of the graph and the state as they stand — eleven deep against a limit of ten — a proposal whose task waits on
open work that nothing waits on was refused whole, with the reason, the depth it started at and the proposal left
standing where the designer wrote it; a proposal that splices (`feeds`) was admitted, and `accept` wrote both tasks,
re-pointed the existing task onto the new one and queued them after the brief. The chain went from eleven to twelve,
which is what a splice does and what the rule admits. Nothing of the live graph was touched: the copy was made in a
temporary HOME with a temporary state and project.

**An empty order is not an order.** Running each command with no arguments to see how it answers a bad call —
against the live state, which was the mistake — showed that `v2.py queue` with nothing after it set the queue to
the empty list and answered "queued". The run's queue of 29 tasks went, and was put back exactly from the status
line, which had printed it minutes before; the command now refuses. `carried` had the same shape in a smaller way:
with no text it recorded "carried where the work reads it", losing the one thing the record exists for. The lesson
beside the repair: probe a command's argument handling in a throwaway world, never against the state a run stands
on. Every other command takes its arguments by count and prints the usage without them.

---

# 2026-09-21 — trees of their own, working again

The owner, on task 49 holding the working tree while it was with the planner: *"make worktrees work again so this
never happens"*, and nothing committed until told. The run is still stopped, `no-launch` holds, nothing was started.

## Why they had been off, and what each fault was

Trees were withdrawn after their first live run (2026-09-20). Three faults, each now repaired where it arises:

- **A session in a tree was invisible.** `claude agents` lists it under the tree's cwd, and Claude Code keeps its
  transcript under the tree's own directory (`-home-…--build-trees-46`, beside the project's). `session_row.py` matched
  the project's cwd alone and every reader of a transcript looked in the project's directory alone, so fix-49 and
  implement-46.3 ran unseen. `session_row.py` now accepts a cwd under `.build/trees/`, and `v2.transcript(sid)` /
  `v2.transcript_dirs()` serve running_jobs, context_of, the watchdog, health, the frontier refresh, the fork check,
  efficiency and the owner's words. **The fake `claude` listed every session under the project**, which is how the
  first worktree test passed while the real listing hid the session: it now lists a session where it was started.
- **A tree carried its own harness.** `_one_tree` had put the state right; the code was still the tree's copy — HEAD
  as of the tree's making, never an uncommitted change — reached by the hooks (`$CLAUDE_PROJECT_DIR` is the tree) and
  by the relative commands. `_one_harness` re-executes any harness script run from a tree's copy as the one tree's
  script, with its arguments and its unread stdin. A tree is not made from a HEAD whose copy lacks it.
- **A tree from an inconsistent HEAD refused every check.** A new tree is checked with `tree_trouble` before anyone is
  put in it, and taken away if it fails; the task then works in the one tree, told why, and the planner is told once
  per reason (`state/no-tree`, in the status and in health).

## Where a task works, decided once

`task_tree(tid)` → (tree, why), and the message is written from the same answer (`tree_text(tid, tree, why)` reads
nothing else — the text and the start parted twice on 2026-09-20). One tree when the task's own installed work stands
there, or when its brief names a path that stands uncommitted there (`in_main_tree`: task 52, whose whole work is
committing four batches installed in the one tree). A task whose blockers' work — through the tasks between — has not
landed waits for it (`landing_wait`, in `deps_done`, `startable` and the width alike), so nothing starts from a HEAD
that lacks what it stands on. `launch(tree=…)` records the tree; `tree_of(rec)` is that record, so a session is resumed
where it was started.

## What a tree changes for the rest

The one tree's holds reach nobody in a tree (`tree_holder`, `finalizing`, `check_isolation` — `finalizing` used to
hold a one-tree task behind a tree's check, and a tree task behind nothing only if both were apart). The write guard
refuses a tree session's write into the repository's own directory (the absolute paths the library holds point there;
such a write would make its task own the one tree again) and any session's write into another task's tree. `v2.py
finalize` finds the files in the task's tree and refuses a check that names the one tree's path — **the planner's
HANDOFF.md working rule pins a check to the one tree by an absolute script path**, which from a tree checks the one
tree and passes on work it never saw. The gather reads the tree the task's work stands in; a reviewer of work in a
tree is started in that tree (`{WHERE}` in its protocol). `_tree.md` keeps only what holds in any tree; the one tree's
rules (one owner, drafts, `park tree`) are said only to a session in the one tree. An empty tree is kept while its task
is under way (a parked session is resumed in it). `ORCH_TREES` now defaults to 1.

Measured, not assumed: a fork started in a tree read its whole base from cache (implement-46.3: 523,284 read, 6,106
written), and `incremental_check.py` resolves its paths, so a check in a tree records the one `.build` behind the link.

**337 tests and 73 mutations**, all green; every new repair was broken in turn and its test failed.

## What a restart meets

Nothing is committed, so HEAD's harness copy does not hand over: **no tree is made until the harness is committed**,
and every task works in the one tree with the reason said. Once committed, HEAD is still inconsistent — it declares
`Development_Loci` and `Development_State_Rows`, whose files stand untracked — so trees wait for #52 to land them.
#52 and #49 work in the one tree in any case (their briefs and their work are there), and #49's hold on it is the
planner's to end (finalize it or fold it into #52). After #52, every new producing task gets its own tree.

Not done: the planner's HANDOFF.md rule on absolute check paths is the planner's file; the next planner reads the
trees line in its status and `v2.py finalize`'s refusal names the rule, but nothing has told it yet. A merged result is
not re-checked as a whole after two trees land beside each other (only `tree_trouble` runs on it); a semantic clash
between two branches that merge cleanly as lines is caught by the next check, not at the merge.

## 2026-09-21, later — HEAD never made worse, landings checked together, and the absolute-path rule retired

The owner asked for three things: that a HEAD from which no sound tree can be made should never happen at all; that
a merged result be checked as a whole; and that the planner's rule pinning a check to the one tree by an absolute path
be resolved. Nothing committed.

**The gate.** `v2.new_trouble(tree, target="index", base="HEAD")`: `tree_trouble` of what a commit would make HEAD —
the staged index or a commit, read from git through a private index into a temporary directory (`trouble_of`, 0.3 s
for three snapshots on this repository) — less the trouble `base` already has. The finalizer refuses a commit that
adds any (both paths), and `commit_gate.py` is git's `pre-commit` and `pre-merge-commit` hook, **installed** as links
in `.git/hooks` (provisional; remove the two links to undo), so the owner's and Codex's commits meet the same
function. A fault of the gate lets a commit through and says so. The rule is "no new trouble", not "no trouble", so
while HEAD still declares Development_Loci and Development_State_Rows every commit that adds nothing goes through;
once HEAD is sound it stays sound. `commit_gate.py` was written without its executable bit first, and git skips such a
hook in silence: the test that commits through the hook caught it.

**The landing.** Every commit and landing holds `state/landing.lock`. A task in its own tree: commit on its branch
(gated), bring main into the branch (`finalize.land`); when that brought anything, the combination is gated against
main and then checked as a whole — `v2.LANDING_CHECK`, the repository's check, in the task's tree, output
`.build/tasks/ID/landing-N`, waiting for Isabelle like any check and inside the watchdog's budget — before
`merged()` moves main. A failed combination is `v2.landing_failed`: a failed check, so the task's quick fix, in the
tree that now holds both; a second goes to the planner. main is read again before the merge, so a commit made outside
the finalizer meanwhile is brought in and checked too. When nothing landed meanwhile, nothing is checked again. Cost:
one repository check per landing that meets new work (about 170–330 s), which one tree never paid and never needed.
A refinement left for later: bringing main in *before* the pre-review check would usually make that one check do.

**The rule.** `v2.one_tree_paths(text, mine)` is the one predicate: paths named by the repository's absolute path
outside `.build/`. `brief_problems` now refuses a brief that names any (the brief form in `_brief.md` says so), and
`v2.py finalize` refuses such a check for a task in its own tree. Of the open briefs only #52 names one. The next
planner is told, by an event in the queue, which three things in HANDOFF.md no longer hold and why #52 is not in form.

**345 tests and 82 mutations**, all green.

## 2026-09-21, later still — review before commit, the planner's graph edits, what a proposal tells it

The owner: review comes before commit and is to be forced; the whole tree machinery reviewed for coherence and
adequacy; nothing added at the end of a chain deeper than 10, by the planner as by a brief, and the planner not to try;
and a proposal to reach the planner as what it needs to decide, not everything. Nothing committed.

**The Isabelle base.** The machine rebooted at 09:24 and `/tmp/structural-isabelle` (the heaps and the active-context
pointer) went with it: every check would have refused "Accepted heap/database missing". Re-established the way it was
on 2026-09-19 — a complete source proof of all 1800 theories (`tools/prove_context.py`, `.build/complete-20260921a`,
13:07), `incremental_check.py adopt`, and a confirming check (`.build/check-20260921a`: all 1800 reused, every recipe
accepted, 201 tool and 35 kernel tests, 150 s) — from the one tree as it stands, the four uncommitted batches
included, as the lost base was. The heaps still live in /tmp: that is a `tools/` change and a task.

**Review before commit.** The planner had decided that a build commits and is reviewed after (HANDOFF.md "Why builds
no longer wait on reviews"), completed 22, 46, 48 and 50 in the list with their work uncommitted and unreviewed, and
planned #52 to commit all four with their reviews to run beside the next build — which could never start, since a
review starts only for a task in review. Now: the planner cannot complete a build, fix or review by TaskUpdate
(`work_meter.graph_edit_refusal`); the finalizer refuses a commit carrying work no review has accepted, the task's own
or another's (`finalize.unreviewed_work`, `v2.review_accepted`); and a build or fix the list calls completed whose work
has not landed is taken back at the step it is owed (`v2.reopen_unlanded`, first in `reconcile_stages`): its check
when it has a final job and no accepted review, its commit when its review accepted it, the planner otherwise. A check
run again gets a fresh `--output` (`finalize.fresh_output`), since the tool refuses one that exists and 22's and 50's
do — otherwise each would have cost a fixer session to rename a directory. At the next start 22, 46 and 50 go through
check, review (#23, #47, and the harness's own for 50) and commit; 48, partial and without a final job, goes to the
planner.

**A fault found on the way.** `cmd_result` set a brief with no final job to `reviewing`, which is no stage of a brief,
and `accept` reads `proposed`: every proposal whose designer then recorded its result — which it is told to — became
unplaceable, and its reminder silent. Both proposal tests went from propose straight to accept. A brief now keeps its
stage through its result, and one that ends without proposing goes to the planner.

**The depth rule, for the planner too.** `v2.goal_refusal(tid, blocked_by, waiters)` — the brief's `further_goals`,
with the graph's depth — is applied to the planner's TaskUpdate (`addBlockedBy`, and `addBlocks`, which can hang the
other task) and to `v2.py blockers`. A task that already waits on open work is being re-shaped, not added, and stays
the planner's to move. The planner protocol says the rule first and the refusal is the backstop; the status says
when the chain is above the limit. Measured on the graph's longest chain, as the brief's rule was built: whether the
owner means that, or the chain the new task would extend, is asked.

**What a proposal tells the planner.** It was told keys and edges and to read the proposal file — every task's full
brief, into the one context that lives across the run. `v2.proposal_text` gives each task's kind, subject, size and
why, what it waits on and is spliced before, whether it runs first, is detail, sits inside the brief or is a further
goal, and the chain's depth before and after (`graph_shape(tasks=…)` measures the graph the proposal would make).
`v2.py proposal ID KEY` prints one brief when a decision turns on it.

**The tree review.** Walking a tree task from queue to landing, drop and restart, three faults: a session could edit
its tree's copy of the harness, whose hooks it runs (now refused like the main copy); `git worktree add -B` would
reset a branch holding commits a failed landing left (now named, and no tree made); and a landing could merge into
main's working files under a running check of a task in the one tree (such checks now hold the landing lock shared,
landings exclusive). The finalizer's reports — which dispatch — are made after it lets main go, not while holding it:
in the test world, where a dispatch runs inline, the first version deadlocked on its own lock.

## 2026-09-21, the owner's answers — per-chain depth, repair of the whole graph, every command batchable

**Per chain.** "Add to the end of a task chain if it is above 10" is per chain (the owner). `chain_depths(tasks)` is
the longest open chain ending at each task; `past_the_limit(group, after)` names the tasks of a group that are not
spliced in, not reviews, and would hang after a chain deeper than GRAPH_DEPTH — measured on the graph as the change
would leave it (`graph_after` for a proposal), so a brief's own tasks count and a splice made by re-pointing in the
same edit counts as detail. One rule for the brief (`cmd_propose`, and `accept` re-checks), the planner's TaskUpdate,
`v2.py blockers` and `v2.py edit`. `depth_at_start` is gone: the graph's longest chain at a brief's start refused a
goal at the end of a chain of one while another was eleven deep. The status names the tasks past the limit and the
graph text gives each task its chain.

**Repair.** The planner protocol now says that what it planned before does not bind it: rewrite, re-point, take a
dependency out, delete — and deleting wrong work gives back the room it took. None of it is refused for depth (tested
at every door). A deletion leaving something waiting on the deleted task is refused whole.

**Batching.** Every command takes groups separated by a bare `--` (`run_command` is one command's single form;
`main` splits); `drop`, `accept`, `proposal`, `tell ID... TEXT` take several ids. `v2.py edit FILE` is the planner's
batched graph edit (create, rewrite, blockers, delete, queue), judged whole by `graph_edit_problems` and written by
`apply_graph_edit`, which keeps every file it touches and puts it back on a failure; `accept` is rebuilt on it. The
gather reads `task:ID` and `proposal:ID[:KEY]`. `_production.md` tells every session to batch what it does, several
writes or edits in one Bash call included. Claude Code's own TaskCreate/TaskUpdate still take one change a call; the
edit is the batched door.

**Found on the way.** A review task the planner wrote itself was never linked to what it reviews — only `accept`
wrote the relation — so the harness would have planned its own review and the planner's stood ready for ever.
`link_reviews` links every review task from its `Reviews:` line at each dispatch.

**Walked end to end** in the fake world, each leaving no ATTENTION: a task in its own tree from queue to landing on
work that landed beside it (forked and seen in its tree, checked and reviewed there, main brought in and checked
with it, merged, pushed, tree gone); and a build completed without landing, taken back through its check and its own
review task to its commit.

**What the mutation check found in this round's own work.** Four of its misses were real: the review-linking test
passed by another route (`v2.py edit` links reviews itself, so the dispatch's call was never exercised; the test now
writes the review task as TaskCreate would and dispatches); the `feeds` seed in `spliced` had become redundant once
the rule read the edited graph, and redundant code cannot be held by a test (removed, with `further_goals`, the second
reading of detail — `spliced(group, after)` is the only one); a case I wrote put a NUL byte into v2.py, so the import
broke and pytest reported errors, which the check read as a miss (the check now says BROKEN for that); and the check
itself was unreliable: Python's bytecode cache is keyed by a source file's modified second and size, the check rewrites
the same files several times a second, and a mutation caught alone read as missed in the full run. It now runs with no
bytecode and clears the cache before each case. Five cases named code this round replaced and were re-anchored or
removed.

**And one more of the same family.** The planner's reading budget is restored by production, and its production was
TaskCreate and TaskUpdate: the harness's own graph commands — `edit`, `blockers`, `queue`, `drop`, `accept` — are
harness commands and counted as nothing, so the batched path spent the budget a change a call would have given back.
`work_meter.graph_edited` counts them, unless every answer of the call is a refusal.

**A correction.** I reported that `cp`, `mv`, `rm`, `mkdir` and the like were classified as reading and went past
the write guard. They were not: `WRITE_SHELL` already matched them at the head of a command, on a second line of the
pattern I had not read. The check I added to `kind()` duplicated it and is taken out; the pattern now takes its list
from `FILE_WRITERS`, the one `write_targets` uses, so the two cannot drift.


## 2026-09-21, reading in batches and bytes, in two tiers

The owner: a batch — one request — is one read, since that is the point of batching; a batch reads at most 30K bytes
and each read in it at most 3K, so that a large chunk is read deliberately in pieces rather than taken whole by
accident; three reads a production, then a reserve of ten that each production gives one back to; and above all that
it counts right, since a session starved of reading works blind. I got the rule wrong twice on the way — counting each
call, then capping the number of reads in a batch — and the owner corrected both: what is bounded is bytes.

**What the review of the existing limit found, and what was done.** Rounds were every request since the last
production — a gather, a question, a park, a write too small to be production, a refused read — so they now count
batches that read (`reading_requests`, from the transcript, a refused call excluded by the id the guard remembers). A
session in its own tree was never credited for what it wrote there: production was measured on the deliverables joined
to the one tree, so after three reads it was refused everything, its step's gather included (`brief_of` gives the
session's tree). The gauge swallowed a failure of the meter's record without a word (now said). The meter's state had no
lock, and parallel calls wrote over each other (`meter()`). A planned input named with its lines never matched its read.
A reserve written under a larger setting was used as it stood (`reserve_of` clamps it). What a call showed was measured
as its JSON (newlines twice), and only calls classed as reads were charged tokens (`shown_bytes`, every reading call).
The harness's own reading commands (`v2.py proposal`, `graph`, `status`, `who`) counted as nothing and were never cut:
`v2.py proposal` printed every brief asked for at once. They are reads now.

**How the bounds are held.** A read's size is known before it runs only for a file's lines; those over 3K are refused
with the lines that fit named. The rest are rewritten through `cut.py` with a PreToolUse `updatedInput` — documented in
this Claude Code (2.1.273) as a PreToolUse output, checked against the tool's schema, and under auto mode a hook's allow
still goes to the classifier, so the rewritten command is judged as any is. **This has not run live** (the hold is on):
the meter says ATTENTION the first time a cut read comes back longer than a read shows, which is the one line to watch.
A batch's bytes are added from what each read showed (`st["batches"]`, by the request's message id, found in the
transcript: a request's calls are written as they are made and run as each is complete, measured in this session's
own transcript), and its further reads are refused once it has read 30K; the read that crosses still runs, so a batch
overshoots by at most one read. A call the guard cannot place in the transcript within `BATCH_WAIT` is taken for a
batch of its own: it refuses nothing it cannot place. A gather cuts each source at 3K, itself at 30K (`GATHER_CHARS`
is `BATCH_BYTES`), and counts as one read, never refused. A check's output is not cut — a check is a run — and it is
charged tokens up to `SHOWN` (30,000, the owner's figure), which is what spends the first tier's 20K now.

**A correction.** I reported that `cp`, `mv`, `rm`, `mkdir` were classed as reading and passed the write guard; the
second line of `WRITE_SHELL` already made them writes. My duplicate is gone and the pattern takes `FILE_WRITERS`.

---

# Handoff, 2026-09-21 ~13:00 — where this session stops

Stopped at the owner's word, mid-change. **Nothing is committed** (the owner: commit nothing before told). The run is
stopped, `state/no-launch` holds, the keep-warm daemon is down, nothing was started. **398 of 400 tests pass**; the two
failures are the half-finished change below, not a regression elsewhere.

## Done in this session (all tested; mutation check 133/133 at its last full run, before the unfinished change)

In order, each section above has the detail:
1. Worktrees working again (listing, transcripts, one harness via `_one_harness`, sound trees only, where a task works,
   landing waits, holds, write guard, finalize, gather, reviewer in the tree).
2. HEAD never made worse (`new_trouble`: finalizer, and git's `pre-commit`/`pre-merge-commit` hooks **installed** as
   links in `.git/hooks` to `commit_gate.py` — remove the two links to undo), landings serialized and re-checked.
3. Review before commit forced (`graph_edit_refusal`, `unreviewed_work`, `reopen_unlanded` — 22, 46, 50 go back
   through check, review, commit at the next dispatch; 48 to the planner).
4. Per-chain depth for briefs and the planner; repair of the whole graph never refused; `v2.py edit FILE` (batched,
   all-or-nothing, `accept` built on it); every command batchable (`--` groups); gather reads `task:`/`proposal:`;
   `link_reviews`; a brief's result no longer makes its proposal unplaceable; the planner told what placing needs.
5. The Isabelle base re-established after the 09:24 reboot (`.build/complete-20260921a`, adopted, confirmed by
   `.build/check-20260921a`). Its heaps are still in /tmp: a `tools/` change and a task.
6. Reading: a batch (one request, or one gather) is one read; a batch reads at most 30K bytes (`BATCH_BYTES`), each read
   in it at most 3K (`READ_BYTES`: a known-size file read over it refused with the lines that fit; an unknown-size read
   cut by `cut.py` through the guard's PreToolUse `updatedInput` — **unverified live**, the meter says ATTENTION if a cut
   did not take); two tiers (3 reads or 20K tokens per production, then a reserve of 10, one back per production);
   the faults of the old limit fixed (tree sessions never credited, every request counted, refused reads charged, no
   lock, silent record failures, and the rest listed above). `SHOWN` is 30,000 again (the owner's figure).
7. The next planner has one event waiting (the planning changes and the base); `notes/worklist-2026-09-21.md` is the
   owner-requested work list, all checked.

## Unfinished then, finished since (see the next section): reads of lines already in context are filtered, not refused

The owner: when a read overlaps what is already in context, filter it and give the rest with a note of what was left
out, rather than refuse it. Written, **not yet tested or mutation-checked**:
- `lines.py FILE A-B[,C-D] NOTE` prints the missing parts of a file, each headed by its lines, and the note.
- `work_meter`: `in_context`, `gaps`, `spans`, `filtered`. In `session_guard`, a read of a file's lines (the
  `requested()` forms) now: all in context → refused as "nothing new to show" (costs nothing); partly → rewritten
  (`updatedInput`) to the missing lines — a Bash read through `lines.py`, a Read to the first missing span with a note
  naming the other missing spans — after the size bound is applied to the missing part only; the rewrite is returned
  only after the batch and tier checks pass, and what it shows is kept in `st["pending"]` by tool-use id so that
  `_record` records exactly those lines as read and adds a Read's note. `stretch_ends` clears `pending`.
- **To finish:** (a) the two failing tests expect the old wording and refusal: `WorkerGuardTests.
  test_a_read_of_lines_in_context_is_refused_until_the_file_changes` (now: partial overlap is rewritten, full overlap
  says "all in your context already") and `ReadTiersTests.test_a_refused_read_takes_nothing_from_either_tier` (its
  assertion text "already in your context" → "all in your context already"); (b) new tests: a partial overlap's
  rewritten command, run, shows only the missing lines with the note; a Read's offset/limit rewrite and its note; the
  recorded ranges after a filtered read; a changed file is not filtered; a Read is not filtered by lines only a Bash
  read showed; (c) mutation cases for each; (d) `covered()` is now named nowhere — remove it (the harness keeps no
  unreferenced function); (e) the protocol (`_production.md`, last sentence of "Production and reading") still says a
  re-read is refused — say it is filtered.
- **A fault found and not yet fixed, the same family:** the gather records every file range it was asked for as read
  (`cmd_step`'s `shown`), even where its per-source 3K cut (`one_read`) or its 30K cut dropped lines. With filtering,
  those never-shown lines would be treated as in context and left out of later reads — information starving. The fix
  planned: the gather bounds its file sources itself (as `fitting` does), filters what is in context there too, records
  exactly what it printed, and cuts the whole at a source boundary, naming the sources it did not show; and it saves the
  meter under `work_meter.meter()` (it uses `load`/`save` without the lock today).

## Questions the owner has open

- The gather: its cut is now the batch bound, 30K (it was 120K). Kept, or separate?
- A check's direct output (an Isabelle run printed into the session) is not cut to 3K — it is a run, not a read — and
  the meter counts at most 30K bytes of it. Since each read is now at most 3K (about 1.2K tokens), three reads can never
  spend the 20K-token budget: only such check output can. Should check output be cut too (keeping its end, where the
  error is), and is the 20K-token budget still wanted?
- The owner also asked how a gather differs from a normal read. As built: a gather is one call that reads many named
  sources, including ones that are not files (facts by name, a task's diff, result or log, task briefs, proposals); it
  opens a step and only after the previous step produced; it counts as one read and is never refused by the tiers; and
  for the planner's roles it serves statements only. A batch of normal reads is also one read, but may be refused past
  the tiers, and reads files and command output only. Unanswered in chat: whether the two should become one.

---

# 2026-09-21, afternoon — reads of lines in context filtered, finished

The owner, repeating the request the last session stopped in: why refuse a read that overlaps what is in context —
filter what is in context, give the rest, and say what was filtered. Nothing committed; the run stays stopped.

**The guard.** A read of a file's lines (`Read`, `sed -n`, `cat`, `head`, `tail`) is compared with what the session
holds of the file unchanged (`in_context`, `gaps`). Nothing of it held: it runs as it is. Part of it: it is rewritten
before it runs (`filtered`, PreToolUse `updatedInput`) — a command through `lines.py FILE NAME SPANS NOTE`, which
prints each missing span headed by its lines and ends with the note of what it left out; a Read narrowed to the first
missing span, its note (and the spans still missing) given after it by the gauge. All of it: the answer is the note
alone, "[lines A-B of F are already in your context (read at T, unchanged since) and are left out]", and the call does
not run and counts as no read. That last is a hook's deny only because a hook cannot answer a call without running it;
its text is the filtered result, not a refusal. The 3K bound applies to the missing part only. A Read is filtered only
once a Read has shown the file (Edit accepts a file only after a Read of it). What a filtered read showed is recorded
from the guard's own account (`st["pending"]`, by tool-use id), and only if the call ran; `saw()` is the one place a
range is recorded (the gauge, the filtered read and the gather), and it starts afresh when the file has changed.
`covered()` is gone; the README and `_production.md` say filtered.

**The gather, the fault the last session found.** It recorded every range it was asked for, including lines its 3K and
30K cuts dropped; with filtering those lines would have been left out of every later read and never shown. Now a file
source is read by `file_read`: what is in context left out and said, at most READ_BYTES of the file's own lines
(measured as the guard measures a read of a file, not with the numbering), where it stopped said with the range to
name next, and exactly the printed lines recorded. A source already shown by an earlier source of the same gather is
filtered too. The 30K bound takes whole sources and names those it did not show; it cut through the middle of one
before. The meter is written under its lock (`work_meter.meter`). The old one-read cut (`one_read`) stays for the
sources that are not files (facts, diff, result, log, briefs, proposals), which are not recorded as in context.

**Found on the way: the second question put to the owner rested on an error.** It said three reads could never spend
the first tier's 20K tokens, since a read shows at most 3K. A read is a batch, and a batch shows up to 30K bytes, about
12K tokens (CHARS_PER_TOKEN 2.5): two full batches end the first tier. The 20K-token bound bites on reads as built.


**406 tests and 150 mutations**, all green (17 new cases: each piece of the filter, the gather's filtering, recording,
whole-source cut and lock, and three older anchors the change had moved). Nothing is committed.

**Open with the owner.** (1) Whether a check's output printed into the session — a run, not a read, so not cut to 3K,
and counted only up to SHOWN (30K bytes) against the batch and the tokens — should be cut like a read, keeping its end.
(2) Whether the gather and a batch of reads should become one; as built they now share the byte bounds, the filtering
and the recording, and differ in what they can read, when they are allowed, and how they treat what is too large.
(3) The gather's size: 30K, the batch bound, since the morning (it was 120K).

---

# 2026-09-21, later — the gather a read, the tokens gone, every output bounded

The owner: the gather is redundant, and should be a read like any other (the only difference being that it is the
first); the token bound is irrelevant now — delete it; and the byte bound applies to everything, outputs and checks
too, with a way to read on. Nothing committed; the run stays stopped.

**The gather is `v2.py read SOURCE...`.** Its sources — files, facts by name, the task's `diff`/`result`/`log` (a
reviewer's: the task it reviews), `task:ID`, `proposal:ID[:KEY]`, each by its lines — are every session's, any time.
It is kind "read" (`V2_READS`), counted and refused as any read, and one call shows at most READ_BYTES: the first
source bounded, later ones whole or named as having had no room. Its file sources are filtered and recorded as
before (`file_read`, measured as printed). Gone: `cmd_step`, the step's state (`step`, `step_at`,
`step_productions`), "not produced yet", `is_gather`, `GATHER_CHARS`. Nothing was lost: the gather opened only after
a production, which restarts the tiers, so the first read after one is always allowed, and a batch is one read. A
consultant was told to gather, and `own_task` refused it every time (it has no task): that fault goes with it.

**The tokens are gone:** `READ_TOKENS`, `read_tokens`, `tier1_until`, `SHOWN`, the meter's `CHARS_PER_TOKEN`, and the
planned inputs (`inputs_read`, `brief_of`'s inputs), which only ever exempted tokens. `tiers(n)` is ROUNDS then the
reserve. efficiency.py's report takes its ratio from ctx_gauge (the context estimate, which stays).

**Every output bounded.** `bounded` sends every foreground command through `cut.py` — reads, scripts, checks,
writes, the harness's own — except a known-size read of a file's lines (measured before), `v2.py read` (bounded
itself) and a background command (it writes a file). The wrapper, `{ ( CMD\n) 2>&1; printf '\n\036%s\n' "$?"; } |
cut.py BYTES head|tail DIR`, carries the command's status out (a pipeline's status is the last command's, and a
failing check must read as failing; the subshell keeps an `exit`'s status too), tried under bash and zsh. A longer
output is kept whole in `.build/outputs/SESSION/N.txt` (the newest 50; a session's go when it is archived, and the
planner roles may read there), and the cut says where and gives the `sed -n` range to read on. A check shows its end,
where it says how it ended, and the circling rule reads its failure from the whole kept file (`KEPT`), not from the
end it showed. Whatever reads the call after it ran takes the wrapper off first (`unwrapped`), so a cut `v2.py ask`
is not counted as a read nor a cut write as other. Still approximate: Grep's bound is in lines, and Glob, WebFetch
and WebSearch cannot be cut by a hook at all (only an MCP tool's output can be replaced after it ran).


**405 tests; 159 mutations, every one caught** — 158 in the full run, and the one it missed ("a cut call recorded as
made") exposed a test that passed for the wrong reason: it fed the rewritten command back through the guard, which
refuses running `cut.py` directly, so the call was never counted either way. In a session the transcript holds the
call as made and only the hook after it may see it rewritten; the test now does exactly that, and catches the
mutation (checked alone). Nothing is committed.

**Open with the owner.** Grep, Glob, WebFetch and WebSearch are bounded approximately or not at all (a hook can only
rewrite a call's input, and only an MCP tool's output after it ran): refuse them in favour of their Bash forms, or
accept it.

---

# 2026-09-21, later — Grep, Glob, WebFetch and WebSearch out of every base

The owner: remove them from the bases completely and refuse them if they are tried; list the tools the sessions still
have, for review. And a question: is the consultant not gone — is the planner not the consultant now?

**The consultant**, as the code stands: `v2.py ask --to kb|designer|task-designer|reviewer` queues a question, and
`consult()` forks the asked session while its cache is warm (the knowledge base otherwise) as `ask-qN`, which answers
once (`v2.py reply`) and ends; `--to planner` is an event to the planner itself. In the state, all 20 questions ever
asked went to the planner, and no consultation has ever run. Whether to take the role out and route every question to
the planner is asked of the owner; nothing changed.

**The tools.** `session-flags` is now `--tools Bash Read Edit Write Agent ToolSearch TaskOutput TaskStop Monitor
TaskCreate TaskUpdate --strict-mcp-config --disable-slash-commands`. `work_meter.guard` refuses the four
(`REMOVED_TOOLS`) to every role, the knowledge base included, before anything else; they stay in the matcher so the
refusal reaches them. The Grep-only paths went with them: the planner roles' narrowed search, the line bound
(`GREP_LINES`), `DOCUMENTS`. Measured over the 71 transcripts in the state: Bash 1,799, TaskUpdate 191, Edit 178, Write
108, TaskCreate 105, ToolSearch 42, Read 4, Grep 4, TaskStop 2 — Glob, WebFetch, WebSearch, Agent, TaskOutput and
Monitor never. Claude Code adds EndConversation itself (deferred, in every transcript's list), outside `--tools`.

**The bases must be built again before anything starts.** The tools are the first thing in every prefix, so a fork
started with other flags than its origin writes the whole of it again (about 530K tokens a base). A base and a started
session now record the flags they were started with (`base.sh` build and layer, `v2.launch`), and nothing forks, pings
or layers over one started with others (`v2.other_tools` in `launch` and `ping`, `base.sh`'s `lean_as` in warm and
layer), with an ATTENTION saying to build it again. Every base standing now predates the record, so all three are
refused until rebuilt (`base.sh WHO build`, then `seal`, and their layers); the knowledge base follows the max base
by itself (`rebased`). Nothing was rebuilt: the run is stopped, and a rebuild is the owner's.

**409 tests and 165 mutations**, all green (seven new cases: the refusal, the fork and ping checks, the recorded flags
and `base.sh`'s ping; the Grep line bound's case went with the code). Nothing is committed.

---

# 2026-09-21, evening — the plan B1 to B5: one command for changing files, checks that stop, four tools

The owner's decisions: D1 leave the consultant for now; D2 tell a session to batch when it makes a single change; D3
checks stop at their first failure; then B1 to B5 only — no base rebuild or seal, no commit, no restart.

**B1, probes** (small sessions outside the harness; their files and transcripts removed after). Tool deferral is
ToolSearch's doing: with it in `--tools`, Opus 5 got TaskCreate, TaskUpdate, TaskStop, TaskOutput, Monitor and
EndConversation as names to load first; without it every tool loads at the start and EndConversation is not there at
all — no setting needed (`ENABLE_TOOL_SEARCH` changed nothing on Haiku or Opus). A PreToolUse `updatedInput` rewrite
is what runs under auto mode — the cut (a 2,000-line output cut at 3K, kept whole, and the model read on from the kept
file), the stop-at-first-error runner inside it (stopped at its first error, not its 30 s sleep), and `v2.py change`
(wrote `\<forall>` and `$HOME` as given). **The hook after the call is given the rewritten input**, so unwrapping it
before counting is required, not a precaution. A heredoc write through Bash passes auto mode.

**B2, `v2.py change`.** `=== write PATH` (the whole file) and `=== replace PATH` / `=== replace-all PATH` with
SEARCH/REPLACE blocks, in a quoted heredoc of the same call; applied in order in memory, written all or none, refused
change by change (with where a missing SEARCH's first line stands); a call of one change is told to batch (D2).
`v2.change_blocks` is read by the command and by the guard alike, so `write_targets` is exact and the write guard,
ownership and production see every file. The guard refuses the call in any other form (unquoted, fed from a file,
with other commands), and every other content write — a redirection into a file, `tee`, `sed -i`, `perl -i`, a
script that writes — whatever the command's kind, a check's `> log` included; where it writes is judged before how,
so a harness file or HANDOFF.md gets its own refusal first. Moving, copying and removing stand. Found by its test: the
put-back on a failed write removed the temporary file and restored the original in one `suppress`, so the restore was
skipped whenever the temporary was already in place — fixed.

**D3, checks stop at their first error.** Not in the repository's tools: `tools/build.py`'s `run_session` is where
they run Isabelle, and it is in the execution closure of all 52 recipes — changing it would have had every recipe
executed again at the next check (a first version there was written, measured and taken back; `tools/` stands as it
did). `first_error.py` runs the check as its own session, passes its output through, and watches it and the logs the
check writes (`--work` for a probe, `--output` for a check), and at the first `***` line ends the whole tree
(descendants from /proc, as `build.stop_process` does) and says so. The guard runs every session check through it,
foreground inside the cut and background alone. Measured on the runs on disk: no accepted check's 276 logs holds a
`***` line (no false stop), 2 of the 9 probe logs do (real failures, whose first line carries the file and line the
circling rule reads), and walking a 67K-file check directory takes 15 ms. The finalizer's check is not a session's and
runs to its end. Also fixed on the way: a heredoc naming a check's tool made its command a check (`CHECK` reads the
command without heredoc bodies now).

**B3, the tools.** `session-flags`: `--tools Bash TaskCreate TaskUpdate TaskStop`. `REMOVED_TOOLS` maps every other
tool to where its work goes, refused to every role; the matcher names them all. Taken out because only Read, Edit
and Write served them: Read's narrowing and notes, `tool_read`, Edit/Write targets, the gauge's writer and Read
cases, the planner guard's Read, and — since a base no longer has Read — `base.sh build-files` and `extend`,
`base-bootstrap.txt`, `manifest.py list` and its folding. `kind` and `requested` keep their Read/Edit/Write cases:
efficiency.py reads old transcripts with them. TaskStop is the session's own (it had been counted as a read).

**B5.** `_production.md` (tools, the change command and its form), `_checks.md` (a check stops at its first error),
planner.md (the ToolSearch paragraph gone), README. **431 tests and 192 mutations**, every one caught.

**Needed before any restart (the owner's):** every base rebuilt (`base.sh WHO build`, `seal`, and layers), since the
tool list changed; nothing forks a base with other tools meanwhile. Nothing committed.

## Later the same evening — a command that went wrong is fixed, not written again

The owner: each command a session makes is to be kept, and it is to be told to fix the problems with the previous
command rather than write everything again, which is counterproductive. Measured first on the 71 transcripts: of
1,799 commands 146 failed (8%), and 40 were followed within three calls by a near-copy of themselves — 88K characters
written again, 15 of them over 1K, the largest 12K; and with every file's change now a command, a refused batch would
be written again whole too. (Reading what was sent before costs nothing new — it is in the prompt cache; what the
rewriting spends is output.)

**Every command kept.** The guard keeps each Bash command a session makes, refused ones included, numbered, as
`.build/outputs/SESSION/commands/N.sh` (`keep_command`, `kept_command`), gone with the session's outputs when it is
archived. **`v2.py again [N] <<'EOF'`** sends only the correction — SEARCH/REPLACE blocks on command N's text (N left
out: the last; no block: as it was) — which the guard applies with the change command's own rule (`v2.replace_one`:
once, or all for replace-all; every block judged and each failure said, nothing run), keeps as the next command, and
guards and runs as if it had been typed: the planner's statements rule, the write guard, the form of writes, the
cut, the check runner — all see the fixed command, which runs by `updatedInput`. It is counted as what it runs
(`st["resolved"]` by call id, read by `is_read` and `_record`; the hook after a call is given the rewritten command,
as the probe showed, and the id resolves it either way). **Told how:** a refusal whose remedy is the command itself —
a write's form, a read too large, a tree session's path into the one tree (`deny(..., fixable=True)`, the mark taken
off before Claude Code sees it) — ends with the command's number and the `again` form; a waiting, budget or
already-in-context refusal does not, since fixing the command is not the remedy. A command that ends failing is told
the same by the cut (`cut.py … N`), except a check, whose fault is in what it checks. A refused `v2.py change` exits
failing, so it is told too. `v2.py again` outside a session says the guard carries it out.

## And later — checks run to their end with every error listed; what a session keeps goes when it ends

The owner, on the cost I named: why stop at the first error — better to wait for the full run, give the session all
the errors, and have it deal with them at once rather than one by one. And: everything now saved — reads, outputs,
commands — deleted once no longer needed. D3's stop is taken back.

**A check runs to its end and ends by listing every error it reported** (`check_errors.py`, which replaces
`first_error.py`). It passes the check's output through; when the check has ended it gathers Isabelle's messages
from that output and from the logs the check wrote meanwhile (a probe's under `--work`, a check's under `--output`),
one line each — `THEORY:LINE: first line` — and prints them last, so the end a check's cut shows holds them, headed
by: fix them all, and what the same cause breaks elsewhere, before the next check. A message is a run of `***` lines
ending at its `At command "…" (line N of "…")`, and that line's place is where it stands (its first may name an ML
file: on the real probe logs `drule.ML:308` became `Positioned_Native_Evaluation.thy:158`); two messages side by side
part where a line of its own names a place. One error in the output and a log is one; another run's log is not read;
a list longer than 2.2K shows what fits and is kept whole in the session's outputs (`errors-N.txt`, the newest 10). The
check's own status stands. `_checks.md` and the README say so.

**What a session keeps goes when it is released** (`v2.release`): its outputs directory — cut outputs, kept commands,
error lists — and, through `forget`, its meter (the reads it holds, its counts), now with the meter's lock, which had
been left behind. While it lives: the newest 50 outputs (cut.py), the newest 50 commands (`KEPT_COMMANDS`), the newest
10 lists. The archive a day later no longer does it. In the live state now: two meters, both of sessions not released,
and no lock yet.

## A pass over what the restrictions leave undoable (the owner, 2026-09-21)

The owner: before proceeding, a broad pass to find where the orchestrator is too restrictive — work that must be done
and could not be — with the native controller's errors as the example; every restriction to be coherent, forcing
nothing unwanted and allowing all that is wanted. Every restriction was read against the work each role must do.

**Repaired** (each tested, each with its mutation case):
- **The owner's questions.** planner.md told the planner to write the owner's questions into the owner ledger, which
  is the harness's file and refused to every session by the write guard. `v2.py ledger TEXT` (the planner's) appends
  `**QN (asked DATE by NAME)** — TEXT` under "Open questions to the owner", numbered on, under the ledger's lock.
- **Native and other failures in a check.** `check_errors.py` listed Isabelle's messages alone: a native controller's
  error, a recipe's exception, a host test's failure reached the session only by reading logs one by one. For a check
  that failed it now lists each part its output names as failed (a JSON row with `"status": "failed"`, as the
  incremental check prints a recipe) with the failure that part's log ends on, the check's summary error, and each log
  written meanwhile that ends on a failure (an exception after its traceback, a panic, an `error:` line). Measured: none
  of the 276 logs of this morning's accepted check ends on such a line.
- **The quick fix's view of a failed acceptance check.** The finalizer gave it the last 30 lines of `finalize.log`; its
  check now runs through the same runner (`work_meter.gathering`, long lists in the task's `run-errors/`), so those lines
  hold every error.
- **A failed command's output.** The cut showed a long output's beginning; a failed one shows its end, where a command
  says what went wrong, and quotes the failure line when it stood before that end — found by its test: a program's
  output is buffered in a pipe and its error is not, so the traceback came first.
- **A program's output had nowhere to go.** Every content write but `v2.py change` was refused, so generated data could
  only be pasted through the change command. Any command may write under `.build/` (`scratch`: not a task's tree —
  whose `.build` is the one behind a link — and not `.build/outputs/`, the harness's records); the repository's own
  files change by `v2.py change` alone, and where it writes is still judged first.
- **Own drafts.** The planner and the task designer could not read back what they wrote under `.build/` — a refused
  graph edit or proposal they must correct. `own_dirs`: their drafts and their own kept outputs and commands.
- **A long fact** could not be read by its lines though the cut said to: `v2.py read Theory.name:A-B`.
- **git's reading forms** (`stash list/show`, `worktree list`, `tag`/`tag -l`, `notes show`) were refused with its
  writing forms.
- **Shell syntax**: a comparison in `$(( ))` or `[[ ]]` read as a redirection and was refused; `&> file` was not seen.
- **A search that found nothing** (grep, diff, cmp, test: status 1 is an answer) is not told it failed.

**Left as they are, knowingly:** a script a session writes and then runs is not read by the guard (a class that was
always there; the finalizer and the commit gate stand behind it); the knowledge base's reading is neither cut nor
metered, as it loads what it is to hold; a consultation forked from a released session finds none of that session's
kept outputs; `v2.py graph` and `status` are cut at 3K like any read, so a large graph costs the planner more than one.

---

# Handoff, 2026-09-21 evening — where this session stops

Stopped at the owner's word, in the middle of the last request (below). **Nothing is committed** (standing rule:
commit nothing before told). The run is stopped, `state/stopped` and `state/no-launch` stand, the daemon is down,
nothing was started. **No base was rebuilt or sealed** (the owner's instruction). Git's index is clean (nothing
staged; twice this session a `git rm --cached` of an untracked file staged nothing, and once a tracked one was
staged and immediately put back — do not use `git rm` here).

## What this session did, in order (each section above has the detail)

1. Reads of lines already in context are filtered, not refused (`lines.py`, `in_context`/`gaps`/`filtered`/`saw`).
2. The gather is gone; `v2.py read SOURCE...` reads any source as an ordinary read (facts by name, `Theory.name:A-B`,
   the task's diff/result/log — a reviewer's: the task it reviews — `task:ID`, `proposal:ID[:KEY]`, files).
3. The token budget is gone; the tiers are 3 reads a production, then a reserve of 10.
4. Every command's output is cut to a read's bytes (`cut.py` through the guard's `updatedInput`), kept whole under
   `.build/outputs/SESSION/N.txt`; a check or a failed command shows its end, and a failure said before the end is
   quoted. Verified live by probes outside the harness.
5. Tools: sessions have Bash, TaskCreate, TaskUpdate, TaskStop only (`session-flags`); every other tool is refused
   with its pointer (`REMOVED_TOOLS`). Deferral was ToolSearch's doing; without it everything loads at start.
6. Bases and started sessions record their flags; nothing forks, pings or layers over one started with others
   (`v2.other_tools`, `base.sh lean_as`). **Every current base predates this and is refused until rebuilt.**
7. `v2.py change` is the one way to change repository files (blocks in a quoted heredoc, all or none, loud); content
   writes any other way are refused except under `.build/` (`scratch`); a single-change call is told to batch.
8. Every command is kept numbered; `v2.py again N` sends only the correction; fixable refusals and failed commands say
   how.
9. A check runs to its end and ends by listing every error (`check_errors.py`): Isabelle's messages placed by their
   `At command` line, and for a failed check native/recipe/tool failures from its output and logs; the finalizer's
   acceptance check runs through it too. (Stop-at-first-error was built and taken back at the owner's word.)
10. What a session keeps (outputs, commands, error lists, its meter and the meter's lock) goes at release.
11. The audit of what the restrictions left undoable, and its ten repairs (`v2.py ledger` for the owner's questions,
    own drafts readable to statements roles, git's reading forms, shell comparisons and `&>`, a search's answer).
12. B1 probes' findings are in the evening section above.

Last full verified state before the final request: **448 tests pass**; the mutation check's last complete run was
210/211 (the miss was fixed by a new test); the run over the audit's 228 cases was stopped part way when the final
request came (its file restored from `.bak`), so **the mutation check has to be run again in full**.

## The final request, unfinished

The owner: review the bases and layers so that no currently incorrect information is in them; review every role's
prompt for adequacy and coherence; read the orchestrator's README fully and make it consistent with the orchestrator
and adequate; and raise the limits to 5K a read and 50K a batch.

**Done:**
- The limits: `v2.READ_BYTES` 5,000 and `BATCH_BYTES` 50,000; `check_errors.ROOM` follows (`ORCH_READ_BYTES` − 800);
  the texts that named 3K now take the figure from the constant; one test that hard-coded 3000 fixed. **The suite
  has not been run on this state** (stopped at the owner's word before its result).
- The memory file `native-speedup-batch-state.md` named the active Isabelle base as `.build/check-20260918k/proof`;
  corrected to `.build/complete-20260921a` (named by `/tmp/structural-active-context.json`).
- Every entry of the three load lists exists (280, 334, 325 entries; none missing).

**Findings not yet acted on — the next agent does these:**

*The bases* (they are what every fork starts with; the corrections reach them only by the rebuild, which the owner
runs). What is wrong there now is harness mechanics, not the library:
1. `library-prompt.md` (every base's system prompt): line 7 "your gathers" → what it reads; lines 37–41 "each step
   opens with one gather of everything it reads" → one batch; the owner section (lines 78–80) says the session writes
   the provisional choice and question into the ledger — now the planner does it with `v2.py ledger` and every other
   session brings it to the planner (`v2.py ask --to planner`) or its result; the harness section should say, briefly:
   the tools are Bash, TaskCreate, TaskUpdate, TaskStop; files change by `v2.py change`; reads are bounded; a check
   ends with every error listed; **the owner's rules held in the base were written for sessions working alone with
   the owner, and some of their mechanics are the harness's here** — the finalizer commits and pushes, waiting is
   refused (a completion notifies, a producing session parks), and what a rule says to report or record goes into
   the result or to the planner; and the start-of-work reading AGENTS.md and DEVELOPMENT_WORKFLOW.md ask for is this
   load (the base holds DEVELOPMENT_WORKFLOW.md; compaction is blocked).
2. The memory files the bases hold ("the owner's voice and the operating rules") that clash in mechanics for harness
   sessions — correct for the owner's own sessions, so leave them and let item 1 interpret them:
   `commit-push-at-milestones` and `large-batches-parallel-work` (commit and push; a background waiter),
   `batched-callbacks` (waiting loops, refused to sessions), `proceed-provisionally-then-ask` (record in HANDOFF.md
   and the ledger — the planner's), `report-check-comparisons` (report in chat).
3. The load lists' curation comments say "HANDOFF.md and gathers carry what is new" (never loaded; wording only).
4. AGENTS.md, DEVELOPMENT_WORKFLOW.md, problems.txt, owner-directions.md, codex-owner-directions.md were read: nothing
   in them is wrong about the harness now (the re-read-after-compaction rule is met by the load; see item 1).
5. HANDOFF.md (the knowledge base's load, the planner's file): its absolute-check-path rule (line 136) no longer
   holds; an event already queued for the next planner says so. Not the harness worker's to edit.

*The role prompts* (read in full; they agree with the rules as they stand, with these exceptions):
6. `_production.md` describes the cut twice (in "Production and reading" and at the end of "Steps, and reading any
   source"): merge into the first — beginning shown, or the end for a check or a failed command.
7. `_first.md` (used only when there is no graph) still names T3 installed and T4–T10 queued, the state of
   2026-09-19: make it timeless.
8. `v2.FRESH_CHARGE` (the fresh start's charge to the first planner) calls PLANNING_LOG.md "new and empty" (it has
   931 lines) and asserts "the graph you inherit is a chain": correct both.

*The README* (read in full, lines 1–627), inconsistent with the orchestrator in:
9. line 30–31: the planner records the owner's open questions by hand → `v2.py ledger`.
10. line 55–56: "the base's system prompt describes the v1 implementer" — it does not (it is `library-prompt.md`,
    every role's): say what it is.
11. line 143: "about 327K on the present 560K base" → the room now: about 364K for a build or fix, 383K for the rest
    (`v2.room_of`).
12. lines 160–175 and 180: 30K/3K → 50K/5K; "the first 3K of its output (a check: the last…)" → also a failed
    command's end, with an earlier failure quoted; "a session's go when it is archived" → when it is released.
13. lines 228–235: "its changes are set aside (`parking_care`)" and the shelf paragraph describe what stopped on
    2026-09-20 — nothing is set aside now; the parked task's work stays in the tree until it commits;
    `v2.py unshelve` serves only a shelf made before then.
14. line 250: "a list longer than about 2K" → about 4K.
15. lines 258–277: the audit paragraph stands between the check rules and the sentence on waiting and filtering that
    belongs with them — move it after them.
16. lines 285–287: the change paragraph must say a command's output may be written under `.build/`.
17. lines 297–298: "`v2.py read` filters its files the same way…" sits at the end of the `again` paragraph; it
    belongs after the filtering sentence.
18. line 577: `base.sh extend` (a 2026-09-18 verification) — gone since 2026-09-21; say so.
19. lines 624–627: "v2 has not run live" — it ran live on 2026-09-20 and 2026-09-21; say what ran live and what has
    not yet (`v2.py read`/`change`/`again`, the cut, the filtered reads, `check_errors`, the four-tool set — all
    tested, the rewrites probed outside the harness, none run by a harness session).
20. The Parts table lacks `cut.py`, `lines.py`, `check_errors.py`, `commit_gate.py`.

## What the next agent should do

1. Read this note from "# 2026-09-21, later — the gather a read" on, and the work list (`notes/worklist-2026-09-21.md`).
2. Run the full suite on the limit change (never run since it was made); fix what fails at its cause.
3. Carry out findings 1, 3, 6–20 above (2, 4 and 5 need nothing of the harness). Keep each change tested where code
   changes (FRESH_CHARGE has tests that read it; the protocols are rendered by tests).
4. Run the full suite, then the full mutation check (`python3 -B notes/mutation-check.py` in this directory, about
   20 minutes; never edit code while it runs — it rewrites files and restores them from `.bak`; if it is stopped,
   move any `*.bak` back over its file).
5. Report to the owner, then wait for the word on: rebuilding the three bases and their layers (required before any
   restart — every current base is refused for its tools), committing, and restarting the run.

---

# 2026-09-21, night — the final request finished: bases, prompts and README brought up to date

The session after the handoff above carried out its findings 1, 3 and 6–20 (2, 4 and 5 needed nothing of the
harness). Nothing is committed, no base was rebuilt, the run stays stopped with the hold on.

**The limits first.** The suite on the 5K/50K change, never run before: **448 passed**. Nothing needed fixing.

**The bases** (reach them only through the rebuild, which is the owner's):
- `library-prompt.md`: "the planner" for "a planning episode"; "what you read" for "your gathers"; each step opens
  with "one batch"; the owner's words reach the planner at once (not "the next planning episode"); a provisional
  choice is made and the work goes on, the question reaching the owner through the planner, which puts it in the
  ledger (`v2.py ledger`; no session writes it by hand). The harness section now names the four tools, `v2.py read`
  and `v2.py change`, bounded reads and outputs, and a check listing every error; and a new paragraph says the owner's
  rules held in the base were written for sessions working alone with the owner — their substance holds, their
  mechanics are the harness's: the finalizer commits and pushes, nothing waits (a completion arrives; a producing
  session parks, any other ends its turn), what a rule says to report or record goes to the result or the planner,
  and the start-of-work reading of DEVELOPMENT_WORKFLOW.md is this load, with no compaction. The memory files stand
  as they are. Only `base.sh`'s build passes the prompt (`--append-system-prompt-file`); forks inherit it, so the
  rebuild carries it and nothing else needs to.
- `base-load-max.txt`: the six curation comments say "the sessions' own reads" for "gathers" (never loaded).

**The role prompts.** `_production.md` describes the cut once, in "Production and reading": the beginning, or the end
for a check or a failed command, with a failure said before that end quoted. `_first.md` is timeless: whatever
carried the development before left its state in HANDOFF.md; no T3 or T4–T10; the parts of one uncommitted change
(theory, ROOT line, import, row) belong together to the task that continues it. `v2.FRESH_CHARGE`: PLANNING_LOG.md is
appended to after what earlier planners left, dated (it has 931 lines); "where the graph you inherit runs as a
chain, each task waiting on the one before, re-plan it…" instead of asserting that it is one.

**The README** (findings 9–20, and two found on the way):
- the planner's open questions go to the ledger by `v2.py ledger`;
- the system prompt is `library-prompt.md`, every role's, and says which mechanics of the owner's rules the harness
  carries out (no longer "describes the v1 implementer");
- found on the way: "until the base topic builds xhigh and high, their roles fork the present base at max" — all three
  are built since 2026-09-20; a role whose base is not built falls back to max (`v2.FALLBACK`);
- a brief's room: `v2.room_of`, about 364K for build and fix, 383K for the rest, on the bases of 2026-09-20;
- 50K/5K; the cut's end for a check or a failed command, an earlier failure quoted; a session's outputs go at release;
  `Theory.name:A-B` among `v2.py read`'s line forms;
- the one tree: its owners include the unfinished task whose installed work stands in it (`tree_writer`) — found on
  the way, the paragraph named only the finalization and the producer; the parked task's changes stay in the tree
  (`parking_care`); nothing makes a shelf since 2026-09-20, why (a change is a set of parts), and `unshelve` serves
  only an older one;
- the error list's bound: about 4K (`check_errors.ROOM`);
- order: waiting and subagents refused joins the check paragraph; the filtering sentence and `v2.py read`'s filtering
  follow the `v2.py read` paragraph; the audit paragraph after the change and `again` paragraphs;
- changing files: any command may write under `.build/` (`work_meter.scratch`), not into `.build/trees/` or
  `.build/outputs/`; where a command writes is judged before how;
- `base.sh extend`: gone with the Read tool (2026-09-21);
- a new section "What has run live, and what not yet": v2 ran live on 2026-09-20 only (71 sessions, 00:15–22:36, the
  last runs on the layered bases); verified there, from `state/v2.log`: the task-list variable leaves a fork's cache hit
  intact (`plan-29`: `cache_read=485372`), sealed sessions other than a base resumed, the layers' pings. Not yet run by
  a harness session: `v2.py read`/`change`/`again`/`ledger`, the cut, filtered reads, `check_errors.py`, the four-tool
  set. The handoff above said "2026-09-20 and 2026-09-21": the log has no session started on 2026-09-21;
- the Parts table: `cut.py`, `lines.py`, `check_errors.py`, `commit_gate.py`.

## The owner asked again: review the bases and layers, and every role's prompt — a second, own pass

Everything a rebuild would freeze was read against the repository as it stands (the theories aside: they are
digests of Isabelle-checked sources and carry no harness claim).

*Held by the bases and layers, corrected:*
- `DEVELOPMENT_WORKFLOW.md` (every base): "DECISIONS.md is loaded whole, as an index, by every base" — the `high`
  base holds no decisions index; now "the planner's and the middle bases hold every entry by its heading and first
  sentence". The same paragraph left "what a theory offers for reuse…" as a fragment starting in lower case since
  `c1843ab1` inserted a passage before it; now a sentence. Both came from an orchestration commit, so the harness's to
  correct.
- Memory (every base): `native-speedup-batch-state` named `NATIVE_SPEEDUP_HANDOFF.md`, which does not exist — the
  paused candidates are `native_mechanism_speedup.md`'s remaining work — and gave "stage 1: seed…; stage 2: one
  refinement" as the next work, which the plan is long past; it now points to the plan's own status and direction.
  `proof-search-over-quantified-facts` said "~1,675 theories" (1,800 now). The other memory files' paths, options
  and remotes were checked and hold (`/tmp/structural-isabelle` holds `Complete_20260921a`; `--advance-base`,
  `adopt --proof`, `--parallel-proofs`, `--prelude`, `--substitute`; `origin`).
- The load prompt of every base and layer (`base_pack.bootstrap`): "Do not use Read, …" — no base has Read.
- Checked and right: the pack's legend and tier headings; `native_control_plan.md`'s status section against the
  commits since (its last result, `44738c20`, and the two untracked theories as "building"); AGENTS.md; problems.txt
  and the owner's directions (the owner's words). `base-settings.json` wires no guard, so the 5K cut never reaches a
  base's 120K chunks.
- The load lists' headers said "DRAFT … not in use" (comments only); max's had "In the / In the".

*Held by the knowledge base, and the next planner's first message:* the event waiting for the next planner (it
survives `--fresh`: `fresh_sweep` keeps it) said in its item 7 that `step` takes several ids and "a gather reads a
task's brief"; both are gone — now `read` and `v2.py read`. Changed under the state lock, logged. HANDOFF.md itself
is the planner's; the event is what corrects it.

*The role prompts, rendered as sent (every role, every part):*
- `investigator.md` did not say that the planner judges an investigation (the finishing part says "a reviewer judges
  the work"); the designer's did. Now both.
- `planner.md` ended with the workers' owner part — "bring to the planner what reaches beyond it (`v2.py ask --to
  planner`)", to the planner. It now has its own: the owner's words to another session reach it as an event, and it
  acts on them in the graph, the order, the decisions and HANDOFF.md. Also said twice there and now once: the brief's
  admission (under Tasks and again under the graph's shape) and the log (`The log.` and `It is a state and not a log`).
- `task-designer.md` said the depth rule and "detail is always admitted" twice; the second paragraph keeps only what
  it adds. It told the task designer to "record your result" when a detailing needs a task past the limit, but gives it
  no result form, and `cmd_result` refuses one not in form: it now names the file, the status and the four parts and
  the command. Its JSON example has a lead-in.
- `_checks.md`: "the run keeps going, keeps its changes in the working tree" — the changes are the session's; the
  paragraph is rewritten with nothing else changed.
- Checked and coherent: TaskCreate/TaskUpdate for workers (their own lists; refused only on the graph's settings);
  production counted from the files a session writes, however written (`check_production`), so drafts by heredoc
  count; the knowledge base's three files fit the 128K output bound unread by the cut.

## Verified, and the owner's word: rebuild, commit, push, start fresh

**448 tests pass on every change above; the full mutation check caught all 228 of its cases**, and every file was
restored (no `.bak`). The owner then said: rebuild the bases, commit and push, and start the run with `--fresh`; and
asked for a command that stops the orchestrator but keeps the warmth daemon.

**`stop.sh --keep-warm`.** `stop.sh` always killed the daemon, so on 2026-09-20 the same stop was done by hand
(`v2.py stop`, `state/stopped` written). The flag does everything `stop.sh` does — `state/stopped` first, every role
stopped, the orphaned tool runs ended — and leaves the daemon, whose watchdog returns at once while `state/stopped`
stands and whose pings keep the sealed bases and layers warm. Tested (the daemon's pid lives through two rounds, the
run stays inactive, nothing is restarted, a wrong flag is refused) with a mutation case, caught. README's Use lists it.

**Is the inconsistent worktree resolved?** Not in HEAD: its ROOT declares `Development_Loci` and
`Development_State_Rows` (committed with task 7, `44738c20`) and holds neither file; they stand untracked in the one
tree, which is consistent. The harness is safe against it (a tree is checked before a session is put in it; tasks work
in the one tree meanwhile with the reason; the commit gate refuses making HEAD worse). It is resolved when 22 and 46
land. Under `--fresh`, `reopen_unlanded` runs in `reconcile_stages`, which the hold does not gate, so their checks (and
50's) start at the first dispatch; their reviews (23, 47) are `support()`, which the hold gates, so they wait for the
planner's order.

---

# 2026-09-21 ~16:42 — every transcript and memory file of the project deleted during a probe's cleanup

**What was lost.** Everything under `~/.claude/projects/-home-julius-structure-and-semantics/`: every session
transcript (the runs of 2026-09-20, the planners, the knowledge bases, the earlier orchestrator sessions, the six base
and layer sessions just built) and every memory file. Only the live session's own transcript remained, written afresh
from that point. The repository is intact. Timeshift here snapshots `@` only (its config's `"include_btrfs_home:"`
key, with the colon inside the name, is not a key Timeshift reads), so nothing of it can be recovered.

**Restored.** The 26 memory files and MEMORY.md, from the full reading of them earlier in the same session: their
bodies verbatim (with the two corrections of that day), their frontmatter (never read, since the reading stripped it)
rebuilt from MEMORY.md's lines. The transcripts are gone for good; what efficiency.py, health.py and the frontier
measurement read from them starts from nothing.

**When, and what ran then.** The memory directory was emptied at 16:42:34, while three throwaway forks of the new
layers, started in parallel to ask which tools they had, were being removed (`claude stop ID; claude rm ID`, then
`rm -rf` of the probe's own transcript path, guarded against an empty id). They were removed during their ten-second
SessionStart hook, before their first request, because the wait loop took the listing's first `idle` for their end.
The project and job directories were last changed at 16:46:48, by `claude rm` of a later probe. Before that, a first
probe had been started from `.claude/orchestration` under zsh, which passed `session-flags` as one word: it did not
resume the base at all and was given Claude Code's whole default tool list. **The deleting command is not
identified.** `base.sh warm` and the harness's release of sessions use the same `claude stop`/`claude rm` pattern.

**The state it leaves.** The six new base and layer records stand, but their transcripts are gone, so nothing can
fork them: all six must be built again. `state/no-launch` is back, with the reason. The keep-warm daemon started by
`seal` still runs (the owner is to stop it: `kill` was refused to the session); its watchdog is inert while
`state/stopped` stands, but its pings of the three layers would fork sessions that no longer exist and remove them
the same way. Nothing is committed, pushed or started.

**Before anything launches again:** reproduce the deletion in a throwaway project with dummy transcripts — one
background fork, removed the same way during its start hook — and repair it where it arises; then build the high base
alone and test on it, one probe at a time; only then max and xhigh, the commit and push, and `start.sh --fresh`.

**The cause, found (the same evening).** Not Claude Code: the session's own first probe command. It was run from
`.claude/orchestration` under zsh and ended `claude stop "$2"; claude rm "$2"; rm -rf
~/.claude/projects/-home-julius-structure-and-semantics/$4 "$f"`, with no guard on `$4`. Started from that directory
the probe's session was not the project's, so `session_row.py` found no row, `set --` left `$4` empty, and the `rm -rf`
took the whole transcripts directory. The session's own transcript was recreated with its first entry at 16:41:21,
the end of that command, and `~/.claude/projects` was last changed then; the three parallel probes came after it.
Reproduced the other way in a throwaway git project with `bgIsolation: none` and the ten-second start hook: a fork
stopped and removed after its answer, and one stopped and removed two seconds after launch, during its start hook,
deleted nothing (`claude rm` leaves transcripts alone). The harness's deletions were read: the one `rm -rf` under the
transcripts directory, `base.sh warm`'s, is guarded by `[ -n "${4:-}" ]` and runs under `sh -u`; every other
deletion is inside `state/` or the outputs directory and skips an empty id. So the harness is not implicated, and the
probe forks after 16:41:21 resumed sessions whose transcripts were already gone — which is also why none of them
forked the base and layer they named. The rebuild procedure itself (build, status, seal, layer) worked; it only has
to be run again.

# 2026-09-21 evening — the sandbox, and the harness made to work inside it

**Turned on by the owner** after the transcript loss: `.claude/settings.local.json` has `sandbox.enabled`, no
unsandboxed commands, writes allowed to `/tmp` (heaps, Isabelle's temp prefix, the active-base pointer, which is
replaced by rename and so needs its directory), `state/`, `.build/outputs`, `.build/tasks` and
`~/.claude/tasks/orchestration-graph`, and the network to `github.com`. Every session reads that file, in a task's tree
too (a worktree reads the main checkout's). Tested: those paths writable; `~/.cache`, `~/.claude/jobs` and the
transcripts refused; a throwaway Isabelle session builds in 2 s; `git ls-remote origin` answers. Not yet seen: a
session in a tree writing `state/` through the explicit entries (this session's own `.` covers it, so it proved
nothing there); the first live tree session shows it.

**No excluded commands.** An exclusion is matched on the command's text: tested with a stand-in script at
`.build/sbxprobe/.claude/orchestration/v2.py`, it ran outside (670 processes visible against 5 inside), and so did
`...v2.py probe; ps -e` chained after it. The owner took the exclusion out.

**The harness change.** Inside the sandbox nothing can start, stop or remove a session. `v2.control()` says whether
this process can (`~/.claude/jobs` writable; `ORCH_CONTROL` states it); without it `release` asks the supervisor
(`state/wanted/`) instead of recording a session released that it could not stop (it did: its `claude stop` failed
unseen), `background` and so `kick` ask instead of running a dispatch or a finalizer inside, `dispatch` does not run,
`hand_mail` leaves mail to the watchdog, `claude()` refuses `--bg`/`stop`/`rm`, and `start`, `stop`, `talk`, `ping`,
`start.sh`, `stop.sh`, `base.sh build|build-packed|layer|seal|warm` and `warm_daemon.sh` refuse with "run it from
your own terminal". The dispatch carries out requests first (`carry_out_wanted`, each taken by rename, done once);
the daemon's minute of sleep ends when one waits. `v2.py start` makes `.build/outputs`, `.build/tasks` and
`state/wanted` (the sandbox opens only paths that exist). Tests: `SandboxTests` (4), one in-process, one daemon test in
test_start_stop; seven mutation cases, all caught. `test_base_pack`'s build-packed test keeps the real HOME with a fake `claude`, so it now states
`ORCH_CONTROL=1`: what the real one could do is not its subject. So: start.sh, stop.sh and the base rebuild are the owner's, from
their own terminal.

**What else the sandbox changes, looked for before anything runs (same evening).** Measured inside it:
- *Each command is its own process namespace*: 5 processes visible against 3,094 on the machine (`/proc/loadavg`). A
  PID recorded outside means nothing inside, and a run started by one command is invisible to the next. **Broken by
  it:** `v2.py measuring` (producing sessions): `exclusive_claim()` finds a finalizer's PID absent and *deletes its
  claim*, and `isabelle_runs()` counts 0, so a measurement is granted beside running checks — the two heavy runs the
  claim exists to keep apart. `health.py` run from a session calls the live daemon dead. The hook's check gate
  (`work_meter.session_guard`) counts the same way and is right only if hooks run outside the sandbox, which the docs
  imply and do not state: confirm on the first live session.
- *Every allowed path is its own mount*: a rename between two of them fails with EXDEV (tested: project root → state/,
  $TMPDIR → state/, .build/outputs → .build/tasks, state/ → /tmp); within one works. No current code renames across;
  every temp file is made beside its target. A trap for new code.
- *An allowed path that does not exist when a command starts cannot be created from inside*: `.build/outputs` was
  missing; `v2.py start` now makes it.
- Fine: file locks hold across sandboxes (flock tested between two commands); CLAUDE_CODE_SESSION_ID passes, so
  `caller()` works; NO_PROXY covers localhost; sessions' git is read-only (the guard refuses the rest); a check in a
  tree writes only the tree and /tmp; the base-advancing check is the finalizer's, outside; writing through a tree's
  `.build` link resolves to the real, allowed path; `running_jobs` reads transcripts, which is allowed.
- Traps: `tools/investigate.py` and `tools/build.py` default their heap store to $TMPDIR, which is /tmp/claude-1000
  inside — a bare run builds a second store. With /tmp writable, a session can still delete the heap store or move the
  active-base pointer (as before the sandbox); narrowing /tmp needs the pointer moved into /tmp/structural-isabelle.
- **Fixed the same evening.** Inside the sandbox `v2.py measuring` asks the supervisor (`want(measure=…)`), which
  decides with every run in sight (`measure_claim`) and answers by message; `exclusive_claim()` leaves standing a
  claim whose process it cannot see; the daemon keeps a heartbeat (`state/warm.beat`, a ticker that ends with it)
  and `health.py` reads that inside. `protocols/_tree.md` says the answer comes as a message. Tests: one in
  SandboxTests, one in-process, one in test_start_stop; five more mutation cases, all caught.

---

# Handoff, 2026-09-21 ~18:30 — where this session stops

Read this section, then the two just above it ("~16:42 — every transcript and memory file … deleted" and "evening —
the sandbox"), then README's "The sandbox". The standing rules at the top of this note hold: nothing about the
orchestration in the project memory; commit only at the owner's word; the base rebuild is the owner's.

## Where it stands

- **The run is stopped**: `state/stopped` and `state/no-launch` stand (the hold's text says why). No session runs. The
  old daemon (`state/warm.pid`: 713125) is most likely dead — `state/warm.log` has nothing after 16:46:48, and it would
  have pinged by 17:20 — but nothing inside the sandbox can see a process to confirm it: the owner does
  (`kill 713125`).
- **No base can be used.** This session built, sealed and layered all three (max 477,804, xhigh 503,141, high 521,553
  tokens; `state/{max,xhigh,high}-{base,layer}.json`), and their transcripts went at 16:41:21, so nothing can fork
  them. `base.sh WHO drop` comes before each build (a build refuses while a record stands).
- **Every transcript before 16:41:21 is gone for good** (Timeshift snapshots `@` only). `efficiency.py`, `health.py`'s
  history and the frontier measure start from nothing; no earlier session can be read or resumed.
- **Memory**: the 26 files rewritten from this session's reading of them (bodies verbatim; frontmatter rebuilt from
  MEMORY.md, types this session's own classification), and two new: `guard-deletions-by-variable`,
  `sandbox-no-exclusions`. Every load list takes `memory/*.md`, so the next builds carry the new two.
- **The sandbox** is the owner's `.claude/settings.local.json`: auto mode refuses the session editing it as
  self-modification, and the sandbox refuses Bash writing it. As saved:
  `{"sandbox": {"enabled": true, "autoAllowBashIfSandboxed": false, "allowUnsandboxedCommands": false,
  "filesystem": {"allowWrite": ["/tmp", "<project>/.claude/orchestration/state", "<project>/.build/outputs",
  "<project>/.build/tasks", "/home/julius/.claude/tasks/orchestration-graph"]},
  "network": {"allowedDomains": ["github.com"]}}}` — no excluded commands.
- **Committed and pushed at the owner's word** (18:40): all of 2026-09-21's harness work and this session's, as
  `1cf9e739` ("Bound what sessions read and write, and run the harness inside the sandbox"; `.claude/orchestration/`
  and DEVELOPMENT_WORKFLOW.md only), with `7d78caf0` and `87f827f4`; origin's main is `1cf9e739`. **458 tests pass.** The 12 mutation cases this session
  added are caught; **the full mutation check has not run since this session's changes.**
- **Untracked zero-byte paths** in `git status` — `.bashrc`, `.zshrc`, `.profile`, `.gitconfig`, `.gitmodules`,
  `.mcp.json`, `.idea`, `.vscode`, `.ripgreprc`, `.claude/hooks`, `.claude/agents`, `.claude/skills` and others, and
  `.claude/.claude/`, `.claude/orchestration/.claude/`: inside the sandbox they are `/dev/null` mounted over paths it
  protects (character devices dated at boot, 09:24:50), and git sees their mount points. **Never `git add -A`**; do not
  delete them from inside (they are mounts). Whether empty files stay on disk outside the sandbox is not checked.

## What this session did (each section above has the detail)

1. Built, sealed and layered the three bases — then lost them with the transcripts.
2. Deleted every transcript and memory file of the project, by its own probe's `rm -rf …/projects/<project>/$4` with
   `$4` empty. Reproduced the other way in a throwaway project: `claude stop` and `claude rm` delete no transcript, even
   of a fork removed during its start hook. Memory restored.
3. With the owner, turned on Claude Code's sandbox and found what the project needs; tested an excluded command as a
   hole (matched on text; any file at the path, and anything chained after it, ran outside), which the owner removed.
4. Made the harness work inside it: `control()`, requests to the supervisor (`want`, `state/wanted/`,
   `carry_out_wanted` first in the dispatch), and inside the sandbox `release`, `background`, `kick`, `dispatch`,
   `hand_mail` and `claude()` ask or leave the work to the supervisor; `start`, `stop`, `talk`, `ping`, `start.sh`,
   `stop.sh`, `base.sh build|build-packed|layer|seal|warm` and `warm_daemon.sh` refuse; the daemon wakes within seconds
   of a request; `v2.py start` makes the allowed paths that must exist.
5. Looked for what else the sandbox changes (process namespace per command, a mount per allowed path — the findings
   above) and fixed what it broke: `measuring` is decided by the supervisor and answered by message
   (`protocols/_tree.md` says so), a claim whose process cannot be seen stands, and `health.py` reads the daemon's
   heartbeat (`state/warm.beat`).

## What the next agent does, in order

1. **The full mutation check**: `python3 -B notes/mutation-check.py` in `.claude/orchestration` (about 20 minutes).
   Nothing else may run meanwhile — it rewrites harness files and restores them from `.bak`; if it is stopped, move any
   `*.bak` back over its file. A miss is fixed with a test.
2. **The rebuild, by the owner from their own terminal** (nothing inside the sandbox can start a session, this agent
   included). One base at a time, high first:

       kill 713125 2>/dev/null; rm -f .claude/orchestration/state/warm.pid
       rm .claude/orchestration/state/no-launch
       .claude/orchestration/base.sh high drop
       .claude/orchestration/base.sh high build
       .claude/orchestration/base.sh high status     # until the load has ended its turn
       .claude/orchestration/base.sh high seal
       .claude/orchestration/base.sh high layer

   Then verify the high layer before the others: `base.sh high warm` writes a line to `state/warm.log` with its
   cache_read (about the layer's context) and cache_write (a few hundred at most). The owner also wants to see which
   tools a fork of the layer has. That probe is the owner's to run: give them a script — bash, `set -u`, run from the
   project root, `claude --bg --resume <layer sid> --fork-session $(cat .claude/orchestration/session-flags) …` with
   the layer's model and effort, waiting for the reply in the fork's own transcript (not the listing's `idle`, which
   comes before the ten-second start hook ends), then `claude stop` and `claude rm` of that fork's id only, and no
   computed `rm` under `~/.claude` at all. One probe at a time, nothing in parallel, no retry before the cause of a
   failure is known (the owner, today). Then max and xhigh the same way.
3. **Commit and push** — done for everything up to `1cf9e739` (above), and the handoff's own update as `9a4f17dd`. **Then the owner said: do not push anything else** (2026-09-21, ~18:45): nothing is pushed, and nothing committed, without the owner's word for it. What follows is how it was done, at the word the owner gave before the loss ("rebuild the bases, commit and push, and start the
   run with `--fresh`"): only the harness — `.claude/orchestration/`, its untracked new files included (`check_errors.py`,
   `commit_gate.py`, `cut.py`, `lines.py`, `notes/worklist-2026-09-21.md`, `test_change.py`, `test_check_errors.py`),
   and `DEVELOPMENT_WORKFLOW.md` (its harness corrections). HANDOFF.md, PLANNING_LOG.md, native_control_plan.md,
   `tools/` and `theories/` are content or not this work's: ask the owner. Style: `git log -3`, no attribution lines.
   `git commit` has not been tried inside the sandbox (`.git/config` and `.git/hooks` are read-only there); do not use
   `git push -u`, which writes the config. `git push origin main` reaches github.com (gh's token is a file).
4. **The owner starts the run**: `.claude/orchestration/start.sh --fresh`, from their terminal.
5. **On the first live sessions, confirm what could not be tested from here**: that hooks run outside the sandbox (the
   check gate, `work_meter.session_guard`, counts Isabelle runs and claims: with one check running, another session's
   check is refused naming it); that a session in a tree writes `state/` and `.build/tasks` through the explicit entries
   (its `v2.py` calls succeed, `state/v2.log` shows them); that `state/wanted/` empties within seconds of a request; and
   that `health.py` from the owner's session says "daemon: alive".

## Open for the owner

- Narrowing `/tmp`: any session can delete the heap store or move the active-base pointer; narrowing needs the pointer
  moved into `/tmp/structural-isabelle` (four places).
- `tools/investigate.py` and `tools/build.py` default their heap store to `$TMPDIR`, which is `/tmp/claude-1000` inside
  the sandbox: a bare run builds a second store.
- Whether the two new memory files belong in the bases: they are rules for any session's shell, not notes about the
  orchestration, but every base loads them.

---

# 2026-09-21 ~19:40 — before the rebuild: forks missed their base; the tool set pinned

The owner asked, before building, to make sure the bases' and layers' tools are what they should be. Five probes
(`.build/probe-sandbox-tools.sh`, `probe-sandbox-cache.sh`, `probe-flags-cache.sh`, `probe-growthbook-cache.sh`,
`probe-multirequest-cache.sh`, with `.build/probe_transcript.py`; logs beside them), run by the owner from their
terminal, one session at a time, each copying base.sh's and v2.py's launch lines:

- **The tool list varied between identical launches.** A base's `prompt_snapshot` attachment records the tools and the
  system prompt actually sent: five bases with the same flags were sent 5, 4, 5, 4, 5 tools — EndConversation (and a
  system-prompt paragraph on it) or not. It is gated by a GrowthBook flag (`END_CONVERSATION_GB_FLAG` in the binary),
  fetched at a session's start in time or not. A fork that drew otherwise than its base read none of it from cache
  (read 0, or only the system prompt's static opening). `--disallowedTools EndConversation` did not take it out.
- **`DISABLE_GROWTHBOOK=1` pins it**: four bases in a row were sent the same 4 tools. Still one hour of cache
  (`ephemeral_1h_input_tokens`), still "Opus 5 (1M context)"; background starts, forks, sandboxed Bash in auto mode and
  the SessionStart hook all worked.
- **With the tools pinned, forks of a base shaped like a real one read it whole**: a base that ran three Bash commands
  before replying (four requests, each reading all before it) was read 14,152 of 14,154 by each of three forks — the
  first in the project with base-settings (how the layer and the warm ping fork), one in a tree with worker-settings,
  one with planner-settings — the sandbox on. So the sandbox is not the cause; a control with it off (its sessions had
  no `sandbox_instructions` attachment; they still called themselves sandboxed) missed the same way.
- **Unexplained, and outside what the harness forks**: forks of a base that made only one request missed its first
  message even with the tools pinned (they read the tools and system prompt, 9.3K of 13.8K), while later forks sometimes
  read an entry the first fork had written. Everything the harness forks — bases, layers, the knowledge base, sealed
  sessions consulted — has made many requests.
- The session listing says `busy` from a fork's start to its reply, never `idle` before its first request: base.sh
  layer and warm wait correctly.

**The fix**: `"DISABLE_GROWTHBOOK": "1"` in the env of base-settings.json, worker-settings.json and planner-settings.json
(background sessions take no environment but their settings'). A FormTests test holds it in all three and holds the
roles to those three files; a mutation case (removing it from worker-settings.json) is caught. README says why.
Flag-gated behaviour runs at Claude Code's built-in defaults in harness sessions. Not committed.

**On the rebuild**: `base.sh high layer` is the high base's first fork. Its cache read is the first confirmation on a
real base; it is not logged by base.sh, so read the layer's first request in its transcript
(`session_fork_check.py <layer sid> <base sid>`). A real base's load also shows whether the server gives these
sessions more than 200K of context (the model attachment says 1M either way).

**Inside the sandbox `claude agents` shows only part of the listing.** At the rebuild `base.sh high build` (the owner's
terminal) refused: "a session named high-base is already live". From inside the sandbox `claude agents --json` listed
two sessions and no high-base; `~/.claude/jobs/*/state.json` held `add75d4d` "high-base" **running** (today's 16:38
base, its transcript deleted at 16:41 — `seal`'s stop did not show in its record), `32f9c132` "high-base" done and
`d8d698d0` "max-layer-163828" done. Most likely the sandbox's block on Unix sockets keeps the CLI from the background
daemon, and it falls back to a partial view. So anything run inside the sandbox that reads the listing
(`session_row.py`: sessions' `v2.py` commands, the owner's session) may miss live sessions; the supervisor, outside,
sees them all. The three are to be removed from the owner's terminal (`claude stop ID; claude rm ID`) before the build.

**Confirmed on the real high base (19:33).** `8956b113` (272,609 loaded) and its layer `5e77c3b9` (524,838) were both
sent the same 4 tools and no EndConversation in the system prompt (their `prompt_snapshot`s); the layer — the base's
first fork — read 272,607 of 272,609 from cache on its first request. More than 200K loaded: the 1M context holds with
the flags off. Meanwhile `seal` had started the keep-warm daemon, which pinged the max layer record `d8d698d0` (its
transcript recreated at 17:52 with only 33 records, a context of 10,058) and missed, writing 46,026 for nothing; the
max and xhigh records were dropped (`base.sh WHO drop`, which starts nothing and runs inside the sandbox) so that no
further ping goes to them before they are rebuilt.

**Max (19:37–19:49).** The base `3fc4a466` (346,336, 4 tools) and its layer `f6f803b6` (481,129, 4 tools; read the
base 346,334 of 346,336 on its first request). `base.sh max layer` refused to record the layer: all four chunks had
arrived and the layer replied its 64-character pack id with one character wrong (`…52a4a4ec…` for `…52a4e4ec…`).
Loading it again would have written 135K, so, at the owner's word: `check-load` accepts the id with one slipped
character once every chunk has arrived (`base_pack.acknowledges`; the chunks are what is checked exactly), and
`base.sh WHO layer --adopt NAME PACK` records a layer session that loaded and was not recorded — the same steps as a
new layer's, now one function `seal_layer`, and only a fork of the recorded base (`session_fork_check.py --is-fork`).
Tests: the slip (one accepted, two refused, an acknowledgement before the chunks refused) and an end-to-end adoption
against a fake `claude` (a non-fork refused, the fork recorded and stopped, nothing loaded); three mutation cases,
caught; 461 tests pass. The owner adopted the max layer (`max-layer-193733`, sealed 19:49:18). Not committed.

**Xhigh (19:51), and all three built.** The base `41c05529` (272,714) and its layer `7c3c2e87` (506,488), both sent
the same 4 tools; the layer read the base 272,712 of 272,714. So: high `8956b113`/`5e77c3b9`, max `3fc4a466`/`f6f803b6`,
xhigh `41c05529`/`7c3c2e87`, every one with the flags session-flags gives, every layer reading its base at 99%. The
daemon runs (heartbeat fresh) and pings only these; `state/stopped` stands and `state/no-launch` is gone. Left: the full
mutation check (not run whole since today's changes), the commit at the owner's word, and `start.sh --fresh` from the
owner's terminal.

**The full mutation check, then the stable bases' warmth (~20:05).** All 245 cases caught (312 s; every file
restored). The daemon pings only layers (`base.sh warm` forks the layer when there is one); whether reading a layer's
entry keeps the stable base's own shorter entry alive — needed by every layer refresh, a fork of the base — was assumed
in the code and never measured, and today's probes suggest an entry exists only where a request ended. At the owner's
choice it is measured rather than paid for: `seal_layer` runs `session_fork_check.py` on each new layer against its
base and writes `layer WHO: OK|MISS …` to warm.log (and prints it); `health.py` names such a miss as a layer that wrote
its base cold, not as a keep-warm miss. A test in each place, two mutation cases caught. If refreshes miss, the choice
is a ping of each stable base besides its layer. Not committed. The load lists high and xhigh were rewritten by the
owner's layer builds (`select_base_load.py --frontier`), as every layer build does.

**The run started (20:05), and two fixes from it.** `start.sh --fresh` (the owner) put tasks 22, 46 and 50 — completed
in the graph with their work unlanded — back to checking through `reopen_unlanded`, which the graph's hold did not gate
(the hold stops task sessions only); their three finalizers started in one second, each counted no Isabelle run (none
had started one yet) and ran three checks at once against ISABELLE_MAX=2: load 96 on 32 cores. All three failed with
"Host tests failed" (the tools suite, one error or failure each); the tools suite passes alone (201 tests, 4.5 s), so the
failures are the load's, not the tasks'. Fixed at the owner's word once the checks had ended: finalizers decide under a
lock and a run let start counts until its finalizer ends (`v2.isabelle_admitted`, `finalize.admitted_no_more`, within
`isabelle_runs()` so every gate sees it); the reopening marks its finalizer held while the graph is held
(`held_finalizer`), `release_held_finalizers` starts it once the hold is gone, and the watchdog does not give up a held
finalizer. Two tests, five mutation cases caught. The three tasks stand as the failures left them (22 fixing, 46 and
50 parked on 22's tree): a fix of task 22 would fix nothing; the owner decides how they are rechecked. Not committed.

**The recheck, and the planner's batching (20:18–20:45).** At the owner's word tasks 22, 46 and 50 went back to their
checks held with the graph (`held_finalizer` set by hand, an event to the planner saying the 20:11 failures were the
load's). The owner declined a ping of the stable bases: when their own entries expire (about an hour after their last
direct read), a layer refresh pays one cold write of the base, and warm.log's `layer WHO:` line will show it. plan-32
(started 20:08) took stock, rewrote the graph in one edit at 20:26 (made 53, 11 rewritten, 2 re-pointed, 52 deleted)
and queued at 20:28:55; the three checks started at once, two were let in (`state/isabelle-admitted/` held 22 and 46)
and 50 waited: 22 passed 20:33:03, 46 20:33:12, 50 20:35:59. The admission fix works, and the failures were the load's.

Read against the batching rules (`protocols/_production.md`, in the planner's prompt), plan-32 batched: 5 reading
requests of 5–7 calls, its 14 briefs in one `change`, the graph in one `edit`. Where it did not, the harness split it:
9 of 13 briefs were cut at 5,000 bytes (5.3–8.4K, their `Planner's:` line at the end), costing three reading rounds;
and its last step took 7 requests (each re-reading ~690K from cache) where 2 do — `drop 52` (its own redundancy, the
edit deletes 52), a script assembling the edit from its drafts refused as a script that writes (its path not literal),
the edit refused on its content (task 48's Deliverable named `tools/`: a fair refusal), a `change` and `again 30` in
one call refused (the call holds nothing else), `again 30` without a heredoc refused although the protocol says "no
block: as it was", then `again 30 <<'EOF'` with nothing in it. At the owner's word, after reasoning each through:
- `v2.py again N` alone runs command N as it was (the AGAIN pattern's heredoc optional);
- `edit` takes `"descriptionFile": PATH` (a draft under `.build/plans/`) in place of `"description"`
  (`edit_descriptions`), stated in the planner's protocol;
- a change and its `again` in one call stay refused — the call must be read as the one command it runs, and a change
  in front would carry a read past the meter — but the refusal and the protocol now say to make them two calls of one
  request, which Claude Code runs in order (measured: the second call started after the first ended) (`AGAIN_ALONE`);
- a brief named whole (`task:ID`, `proposal:ID:KEY`) is shown whole, up to BATCH_BYTES of briefs a call
  (`whole_brief`; files and every other source keep READ_BYTES).
The warning "the guard's rewrite of it through cut.py did not apply" had fired at 20:30:34 on fix-49.3's `v2.py read`
with four `--` groups (each group a read of its own, 15,228 bytes in all): a false alarm; `v2.py read` now has its own
ceiling there (`reads_itself`). Tests: again alone and the refusal, the edit's drafts (read, refused outside
.build/plans/, unreadable, both forms at once, judged as a brief), briefs whole and bounded, the warning. Seven
mutation cases, caught — run on a copy under $TMPDIR (without test_layer.py, which reads the project's THEORY_MAP.md
when it loads), because the mutation check rewrites the harness in place and the run was live. Not committed.

**The other sessions, read the same way (20:50–21:05).** The run's other sessions (fix-48, brief-14, fix-49.3,
investigate-53, brief-10, implement-54, brief-13; kb-6 only loads) batched their reading: several calls a request,
several sources a call, `--` groups (brief-10 read 27K of DECISIONS.md in one call, and three briefs whole in another).
Three things spent requests, about 11M tokens read from cache in all: a `v2.py read` of several sources showed 5K in
all while `--` groups showed 5K each (fix-49.3: five reading requests in 30 s, learning `--` on the third); every
session that wrote lost a request to the form of `change` (a command after it in the same call 3, a `mkdir` first 2 —
`change` makes its directories, which no protocol said —, `cd DIR;` 1); and brief-10 wrote its ten briefs in five
requests back to back, implement-54 probed each change in the request after it. At the owner's word, reasoned first:
- a read bounds each source at READ_BYTES (a brief named whole, whole) and the call at BATCH_BYTES; its `--` groups
  are one call (v2.main) — what READ_BYTES is for, a large chunk read in pieces, is a bound on a source;
- a change out of its form is told what was wrong with the call (`change_form_faults`): a command that needs it is
  a call of its own after it in the same request, no `mkdir` first, a `cd` joined by `&&` (a `cd DIR;` stays refused:
  a `cd` that failed would leave the change writing elsewhere); the protocol says a write makes its directories;
- a request that only changes files or checks, right after one that only changed files (every change gone through,
  nothing read, no mail or job's end between: a `queued_command` attachment or user text), is told that what it
  holds was ready there (`ready_before`, `READY_NOTE`), once a request; a note, not a refusal. Replayed on the run's
  transcripts it is told exactly where found by hand: brief-10 5, implement-54 4, investigate-53 1 (a correction of
  its own result written in the request after it), none in the others.
Tests for each; 14 mutation cases (the batch before and these, two of the earlier rewritten for the new code),
caught, on a copy under $TMPDIR. Not committed.

**Brief 13's proposal, sent back (21:05–21:25).** plan-32 found brief 13's 14-task proposal built for the old harness
(its builds handed over unchecked, one group check at the end; every build now lands by its own check, review and
commit) and told its designer what to change (`v2.py tell 13`, 21:01:19): refused, "no session works on task 13" —
the watchdog had released brief-13 at 21:00:28, three seconds after its result, since a task designer was held only
while tasks it briefed are open and an unplaced proposal has none; and `tell` reached only live or parked sessions. So
it re-planned the brief (drop, rewrite pointing at the old proposal, requeue), and brief-13.2 briefs it again (brief-13
had cost 12 requests, 6.8M read from cache). The planner's account and substance were right; the harness failed it.
At the owner's word, reasoned first: the watchdog holds a task designer while its own brief is `proposed`, within
HOLD_MAX; `tell` on such a brief records the correction (`revise_proposal`), the supporting slot resumes the designer
with it before any review or brief (`revise_now`: the brief `running` again; a designer that cannot be resumed gives
the brief to the planner with the correction), `accept` refuses the proposal meanwhile and the placing reminder is
silent; a released designer is said to be. The planner protocol and the harness's proposal message say `tell` sends
a proposal back. Tests (the round trip; the slot taken; released; cold; the reminder; the hold), seven mutation cases
caught on a copy. brief-13.2 was left running. Not committed.

**The new sessions, read again (21:15–21:30).** Every session started since 20:47 batched its reading (several calls
and sources a request, up to 27 sources; reads after a cut at most two a session; review-23's four single reads at
its end a chain of checks each on the last). The tailored `change` refusal worked where it was given: implement-60
(20:57) and fix-22 (21:05) put the change and its probe as two calls of one request every time after it (6 of 6 for
implement-60); implement-58's refusal (20:50) came before it and was told the form only. The ready note was said where
it held (brief-13 once, design-66 once). The waste left was a defect of `change`: design-66's eight-block change
(21:13:53) had a first block without its `>>>>>>> REPLACE` line; the parser ends a block at its first REPLACE line, so
the first block's replacement took in the second block, markers and all, and they were written into entry.md; five
requests went to repairing it. At the owner's word, reasoned first: a replace block whose search or replacement text
holds a marker line is refused, naming the line it lost (`=======` when the search text holds one, `>>>>>>> REPLACE`
when the replacement does); `=== write` bodies stay unchecked, the way to write a text that must hold such a line. It
is in `change_blocks`, so `change`, `again` and the guard all have it. A test (both losses, nothing written, a whole
file holding markers written), one mutation case caught on a copy. Not committed.

**Why everything parked (21:20–21:35).** No builder ran because the two sessions allowed at once were review-47 and a
consultation (ask-q23, which counts against WORKERS_MAX); and everything parked because HEAD is inconsistent, so no
tree is made, every task works in the one tree, and each finalization holds it while all others park — the run has
been serial since 20:05. The two landings that end it are 22 and 46: review-23 rejected 22 (21:04), whose fix-22 parked
for the tree two minutes later; review-47 rejected 46 (21:24), and fix-46 was stopped by its quick-fix budget at its
eighth request (four single reads, a `cd DIR;` change refused, one probe) with its one-line repair in hand, so 46 went
back to the planner, still holding the tree as its writer. plan-32 queued 46 first and implement-46 started 21:29;
review-50 rejected 50 (21:27, fix-50 parked). The order after 46 is the planner's and was not changed: the harness
resumes tasks parked for the tree longest-parked first (48, 49, 58, 60 before 22), and the planner has no command
that orders parked tasks; plan-32 was told the problem and the proposal (22 next; unstarted builds to wait for 22 and
46 by `blockers`; the owner's word for a harness change that resumes parked tasks in the queue's order, if it asks).
At the owner's word, reasoned first: a rejecting reviewer is held while the task it rejected is unfinished (active
stages as before; parked, with the planner or queued again within HOLD_MAX) — review-23, -47 and -50 were released and
each re-review needs a new reviewer; and a parked quick fix's clock stops while it waits (produce shifts `fix.since`
by the time parked). The owner set the quick fix's budget to 30 minutes and 15 requests (from 15 and 8). Tests and two
mutation cases, caught on a copy. Open for the owner: the quick fix's requests count refused ones too. Not committed.

**No refused request counts (21:40).** At the owner's word, a refused call counts in no limit counted in requests: the
guard records every refusal in one place (`guard` wraps `_guard`), into the stretch's `refused` (the reading tiers,
which counted a read refused early — a removed tool, a malformed `again`) and a `denied` list kept past productions
(the quick fix's count, `rounds_since`, which now leaves out a request whose calls were all refused). The quick fix's
refusal and `_finishing.md` say "requests, a refused one not counted". Tests (refused requests past the budget
uncounted, made ones counted; refused early reads leave the tiers at one), three mutation cases caught on a copy; the
wiring test reads the removed tools' refusal in `_guard`. Not committed.

**The deadlock of 21:37, and the parked order (21:38–21:50).** From 21:37:13 nothing ran: task 46's fix passed its
check and stood `reviewing`, but no review started — plan-32's re-plan (`v2.py queue 46`) had rebuilt 46's record
keeping four fields and dropping `rejections`, which then read 0 against review 47's round 0 (`pending_reviews`), so
the re-review read as done; 46's finalization held the one tree and nine tasks stood parked. At the owner's word,
reasoned first: `queue` keeps a re-planned task's `rejections` (its review history pairs with its review tasks'
rounds); 46's count was restored to 1 by hand (21:41:35) — review-47 was resumed, accepted, and 46 committed as
7b4bb54f (21:42:44); and `returned_tasks` names a finished build or fix in review with no review due and none
running, after STALL_AFTER (5 min), as ATTENTION and to the planner. Then the parked order, as proposed and approved:
`resume_order` — a hold within PARK_URGENT (45 min) of its end first, then the planner's queue, then what it does not
name, longest parked first; the status line lists them so, the planner protocol says it ({PARK_URGENT}), and plan-32
was told (its Q8 answered; 50 not in its order). fix-22 took the tree when 46 landed, being the tree's writer. Tests
and six mutation cases (one first missed — the urgent task was also the oldest — and the test made to tell the orders
apart), caught on a copy. Not committed.

**The sessions after the last changes, and the trees back (21:45–22:00).** Reading stayed batched (review-47 read 25
and 18 sources in single calls). Every new session lost one request to the `change` form (implement-68, fix-46,
fix-50, implement-46): three led with `cd <the project>;`, three put a command after the change; ask-q23 had two
valid `again` calls refused for giving its runner by path (`/usr/bin/python3`); and implement-68's change and probe in
two requests went untold, because the recorder looked for its call's request without waiting and a background probe
returns before its line is written. At the owner's word, reasoned first: the runner by path and flags in the forms of
`change` and `again` (RUNNER_ARG); `cd DIR;` accepted when DIR is the session's own directory (`own_directory`),
refused and named otherwise; the protocol says at the form that the call holds only the change; the recorder waits
for its call's line (BATCH_WAIT), once, for the note and the batch's bytes alike. Tests and four mutation cases, caught
on a copy. Meanwhile task 22 was checked (21:47:13), re-reviewed by review-23 resumed, and committed as 612ee5a9
(21:48:02): HEAD is consistent, and task 24 was started in a tree of its own (.build/trees/24, 21:49:10) — the first
tree of the run. fix-48 resumed first among the parked (the planner's order) and holds the machine for its replay.
Not committed.

**`v2.py read` crashed on a cut read partly in context (22:00).** review-23 (21:01, `v2.py read DECISIONS.md:9600-9659`)
and the planner got a TypeError from `work_meter.gaps`: when a source is cut at READ_BYTES and some of its lines were
in context already (two overlapping sources of one read, or a range read before), file_read passed gaps() the lines
shown as lists and those left out as tuples, which sorted() cannot order. Reproduced both ways in a fake world; gaps
now reads each range as a pair of ints, whatever its form (the meter's JSON gives lists, gaps itself tuples). A test
(both ways: the rest shown, the lines in context named, the cut said), one mutation case caught on a copy. Not
committed.

**fix-48 and implement-24 (21:48–22:05).** Both batched reasonably; implement-24 has the first tree of the run and
worked in it without harness trouble (a detour through a scratch copy of DECISIONS.md cost two requests; two small
independent reads were one request each). fix-48's replay launch failed on a missing /usr/bin/time (the machine's,
not the harness's), and its edit of commit.md was refused as a git command: its text named `git rm --cached`, and the
git, waiting and job-output checks read the raw call, a change's text included. At the owner's word, reasoned first:
those checks read a `v2.py change` without its heredoc text (data written to a file, never run); what the call holds
outside it, and every other heredoc, is still read. A test and one mutation case, caught on a copy. Its retry was
refused for `cd <the project>;`, three minutes before own_directory went live. implement-24 was not told that its
small single reads each cost a read: every read gets the same countdown, whatever it held. Not committed.
At the owner's word, then: a reading request right after one that showed under SMALL_READ (2,500 bytes) is told, once
between two productions, that the earlier one cost a whole read (`small_read_before`, looking back one request as the
ready note does, since a call cannot know whether more calls of its request are coming). A test, two mutation cases
caught on a copy. Not committed.

**Isabelle in runs, and a park for the machine (22:10–22:20).** implement-78 (q26 to the planner) had only its probe
left, refused seven times in forty seconds as "11, 10, 9, 7, 3, 2, 2 Isabelle runs are going" while at most two were:
`isabelle_runs` counted poly processes against a limit in runs, and one run makes several; and no park reason fitted,
so it asked. (The planner answered: hand over, the landing check proves the theory first.) At the owner's word,
reasoned first: runs counted by the outermost probe/check/replay/build/Isabelle tool among a poly process's ancestors
(`isabelle_run_roots`; unknown ones count alone); one condition for a run (`run_blocked`: another's measurement, or
ISABELLE_MAX runs) for the guard and for `v2.py park machine`, whose session is resumed when a run may start; the
refusal says to park rather than to try again, and the protocols (_checks, _tree) say so; the watchdog writes the
machine's Isabelle processes with their runs to state/isabelle-processes.json. Its first snapshot (22:15:36): two
checks (78's in its tree, 50's), each one run rooted at check_errors.py, one poly each in their recipe phase. Tests
and five mutation cases, caught on a copy. Not committed.

**`park machine` in the sandbox, and two run limits (22:15–22:35).** implement-24 (q27) was told by `v2.py park machine`
"a run may start now" and then refused four times: the command runs in the session's sandbox, whose process
namespace shows no Isabelle. Fixed, reasoned first: a sandboxed park parks without judging (the dispatch, outside,
resumes it), and inside a sandbox the count is the watchdog's snapshot (written every pass), a stale or missing one
counting the machine as full. Then the owner: probes take tens of seconds at most and 8 may go at once, the limit of
2 being for full builds. The review: every ordinary probe took 3-4 s; the long one was implement-24's (21:58:55,
`--timeout 900`, one theory, hung at a `have` 3 s in, killed at 900 s, holding a run slot — part of why implement-78
was refused); task 7's long ones (09-20) were engine measurements; checks take 164-272 s. Made, reasoned first: two
kinds and limits (`run_kind`, `isabelle_load`, PROBE_MAX 8, ISABELLE_MAX 2 for heavy runs, unknown tools heavy); a
probe names `--timeout 60` at most (PROBE_SECONDS) unless measuring, said with the machine's refusal in one message;
the finalizer's check waits for a heavy slot, a base advance for no run; a park waits for the kind it was refused;
the snapshot gives kinds and memory (a heavy check's main process 7.5 GB — a probe's is still to be seen, and 8 of
them beside 2 heavy runs fit only if a probe is far lighter). The planner was told, with a proposed task for the probe
tool (default 60, report the command a timeout stopped at) after task 50 lands. Tests (the guard's older probes now
name a limit) and 9 mutation cases, caught on a copy. Not committed.
Then, at the owner's word: no run starts while the machine's available memory (MemAvailable, readable from a sandbox
too) is below MEM_MARGIN_GB, 10 GiB (`memory_short`, in `run_blocked` — the guard and a park for the machine — and in
the finalizer's wait), whatever the counts allow; unreadable memory blocks nothing and is said once. The machine: 60.4
GiB, 89 GB swap, 32 cores; 39 GiB available with one heavy check running. The snapshot records the memory available.
Tests (the fake world and the finalizer's tests state the memory), three mutation cases caught on a copy. Not committed.

**The sessions after the two limits (22:35–22:55).** Batching held (reviewers up to 28 sources a request; the notes said
where they held). Harness faults found, and fixed at the owner's word, reasoned first: plan-32's ledger question was
refused as a git command for its quoted text (`harness_only`: a call of harness commands only carries its quoted words
and heredocs as data, unless something runs from inside a quote); fix-48's finalize refused the tracked
tools/__pycache__/build.cpython-314.pyc as exempt and ignored (a path HEAD tracks is the repository's: `v2.py
finalize` takes it, `finalize.stage` stages it with `add -f`, or `rm --cached` when gone — `git add` refused both;
the harness's own paths stay refused) — the obstacle of plan-32's Q9 to the owner; fix-48's `again` correcting its
change was refused by the marker check (off for corrections); `change` then `v2.py result` in one call cost a request in
most sessions (the harness's inert commands may follow a change, rewritten to run only if it went through); and 3 s
probes run in the background cost three requests each for implement-78 (the checks protocol: a probe in the foreground,
after its change in the same request; heavy runs in the background). Tests and seven mutation cases, caught on a copy.
Not committed.

**Every tree session was told its whole load was stale (22:55).** review-79 got "stale since xhigh load … (664): …" of
the 362 files the xhigh load holds: `manifest.py changed` compared the recorded absolute paths (the one tree's) with
the tree's own, so every file read as changed and again as new — for every session in a tree since trees came back at
21:49. Fixed: files compared by their place in their own tree (`changed_since`, ONE for the record, the tree for now);
tree 79 now reads 6 (the tools 48 and 50 landed, the plan 49 did, two regenerated indexes). A test and one mutation
case, caught on a copy. Not committed.

**The four fixes of 22:55, finished in a new session, and every rule taught before it refuses (23:08–23:35).** The
session above was cleared mid-way through the four fixes the owner had approved ("reason whether the changes are
adequate and coherent and then fix it, yes I want to increase the hold"); this one read its transcript and finished
them, each reasoned again first:
- *The stable bases pinged* (`base.sh WHO warm stable --if-due`, run by the daemon for each base under a layer, 40 to
  55 minutes after its last read; its own mark `state/WHO-stable.hit`; `health.py` reports it apart). Its test failed
  on the fake `claude`, which listed its fork only as `warm-max`. Corrected on the way: a fork that misses does not
  make the stable base's entry again — the max refreshes of 22:25 and 22:40 both read 9,270 and wrote 339K, fifteen
  minutes apart — so only a layer that read its base from cache marks it warm, and the mark the session above had set
  by hand (`max-stable.hit` at 22:40) was removed: every stable base's own entry has been gone since about an hour
  after its layer was built (19:33–19:51), and only a rebuild makes one; the pings keep it from then on. **The daemon
  runs the old loop** (a shell loop is read once): the stable pings start when the owner restarts it.
- *The file lock in a task's own tree*, adequate only with the landing: an own-tree task lands by a merge into the one
  tree, which git refuses over a working change there. So: no lock of the one tree's files for a finalization in a
  tree (`locked_files`); an own-tree commit is not refused for another task's one-tree work (`unreviewed_work` — the
  false refusal of task 24 at 23:02:10, for task 54's THEORY_MAP.md, which 54 committed at 23:03:06; implement-24 was
  released and 24.2 started from nothing); the landing waits, before it holds main and within the commit's budget,
  for the one tree's uncommitted changes of the files it writes (`one_tree_changes`), refused past it as what it is;
  what came between is named as standing there (`merge_refused` with its own text); and a commit standing on its
  branch lands as it stands when made again (a commit of nothing failed).
- *The probe rule*: the probe tool's default became 60 at 23:02 (bba91b39, task 50), so the guard reads the default of
  the tool the session runs (`probe_default`: trees 24 and 80 still hold 1200) and lets a bare probe go where it is
  60; `_checks.md` states the bound.
- *The hold*: 6 hours for a task parked for the one tree (`HOLD_TREE`, `hold_of`: the watchdog, the park's message,
  the resume order, the status), 3 for the rest; the wake names what the session waited for (it said "the fix" to
  every park). Not changed: a rejecting reviewer is held at most HOLD_MAX (3 h) while its task's fix may wait 6 for
  the tree, so a re-review after that needs a new reviewer.

Then the owner: "do 4 for others" — teach every rule the guard enforces in the protocol of every role it reaches. The
audit (each refusal of `work_meter`'s guard against each role's composed protocol): the rules held over every session
but the knowledge base (no git mutation, the harness's files, its scripts other than `v2.py` and `show.py`, no
waiting, subagents or sessions) were stated to the producing roles only, or nowhere — now `_production.md`, which
every guarded role gets (the planner's and task designer's own lines trimmed); the machine's limits were in
`_tree.md`, which reviewers do not get — now `_checks.md`; HANDOFF.md and PLANNING_LOG.md as the planner's — now
`_result.md`; the marker-line rule of `change` — now `_production.md`; a consultation of the knowledge base, the
planner or a task designer is guarded to statements and was never told — now `{READING}` (`STATEMENTS_READ`). And one
the audit found undoable: a reviewer refused a run for a full machine was told to park, which is refused to it, and
`may_end` would not let it end its turn — it could only retry. Now it ends its turn (`machine_wait`: the guard's
refusal, cleared when a run of it is let through), the watchdog wakes it when a run may start, and `park machine`
tells it so. A form test holds every guarded role to the rules; 20 mutation cases, all caught on a copy (the check
now takes `MUTATION_ORCH` and case keys). Not committed.

**Can a base still be written cold? (23:37–23:50).** The owner restarted the daemon (pid 2098968, 23:37:32; its loop
holds the stable pings) and asked to check that cold caching can no longer happen. It can, in these cases, and one is
certain: every stable base's own entry is gone (their last reads were the layer builds of 19:33–19:51), and nothing
but a rebuild makes one again — each fork's first turn carries the fork's own session id (the sandbox's instructions
name its task directory; the two max refreshes' first turns differ only there), so no fork, whatever its first
message, writes a prefix a later fork reads beyond the base. So the next refresh of each layer writes its stable base
cold (max about 339K, xhigh and high about 273K; xhigh's layer stands at 16% of its 20% threshold), and a rebuild of
the base costs about the same while leaving an entry the daemon keeps. After that, an entry goes cold only while the
daemon is down for its hour, when its base is unused for 12 hours, or after two missed pings. One change: a missed
ping took itself as a read (the mark touched), so its retry came forty minutes on, when the entry was surely gone; it
is now counted only, and the next pass tries again. A test and a mutation case. Also: 19 cases of the mutation check
had anchors the day's later changes had rewritten (18 before this session, one of its own), so they broke nothing;
they are re-anchored to the same repairs. Not committed.

**A cold stable base is loaded again by the refresh (00:00–00:30, the owner's "2").** Given the choice (rebuild the
three by hand; let a refresh that finds its stable base cold rebuild it; leave every refresh cold), the owner chose the
second. `base.sh WHO layer` now loads the stable base again first when its entry is cold (`stable_warm`:
`WHO-stable.hit` within WARM_MAX), as its own step `base.sh WHO restable` (`rebuild_stable`): a fresh load of the
stable part of the list as it stands now, under a new name, recorded in `WHO-base-next.json` with its snapshot in
`WHO-manifest-next.json`, while the base and layer standing serve. The layer is then a fork of that base, and
`seal_layer` puts base and layer in place together, two renames apart; before that, `keep_stable_snapshot` merges the
old stable snapshot into the kept snapshot of every layer a session still holds (and every new layer's kept snapshot
holds its stable part), so a session forked before is still told what changed since the load it has. A base loaded
again for a layer that did not seal is reused while warm; `layer --adopt` takes a layer over it. Found on the way: the
hourly tidy swept every pack no sealed base names — so the pack of a layer or base being loaded could go mid-load (the
max layers' packs of 22:24 and 22:39 went at 23:06, after their seal); now the packs of loads in progress and any pack
younger than 3 hours stay. The xhigh layer, at 16% of its 20%, is the first it will meet. Tests (the rebuild and the
swap end to end against a fake `claude`; the tidy), six mutation cases caught. Also fixed: two mutation cases named a
test renamed later (they ran nothing and read as missed), and the recorder-wait test slept less than its hook took to
start, so it held nothing; all 345 cases are caught. Not committed.

**Task 24's and task 80's landings, and a task that came back (00:05–00:40).** The owner relayed plan-33's finding
("#24 was stuck because a rewritten brief alone does not restart a task that has come back to me; it has to be queued
again") and asked which of these problems are fixed, still open, or not the harness's; then, after the review below:
"review the fixes and if they are coherent and adequate apply them". Traced in the log, git and plan-33's transcript:
- task 24's first refusal (23:02, another task's one-tree work) was fixed above; its landing then waited for task 58
  (23:22–23:29), as meant;
- its second failure (23:29:03): main had changed Development_Loci's row (task 79 added an import) and task 24's branch
  added its row just below; union kept both versions of the changed row and the commit gate refused the merge.
  Fixed: the merge of main into a branch is made without committing, THEORY_MAP.md rows and ROOT's theory lines are
  agreed by their theory as a three-way merge does (`finalize.agreed`, `rows_agreed`; on task 24's real merge: one
  Development_Loci row, main's, and its own row kept), then committed through the gate;
- that refusal was said as lines "written in the same place by another task", git's text cut to its last 300
  characters. Fixed: a gate refusal says what the gate found, whole, and to queue the task (`gate_refused`);
- task 80 (00:00:55): its landing waited for task 68 as meant, then during its five-minute landing check task 66 wrote
  DECISIONS.md in the one tree, and the check before the merge refused it to the planner — a hole this session's
  removal of the file lock opened. Fixed: the landing hands back what came to stand, and the finalizer lets main go,
  waits for it and lands again (`stood_for`), within the commit's budget; past it, the task is marked (`lands_again`)
  and `v2.py queue` makes its commit again with no session. The planner had already re-queued task 80 as a session;
- a task that came back moves only when queued, which neither the protocol ("re-plan it") nor the 30-minute notice
  said, and plan-33 rewrote task 24 at 23:30 and queued it at 23:59. Fixed: the protocol and the notice say it, and an
  `edit` that rewrites such a task says so at once; nothing queues it by itself, the order being the planner's;
- not the harness's: plan-33's `tell 80` reached the reviewer (the fixer had handed over; the reply named it); Q11.
Tests for each (landings against the one tree, the rows, the gate's text, queueing a commit again, the edit's reply,
the notice, the protocol); ten mutation cases, and three older ones re-anchored to the changed code. Not committed.

**Task 56's install past the tree's holder (00:45–01:00).** Relayed by the owner: while task 66 held the one tree
(reviewing), implement-56.2's `v2.py change` of ROOT was refused, and its next call — `for f in …; do cp
.build/tasks/56/draft/$f.thy theories/$f.thy; done` — went through: three theories changed and
`theories/Development_Entity_Keys.thy` new, undeclared in ROOT, so the one tree refuses every check. The guard read the
loop's command as `do` (the write test wanted a writer at a command's start, and the command splitter took `do` for
the command), so it saw no write at all; any file command in a loop or a condition escaped it, and the planner's
statements-only reading the same way. Fixed: shell keywords are read through (`SHELL_KEYWORDS` in `segments`, and
`WRITE_SHELL`). Its revert was refused rightly (its `rm` named a tree file), and the originals it names under
`.build/tasks/56/orig/` do not exist — that call never ran; the three are HEAD's, and the new file's copy is in its
drafts. Also from its transcript: its question to the planner was refused as a change out of form because its quoted
text named `v2.py change`; a change is now read from the command's syntax, quoted words out. Tests and three mutation
cases. The one tree still holds the partial install (no task owns it); restoring HEAD's three files and removing the
new one is the owner's call. Not committed.
At the owner's word the one tree was restored (00:20): HEAD's three theories, the new file removed (its draft kept);
`git status` clean there, no tree trouble. Task 56 was told (`v2.py tell 56`: skip the restore step of the planner's
q30 answer, whose `orig/` does not exist), and the planner by an event from the owner (the restore, the guard fix, and
tonight's fixes not in the protocol it holds: a returned task moves only when queued; a landing waits for the one
tree and `queue` re-makes a marked commit with no session; one-sided row changes merge to one row). The full mutation
check: 353 of 355, the two misses tests that no longer pinned their repair (the wait before the landing, now also
covered by the wait inside it, saves a landing check — pinned so; the gate's finding — its boilerplate asserted out);
with those and the guard's three cases (one re-anchored on the form check that refused task 56's question), all 358
are caught. The suite: 521 pass. Not committed.

**The sessions after 22:55, read (00:30–01:10).** At the owner's word ("check all the new sessions for harness
issues"): 17 sessions (8 implementers, 2 fixers, 7 reviewers), 35 refused or failed calls, read one by one. Harness
faults, fixed:
- `git merge-base` was refused as `git merge` (`GIT_MUTATE` ended in `\b`, which a hyphen satisfies): four requests
  in four sessions (implement-24.2, -24.3, review-25.2, -25.3);
- a check was any command naming a check's tool: `grep … tools/incremental_check.py`, `sed … probe_theories.py`,
  `probe_theories.py --help`, a script reading a check's output directory — refused while the machine was full (six
  requests: fix-81, implement-56, fix-80.2). Now what a command runs (`runs_check`: the tool as the program, by a
  runner or by path, after `timeout`/`env`/…; `isabelle build|process|ML_process`; not `--help`); replays count as
  checks here too, as they do in the machine's count;
- `cp`'s sources were counted as written: `cp theories/A.thy … .build/tasks/56/draft/` was refused as a write into the
  held tree (two requests). Only the destination (or `-t DIR`) now;
- writes under .build/ behind a leading `cd DIR &&` or a plain variable (`W=…; … > $W/x`) were read as written into
  the session's tree (fix-80.2, four requests): both are followed now (`shell_context`); a script's target handed to
  it as an argument still cannot be read, and its refusal now says so;
- `v2.py measuring` after a change was refused as out of form (implement-56, twice): it reads nothing, and may follow;
- an `again` correction of a change, as the protocol says to make one, holds the change's own heads and blocks, and
  was read as further changes (implement-72): a correction is now read to its end, its markers nested (`marker_at`);
- two keep-warm pings gave no verdict (`session_fork_check` failed — the fork's transcript not found, cause unseen:
  each ping deletes its fork) and each session went cold ten minutes later, its whole context lost (fix-49.3 at 22:11,
  implement-56 at 00:09): the retry was held off by the ping's ten-minute mark. A ping with no verdict now says why,
  and sets its mark back so that it is tried again in two minutes; each ping's fork has a name of its own.
Not harness faults: reviewers and fixers reading a job's output after parking (refused, rightly); reads over 5K
(told what fits); a SEARCH that did not match; real writes into a held tree (refused, rightly); a heavy run refused
with three going. Open for the owner: a check put after a change in the same call is refused by design (three of the
17 sessions did it; the protocol says two calls), which the guard could instead judge as the check it is. Tests for
each; ten mutation cases. Not committed.

**A change and its check in one call; design 66 and review 67; the build directory (01:00–02:10).** At the owner's word:
- *A check after a change, in its call* (`change_then_check`): a change followed by one check line (and what filters
  its output) is judged as the check it is — the probe's bound, the machine's limits, a failure's repeats, gathered
  and cut as a check — its change as the change it is (write guard, form, the task's files), and the check runs only
  if the change went through (`STATUS_LINE`). A read after a change is still a call of its own. `_production.md`,
  `_checks.md` and the change's form refusal say so.
- *Design 66 waited half an hour after the planner accepted it* (00:04 to 00:31), the harness answering "its other
  reviews are pending": review task 67, deleted from the graph, which no reviewer would ever take — a design's reviews
  are the planner's verdict alone. `deciding`: a build's or fix's review tasks count while the graph holds them
  (`held_reviews`, in the verdict, `pending_reviews`, the stall check and the completion); a design's or an
  investigation's verdict decides alone, given on it or on a review task of it, and its review tasks go with it.
- *More from the newest sessions*: investigate-82's `mkdir`/`grep "…shutil.copy…"` was read as a script that writes
  (the pattern as code): a script is looked for only where an interpreter runs (`runs_script`, `programs`); its
  change followed by `v2.py ask "…; …"` was refused as out of form (the tail stopped at a quoted `;`): quoted words
  are read whole; implement-62 was told no command number with the tree holder's refusal and corrected the wrong
  commands: the tree holder's and the file lock's refusals now name it (fixable).
- *Batching, sessions since 22:50* (23 sessions, 355 requests, 1.5 calls a request): reviewers read 8–17K a reading
  request, implementers and fixers 2–5K; 68 of 170 reading requests showed under 2.5K, 21 right after another. Most
  of those pairs were retries after the misread refusals fixed tonight, the rest lookups each needing the one before;
  fix-80.2 (a measurement, 70 requests at 1.0 calls) is the outlier. Writes: 49 calls made one change alone.
- *The build directory, 131 GB*: 46 check outputs of about 3 GB each (recipes 2.6, exports 0.5) and 36 GB of checks in
  tasks' directories; nothing removed any of them. The tidy now removes a check output once every task naming it has
  landed or left the graph — not the newest of those (`retain` reads the last landing's), nor one a task in flight
  names, nor one no task names younger than 3 hours, nor anything but a check (`.build/check-*`, and `check*`,
  `landing-*`, `final-check*` in a numbered task's directory — a base being made under `.build/tasks/base-advance/`
  is none). Dry run on the live state: 47 outputs, 108 GB, at the next hourly tidy.
Tests and mutation cases for each. Not committed.

**A turn the API broke off (01:00).** investigate-82's reply ended in "API Error: Server error mid-response" (00:54:46);
the watchdog would have resumed it after five idle minutes and the ten-minute backoff of loops (about 01:03:45), told
only that its turn had ended. At the owner's word: `api_failed` resumes a session whose last reply is such an error
after a minute (`API_RETRY_AFTER`), saying the reply may be incomplete and to redo the step, up to three times in a row
(`API_RETRIES`, counted in `state/api-errors-NAME`, cleared by a reply of its own), idle or listed as blocked (a blocked
row counted as gone). It resumed investigate-82 at 01:02:54 on its first pass. Also: two mutation cases had tests my
earlier changes had made blind — the recorder's unwrapping (the guard now reads through the cut's wrapper, so only a
check, hidden in check_errors.py's `bash -c`, shows it: pinned so) and "a pattern naming a writing call" (its test's
targets were all under .build/: now one outside). Not committed.

**The one tree emptied, and a measurement queued (01:05–01:30).** At the owner's word, reasoned first:
- *Placement*: a task was put in the one tree when its brief named a path standing uncommitted there — and nearly every
  brief names THEORY_MAP.md or DECISIONS.md, so while one task in the one tree held a row uncommitted every task
  started was put there too (56, 62, 72; the one tree never emptied, and most of the night's trouble came from it).
  `in_main_tree` no longer counts `SHARED_FILES` (ROOT, THEORY_MAP.md, DECISIONS.md, HANDOFF.md, PLANNING_LOG.md); a
  task whose own work stands there, or whose brief names another uncommitted file, stays. What made it coherent: with
  no task in the one tree, nothing would have committed the planner's HANDOFF.md — a landing's merge (`merged`) now
  takes it, as a commit made in the one tree did. DECISIONS.md still merges by union; an amendment beside another's
  entry is caught by the gate, not agreed.
- *Task 56's measurement*: parked for the machine, it was woken when a heavy slot was free, claimed the machine for a
  fifteen-second timing, and was refused, other runs going — three times (it then asked the planner, who let it
  measure unheld, alternating the two forms in one run: q32). A claim made while runs go is now queued
  (`pending_claim`): no new run of another task starts (`run_blocked`, and the finalizer's admission), and once the
  machine is empty the claim is the session's — by message (`grant_pending`, in the dispatch) or with its resume if it
  parked for the machine (`parked_ready`, `produce`), for at most `PENDING_MAX` (30 minutes) of waiting or while its
  session stands. `_tree.md` says so; the planner was told (an event from the owner).
Also: a mutation case whose test gave a base a `recipes` file instead of a directory; and the fix of the review count
(a review task counts while the graph holds it or once it has judged — a finished one left the graph and blocked a
commit in a test). Tests for each; the full mutation check and the suite run on the copy. Not committed.
Verified at 01:30: the full mutation check caught all 391 cases (on a copy), and 533 tests pass. The owner then left the
run to be monitored: the stop, if needed, is a request to the supervisor (`v2.want(run=["v2.py", "stop"])`, carried out
within seconds — tested with `status`), then `state/stopped`; running checks and finalizers finish by themselves.

# STANDING INSTRUCTION (the owner, 2026-09-22 ~01:35): monitor the run, never stop, through compaction

The owner left the run to this session: "keep doing the work we have been doing together — looking at the sessions,
diagnosing problems, fixing and repeating. Make sure you keep going through compaction, make sure you never stop
monitoring." Also: "add stuck investigations to your review loop", and stop everything if something goes wrong.

**The loop, kept up without end:**
1. A Monitor on `state/v2.log` and `state/warm.log` for problem lines (ATTENTION, went cold, lost, failed, refused
   commits/landings, stood/waited, given up, inconsistent, MISS, stable/layer lines, not resumed), `grep -v "protocol
   has no value"`. It expires every 30 minutes: re-arm it at once on its expiry notice.
2. Every ~25 minutes a review (a background `sleep 1500` as the timer; on its completion run the review, then arm the
   next timer): `python3 -B notes/session-review.py` (since the last review; mark in $TMPDIR/session-review.since) —
   each session's refusals, errors and batching, the log's anomalies, keep-warm, bases, disk, the one tree; plus stuck
   work (tasks parked long, stages unchanged long, sessions resumed repeatedly — to be added to the script).
3. Each harness fault: reason whether the fix is adequate and coherent, write it with a test, add a mutation case
   (run on a copy: `MUTATION_ORCH=$TMPDIR/mut/p/.claude/orchestration python3 -B notes/mutation-check.py KEYS`), run
   the suite (`python3 -m pytest -q -p no:cacheprovider test_*.py` in .claude/orchestration, background), update
   README and this note. Never commit (the owner's word is needed). Tell the planner by an event from the owner when a
   change alters what it should do (`with v2.state() as w: v2.event(w, "the owner", text)`, then `v2.kick()`).
4. Stop everything only for ongoing damage (runaway spending — repeated cold rewrites, resume loops; repository damage
   — HEAD inconsistent, unreviewed commits, conflict markers; the harness failing repeatedly; memory or disk out):
   `v2.want(run=["v2.py", "stop"])` (the daemon carries it out within seconds; tested), then write `state/stopped`.
   Running checks and finalizers finish by themselves; `start.sh` (the owner's terminal) resumes.

**Open at this handoff (01:40):**
- Just made: authors are no longer held to be asked (`watchdog.held`: the task designer's "tasks it briefed are open"
  and the designer's "tasks built on its design are open" removed; the proposal-wait hold stays). Test added;
  `test_what_nothing_refers_to_is_released_and_what_may_come_back_is_held` fails — it expected a held author: update
  it, add a mutation case, run the suite.
- The owner asked: what happened to task 56 (parked on q32, then running without the hold; check its state and
  result), and to add stuck investigations to the review loop (extend session-review.py).
- session-review.py's keep-warm section printed old traceback lines (continuation lines without a timestamp pass the
  date filter): fix it.
- implement-76: `perl -0pi` on its own `.build/tasks/76/runprobe.sh` was refused as an in-place edit — write_targets
  reads `sed -i` targets but not `perl -i`'s, so the target under .build/ was not seen: fix. Its three `change` calls
  refused as out of form (22:27:05, 22:27:58, 22:28:10 UTC): see what followed each (a probe run through its own
  wrapper script is not recognised as a check).
- Disk: 919 GiB free after the sweep removed 108 GB (926 before): the space may be held by filesystem snapshots
  (Timeshift) — report to the owner, not a harness fault.
- review-73's one bwrap failure (a worktree removed while its call started): a race, one request; noted only.

**Done since (01:40–02:00):**
- Author holds removed (above): the old test updated, mutation case `not_held_to_be_asked` caught; design-66 released
  01:35:34. session-review.py: keep-warm continuation lines fixed; a `## stuck work` section (tasks parked over 30 min
  with reason, readiness and hold left; sessions resumed ≥3 times in ten minutes from `state/NAME.woken`; busy sessions
  whose transcript is still 20 min; nothing producing while queued tasks could; a task claiming the whole machine ≥3
  times in two hours).
- Task 56: parked for the machine behind task 80's measurement (01:16–01:47), resumed 01:47:10 and again 01:53; fine.
- implement-76's refusals, fixed: `scripts_run` (work_meter) reads a shell script a command runs from a file (`bash F`,
  `source F`, a `.sh`/shell-shebang file by its path; two deep) as part of the command for `runs_check`, the run's
  kind and a probe's bound, and git; so a probe in the session's own script counts as the check after a change, and is
  refused beside a measurement's claim (it had escaped the machine's limits). `perl -i` names its files in
  `write_targets` (`-M`/`-I`/`-m`/`-x` excluded), so an in-place edit of a draft under .build/ stands. Mutation keys
  `script_of_the_session`, `in_place_edit_of_a_draft`.
- A read of a file's lines longer than READ_BYTES is no longer refused: it shows the lines that fit (`within`) and
  names the rest with how to read on (`cut_short`), through lines.py as the in-context filter does (ten refusals that
  night, six within 12% of the bound, a request spent each). The recorder records only what a rewritten read showed;
  a stale rewrite record for a call run as is is dropped. Protocol `_production.md` and README updated. Mutation key
  `longer_than_a_read` (+ `lines_in_context_is_filtered` re-anchored).
- Task 80: its first handover named a check without `--output` ("did not run", no round spent), corrected, passed.
- Remaining known: change followed by a read (fix-83's `git diff --stat`, implement-76's `--help`) is still refused as
  out of form — two in two hours; left as is (a read would need the read bounds on its part).
- 02:00:37–02:01:40 the xhigh layer refresh (21% stale) exercised the restable path live: "stable xhigh: its entry is
  cold, so the base is loaded again before its layer" → new stable base 4a18e83e (02:01:05) → the layer's fork read
  273,316 of it from cache (99%), sealed at 517,620 (02:01:40), xhigh-stable.hit set. Verified: the next xhigh fork
  (review-57, 02:08:16) read 517,618 from cache. The max layer stood at 23% stale at 02:01: its refresh comes at its next look
  (LAYER_EVERY 900 s) and will take the same path.
- session-review.py: a resume's synthetic "No response requested." is not listed as an error.
- 02:15:46–02:16:58 the max layer (23% stale) took the same path: stable reloaded (95f7de81), the layer's fork read
  346,976 from cache (99%), sealed at 482,899. All three layers now refreshed or warm; the high layer (0.178 at 02:01)
  is next when it passes 0.20.
- 02:26 review: change followed by other commands — fix-84 (`rm -rf` of an old check output), fix-80.3 (a preparation
  chain) — refused as out of form; with fix-83's and implement-76's reads, four in two hours, each corrected by
  `again`. The owner allowed one check after a change; broadening to any command would need the tail guarded as a
  call of its own (reads, writes, counting). Left for the owner. session-review.py's "nothing produces" now uses
  `v2.startable` (the queue of 22 was all blocked: the graph narrow, the planner at work).
- ~02:27 the machine ran low on memory: Claude Code killed this session's review timer for it (19.7 GiB available at
  02:26, 29.9 at 02:28, 34 at 02:31; swap 8.8 GiB used). Running then: task 32's landing check (5.7 GB RSS) and task
  84's final check (passed 02:27:31). Host processes are not visible from the sandbox (only /proc/meminfo and the
  watchdog's Isabelle snapshot), and nothing was routed around that. A memory Monitor now says when available memory
  falls below 12 GiB (re-arm with the others); the harness's own gate refuses new runs below 10 GiB (MEM_MARGIN_GB).
  If it stays low with runs refused and sessions slowed, that is a stop condition to weigh.
- 02:57–03:10 task 32 (and 76), accepted, kept out of main by task 62's uncommitted ROOT/THEORY_MAP.md for 60 min,
  refused to the planner. Fixed three things:
  1. `v2.lands_when_free` (watchdog pass): a commit marked `lands_again` lands by itself once what stood is committed,
     with no session; `drop` clears the mark; the refusal's words say so. Tests in test_finalize (`lands_by_itself`,
     `does_not_land_by_itself`); mutation cases.
  2. The planner's requeue at 02:58 did NOT take the no-session recommit: `cmd_queue` read the accepted review task 33
     (stage done, completed in the list only at its task's commit) as a task put back to pending whenever the planner
     named it in an order, and reset its entry — the verdict gone, 32 read as unreviewed, so the re-plan path started
     implement-32.2 and implement-76.2, which found nothing to do; checks and reviews ran again (32 committed 03:10:23
     as 0381bc5f after its second review). Fix: `awaiting` in cmd_queue (a review with a verdict whose task is not done
     is not reopened). Test `keeps_its_verdict` (the order names the review first); mutation case.
  3. `tree_checked` said "after its commit (task 32)" and "every task's check refuses" when task 62 (told by the
     planner to take its ROOT and THEORY_MAP.md lines out) left its new theory undeclared in the one tree: it now
     names whose uncommitted change stands there and says only checks made in the one tree refuse. A correction was
     sent to the planner (event from the harness). The one tree stays inconsistent until 62's ROOT line is back; only
     one-tree checks are blocked (62 holds the tree anyway).
- 03:16 review: (a) implement-62's `git show HEAD:$f > .build/tasks/62/head/$f; …; cp … .` refused as a redirection
  into the tree — content_write counted the cp destination; now `write_targets(content=True)` judges only content
  writes (redirection, tee, truncate, -i edits, scripts); copies stand as the rule says (write_guard still judges
  them). (b) plan-35, moving 62's stray theory itself, was refused rightly (62 holds the tree) but told to write drafts
  under `.build/tasks/None/` and park: a session without a task is now told the tree is the holder's to change and to
  `v2.py tell` it. Mutation keys `draft_written_beside`, `without_a_task_is_told`. (c) Change + read after it: a fifth
  (implement-34's grep) — still for the owner. (d) plan-35's `git show HEAD:DECISIONS.md` with diffs refused by the
  planner's statements rule — as designed.
- 03:26 suite 542 passed. Reviewer holds are used: review-27, -73, -77, -57 were resumed for re-reviews; review-63 is
  held because it rejected task 62 and the fix is under way. Task 80's re-reviews got new sessions because after its
  second rejection it went to the planner and was re-planned, and cmd_queue's reset of a re-planned task clears the
  `verdict`/`reviewed_by` a harness-planned review keeps on the task itself: a fresh reviewer (a warm fork) — left.
- 03:32:45–03:34:28 the high layer (21% stale) refreshed by the same path: stable reloaded (f4581b85), the layer's fork
  read 273,144 of it from cache (99%), sealed at 541,897. All three layers refreshed tonight through restable.
- 03:42 review: the max and xhigh layers read 23.3% and 24.9% stale 1.5–2 h after their refreshes. Two generated
  indexes (state/held/theory-names.md, decisions-index.md: 34.5K of max's 148K tokens) change a line with almost every
  landing and were counted whole — max past the line after nearly any landing, and each max refresh is followed by a
  new knowledge base (kb-7, kb-8, kb-9 right after the 22:24, 22:39, 02:15 refreshes). `manifest.moved_tokens` now
  compares with the text the layer loaded (restored from its pack): same held text → 0 (proof-only changes), the
  generated INDEXES by changed lines, anything else whole (bases-design §1's re-read cost). Max 1.3%, xhigh 11.5%,
  high 0. Falls back to digests when the pack is gone. Test StaleShareTests; mutation key
  `index_moves_by_its_changed_lines`. The CLI wiring (`layer_texts` in stale-share) has no test. Also: base.sh and
  warm_daemon.sh no longer print a missing .miss file's error (warm_daemon's change takes effect at its next restart:
  the running loop was parsed whole).
- 03:50 memory dipped to 9 GiB: two heavy session checks at ~15.7–16.6 GB RSS each (fix-97's in its tree and one
  other) — twice the 7.5 GB per check the two-run limit was set on (2026-09-21). Recovered within a minute when one
  ended; available memory swings 13–44 GiB within 20 s while they run. The 10 GiB start gate held. If two such runs
  become the rule, the heavy-run limit or the margin is the owner's to weigh (not changed).
- A stray git stderr line reached v2.log at 03:49 ("Another git process seems to be running in this repository"):
  index.lock contention between two git commands; noted only.
- 04:07 review: API 529/500 errors hit five sessions 03:56–04:06; the retries brought plan-35 and design-95.2 back.
  Fixed: (a) the retry count ran across own replies ("2 of 3 in a row" for plan-35 after it had worked again) — the
  mark now keeps the handled failure's moment, a reply of its own since restarts the count (`replied_between`), and one
  failure is resumed once. (b) task 95's landing commit met another git process's index.lock in its tree and was taken
  for the commit gate's refusal ("does not stand with what landed"), sending the task back — a new designer found its
  work whole. finalize.git() now tries a command refused on the index lock again (10 × 2 s) for every command
  (git_retrying is the same function). Mutation keys `not_counted_in_a_row`, `api_broke_off`, `holding_its_tree_s_index`.
- 04:27 a watchdog pass ran 04:19:30–04:27:07 (a 5-minute silence after "resumed fix-97"); every resume and start
  waited on it. Unknown which part: now each part of a pass (watchdog.contained: the care of each session, the mail,
  finishing, holds, layers, landings, archive, snapshot) and of the dispatch (dispatch_once) that takes longer than
  v2.SLOW_PART (120 s) is logged ("the watchdog's X took N s" / "the dispatch's X took N s"). Test
  `slow_part_of_a_pass_is_named`. Watch for these lines to find the cause.
- Memory: two heavy runs at 9 and 13 GB again 04:26–04:28, swings down to 7 GiB for seconds; swap creeping 8 → 10 GiB.
- 04:24–04:35 review-77.2 resumed (logged) but its transcript got nothing after its earlier round (03:38): the resumed
  job died before its first request — during the API outage (529/500 03:56–04:38) — and was found gone after
  GONE_CHECKS passes, 11 minutes later; review-77.3 started, accepted, task 76 went on to land. First "is gone" of the
  night; noted only. Stable-base pings meanwhile ended "fork has made no request of its own yet" (the API refused
  them): neither a hit nor a miss, tried again; if the entries expire meanwhile, the next refresh reloads the base.
- 05:02 implement-36's 60 KB `v2.py change` could not start: E2BIG, "command line 137.7KB" at spawn (Linux's 128 KB
  per-argument limit) — Claude Code's quoting of the command more than doubled Isabelle text full of `'a`; the
  guard's wrap adds ~200 bytes. It wrote the file in two parts at the next request. The only one all night: no rule
  added (a protocol line would cost every prompt and stale the layers); if it recurs, the guard could refuse a change
  over ~50 KB up front with "write it in parts".
- 05:15 memory swings 10–25 GiB with two full checks (13 and 9–15 GB); the memory Monitor now fires below 7 GiB for
  30 s or at 20 GiB of swap (was 12 GiB, which fired on every swing).
- 05:38:45–05:39:59 the xhigh layer refreshed at 21% (theories changed by landings, counted whole; indexes by lines):
  no reload this time — its stable base 4a18e83e, kept warm by the daemon's stable pings, was read from cache
  (273,316, 99%) and the layer sealed in about a minute. The stable pings pay off as designed.
- 05:43 THREE heavy runs at once (13.6 + 6.1 GB session checks, 12.9 GB task 101 landing check), memory 6 GiB for
  30 s: a sandboxed guard counts heavy runs from the watchdog's snapshot (fresh for 180 s) plus finalizer admissions,
  and a session's check registered nothing, so checks started within one snapshot's life each saw room. Now the guard
  decides under the finalizers' admission lock (`v2.admission`) and marks an allowed heavy check
  (`v2.admit_session`, state/isabelle-admitted/session-NAME), counted until a snapshot 90 s newer (SEEN_AFTER), 600 s
  at most, taken back when the guard refuses the call for another reason. Test `let_start_counts`; 3 mutation cases.
- 05:47 review: (a) scripts writing by a name given a literal path (`p='.build/tasks/97/result.md'; open(p,'w')`) were
  refused as unreadable — implement-26, fix-97.2: `write_targets` now follows SCRIPT_NAMED/PY_ASSIGN; test
  `writing_by_a_name`. (b) review-75's `v2.py change <<'EOF' && v2.py verdict …` (the verb on the opener line) refused:
  once; CHANGE_CALL's groups are used in several places — left. (c) task 97's landing refused at 05:23 for
  Native_Path_Stores twice: replayed with the real versions (base d69bd0c9, ours 492a6b80, theirs 37a97cad) the two
  sides changed the row differently (3,260 vs 2,968 chars), a true conflict `agreed` rightly leaves to the gate;
  fix-97.2's "same text" was not so. No harness fault.
- 05:58 THREE heavy finalizer checks again (tasks 115, 97, 106 admitted 05:54:42, 05:55:42, 05:57:40), memory 2.2 GiB
  at the snapshot, swap 10 → 21 GiB: a finalizer's admission counted ADMIT_GRACE (60 s) and then only the machine's
  processes, but a check prepares for minutes before its Isabelle starts — each admission lapsed before its run
  showed. Now `v2.unseen_finalizer_runs(procs)` counts an admission while its finalizer (first pid of
  .build/tasks/ID/finalizer.pid) lives and no poly descends from it; the control branch of isabelle_load uses it, and
  the watchdog's snapshot adds it to "heavy" (field "unseen") so sandboxed guards count it too. `session_marks()` split
  out. Test `counts_until_its_isabelle`; 2 mutation cases. The snapshot wiring has no test.
- 06:12 review: tasks 36 and 94, parked for the machine 31–37 min, were ready (no heavy run going) and waited for the
  one producing slot, held by design-85 — the machine idle meanwhile. By design (one producing slot); an observation
  for the owner on throughput, not changed. session-review.py now says whose slot a ready parked task waits for.
- 06:26 memory 7.8 GiB free, swap 26 GB used, with only one visible Isabelle run (9.8 GB) and one preparing: about
  40 GB outside Isabelle (sessions' Claude processes, desktop, /tmp tmpfs 3.1 GB of which /tmp/structural-isabelle
  3.0 GB is the project's tooling, left alone). Swap traffic over 30 s at 06:28: none — idle pages parked in swap, no
  thrashing; free memory back to 35 GiB. Claude Code again killed this session's review timer for low memory.
- 06:29 task 115's landing check failed on one tools host test (1 error of 205; which is not recorded — the check keeps
  only the tail) with proof and all recipes accepted, at the memory low; its own check at 06:21 passed the same tests.
  Second failure → the planner; told the facts (event from the harness). A harness retry of a host-test-only landing
  failure is NOT safe as is: on a re-run the branch already holds main, so land() would skip the landing check. If
  such failures recur: a retry must force the landing check (and the check tool should record which test failed).
- 06:37 review, fixed: (a) plan-37 lost a request of seven reads of design 85's DECISIONS.md in its tree: BODY now
  lets the planner read a task tree's top-level .md (`trees/N/*.md`), theories and tools there stay bodies. (b)
  review-97.3's `> $TMPDIR/main.md` read as a write into its tree: `scratch` takes /tmp and $TMPDIR (TEMP_DIRS), and
  shell_context knows TMPDIR. (c) fix-122's change followed by `cd tools && python3 -m unittest …` refused twice: the
  tools' unit tests may follow a change like a check (`runs_tests`), a `cd DIR &&` may lead the tail, and the call is
  judged as the write (no machine limits); `_production.md` and the refusal text say so. Mutation keys
  `unit_tests_that_need_it`, `temporary_file_is_no_write`, `reads_a_task_tree_s_documents`. Planner events: none needed.
- 07:02 review: review-122's script testing fix-122's function in a `tempfile.TemporaryDirectory()` refused twice as a
  script whose target could not be read: `content_write` now lets a script stand that writes through `tempfile`
  (TEMPFILE) when no target it names is outside scratch (a named repository path is still refused). Test
  `temporary_directory_it_makes`. Else: fix-124's change + tail refusals (the owner's question), fix-88.2's `again`
  with a SEARCH not in its command, brief-121 refused a detail by its role — as designed. 552 passed before this.
- 07:26 review: task 94, parked for a heavy slot since 05:55, starved: landings and checks (115, 88, 120, 122, 126)
  took the slots back to back 06:54–07:20, then task 124's measurement held the machine (and the producing slot).
  It had an hour of its three-hour hold left — then a forced partial result. A machine slot always comes, like the one
  tree: `hold_of` now gives machine waits HOLD_TREE (6 h). Test `machine_is_held_for_its_turn`; mutation case.
  NOT changed (owner's to weigh): finalizers take a freed heavy slot within 15 s while a parked session is resumed only
  at a dispatch — no queue between them; a FIFO of heavy-slot waiters would make it fair.
  Also: task 115's landing check, re-run after the planner queued it, passed at 06:59 — its host-test failure at 06:29
  was load, as told.
- 07:43 max layer refresh at 34%: REASONING_REUSE.md (49K of 151K tokens) changed — a document, counted whole by
  design, so the refresh stands — and theory-names.md counted whole again although a generated index: its names are
  wrapped many to a line and one new theory re-wrapped lines 107–230. `moved_tokens` compares indexes by word now;
  test (wrapped names) and mutation case. xhigh refreshed at 25% (theories), warm (its stable read 99% from cache).
- 08:16 review: implement-30 told "3 heavy runs (at most 2)" at 07:55:59 — implement-128's check (started 07:54:24)
  counted twice, by its visible run and its session mark (the 90 s rule), a safe overcount; but the same rule let a
  mark lapse while a check still prepared (as the finalizers' did). `session_marks` now matches each mark with a heavy
  run in a session's sandbox (under bwrap) that started after it: the snapshot's new `roots` carry each run's start
  (`v2.process_started`) and `session`; a mark counts until matched, SESSION_GRACE (600 s) at most. SEEN_AFTER is gone.
  Test `let_start_counts` extended (preparing, earlier run, matched); 4 mutation cases caught.
  test_layer's frontier test asserted a named theory (Development_Machinery) the refreshed frontier no longer holds:
  it now asserts the property (the layer begins with the frontier tier and holds theories). Suite: 553 + that one.
  Also: fix-124.2's answer to q47 arrived after it finished ("reached nobody"): written to its answers, as designed.

# The owner's decisions of 2026-09-22 ~09:10, deployed 09:43:18 (built in $TMPDIR/dev/orch, tested there, then copied)
1. A `v2.py change` may share its call with any other commands (`change_parts`: the changes judged by their blocks,
   the rest — the call with each change put as `true` — as it would be alone: writes, how, a check and its limits,
   git, waiting; `after_changes_only` puts STATUS_LINE after each change something follows). A `cd` elsewhere joined to
   a change by `;` or a new line is refused. `again` stays alone. The old one-form code (CHANGE_CALL, change_call,
   change_then_check, after_change_only, change_form_faults, CHANGE_FAULTS, INERT_VERBS, runs_tests) is gone.
2. The machine goes in the planner's queue order, finalizers included (`machine_waiters`, `machine_ahead`): finalizers
   waiting to start (state/machine-wait/ID, heartbeat each poll, fresh 60 s: `machine_waiting`), tasks resumed for a
   heavy run (state/machine-turn/ID, until admit_session, TURN_GRACE 180 s), tasks parked for the machine while a slot
   could resume them. Applied in run_blocked (sessions' checks, parked_ready), finalize.wait_for_isabelle.
3. Two producing slots (`PRODUCERS_MAX`, `producing(st)`): produce() takes up to two within WORKERS_MAX; a waiting
   review takes a free slot before a second producer.
Also from the owner's "are these harness problems" (09:3x): the sweep keeps check outputs a live session names
(`read_by_the_living`: its kept commands and the scripts under its task's directory — task 128's before-export was
swept); a theory whose sides conflict only in `imports` merges as a list at a landing (`finalize.imports_agreed`);
`v2.py bring-main` (finalize.bring_main) merges main into a task's own branch on its session's request (implement-94,
q50/q51), told in tree_text. The planner was told all of it by an event (09:43). Suite in the dev copy: 538 passed, the
6 failures the unchanged copy has too (tests that need the real project), the 2 one-slot tests pinned to ORCH_PRODUCERS=1.
Mutation cases added for each; 24 stale anchors of the old change form replaced.

# The owner: "the persistent one-change calls and small reads … investigate, this balloons the cost" (2026-09-22 ~09:50)
Deployed 10:16:33 (built in $TMPDIR/dev/orch; the dev suite's six failures are the copy's own — git status, theories/ —
as before the change).
Measured over nine hours of the sessions' own requests ($TMPDIR/costscan.py): 2,242 requests, 168.7M input-equivalent,
81% cache reads, about 70K a request whatever the request does — the cost is the number of requests. Three levers:
(a) the closing text after a turn-ending command: 217 text-only requests right after a call, 172 of them after a park
(78), a result (60), a verdict (16) or the guard's "You are parked" refusal (18) — 11.1M; (b) hand-overs made one step a
request (change → change → finalize → result; C1→H:result 34 times, C1→H:verdict 30): 138 runs of 2–11, 227 requests
mergeable, 15.8M; (c) a single small read right after a read: 182 requests, 13.4M, an upper bound (many need what the
read before showed).
1. (a) `v2.turn_over(c)` marks the turn over (`state/flags/<sid>.ended`) where a result (with no question of its own
   open: it still completes its result then), a reviewer's verdict, `planned`, a consultant's reply or a park succeeds;
   `ctx_gauge.turn_ended` takes the mark in the call's PostToolUse and answers `{"continue": false, "stopReason": …}`;
   the guard's parked refusal carries `continue: false` too (`deny(end=True)`). Mail taken in the same hook continues
   the turn instead; a mark older than ENDED_FRESH (600 s) ends nothing; `resume` removes it. Read in Claude Code
   2.1.273's source (the claude-code-guide agent pointed at issue #29991, which is about the Agent SDK's callback
   hooks, not command hooks): PostToolUse `preventContinuation` → `hook_stopped_continuation` → the query loop returns
   `hook_stopped` before the next request; a PreToolUse deny with it likewise; the Stop hook is then run only for session
   function hooks (`sessionFunctionHooksOnly`), so ctx_gauge stop does not run and cannot take mail it would drop. The
   stopped turn clears the `blocks` count itself (the Stop hook did).
2. (b) The protocols hand over in one call: _finishing.md (one change writing the rows, entries, commit.md and
   result.md; then `v2.py finalize … && v2.py result ID`, with an example), _result.md, reviewer.md (review.md's change,
   then the verdict), planner.md (the notes' change, then `planned`), task-designer.md (proposal.json and the result,
   then `propose … && result`). For `&&` to mean it, a refused `v2.py` command exits 1 (`say`/`REFUSED` in
   `run_command`; `change` already did); _production.md says so.
3. (c) not changed: the reading limits and the small-read notes already ask for batches; what remains is the model's.
   The planner's closing summaries (about 40 requests, 2.7M) are not stoppable by the harness — nothing says its
   handling is over; a `v2.py handled` verb would be the owner's to want.
Tests: gauge (ends the turn, mail goes on, stale mark), v2 (marks by park/result/verdict/planned/reply, none for a
refusal or an open question, resume takes it; a refused command exits 1), work_meter (parked refusal ends the turn).
12 mutation cases, all caught.
- 10:25 review (deployed 10:24:27): implement-38's call (a change of 59K bytes) failed "Could not start /bin/zsh: … E2BIG … command line
  200.3KB … largest single arg 200.3KB" at 09:56, and implement-36's at 07:52 — never run, a request lost and the
  change redone in parts. Claude Code passes the command as one argument, about 3.3× its length (the guard's rewrite
  was 60.7K), and MAX_ARG_STRLEN is 128K. `work_meter.spilled`: a call over ARG_SAFE (32K) is written as it would run
  to `commands/N.run` and becomes `. FILE`; `resolved` makes the meter record it as made (without it the change counted
  as a read, "other"). Test `too_long_to_start` (runs the spilled change in a world); 2 mutation cases caught.
  Also seen: task 94's landing refused on 166 validation/ receipts both it and main's base advance retained; the
  planner answered q52 (a task retains no receipt; hand over at main's content). The finalizer could refuse
  validation/ receipts in a task's --files — the owner's to want; not changed.

# The owner (~10:30): "do the planner closing summary removal … shouldn't this be done for everyone … enforce it in the
# finalizer. Also plan-40 turned to plan-41 in 30 minutes, why is that?" — and after it: brief-142's "shell wrapper"
# errors, the planner's refused `tell`, and "find all such failures, where sessions are not reused"
Deployed: the status line 10:43:42 (hotfix), the gauge 10:55:26 (hotfix: plan-41 had rotated at 711K too, told
1031K), the rest 11:00:35. Dev suite 554 passed (its 6 failures the copy's own).
1. plan-40 was told "Context is at 948K tokens, near the end of your window" at 09:48:04 with 652K — a room of 380K
   used for 125K — wrote its notes and `planned` (09:49), and the knowledge base integrated them for plan-41. Two faults
   of the gauge together: its call ended before Claude Code recorded the request it was made in, so the latest request
   read was the one before (624,611); and after it stood the task list's reminder (planner-settings.json puts the
   planner on the shared list), 744K characters of task objects counted as 298K tokens — the model is given one line a
   task (`#id. [status] subject`, read in 2.1.273's source), about 6K. `ctx_gauge.model_chars` counts what is rendered:
   the reminder by its lines, a PreToolUse/PostToolUse `hook_success` as nothing (not sent; its additional context is
   an attachment of its own, counted). plan-39's end at 873K may have come early the same way. Test
   `what_reaches_the_model`; 2 mutation cases.
2. `v2.py end` (cmd_end): the last call of a turn no harness command ends — `… && v2.py end` — marks it over
   (turn_over) where `ctx_gauge.may_end` lets it end, and is refused elsewhere (a producing session: its result or a
   park); the knowledge base (its INTEGRATED is read) and an owner's episode are refused. _production.md ("Ending a
   turn", every role), planner.md (between its events, no summary). Test `no_command_ends`; 2 mutation cases.
3. Receipts: `v2.receipts_refused` at `finalize` — receipts (validation/incremental-check.json,
   validation/reconstruction/) with other files are refused unless the task's brief delivers them; alone they are a
   retention (#119's 158). Not a blanket refusal: #119, #144 and #145 are retentions and conversions the planner
   placed (HANDOFF Q11). `finalize.put_back_receipts`: a task tree's uncommitted receipts (only `retain` writes them; the
   check does not) are put back before main is merged in, as git merges nothing over a changed file; the one tree is
   left alone (a retention may stand there uncommitted). Tests `retention_and_by_no_other`,
   `did_not_commit_are_put_back`; 4 mutation cases.
4. Since 10:16, 12 turns ended by the harness; four closing messages remained. implement-40's park at 10:24 came
   with a message of the harness in the same call, which by the rule went on to the session: a parked or finished
   session's mail now waits in its box for its resume (test `parked_waits_in_its_box`). Its result at 10:36 had a
   question open, which by the rule left the turn going to "say in your result what you assumed" — and it wrote a
   summary instead: a result is now refused while an open question of its own is unnamed in it, and a recorded result
   always ends the turn (test `question_open` rewritten; mutation re-anchored). The other two were wakes of parked
   sessions by their run's completion (implement-40, implement-90) answered in text: no call, so no hook ends them —
   a parked session woken by its run could be resumed in that wake if the slot is free (not built; the dispatcher's
   order would have to be read in the guard).
5. brief-142 (10:33, the owner relayed it): "The assembly step hit an error in the shell wrapper … the shell wrapper
   failed again after the change". `(eval):42: read-only variable: status`: STATUS_LINE (`status=$?; …`), put after a
   change when more follows, runs in zsh — Claude Code's shell for a session's command — where `status` is $? itself and
   read-only. Every change followed by anything that is not a check (a check is wrapped in `bash -c`) failed after the
   change, since the line went in: 157 times from 2026-09-21 23:08 to 10:40, 23 in the last hour as batching grew. It
   is what implement-94 called "the same shell issue as before with a command after the change" at ~09:30, which I had
   read as the old form's refusal. `orch_rc=$?` now; the tests ran the rewritten commands in bash, and
   `sessions_own_shell` runs a change and what follows in zsh and bash (mutation: the old line, caught). Hotfixed alone
   at 10:43:42.
6. The planner's `tell 94` refused three times (the owner: why sessionless?). Two windows: from its result (09:44) its
   session is `done` while the task is finalized — held for a quick fix, but `tell` reaches only live and parked
   sessions; and when the landing did not merge (10:03) the task went to the planner, `held()` holds a producing
   session only while its task is checking/reviewing/fixing/committing, so the watchdog released implement-94 at
   10:04:27, and the planner's queue started implement-94.2 afresh at 10:06 (its context gone: 15 requests to learn
   the work again). `keep_told`/`hand_told`: a tell to a listed, unfinished task no session works on is kept on the
   task and posted to the session that next starts or is resumed on it (test `task_nobody_works_on`; 2 mutation cases).
   Not changed (the owner's to want): holding a task's session while the planner decides after a failed landing, and
   resuming it when the task is queued again, instead of a fresh fork.
7. The owner: "find all such failures, where sessions are not reused — this is a very expensive problem". From the state
   and the log, 2026-09-21 20:00 to 2026-09-22 10:50: 22 fresh producing sessions on tasks another session had worked
   (13 after the finalizer — merge refused, commit refused over the one tree, landing failed, a git lock — sent the task
   to the planner: 24 ×2, 80 ×2, 76 ×3, 32, 97 ×2, 95, 94, 124; 5 after a partial result: 46, 88, 124 ×2, 128; 2 went
   cold while they waited: 49, 56; 1 re-planned brief: 13), 564 requests and 35.7M, 177 requests (10.8M) before their
   first change; and 11 fresh reviewers for reviews an accepting reviewer had made (25 ×2, 80 ×2, 77 ×2, 33, 97 ×2, 116,
   125), 119 requests, 9.1M. The cause was one rule: `held()` kept a producing session only while its task was
   checking/reviewing/fixing/committing, and an accepting reviewer not at all once its verdict was in; the planner's
   `queue` then read the task's record afresh (dropping `session`, `reviewed_by`, `told`). Now: `v2.may_come_back` and
   the hold "its task may come back to it"; `start_producer` resumes `reusable(tid, role)` with why it came back and the
   brief as it stands; the hold "the task it accepted has not landed" and `start_review` resuming `accepted_by(r)`;
   `cmd_queue` keeps previous_session, previous_reviewer, back and told. Tests `comes_back_goes_to_the_session`,
   `judged_again_by_the_reviewer`; 8 mutation cases. Holding costs a ping per ~50 min (about 60K a ping) against a fresh
   session's learning (8–21 requests). The two cold losses (49, 56, both on the night of 09-21) were parked sessions;
   not changed.

# 2026-09-22 ~11:25–11:45: script targets (11:28:14), the parked wake, fix-175, task 128's conflict (deployed 11:36:31)
- 11:25 review: plan-42's `open('.build/plans/plan-42/b'+tid+'.md','w')` and review-94.2's `open(f'{T}/{n}','wb')` with
  `T=os.environ['TMPDIR']+'/mf'` refused as scripts whose targets could not be read; review-94.2's third try, literal
  paths under .build/outputs/, refused on the same words ("under .build/"), though .build/outputs/ is the harness's.
  `work_meter.script_writes`/`fixed_start` read each write's fixed beginning (a literal, an f-string's known first
  field, a name given TMPDIR or a literal) and a write whose directory is a draft's place stands; the refusal names
  .build/tasks/<task>/ and $TMPDIR, and says .build/outputs/ is the harness's when that is the target. Test
  `made_at_run_time`; 3 mutation cases. Deployed 11:28:14.
  Also: review-104's `bwrap: Can't find source path …/.git/worktrees/40/commondir` — Claude Code binds the registered
  worktrees' paths into its sandbox, and task 40's tree was removed between its listing and the call (second such, one
  request each); not changed.
- The owner on the parked wake ("can we address this?"): a parked session's run that ends makes Claude Code queue a
  task notification, which woke it for a request answering "Waiting to be resumed." Claude Code 2.1.273 runs the
  prompt hooks (prompt.submit) on it as on any prompt, and a hook's preventContinuation sets shouldQuery false. The
  UserPromptSubmit hook (ctx_gauge owner) answers `continue: false` for a parked session and keeps the notification
  (`v2.notified`); `running_jobs` reads it as the run's end (it read the transcript alone, where a stopped prompt may
  not be), `resume` gives it to the session and removes it, `forget` too. Tests `woken_by_its_run`, the park-for-run
  test; 3 mutation cases. Not yet seen live: watch for "was told a background run ended: kept for its resume".
- 11:32 task 128's landing did not merge (theories/Development_Admitted_Publication.thy: main's 4ab8486e and its
  d73ae6ca rewrote the same lemmas). implement-128.2 is held ("its task may come back to it", warm) — the reuse working
  live — and the planner's tell was kept for it (11:35). But a session could not resolve such a conflict: it runs no
  merge, bring-main refused "changed the same lines … write main's version of each with your lines in it, then ask
  again", and asking again was refused as uncommitted changes (implement-94.2's loop); handing over without a merge
  commit conflicts again where both changed a line differently. `finalize.keep_marked`: the landing's refusal and
  bring-main's leave each conflicted file, both sides marked, in .build/tasks/ID/merge/ (with the main merged against);
  `resolved_drafts`: bring-main asked again takes the session's unmarked files for those paths and commits the merge.
  merge_refused tells the planner so. Tests `written_by_the_session`, the landing conflict test; 3 mutation cases.
- The owner: "why did fix 175 not continue in the implementer session?" — 175 is a new task the planner made at 11:17
  from follow-ups of the reviews of 32, 40 and 103 (a probe keeps no summary), in tools/probe_theories.py; reuse is for
  a task that comes back, and those implementers were released at their landings (two cold). fix-175 took 9 requests
  (74 s). Its prompt opened "whose session could not take its own fix", the quick-fix wording, over a "Nothing failed"
  section: protocols/fixer.md now opens for both. Routing follow-ups to the finished task's session would need holding
  implementers past landing — the owner's to want.
- 11:50 measurement (the owner: are the batching changes working, and no errors of the orchestrator?). Deployed 11:49:55:
  brief-141's change of its own draft saying "show.py finds none" was refused as a reading of details — planner_guard
  judged the change's text; it now judges the call without it (test `change_writes_is_no_reading`). And its
  `cd .build/tasks/141/brief && jq … > proposal.json` after the change was read as writing the project's proposal.json:
  write_targets followed only a leading cd; a redirection now resolves where the call stands then, every cd before it
  counted (test `where_the_call_stands_then`). 2 mutation cases.
  Seen live: 11:47:49 "implement-128.2, parked, was told a background run ended: kept for its resume, no request made" —
  the prompt hook does run on task notifications.
- 11:58 (the owner, from a review: "bring-main dropped uncommitted ROOT and THEORY_MAP.md edits … is this resolved?"):
  implement-139's result said so at 10:08. `rows_agreed` (after bring-main's and a landing's merge) agreed the rows of
  ROOT and THEORY_MAP.md whatever the merge had done with them, reading the file in the tree — the session's uncommitted
  one: its new ROOT line and THEORY_MAP row, in neither side, were dropped, and its other edits `git add`-ed into the
  merge commit. Now only a file both sides changed is agreed (one side alone: git's merge is exact, no union doubling).
  Test `uncommitted_index_rows`; mutation case. Deployed 11:53:54. The probe's missing `--parallel-proofs` is task 175's
  (a summary file with the options beside each probe log), waiting for its check since 11:24; not landed yet.
- 12:05 the owner: "the planner receives a lot of information from the harness — is it all needed?" In sixteen hours the
  planners were given 342K characters by the harness (~85K tokens, each kept and read again by every later request).
  The finalizer's commit events were 141K of it (47): half the review's whole Summary of an accepted task, which its
  review file holds. `v2.first_sentence`: the summary's first sentence, the review file's place, the follow-ups whole
  (the planner places them). A failed check's message carried the log's last 30 lines — task 143's second failure 28
  lines of recipes accepted and a 1.5K summary, its error list after them: `finalize.log_tail` gives the check's own
  error list (check_errors.py's) and the whole log's place, else the last 15 lines each cut; the quick fix is told the
  same. Tests `told_by_its_errors`, the review cycle's commit event; 2 mutation cases. Deployed 11:58:58.
- 12:10 the owner: "check all the other harness messages to every role for similar problems". Measured over sixteen hours
  ($TMPDIR/harnessmsgs.py, every session's transcript): 5.5M characters of harness text — launch prompts 3.8M (20–34K
  each: the brief ~7K, the role's protocol ~15K, the same for every session of a role and written into each one's cache),
  notes after calls 0.99M, resumes 0.37M, refusals 0.15M, mail 0.14M, Stop replies 0.03M. Changed: the read-count note
  (2,850 of ~300 characters, 200 of each the protocol's own sentence on how reads count) says the counts, and the
  sentence only at the first read drawn from the reserve and the last (`countdown`, test
  `where_it_starts_to_bite`); a merge refusal names at most twelve paths and how many more (`finalize.listed`: task
  94's named its 166 receipts to the planner and its session). 2 mutation cases. Deployed 12:04:57. Not changed: the old
  form's change refusal (67, none since 23:45 yesterday); the proposals, findings, answers and questions, which are
  what their readers act on; the protocols' length — sharing them would mean holding them in the bases (a base rebuild,
  the owner's), and trimming them is the owner's text.
  And the reuse's own resume (11:00) gave the brief whole again (~7K), which the resumed session holds: the brief's
  hash is kept at a start (`brief_sha`, through the re-queue), and the resume says "Its brief is as you have it." unless
  the planner changed it. Tests `comes_back_goes_to_the_session`, `brief_changed_is_given`; 2 mutation cases.
  Deployed 12:08:17.
- 12:20 design-171 reviewed request by request (the owner): 46 requests, 4.1M; about 20 avoidable (1.7M): the entry drafted
  in six files then written again (6, 0.55M), reading on outputs cut at 5K (6, 0.41M), the machine (5, 0.38M), task-list
  calls alone (2, 0.17M), its own acceptance check (2, 0.16M). The machine's: granted at 11:39:04 four minutes into a
  request, its claim cleared at 11:42:05 (CLAIM_GRACE from the grant) before it had read the mail. Now a claim given by
  mail is `seen=False` and held up to CLAIM_UNSEEN (600 s); the gauge marks it seen when the session's mail says so
  (`claim_seen`), and CLAIM_GRACE counts from then; a resume that says so (produce) and the session's own
  `measuring` are seen at once. Test `given_by_mail_is_held`; 2 mutation cases. Deployed 12:18:48 (the owner: yes).
  (the owner: yes to 3) implementer, investigator and designer protocols: the task list made in the request of the
  first reads, each update in the request of the work it marks; the designer writes its entry once, into DECISIONS.md,
  all its sections in one call (two or three for a long one), drafts only for what is not settled. Deployed 12:19:25.
- 12:30 Open for the owner, written down, not built: the finalizer's own check for a documents-only commit (designs,
  investigations) — notes/proposal-documents-only-check.md (--check optional for Markdown-only --files; a second-long
  documents check; no heavy slot; the same check at its landing instead of LANDING_CHECK).
- 12:35 deployed 12:30:43: (2, the owner's idea) a call declares how much it wants shown, `SHOW=20K …` up to the batch's 50K
  (`shown_bound`, `v2.source_bound` for `v2.py read`, cut.py and the file-read cut name it; _production.md says it;
  tests `declare_how_much`, the read test; 3 mutation cases). And main: from 11:24 to 12:23 one landing held main while
  it waited for a heavy run for its check with what landed, and 147 and 132 were refused behind it and went to their
  implementers through the planner, with nothing to do. `finalize.MACHINE`: a landing that would be checked with what
  landed and cannot start a heavy run now lets main go, waits (`machine_free`, wait_for_isabelle's own test without
  admitting), and lands after; past its budget as before. A commit refused for main held past its budget is
  `lands_again` (why: main) and lands again by itself, no session; may_come_back holds no session for it. Tests
  `lets_main_go` (main free while it waits), `lands_again_by_itself`; 2 mutation cases.
- 12:45 Open for the owner, planned, not built: landing trains with the documents-only check folded in —
  notes/plan-landing-train.md (a queue; one lander at a time takes every accepted task waiting as one train in an
  integration tree; one check of the combination; a failure resolved by attribution from the check's report and
  bisection on both heavy slots, never one by one — the owner: "do not allow that"; documents-only commits take no
  heavy slot). Measured: 38 rechecks, median 302 s, 37 passed.
- 12:58 the owner's decisions: the finalizer takes over the proof base's advance and the receipts (a harness commit per
  landing is fine); the lineage's depth decided by measured data. Planned (notes/plan-landing-train.md 1a, 1b): the
  base and receipts follow main; the finalizer takes the session's own accepted check when the tree is unchanged; and
  checks batched across tasks — sessions check with probes, the repository's check is the harness's, run once for
  every task ready (attribution and parallel bisection as in the train). Measured: 235 heavy runs in 17 h (80 by
  sessions, 27 of them refused; 116 finalizer, 24 of those repeats; 39 landing); 93% of finalizer checks pass.
- 13:04 the machine rebooted (uptime from 13:04): /tmp is a tmpfs, and with it went every stored Isabelle heap
  (`/tmp/structural-isabelle`: complete-20260921a and bases a–d) and the active pointer
  `/tmp/structural-active-context.json`; the base directories under `.build/` stand without their heaps. Every check
  and probe fails in seconds until a base exists. plan-43 (13:07–13:14) rewrote #144 into the lasting fix (heap store
  and pointer under `.build/`, one complete proof after the interrupted landings) — but #144 waits on 128, 132, 147,
  172, 173 and 175, whose own checks need a base. The owner stopped the orchestration at 13:14 (`stop.sh --keep-warm`).
  An interim complete base is established from HEAD (`incremental_check.py establish`, /tmp/structural-accepted, the
  tool's fallback when no pointer exists) so that those landings can be checked; #144 then makes it lasting. Found on
  the way: `establish` inside Claude Code's sandbox puts its heaps under `$TMPDIR/structural-isabelle` (tools/build.py's
  `--cache-home` defaults to `tempfile.gettempdir()`), where the base's own heap identity never looks — run with
  `TMPDIR=/tmp`.
- 13:26:50 deployed stages 1 and 2 of notes/plan-landing-train.md. (1) documents-only: `v2.documents_only` (Markdown
  outside theories/, tools/, validation/); `--check` optional for it (`v2.DOCUMENTS_CHECK`); `finalize.documents_check`
  (tools/check.py `source_checks()`, THEORY_MAP.md rows that name no theory or twice — only what HEAD does not already
  have — and conflict markers), at the hand-over and at the landing instead of LANDING_CHECK, no machine. (2) the base
  and receipts follow main: a landing check runs `--advance-base` into `.build/bases/<time>-task<ID>`, each recorded in
  `state/lineage.jsonl` (depth, rebuilt, phases, heap bytes: the depth is decided from it); after the landing the harness
  retains and commits its receipts alone (`retain_landed`); a landing that did not happen puts the pointer back
  (`undo_advance`, writing through a link at the old path, as #144 will leave); `v2.prune_bases` (with the tidy) keeps
  every level's proof, drops its recipes/ and exports-context/, removes a base no lineage holds after BASE_KEEP with its
  heap (tmpfs: memory), and prunes nothing without a pointer. The receipts refusal and _finishing.md say so. Tests:
  documents (hand-over, finalizer, HEAD's own row, landing), advance and receipts, put back, prune; 21 mutation cases,
  all caught (the landing ones only after the tests were moved out of the file's `if __name__` block, where pytest never
  collected them). Once #144 lands: v2.ACTIVE_CONTEXT and v2.ISABELLE_HOME are to be read from the one module it names.
- 13:28:34 the interim base is established (1,825 theories, 679.8 s; heap 841 MB; Pure and HOL rebuilt into /tmp/structural-isabelle too); the check tool selects it (load_parent verified). An event for the next planner says so, and that advances and retentions are the harness's now (Q11), documents need no --check.
- 13:52 the xhigh layer went cold: no xhigh fork started between 12:28 and 13:45 (the stop), and its own cache entry
  outlived nothing — review-129.2 (13:45) and review-133.2 (13:48) each read only the stable base (273,316) and wrote
  ~236K. A fork that misses writes its own prefix, never the layer's (base.sh's own finding for the stable base), so
  every xhigh fork would miss until a new layer is made; and the daemon never pings a layer whose `<who>-base.hit` is
  fresh, which every fork's start and every kept session's ping touch (v2.hit_chain), though they read their own
  entries and not the layer's — the session review's "layer last hit" reads the same mark. Asked the watchdog for an
  xhigh layer refresh (state/xhigh-layer.refresh: one frontier write on the warm stable base instead of ~236K per
  fork). Not changed: pinging every layer every 40 minutes whatever its forks do would cost more (~500K cached reads
  a ping) than the two misses in three days; the misleading mark is left as an observation for the owner.
- 13:56:50 deployed stage 3 (and 4) of notes/plan-landing-train.md: landing trains, `train.py`. A task in its own tree
  is committed on its branch and queued (state/landing-queue.json); whoever holds main next — a finalizer, or
  `finalize.py land-queue` the watchdog starts when entries wait and nobody lands them — lands every entry waiting as
  one train: merged onto main in `.build/trees/train-a|-b` (imports, rows, keep_marked, the gate: a member that cannot
  be merged is taken out and said), one check of the combination (documents alone: the documents check; else the
  documents' rows and markers, then LANDING_CHECK advancing the base), main fast-forwarded once, the receipts and
  HANDOFF.md in one harness commit ("Retain …"), one push, the planner told once (`v2.landed_together`). A failed
  train: attribution from its report (failed theories → their import closure; failed recipes → their manifests'
  files; host tests → the tools) — the cleared land after one check, the suspects checked stacked on top; what nothing
  names in halves side by side on both heavy slots; an interaction lands the first half and checks the second on top;
  a member found gets main brought into its tree and its quick fix with that check's log. Main let go while a train
  waits for the machine or the one tree; a combination checked is not checked again for the wait (PASSED). A finalizer
  whose budget ends leaves its entry queued (lands_again(main) is gone for own trees); known failures carry over to the
  next lander. ORCH_TRAINS=0 restores the one-by-one landing. Tests: TrainTests (7) plus the landing suite, all
  through trains (intended changes: check outputs under .build/tasks/trains/, imports in main's layout first, the
  put-back log); 14 mutation cases, all caught. planner.md and README say so.
- 13:58:26 deployed: v2.job_stale — a background job whose output's directory is gone counts as ended (the reboot took implement-163's run and /tmp with its output; the job counted as running and held task 163 parked). Test `output_went_with_a_restart`; 1 mutation case, caught.
- 13:59:28 deployed: an ended job is said once a day (v2.job_ended, say_once under state/jobs-ended/): every read of a session's jobs judged it again and logged it each time.
- 14:04:57 deployed: the proof base's lasting places. fix-144 (13:40–14:02) made a complete proof of HEAD a2ed0ed7
  (777 s) at .build/tasks/base-lasting/complete-20260922e, its pointer .build/tasks/base-lasting/active-context.json and
  its heaps in .build/tasks/base-lasting/isabelle-home, named once in tools/isabelle_places.py (in its tree; it lands
  with #144), and turned the /tmp pointer and home into links. Until #144 lands, main's tools are older: an advancing
  check (a landing's, a train's) replaces the /tmp pointer link with a file of its own (fix-144's follow-up). Now
  `v2.ACTIVE_CONTEXT` and `v2.ISABELLE_HOME` are the lasting ones once the lasting place is there, and
  `v2.keep_pointer_links` (every watchdog pass, stopped or not, and before the finalizer reads the base) carries a
  pointer an older tool wrote over the link to the lasting pointer and makes the link again, and makes the /tmp links
  again after a reboot. Test `older_tool_wrote_over`. Once #144 has landed and every tree has brought main in, the
  links are no longer read; v2 could then read tools/isabelle_places.py itself.
- 14:15:10 deployed: the ended-job rule narrowed to Claude Code's own /tmp area (v2.CLAUDE_TMP, /tmp/claude-<uid>/), which a reboot clears — the tests' fictional paths (/x/…, /t/…) and any other path stay as they were.
- 14:06–14:09 what the lasting base's link did, and the repair (the planner told, 14:09 and 14:10): a base records its
  heap by its absolute path; fix-144's link of /tmp/structural-active-context.json to the lasting pointer led every
  tree's older tools to complete-20260922e, which they refuse ("Accepted heap/database changed", in a second). The
  landings of 128, 132 and the trains of 147, 172, 171 were sent to quick fixes, the checks of 173, 175, 179, 181, 151,
  145 told their commands were not runnable. Removed the pointer link (14:07:59: the older tools fall back to the interim
  base /tmp/structural-accepted, still valid through the heap-store link); `v2.places()`: the harness reads the pointer
  main's own tools read (tools/isabelle_places.py once #144 lands, /tmp before); `keep_pointer_links` keeps only the
  heap-store link, never crosses the pointers. Put the tasks back (to land or be checked, no failure counted), told
  147 and 151, whose fixes had begun. My own slip: an edit cut `_read`…`base_lineage` out of live v2.py from 14:07:59 to
  14:08:27 (a slice ended at the wrong anchor); restored from the backup; nothing in the log failed in that window.
- 14:20:54 deployed: (1) a check the proof base refuses before it begins (`finalize.BASE_REFUSED`: heap changed or
  missing, lineage broken) is nobody's failure — a hand-over's stays checking and is run again by the watchdog once the
  pointer changes or after BASE_RETRY (600 s); a train's or a batch's entries stay queued (the lander waits for the base
  to change); (2) train.py's rounds as a strategy (Train, Batch) over two queues; (3) stage 5, dormant behind
  ORCH_BATCHES=0: `v2.py check` (a snapshot of the task's tree, queued, the session parked for "check" and resumed with
  its result), `finalize.py check-batch`, the finalizer's hand-over of exactly the repository's check joining the batch
  (`BATCHABLE`), a passed tree not checked again (state/check-results.json), the guard pointing own-tree sessions to
  `v2.py check`, the watchdog starting a batcher; (4) integration and check trees (any non-numeric name under
  .build/trees) are no tasks' trees; the combined checks' bulk is pruned after an hour, their reports kept. Tests:
  BatchTests (4), base-refused (2), the guard, pruning; the stage 3 and base-refused mutation cases all caught.
- 14:24 correction: complete-20260922e's accepted-context.json was re-recorded by fix-144 at 14:14:33 with its heap under
  /tmp/structural-isabelle; both the older tools and #144's accept it now (verified), and the 14:06 failures were the
  record as it stood then, not a lasting incompatibility; the planner is told. The first live train landed at 14:23:15:
  tasks 171 and 172, one check (159 s, 0 theories rebuilt: its recipes and host tests), the base advanced, one harness
  commit "Retain the recipe receipts of the check tasks 171 and 172 landed with, and the planner's state".
- 14:25:13 switched on: checks batched across tasks (ORCH_BATCHES=1): train.py, protocols/_checks.md (the repository's check of a task in its own tree is asked for with `v2.py check`), _finishing.md (a hand-over of exactly that check joins the batch; a tree its `v2.py check` passed is not checked again), README. Suites green but the three location-bound tests (green on live); stage 5 mutation cases (9) all caught. The nine finalizers checking since 14:09 run the older code and check one by one; every check handed over from now joins a batch.
- 14:43:01 removed state/isabelle-admitted/173 (written 14:26:13 by 173's older finalizer, stopped at the owner's word; the relaunched one counted it as its own unseen run, and the batch of seven waited behind a phantom).
- 14:45:20 deployed: an admission marker names the process let start the run (finalize.wait_for_isabelle writes its pid; v2.unseen_finalizer_runs reads it): a train's or a batch's lander admits under its first member's name and runs the check itself, and that member's own finalizer — running nothing — made the run count twice (the train of 144 and 132 at 14:42 counted 3 heavy runs for 1); a marker older than the finalizer on record (a stopped one's) counts for nobody. Test `counts_until_its_isabelle_shows` (+2 cases), 2 mutation cases.
- 14:46:23 deployed: a batchable hand-over check that runs by itself says why (ATTENTION when the batch gave no answer). Unexplained: task 151's relaunched finalizer (14:27:46, queued in the batch) ran its own check at 14:32:46 with nothing logged; its check passed. The batch of the others waited behind phantom runs (above) and the train of 144 and 132, which lands #144's tools.
- 14:48:03 #144 landed with 132 as one train (79f16061; 368 s, 177 theories rebuilt, heap 79.6 MB): main's tools name the lasting places (tools/isabelle_places.py), and the harness reads the lasting pointer since (v2.places): it names the train's advanced base over complete-20260922e (lineage depth 2). Trees made before it keep the /tmp pointer (complete-20260922e) until they bring main in. 14:44:49 the first batch: tasks 173, 175, 181, 179, 145 and 163 checked together with main.
- 14:52:02 deployed: v2.snapshot adds with --ignore-errors and leaves out only what git refuses as no regular file (the sandbox's /dev/null mounts over .bash_profile and .bashrc in a session's tree: implement-185's `v2.py check` was refused, q59); any other error still refuses. Test `snapshot_leaves_out`. The planner is told.
- 15:05:19 deployed: manifest.py's stale line says each load part with its own time (the stable reference, the layer) and apart what differs only in the session's tree (its work, or main moved since the tree was made: bring-main); a file only the one tree holds (the generated indexes) is compared there. The owner asked why task 145's session was told tools a layer loaded at 14:55 were 'stale since xhigh load 02:00:38': the one line took the stable load's time over both parts, and its tree predated #144's tools. Test `said_by_the_load_that_holds_it`, 2 mutation cases.
- 15:06:38 asked the watchdog for a high layer refresh: the high layer, loaded 03:33:15, held 17 files changed since (12 theories, the tools #144 rewired: incremental_check, build, development_answer), at 17.5% of its tokens, below the 20% refresh line; implementers and fixers fork it. max (14:48) and xhigh (14:55) layers are current; all three stable parts hold the same 9 changed theories (a restable is the owner's).
- 15:06:41 my refresh request met the high stable base's own entry cold (≈676 min): the harness's rule loads the stable base again before its layer, so the request cost a whole high stable load as well (it also brings the stable part current). Before asking for a refresh: read the stable entry's age in the review's 'standing' (warm under ~55 min), and ask the owner when it is cold.
- 15:16:20 deployed: a SHOW declared at the head of any command of a call counts, the largest (work_meter.shown_bound): implement-130's `sed …; SHOW=12K sed …` was cut at the default. Test in declare_how_much; mutation cases updated (2 caught). From implement-130's review (the owner's ask): 14 requests, 0 errors, one-call hand-over; 4 spills at the 5,000-byte default (19.6K, 14.4K, 12.5K, 8.3K), each remainder read later; 3 requests (#15–#17) building by hand the recipe-reach list its brief demanded. Across today's sessions: 257 spills in 101 sessions, the remainder read later in 52%, whole output median 7.5K bytes, 72% ≤ 10K, 92% ≤ 20K; 5 briefs demand the recipe-reach list.
- 15:23:35 deployed (the owner: yes): READ_BYTES 10,000 (was 5,000): on the day's 257 cut reads in 101 sessions, a median 7.5K whole, 72% within 10K, the rest read later in 52%. ReadTiersTests pinned to 5,000 (their fixtures measure the mechanism); a v2 read test's claim relative to it corrected.
- 15:25:08 deployed (the owner: yes): `v2.py read reach:A,B` (and `reach`: the task's changed theories): the recipes whose exported theory reaches each theory through its imports, in the tree's own sources; 'all N', 'all but …', or the few named; a theory no recipe reaches named so. _production.md lists it. 0.03 s. Test `which_recipes_reach_each_theory`, 1 mutation case.
- 15:32:10 deployed: the harness states its own checks in the commits it makes — a task's commit gets 'Checked by the harness: the repository's check of this work with main [and the work of tasks …] passed in N s — T theories, R rebuilt and K reused from the base; recipes run and reused, all accepted; tool and kernel tests' (finalize.harness_validation, from the check's report: check_output recorded for batches, reuse and solo checks; the documents check said as such); a train's 'Retain …' commit closes with 'Validation: the harness's check of tasks … together with main, exactly as it lands, …'. _finishing.md: the Validation paragraph states what the session verified itself; reviewer.md: the harness's outcomes missing from a message is no finding; the planner told. Task 181's review had rejected a message saying the landing check 'is run by the finalizer' (its brief asked for the landing check's outcome, which no session can know). And manifest.py's stale line says a file once, under the load that brought it: a layer's kept record holds the stable files too (the owner: 'why twice?'). Tests; mutation cases caught.
- 15:36:35 deployed: a lander lands one train a call and lets main go between them (train.rounds returns after each; run_lander and run_batcher go round again while entries wait): the reports it defers while it holds main are made when each train has landed. Task 151 landed at 15:30:23 while 181, 145 and 163 waited; its lander went on to their train holding 151's report, 151's finalizer ended with its entry decided, and the watchdog sent a landed task to the planner, which queued it, and implement-151.2 was started on it (released at 15:33, 151 recorded done as c26ecb22 by hand). The watchdog (15:36:19) makes a landed entry's report itself when no lander holds main and a minute has passed, and never takes such a task for a finalizer that ended without reporting. Test `report_was_never_made`, 1 mutation case.
- 15:47:39 deployed: BATCH_BYTES 80,000 (the owner; sessions' bashOutputMaxChars is 128,000); `read diff` shown whole up to the call's bound by default, as a brief named whole (21 of the day's 54 reviews read it twice); `v2.py read probes`: the task's probe runs, newest first — what each loaded, its completion marker, its errors and time, and whether each probed theory is the tree's as it stands (a renamed copy matched by its body against the theories the task changes; an empty probe said to prove nothing) — reviewers spent about a request each digging it out (47 in 55 reviews). From review-197 (the owner's ask): 6 requests, 2 of them the diff's remainder and the probe hunt. _production.md lists both sources; the read-batch tests pinned to 50K. Tests `diff_whole`, `probes_certified`; 2 mutation cases caught.
- 15:48:00 reviewer.md's first batch names `read probes` beside result, diff (whole) and log.
- 15:59:37 deployed (the owner's choices from design-218): `v2.py read check:STAMP` or `check:ID` — a check the harness ran, found under .build/tasks/batches/, .build/tasks/trains/ or .build/bases/ by its stamp, or by a task's number (its finalized.json check_output, else the newest batch or train whose stamp names it): its report and log paths, status, time, rebuilt and reused counts and base, error, failed recipes with where their logs are, failed host tests, the proof's *** errors (the first twelve). A batch's failure text and a train's failure tail name the report and the read. design-218 spent five requests finding a batch report its brief named by its stamp. And every allowed Bash call of a session starts with `setopt nonomatch 2>/dev/null; ` (work_meter.globbing, applied last; unwrapped strips it): zsh refuses a whole command at an unmatched glob however its errors are redirected — `cat a *x* 2>/dev/null` prints nothing, a `for` over an unmatched glob ends the whole call — while sessions write for bash; 65 of the day's 8,842 calls in 41 sessions. Sessions run under --permission-mode auto, so the rewritten call still goes to the classifier. Tests `what_a_check_found`, `unmatched_globs_left_as_they_are`; 2 mutation cases caught. Backup: state/dev-patches/predeploy-155937.
- 16:06:22 deployed: a batch tells a member its report found at once, wherever its group stands (train.Batch.found_at_once): task 153, found by the report of its batch with 176 at 15:42:53, was told at 15:46:19, after the 206 s check of 176 alone that the report had cleared, while its session waited parked. A train still tells its found member after what the report cleared has landed (Train.found_at_once False): its tree gets main merged in, and that main should hold what landed, and its report waits for main to be let go anyway. The narrowing line said "176 is cleared, and 153 is checked apart", the reverse of what ran; it now says "its report clears 176, checked again without task 153, which it finds" (or "tasks …, which are checked in halves"). Test `failure_goes_to_its_own_task` pins the order; 1 mutation case caught. The dev copy had test_layer.py, which the mutation doc says a copy leaves out (it reads the project's THEORY_MAP.md): its collection error read as "broke the import"; removed from the copy.
- 16:12 measured, no change: whether batches should overlap (the plan's 1b.3 says a batch starts "when a heavy slot is free"; the batcher runs one at a time). Since BATCHES went on at 14:25: 26 waits for a batch, 191 min in all; 99 of them in one stretch, 14:27–14:41, when seven base-refused checks were queued at once while the solo checks begun before batching (147, 132, 151) held both heavy slots — the switch-over, not the batcher; 29 min behind a train's check, which advances the base and so runs alone; 63 min beside one running batch, the part an overlapping batch could take back (~2.4 min a task). Against it: an overlap is one more heavy check, and it narrows the empty-machine windows a train's advancing check needs. Left as it is; to be measured again with a day of steady state.
- 16:36:04 deployed (the owner, on implement-221's analysis: "the failure outputs should be batched and then fixed together. Try to find other similar failures and fix them too"):
  1. A probe reports every failing proof of a theory in one run: the guard leaves `--parallel-proofs 0` out of a probe (work_meter.forked, heredocs untouched), and check_errors.py says so after the output (`--note`); `IN_PLACE=1` leading the call keeps it, for what in place is for — which proof does not return, after a probe timed out (_checks.md says both). In place a probe stops at the first failing proof; forked it lists all, in the same 5.4 s (a probe of a theory with three failures, both ways). 512 of the day's 728 probes ran in place, and 100 times in 31 sessions the next probe failed further down the same theory; implement-221 spent requests 6–8 on lines 60, 390 and 395 of one theory.
  2. A check the harness runs (a batch, a train, a finalizer's) ends with every error it reported: fz.run_logged runs it through check_errors.py watching its --output (the proof's build.log, the recipes' logs), the list kept whole beside its report when too long, and log_tail sends the whole list. Since the harness runs the checks, a failure reached its session as the check's one JSON line cut at 300 characters, naming build.log and no error — task 153 at 15:46. Test `lists_every_error_its_check_reported` (a fake check shaped as the real one: errors only in proof/build.log; the test world's check command now written with --output, as the real one is).
  3. `v2.py read check:` lists every error of the proof, one line each (check_errors.errors_in), where it showed the first 12 `***` lines (the 40 of batch176-153's are 2 errors).
  4. bring-main merges main under the session's uncommitted changes instead of refusing them: set_aside keeps its versions of the files main changed too (.build/tasks/ID/bring-main/), merged_in commits the merge as before, carry_back brings each version onto it as a three-way merge (index files as unions with their rows agreed; other files with lines both changed marked `<<<<<<< main` … `>>>>>>> yours`), put_back restores them exactly on any refusal. The refusal told sessions to copy main's version in by hand (`git show main:PATH`): a branch holding main's lines without main in its history lands them as its own changes, and a row main changed again is then both sides' — THEORY_MAP.md held a row twice at the landings of task 176 (16:21, Native_Collection_Programs), 97 (05:23) and 24 (23:29), each a fix round. 11 of the day's 83 bring-mains were refused so. The refusal that remains (a file that could not be set aside) says not to copy by hand.
  Swept for more: back-to-back refusals of one kind of call with different reasons — none but a session trying three forbidden ways to write a file (each refusal named the right way); `again` and `change` already say every block's problem, the documents check every problem, a review every finding. Tests; 4 mutation cases caught.
  Also: test_v2's review test expected the first batch as it read before 15:48 (reviewer.md names the diff whole and `read probes`); updated. Backup: state/dev-patches/predeploy-163604.
- 17:02:10 deployed (the owner, on brief-230's analysis and the two messages about task 176: "Add them to the other fixes", "tell the planner what to do once you deploy it"):
  1. `v2.py tell ID... --file FILE` tells the file's text; an unknown `--` option is refused, not told. It told the words "--file PATH" themselves: six of plan-45's messages of the day (t176, t176b, t176c, t212, t212b, t230), and brief-230 never had its own.
  2. A planner's notes (.build/plans/plan-N/*.md) are no body (work_meter.BODY): every statements reader reads them. brief-230 was refused t230.md twice (requests 9–10), losing the calls beside it.
  3. A row one side holds as the other side once had it is a copy, and the other side's row stands (finalize.agreed with row_history: the rows each side's first-parent line held since the merge base; rows_agreed passes both sides', carry_back main's). implement-176 copied main's rows by hand (as the old bring-main refusal said), its branch 5562b8a6 held them without main in its history, and every merge after held them twice: its landing (16:21), review-176.3's rejection (16:42), bring-main's merge commit refused by the gate (q62, 16:50). Dry run on task/176 against main: before, Native_Collection_Programs and RRA_Syntax_Forests twice; after, the merged map differs from main only in 176's three rows. The planner had made #243 to re-land 176's work from HEAD (sound, left to finish).
  4. show.py (and `v2.py read NAME`) resolves a qualifier as a theory where one has that name, else as a locale (a fact in its `locale … begin` / `context … begin` block, or `lemma (in L)`) or an interpretation's prefix (the fact of the locale it interprets). It took every qualifier for a theory: brief-230's store_found_program.any_exact and four more "introduced nowhere, mentioned nowhere"; 19 such names in 12 sessions of the day.
  The planner told by an event (what 176's failure was, let #243 land and leave 176 dropped, no such workaround again; the six --file messages and t230's unanswered question on #189 and #191; show.py). Tests (test_show's locale test; the row tests with the repository's union attributes); 6 mutation cases caught. Backup: state/dev-patches/predeploy-170210.
- 17:09:57 deployed: `v2.py read probes` names a probe's two times — its theories' load (Isabelle's elapsed time, the log's last) and the run's whole (the probe tool's `seconds`, the heap's load included). It gave the first alone and unnamed: task 188's commit message said 6.0 s (the run), the read 0.235 s (the theory), and review-199 flagged them as differing (a minor finding, the owner's question: harness-made). Test `probes_certified`; 1 mutation case. Backup: predeploy-170957.
- Correction to 16:12's measurement: a train's check does not run alone. It is admitted as any heavy run (train.run_checks: wait_for_isabelle(lead, False)), and at 17:09 train 233 and batch 225 ran side by side (heavy 2, no exclusive holder). So of the 191 min of batch waits, the 29 counted "behind a train" had a slot taken by the train, not the whole machine; the conclusion stands (an overlapping batch would take the second slot a train or a batch holds), but not its reason.
- 17:21:41 deployed (the owner: "check that everything is hitting cache, that there is no unexpected misses"): a read keeps warm the entry it read and nothing under it (v2.hit; hit_chain removed). Since 10:00, 1,648 of the sessions' own requests: none missed within the hour; nine base/layer loads, each a refresh the log names (13:53 by hand, 14:48, 14:55, 15:06 mine, 15:42, 15:49, 16:05, 17:07) and each read at 98–99% by its fork. The misses were three, all one cause: every request of a session marked its origins hit down to the base (ctx_gauge → hit_chain, "measured 2026-09-18"), but a request reads the longest prefix cached, and a shorter entry under it is not kept alive (base.sh's own note, the max refresh of 2026-09-21). plan-42's 95 requests (10:46–12:54) kept kb-10 marked warm — held as the knowledge base, never pinged — while its entry expired at ~11:47: resumed at 12:54, 527,247 tokens written anew. design-171's requests until 13:33 kept the xhigh layer (7cba04e1) marked while its entry, last read by review-176's fork at 12:27, expired: review-129.2 and 133.2 forked it at 13:45 and 13:48, 235K each. Now a session's request marks itself (ctx_gauge), a fork's start its direct origin (start), a ping the session pinged; the daemon and the watchdog keep bases and held sessions warm by what they see truly read. Tests rewritten (test_v2, test_ctx_gauge, test_layer: they pinned the chain); 1 mutation case. Backup: predeploy-172141.
- 17:57:40 committed 34901a81 "Land and check tasks together, keep the base at main, and tell every failure whole" (47 files; pushed eca462e1..34901a81). The commit waited 16 minutes for the landing lock behind train 225 (842 s); taken under the lock so that no landing moved main under it.
- 18:17:52 deployed (the owner: fix-220's and fix-227's findings, "put them in a queue for probes", the probe evidence, "why disk usage is not cleaning up", "update the testing and mutation setup as it is taking way to long"):
  1. Every error of a check comes with what fixing it needs while room is left (check_errors.detailed: a failed proof's goal, a type error's term and type; the whole list with them kept when it has no room): fix-220 read the probe log for the goals after each list.
  2. A measurement's hold is its call's (v2.claim_call / release_claim, from the guard): a foreground measurement held the machine CLAIM_GRACE from the grant whatever the run did — fix-220's 17 s timing idled it three minutes while two checks waited, and task 128's ~200 s pair lost its hold at 189 s; all seventeen holds of the day ended "what held it is gone".
  3. A check refused for the machine takes no change of its call with it (work_meter.through_changes): the call runs up to its last change and says what did not run — implement-189, implement-182 and fix-227 lost their changes so (fix-227: three requests).
  4. A probe queue (the owner's): a producing session's probe led by QUEUE=1 is queued when the machine refuses it (v2.py queue-probe, the session parked), the watchdog runs it as soon as the machine has room (run_queued_probes, whatever the producing slot does), and the session is resumed with its output. _checks.md says it.
  5. The harness keeps each task's probes (v2.keep_probes into state/probes/ID/, before and after every call of its session); `read probes` shows a removed one from the copy. fix-245 and implement-221 removed their probe directories before handing over (the project memory's "remove probes … promptly", read by every session forked from a base; the owner had the line changed) and review-246 found no probe evidence.
  6. Every repository check's bulk is pruned an hour on (prune_combined_outputs, now for all of .build/tasks): recipes/ and exports-context/ go, the reports, logs and the proof's own files stay; the base's lineage is never touched. The checks a hand-over names (.build/tasks/NAME/check…) and the task-by-task landings' (landing…) were never pruned: 115 of the 139 GB under .build.
  7. finalize.run_check no longer wraps its check in gathering: run_logged lists every check's errors, and the finalizer's own check listed them twice.
  8. Tests in parallel: notes/run-tests.py shards the suite by recorded times into 16 pytest processes at nice 10 — 634 tests in 30 s (7 min before). The mutation check runs its cases side by side, each in a copy of its own, only the test files that name its key, stopping at the first failing test (-x): 572 cases in 187 s (20 min before). test_finalize's leak test waited on any `sleep 5` on the machine; it now waits on its own.
  9. Mutation cases: 22 stale anchors re-pointed (code reshaped since), the task-by-task landing path's 16 re-pointed to the train path the tests run now (one deleted: receipts left in a tree cannot reach a train, whose branch holds the listed files alone), "lands again by itself" given the test that reaches it, the brief-whole test pinned to the 5K read it was written for.
  All 634 tests pass live. Backup: predeploy-181752.
- 18:26:40 the new prune run once by hand rather than at the next tidy (19:15): 229 parts, .build from 139 GB to 16 GB. df did not move at once (btrfs; snapshots may hold the extents).
- 18:30 the owner: no commits or pushes of mine until told (memory commit-push-at-milestones suspended). Everything since 34901a81 is uncommitted.
- 18:30:10 deployed (fix-249's findings, the mutation cleanup): `v2.py change` writes the glyphs of what it writes into a theory as their escapes by Isabelle's table (v2.escaped; its search too, and the file's own text as it was; a note says how many) — fix-249 wrote a converter script of its own. _checks.md names the base's pointer (.build/tasks/base-lasting/active-context.json) and says the /tmp one is the older trees': fix-249 read /tmp/structural-active-context.json (14:51, the 14:14 base) for what the base holds. It stays: trees 128, 143, 147 and 176 hold pre-#144 tools whose probes read it, and a link would be refused ("heap changed", 14:06). Mutation check: 567 cases, every one caught, in 199 s; dropped three whose lines are redundant now (kind's out-of-form change branch, shell_context's leading cd, write_targets' SCRIPT_NAMED — the guard enforces each elsewhere, the tests hold with the line removed: candidates for removal) and the fixed-command allow (globbing carries it); test_finalize asserts a landing held out of main is marked to land again. All 635 tests pass live. Backup: predeploy-182939.
- 18:32 two findings of another reviewer (P1: adopted() in tools/development_answer.py:136 takes the theory file's existence for adoption; P2: tools/development_adoption.py's rollback omits TimeoutExpired), relayed by the owner, passed to the planner by an event to verify and fix what is confirmed — the planner's to fix, not the harness's.
- 18:37:07 deployed (the owner: review the planners since plan-43): a task's records (brief.json, finalize.json, finalized.json) and the base's pointer (.build/tasks/base-lasting/active-context.json) are a statements reader's reading (work_meter.BODY), and planner.md names them with `read check:ID`. plan-43 was refused task 128's outcome after the reboot (13:08) and plan-44 the base pointer after #144 (15:10). The rest of the planners' refusals were right by role (finalize logs, greps of tools/ for the base's paths), one Claude Code classifier outage (plan-44 13:40), and plan-45's q62 answer refused whole for a `git … | wc` read in its call (one request). Batching: an event takes one request as a rule (change + edit + tell + end chained); three lone `v2.py end`. Not committed. Backup: predeploy-183637.
- 18:40:39 deployed (investigate-253, the planner's verification of the reviewer's P1): worker-settings.json and planner-settings.json set PYTHON_COLORS=0 and NO_COLOR=1 for what sessions run — its traceback, written to a file, came back as `\x1b[35m…` codes read as text (143 of the day's 11,256 outputs held such codes). base-settings.json is left as the bases were built. investigate-253 itself batched well (reads of 34K, 12K, 12K in one request; a run launched beside the next read; its report drafted while the run went); its one lost round was its own driver's wrong path. Test `feature_flags_off`. Not committed. Backup: predeploy-184008.
- 18:52:03 deployed (the owner relayed q64: investigate-254, done, could neither record its result — "hand the finalizer the final job first" — nor finalize its `.build/tasks/254/report.md` — "not under .build/"): its brief's Deliverable named `report.md` bare, "in this task's own folder" (a brief made in an edit cannot know its id), and `deliverables()` took it for a file at the repository's root, so `result` wanted a final job the finalizer refuses. A done task whose deliverables all lie under .build/ was already recorded without a final job (judged as it is) — the planner's answer ("the harness cannot yet record …", #134's gap of 07:35) was stale. Now `v2.placed`: a bare file name in a Deliverable is `.build/tasks/<id>/NAME` unless the root holds that file; a new root file is `./NAME` (protocols/_brief.md, README). And `brief_record` writes brief.json again when the planner rewrites a brief a session works to (cmd_edit): plan-46 added a test module to 253's and 254's Deliverables at 18:44 and the harness went on reading the briefs as they were at start; both records refreshed by hand. The result refusal names the repository files the brief delivers. Tests `file_named_bare_is_the_task_s_own_folder_s`, `own_folder_needs_no_final_job`, `rewritten_while_a_session_works_to_it`; 3 mutation cases caught. The planner told by an event. Backup: predeploy-185203.
- 18:40 the batch of 227 and 223 failed in 1237 s on the proof's own `*** Timeout` (the check's --timeout 1200, one Isabelle session; 1,248 theories rebuilt from base train247) with nothing else heavy running; #225's rebuild of about as many took 559 s. The session's log database (…/isabelle-home/.isabelle/Isabelle2025-2/heaps/polyml-*/log/<session>.db): 1,245 theories ended (a theory's `PIDE/markup` export is written when it ends), three native-control theories did not — Native_Control_Child_Review, Native_Control_Source_Execution, Native_Control_Sourced_Children; command timings total 3,150 s over 16 threads, the longest Native_Control_Quotation_Code's local_setup 136 s. 223 alone then failed in 478 s on a real proof (Factor_Premise_Forests.thy:147), listed as four errors (its head cut by Isabelle's "...", and twice again through Certificate_Construction_Review's and Native_Control_Guard_Source's `ML`); 227 alone was still running at 19:00.
- 18:58:50 deployed: check_errors — a `*** Timeout` names the theories its session left unfinished (`unfinished`: sources without the `PIDE/markup` export, from the session's log database under the harness's Isabelle homes, ORCH_ISABELLE_HOMES for tests), and the train's attribution takes them as failed theories (their import closure); the commands a failure is reported through after its own (`At command "ML"` of an importing theory, and the blank line before) are no error of their own; a message whose beginning Isabelle's limit cut off goes when a whole one stands at its place, else it is said to be cut. 223's four errors are one, and `read check:` of the timed-out batch names the three theories. Tests `one_failure_reported_through_other_theories`, `timeout_names_the_theories`; 4 mutation cases caught (the train's line has no test of its own: its attribution tests fake the check). Backup: predeploy-185850.
- 19:01 227's half timed out too (1227 s, 106 theories rebuilt from base train247): every one of its theories ended (all 106 with `PIDE/markup`; command time 598 s against 574 s in its passing check of 18:06, before trains 182, 189 and 247), so a proof forked from its theory — joined only at the session's end — did not finish. fix-227 told so by the harness (deliver, 19:05), with the 106 theories in .build/tasks/227/timed-out-theories.txt and IN_PLACE=1 probes as the way to it.
- 19:12:06 deployed: (1) check_errors — that case gets its own line ("every theory of the proof's session ended, and the session still ran out of its time: a proof forked from its theory … did not finish — a probe with IN_PLACE=1 stops at it"); `unfinished` is None with no database (a session's sources are written only when it ends). (2) train.run_checks: a half checked alone that fails is told at once in a batch (Batch.found_at_once), not when the check beside it ends — 223's half failed at 18:48:44 and its session heard nothing until 227's half ended at 19:01:09. The running batcher (pid 1778126, 19:01) keeps the older code until it ends. The fake check takes SLOW_WITH=T:seconds (a slower check where a theory is). Tests `half_found_alone_is_told_when_its_own_check_ends` (5/5 green, red on the old code), the timeout test extended; 2 mutation cases, all caught. Backup: predeploy-191206.
- 19:02 the next batch (253, 254, 249, 191, 235) passed in 90 s; 254 landed at 19:06:41 with no check of its own (its tree, main plus its test module, was a tree the batch had passed: record_pass), 253 at 19:07:07 (train check 20 s).
- session-review.py, run 19:10 from this session, tried api.anthropic.com three times: `v2.row` spawns the `claude` CLI (v2.py:658) to read a session's row, and the CLI reaches for the API, which this session's sandbox refuses; the review's output was whole. Not a harness fault.
- 19:11:12 "ATTENTION a call of review-249 showed 86,436 bytes … cut.py did not apply": the call was four `v2.py read` commands chained (`SHOW=20K read result; SHOW=40K read diff; read log; read probes`), each bounded by itself, their sum over the batch's 80K — no cut failed. 1 of the day's 39 calls chaining two or more `v2.py read`s went over; left as is (one `v2.py read result diff log probes` bounds them together). The ATTENTION's words fit a cut that failed, not this.
- 19:12:41 223's check passed (602 s); 19:13:08 235 landed as fb032252.
- 19:18:51 deployed (the owner: "check review-202 for read/write batching/errors"): review-202, 6 requests, no refusal; batch 1 (result, diff 63K, log, probes: 69K) and the one-call verdict were as the protocol has them, but parts of requests 2–5 hunted for two things no read gives — the commit message (`cat .build/tasks/edited-reach/commit.md`, its brief's key, failed; then an `ls`; found in .build/tasks/191/) and q63's answer, which the result names (a grep of state/v2.json, then a script over it). Over the day, 55 of 106 reviewers read the commit message by hand (96 calls) and 10 dug for answers. Now `v2.py read result` (whole, not a range) is followed by the commit message its final job names and by each question the result names with its answer (`beside_the_result`, 4K each at most) — reviewer.md's first batch already reads it, so no protocol changed. Test in `every_source_it_names_at_any_time`; 1 mutation case caught. test_start_stop's `request_from_inside_the_sandbox` failed once in the parallel suite and passes alone (load). Backup: predeploy-191851.
- 19:43:39 deployed: ARG_SAFE 32,000 → 6,000 (work_meter.spilled). fix-255's `v2.py change` of 23.8K was refused at spawn, E2BIG, "command line 145KB … largest single arg 145KB", where 8.1K had started in the same session: the sandbox's profile goes into the same argument — Claude Code's message: "166 filesystem deny paths … 52 of them for registered git worktrees", about four per tree (its settings, skills, hooks), fixed at the session's start — so a session's room was about 10K, not the 128K the 32K threshold assumed. The day's three real E2BIGs: 61K (05:02), 61K (09:56), 24K (19:14); the one spill since 10:24 (implement-223's 38K at 17:07) ran through the classifier as `. FILE`. 6K spills about 8% of calls (180 of 2,353 in ten hours). Test extended (a 10K call is spilled); mutation case caught. 15 worktrees are registered now; two are deleted tasks' trees (143, 176) holding work, which trees_tidied keeps. Backup: predeploy-194339.
- 19:40:13 THREE heavy runs, memory 3–4.5 GiB, swap 27 GiB: train 223's check (19:35:54), fix-263's replay in its tree (the guard admitted it at 19:39:07, mark session-fix-263), and batch 255 (19:40:13, "waits for the machine" at 19:39:43). Suspected: in control mode a session's run is counted by its live Isabelle processes, and its mark only until a snapshot first shows it — a replay runs Isabelle in phases, and between them it is in neither count. To fix next (the mark held until the call ends).
- 19:47:51 deployed: runs are counted by their tools' processes too (`v2.run_roots`, `run_tool`, `outermost_tool`, `claude_process`), in isabelle_load's control branch, the watchdog's snapshot and unseen_finalizer_runs' lines. The 19:40 case: batch 255 was let start while train 223's check and fix-263's replay ran (heavy 3, 3 GiB, swap 27 GiB). A run was counted only while a poly showed under it; fix-263's replay runs Isabelle in phases (replay_development_answers.py → development_answer.py → prove_context.py → isabelle build), and its session mark had been answered by the snapshot that first showed it — between phases it was in no count. Now the outermost process running one of RUN_TOOLS is a run whether or not an Isabelle shows under it; Claude Code's own processes (their prompts name tools) are none; a runner with its tool under it is counted by that run, not also as unseen. Tests `between_its_isabelle_phases` (new), `counts_until_its_isabelle_shows` extended; 5 mutation cases caught. The batcher and landers running at 19:47 keep the older code until they end. Backup: predeploy-194751.
- 19:50:15 a third heavy run again (batch 267 beside train 223's check and fix-263's replay), admitted by pid 2016496 — the batcher begun before the 19:47:51 deploy, running the older count; fix-263's session mark had lapsed at 19:49:07 (SESSION_GRACE 600 s from 19:39:07) with its replay still going, so from then the older count saw the replay only while a poly showed. The batcher begun at 19:47:53 (2068962) counts by the new rule; the older one ends with its batch.
- ~20:05 the owner, leaving for some time: finish the delta layer's implementation and deploy it if the sandbox allows; monitor the run; review sessions as they finish for read/write batching and harness errors, and fix what is found. Written into notes/plan-delta-layer-tasks.md ("Standing orders") with the progress so far. Found meanwhile: the queue holds ['267'] only (59 tasks ready) though plan-46's last edit (19:41:04, e12.json) queued 68 — being traced.
- 20:12:35 deployed (backup predeploy-201235): the delta layer, dormant (notes/plan-delta-layer.md, notes/plan-delta-layer-tasks.md tasks 1–7: manifest.py delta/delta-share/snapshot-delta, base.sh WHO delta [--ask], base_pack.py held/last-reply, v2.deltas_on/delta_record/base_file, the stale line from a delta's snapshot, tidied, watchdog.deltas and the layer rule under a delta, `warm WHO layer --if-due`, the review's standing line; test_delta.py 27 tests; ~30 mutation cases caught); and three fixes: (1) q65 — v2.snapshot takes the receipts a brief delivers (`delivered_receipts`, which receipts_refused now reuses) into what a batch checks: fix-267's re-recorded report words were checked as HEAD's old ones and could never pass; fix-267 told to hand over again, the planner told; (2) every order the planner sets is logged with who set it and its size (the queue stood at ['267'] alone at 20:01, 59 tasks ready, with nothing saying how; plan-47 set 55 at 20:04); (3) a refresh reason the watchdog writes is `why: …`, read as the log's reason, anything else in the file read as by hand.
- 20:13 task 8 begun: state/high-delta.build asked (the high layer sealed at 20:12:37 after its 35% whole-file refresh).
- 20:14:03–20:14:22 the first high delta (asked by hand): 1,187 tokens (all the stable reference's drift since its 15:07 load; the layer had sealed at 20:12:37), built in one request that read the layer's prefix from cache (600,393, 99%) and wrote 3,250 — about 64K input-equivalent against 720–810K for a layer refresh. Record state/high-delta.json (f57f73e2), text state/high-delta-20260922T201403.md.
- 20:15:53 the canary (state/high-delta.ask): "which theories does RRA_Syntax_Forests import, and which lemmas about premise forests does Factor_Reference_Tables prove?" — only the delta holds the answer (RRA_Placed_Forests came with #221 at ~16:47, the premise-forest lemmas with #223, both after the stable load). The fork answered from the delta: RRA_Syntax_Construction and RRA_Placed_Forests; premise_forest_reference_table and premise_forest_callee_range, "in its current proved-here list, after the new reference_table_placed".
- 20:17 `echo high > state/deltas`: high's roles fork the delta from now; the watchdog builds the next one when 2K tokens have moved (at most every 20 min), and refreshes the high layer when the delta holds 8% of it. warm_daemon.sh's layer ping waits for the daemon's next start; until then the layer's entry is kept warm by the delta's builds, and a build that finds it cold asks for a layer refresh instead.
- 20:19:09 deployed: reviewer.md's first batch reads `result`, `log`, `probes`, then the diff (whole, up to the call's bound) — "a batch refuses what comes after 80K read, so the diff goes last". Read first, a large diff took the batch past 80K and the log and the probes were refused, one request more (review-236, review-261; 3 of the day's 116 reviewers). The guard does not cut a read to the batch's remainder, so the diff read last keeps its own bound. Test updated. Backup: predeploy-201909. (test_v2's protocol test failed once and passed on the rerun: it reads the real repository's git state.)
- 20:20 notes/delta-measure.py written (task 9); the baseline 10:00–20:00: high 403K an hour of upkeep (5 layer refreshes 3,848K, 5 pings 184K), xhigh 324K, max 224K.
- 20:19 the first forks of the high delta: fix-271 and fix-272 read 603,643 from cache at their first request (the delta's whole context, 603,645) and wrote 11.0K (their own launch prompt); fix-271's stale line: "since the high delta load of 2026-09-22T20:14:21 (2): replay_development_answers, development_answer" — only what changed after the delta.
- 20:33:58 deployed (from the 20:29 review; 39 of the day's refusals "Not by a redirection/a script that writes", 32 of them naming $TMPDIR, /tmp or .build/tasks/): the guard reads more of where a command writes — (1) a shell assignment made from variables already known is followed (review-227's `T="$TMPDIR/r227"; … > "$T/$n"`, refused as a write into its tree); (2) a script's triple-quoted strings are text, not write sites (fix-265's `inj.replace("""…theory.write_text(…)…""")` made its targets unreadable); (3) `(NAME / …).write_text(…)` is a write site placed by the name (fix-265's `(dst/'inject.py').write_text`). Tests in `where_the_call_stands_then` and `made_at_run_time_in_a_draft`; 3 mutation cases caught. Backup: predeploy-203358.
- 20:53:18 deployed: a task holding the machine's claim is not held back by a task waiting ahead of it in the planner's order (run_blocked: its claim is the permission). 20:37:30–20:47:42 was a deadlock: fix-274 asked `measuring` (queued, 1 run going) and was told to park; its claim was granted at 20:37:39 as it parked for the machine; parked_ready → run_blocked → machine_ahead found task 271's finalizer ahead in the order, waiting for the machine that 274's claim held — so 274 was never resumed (the dispatch started implement-42 and implement-110 and resumed fix-271 in the slots meanwhile), 271's check and 42's probe waited on the claim, and the machine stood idle until the unseen claim lapsed (CLAIM_UNSEEN 600 s). Test in `waits_its_turn_in_the_planner_s_order`; mutation case caught. Backup: predeploy-205318.
- 20:56:29 deployed: the watchdog pings the layer under a standing delta when its own entry is due (ORCH_WARM_EVERY to WARM_MAX after its last read) — `base.sh WHO warm layer --if-due`, as warm_daemon.sh's new line does, which waits for the daemon's restart (its loop is parsed once); base.sh keeps one ping of an entry at a time (`WHO-PART.pinging`, 300 s), since the watchdog asks each minute while the entry is due. At 20:55 the high layer's entry stood at 40 minutes with no ping to come: a delta build after 55 minutes would have been a layer refresh instead (about 800K against a 60K ping). Also seen at 20:55: fix-274 waits for a worker slot only (at_capacity), second in the resume order after task 110 — no fault. Tests `layer_under_a_standing_delta_is_pinged_when_due`, the pinging marker in `layer_under_a_delta_is_pinged`; 2 mutation cases caught. Backup: predeploy-205629.
- 20:57:17 the watchdog's first ping of the high layer under its delta: OK, 600,393 read from cache (99%), 1,879 written (about 62K); high-layer.hit refreshed, the pinging marker gone.
- 21:03–21:17 a cache eviction across the account's entries, not a harness fault: forks of the high delta and the xhigh layer missed (fix-251 617K, review-43 541K, review-275 529K, review-274 528K written anew), the ping of the held implement-147 missed 46 minutes after a hit (634K), the high delta's build read 9,269 of the layer and wrote 597,594, the xhigh layer's refresh read 9,270 of its stable base and wrote 267,946, and the max stable pings missed twice (341K each; two misses stop that entry's pings). A fork that misses writes its own prefix, which no later fork reads, so every fork after an eviction pays it again.
- 21:15:31 deployed (backup predeploy-211531): a fork's miss marks its base (v2.cache_check → state/WHO-forked.miss) and the watchdog makes what its roles fork anew, once — a delta build where a delta stands (deltas), a layer refresh otherwise (layers), and a part sealed since the miss (SEALED_FRESH 600 s) answers it. Tests `a_fork_that_missed_its_origin_marks_its_base` and `a_fork_that_missed_its_entry_has_it_made_anew`; 4 mutation cases caught. The marks for the 21:04–21:10 misses were set by hand: the high delta was rebuilt at 21:15:09 (4,314 tokens: 3,127 frontier, 1,187 stable; context 606,865) and the xhigh layer refreshed at 21:16:56. The stable entries of max and xhigh are cold: the next layer refresh of each loads its stable part again (base.sh: rebuild_stable when it is not warm).
- 21:20:12 deployed: the review's stuck-work line reports the time a task held the whole machine, not how often it claimed one (HELD_TOTAL 600 s, or one hold over HELD_LONG 300 s) — task 269's four holds of about 30 s each, every one ended by the call that ran it, were flagged where nothing was wrong, while fix-274's ten-minute hold is what the line is for. Backup: predeploy-212012.
- 21:23:59 deployed: one miss stops that entry's pings (base.sh warm --if-due, warm_daemon.sh's own gate, which waits for the daemon's restart) — an evicted entry does not come back, and each further ping writes its whole prefix for nothing: the stable bases of max and xhigh were each pinged twice after the eviction, 341K and 268K a ping, both times missing. What makes an entry again is a load — a layer refresh (which loads a cold stable base first), a delta's build or a base's rebuild — and each clears the misses of what it wrote. Test in `missed_ping_is_not_taken_as_a_read`; mutation case caught. Backup: predeploy-212359.
- 21:26:51 deployed: a keep-warm ping that missed what the roles fork (`<who>-base.miss`) asks for the same rebuild a fork's miss does (watchdog.missed_fork), since the entry is gone either way and the next fork would write its whole prefix before anything made it again — the max layer was pinged twice at 21:23, 486K a ping. The ping's mark is left for the load that makes the entry to clear (base.sh), so no ping pays again meanwhile. Test in `a_fork_that_missed_its_entry_has_it_made_anew`; mutation cases caught. Backup: predeploy-212651. Markers standing: max-base.miss (its layer's refresh takes it, and loads the cold stable base with it), max-stable.miss, xhigh-stable.miss (the next xhigh layer refresh loads it).
- 21:30:10 deployed: a stable base whose entry was missed is cold whatever its last read says (base.sh stable_warm reads `<who>-stable.miss`), so a layer built over it loads it again first and leaves an entry the refreshes after it read — the max layer's refresh of 21:28 forked a stable base evicted twelve minutes before, whose hit was 51 minutes old, and wrote its 341K inside the layer's own prefix. New mode `base.sh WHO stable-warm` (exit 0 while the entry is there), which the test reads. Test `a_stable_base_whose_entry_was_missed_is_cold_whatever_its_last_read_says`; mutation case caught. Backup: predeploy-213010.
- 21:34:22 deployed: a keep-warm ping of a held session that missed is no read — it marks the session (state/hits/NAME.miss) and no ping goes until the session's own next request writes its entry again (v2.hit clears the mark; the watchdog's gate reads v2.ping_missed). A ping cannot make a session's entry: its fork writes its own prefix, which nothing reads. kb-12's ping missed at 21:28 (534K) and the session was marked warm all the same, so it would have been pinged every PING_AGE, each ping missing and writing 534K. Test `a_ping_that_missed_is_no_read_and_stops_the_pings_of_that_session`; 2 mutation cases caught. Backup: predeploy-213422.
- 21:54:22 deployed: what a build that fails says is kept where the run is read. The high layer refresh asked at 21:36:26 left a fresh pack, no layer, no session and no reason anywhere: the watchdog starts `base.sh WHO layer|delta|warm` with stdout and stderr on /dev/null, so every refusal and every traceback went nowhere (only the warm ping already kept its stderr). base.sh now says its failures through `fail` — the line timestamped into state/warm.log, and to stderr as well unless stderr is warm.log already (ERRLOG, read at the start before a `2>/dev/null` in a substitution can be read instead) — and the watchdog starts every build through `base_run`, whose stderr is warm.log. 17 refusals converted (the reloads, the layer and delta loads, the held-delta check, the list and record checks). Tests `a_build_that_fails_says_why_where_the_run_is_read`, `what_the_builds_it_starts_say_is_kept_where_the_run_is_read`; 3 mutation cases caught. Backup: predeploy-215422. It paid at once: the retry at 21:56 said `base_pack: incomplete load: 6/6 complete chunks; final acknowledgement=False`.
- 21:58:18 deployed: a stable miss recorded before the base was sealed is not that entry's (base.sh stable_warm compares the miss's time with the record's `sealed`, and takes the miss when the load answers it). `seal` marks the stable entry warm but left the miss of the base before it standing, and stable_warm reading that would send every layer refresh from then on through a fifteen-minute reload of the stable base. Test `a_miss_recorded_before_the_base_was_sealed_is_not_its_entry_s`; 2 mutation cases caught. Backup: predeploy-215818.
- 22:03:35 deployed: a complete load is no longer thrown away over the id copied back (base_pack.acknowledges, SLIPS 4, bounded edit distance `slips`). The high base's reloads at 21:36 and 21:56 each loaded all six chunks and each was refused: the 21:56 reply said `ad30832f993f993fef05…`, four characters stuttered, so the length no longer matched the 64-character pack id — 270K thrown away twice, and no high layer refresh could finish. A character slipped, doubled or dropped is the same kind of slip; the chunks are what is checked exactly, and the line has only to show the session read to the end. A delta's `HELD <digest12>` takes one slip of any kind by the same measure. Tests `an_id_copied_with_slips_says_the_session_read_to_the_end`, the old `slip_in_the_echoed_id` case rebased (two slips are a copy, eight are not); 5 mutation cases caught, two stale anchors in notes/mutation-check.py repaired (one had matched two places since check_held was added). Backup: predeploy-220335.
- 22:06:04 deployed: a layer whose own cache entry was missed holds no delta over it (watchdog.entry_missed, read by layer_entry_age) — the entry is gone however lately its reads say it was read, and a delta built over it would fork a session nothing holds and write the whole prefix again, for a delta no fork would read. The high layer's ping missed at 21:56:18 (593K written, 1% read) with its last read 41 minutes old; the mark stands until the load that writes the entry clears it (base.sh), and a layer sealed since the miss answers it. deltas() then asks for a layer refresh ("its own cache entry is cold") instead. Test `a_layer_whose_entry_was_missed_holds_no_delta_over_it`; 2 mutation cases caught.
- 22:10:41 deployed: a transcript that is not there is no request and no traceback (session_fork_check.requests): a ping's throwaway fork is deleted as soon as its verdict has been read, and a check running beside it wrote a traceback into warm.log (three of them on 2026-09-22, each five lines with no timestamp, which every `awk '$1>=...'` view of the log keeps showing). The caller reads OK or MISS and anything else as no verdict, so the ping is tried again as before, now saying what it found. Test `a_transcript_that_is_not_there_is_no_request_and_no_traceback`; mutation case caught. The ping test's assertion follows the verdict's wording rather than the traceback's.
- 22:19:56 deployed: a marker line inside a change block is refused as before, and the refusal now says which line it stands at and both ways out — either the block's own line is missing and it has taken in the next block, or the line belongs to the text, and then two blocks around it cost nothing where writing the file whole costs the session the file's whole text. 20 of the day's refusals were a `=======` in a replacement (10 a `>>>>>>> REPLACE` in a search, 6 a SEARCH line), fix-251's among them. The rule itself stands: a bare `=======` in a replacement cannot be told from a block that swallowed the next one without reading the file, and a markdown heading rule is such a line. Test extended (`a_block_that_lost_a_line_of_its_own...`); 2 mutation cases caught. Backup: state/dev-patches/predeploy-221956.
- 22:18:14 the high layer refreshed and sealed (601,541 tokens) over its stable base loaded again at 22:17:35 (276,298), the first refresh to finish since 20:12: the acknowledgement fix let the reload through. Its forks take the new layer, the delta of 21:15 standing on the layer that is gone being read as none (v2.delta_record); the next delta is built when 2K has moved. state/high-stable.miss and state/high-layer.miss are cleared by the loads that wrote those entries; max-stable.miss and xhigh-stable.miss stand, each taken by that base's next refresh.
- 22:21:34 deployed: protocols/_production.md says the same two ways out of a marker line inside a block (two blocks around it, or the file whole), so a session reads it before it spends a request finding out. Backup: state/dev-patches/predeploy-222134.
- 22:28 committed and pushed as ac0f64c1 (the owner lifted the hold): the harness's work since 34901a81 in one commit, 37 files — the delta layer, the cache-entry accounting, the builds that said nothing, the session and task repairs, the check reporting and the review tools. Left for the run's own landings: PLANNING_LOG.md, HANDOFF.md, owner-ledger.md and tools/__pycache__.
- 22:51:28 deployed (the owner, after stopping the run: evaluate the state; then "fix the 128/147 hole"): an accepted task left in review with no review due has its commit made (watchdog.accepted_unmoved, in finishing). A verdict is what moves an accepted task to its commit (v2.cmd_verdict); a task accepted in an earlier round and checked again is put in review by checked() with no verdict to come — pending_reviews offers no review whose verdict is given, the stalled line leaves accepted tasks out, and finishing watched only checking and committing. Tasks 128 and 147 came to it so: accepted (reviews 129, 148), their landings interrupted by the reboot of 13:04 (landing checks failed in 1 s at 14:06 while the proof base was unusable), their finalizers ended without reporting, sent to the planner, queued again by plan-44 (cmd_queue read them afresh), checked again (passed 14:10 and 14:26) — and they stood in review eight hours, in no landing or check queue, their sessions pinged warm (23 pings, about 2.5M input-equivalent, two of them misses of 570K and 629K), 147 heading the planner's order and its deepest chain. Not while a review of it runs, nor while the graph is held (the planner's order first, as reopen_unlanded's commits wait); only with a final job and every deciding review accepting. Against the live state it matches 128 and 147 and nothing else (276 awaits its first review). The run is stopped: on restart, once the graph is released, both are committed and land in the next train (their branches stand 187 behind main, so the train merges main in; a conflict goes to the planner as any landing's does). Test `an_accepted_task_left_in_review_with_no_review_due_has_its_commit_made`; 5 mutation cases caught; suite 682 passed on the live code. Backup: predeploy-225128.
- 23:42 deployed (the owner, ~23:00: review the bases against the day's sessions and optimize for cost and above all quality; notes/plan-bases-upgrade.md, D1-D5 and D10): what a worker base holds is chosen by use. select_base_load gains the evidence of use (use_of: a session uses a theory when it reads it or its own writing names one of the names the theory defines; defined_names, own_writing), the frontier chosen within the layer's budget (layer_room: the target less the stable part and the layer's other entries, with the layer's measured overhead LAYER_FACTOR 1.075) by use per token from the last 60 sessions (FRONTIER_SESSIONS; it was a fixed 40 from 7), each theory used by at least 5% of them (FRONTIER_FLOOR); the founding tier rewritten to the founding theories its roles used (FOUNDING_MIN 2 of the last 400 sessions) and main left unchanged for 3 days (FOUNDING_QUIET_DAYS: a changing theory is the frontier's); what the rest of the list holds is judged by position (counted by name, two theories were chosen again and held in both parts); a founding index for a list that holds it (xhigh); the theory map's index cut at 90 characters of first clause (it was 100.9K tokens of the high layer where the design measured 56K); idea_candidates imported when first asked (at the top it made select_base_load unloadable where THEORY_MAP.md does not stand beside it — the cause of three tests that always failed in the dev copy, which pass there now). The lists: founding tiers, high 27 and xhigh 23 of 238 (176 of 226 had been used by no implementer or fixer in a week); frontiers, high 71 theories within its 273K, xhigh 55 (the floor binds before its 227K); the memory directory held without MEMORY.md; xhigh's founding index. Estimated loaded: high ~530K (601,541 measured today), xhigh ~457K (542,564). Tests: test_select.py (10), test_layer's frontier count read from its header and every worker base under the target; 13 mutation cases caught; the suite 693 passed on the live code. Backups: predeploy-233805, predeploy-234144 (the lists before, too).
- 23:52 deployed (notes/plan-bases-upgrade.md D6-D8): a layer is refreshed when what its delta has cost the forks that carried it reaches what a refresh costs — watchdog.carried (0.1 × the delta tokens each fork of the delta recorded at its launch, v2.delta_size, × its own requests, own_requests; and 2 × each delta build's write since the layer sealed, from warm.log) against refresh_cost (2 × the layer's tokens + 0.1 × the stable base's, from the records). The share rule (LAYER_DELTA_MAX 8%) and the frontier trigger (FRONTIER_MOVED 5, which asked a refresh 1h24m after the last, the old whole-file pace, and ran a dry-run selection every look) are gone; a cold layer entry, a missed fork and a refresh asked by hand still refresh, and the stable reference's drift is still said to the owner at 15K. base.sh says a base its layer takes over the target at the layer's seal (warm.log), rather than refusing it. xhigh switched to deltas (state/deltas: high, xhigh): its forks keep forking the layer until the watchdog builds a delta over the new one. Also: 13 mutation cases whose anchors no longer stood in the code (they guarded nothing: the marker refusal, the stable miss, the run count, the delta rules and others, some since before today) rebased onto the code as it is, and two keys renamed with their tests; every case of notes/mutation-check.py now names code that exists and a test that exists. Tests: DeltaCostTests (3), the fork's delta_tokens, the refresh by carried cost, the seal note both ways; 11 mutation cases caught. The suite 697 passed on the live code. Backups: predeploy-234944, predeploy-235201.
- 00:03 deployed: a layer is not built over a stable base the list no longer names (manifest.py stable-listed WHO: whether the stable snapshot's files are the files the list's stable part names now; base.sh layer reloads the stable base, saying why, when they are not, where it forked the recorded one whenever its entry was warm — with the founding tiers chosen by use that would have put the old 276K reference under a layer chosen for the new one, about 665K on high). On the live lists: high and xhigh name another reference (200 and 205 files out), max the same. And a bug of my 21:58 fix, found when the clock passed midnight: a base record with no seal time was read as sealed at midnight today (`date -d ""` is not an error), so after midnight every miss recorded the day before looked answered and the stable base warm; a record with no seal time is no seal now, and the test records its miss before any midnight. Tests: StableListedTests, the layer that reloads a reference the list no longer names (end to end, stopped at the fake load), the miss test made independent of the hour; 4 mutation cases caught. The suite 699 passed. Also 23:55: the fresh charge names each task's own tree (a task whose session is gone keeps its tree; a tree whose task is done or dropped holds work that never landed), and the run-specific note for the next planner is queued as an event (notes/fresh-start-2026-09-23.md). Backups: predeploy-235513, predeploy-000139, predeploy-000300.
- 00:09 deployed: DELTA_MIN 4,000 (was 2,000; notes/plan-bases-upgrade.md D11, report-M). Of the files a fork's stale line listed on 2026-09-22, high forks named 17% in their own calls (24% as forks of the layer) and xhigh forks 8%; a delta build costs the layer's read and its write, so the optimum is a build at ~3.7K tokens moved on high and ~5.2K on xhigh. The trigger tests take their moved tokens from DELTA_MIN. The suite 699 passed. Backup: predeploy-000939.
- 00:16 deployed: a reviewer is given its first read in its first message (v2.first_read, reviewer.md {FIRST}): the task's result, the end of its finalizer's log, its probes and its diff, rendered as `v2.py read result log probes diff` renders them — each source bounded as a read bounds it, the diff last and whole where it fits, otherwise as much as the batch's room holds with how to read the rest. Every reviewer of 2026-09-22 opened with that batch (104 of 104), a request each (about 50K on xhigh) before it could judge anything; the texts are written once either way. Tests: the reviewer's first message holds the four sources in order; the placeholder table knows FIRST; the protocol's old first-batch wording gone. 2 mutation cases caught. The suite 700 passed. Backup: predeploy-001630.
- 00:21 deployed: library-prompt.md, the system prompt of every base, says which founding theories a base holds — every one on the planner's base, on the others those their roles use, each other one named with what it holds in an index — where it said every base held the founding theory of every notion, which the founding tiers chosen by use made false for high and xhigh (a role told it holds every founding theory could take one it does not find for one that does not exist). The system prompt is part of every base's prefix: the owner's rebuild tonight reloads all three stable parts (high and xhigh because their lists changed, max because its entry is cold), so each base carries it. The owner reads changes to this file (bases-design §9, §12). Backup: state/dev-patches/predeploy-002059.
- 00:23 deployed: the sessions measured reach into v2's archive (select_base_load.archived_sessions: state/v2-archive.jsonl), where a session goes a day after its release — a window of FOUNDING_SESSIONS (400) was a day of sessions, not the week it is meant to be. The founding tiers chosen again with it: high 27 (133 sessions), xhigh 26 (156); the frontiers unchanged. Test in test_select; mutation case caught. Backup: predeploy-002313.

## 2026-09-23, from 00:35: the orchestrator improved at the level of its concepts (nothing committed: the owner's order)

The owner's order and the work plan: notes/owner-order-2026-09-23.md, notes/plan-orchestrator-concepts.md (findings,
concepts C1–C6 and their state). The data: notes/timeline.py (where each session's wall time went), notes/lifecycle.py
(every task's way from the graph to main, the machine's runs, the planner's turns), state/analysis/.

- 01:01 deployed (C1: the close is one transaction, index files edited by key). `v2.py change` takes `=== row THEORY`
  (the THEORY_MAP.md row's content; imports read from the theory as the call leaves it, `theory_imports`, which the
  tree's trouble and the recipes' reach now read too; a new row placed in ROOT's order) and `=== root THEORY [after
  OTHER]` (by default after the last of its imports ROOT declares), applied after the call's other changes; a change
  that writes a theory, ROOT or THEORY_MAP.md is answered with what the structural checks say of the theories it
  concerns (`sources_said`). `v2.py result ID` takes its text as a heredoc; `v2.py finalize` records a result the
  session wrote this round (since its start or its last resume, the new session field `resumed`) and says so, and a
  `v2.py result` chained after it is told it is recorded (`handed`, RESULT_ECHO 10 s, which a documents check's quick
  fix can race); in a task's own tree `--files` defaults to what the tree has changed. Protocols: _production.md
  (the keyed verbs and the sources told), _finishing.md (the one call, --files, bring-main only when told), _result.md.
  Why: 24% of implementer and 27% of fixer cost on 2026-09-21/22 was requests that did only bookkeeping (69M), and 1
  of 69 sessions made the protocol's one-call close. Tests: KeyedTests (6), four close tests in TaskTests, a guard
  test; 15 mutation cases caught, one anchor rebased. The suite 712 passed on the live code. Backup:
  state/dev-patches/predeploy-010127.
- 01:08 deployed (C4, rework prevented where it is written): a change that writes a theory is also told what it
  declares anew that the library has — a name of at least 8 characters with an underscore that one or two other
  theories declare, a statement of at least 30 characters another states word for word — and a name its
  THEORY_MAP.md row still offers that the change took out (`restated`, over `library_index`, 0.25 s). Why: of the 31
  rejections whose findings the state held, 14 were a notion or fact the library had (`path_term_inj`,
  `syntax_branch_eq_iff` three times, `map_filter_member`), three a row offering what the task removed; the
  library's own base rate is low (79 of 22,783 such names declared twice, 19 of 8,347 such statements). The
  declarations pattern moved to digest.py (DECLARED, with STATED), which select_base_load imports. Tests: one in
  KeyedTests; 5 mutation cases caught. The suite 713 passed on the live code. Backup: predeploy-010844.
- 01:15 deployed (C4c: evidence recorded, not narrated): the commit states the harness's record of the session's
  probes beside its check (`finalize.harness_validation`: "Probed in its session, as the harness keeps the runs: …,
  as the tree holds them, to the completion marker with no error (N runs)"), from `v2.probed_whole` over
  `probe_runs` — the probe report split into the runs as data and their text (`probes_text` formats them, as `v2.py
  read probes` shows). _finishing.md: the Validation paragraph holds what no record does (a measurement, an argument);
  reviewer.md: the probe record is the harness's too. Why: five of the 31 rejections whose findings the state held
  were a commit message misstating a run. Tests: the probe read test (a clean probe of another text, a cut probe of
  this one: neither a record), the batch hand-over's commit holds the probe record; 3 mutation cases caught. The suite
  713 passed on the live code. Backup: predeploy-011456.
- 01:20 deployed: the restatement hints read definitions too — a definition whose body, its arguments by position, is
  another theory's (`digest.definition_bodies`, in `library_index` as `definition BODY`): the library itself holds 27
  such pairs among 5,088 definitions (`native_derivation_cell_result` and `native_history_cell_result`, the two
  reports' `…_cell_report`), and 23 of the 51 fix tasks from #100 on consolidate what was stated twice. The reviewer
  protocol's wrap repaired. Tests: the library-has test; 2 mutation cases caught, one anchor rebased. The suite 713
  passed on the live code. Backup: predeploy-012021.
- 01:28 deployed (C2: a task's inputs delivered, not searched): a producing session's first message states the facts
  and definitions its brief's Inputs and Decided name, as its tree holds them, proofs left out (`{INPUTS}` in
  implementer.md and fixer.md, `v2.inputs_read` through show.py --statement: 0.1–0.5 s, 2–10K bytes on yesterday's
  briefs, bounded by INPUTS_BYTES 20K; `_def`, `.simps` and the like read by their definition; theories and files
  left to the session's reading; a name the theories do not state is said — HOL's own, one to make, or one that has
  moved). The implementer's protocol: consume them as stated, a contract used and never proved again. Why: 26–28% of
  producer cost before the first change, 55% of the files read then named by the brief; 7 of 31 rejections a named
  contract proved again. The first test caught a launch that would have failed in the one tree (a task without a tree
  of its own has none: `tree or PROJECT`). Tests: the launch message holds the named statement; misses, files, a
  theory and the bound; 7 mutation cases caught. The suite 714 passed on the live code. Backups: predeploy-012633,
  predeploy-012818.
- 01:34 deployed: the reviewer reads the harness's restatement findings over the task's whole change — `v2.py read
  restated` (`restated_text`: every theory the task changed, from where its branch left main or from HEAD in the one
  tree, through `restated`), in its first read between the probes and the diff; reviewer.md and _production.md say
  what it is (the harness's reading, which the reviewer judges). Tests: the reviewer's first message holds it; 3
  mutation cases caught. The suite 714 passed on the live code. Backup: predeploy-013424. Also: the watchdog test of a
  session gone cold while it waited for its answer waits for its background ping to end before ageing the session
  (it failed twice under the suite's load: the ping's own hit landed after the age was set). Backup: this entry's.
- 01:37 notes/run-report.py (analysis, not the harness): the run's efficiency and quality over a window of sessions —
  cost by role and its base share; producers' requests before the first change and doing only bookkeeping; closes;
  the new mechanisms' use (keyed edits, results given as text, what the change replies told, launches stating the
  brief's facts); rejections; landings, machine runs, planner turns. The baseline from 09-22 12:00–23:00 is in
  notes/plan-orchestrator-concepts.md; after the fresh start, `--since <the start>` reads the run against it.
- 01:38 deployed: _brief.md asks each fact or definition a task consumes to be named exactly under Inputs, since a build's or fix's session is given their statements (C2). Backup: state/dev-patches/predeploy-013804.
- 01:41 deployed: the task designer's and the designer's first messages state their brief's named facts too ({INPUTS}; the task designer read statements with show.py in 90% of its sessions before its first change). Test: the task designer's launch; 1 mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-014106.
- 01:46 deployed: the files the sandbox mounts over a session's working directory (.bashrc, .bash_profile, .gitconfig, .mcp.json and the like: a device inside the sandbox, an empty file outside it, at the tree's top, untracked) are no one's change — changed_paths leaves them out (sandbox_mount): the default --files of C1 would have committed them, and the tree's uncommitted work named them (the first episode's unowned list). Found reading implement-185's report of its refused check. README: the read sources listed (probes, restated, check). Test: the own-tree default with two mounts; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-014533.
- 01:49 deployed: a probe is found wherever it ran. The guard records the directory each probe of a session's call names as its --work (work_meter.probe_work: after a leading cd, $TMPDIR and the call's assignments filled in, links resolved), for its task (v2.note_probe_dirs, state/probes/ID/dirs.json); v2.probe_logs and keep_probes read those beside the task's own folder, so `v2.py read probes`, the reviewer's first read and the commit's probe record (C4c) see them, and a copy is kept when the session removes them. Why: the reviews of tasks 233 and 245 could not read back the completion marker their results claimed — the probes ran in folders of their own naming. Tests: the elsewhere probe read, kept and found once removed, a tree-link path not recorded twice; the guard's record; 4 mutation cases caught. The suite 716 passed on the live code. Backup: predeploy-014916.
- 01:52 deployed: a change that writes a theory is told what the repository's import graph says of it (import_graph: the tree's own tools/execution_support.source_graph over the theories it wrote, in a process of its own, 0.02–0.05 s: a cycle, an import that is not there) — with the source checks, the planner's standing last step before every hand-over, which sessions ran by hand. Test: a stand-in tool's refusal reaches the reply; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-015211.
- 01:53 the fresh start's note for the first planner (notes/fresh-start-2026-09-23.md, and its queued event in state/v2.json, rewritten under the state's lock) says what tonight's changes mean for briefs: name consumed facts exactly (their statements go to the session), the standing last step is the harness's at every change, rows and declarations by name, the probe record in the commit.
- 01:54 deployed: a reviewer's first message states the facts its task's brief names, as the task's tree holds them ({INPUTS}: what the work is to consume and not prove again — the principle of 7 of 31 rejections). Test: the reviewer's launch; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-015419.
- 01:56 deployed: where the commit message stands, agreed between briefs and the finishing protocol — 42 briefs named it in a folder of the planner's naming while the protocol's form wrote .build/tasks/{ID}/commit.md, and reviews noted the mismatch (tasks 211, 219): _finishing.md, the Deliverable's path, else the task's folder; _brief.md, `commit.md` bare. Backup: state/dev-patches/predeploy-015610.
- 01:58 deployed: a probe's renamed copy is read as the theory the probe tool says it stands for (probe.summary.json's from_tree), compared with that theory as the tree holds it — an intermediate the task did not change was "no theory the task changed" (#229's review asked for it). Test: an unchanged intermediate's copy; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-015818.
- 02:00 the full mutation check on a copy of the harness as of 01:55 (721 cases): every case caught but three — two whose anchors tonight's refactors moved (the commit's check paragraph, a probe's completion), rebased and caught, and one that had been guarded by nothing: the marking of a fork's miss on its base (cache_check), whose test wrote the mark itself; a test of the marking now (a read marks nothing, a miss marks the base it forked, a session's fork marks no base), caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-020026.
- 02:04 the change's new replies tried on the real library (a copy of theories/, ROOT, THEORY_MAP.md and tools/execution_support.py under $TMPDIR, removed after): a new theory with `=== root` and `=== row` declared after its import and its row placed in ROOT's order, the definition restating native_derivation_cell_result's body told; a row-offered lemma renamed away told; a self-import told by the real import graph, with the row's stale imports; each call 0.46 s whole.
- 02:08 deployed, off: ORCH_SUPPORT_APART=1 puts the supporting session outside the worker cap (C6, the owner's to set; with it two producers and a review work at once, a producer no longer yields to a waiting review, and the status says so). Default unchanged. Tests: two producers and a review; a running review holding no producer back; 3 mutation cases caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-020804.
- 02:10 the C6 switch is a state file (state/support-apart, or ORCH_SUPPORT_APART=1): background sessions do not take the launching shell's environment, so a switch in it would reach the daemon's dispatch and not every command's view of the slots. Mutation case for the file read; the suite passed on the live code. Backup: state/dev-patches/predeploy-021027.
- 02:13 deployed, off: state/grouped-repairs gives the planner's and the task designer's protocols a rule on a task's size against its fixed cost ({GROUPING}, grouping_text; C8, the owner's to set). Default unchanged (the placeholder renders empty). Test: the rule only with the switch, only in those two protocols; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-021250.
- 02:15 an integration test of tonight's pieces together: the theory, its declaration and row by name, the commit message and result in one change and the hand-over in the same call recording the result; the reviewer's first message with the brief's statements and the restatement reading; the commit taking the row and the declaration. The suite passed on the live code. Backup: state/dev-patches/predeploy-021509.
- 02:19 deployed: `v2.py read tree` (tree_state_text: the task's tree and branch, where it left main, its own commits past that, main's commits since then touching the files it hands over, what stands uncommitted — the sandbox's mounts and the harness's own left out), in the reviewer's first read before the diff; reviewer.md and _production.md name it. Why: reviewers and producers ran about 700 git status, diff, show, log and merge-base calls on 2026-09-21/22 to find this out. Test: the reviewer's first read; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-021840.
- 02:20 the fresh start's note (and its event) adds: a task need not bring main in before its hand-over for the check's sake — batches and trains check the work merged onto main; HANDOFF's working rule dates from the landing check in the task's own tree (#124).
- 02:20 implementer.md: the named statements are the tree's before the work — consume those the task rests on, and those its Deliverable changes are shown as they stand (the first wording told the session to consume every one as stated).
- 02:23 the full mutation check again (735 cases, the harness as of 02:30): every case caught but one whose anchor the C6 switch moved, rebased and caught.
- 02:25 deployed: the planner's status says beside each task that could start how many open tasks wait on it, directly or through others (waiting_behind: "startable now: 7 (2 wait on it) 10") — for its order, dependency before size; a task's wait to start was a third of its way on 09-22, most of it on blockers. Test; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-022458.
- 02:28 deployed: a change that takes a specific name out of a theory is told which DECISIONS.md entries cite it (decisions_citing, by their headings): task 275's review found its law entry stating the opposite of the delivered work, task 30's an entry silent on what it retired. _production.md says so. Test; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-022827.
- 02:32 deployed: the named statements leave out the bare `context NAME` blocks a locale's name brings (they said nothing of it; two of eleven blocks on task 139's brief). Test; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-023141.
- 02:34 deployed: `=== row THEORY after OTHER` places a new row beside OTHER's — THEORY_MAP.md is in four sections (the active graph, native source development, native execution refinements, export content boundaries), and ROOT's order alone could put a row in the wrong one; _production.md and the README say so. Tests: the section placement, an existing row given `after`, an unknown OTHER; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-023401.
- 02:36 deployed: health.py says the owner's switches while they are on ("switches on: support-apart"). Test; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-023548.
- 02:44 deployed: a planner is told what HANDOFF.md's graph, decisions and deliveries say now that its knowledge base's copy lacks (handoff_delta beside `## Now` and `## Open`: the items added or rewritten, the first lines of those taken out, bounded; the copy kept at the knowledge base's launch, keep_kb_handoff, and swept when it is no longer forked). Why: kb-10 was built at 04:44 on 09-22 and forked until 13:30, and plan-40 read the file again in six ranges; against the history, an old copy's delta was 8.4K characters, a recent one's 445. Tests: the planner's message, the copy kept at the knowledge base's launch, an old copy swept; 4 mutation cases caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-024359.
- 02:48 the full mutation check a third time (736 cases, the harness as of 02:58): every case caught but one whose test key named no test (the handoff copy kept at the knowledge base's launch); the key corrected and the case caught. Every case's key now names a test (two by pytest expressions). The analysis scripts' unused imports taken out.
- 02:50 deployed: the result form asks for `## Acceptance` — each clause of the brief's Acceptance and Decided and where the work meets it, read against the brief once more before the hand-over — and the reviewer's protocol names it as the session's reading, which it judges. Taught, not enforced (result_problems unchanged: no refusal for a result without it). Why: 7 of the 31 rejections whose findings the state held were a reading of the brief missed (a field at the wrong state, a law narrower than it holds, a reading without its locale). The suite passed on the live code. Backup: state/dev-patches/predeploy-024953.
- 02:53 deployed: what the harness tells beside the work fails soft (v2.softly: the sources after a change, the restatements, a task's tree, a brief's statements, the handoff's delta, the commit's probe record, the guard's record of where probes run) — a failure is logged as an ATTENTION and said in one line, never raised into the change, the read, the launch or the commit it rides on (the one-tree launch failure before its test showed the risk). Test: a change whose sources reading raises is written and says nothing of it; mutation case caught, seven anchors rebased and their cases caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-025318.
- 02:54 deployed: an index edit that raises is refused whole and said, as a change that cannot be made (changed_texts), rather than a traceback. The suite passed on the live code. Backup: state/dev-patches/predeploy-025405.
- 02:55 checked: `base.sh high pack` still builds and verifies its pack with tonight's digest.py (loaded estimate about 524K, under the 530K target); the two packs removed after.
- 02:57 deployed: `v2.py read tree` in the one tree names only the task's own uncommitted work (the paths the guard recorded as its, and those it hands over), not the other tasks' the one tree holds too. Test; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-025713.
- 02:58 the full mutation check a fourth time (737 cases, the harness as of 03:04): every mutation caught. (The one-tree tree read's case, added after, caught on its own.)
- 02:59 the restatement and tree reads tried on the stopped run's trees (read only): task 276's new `reach_step_rule` has `native_member_later`'s body word for word — a genuine duplicate — and tasks 44 and 176 leave rows offering names their changes took out; one coincidence of name only. Each read 0.4 s.
- 03:03 the test world ends its own processes before its directory goes (fakes.World.close: every process whose environment names its root): background pings and checks a test started outlived it and wrote their logs into directories they made again under /tmp — about four a suite run, none now. The suite passed on the live code. Backup: state/dev-patches/predeploy-030239.
- 03:05 the fresh start's note (and its event) adds: 138 of THEORY_MAP.md's rows name imports their theory no longer has, and `=== row THEORY` alone sets each right (tried on a copy: Presentation_Completion_Investigation's row now names its _Base and Native_Execution_Refinements, its content kept) — one small task for the planner to place if it wants it.
- 03:06 the fresh start's note (and its event) checked against the trees and corrected: task 44 also holds a new theory, 192 a new theory, 176 one modified file (its second was a compiled tool file).
- 03:08 deployed: the base in the lasting store (.build/tasks/base-lasting, the harness's own place by the owner's choice of 09-22) is no longer named as standing in a task's own directory — health.py said so on every run (task 144's review had asked). Test; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-030754.
- 03:10 deployed: each measurement's hold on the machine is recorded in the task's own folder (.build/tasks/ID/measurements.log: when, how long, what for, no other run beside it), where its review reads it — task 129's review found a claim left no durable record; _tree.md says where. Test; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-031023.
- 03:28 deployed: a task's passing state rendered for the planner, not written by it — the graph shows a parked task's reason and since when and a rejected task's rounds (stage_text), the status the landings of the last three hours with their commits (landed_lately, from finalized.json); planner.md: HANDOFF.md names the task and what it is for, never where it stands (405 of the 908 blocks by which the planners of 09-21/22 edited HANDOFF.md changed such words: commits, landed, parked, handing over, the order). README. Test; three mutation cases caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-032741.
- 03:29 notes/run-report.py counts the planner's HANDOFF.md edit blocks that change a task's passing state (C12's measure): 146 of 381 in the baseline window. Plan: findings 11–14, C11 decided against, C12.
- 03:32 repaired: the soft-failure test (test_change) called softly outside its fake state, so every live suite run since 02:53 wrote 'ATTENTION x could not be had' into the live v2.log (7 lines, removed; the log before in the backup). The call is inside the patch now. The suite passed on the live code and left the log as it was.
- 03:38 deployed: a hand-over needs no arguments in a task's own tree — `--check` left out is the repository's check (REPOSITORY_CHECK, --output .build/tasks/ID/check, batchable) for a commit with code and the documents check for Markdown alone; `--message` left out is .build/tasks/ID/commit.md; the reply names what it took. 109 of the 126 hand-overs whose record stands had named that check, nine one not runnable as written. _finishing.md: `v2.py finalize {ID}`, and what to name when it differs. The documents test now expects the repository's check where it expected a refusal. README; run-report counts argument-free hand-overs. Test; three mutation cases caught, the documents cases again. The suite passed on the live code. Backup: state/dev-patches/predeploy-033734.
- 03:40 notes/run-report.py gives finding 11's measure (idle working minutes, and those in which a task waited only on blockers past their result), from the sessions' own records, so that the run after the fresh start can be read against 349 of 638 and 246.
- 03:48 deployed, behind the owner's switch (off): C13, a continuation forks the work it continues — a task whose metadata names the task whose work it continues (`"continues": "N"`, the planner's; planner.md's {CONTINUES} says so while the switch is on) forks that task's last producing session instead of its role's base, while it is warm, not working, at the base's effort and model and within ORCH_CONTINUE_MAX (700K) (continued_session), is told whose work it holds and that its task is over ({CONTINUED} in implementer.md and fixer.md), and the watchdog holds that session until the task starts (watchdog.continuing). `touch state/continue-by-fork` turns it on. Data: 27 of 52 fix tasks with a fixer session named the task whose review they came from, its producer warm at the fix's start for 18; fixers spent 31% before their first change and grew a median 45K from a producer's 638K. With it, a correction the switch does not govern: a fork of a session (a planner of the knowledge base, a consultation of an author) is told what changed since the load that session holds — stale_of followed its own origin's sid, which names no layer, and manifest.py fell back to the layer standing now. health.py and run-report name the switch; README. Tests (three); ten mutation cases caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-034844.
- 04:00 deployed: the hooks and a session's harness commands say in v2.log when they take longer than ORCH_SLOW (2 s), and where the time went (v2.Stopwatch: the process's start — the interpreter and the harness's compilation — then each part: the gauge's context read, its mail, the machine's claim, its probes kept, its meter's lock, its reads and production; a change's writing and what the sources say). Why: theory changes took a median 0.8 s with no heavy run going, 7.7 s with one and 13.1 s with two (478 changes of 09-21/22, 1.4 hours of the sessions' tool time), every other change about half a second — and every part timed apart on the repository (the change 0.49 s with tonight's checks, the transcript reads 0.01–0.02 s, the production measure, the probe copy) was fast: the cause shows only under the machine's load, so the next run names it. The guard's line is named only when said (a guard runs on every call). Test; four mutation cases caught. The suite passed on the live code and left no slow line in the log. Backup: state/dev-patches/predeploy-035944.
- 04:00 notes/run-report.py sums the slow calls of its window (finding 15's instrument): by what they were and where their time went. Plan: finding 15.
- 04:04 C13's line to the planner (only while its switch is on) adds that a continuation's brief may name the findings it takes up by their place (the review file, its follow-ups by number) rather than restate them — the planner drafted those briefs itself, 1.5M output tokens and 3.6 hours of its time over 09-21/22. The suite passed on the live code. Backup: state/dev-patches/predeploy-040337.
- 04:07 deployed: the planner's status says the last hour — sessions working on average, and the minutes in which a slot stood free while a queued task waited only on work in its check, review, quick fix or landing (occupancy_text), from a line a minute the watchdog writes to state/occupancy.log (sample_occupancy; the last 2,000 kept). The status had shown the moment; the afternoon of 09-22 had fewer than two sessions working in 349 of 638 minutes, 246 of them with such a task waiting (finding 11). README. The full mutation run (763 cases) caught every case but one whose anchor C13 had moved: rebased and caught; four new cases for the occupancy, caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-040651.
- 04:11 the graph names every kind of park (a check the session asked for, a queued probe: seen on the live graph as 'parked for probe'); _production.md points a session's git reading to `v2.py read tree` too. The suite passed on the live code. Backup: state/dev-patches/predeploy-041058.
- 04:13 C13 (behind its switch): a producer whose review asked for follow-ups is held for ORCH_CONTINUE_GRACE (90 min) after its own work ended — it was released within a minute of its task's landing, before the planner, handling the landing, could make the follow-ups into tasks that continue its work; continuing() holds it from there until they start. Test; two mutation cases caught. README. The suite passed on the live code. Backup: state/dev-patches/predeploy-041255.
- 04:15 a walk test carries a continuation (C13's switch on) from the fork of its producer, in a tree of its own, through `v2.py finalize 2` with no arguments (its files, the repository's check, its commit.md), its check, its review and its landing, with no ATTENTION on the way. The suite passed on the live code. Backup: state/dev-patches/predeploy-041506.
- 04:19 deployed, behind the owner's switch (off): C14, a session's measurement holds the machine at most ORCH_MEASURE_MAX (600 s) — past it the claim lapses (only the reader that removes it says so), its session is told to time the one judgment its measurement is for with its theories loaded first, and the task's measurements.log records the lapse (measure_lapsed); a check advancing the base is not bounded. `touch state/measure-bound` turns it on. Data: 37 holds of 09-20/22, 3.0 hours, and 1.5 hours more of the machine emptying for them; four past ten minutes, 1.1 hours — the longest one background probe of 31 minutes (fix-278, 22:04–22:34, loading its theories and timing one judgment) with every check waiting. health.py and run-report name the switch; README. Test; three mutation cases caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-041847.
- 04:28 the restatement hints checked against history and made precise: replayed over the 68 landed changes of 09-21/22 that touched theories (each against its own library as it landed), the hints named 7 duplicates review had let through (110, 182, 208, 179, 40, 76, 34 — some consolidated by fix tasks since) and 15 row mentions of names the change took out, nearly all of them citations of the name's new home or notes of its removal, and one an `abbreviation (input)` digest.DECLARED did not read. Now a name another theory still declares has moved (no row or decision hint for it), a mention in a clause that notes its removal offers nothing, and DECLARED reads `(input)`/`(output)` modes (which the base's evidence of use reads too). Replayed again: one row hint left, and it was the abbreviation's. Test extended; four new mutation cases and two rebased anchors caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-042733.
- 04:30 _production.md says what each hint asks: a name or statement the library has — reuse it or name what differs; a name taken out that its row still offers — correct the row, which says what the theory offers now; one a decision entry cites — correct the entry where it states the present (its contracts), and leave it as the record it is elsewhere. Replayed over the 68 landed changes, the decision hint named 21 citations in 10 of them, most in dated entries; the sentence had given no guidance for rows and decisions at all. The suite passed on the live code. Backup: state/dev-patches/predeploy-043011.
- 04:32 README: the slow-call lines (ORCH_SLOW, v2.Stopwatch) under Hooks. Backup: state/dev-patches/predeploy-043243.
- 04:34 the fresh start's note (and its queued event) names the four doubles the replay found standing in HEAD, for the first planner to judge.
- 04:37 the health screen shows the last hour's occupancy too (the planner's line, for the owner). The final full mutation run: 772 cases caught, one anchor that C14 had made ambiguous rebased and caught; the health line's case added and caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-043644.
- 04:41 two form tests no longer depend on where the harness copy stands (a temporary project with its theories/ for the directory check; the render test looks for what it means — nothing left unfilled — not for an empty log, which a git status outside a repository also writes): a copy's suite now fails only test_layer's six, which read the live project by design. The suite passed on the live code. Backup: state/dev-patches/predeploy-044041.
- 04:45 a read's guard counts, in its session's meter, whether it found its call in the transcript within BATCH_WAIT and how long it waited (batch_lookups; run-report sums them): read from the transcripts of 60 sessions, a read's guard took a median 0.64 s against 0.10-0.16 s for every other call, the wait for its call's line, which nothing recorded the outcome of — if the line is seldom there in time, the per-batch byte bound is seldom enforced and every read pays the wait. (The timeline's per-call durations charge a call from its request's start, so a read's 2-3 s there was its request's.) Test; mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-044441.
- 04:48 the investigator's first message states its brief's named facts too (C2): the harness computed them for every producing role and the investigator's protocol had no place for them, so they were dropped. Test (every producing role's protocol has the section); mutation case caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-044736.
- 04:49 README: the read guard's lookup counters. Backup: state/dev-patches/predeploy-044903.
- 04:50 the fresh start's note (and event): Q9's tracked compiled file can be removed by a task now (finalize.stage admits a tracked, ignored path's removal since 09-21).
- 04:56 deployed, behind the owner's switch (off): C9, the review beside the check — with state/review-beside-check a build's or a fix's review starts when its result is recorded (pending_reviews takes a task in its check); an accept waits for the check and is committed when it passes (accepted_early), an accept of work that then fails its check is void (its reviews' verdicts cleared) and the fix is reviewed again, and a rejection waits for the check's end and reaches the session with the check's failure, if any, in one fix round (rejected_early). The reviewer's first line says the check runs beside it ({CHECKED}; 'Its check has passed' otherwise). With the switch off no new branch is taken. Data: from result to commit a median 18.4 minutes on 09-22's afternoon; begun at the result, the review would have ended a median 8.2 minutes sooner. health.py and run-report name the switch; README. Five tests (the dispatch starting the review during the check among them); eight mutation cases caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-045625.
- 04:58 notes/run-report.py measures C9's effect: from a task's result to its commit, a median 21.3 minutes over the baseline window's 60 tasks.
- 05:01 C9's line to a reviewer beside the check says the finalizer's log read for it may be an earlier check's (a re-check after a fix). The suite passed on the live code. Backup: state/dev-patches/predeploy-050035.
- 05:02 the certifying full mutation run: 783 cases caught, one anchor C9 had moved (the reviewer's statements) rebased and caught. Backup: state/dev-patches/predeploy-050246.
- 05:03 the fresh start's note (and event): investigations get their brief's statements too; the argument-free hand-over, so a brief's Acceptance may name the repository's check without its command; lines rewrapped.
- 08:23 deployed, from reading the last session of each role (notes/plan-owner-word-2026-09-23.md, its findings): the small-read note sums the previous request's own calls, recorded by id, and says nothing of a request that ran more than reads (implement-192 was told 3,966 bytes after reading about 33K; fix-279 had a probe counted); a batched `ask` group takes a bare target or the previous one (implement-192's second question refused); the queued measurement says `v2.py end` does not end a producing turn (fix-279); a refused done result names its unwritten repository deliverables and the argument-free hand-over, and the finalizer says a task's .build folder is its record, never committed (investigate-254); `=== append PATH` adds a log's next entry with nothing to match (plan-47's whole batch refused for a recurring SEARCH text; planner.md and _production.md name it); the one-change note is no longer said of a session's own record under .build/; a session's first message gives each DECISIONS.md entry its brief names by heading with its lines, headings many entries share left out (design-258 grepped for them: 23 of the last 41 briefs citing DECISIONS get their entries placed); a re-review's resume carries its first read — result, log, probes, restated (review-251). Tests; ten mutation cases caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-082326.
- 08:31 deployed: C10, the landing reuses its check batch's build (the owner's yes) — tools/incremental_check.py check --keep-heap stores the rebuilt theories' heap without selecting it and reports it as kept_context (heap_flags, kept_context; tools/test_incremental_check.py KeptHeapTests); a batch of the repository's check keeps its heap, its output in .build/bases/ (heaps are path-bound), and is recorded by the content it checked (train.record_build: its tree's entries, the planner's state files aside); a train whose tree has that content, on the base the batch stood on, lands on the batch's build with no check of its own — adopted as the base by settle_pointer, its receipts retained, the lineage recorded, the commit's Validation naming the batch's check of the same content (kept_build); a base part nobody adopts keeps its reports and loses its heap and bulk after BASE_KEEP; run-report counts the trains that landed so. Isabelle cannot join two heaps, so this holds only where nothing landed between the batch and the train — the rate C9 raises. ORCH_BATCH_KEEPS_HEAP=0 turns it off. Tests; six mutation cases caught. The suite passed on the live code; the checker's tests pass. Backup: state/dev-patches/predeploy-083053 (tools/incremental_check.py is the repository's, its change seen by git diff).
- 08:40 deployed: C7, the reviewer corrects words (the owner's yes) — a reviewer writes in the repository only its own record and the reviewed task's (.build/tasks/ID/: its verdict, its scratch, the task's commit.md and result.md, never its finalize.json or brief.json) and, by `=== row THEORY`, the row of a theory the task changed when the task hands THEORY_MAP.md over (work_meter.reviewer_write_refusal); a theory, code, ROOT or a decision entry is refused as a finding (a reviewer stands in the reviewed task's tree, which no guard kept it from writing before). Its scratch outside the repository stays its own (read from every reviewer session since 09-19: review.md, diffs and rows under the task's folder, $TMPDIR). An accepting verdict names what it corrected under `## Corrected`, in backticks; verdict_problems refuses corrections on a rejection and a named file other than commit.md, result.md, THEORY_MAP.md; the planner's commit event carries "Corrected by its review: …". protocols/reviewer.md says so. Tests; nine mutation cases caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-083943.
- 08:46 deployed: C15, a follow-up's brief begun by the harness (the owner's yes, "if information quality stays the same or increases") — `v2.py follow-up TASK:ITEM,ITEM...` (several reviews' in one; `--kind build` when not a fix) writes a draft brief under the planner's drafts from the last verdict of each task's review (verdict_file_of, follow_items: numbered items by their numbers, bullets in order): Serves naming each review and its follow-ups, Inputs the review file and the names the follow-ups give exactly as given (backticked names with `_`, `.` or `/`, and theories named bare that the tree holds; follow_names), the follow-ups verbatim, quoted, under a new form field `From the review:` — and every judged part (why now, the files, what shows it done, Decided, Plan, Size) marked `<<PLANNER: …>>`; brief_problems refuses a brief with a mark left, naming its fields. It prints the edit op to place it. Quality: nothing is summarized; the session now reads the review's own words in its brief where the planner's restatement stood (read on 272:1 + 247:1,2 against the planner's b-ncp). With it, a gap of C13 closed: `v2.py edit` creates and rewrites now carry `"continues": "N"` (checked to name a task) — before, only TaskCreate's metadata could, and the planner places tasks by edits. protocols/planner.md says so. Tests; eight mutation cases caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-084528.
- 09:05 deployed, switch off: the per-role reasoning layer (the owner's word: "design and build the per-role reasoning layer which I will then either activate or not") — `state/role-layers` (or ORCH_ROLE_LAYERS; its words name roles, empty or `all` every role that forks a base: v2.role_layers). While a named role is wanted (a session of it within ORCH_ROLE_LAYER_IDLE, 2 h, or a queued or staged task it would take: role_wanted), the dispatch's role_layer_care has role_evidence.py read, in the background, what the run has shown of the role — its last 12 ended sessions' requests, requests before the first change, cost, the harness's notes (its counters and mail left out) and refusals most often, and the blocking findings of the last 60 reviewers' rejections of its work, taken from the verdict's own change in the transcript (a review file that now holds a later verdict is not read as the rejection's); a reviewer's layer, the rejections and what became of each — then forks `layer-ROLE` from the role's base with that and the role's protocol (generic_protocol: each session's own parts as `<BRIEF>`, `<ID>`), protocols/role-layer.md: reason once for every session of the role, at most 12 practices each with its evidence, no tool (work_meter refuses every call), ending `ROLE-LAYER READY`; sealed on that line (role_layer_replied), it is what launch forks for the role (role_layer_of: sealed, warm, forked from the base as it is now), each fork told so (`{LAYERED}` in _inherited.md, layered_text); rebuilt when its base is rebuilt or refreshed, when cold, or past ORCH_ROLE_LAYER_AGE (4 h) with 6 sessions ended or a rejection since (rejected_at, recorded by cmd_verdict); until sealed the role forks its base. The watchdog holds it (held) while wanted and lets it go when not wanted for 2 h or when its switch is off; its reply may end its turn (ctx_gauge.may_end); its forks count in the delta's carried cost (watchdog.carried). health shows each switched-on role's layer; run-report sets each role's sessions that forked its layer beside those that forked its base (requests, before the first change, rejections, cost; medians) with what the layers cost, and now also counts C7's corrections and C15's drafted briefs. Read on the live data: the implementer's evidence 13K characters (12 sessions, median 19 requests, 6 before the first change, 6 of 12 tasks rejected, 10 findings), read in 0.3 s. Tests (RoleLayerTests: five; test_delta's carried); nineteen mutation cases caught. The suite passed on the live code. Backup: state/dev-patches/predeploy-090426 (new files: role_evidence.py, protocols/role-layer.md).
- 09:11 coherence (task 7 of the owner's word): the full mutation check over 838 cases on the dev copy — 833 caught at once, two anchors rebased (the small-read note and the note to batch, both changed by the per-session pass's fixes) with a case each added for what those fixes made (a request that did more than read is no small read; no note to batch for a session's own record under .build), and a C7 case for a reviewer standing in a task tree (its folder through the tree's .build link, test added), all caught. README: C7 and C15 described beside the finish, the role layer among the switches, the roles table and the parts, and what was built on 09-23 and not yet run live. The first planner's queued event (notes/fresh-start-2026-09-23.md) now says what C7 and C15 change for it. The concepts plan's State and the owner-word plan's as-built notes brought up to what was built. The suite passed on the live code (756). Backup: state/dev-patches/predeploy-091030.
- 09:25 committed and pushed on the owner's word ("Ok commit and push all the work you did"): 6a4b17be (tools/incremental_check.py `--keep-heap` and its tests) and b798ff0b (the harness's work of 2026-09-23, every entry above from 01:01). Left out as not this work: HANDOFF.md, PLANNING_LOG.md and the owner ledger's Q12 (the run's own state of 09-22, the finalizer's to land), the tracked tools/__pycache__ .pyc, and the sandbox's empty placeholder files.
- 10:05 deployed, the owner's word of about 10:00: (1) C9's gap — a review still under way when its check failed had its verdict refused ("not awaiting a verdict (it is fixing)"), its reviewer unable to end its turn, and the fixed work's review began from nothing. Now the reviewer is told the check failed (`reviews_going`), and its verdict counts (verdict_during_fix): a rejection joins the fix round — in the fix's message if it has not begun, by mail to the session fixing if it has, as `rejected_early` with the next check's end if the fixed work is already being checked — and counts as the round's rejection; an accept of the failed work is void and the fixed work reviewed again; the record is cleared when a review begins anew or its reviewer is lost. (2) C14's window is a variable: `measure_max`, the seconds `state/measure-bound` says, else ORCH_MEASURE_MAX, now 180; the protocols name it by `{MEASURE_MINUTES}`. _tree.md: a held measurement is extremely expensive (every other run waits), so it is quick and sized to fit the window. (3) `v2.py measuring --shared "what"`: a measurement beside everything else — its next foreground check goes past the machine's order and the limits of heavy runs and probes (another task's held or queued measurement still first, the memory floor kept; a probe bounded at the window), holding nothing; when the call ends the session is told the machine's load over it — the CPU's share busy and the share of the time runnable work waited for a CPU (/proc/stat and /proc/pressure, exact over the interval), memory in use on average and at its peak (`v2.py sample-load`, a sample a second, ended with the call), memory stalls, the runs counted — and what that says of the number (load_verdict); a held measurement's record now carries its load too; both in measurements.log. (4) The role layer reasons over the content as well as the evidence: its evidence gains the work ahead (the tasks its sessions will take next, each with its Deliverable and the names its brief gives) and what its last sessions worked on; protocols/role-layer.md asks first for `## The work ahead` — for those areas, what the library it holds already states that the tasks should consume (by name, where, its contract), how those theories are built, what is easily confused or duplicated, what it does not hold — then the practices, at most ORCH_ROLE_LAYER_WORDS (1,500) words; it is rebuilt when half its work ahead is done (after ORCH_ROLE_LAYER_SETTLE, an hour). Tests (the shared measurement, the load and its sampler, the window, four C9 cases, the work ahead); nineteen mutation cases caught, one anchor rebased. The suite passed on the live code (763). The full mutation check after it (857 cases): 853 caught at once, four anchors this batch moved rebased and caught. Backup: state/dev-patches/predeploy-095558b. Then the owner's switches turned on: continue-by-fork, measure-bound (180), support-apart, grouped-repairs, role-layers (every role); review-beside-check left off. The first planner's queued event says what that means for planning.
- 10:31 deployed, the owner's second word (notes/plan-owner-word-2026-09-23-b.md): (1) C9's re-review: every verdict keeps the files it judged (`.build/tasks/RID/reviewed/`, snapshot_review), and every re-review — after a rejection, after an accept voided by a failed check (its reviewer now held for it: watchdog.held), after an accept whose task came back — resumes the reviewer that judged it with what changed since its verdict, mechanically (`v2.py read since`, since_text: each file of the change then or now that differs, a unified diff from what it judged to what stands; a file new to the change compared with main's), before the fix's result, log, probes and restatements. Before, only a rejecting reviewer was resumed, told to find the change itself; after a voided accept a fresh reviewer read everything again. Then `state/review-beside-check` on. (2) The shared measurement is admitted as any run of its kind (its slot, the machine's order, the memory floor) — the only difference from any run the hold it does not take, its probe bounded at the window, its load reported; `v2.py measuring` has no default: `--exclusive` or `--shared`, bare refused naming both (MEASURE_CHOICE); _tree.md and _checks.md say so. (3) The role layer thinks and writes nothing: its thinking stays in the context its forks resume (plan-47: a request of 31,593 output tokens, nearly all thinking stored as a signature, grew the next context by 34,819), so its message asks it to think through the content of the work ahead and the practice the evidence calls for and to reply with the done line alone; its forks are told whose reasoning precedes them. (4) Four layers in the order of their change: the stable base → the medium layer → the role layer → the churn. The role layer forks the medium layer (`WHO:layer`, medium_record; FALLBACK kept) and outlives every delta rebuild; each role's churn (`churn-ROLE`, protocols/role-churn.md, role_churn_care) is a fork of its role layer holding the shared delta's text, rebuilt when the shared delta's digest moves and the role is wanted, sealed on `HELD digest` with the shared delta's snapshot copied as its own, so stale_of counts what changed from the churn; the role's sessions fork the churn, else the layer, else the shared delta; carried() follows forks through churns and layers and counts each churn's write. (5) The run's console: dashboard.py (stdlib server on 127.0.0.1, a token per start, the X-Token header for controls, other hosts refused) and dashboard.html (views: the run, sessions with their turns, calls, batching, refusals, notes and production, tasks with their files, checks, the log; controls: switches, holds, dispatch, start and stop, queue, drop, tell, ping, release). Read on the live data: every view under 2 s (the whole session list 1.6 s; plan-47 whole: 47 requests, 36 calls, 78 items). Tests: two re-review cases, the four-layer case, the measurement modes, four console cases; mutation cases added and three older ones rebased (the carried arithmetic, the shared measurement). The suite passed on the live code (770). Backup: state/dev-patches/predeploy-103106c (new: dashboard.py, dashboard.html, test_dashboard.py, protocols/role-churn.md). The full mutation check after it (874 cases): 865 caught at once, one older case and eight anchors this batch moved re-pointed and caught. Nothing committed (the owner's hold).
- 10:54 deployed, the owner's question on warmth and the updates' cost: (1) the shared delta is pinged only while a role forks it (`v2.py base-forked WHO`, shared_part_forked; warm_daemon.sh asks before `base.sh WHO warm` — the daemon reads its loop once, so from its next start): with every role of a base on its own churn nobody read it, and each ping read about 60K for nothing; a role that falls back to it once it is known cold (entry_cold) forks the medium layer instead, told what changed since, rather than writing the whole prefix again (about 1.2M). (2) A role layer serves until its successor seals, after a medium refresh too (it and its churn hold what the refreshed layer took in; its forks are told what changed after the churn); churns are built only over a layer on the medium layer as it is (role_layer_current). (3) Holding by cost: a role's layer or churn is held (pinged) while the pings since its last use — every fork or churn build marks `used` — cost less than building it again (watchdog.worth_holding; its build cost measured from its own request at seal, its ping 0.1 of its context; estimates where unmeasured: 200K, 70K, 60K), in place of a fixed two hours. (4) A churn behind the delta still serves and is built anew when what its staleness has cost the role's forks — each fork behind it counted (behind_forks), at ORCH_STALE_READ (4) a token moved — reaches its build cost, in place of a build per wanted role at every delta move. (5) The separate hourly rebuild of a role layer for its work ahead folded into the age rule (four hours, and the run has shown more or half the work ahead is done). (6) A medium refresh's cost counts the role layers it builds again (refresh_cost). Tests (the shared part and the cold fallback, holding by cost, the churn's staleness rule, the refresh cost, the successor serving); eight mutation cases added, three superseded ones removed. The suite passed on the live code (771). Backup: state/dev-patches/predeploy-105358d. Nothing committed.
- 11:03 deployed, the owner's question on the fixers' calls per request and on prose: read from the 09-22 afternoon's transcripts (12:00–22:37). The ratio misled on one side: sessions batch by chaining commands in one call — fixers made 1.03 calls a request but 4.1 operations (implementers 4.2, reviewers 5.7, designers 6.5), and each harness-ended turn left a synthetic "No response requested." entry the console counted as a request. It was real on the other: 97 of the fixers' 703 requests and 77 of the implementers' 435 began where the protocol puts them in the request before — a change on a clean reply, then another change, its probe or the hand-over — 95 of the fixers' 103 such pairs (by the looser count) with nothing in the first reply to wait for (56 another file, the probe or the hand-over; 39 the same file again), each a context of about 635K read again (about 12M together in the window). Prose: the fixers' visible text was 615 tokens in 703 requests (0.05% of their 1.28M output tokens, the rest thinking and calls), their calls' descriptions 4.7K. Changes: role_evidence.call_ops (a call's operations: its commands split at ; && || and new lines, heredoc bodies aside, each change block one) and joinable (the protocol's rule, a correction or a reply with source checks or restatements excepted), used by the console (operations per request and joinable requests per session and marked per request; synthetic entries no longer requests), run-report (per role) and the role layer's evidence (its measured batching line); _production.md's **No prose**: nothing outside a command or a file is written — no sentence before a call, no summary, no call description — the owner's own conversation excepted. Tests; five mutation cases. The suite passed on the live code (772). Backup: state/dev-patches/predeploy-110315e. Nothing committed.
- 11:30 deployed, the owner's third word (notes/plan-owner-word-2026-09-23-c.md): (1) a producing session's change that writes a theory of its tree says `--probe` or `--no-probe` — no default (the owner: "a deliberate choice again"), and saying neither is refused, nothing written (probed_theories decides what counts: theories/*.thy of the session's tree; a change of any other file says neither, as the owner asked); `--probe` probes the theories it wrote as it left them (change_probe: the machine's admission as any probe, bounded at PROBE_SECONDS, `.build/tasks/ID/probe-change-*`, recorded as its probes are) and its reply says what the probe found (probe_said: complete or not, at most eight error lines, the time, the log); `--no-probe` when more changes are to come. The guard reads the flag (CHANGE_OPEN); _checks.md and _production.md's example say so; the first planner's event says a brief need not plan a probe after each change. (2) The console: the task graph (/api/graph and an SVG view laid out by the longest chain of blockers, each node where its task stands — waiting on which blockers, ready, running, parked for what, waiting for or in a check batch, reviewed, fixed, committing, waiting for or in a landing train, landed, with the planner; the done ones within N hours on a toggle); the machine (/api/machine: each run from the watchdog's snapshot with its kind, whose, processes and memory, the slots and the memory floor, the holds, the probe queue, the shared measurements, the occupancy); batches and trains (/api/checks: both queues with their states, the batch and train logs opened in place, the passed trees, the kept builds). (3) The console follows its source: /api/version; the page reloads itself when the server's start or dashboard.html changes; the server re-executes itself — same port and token, from its main thread after the server stops — when dashboard.py, v2.py, role_evidence.py, watchdog.py or train.py changes and compiles (compiled in memory; a file that does not is not run). Read on the live data: the graph 46 open tasks, 42 edges; each view under 20 ms. Tests (the flag and the probe with a stub probe tool, the graph's statuses and edges, the machine's runs, both queues, the re-execution and a non-compiling source); ten mutation cases. The suite passed on the live code (778). Backup: state/dev-patches/predeploy-112137f. Nothing committed.
- 11:54 deployed, the owner's word on the console ("extremely crooked … optimized for me to be able to monitor, review, control the runs"), round 1 of its redesign — the page alone (dashboard.html), on the server's endpoints as they stand: a header on every view with the run's state, the daemon, the holds, the heavy and probe slots and the live sessions; the views in the owner's three jobs — Monitor (Now, Task graph, Machine, Batches & trains), Review (Sessions, Tasks, Log), Control. Now: what needs the owner (the daemon down while the run is active, the holds, the log's ATTENTION lines of the last 3 h, one of each kind, the questions sessions ask, the tasks with the planner, a whole-machine measurement waiting, events for the planner), counted on the nav from any view; the pipeline as lanes left to right as tasks move (empty lanes narrow); the live sessions with their task's subject, duration, requests, context and quiet time; the machine, the switches, the bases and role layers; the log's events (starts, checks, landings, rejections, parks) newest first. Sessions and tasks searchable and filtered (by role; by where a task stands); a session opened whole as metric tiles, its production, and its requests collapsed to one line each (their commands, calls, operations, joinable or refused marked); a task with where it stands, telling its sessions, its sessions and its records as tabs. Times: transcripts' UTC read as UTC, the log's local time as local, a 24-hour clock with the date when not today; the log with a line per day. Every view read on the live data through a stand-in DOM in node (no view raises). notes/console-screenshots.sh takes the new views (now graph machine trains sessions tasks log control; the last round's PNGs removed first). The console's tests pass on the live code. Backup: state/dev-patches/predeploy-115438d. Nothing committed.
- 12:01 deployed, the console's round 2, from the owner's screenshots of round 1 (every view at 1440 px, one session and one task whole, the phone): the pipeline's cards no longer spill out of their lane (a line-clamped subject sized its lane's column to its whole length); panels no longer stretch to their neighbour's height (the task's "where it stands", the Now page's sessions); a session's requests no longer run past the page (a one-line command sized the list to its length); another tool's call shows as its name and subject, not its JSON, and counts one operation, as role_evidence counts it (the console counted TaskCreate's JSON by its semicolons and lines: implement-192's first request read 21 operations for six calls; dashboard.py, a test case and a mutation case); the graph's nodes are opaque, each later column ordered by where its blockers stand (fewer crossings), and hovering a task lights what it waits on and what waits on it; the Now page's sessions list the six that ended last beside the live ones, with how long each ran; the attention items name a planner task's subject; the activity leaves out the harness's housekeeping (a parked session told of a background run, the base following main, a check's "passed (alone)" beside its "passed in", layer refreshes), which the log dims; the batch and train logs show six with the rest on a click; the task view's records take two thirds of the width (a brief's own lines no longer wrap twice); a 24-hour clock everywhere. The console's tests pass on the live code; the mutation case caught. Backup: state/dev-patches/predeploy-120119e. Nothing committed.
- 12:06 deployed, the console's round 3, from the owner's screenshots of round 2: at a phone's width a session's row stacks its figures under its name (they overlapped); the session and task lists sort by any column on a click of its heading (again: the other way; what a row lacks last either way; kept while the page is open) and show 150 rows with the rest on a click, kept open across the page's refreshes, as the batch and train logs (six) and the trees that passed (eight) now are; the Now page says the run is stopped among what needs the owner, with the way to the controls. Every view read on the live data through the stand-in DOM, sorted both ways. The console's tests pass on the live code. Backup: state/dev-patches/predeploy-120602f. Nothing committed.
- 12:07 deployed, the console's round 4, from the owner's screenshots of round 3: a table with nothing more to show left the text "null" under it (the check batches, the landing trains); the phone's session rows and the sorted lists read as intended. Every view read again through the stand-in DOM, no stray text. The console's tests pass on the live code. Backup: state/dev-patches/predeploy-120749g. Nothing committed.
- 12:12 deployed, the owner's word "in some menus for example tasks I cant see all of the table collumns and cant see how to scroll to see them": a table's sideways scrollbar was under its last row (150 rows down in Tasks and Sessions). Now a table scrolls in a box of its own, a long one (over 15 rows) at most the window's height with its header held at the top, so its sideways scrollbar is on screen; a shadow marks the side where columns are out of view; its scrollbar is drawn visibly in the dark theme; the subject column narrows with the window (a third of it) and headings wrap; cells are narrower below 1250 px. The page's refresh (every 6 s, 30 s on a session or task) now keeps what the owner scrolled — each table, the graph, a text, a lane — and what was opened or closed on a session (its requests, messages and results, by key; before, an opened request closed again at the next refresh). notes/console-screenshots.sh also takes Tasks and Sessions at 1100 px with the scrollbars shown. Every view read through the stand-in DOM. The console's tests pass on the live code. Backup: state/dev-patches/predeploy-121246h. Nothing committed.
- 12:19 deployed, the owner's word "The performance seems to be poor there is a noticable lag between pressing and it loading": timed on the live state, every endpoint answered in 1-30 ms but the session list, 1.65 s at every call — warm too: the parsed-transcript cache was emptied past 200 entries and there are 298 sessions, and the Now page asks for the list at every refresh (its sessions that ended last). Now each session's summary is kept apart from its whole conversation (small; a transcript parsed again only when it grows), the last ORCH_DASHBOARD_KEEP (40) conversations kept whole, under a lock (the server answers in threads), and every summary read in the background at the start (the server starts again at each change of its source): the list 37 ms warm, 45 ms three seconds after a start. /api/version says the transcripts parsed (a test: a second list parses none with no conversation kept; two mutation cases caught). The page asks for its view's own data at once with the shared data and the source check (three rounds were one after another), one fetch per address a refresh; a click shows its tab and dims the page at once; a refresh superseded by a later one (a click, the timer) no longer replaces the page with the view it was for. The console's tests pass on the live code (8). Backup: state/dev-patches/predeploy-121933i. Nothing committed.
- 12:42 deployed, the owner's word "Ok now need a bases and layering dashboard - bases, layers, token amounts, outdated data (computed inteligently not just some random number), how they are organized, last ping, ttl to next ping, also a general cost screen that shows statistics regarding costs all facets caches, normal costs, comparisons, charts": two views of the console, each computing nothing the harness does not. **Bases & layers** (/api/bases): each base's parts — the stable reference, the medium layer, the delta (delta_record) — with their own tokens (a part's context less the one under it) and prefix, which one its roles fork (base_file), and each part's own cache entry: its last read (the harness's marks: WHO-base.hit for what the roles fork, WHO-stable.hit, WHO-layer.hit, hits/NAME), when it expires (an hour after: promptCacheTtl), warm by WARM_MAX, its misses, and when it is pinged next or why not, by the rules that ping it — warm_daemon.sh's `warm WHO` (WARM_EVERY after its read, while a role forks it: shared_part_forked, used within ORCH_WARM_IDLE_MAX, never after a miss), base.sh's `--if-due` for the entry under it (only while warm), the watchdog's for a held session (PING_AGE after its read, why it is held: watchdog.held, only while the run goes), none without the daemon (its heartbeat, warm.beat) — and its last ping from warm.log or v2.log with what it read, wrote and cost; staleness measured in the background every ORCH_DASHBOARD_STALE_EVERY (60 s) as the watchdog measures it: manifest.py stale-share (the refresh rule's count: a proof changed under unchanged statements moves nothing, an index by its words), delta-share (what a delta built now holds, of the layer and of the stable base), watchdog.moved_since_delta against DELTA_MIN, carried against refresh_cost (the refresh rule under a delta), and manifest.py changed — what a fork of the layer, or of the delta (--since-layer), is told; the roles' layers and churns (their own tokens over the medium layer, the churn current or behind the delta, its forks behind and what they cost against its build: role_churn_care's rule, worth_holding); every other session held warm; the recent pings and loads; the organization as bars of tokens at one scale (each base's shared chain, the knowledge base over max, each role's own chain; cold entries hatched; what is forked now marked). Read on the live state: high forks its delta (608K), its layer 36.7% moved since 22:17 by the refresh count, a delta built now 198K against the standing 2K (189K moved: the list names 33 files the layer did not load); xhigh 29.6% moved, no delta; max 2.6%. **Costs** (/api/costs?hours=): the sessions' tokens by kind and hour from their transcripts (each summary now keeps them: read, write, uncached input, output, requests, and run-report's "base read again", by the hour, UTC), weighed as the harness weighs them (0.1, 2, 1, 5), for 6 h to all of the run beside the span before: tiles (all it cost with the pings and loads, the sessions, requests, per request, the share read from cache, the prefix read again, the pings and their misses, the loads that found their base cold), cost over time as stacked bars on whole hours, where it went by kind, the input tokens split (prefix read again, read otherwise, written, uncached), by role with the span before, the costliest sessions and tasks, the forks whose first request wrote 50K or more, the pings and loads. Read on the live state, the last 24 h: 201.5M in all (sessions 180.8M, 47% below the 24 h before; pings 16.9M in 116, 12 missed; loads 3.0M), 98.4% of input read from cache, 86% of what was read a fork's prefix read again. /api/bases 39 ms, /api/costs 63 ms. Tests (the bases: parts, own tokens, expiry, the next ping by each rule, a missed entry, the daemon gone, a held session and its ping's cost; the costs: kinds, the prefix read again, the weights, a cold fork, a ping in its hour's bar); nine mutation cases caught. README's console section names both. notes/console-screenshots.sh takes both views. The console's tests pass on the live code (10); the whole suite passed on the live code (781). Backup: state/dev-patches/predeploy-124250j. Nothing committed.
- 12:46 deployed, from the owner's screenshots of the two views: the organization's bars were narrow, centred and cut (their class, `bar`, is the page header's, with its padding, gaps and centring): their own class now; each base is one panel the page's width, its parts on the left and its staleness on the right (three cards fell into two uneven columns at 1440 px); a list of more than twelve files a fork is told of is behind its count; the cost tiles fit one row. Every view read through the stand-in DOM. Backup: state/dev-patches/predeploy-124603k. Nothing committed.
- 13:00 deployed, the owner's word "add the controls to build layers also why are the role layers missing? I want some view of what it currently should be not what it is factually": (1) why missing: the role-layers switch went on at 10:05 with the run stopped since 22:37; role_layer_care builds a role's layer in the dispatch, only while the run goes and the role has work — none was built. (2) **What it should be** (dashboard.should, in /api/bases): the steps the harness's own rules call for now, in the order each stands on the one before — a medium layer refreshed (asked by hand; a fork or ping missed; under a delta, carried ≥ refresh_cost; else the stale share ≥ LAYER_STALE; a delta due over a layer whose own entry is cold; the entry the roles fork cold, so the first fork would write its whole prefix), its stable base loaded again first when manifest.py stable-listed says the list names another reference (base.sh layer does so itself; a restable step of its own only where no refresh is due) or its entry is cold, the delta over it going with it; a delta built (moved ≥ DELTA_MIN, no refresh due); a role's layer (role_layer_due, after its medium layer's refresh; the dispatch waits for the role to have work); its churn once a delta stands — each with why, who does it and when (the watchdog, the dispatch, once the run goes), about what it costs, and a button; and what each role should fork against what it forks. On the live state: refresh high, max and xhigh (high's and xhigh's stable bases loaded again: the list's stable part names about 70 files where they loaded 270, the founding tier chosen by use), then the six role layers over them; churns and deltas as the bases move after. The organization draws each switched-on role's chain as it should be, a part not built dashed. (3) **Builds from the console** (control `build`): a base's layer refreshed, its delta built, its stable base loaded again — base.sh in the background as the watchdog starts it (watchdog.base_run), refused over a build going (WHO-layer.building) and a delta over a layer whose own entry is cold, the daemon's absence said; a role's layer (role_layer_build, carried through the evidence's reading by the console, at most ROLE_LAYER_BUILD_MAX) and its churn (v2.role_churn_care(role, force=True): the owner's hand, built though nothing is owed yet or the role has no work, never one holding the delta standing), both refused while the run is stopped — nothing would seal or keep warm what is built, gone cold within the hour. Buttons on each step, each base and each role. ORCH_DASHBOARD_BUILD names what the tests run in place of base.sh. Tests (the plan's steps and order, the refusals, the builds asked; the churn's force in test_v2); seven mutation cases caught. README's console section says both. The whole suite passed on the live code (783). Backup: state/dev-patches/predeploy-130058l. Nothing committed.
- 13:16 deployed, the owner's word "I want a projected view of how they are organized for both the current layout and the layout that would be built if building from scratch right now" and "base layers also drift but we expect less but that needs to also be available": (1) select_base_load.py: the frontier's and the founding tier's choices are functions that return them (frontier_choice, founding_choice; tier_of reads a tier) — frontier() and founding() write what they return, as before — and projection(who) is what a base built from scratch now would hold, in the tokens its loads take (estimate, the lean session included): the list's stable part with the founding tier chosen again, a layer with the frontier chosen again (× LAYER_FACTOR), nothing written. Read on the live state: high 156K + 387K = 542K from scratch against 602K built (its stable part 71 files against 270 loaded); xhigh 151K + 329K = 480K against 543K; max 351K + 130K against 494K. (2) manifest.py stable_share (and `stable-share`): the stable reference's drift counted as the layer's (moved_tokens), and the tokens it holds of files the list no longer names — max 3.4% moved, xhigh 4.4% and 150K unlisted, high 1.5% and 145K unlisted. (3) The console: How they are organized draws each base twice at one scale — as built now, each part's drift marked in it (moved since it loaded, hatched; held and no longer listed, darkened) — and as a build from scratch would hold it now (the difference beside it), with the knowledge base over max and each switched-on role's chain (its layer as last built, or at least its message: its protocol with its evidence as they stand, 8.6K to 18K; its reasoning on top); the projection in the background every ORCH_DASHBOARD_PROJECT_EVERY (600 s, about 5 s a base), the stable drift with the other measures every minute; each base's card says the stable base's drift, what it holds unlisted and what a delta holds of it against STABLE_DELTA_MAX. Tests (the projection equals the list after both choices are written, nothing written meanwhile; the stable drift: nothing moved, a file moved whole, a file held unlisted); five mutation cases caught. README's console section says both. The whole suite passed on the live code (785). Backup: state/dev-patches/predeploy-131555m. Nothing committed.
- 13:45 deployed, the owner's word on the bases (~13:30): "what do you think the target of the bases are? it is not just to give what will be used to change it is also to allign the content produced with the goals and intent of the repository. Thus it is a two fold problem - reduce reading … and reduce writing and mistakes and improve the content by having the information necessary to steer the correct changes"; then "It does not mean however that we need to keep the bases and layers as they were before it just means that we need to improve them and optimize with the twofold objective." D2 of notes/plan-bases-upgrade.md (the founding tier by use) is struck through with the owner's word; the founding tiers of high and xhigh are put back as the stable bases hold them (226 founding theories as signatures, the block of ac0f64c1; the lists' stable parts and the built stable bases agree again: `manifest.py stable-listed` exit 0, nothing held unlisted), and their frontiers chosen again within the room that leaves (select_base_load --frontier, what a layer refresh runs: xhigh 36 theories ~87K, high 43 ~145K; the lists within the target again) — a holding state until the selection is optimized for both purposes (notes/plan-bases-two-purposes.md). select_base_load.projection takes the stable part as written (the owner's), the frontier chosen again; the console says so. A fault of 13:32 found and mended: the rewrite of projection() had removed select_base_load.py's main() and entry point (every function's test passed), so `select_base_load.py --frontier` — which base.sh runs at every layer refresh — did nothing from 13:32 until 13:40; the run was stopped and the daemon down, so no refresh ran; main() restored as committed, and test_select now runs the command as base.sh runs it (a mutation case removing the entry point caught). The whole suite passed on the live code (786). Backups: state/dev-patches/predeploy-133241n (its restored/ the lists between). Nothing committed.
- 14:20 added (standalone, nothing uses it yet): base_plan.py — what each base should hold, at what depth, in which layers, and where each role's layer stands, computed for both purposes (notes/plan-bases-two-purposes.md, with the owner's words of 13:55–14:10: the layer count from the domain and data, observed signals biased by what was run, depth per item, the hot material under or over each role's layer by what it is worth, budgets deliberated not fixed, the whole plan weighed and not only the part the run worked on). `base_plan.py data` (15 s) gathers into state/analysis/base-plan-data.json: tokens at each depth for 1,837 theories (index line, signatures, definitions, statements), the reference graph, the work ahead per role (92 open role-tasks), the rates per role over 27 active hours, the steering evidence (repair tasks weighted by cost, rejecting reviews), use per role, churn of 715 theories at three depths (each commit's held text before and after, cached), and the plan's 30 parts (each section of native_control_plan.md and each condition of problems.txt, with the theories it names). `base_plan.py plan` computes each theory's depth for each base by value over cost (reads spared, rework prevented, against 0.1 a token a request and its churn; no budget imposed), the layers by a cut of the churn-ordered items minimizing refresh, carry and ping cost (the count from the data: 2 least at these weights, 3 within 1%), each role's placement, and the plan's coverage. First result: max 281K, xhigh 721K, high 313K; the size is decided by the rework a held notion spares (3K → 151–435K, 11K → 267–802K, 30K → 634K–1.5M), which the run can measure only by its repairs — the owner's deliberation, and the next analysis. No test yet (it builds and changes nothing). Nothing committed.
- 14:40 the owner (~14:30): "cost is not really that much of a concern and using this numeric based approach is not very smart - the constants are pretty much meaningless … the methodology you use is completely backwards - first you need to reason, understand and prove your reasoning and then a number is just an operational way to execute the idea". base_plan.py's `plan` is withdrawn (it answers "withdrawn"; `data` stays, a source of facts). Checking one premise against the evidence corrected me: the "32 repair tasks, 10.8%" were counted from subjects I had not read — the largest (#74, #76, #117) re-cite uses written before the index notion existed (Carrier_Indexes added 09-21 23:55), the factoring the workflow prescribes, not content made without what a base could have held; struck through in the plan. notes/plan-bases-two-purposes.md now carries the reasoning — premises P1–P5 and how each is known, consequences C1–C7 (what is held, what is read, depth by a notion's relation to the role's work, layers by kinds of change, a role's layer above what its reasoning is about, numbers only as the operational form), and the checks that could prove each wrong — for the owner's criticism before anything is computed from it. Nothing committed.
- 15:05 written, the owner's word ("write all of our discussion into a file with my comments verbatim … make sure that all of this is available and the plan and tasks for the next steps to finish this fully is written and then give me a prompt to direct another agent"): notes/bases-discussion.md — the owner's words on the bases and their layers from 2026-09-22 (the delta) to now, verbatim, each with what it answered and what came of it; notes/plan-bases-two-purposes.md gains "State, and the tasks to finish": the principles the owner set, what stands deployed, and ten tasks (the checks of C1 and C5, selection by relation, the reasoning block over each stable base, further reasoning blocks, the reviewer's layer over the changes, purposes in the lists, the console, coherence, the owner's build order). protocols/base-reasoning.md (the reasoning block's message) is in place, unused. Nothing committed.

- 17:03 bases redesign installed: reference → shared reference reasoning → direction → catalogue → working material, with named boundaries, explicit reading/steering purposes and role reasoning placed against its actual subject. Selection follows role responsibilities and source relations; no use ranking, weighted values or 530K ceiling. Exact frozen inputs, direct parents and session-specific warmth govern reuse. Failed reasoning is explicit; required material and unknown room cannot be silently admitted. Review/design/task-design reasoning stands above current changes; other production roles receive changes above their methodological reasoning. Actual fork context gates task sizes. The console uses the same parts and selection. Generated priming prompts are excluded from owner directions. Checks of actual inherited loads corrected C1's missing-context guarantee; integration history corrected C5's absolute rate/causality claim. Reasons, all ten task results and owner build order are in notes/plan-bases-two-purposes.md. Fixed-copy validation: 804 tests, all 929 mutations caught, twelve real material packs reconstructed exactly; no live model or cache experiment. The live-code suite also passed all 804 tests; installed sources were unchanged during validation. Evidence: state/analysis/bases-redesign-20260923; backup: state/dev-patches/predeploy-bases-20260923-170301. First planner's harness-change event updated under v2.state(). Run stays stopped; no bases built, commits or pushes.
- 17:59 the review of the bases redesign, and its corrections (the owner: "The owner's hold on commits and pushes remains - this is only true for the orchestrator development sessions it has nothing to do with the runs. Do all the fixes"). A base holds nothing that depends on the queue: the working part — the union of every current task's relations, which grew with the queue (280K for 5 tasks, 620K for 20; what two or more tasks share still 480K for 20) — is gone; a task's own relations (suppliers at statements on high, definitions on xhigh; subjects and consumers at signatures; less what its base holds) are written as its tree holds them to .build/tasks/ID/relations-WHO/ and named in each session's first message for its first batch, with the other current work on the same theories (v2.relations_read, select_base_load.task_relations, concurrent_work), and counted against its room at the brief's form check and at its first start. The whole-plan tier and the tools' contracts stand in the catalogue. A chain is rebuilt at once only for a change of its structure (the list's parts or their entries against the chain; the reference reasoning absent); the delta and the watchdog's cost rule carry the rest, a chain's rebuild priced from its lowest changed part (base_stack.rebuild_cost). A build works on a candidate list and installs it with the chain it describes. The room check never hands back a fix or a begun task; a role layer's thinking counts in its forks' room. A judging role's reasoning stands on the delta warm or cold. A failed reference reasoning is retried once automatically, then left to the owner; whether its thinking reaches its forks is measured and said. Dead use readers and --founding removed; the redesign's code in the harness's style; bases-design's second §18 is 18b. The first planner's note and its queued event (under v2.state()) no longer tell the run the owner's hold applies to it, and again say accepted work lands. Projected: max 591K, xhigh 549K, high 431K. Copy: 819 tests, all 950 mutation cases caught; live: 819 passed. Evidence: state/analysis/bases-review-20260923; backup: state/dev-patches/predeploy-review-175932. Run stopped; no bases built; nothing committed (the hold binds this development).
- 18:47 the window and what each base holds (the owner: "Change the bases to opus 5.5 turn off auto-compact, raise the ceiling and leave 30k margin for wrap up and add a health tracker that catches if this ever becomes a problem"; "memory is included in the bases, but clearly raw memory includes orchestrator session information which should never be shown to any of the content producing bases"). `base-model` (Claude Opus 5.5) for every base; auto-compact off in every settings file; ceiling 977K, notice 30K below, end mark 10K below; `window_watch.py` (compactions, refused requests, a step past the margin, sessions past the notice), read each minute by the watchdog and shown by health.py. No list names the memory; auto-memory off; a run session is refused the memory and the orchestrator's notes (work_meter.PRIVATE); eleven memory entries whose subject is the library held as its working practice (library-practice.txt); the owner-word collector leaves background sessions out. Copy: 835 tests, 987 mutation cases caught; live 835 passed. Backup: state/dev-patches/predeploy-window-content-184750. Evidence: state/analysis/bases-content-20260923 (suite-w1, mutations-w, suite-c1, mutations-c, live-suite-c).
- 19:30 every channel into a run session, every piece once (the owner: "Ok generalize this and try to find other similar problems with the bases content"; "Ok now generalize even further and review the rest of the content find what is incorrect, what is redundant and what can be cut and what is misplaced …"). Claude Code's git status and commit guidance off (includeGitInstructions, CLAUDE_CODE_DISABLE_GIT_INSTRUCTIONS); its summarization and closing-report guidance named in the base prompt as not holding; each base's opening audited by window_watch; the fresh charge the harness's; a role layer's evidence from the base model's sessions only; the designer's protocol corrected; per-base catalogues without what the base holds (`theory-map-index-WHO`, `tool-index-WHO`); the plan's map for high only; decisions as `##` entries, first sentence whole; the practice per base; `protocols/_owner.md` removed, the owner's paragraph the base prompt's alone; a layer's forks given their values, not the protocol again; a brief's facts not restated where the session holds their theory at statements; AGENTS.md held by no base. The first planner's note and queued event (under v2.state()) name 25 theories without a THEORY_MAP row and DECISIONS.md's checkpoint entry. Copy: 851 tests; 1,011 mutation cases, 1,004 caught at first, the 2 missed and 4 stale anchors repaired and their 36 cases caught. Live: 851 passed. Backup: state/dev-patches/predeploy-content-review-193011. Evidence: state/analysis/bases-content-20260923.
- 19:44 the solo entry (the owner: "Is the rest of development_workflow.md content still needed? Is it not in protocols, briefs or other parts that are in the layers already and deploy after you build always"). No base holds DEVELOPMENT_WORKFLOW.md: each paragraph is held in every base by the owner's words, problems.txt (which names the document the defect itself), the protocols or the pinned closed-workflow theories; the one statement it alone makes (Isabelle establishes the account's adequacy) is the owner's open question Q3. The base prompt says AGENTS.md and it are not a run session's to read; `_finishing.md` no longer points to it; neither the base prompt nor the reference reasoning names "the operating rules". Copy: 851 tests, 1,017 mutation cases caught. Backup: state/dev-patches/predeploy-solo-entry-194355. Evidence: state/analysis/bases-content-20260923 (suite-d1, mutations-d, live-suite-d). Run stopped; no bases built; nothing committed.
- 19:56 every source the same way (the owner: "Ok now generalize this method and search for other redundant information and files … having too little information is bad but having noise and contradictions and multiple sources is just as bad"). The base prompt quotes the owner's words of 2026-09-19 on the performance channel and parking verbatim (recorded in notes/orchestration-v2-plan.md, session 212840df; it had paraphrased them under the owner's name) and no longer says what the protocols say (the tools and `v2.py change`, a check's end, the machine's 60 GiB, the finalizer and parking twice); the planner's protocol no longer repeats the base prompt's ledger sentence, nor the designer's `_finishing.md`'s recording rule. The stale copies `state/held/` kept from 09-18/20 (ADMISSION.md, OBLIGATIONS.md, REASONING_REUSE.md, owner-directions.md, founding-index.md, an orchestrator note, the definitions/signatures/statements folders), named by no list and read by no code or run session, moved into the backup. The repository's historical documents (GENERALIZATION_REVIEW.md, ADMISSION.md, proposal.txt, OBLIGATIONS.md, plan.md, the plan's citation of DEVELOPMENT_WORKFLOW.md), read by none of the 320 run sessions of 09-21/23, are in the first planner's note and its queued event (under v2.state()). Copy: 850 tests and the console's timing test, which failed once under load and passed three times alone; 1,020 mutation cases caught. Live: see live-suite-s. Backup: state/dev-patches/predeploy-sources-195623. Evidence: state/analysis/bases-content-20260923 (suite-s1, suite-s2, mutations-s, live-suite-s). Run stopped; no bases built; nothing committed.
- 20:06 every layer checked for what it holds twice (the owner: "Ok continue on checking every base layers for redundancy"; "Do more work between full suite tests and deployments"). Every entry of each base rendered as held and measured: no source held at two depths, no catalogue line for a held theory or tool, no verbatim repetition between the direction documents and the catalogue (the plan's quotations of the owner's words are its citations and stay). The knowledge base read the ledger's two Codex questions of 09-19 twice: `extract_owner_directions.py --new` now leaves out what the ledger records (`ledger_quotes`, compared as words however wrapped); the live file regenerated, none left. The console's timing test given a 30 s deadline for the console to re-execute (it had failed twice under a loaded suite with 10 s). Copy: 852 tests; 1,022 mutation cases caught, and the 3 of the changed test and collector again on the final copy. Backup: state/dev-patches/predeploy-ledger-once-200641. Evidence: state/analysis/bases-content-20260923 (suite-t1, suite-t2, mutations-t, mutations-t2, live-suite-t). Run stopped; no bases built; nothing committed.
- 20:57 the order of the parts and each part's own schedule (the owner: "REASONING_REUSE.md is in direction, but does it not change often? is the layer ordering based on churn?"; "Idealy we would want to make the dependency and churn based orders coincide …"; "Also some things like decisions and probably reuse too are append based …"; "And same is true for reuse no? Have you not found other append structures? … where do they go?"; "The rule needs to be revised - the layers must be ordered by churn and dependency and so update cschedules also should differ."; "And then sometimes consolidation for the lower parts rather than carrying their changes in a higher layer."). Measured over the run's 472 commits by each source's own units (audit/churn.py, kinds.py, appends.py): the parts ordered by dependencies, which is also the order of modifications per token held — the stable part the owner's words, problems.txt and the practice, then the reference; direction the plan (high: its map) and the decisions index (append-only as held), on high the tool index; inventory (max, xhigh) the tool index (append-built), the plan's notions, REASONING_REUSE.md (revised with nearly every addition); catalogue the theory map and the tools held whole. Each part on its own schedule: the delta counted by part (manifest.delta_parts, in its record), each fork's shares (v2.delta_shares), each part's account since its own load (watchdog.carried_parts), a refresh from the lowest part whose account with those over it has paid for loading them again (watchdog.refresh_plan, base_stack.suffix_costs replacing rebuild_cost, base.sh WHO layer --from PART, build_chain keeping the parts under it); the stable part's account said to the owner when paid (its reload the owner's), in place of the fixed 15K line. The delta names "the stable part" and "the parts over it" (no working frontier). The console shows the plan. The first planner's note carries the owner's words on REASONING_REUSE.md. Copy: 856 tests; 1,032 mutation cases, 1,026 caught at first, the missed one and five anchors moved by this round's edits repaired and their 28 cases caught. Live: 856 passed. Backup: state/dev-patches/predeploy-order-schedule-205652. Evidence: state/analysis/bases-content-20260923 (suite-order, mutations-order, suite-schedule, mutations-schedule, mutations-schedule-reanchored, live-suite-schedule, audit/). Projected: max 555K (stable 363K, direction 35K, inventory 88K, catalogue 69K), xhigh 513K, high 399K. Run stopped; no bases built; nothing committed.
- 21:56 the delta as a chain, the stable part by the rule, and the review of the refresh logic (the owner: "delta is rebuilt once at least 4k tokens - … should the delta not be layered … the 4k number needs to somehow depend on the size of the delta. should the stable part's reload also follow the rule automatically once its account has paid - yes and retire them yourself."; "Do not carry it into native_control_plan.md it is the current plan with a current scope."; "do one more review of the logic for refreshing the layers its adequacy and coherence before we deploy it"). The delta is a chain of messages each written once: `base.sh WHO delta --increment` forks the chain's top with what changed since its messages took each file in (manifest.increment_text, the texts it gives in state/WHO-delta-held.json, orphaned with its layer); a message is built once what the pending changes have cost the forks started since reaches what it costs (watchdog.pending_paid, forks record pending_tokens), the chain written anew once its superseded forms have (stack_waste, superseded_tokens), measured every 5 minutes (DELTA_EVERY 300; DELTA_MIN and moved_since_delta gone); a churn takes the chain's later messages by forking itself (`over`, stack_base, stack_len). The stable part is reloaded by the rule (`--from stable`, base_stack.reference force). Review corrections: the sweep keeps every message of a chain; a message's cost counts the judging roles' layers it makes due; the console's follower reads its sources before serving (its test's intermittent failures). ADMISSION.md and proposal.txt deleted from the working tree by the owner's word (uncommitted); plan.md, OBLIGATIONS.md and GENERALIZATION_REVIEW.md stay; native_control_plan.md untouched. Copy: 864 tests, 1,056 mutation cases caught; live 864 passed. Backup: state/dev-patches/predeploy-delta-chain-215618. Evidence: state/analysis/bases-content-20260923 (chain-*, live-suite-chain). Run stopped; no bases built; nothing committed.
- 22:46 the judging roles' churn and the arithmetic review's fixes (the owner, 22:10: "the answer to the last question it posed is yes" — the judging roles take the chain's increments as a churn over their layer, reasoned again only when the chain is written anew or the parts are refreshed). `v2.layer_stands` (a judging layer stands while the chain it forked stands; it records `digest`, `stack_base`, `stack_len`, `delta_size`), `role_churn_care` grows a churn from what holds the chain's beginning (the churn, or a judging layer before it has one) by the churn's rule, a fork of a judging layer behind the top counted in `behind_forks`; A: `pending_paid` charges a fork 2 a pending token (its write, not its carrying), `STALE_READ` 2; C: a part's account is its old forms carried (`manifest.old_forms`, recorded in each message, inherited by forks, churns and layers) and its changes written again at each whole rewrite (`state/WHO-delta-builds.jsonl`, a churn's `whole_parts`); D: `refresh_plan` takes the part where the accounts from it up most exceed its cost, the stable part among them; found on the way: every fork descending from a chain records what is pending (`top_rider` walks the origins — with every role layered, high's messages would never have paid), every message of a standing chain and every standing layer's origin keeps its snapshot (`tidied`), the churn's digest guard removed (it kept a role on its bare layer once its churn was let go). max switched to deltas (`state/deltas`: max xhigh high, the owner's word of 21:50). Copy suite 869, mutation check 1078 caught; live suite 869 (state/analysis/sim-20260923/). Backup: state/dev-patches/predeploy-judging-churn-224614. Not committed (the hold).
- 23:17 three machinery faults found by the simulation of the run of 09-21/22 (the owner: "build a simulation from the existing data and execute the current machinery on it fully end to end"; notes/plan-bases-two-purposes.md, last entry): the generated indexes the parts hold made again for each commit of main (`watchdog.held_indexes`, before layers and deltas — made only by builds, every rule was blind to them and forks were not told they changed); a judging layer over the parts stands under the chain's first message (`layer_stands` counts `delta.layer`; a fork of a judging layer is behind whenever its digest is not the top's); an entry's age is its latest read under any mark naming it (`base_stack.warm`, `watchdog.layer_entry_age` reads the chain's top part; base.sh's OK ping marks `entry-hits/SID`) — warm entries had been judged cold and the high chain with its stable base loaded again. Copy suite 874, mutation check 1088 caught. Backup: state/dev-patches/predeploy-sim-fixes-231658. Not committed (the hold).
- 23:51 every churn by its rule, and a part pinged only while worth keeping (the simulation of 09-21/22, notes/sim/FINDINGS.md): an executing role's first churn waits for its forks' cost like every other (forks of a bare layer count behind; the investigator's had been built twice for no fork); `base_stack.worth_keeping` (entry-used/SID marks a real read; a ping is none) stops a part's pings once they cost more than making it again, the top part always, the stable reference weighed against the whole chain — the day from 531.5M to 519.0M, upkeep 41.5M to 30.4M. Copy suite 877, mutation check caught all (the last cases re-pointed after). Backup: state/dev-patches/predeploy-churn-rule-pings-235126. Not committed (the hold).
- 00:13 (09-24) a session standing on a base is a use of it (the simulation of 09-21/22: max, which planners reach through the knowledge base alone, went cold at 10:00 with a planner every hour, its chain and the knowledge base built again at 15:52): `v2.launch` marks `WHO-base.used` for every session whose origin descends from the base (top_rider), which the daemon's idle rule reads (warm_daemon.sh). Simulated day 519.0M to 518.4M, upkeep 30.4M to 29.7M (the max stable reference and its parts no longer loaded again: stable loads 10 to 8 requests, part loads 28 to 22). Copy suite 878, mutation check caught all; live 878. Backup: state/dev-patches/predeploy-idle-use-001253. Evidence: state/analysis/sim-20260923 (full-idle.report.txt, suite-idle-use.log, mutations-idle-use.log, live-suite-idle-use.log). Not committed (the hold).
- ~00:28 (09-24) the console for diagnosing and controlling, round 1 of the owner's word "functional and have high utility and be easy to navigate and understand … control, monitor, diagnose, review": (1) a hazard removed: `v2.py queue` sets the order whole, and the task page's "Queue" button sent one id — it would have left that task alone in the queue (45 others out); the console's `queue` now needs `whole` and refuses a partial list, and one task is moved by `place` (first/up/down/last/out: the whole order set again with it moved); the task page says its place and moves it, the Control view shows the queue with ↑ ↓ first out, and "set the whole order" is pre-filled and says what would leave. (2) Where a session's time went, from its transcript's own times (`timings`): each request's model time (from what it answered being ready to its last block), its calls' time (to their last result), idle before a message (parked, mail); the session page's tiles and a clickable timeline, each request's model/calls time and context added; the list's "Ran" split as a bar; each live session's current call (running for how long) on Now. (3) What holds tasks up: Now's pipeline shows what moves, and "Held up" groups every waiting task by the tasks at the heads of its chains of waits (most held first); "holds N" on the graph, the pipeline cards and the task list; a task page's "waited on by". (4) A task's history: its lines of v2.log (made, tree, sessions, checks, parks, probes, train, landing) with the time to the next line marked. (5) Navigation: a jump box (/ — a number opens the task, a name the session, with the sessions listed), keys 1–0 for the tabs, tasks and sessions linked wherever the log names them; the header's time of the last event; pause, and no refresh while text is selected; "Console unreachable" when a read fails; attention for a session silent 20 min and a task parked 45 min while the run goes. Costs' "per request" read NaN% with no request in the span (fixed). New check: notes/console-views-check.py renders every view with the page's own script over the real server's answers (the test transport, a stand-in DOM) and says what shows NaN/undefined/null or fails — 14 views clean. Console tests 16 (3 new), mutation cases 5 new, all caught. Backup: state/dev-patches/predeploy-console-20260924-0019. Not committed (the hold).
- ~00:39 (09-24) the queue drops only when told (the owner: "do you think dropping the queue should happen explicitly not by accident allow chaning the queue without a flag and force a flag to allow dropping update all the relevant places like the protocol/layers that need to know about this change"): `v2.py queue ID...` puts the named tasks first, in that order, and every other queued task after them as it stood — nothing leaves the queue by being left out; `--drop-unnamed` makes the queue the named tasks alone, each queued task left out said back ("taken out of the queue, not named … still in the list") and logged as the planner's; `v2.py edit`'s queue operation the same (`"dropUnnamed": true`, anything else beside it refused); a finished task (done, deleted) leaves the queue whenever an order is given; the tasks briefed since the episode began keep their place after their brief either way; a typo'd id refuses the order ("nothing was queued"). Said where it is read: planner.md (the edit's operations; the Order paragraph — each planner is given it at launch, no base or knowledge base holds it, and no role layer's protocol names the queue's rule), README, v2.py's usage and refusals. The console: its queue action passes `drop_unnamed` only from the Control view's explicit checkbox (the confirmation says which tasks leave or stay after); "out" is the one place move that drops. And the console's "What it should be" (Bases & layers) is removed with the server's `should()` it alone read (the owner: "remove the what it should be part"); the role-build buttons read `going`. Round 2 from the screenshots: the queue table one line a row, a message over 800 characters closed until opened, a landed task offers no queue moves, the timeline's "calls' time" said as the wait after the model's last block (calls run while it writes: implement-44's 98% model time is real — 4 min thinking before a 300 s probe that was refused at once). Tests: v2 2 new, console 1 changed; mutation cases 7 new (3 removed with `should`), all caught. Not committed (the hold).
- ~00:52 (09-24) the console's charts made true to their data (the owner: "A lot of the charts look crooked and also are not correct representations of data"), by the dataviz skill's method, its palette validated (validate_palette.js against the panels #ffffff/#171b21): the categorical slots in their fixed order for the six kinds of cost and for what stands on a chain (delta, role layer, churn over it — violet: aqua beside magenta failed deutan 1.6 —, knowledge base, reference reasoning); the shared chain's material parts an ordinal blue ramp, bottom darkest (before: inventory, working, medium layer one blue; catalogue and knowledge base one amber; direction and stable one grey; reasoning and role one purple); no hatching, no clipped label (a label is placed only where it fits, the rest in a tooltip), the unmeasured reference reasoning no sliver but "+ reasoning, unmeasured" beside the total, warmth said in the row, drift a status strip under its part. Costs: ticks on 1/2/2.5/5 steps with the precision they need (an empty span drew "1, 1, 1, 0, 0"), columns ≤ 24 px with rounded data ends and 2 px of surface between parts, one tooltip listing every kind; a span with nothing in it shifts to the run's last activity and says so (the 24 h after a day's stop was empty); tiles say "—" and "nothing in this span" where there is nothing (they read 0% in green and ▼100% in green), and only a direction that means better or worse is coloured. A session's time on a real time scale with a clock axis (idle had been drawn shortened with no scale), "active time only" on request with each cut marked; the list's time bars on the scale of the longest in the table, no track (idle had matched the track and read as an unfilled meter). The occupancy chart with its axes. One tooltip layer for every mark. Console tests 15 (the costs' shift new), the views check clean. Not committed (the hold).
- 00:50 (09-24) the delta as texts, sessions made on demand, and the knowledge base lazy (the owner, ~00:10: "write the text on every change, as now, but build the session only when something is about to start from it"; ~00:15: "In general everything should be done lazy when its better"; ~00:20: "the knowledge base is rebuilt on every max session make this lzay too"). Plan and as-built: notes/plan-text-deltas.md. A text node is cut (`base_stack.cut`, `base.sh WHO delta --text`: no session, its snapshot `layer-<text id>-manifest.json`) when something takes the chain in; a session of the chain is made (`base_stack.materialize`, `base.sh WHO delta`; over the chain's session when that holds its first texts and is warm, else over the layer) only once the forks of the base itself (`v2.top_rider`, now direct: the base or its medium layer, never a layer role, a churn or the knowledge base) have paid for it (`watchdog.pending_paid`); the chain is begun anew as one whole text, a cut, when its superseded forms have cost its holders what taking it anew costs (`stack_waste`). The judging roles' layers and the knowledge base hold the texts in their own first message (`v2.chain_carried`, `{CHANGES}`); the knowledge base takes later texts in by integration (with the planners' notes, or alone by the churn's rule over `kb_lacking`) and is built again only when max's parts are refreshed (`v2.kb_stands`), grown, cold or lost. `v2.stands_on` keeps the idle rule's use marks. Deployed by a three-way merge onto live (another session's queue and console round had changed v2.py, README.md, dashboard.py, test_v2.py, notes/mutation-check.py meanwhile; re-staged once when dashboard.py moved again). Copy suite 885 (+ the location-dependent layer-list test), mutation check 1,117 caught (the first run's five misses repaired: stale tests, a redundant sweep line); staged suite 888; live 889 passed. Not simulated (the owner: the simulation only when asked). Backup: state/dev-patches/predeploy-text-deltas-005041. Evidence: state/analysis/text-deltas-20260924. No role layer is due from it (no role protocol changed). Not committed (the hold). Next round: v2.py:4242's comment "its churn at once" is stale since the churn rule of 23:51.
- ~00:55 (09-24) from the owner's screenshots of the charts' round: the base cards' styles (.stale, .sh, .told, .basebody) had gone with the chain's old rules and are back; a chain's total is its bound and its change on now, one line each, why a bound in its tooltip; a session's time in the lists as its shares (a whole bar: one scale over 16 s to hours left most bars a few pixels; its length is Ran's); "nothing since" says the last request's time, not the hour after. Console tests and the views check clean. Not committed (the hold).
- ~01:07 (09-24) the bases' layers built from the console, one or every one (the owner: "add to controls the ability to to a layers build individually and all together"): Control's "Bases and layers" (/api/builds) shows each base as it stands — a chain of named parts or the stable base and one medium layer (the layout before the parts, which its next build makes a chain) —, when it sealed, its entry, what a build from scratch holds, a build going over it, and warm.log's lines about builds; "Build its layer" is `base.sh WHO layer`, "Build every layer" (also on Bases & layers) runs max, xhigh, high one after another in one process that outlives the console (`state/layers-build.json`): one after another because the builds regenerate the indexes they share in place (select_base_load --refresh-index: theory-names, plan-index, decisions-index), and one beside another could pack one half written; refused while any build over a layer goes or while it goes itself; a single base's build is refused while it waits its turn. Also: the costs' shift also when the last active hour ends where the span begins (the test found it at five past the hour). Console tests 15, mutation cases 2 new (all 5 of building_it_from_the_console caught), the views check clean. Not committed (the hold).
- 01:17 (09-24) nothing a session holds is given it again (the owner, ~01:05: "the goal is to not duplicate information and use changes when possible not just in this case but in general - find other such mistakes and fix them all"; before it: "why not just the changes … wasn't everything supposed to be delivered in changes and use the delta layers?"; and "Why is the planner protocol not held below knowledge base layer"). The audit, measured on the run's recorded first messages: bases clean (no file at two depths, no index beside its source); fixed: (1) a changed protocol went whole to every fork and made every layer including the part due (~1.2M for one shared-part edit) — now kept by digest (`state/role-protocols/<sha>.md`), each session records the copy it holds, forks get values and the changed paragraphs (`protocol_changes`, `protocol_block`), the churn takes them, the layer is reasoned again by rent-or-buy (`protocol_paid`); (2) continuations got their protocol whole again — the session they fork holds it; (3) the planner's (~8.6K tokens an episode) and consultant's protocols whole — the knowledge base holds them (`kb_protocols`, `protocol_shas`) and takes their changes with the notes; (4) the graph whole in each episode and brief (14K/12K chars) — held by the knowledge base (updated with each episode's notes) and the task designer's layer, `graph_for` gives the changes; (5) HANDOFF.md's Now and Open whole — changes since the knowledge base read it (`handoff_parts`); (6) stale files read again whole — `v2.py read changes[:NAME]` gives the changed units since what the session holds (`manifest.held_changes`, `layer-<text id>-held.json`; `_inherited.md` says so); (7) a task coming back got its changed brief whole — its changed lines (`keep_text`, `line_changes`); (8) a continuation's brief facts stated again — its source's `stated_theories` are held. Also: two churn early returns made redundant by the final guard removed; the stale "its churn at once" comment corrected. Copy suite 898, mutation check 1,146 + 40 targeted caught (one equivalent mutant retired, with its reason); staged 898; live 899 passed. Backup: state/dev-patches/predeploy-no-duplication-011714. Evidence: state/analysis/no-duplication-20260924. Merged three-way onto live (the other session's console round). Existing layers stay (their protocols unchanged); the current knowledge base, built before, gives planners their protocol whole until its next build. Not committed (the hold); not simulated.
- 01:21 (09-24) the console as one text (the owner: "build a script that will output an aggregate log of everything that is displayed in the console so that once I start a run you can use it to monitor the run, diagnose problems, verify that everything is going smoothly, find bottlenecks, find issues with batching, errors with delivery, problems with economics"): `console_report.py [--since 3h|last|all] [--only …] [--quick] [--rows N]` reads through the console's own functions and prints findings, run (with v2's status), sessions, pipeline (held up), machine, checks, batching (by role), delivery (grouped by what came back), costs, bases, log; `--since last` for passes (its mark in $TMPDIR). To share one implementation, what only the page computed moved to the server: the attention list (`dashboard.attention`, in /api/overview), what holds tasks up (`held_up`, in /api/graph: each node's `holds`, the `held_up` groups), the log's noise (`LOG_NOISE`) and the ceiling (v2.CEILING; the page had 972K). Calls that did not deliver told apart at the parser: refused, stopped by the guard (an error that is no exit code nor the tool's own failure: 96% of the "failed" of 09-19/23), failed; the console shows a Stopped column, tile and mark. Over the last run the report found: 2 sessions lost, 4 forks that wrote their prefix anew (~1.1M each), 12 of 44 pings cold, planners' requests 30–60% joinable, checks of 223, 227, 267 failing repeatedly, a request 36% dearer than the span before. Console tests 16 (2 new: the three kinds and the report's every section), mutation cases 3 new, all caught; views clean. Not committed (the hold).
- 01:32 (09-24) the first planner's material brought up to date (the owner: "Is the first planner prompt up to date with everything?"): the queued harness-change event (and its source, notes/fresh-start-2026-09-23.md) still said the knowledge base is built again over each new message of max's (true before the text deltas of 00:50) and named neither the text deltas' lazy sessions, nor the no-duplication round of 01:17, nor the queue's new rule — each said now; FRESH_CHARGE tells the first planner its first order says the queue is its tasks alone (the queue it inherits is the last run's 49 entries: otherwise every task left out stays queued after its order). Then, on the owner's word ("The commands are given in the protocols not in the initial prompt"), the event, its note and the charge say what changed and never how to invoke it: every command they named (queue --drop-unnamed, dropUnnamed, read changes, finalize, === row, follow-up, "continues", measuring --exclusive/--shared, --probe/--no-probe, room_of, git -C, drop, queue) is said as what it does — each stands in the protocols (planner.md, _production.md, _inherited.md, _checks.md, _tree.md), which the knowledge base holds. The rest of the event stands as the state does (the run has not moved since 22:37): tasks in flight 44, 278, 192, 279, 276, trees 143 and 176, the switches, the window. The planner's protocol reaches it through the knowledge base --fresh builds (kb_protocols), current. v2 tests of start, planner, event and queue pass (75). Not committed (the hold).
- 01:49 (09-24) the monitor: console_report.py rebuilt as the run's data aggregator (the owner: "fix everything so that it can serve its purpose it should be a complete data agregator from an active run with functions tailored to extracting particular information such that it can be used to monitor a live run"; "Not just session summaries everything produced should be accesible so that you can evaluate every facet of the run"). Its review's faults fixed: checks counted once (the session's verdict line and the per-task verdicts are no runs), a lost session says what is known (a start never confirmed, a transcript gone, or its reason — watchdog.lost now records `lost_why`), parked and held sessions stand (never "ended"), the costs' line in an empty window, the `--since last` marker moved only by a `changes` pass. Added: findings grouped by pattern across sessions, each with the command that opens its evidence (`delivery ID`, `session NAME --from N --full`, `task ID --history`); `changes` — conditions new, standing or resolved, the interval's own events, tasks moved, sessions started or ended, entries warmed or cooled, the interval's checks, landings and cost; `waits` — the tasks' time by stage and by what they waited for, throughput, time counted to the run's stop; `errors` (a traceback said by its exception, API errors); economics (pings against use, outlier tasks, tasks gone round, idle shares); `inventory` and drill-downs into every product (session calls whole, task folders and files, checks, questions, mail, planning episodes, knowledge bases, the delta's texts, layers, the graph, raw records, any file, any log). test_console_report.py (9); 15 mutation cases; one test strengthened after the check missed it. Copy suite 908, mutation check 1,171 + 1 caught (the one missed: the dashboard's case of the other session's, its anchor gone); staged 908; live 909. Backup: state/dev-patches/predeploy-monitor-014906. Evidence: state/analysis/monitor-20260924.
