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
