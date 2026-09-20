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
