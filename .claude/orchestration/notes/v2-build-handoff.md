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
