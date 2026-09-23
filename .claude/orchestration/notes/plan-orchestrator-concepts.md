# The orchestrator, improved at the level of its concepts: the work of 2026-09-23 onwards

The owner's order (verbatim in `notes/owner-order-2026-09-23.md` and in memory): no commits, work locally; improve the
orchestrator from the real data — the content of each session, scheduling, what took most time, what limited speed,
what held up the tasks, how content was used, what could better prepare the sessions; the existing framework is the
baseline, to be improved conceptually, not only in its details; autonomously, without stopping, until the owner says
stop. After a compaction: re-read the order, this file, and continue from the first open task.

Working rules (until the owner's word of 09:25, which had it committed): nothing committed or pushed; every change built in `$TMPDIR/dev/orch`, tested (tests, mutation cases,
`notes/run-tests.py`), then deployed to the live files with a backup in `state/dev-patches/predeploy-*` and recorded in
`notes/v2-build-handoff.md`; the run is stopped (state/stopped 2026-09-22 22:37:06) and stays so; data under
`state/analysis/` (ignored by git). A conceptual change the owner must decide (it changes a policy they set) is
written here as a proposal with its data, and implemented behind a switch that leaves the current behaviour as it is.

## State (kept current; read this first)

**The owner's word of 09-23 morning** (C7, C10, C15 yes; the per-role reasoning layer to be built behind a switch; the last session of each role read): its tasks and plan are notes/plan-owner-word-2026-09-23.md.

**For the owner, on waking.** Committed and pushed on the owner's word at 09:25 (6a4b17be, the checker's `--keep-heap`; b798ff0b, the harness's work of the night and the morning). Six switches, each a file whose presence turns it on — all six on now: five by the owner's word of about 10:00
(continue-by-fork, measure-bound at 180 s, support-apart, grouped-repairs, role-layers for every role) and
review-beside-check by the owner's second word (after the same reviewer was made to get what changed since, 10:31);
the batches in notes/v2-build-handoff.md at 10:05 and 10:31, the second word's plan in
notes/plan-owner-word-2026-09-23-b.md —
(`touch .claude/orchestration/state/NAME`, remove it to turn it off; the health screen names those on):
- `review-beside-check` (C9): a task's review starts at its result, beside its check — a median 8.2 of the 18.4 minutes
  from result to commit; an accept waits for the check and is void if it fails;
- `continue-by-fork` (C13): a follow-up the planner marks `"continues": "N"` forks the session that did task N instead
  of the base — a fifth of such a fixer's cost and a session that knows the work;
- `measure-bound` (C14): a session's measurement holds the machine ten minutes at most (four holds took 1.1 hours);
- `support-apart` (C6): the review in a slot of its own beside two producers (the machine's caveat: it binds at 1.2–1.6
  of 2 when checks run) — worth most together with C9;
- `grouped-repairs` (C8): small repairs of the same theories briefed as one task;
- `role-layers` (the owner's word of 09-23): each named role's sessions fork a reasoning layer made for the role — a
  fork of its base that reasoned once over the role's protocol and what the run showed of it (its last 12 sessions'
  measures, notes and refusals; the findings of the reviews that rejected its work) and wrote at most 12 practices
  with their evidence. The file's words name the roles (`implementer fixer`, or empty for every role that forks a
  base). Its cost, estimated: a layer adds about 10–15K tokens to each fork's prefix (read at 0.1 in each of a
  session's ~20 requests: ~25K a session), about 30K to build, and a keep-warm ping of its whole prefix (~60K) each
  PING_AGE while its role is wanted; one rejection it prevents saves a fix round (~1.7M). run-report sets each role's
  sessions with and without it side by side (requests, before the first change, rejections, cost).
Built on the owner's yes of 09-23 and deployed (no switch): C7 (the reviewer corrects a commit message, a result or a
row itself and accepts; it writes nothing else of the repository), C10 (a landing reuses its check batch's build when
the content is the same), C15 (`v2.py follow-up TASK:ITEM…` drafts a follow-up's brief, copied, the judged parts marked
for the planner). The repository is ready for the build, the
seal and `start.sh --fresh`: the first planner's event (notes/fresh-start-2026-09-23.md) says what tonight's changes
mean for planning; no base loads a protocol, so none needs rebuilding for them. After the start,
`python3 -B notes/run-report.py --since <the start>` reads the run against the baseline below.

**Deployed, locally** (each with its tests, its mutation cases and the whole suite on the live code; a backup under
state/dev-patches/predeploy-*, an entry in notes/v2-build-handoff.md from 01:01):
- the close (C1): index files by key (`=== row`, `=== root`), the structural checks and the import graph told with
  every change that writes a theory, the result given as the command's text and recorded by the hand-over, and in a
  task's own tree `v2.py finalize ID` alone — its files, the repository's check, its commit.md;
- a task's inputs (C2): the facts and definitions a brief names stated in the first message of implementers, fixers,
  designers, investigators, task designers and reviewers; the reviewer's first read (result, log, probes, restated, tree, diff);
- rework prevented (C4): what a change adds that the library has (a specific name, a statement, a definition's body),
  a row offering what was taken out, decision entries citing a removed name — told to the writer, read by the
  reviewer; the commit's own record of the session's probes; probes found wherever they ran; the result's
  `## Acceptance` self-check (taught);
- the planner's view: a task's passing state rendered and never written into HANDOFF.md (C12); the landings of the
  last three hours; how many tasks wait behind each that could start; how the last hour used the slots; what
  HANDOFF.md says beyond its knowledge base's copy;
- records and instruments: each measurement's hold in the task's measurements.log; slow hooks and commands saying where
  their time went (finding 15); a fork of a session told what changed since that session's load; every information
  part failing soft; a test that wrote into the live log repaired;
- analysis tools (not part of the harness): notes/timeline.py, notes/lifecycle.py, notes/run-report.py; their datasets under state/analysis (7.8M). The backups of every deployment are under state/dev-patches (with the earlier sessions', 150 of them, 72M): what rolls a change back, to be pruned once the work is accepted.

**Decided against, on the data**: C3 (a proof loop in a smaller context), C11 (dependents started on their blockers'
accepted work), a role-level primer (C2), whole deliverable theories in the first message, statements matched up to
variable names, definitions matched by type, code bodies matched (each in its finding or concept below).

**Checked**: the full mutation check run eight times, the last over 838 cases (09-23 09:10, after C7, C10, C15 and the role layer): 833 caught at once, two anchors rebased (the small-read note's and the note to batch, changed by the per-session pass) and three cases added, all caught; the suite 756 on the live code; walk tests carrying a tree task, a review-before-commit, a fresh start and a continuation from start to landing; the restatement hints and the brief statements replayed over the landed history (C2, C4g).

## The direction since the harness was built here, and where each thread goes next

Read from the 139 commits of .claude/orchestration (09-19 → 09-23), the owner ledger, notes/orchestration-v2-plan.md,
fable-knowledge-base-orchestrator.md, plan-landing-train.md, plan-delta-layer.md, the work list of 09-21 and
problems.txt. Each thread: what moved it, where it stands, what tonight added, what is next on it.

- **Knowledge by the cache, not by reading.** 09-18: sealed bases, forks read them from cache (v1's implementers
  spent 200–280K re-acquiring context each rotation). 09-20: layered bases, a layer refreshed when it has moved.
  09-22: the delta layer (a refresh at 720–810K against a delta build at 70–100K). 09-23: each base holds what its
  roles use. Tonight: what a task names delivered in its first message (C2), the planner told what HANDOFF.md says
  beyond its base's copy. Next: the work's own knowledge — a follow-up forked from the session that did the work it continues (C13, behind the owner's switch); a role-level primer costs about four times what it saves (C2).
- **One self-contained piece of work per session.** 09-20: v2 — a planner above one session per task, the roles,
  consultation by fork, warmth. Tonight: holding pays (finding 14); a task's fixed cost against its size (C8, the
  owner's switch).
- **The harness takes over the mechanics.** 09-20: the finalizer, a tree per task, index files merged by union.
  09-22: check batches, landing trains, the base following main. Tonight: the close as one transaction and the index
  files by key (C1), the commit's own probe record (C4c), a task's passing state rendered instead of written (C12).
  Next: the reviewer's corrected words (C7) and one heavy check a task (C10), both the owner's.
- **Batching made structural, not asked for.** 09-19: the gather; 09-21: every command batchable, one change command;
  09-22: batches and trains. Tonight: the one-call close. Next: small repairs on the same theories as one task (C8).
- **Never idle, never waiting in a slot.** 09-19: parks, the efficiency channel. Tonight: the workers were idle
  more than half the afternoon while the open work waited on blockers past their result (finding 11) — C6 and C9
  built behind the owner's switches; C11 decided against (the safe variant saves five minutes a link, the fast ones build on work rejected 42%
  of the time).
- **Rework prevented where it starts.** 09-21/22: reviews with one complete verdict, one fix round. Tonight: what the
  library already has told when it is written, rows and decisions at odds, the acceptance self-check (C4). Next:
  blockers are rejected more (finding 12), so what prevents a rejection shortens every chain behind it.
- **Measured before decided; guards fail closed; repairs proved by breaking them.** From 09-21 the mutation check.
  Tonight: timeline, lifecycle and run-report over the whole history; 740 mutation cases.
- **The planner at the highest level.** 09-20: statements only, events, HANDOFF.md a state and not a log. Tonight:
  the waiting-behind count, the handoff delta, the passing state no longer its to write (C12).
- **Structure, not prose** (problems.txt: "the development process is prose where the system is structure"; a
  requirement holds by construction). The harness's forms are checked (briefs, results, verdicts), its edits keyed,
  its state rendered. Next on this thread: the brief's acceptance items carried by identity through result and review
  (C4f is taught, not enforced).
- **The native machinery in planning** (v2's goal 4: the planner uses the loop's machinery wherever it can carry
  planning — readiness, selection — and records the rest as residuals). Not the harness's to build: presenting the
  task graph to the loop is a task of the graph, placed where the planner's order puts it; condition 5a asks that the
  workflow be used on real development work.

## Questions, and the data that answers each

1. **Where does a task's time go?** Every task's lifecycle from the log: created, ready, started, result, check
   queued/started/ended, review queued/started/verdict, landing queued/landed; each stage split into waiting and
   working; what it waited for (a slot, the machine, a check batch, a train, the planner, a tree, an answer).
2. **What limited the rate of landings?** Slots, the machine (two heavy runs, measurement claims), the check and train
   queues, the planner's order and its graph hold; their occupancy over the day.
3. **What does a session spend its wall time on?** Model turns against tool runs (probes, checks) against waiting
   (parked); requests and their latency.
4. **What is redone?** Rejections, fix rounds, failed checks, landings that did not stand, sessions lost or restarted,
   work dropped or superseded; what each cost.
5. **How is content used?** What sessions read against what they produced; what the base holds against what they
   used (tasks 1–4 of plan-bases-upgrade); what the planner reads and writes.
6. **What could prepare a session better?** What each role must find out before it produces, and what of that the
   harness knows or could compute before the launch.

## Tasks

Status: `[ ]` open, `[~]` in progress, `[x]` done (where), `[-]` decided against (why).

1. [x] A task-lifecycle dataset from v2.log (notes/lifecycle.py, state/analysis/lifecycle.json) and its report
   (finding 5): time by stage, per task kind; dependency waits dominate the wait to start.
2. [x] Resource occupancy over the day (finding 4, C6).
3. [x] Session wall time (notes/timeline.py; finding 1): time is output; requests' fixed cost is money.
4. [x] Rework (finding 6, C4, C7); lost sessions, API failures, cold waits: small (14 API failures resumed, 7
   sessions gone cold while they waited, 2 lost over the three days) — nothing to change.
5. [x] Content use and preparation (C2; the priming layer reasoned through again).
6. [~] Concepts: C1–C13 written; the sessions' own reports of the harness read (46 follow-ups of the afternoon):
   acted on where still open (probe locations, renamed copies, the commit message's place, the sandbox's mounts);
   the direction since the harness was built here read from its 139 commits and its plans (the section above).
7. [~] Implementation: C1 (with the argument-free hand-over), C2, C4a–f, C12 deployed; C6, C8, C13 behind switches,
   off; C7, C9, C10 written as designs or questions for the owner; C3, C11 decided against; this file and the handoff
   kept current.
8. [x] Where the idle time is (finding 11) and what holds a chain (finding 12), measured over the whole history; the
   planner's status gives the last hour's occupancy; run-report gives both.
9. [~] Why a theory change waits on the machine (finding 15): instrumented; the cause is for the next run's log.
10. [x] The planner's time (finding 13) and holding warm (finding 14).

## Findings

Data: `notes/timeline.py` (state/analysis/timeline.jsonl: 315 sessions of 09-21 and 09-22 — the 09-20 transcripts
are not reachable from the state — each interval charged to the model, a tool or waiting), `notes/lifecycle.py`
(state/analysis/lifecycle.json: 237 tasks, 150 machine runs, 148 planner turns from v2.log), the sessions datasets.
The direction of the harness since it was built here (139 commits, 09-19 → 09-23): knowledge delivered by the prompt
cache instead of re-read (sealed bases, forks); one self-contained piece of work per session instead of a rotating
implementer; the harness taking over mechanics sessions did (ids, placement, checks, merges, landings, bases);
batching (reads, changes, check batches, trains); measurement before every decision; guards that fail closed. v1's
baseline (notes/efficiency-baseline.md): 35 of 40 minutes generating, 62% of thinking in mechanical proof repair,
94% of requests one tool call.

1. **Time is output.** A request takes about 3.5 s plus 8.3 s per 1K output tokens, in every role (fits over 6,000
   requests; a request with under 200 output tokens: median 3.2–4.3 s at 550–740K of context). Tools are a fifth of
   a producer's active time (implementers 8.8 h model, 1.8 h tools over the two days). The fixed cost of a request is
   money, not time: each re-reads its base, 55–75K input-equivalent.
2. **Cost, 09-22 (435M).** Implementers 30%, fixers 26%, reviewers 19%, planner 13%, designer 4.5%, task designer
   3.5%, investigator 3.5%. The base prefix is 69–77% of a producer's cost, 56% of a reviewer's, 43% of the planner's.
3. **Inside a producer.** Implementers: 26% of cost before the first change (8 requests of 33), 51% between the first
   and the last probe (18 requests), 11% writing before the first probe, 11% after the last probe. Fixers: 28.5%, 41%,
   13%, 17.5%. **Requests that only do bookkeeping** — a THEORY_MAP row, ROOT, commit.md, result.md, source checks,
   bring-main, git status, `v2.py result|finalize|park`, the todo list — are 24% of implementer and 27% of fixer cost
   (511 and 419 requests over the two days, 69M), 11–30% in other roles; the largest: THEORY_MAP rows alone 161
   requests 13M, `v2.py result|finalize|park` alone 188 requests 12M (a call that could have closed the request
   before it), commit.md 89 / 7.8M, git status 78 / 5.4M, source checks 68 / 4.5M.
4. **Concurrency.** On 09-22 (00:00–22:37) producing sessions were active (model or tool) 0.9 of the 2 producing
   slots on average, the supporting slot 0.38, the planner 0.32; the machine's runs 0.55 of its 2 (1.2–1.6 from
   15:00, when batches and trains ran). ORCH_WORKERS 2 caps producers + support: 1.3 of 2 used.
5. **A task's way (09-22, 50 landed tasks, mean 114 min from made to landed).** Waiting to start 34% (39 min: 18 on
   dependencies, 20 ready and not started, median 5, a tail to 4 hours for tasks whose blockers were "with the
   planner"), producing 30%, after the result 12%, check 10%, waiting for review 8.5%, landing 5%.
6. **Rework.** 48 of 158 producing tasks were rejected at least once (30%); the rejections' findings: a notion the
   library already states re-derived, the brief's reading missed, a commit message misstating its run, THEORY_MAP
   rows doubled by a merge. Sessions of a task after its first (fixers', implementers', reviewers' `.2`, `.3`): 54M.
7. **The planner.** 16 planner sessions from 09-21 20:08 to 09-22 22:09, each started at 527–577K (a fork of the
   knowledge base) and ended at 623–941K, three of them after 7–9 requests (one by a restart, two by their own
   choice, far from the notice at 907K). 64 landing events cost 48M of its handling (with 54 graph edits: the
   reviewers' follow-ups made into tasks), questions 28 / 18M, failures 11 / 7M. A turn: median 2.0 min, p90 4.9.

8. **The close.** The protocol asks one call for the hand-over and the result (`_finishing.md`); of the 69
   producing sessions of the two days that recorded a result, 1 did. 41 handed over, then wrote result.md, then
   recorded it — three requests — after a row read to be quoted, a row written, a ROOT line, the source checks run
   by hand and git status read. The finalize's reply ("its check runs when you record your result") comes after the
   request that could have held the result. Read by time: before 09-22 12:00, 8 of 51 closes put the hand-over and
   the record in one request; after it, 6 of 7 did (the turn-ending repairs of that morning) — but the bookkeeping
   share stayed where it was (implementers 24% before and after, fixers 26% and 28%): rows, declarations, source
   checks, git status and the commit message kept their requests. Text-only closing messages (about 25M over the two
   days) stopped at 11:00 on 09-22, when the turn's end became the harness's (`continue: false`): nothing left there.

**The baseline the next run is read against** (`notes/run-report.py --since 2026-09-22T12:00 --until
2026-09-22T23:00`, the harness as it stood from midday): 133 sessions, 171.8M; implementers 22.2 requests a session,
6.8 before the first change (34% of their cost), 4.4 that only did bookkeeping (20%); fixers 20.8, 6.0 (31%), 5.0
(27%); closes in one request 52 of 53; 25 of the 71 producing tasks the window touched rejected at least once; 60
tasks landed, 112 machine runs (9.1 h), 61 planner turns; of the 31 tasks both made and landed in the window, 78
minutes each from made to landed — waiting to start 26 (33%), producing 17 (21%), its check 16 (21%), landing 7,
after its result 7, waiting for its review 5. After a fresh start: `python3 -B notes/run-report.py --since
<the start>` gives the same figures, and what the new mechanisms did (`=== row`/`=== root` uses, results given as
text, what the change replies told, launches that stated the brief's facts).

9. **Cache entries missed.** On 09-22, 13 requests wrote their whole context (16M): 9 in the account-wide eviction
   of 21:03–21:19, and the knowledge base's integrations after 83–137 minutes (about 1M each), whose entry expired
   while its planner's own requests read only their own — the harness had counted every request of a fork as keeping
   its origin warm. Both already answered by last night's repairs (the miss marking and the rebuild it asks; `hit`
   marks only the entry a request read, and a fork's start its origin).
10. **What the sessions said of the harness.** 46 follow-ups and questions of the afternoon's results and reviews
   named the harness: most already acted on by the day's repairs (the zsh `status`, the standing step's name, the
   union rows, the harness's check in the commit); still open until tonight and now done — probes run outside the
   task's folder not found (tasks 233, 245), renamed probe copies (229), the commit message's place (211, 219), the
   sandbox's mounted dotfiles (185); left — a session database moved during a base move (173: the base's move to its
   lasting store that day, once).

11. **Idle workers, and what the open work waited on** (afternoon of 09-22, 12:00–22:37, from the sessions' own
   request times). Working sessions active (model or tool) in each minute: none 158 of 638 minutes, one 191, two
   258, three 31 — fewer than two in 349. In 246 of those 349 minutes some task not yet started waited only on
   blockers already past their result (in their check, review or landing); in 235 no task was ready at all and such a
   task waited; in 114 a task was ready (mostly 12:00–13:40: 144, 145 and 151 behind the lasting base's move). Ready tasks started a median 3.2
   minutes after their last blocker landed (22 dependents). What a dependency link costs is its blocker's way after
   its result: a median 22 minutes, a mean 51 — rejections make the tail.
12. **Blockers are rejected more.** Of the 84 build, fix, design and investigation tasks that other tasks wait on and
   that gave a result, 35 were rejected at least once (42%), against 11 of 40 that nothing waits on (28%); 11 and 4
   failed a check. Among the 58 tasks landed in the afternoon, the 35 never rejected took a median 22 minutes from
   their first result to landing (mean 32), the 23 rejected 46 (mean 78). The blocking findings of the afternoon's
   rejections (#144 on): a notion or fact duplicated (153, 221, 229, 249, 251, 269, 271 — mostly re-derivations no
   text match sees; `Merge_Sort_Keys` duplicates a proof of Isabelle's own library, outside the repository's
   theories), the commit message's Validation (181, 185, 217, 223, 225), a row or decision entry at odds with the
   work (275), the brief's acceptance missed (144, 191), code copying a function (145). Matching statements up to
   the names of their variables finds 3 more duplicate pairs in the library's 8,347 statements than word for word
   (19) — not worth a hint of its own; a definition's type, as a second key, is shared by one or two others for 13%
   of the library's 4,304 typed definitions — noise without evidence that it would have named the rejected ones.
13. **The planner's time** (09-21/22, 680 requests, 71M, 8.4 hours of model time, 3.2M output tokens — its time is
   its output). Graph edits 164 requests, 24M, 1.5M output (3.6 h: the briefs it drafts itself); HANDOFF.md 113
   requests, 12.7M, 0.5M output (1.2 h); reading 109, 12M. Of the 908 SEARCH/REPLACE blocks by which the planners
   edited HANDOFF.md (510K characters written, the old text quoted as well as the new), 405 (309K characters)
   changed words of a task's passing state — a commit, landed, parked, handing over, queued, the order.
14. **Holding sessions warm pays.** 69 finished sessions were held and pinged (158 pings, 9.4M over three days); 37
   were resumed afterwards (a quick fix, a re-review, a consultation), each resume read from cache instead of
   written cold (about 1.2M a resume at 600K of context): about 44M saved for 9.4M. Questions: 68 over three days, a
   median 86 seconds to the planner's answer, 7 of 41 answered after their asker had ended (the answer written to
   the task's folder). Nothing to change.

15. **A theory change waits on the machine.** Of 478 theory changes of 09-21/22 (`v2.py change` naming a theory), the
   median took 0.8 s with no heavy run going, 7.7 s with one and 13.1 s with two (p75 39 s) — 1.4 hours of the
   sessions' tool time — while the 1,109 other changes took about half a second whatever ran. Read in one case
   (fix-269, 17:13): its guard ended 0.2 s after the call was written, its result came 19.9 s later, and the
   command itself does nothing heavy; timed apart on the repository, every part (the change 0.49 s with tonight's
   checks, the transcript reads 0.01–0.02 s, the production measure, the probe copy) is fast. The cause shows only
   under the machine's load: **instrumented 04:00** — the hooks and a session's commands say in v2.log when they
   pass two seconds and where the time went, so the next run names it; `run-report.py` sums those lines. Its weight: change calls are 59% of implementers' tool time and 43% of fixers' (probes 23% and 36%). Read again from the transcripts of 60 sessions, a change's command and post-hook took a median 0.79 s and a p90 of 34 s, while its guard took 0.10 s; a read's guard took a median 0.64 s against 0.10–0.16 s for every other call — its wait for the call's line in the transcript, whose outcome the guard now counts (`batch_lookups`, summed by run-report) — and the per-call durations of timeline.py charge a call from its request's start, so a read's 2–3 s there was its request's.

## Concepts proposed or implemented

(Each: what the framework assumes now, what the data shows, the change, its cost and risk, its state.)

**C1. The close is one transaction; index files are edited by key** (findings 3, 8). Now: the harness supplies
text-level edits (SEARCH/REPLACE) and leaves every bookkeeping step to the model — a row quoted before it is replaced,
its imports column copied by hand, ROOT found and edited, the source checks run by hand, the result written, then
recorded. Change: (a) `v2.py change` takes `=== row THEORY` (the Content cell; the imports column is computed from
the theory as the change leaves it; a new row goes after the row of the theory before it in ROOT) and `=== root
THEORY [after OTHER]` (declared after OTHER, or after the last of its imports ROOT declares) — keyed as the merge
already keys them (finalize.ROW_KEYS); (b) a change that writes a theory, ROOT or THEORY_MAP.md is answered with
what the structural checks now say about what it wrote (a theory not declared, a declaration without its file, an
escaped proof, a theory without a row, a row whose imports are not its theory's) — the documents check's items, told
when they arise rather than at the hand-over; (c) `v2.py result ID` takes its text on stdin (written and recorded in
one command), and `v2.py finalize` records a result already written in form by the session, so the protocol's one
call is what the commands do rather than what a session must remember; a result recorded twice is said, not refused;
(d) `--files` defaults, for a task in its own tree, to what the tree has changed. Coherence: every write still goes
through `cmd_change`'s all-or-none application and the guard's reading of change paths (a keyed verb's path is
THEORY_MAP.md or ROOT at the change's base, as `=== replace` would name it); production is measured from the files;
the finalizer's documents check is unchanged and still decides; rows and declarations use the keys the merges use.
Expected: most of the 161 row requests, 68 source-check requests, 23 ROOT requests and about half of the 188
result/finalize requests of the two days — roughly 40M of 242M producer cost. State: **deployed 01:01** (tests,
15 mutation cases, the suite 712 on the live code; handoff entry). To measure on the next run: requests per producer
session that only do bookkeeping (24–27% before), and how many sessions close in one or two requests. Measured again
on the harness as it stood from 09-22 12:00 (58 producer sessions in 11 hours), the bookkeeping-only requests C1 and
its companions address: THEORY_MAP rows 113 requests (10.0M), git status/log/diff 77 (5.5M: `v2.py read tree`),
source checks and the import graph 51 (3.6M), bring-main 30 (3.4M: the finishing protocol and the first planner's note
say it is not needed), ROOT 24 (1.9M) — about 20M in those 11 hours, some 35–40M a day at that rate. (e) **Deployed 03:38**: in a task's own tree `v2.py finalize ID` is the whole hand-over — the check left out is the repository's (109 of the 126 recorded hand-overs had named it, nine named one not runnable as written), the message left out is the task's commit.md, the files what the tree changed; the reply names each.

**C2. A task's inputs delivered, not searched** (finding 3: 26–28% of producer cost before the first change). Measured:
55% of the files producers read before their first change are files the brief names; 38–39% of their orientation
reading requests read nothing else; briefs name 15–30 facts each, exactly (133 briefs: 580 theory or fact mentions,
74 decision entries by heading, 209 result or review files). Whole files delivered would cost about what the reads
they replace cost; the named facts' statements are small (2–10K bytes) and are what a consuming task must see —
7 of 31 rejections were a named contract proved again. **Deployed 01:28**: the statements in the first message
(`inputs_read`). The owner's priming layer, reasoned through again with this data (D9 of plan-bases-upgrade): what a
session must learn before producing is task-specific — the named facts, the theories it edits, the entries its brief
cites — so its preparation is this, per task, and not a role-level layer; a role's text is 3–5K tokens and the same
for every fork. (Correction, 01:31: I first wrote that thinking done ahead is not kept in a fork's context; the API
documentation says the opposite for Opus 4.5 and later — previous-turn thinking blocks are preserved — so a primer's
thinking would stand in every fork's prefix. That makes it carried, not free: 5–20K tokens of role-level
interpretation read at 0.1 by each of about 5,000 requests a day is 2.5–10M a day, for orientation that is
task-specific; the conclusion stands on that, not on the reason first given.) The other form a role layer could take —
the role's protocol sealed into a fork of the delta that every task of the role forks, so that the protocol is read
from cache instead of written by each fork — computed on 09-22's numbers: about 260 forks a day would each write about
4K tokens less (2.1M a day), and every delta build would rebuild each role's layer over it (the delta's prefix read and
the protocol written: about 63K a role), high about 30 builds a day for its two roles and xhigh about 22 for its four
(3.8M + 5.5M a day): four times what it saves. To measure on the next run: requests before
the first change (8 implementers, 7 fixers before), and rejections for a contract proved again. Extended (01:41,
01:54): the task designer's and designer's first messages (the task designer read statements with show.py in 90% of
its sessions before its first change), and the reviewer's (what the work is to consume); _brief.md asks the named
facts exactly. Not delivered, measured: the decision entries briefs quote by heading (193 quoted, 185 found) run a
median 20K characters (the upper quarter 29K) — whole, they would cost more than the reads of the parts sessions take;
the task files briefs name (46% read before the first change, a median 3.3K) about even. Nor the theories a brief's Deliverable names (measured 03:39 over the baseline window): 96 of the 125 that existed were read before the first change (a median 29K bytes, in a median of two requests each), but among other reads — 3 of the 364 requests before a first change read nothing else — so delivering them would move tokens, not save requests. Replayed over the last 43 build, fix and design briefs against HEAD (04:36): the statements section runs a median 1.2K characters (the upper quarter 4.3K, the largest 13.3K), and the names briefs give resolve.

**C3. The proof loop in a context sized to it** (finding 3: 41–51% between first and last probe) — decided against,
on the data. Of 1,129 probe and check runs of 128 producer sessions, 275 failed (234 of them with one error) and 824
came back clean: the phase is the building itself, a change probed after each step, not a loop of repair a smaller
context could take over (v1's "62% of thinking in mechanical proof repair" is not today's shape). What it spends in
requests that could have been joined is small: 64 theory changes over the two days were followed by a request that
only probed (about 4M) — not worth a probe run after every change, which 331 changes without a probe would each have
paid in output read and machine time.

**C4. Rework prevented upstream** (finding 6). The 31 rejections whose findings the state holds: 14 a notion or fact
the library had, re-derived or restated (exactly restated or under the same name: `path_term_inj`,
`syntax_branch_eq_iff`, `map_filter_member`; the rest re-derivations a text match cannot see); about 12 a document
misstating the work (the commit message's Validation paragraph five times, a THEORY_MAP row offering what the task
removed three times, a DECISIONS entry at odds with the work); about 7 a reading of the brief missed. Rework about
2M a rejected task (a fix session, a re-review, the planner's handling) and about an hour. (a) **Deployed 01:08, 01:20**:
the change that writes a theory is told what it adds that the library has — a specific name, a statement word for
word, a definition's body — and what its row offers that it took out (`restated`). Why it matters beyond the
rejections: 23 of the 51 planned fix tasks from #100 on consolidate what was stated twice ("state X once, every copy
re-cited"), each a whole pipeline (task, session, check, review, landing) spent after the fact. (b) Open, the owner's: a finding about the commit message, the result or the task's row alone costs
a whole fix round today; the reviewer, who has found the right words, could write them (accept with the correction
made) — a change to "the reviewer judges, never produces". (c) **Deployed 01:15**: the commit states the
harness's record of the session's probes beside its check (harness_validation, probed_whole); the session's
Validation paragraph holds only what no record holds (a measurement, an argument). (d) **Deployed 01:34, 01:49,
01:52**: the reviewer reads the restatement findings over the whole change (`v2.py read restated`, in its first read);
a probe is found wherever it ran (the guard records each probe's --work: two reviews could not read back the marker a
result claimed); the import graph is told with every change that writes a theory (the planner's standing last step).
From the sessions' own reports: the sandbox's mounted dotfiles are no one's change (changed_paths), which the default
--files of C1 would otherwise have committed. (e) **Deployed 02:28**: a change that takes a specific name out of a
theory is told which DECISIONS.md entries cite it (decisions_citing) — the entry-at-odds-with-the-work rejections. Tried on the trees the stopped run left (02:59, read only): task 276's
new `reach_step_rule` has `native_member_later`'s body word for word, arguments aside — a duplicate its review would
have had to find — and `state_presents_root_inside` stands in another theory too; tasks 44 and 176 each leave a row
offering a name their change took out, and 44 a decision entry citing it; one name only coincides (`predecessor_at`,
another lemma in RRA_Fresh_Generation_Frames), which the hint asks about rather than asserts. (f) **Deployed 02:50**: the result
form asks, taught and not enforced, for `## Acceptance` — each clause of the brief's Acceptance and Decided and where
the work meets it — the self-check against the seven rejections for a reading of the brief missed; the reviewer's
protocol names it as the session's reading.
(g) **Checked against history, 04:28**: replayed over the 68 landed changes of 09-21/22 that touched theories, each against its own library as it landed, the hints would have named 7 duplicates that review let through (tasks 110, 182, 208, 179, 40, 76, 34; fix tasks consolidated some of them later, each a whole pipeline) — and 15 row mentions of names the change took out, nearly all of them false: a citation of the name at its new home, a note of its removal, one an `abbreviation (input)` the declared-name pattern did not read. Made precise at once: a name another theory declares has moved, a mention in a clause noting its removal offers nothing, and the pattern reads the abbreviation's modes; replayed again, the row hints fell to one, the abbreviation's, since read.

**C5. The planner's load** (finding 7). Measured and left as it is: a planner's life of about 14 turns is near the
optimum of rollover against context (a rollover about 1M — the knowledge base's integration, the fork, the reading
of HANDOFF.md — against each turn's ~4.3 requests at a context that grows ~25K a turn: the optimum
sqrt(2R/(0.1·k·g)) ≈ 13.6 turns); its requests: reading 10M, HANDOFF.md 7M, graph edits 6M, briefs of fix tasks it
drafts itself 13M of 62M over the two days — the briefs are the planner's own judgement of what a follow-up needs,
and moving them to a task designer would put a brief task on the supporting slot the reviews share. Two planners
ended by their own choice at 671K and 723K (about 1M each): too few to act on. The text-only closing messages that
cost 25M over the two days stopped at 11:00 on 09-22 (the harness ends the turn).

**C6. Throughput** (findings 4, 5) — a proposal to the owner, whose settings these are. On 09-22 the two workers
(ORCH_WORKERS: producers and the supporting session together) were both busy 47% of the minutes (a producer and a
reviewer, or two producers), one or none 35% with nothing else running in 205 minutes of them; the machine's two heavy
runs were used 0.55 on average (1.2–1.6 from 15:00). A task waited 8.5% of its way for its review and 34% to start,
most of the latter on dependencies (a blocker's own way, ~2 hours a link). Two levers: (a) the supporting session outside
the worker cap (two producers and a review at once): the cost per task unchanged, the spend per hour up by what the
third session works, reviews no longer waiting for a producer to end — **built behind state/support-apart, off**;
(b) for the dependency waits, a graph drawn wider — the planner's; its status now says beside each task that could
start how many wait behind it (waiting_behind), for an order that puts what releases most first. The caveat, measured:
from 15:00 on 09-22, when batches and trains carried the checks, the machine's two heavy runs were busy 1.2–1.6 of 2
(two heavy checks a task: its batch, 220–350 s, and its train, 250–500 s, both rebuilding what a change near the root
reaches); a third worker adds checks at the same rate, so the machine becomes the constraint where it was not — (a)
is worth what the machine has left, about a quarter more landings an hour on that afternoon's mix, not a third.

**C8. A task's size against its fixed cost** — a proposal to the owner (the planner's and task designer's sizing).
Producer sessions end at 600–700K of a 907K window: a task uses about a third of its room. What every task pays
whatever its size — a fork's launch, the orientation (6–8 requests, 31–34% of producer cost in the afternoon of 09-22),
the close, a review (0.67M), a landing — is paid again for each small task. With a session's cost 0.1·(n·B + g·n²/2)
(B ≈ 550K the prefix, g ≈ 2.8K the growth a request, measured) and 8 requests of orientation, 25 of work: one task
2.72M; two related tasks in one session 2.33M each (−14%), three 2.24M (−18%) — the growth of the context eats the
rest. Against it: a larger rejection's reach, less parallelism, a longer way to land. The measured case for it is the
consolidations: 23 of 51 planned fixes from #100 on were "state X once, every copy re-cited", often several on one
line of theories in a row. The rule, **built behind state/grouped-repairs, off** (the
planner's and task designer's protocols, {GROUPING}): small repairs on the same theories go into one task up to about
half its room; a repair another task waits on, or a notion's contract, stays a task of its own. Measured beside it: briefs' Size runs about twice what a session grows (147
sessions: a median 130K estimated against 68K of context grown; the growth a quarter to four fifths of the estimate
in the middle half), so the room a brief is checked against has never been what bounds a task — its writer's habit is. Of the 20
consolidation fixes from #100 on, 15 share a deliverable theory with another (28 pairs: Native_Collection_Programs,
Development_Verdict_Unreached and Development_Located_Rows among them) — each pair two landings rebuilding the same
dependents, where the reviews asked for one ("batch the next change here … so the rebuild is paid once", tasks 234,
245, 251).

**C9. The review beside the check** — built behind the owner's switch, off (`touch .claude/orchestration/state/review-beside-check`; the order of the finalization is theirs). A task's
way after its result is sequential: the check (11.4 min a task on 09-22, queue and run), then the review (9.7 min
waiting for the supporting slot, then about 5 working), then the commit and the train (5.8). Started at the result,
beside the check, the review would take the check's minutes off every task's way — 5–11 minutes of the 114, and more
where the machine queues; what it risks is a review of work that then fails its check (20 of 146 checks failed on 09-22,
about 14%: 0.09M a task in expectation at 0.67M a review) and a verdict held until the check passes (an accept is not
a commit before the check). Measured on the 12 build and fix tasks of the afternoon with every event in the log: from
result to commit a median 18.4 minutes; started at the result with its own length, the review would have ended a
median 8.2 minutes sooner (mean 13.2) — about 45% of that stretch, the review slot taken as free (C6 makes it so).
Built at 04:56 behind the switch, as designed below: with it off, nothing changes. `run-report.py` measures it: from a task's result to its commit, a median 21.3 minutes over the baseline window's 60 tasks. Why the owner's: it changes when a reviewer may start and what an accept means before a check, the owner's order of the finalization.
The design, as built: (1) a hand-over puts the task in its check as
now and makes its review pending at once — `pending_reviews` takes a task in `checking` as well as in `reviewing`;
(2) the review judges the work as handed over, its tree's state recorded with the verdict (the hash of the handed
files); (3) the commit waits for both, whichever ends last: a passed check and an accept of the same state; (4) a check
that fails while the review runs: the quick fix is told the failure and, when the review has ended, its findings, in
one round — the re-review judges the fix alone, as after a rejection; (5) a review that rejects while the check runs:
the fix waits for the check's end and takes both; (6) an accept of a state the fix then changed stands for what the fix
left alone, and the re-review judges the rest, as now. What it saves: a median 8.2 of the 18.4 minutes from result to
commit (the afternoon's 12 tasks with every event logged), and a round when a task both fails its check and is
rejected. What it costs: a review of work that fails its check (14% of checks, 0.09M a task in expectation), and a
supporting slot taken earlier — so it is worth most with C6 (the review's own slot).

**C10. Two heavy checks a task** — a question for the owner, measured. On the afternoon's harness a task's check took
as long as its producing (16 minutes against 17, of 78 from made to landed). From 12:00 on 09-22 the machine ran 62 batch
checks (5.5 h, 1.63 tasks a run, 12 failed) and 46 train checks (3.3 h, 1.24 tasks a run, 3 failed) for 60 landings:
each task is proved twice against the same active base — once with main as its session asks or hands over, once
with main as it lands — and with main moving about five times an hour the second is rarely the first's tree: of 70
tasks whose batch passed and whose train came after (a median 13 minutes later, the review between), main had moved
for 62. The
batch is what finds the failures (19% of its runs against the train's 7%) while the session is warm; the train is
what lands. Ways to one check a task, none built: the train reusing the batch's own build where main has not changed
what the task's theories import or its recipes read (the incremental checker's part, the repository's tool); or the
batch left out for a task whose every changed theory a clean probe loaded as the tree holds it (probed_whole), which
leaves the recipes and host tests to the train. Either takes up to three fifths off what the machine spends (the batches were 5.5 of its 8.8 hours) where it binds (C6's caveat). What the
batches found, read from six of the afternoon's failed logs: a proof failing in a dependent or with main's work (two),
a recipe's words changed (one), host tests (one), two not said in the log's head — so a clean probe of the changed
theories alone would have caught none of them; (b) would move those to the train, after the review.

**C7. A finding about words costs a round** (finding 6) — a proposal to the owner. About 12 of the 31 rejections were
a commit message, a result or a row misstating the work; each cost a fix session, a re-review and an hour for words
the reviewer had already found. The review could accept with the correction made: the reviewer writes the corrected
commit.md, result or row (documents only, never a theory or code), says so in its verdict, and the finalizer commits
it — against "the reviewer judges, never produces", which is the owner's. C4c removes the commonest case (runs
misstated) without it. The design, if the owner wants it: (1) the write guard lets a reviewer write, in the reviewed
task's tree, that task's commit message and result (.build/tasks/ID/commit.md, result.md) and, by `=== row`, the rows
of the theories the task changed — nothing else; (2) its verdict says `Verdict: accept` with a `## Corrected` section
naming each file and why, which the harness checks against what the reviewer wrote (tree-owners); (3) the finalizer
commits as now (the message file is read at commit time; THEORY_MAP.md is among the files a task that writes rows
hands over); (4) a finding about a theory, code or a decision stays a rejection. Expected: about 12 rejections in 31
become accepts with a correction, each a fix session (about 1.2M), a re-review (about 0.5M) and an hour saved.

**C11. A dependent started on its blockers' accepted work** — decided against, on the data. Finding 11 shows the
workers idle while the open work waited on blockers in their check, review or landing; started earlier, a dependent
would fill that time. Measured at three points of its blockers' way (the afternoon's 22 dependents): at their result,
a median 25 minutes sooner and 246 idle minutes filled; at their passed check, 17 minutes and 162; at their review's
accept (committed, waiting to land), 11 minutes and 66 — of which the landing itself is a median 5.4 minutes (58
tasks from commit to landing). The first two build on work that is then rejected 42% of the time (finding 12), and
about half the rejections change what a dependent would consume (a duplicated notion taken out, a brief's reading
corrected); the third is safe but small, and needs a tree made from main with the blockers' branches merged and a
landing that never lets a dependent's branch carry a blocker's commits into main ahead of it — a new rule on the
landing's hardest path for about five minutes a link. The time is better sought in the blockers' rejections (C4, C7)
and the way after a result (C9, C10).

**C12. A task's passing state is rendered, never written** (finding 13; "the development process is prose where the
system is structure", problems.txt). The planners kept, in HANDOFF.md's prose, a mirror of what the harness records —
which task is parked and for what, handing over, landed and as which commit, the order — stale between edits and paid
for in them (405 of 908 edit blocks). **Deployed 03:28**: the graph every planner is shown gives each open task's
stage with a parked task's reason and since when and a rejected task's rounds (stage_text); the status names the
landings of the last three hours with their commits (landed_lately); the planner's protocol says HANDOFF.md names a
task and what it is for, never where it stands. To measure on the next run: HANDOFF.md edit blocks per planner turn
and the share touching those words — `run-report.py` counts the blocks whose old and new text differ in them: 146 of 381 in the baseline window (09-22 12:00–23:00).

**C13. A continuation forks the work it continues** — built behind the owner's switch, off (`touch
.claude/orchestration/state/continue-by-fork`). The thread "knowledge by the cache, not by reading" applied to the
work itself: what a follow-up needs to know is what the session that did the work holds, already cached. Measured
(09-21/22): of the 52 fix tasks with a fixer session, 27 named in their brief the task whose review they came from; that
task's producer was still warm at the fix's start for 18 (a median 38 minutes after its last request) and had ended
at a median 638K; fixers spent 31% of their cost before their first change and grew a median 45K. A fork of the
producer starts about 90K larger than one of the base (about 9K more a request) and skips the orientation (six
requests, 0.4–0.6M): about a fifth of such a fixer's cost, and a session that knows the work it repairs. The design:
the planner marks a continuation in the task's metadata (`"continues": "N"` — its own judgement, as it drafts those
briefs itself); the harness forks N's last producing session when it is warm, not working, at the effort and model of
the role's base (a fork carries its origin's), and within 700K, and the role's base otherwise; the first message says
whose work the fork holds and that that task, its brief, its tree and its session's rules are over; the watchdog holds
the producer until the continuation starts. Why the owner's: it changes what a session is forked from, a line the
owner drew (every piece of work a fork of a base or the knowledge base; a resume only for the same piece of work) —
a fork of a producer is still a fork, but a new task starting inside another's context is a new kind of start.
Risks: a fork that takes the finished task's brief for its own (the first message says otherwise; measured on the
first runs); a producer held longer (one ping, about 65K, an hour).

**C14. A measurement holds the machine only as long as a timing needs** — built behind the owner's switch, off (`touch
.claude/orchestration/state/measure-bound`). The owner's rule (09-20): a run whose result is a timing takes the whole
machine, since a neighbour distorts the number. Measured over 09-20/22: 37 holds took 3.0 hours (a median 3.2
minutes), and the machine emptied for them 1.5 hours more (21 waits, a median 3.8 minutes, no new run starting); four
holds passed ten minutes and took 1.1 hours between them — the longest one background probe of 31 minutes (fix-278,
22:04–22:34 on 09-22) that loaded its theories and then timed one judgment, with every check of the run waiting behind
it on an afternoon when the machine was the constraint (C6's caveat). The timing needs the hold; the loading before it
does not. Under the switch a session's hold lapses after ORCH_MEASURE_MAX (ten minutes): its session is told that what
it times after that is no held number and to time the one judgment its measurement is for with its theories loaded
first, and the task's measurements.log says so; a check advancing the base keeps its hold. Why the owner's: it bounds a
rule they set. The finer form, not built: a measurement that loads under no hold and claims the machine only for its
timed part (the probe tool's, a phase it does not have yet).

**C15. A follow-up's brief begun by the harness** — a question for the owner, not built. The planner's time is its
output (finding 13): its graph edits took 1.5M output tokens and 3.6 hours of its model time over 09-21/22, most of it
the briefs of the fixes it drafts itself from reviews' follow-ups, each in the full form (Kind, Serves, Deliverable,
Acceptance, Inputs, Decided, Plan, Size). Much of such a brief is mechanical: its kind, what it serves (the review and
its follow-up by number), its inputs (the review file, the theories the follow-up names), its acceptance (the
repository's check). A command could write that part from the review — `v2.py follow-up N ITEM...`, a draft brief the
planner completes with what only it decides (why now, the plan, what is decided) — halving what it writes for each.
Against it: the brief is the planner's judgement, and seven of the 31 rejections were a brief's reading missed; a
skeleton may invite a thinner brief. With C13 on, a continuation's brief may already cite the findings by place.
