# The knowledge base, its planner, and one session per piece of work

`native_control_plan.md` is carried out by sessions that each do one self-contained piece of work (the design and
its reasons: `notes/orchestration-v2-plan.md`). Every piece of work is a fork: of a sealed base, of the knowledge base,
or of a sealed session that is consulted. A resume only continues the same piece of work. A session whose cache has
expired is never woken or forked. No model supervises: a daemon runs the watchdog and the dispatch once a minute,
keeps the bases warm, and the watchdog keeps warm what may still be consulted. The owner speaks to the planner
(`talk.sh`) or to any session directly. Until 2026-09-19 a single rotating implementer did everything (v1); why it
was replaced is measured in `notes/efficiency-baseline.md`.

## Use

    .claude/orchestration/base.sh WHO build     # WHO is max, xhigh or high: freeze its load list into a verified pack and load it
    .claude/orchestration/base.sh WHO status    # until the load has ended its turn (the measured context)
    .claude/orchestration/base.sh WHO seal      # check every chunk arrived, snapshot the frozen sources, stop it, record it
    .claude/orchestration/start.sh              # make the orchestration active (the knowledge base first), follow the planner here
    .claude/orchestration/start.sh --fresh      # the same, on a knowledge base built anew, the first planner charged to take stock
    .claude/orchestration/talk.sh               # speak to the planner, which lives across its events
    .claude/orchestration/attach.sh [ROLE]      # open and follow a role: planner, producer, support, fix, consultant, kb
    .claude/orchestration/stop.sh               # stop everything: daemon, every session, the runs they left behind
    .claude/orchestration/stop.sh --keep-warm   # the same, but the daemon stays to keep the bases warm (its watchdog is inert)
    .claude/orchestration/health.py             # one screen; lines that need someone start with ATTENTION
    .claude/orchestration/v2.py status          # the slots and the queue; `v2.py graph` the task graph
    .claude/orchestration/efficiency.py         # how each session spent its window and what it produced, by role

`start.sh` refuses without a sealed base. `stop.sh` makes the orchestration inactive; what it interrupted is an event
for the planner, and `start.sh` resumes with the sealed knowledge base. A wake writes
`state/<name>.woken` before it stops a session, so that `attach.sh` tells a wake from leaving the view on purpose.
What you type to any orchestrated session is recorded verbatim and dated in `owner-ledger.md` by its
UserPromptSubmit hook, and (but in the planner itself) becomes an event that reaches the planner at once; what is
yours to decide the planner decides provisionally and puts there as an open question with its basis (`v2.py ledger`,
numbered under "Open questions to the owner": no session writes the ledger by hand), and the work continues (see
"The owner's directions").

## The sandbox

Claude Code's sandbox (`sandbox` in `.claude/settings.local.json`, which every session reads, in a task's tree too)
runs each Bash command of every session, and of the owner's own session, where it may write only its working
directory, `/tmp`, `state/`, `.build/outputs`, `.build/tasks` and the task list, and cannot start, stop or remove a
session (`~/.claude/jobs` is not writable there). So `base.sh` (build, seal, layer, warm), `start.sh`, `stop.sh` and
`v2.py start|stop|talk|ping` are run from your own terminal, and refuse inside the sandbox (`v2.py control`). The
daemon they start runs outside it and is the supervisor: what a command inside needs of that kind — a session released
(`v2.py drop`, `edit`), a dispatch (after most commands), a final check or commit (`result`, `verdict`), the machine for
a measurement (`measuring`, answered by message) — it asks as a request in `state/wanted/`, which the daemon notices
within seconds and the dispatch carries out before anything else; mail that cannot be handed over there stays in its
box, and the watchdog hands it over. Each command there sees only its own processes: a claim on the machine whose
process it cannot see stands, and `health.py` reads the daemon by its heartbeat (`state/warm.beat`). Each allowed path
is its own mount there, so a file is renamed only within one of them. No command is excluded from the
sandbox: an exclusion is matched on the command's text alone, and on 2026-09-21 it let any script at the excluded path,
and anything chained after it, run outside.

## Roles

| Role | Session | Does | Forks, effort |
|---|---|---|---|
| knowledge base | `kb-N` | holds what the development knows beyond the library: HANDOFF.md, the owner's words, every planner's notes; never works | the planner's base (`max`), max |
| planner | `plan-N` | one long-lived session: every event as it happens, the graph, the order, the high-level decisions, verdicts on designs and investigations, and at the end of its window the notes for the knowledge base | the knowledge base, max |
| designer | `design-ID` | a conceptual decision, written into the plan or DECISIONS.md | the middle base (`xhigh`), xhigh |
| task designer | `brief-ID` | a brief task: the planner's plan of a detailing, carried out as build and fix tasks, each with its review tasks | the middle base (`xhigh`), xhigh |
| investigator | `investigate-ID` | measures and finds out; findings written | the middle base, xhigh |
| reviewer | `review-ID` | a review task: a finished build or fix judged by the review's plan; one complete verdict, a summary for the planner, follow-ups | the middle base, xhigh |
| implementer | `implement-ID` | a written design built | the implementation base (`high`), high |
| fixer | `fix-ID` | a failed check or a rejected review repaired, when the task's own session cannot take it | the implementation base, high |
| consultation | `ask-qN` | one question answered by a fork of the consulted session | the consulted session |

A fork runs at its origin's effort: an effort change invalidates the messages cache (API documentation, prompt
caching, invalidation hierarchy), so choosing a task's effort is choosing what its session forks. A role whose base is
not built forks the max base instead (`v2.FALLBACK`); all three have been built since 2026-09-20. Each role's first
message is its protocol (`protocols/<role>.md`, with the shared parts `protocols/_*.md`): its name, its piece of work,
the held files changed since the load, and the rules it works under. A role is given only the parts that hold for it:
`_tree.md` and `_checks.md` go to the sessions that write the working tree and run checks, and not to the planner, the
task designer or a consultation, which have neither a tree nor a check — until 2026-09-20 every role was told it had a
git worktree of its own, which four of them never have, and `{TREE}` now says where the session really works, its own
tree or the one it shares. The base's system prompt (`library-prompt.md`) is every role's: the standing goal, what the
session holds, the settled distinctions, the owner, and the harness — including which mechanics of the owner's rules
it holds (committing, waiting, reporting) the harness carries out here; the protocol says the rest, and the hooks
behave exactly as the protocols say.

**Standstill.** Nothing works, nothing in the queue can start, and nothing has happened: only the planner can move
the graph, and nothing wakes it, because it is woken by events. The dispatch names it to the planner instead — what is
parked and for what, what is ready but blocked, what came back and has not been re-planned — and names it again every
`ORCH_STANDSTILL_EVERY` (30 min) while it lasts. On 2026-09-20 the orchestration stood still three times this way, six
and a half hours in all, and only `health.py` said so, to nobody.

**Slots** (`v2.dispatch`, run after every change and once a minute): one producing session (designer, investigator,
implementer or fixer, by the task's kind); beside it one supporting session, a task designer or a reviewer, not both
(the owner's decision), the brief first when nothing is ready to produce, the review first otherwise; one quick fix;
consultations side by side (up to `ORCH_CONSULT_MAX`, 4: each a fork answering one question, the owner's decision).
The planner is outside all of this: it is one session, not a worker, so the rate never holds an event back from it.
`ORCH_WORKERS` (2) caps the sum of the producing, supporting and consultation slots — a quick fix starts whatever it
says. It is not what limits production: one producing session runs whatever it is set to, and past two the machine's
two Isabelle runs bind. At 1 a finished task waited to be reviewed and a question to the knowledge base waited for a
gap in production, which is what 2 buys back (the owner, 2026-09-20).
A producing session never waits
holding its slot (the owner, 2026-09-19): with nothing productive left it parks (`v2.py park run|fix|tree|answer`) and
the slot goes to the next task; when what it waits for has come and the slot and the working tree are free, it is
resumed, its context intact, before anything new starts.

**The knowledge base** loads HANDOFF.md, the owner ledger and `state/owner-directions-new.md` (the collector runs
before every build), replies INTEGRATED and is sealed. It is resumed only to integrate a planner's notes
(`state/<kb>-notes.md` keeps them), one at a time, and sealed again; nothing forks it meanwhile. Every question to it
is answered by a fork, so questions never grow it. Its limit is set by its forks' room, not its own window: a fork
starts with its whole context, so it is rebuilt from its base before it leaves a planner less than 150K or a
consultation less than 60K before the notice (907K, so at 757K), or when it has gone cold. A rebuilt knowledge base
loads HANDOFF.md, not the notes: whatever must outlast one goes there, condensed (a settled decision written where it
belongs and referenced). HANDOFF.md is the state a planner needs to act now, bounded by `ORCH_HANDOFF_MAX` (60K
tokens) because every knowledge base holds it and every designer reads it; what was done and how goes to
`PLANNING_LOG.md`, which no base holds, nothing reads to plan from, and nothing bounds. `v2.py status` tells the
planner what its state weighs and which section carries it, so the pressure runs both ways: it grew from 6.5K
characters to 81K in a day when nothing measured it. `start.sh --fresh` leaves the one that stands behind on purpose — the planner that lives
goes with it, so the next forks the new one — and charges the first planner to take stock before it queues anything:
what has been produced and is not yet carried, what the graph no longer needs and why, and what its structure should
be under the harness as it now is. What the old knowledge base held and HANDOFF.md does not is lost to that, which
is the point of writing HANDOFF.md as the state and not as a log. A designer forks the middle base, which holds the working frontier a design needs, opening
with a batch that reads HANDOFF.md and the ledger: the most recent details are not the most important, and HANDOFF.md
holds what persists. When even a fresh knowledge
base loads within 50K of its limit, the planner is asked to condense HANDOFF.md, and `health.py` says a base
rebuild is due: that is the owner's (base.sh), and takes in what the documents now hold.

**The planner** is one session that lives across its events. Each event (a result, a verdict, an escalation, a
failure, a question, what a stop interrupted, the owner's words) reaches it as its own message as it happens: nothing
is gathered into a batch and nothing waits for a gap in production, so it works problem by problem and what it learned
from one event is still its own when the next arrives (the owner, 2026-09-20). Its turn ends when it has handled what
it was given; it is then sealed, held warm and woken by the next event. It ends once, when its window is full: then it
writes HANDOFF.md in the form of the planner's state (`## Graph`, `## Decisions`, `## Delivered`, `## Open`, `## Now`)
and, with `v2.py planned --notes FILE`, the notes the knowledge base is to hold — what it has settled, aggregated,
with what has since been answered or superseded left out — and the next planner forks from a knowledge base that holds
them. Its deliberation ends with it; what it decided persists in the task list, HANDOFF.md, the decision register and
the knowledge base. What a lost planner was given and had not handled goes to the next.

The planner and the task designer prefer tasks that can run beside each other, where the work admits it: a
dependency is written only where it is real (a task's inputs are another's artifacts, or its brief rests on a
decision another takes), never for order or tidiness, and never at the cost of splitting reasoning that belongs
together or letting two tasks establish the same notion. `v2.py status` says which tasks could start now — the width
of the graph as it was drawn; at one, nothing can take the producing slot while the task holding it is parked or
checking, which is how 2026-09-20 stood still for six and a half hours.

## Tasks and briefs

The graph is the Claude Code task list `orchestration-graph` (`CLAUDE_CODE_TASK_LIST_ID` in `planner-settings.json`),
edited by the planner and by nobody else — the guard refuses TaskCreate and TaskUpdate to every other role, the task
designer included, which proposes its tasks and their placement instead (`v2.py propose`, then the planner's
`v2.py accept`). The planner edits it in one call with `v2.py edit FILE` — tasks made, rewritten and deleted,
dependencies set or taken out, the order — judged whole (`graph_edit_problems`) and written all or nothing
(`apply_graph_edit`, on which `accept` is built too); TaskCreate and TaskUpdate still work one change a call, under
the same guard. What the planner planned before does not bind it: repair is never refused, and a deletion that would
leave something waiting on the deleted task is refused whole. `v2.py queue ID...` is the order. `v2.py` marks a task in progress with
its session when it starts, and completed when it is done, under Claude Code's own lock on the task file
(proper-lockfile's `<file>.lock` directory, stale after 10 s, read from Claude Code 2.1.273).

Every piece of work beyond a question is a task of the graph with a brief in form, planned by the same machinery
(`protocols/_brief.md`); only consultations and the planner, which are driven by events, are not. The
kinds: design, investigate, build, fix (the producing slot), brief and review (the supporting slot). The planner
writes the design and investigation tasks and the brief tasks, a brief task being the plan of a detailing; its task
designer writes the build and fix tasks and, for each, its review tasks, whose plans are the reviews' courses
(`v2.py propose BRIEFID FILE` refuses a build or fix without one). The task designer does not edit the graph: the task list is the graph and the planner alone writes it, so the designer proposes its tasks and where each goes, once and in full, and `v2.py accept BRIEFID` writes them as proposed and queues them after the brief task. Nothing is added at the end of a chain deeper than `GRAPH_DEPTH` (10), by a brief or by the planner: per chain (`chain_depths`, `past_the_limit` on the graph as the change would leave it), with detail spliced in, work that runs first and reviews exempt; a proposal that would do it is refused before anything is written, and the planner resolves it. The planner is told what placing a proposal needs (`proposal_text`), not its briefs, and reads those on demand (`v2.py proposal ID KEY...`, or `v2.py read proposal:ID:KEY`). A review task the planner writes is linked to what it reviews from its `Reviews:` line (`link_reviews`). Every command is batchable: groups separated by a bare `--`, and several ids directly where natural.
A task is committed only when all its review tasks accept; a build or fix nobody briefed a review for gets one the
harness plans from its brief. A task not in form is not taken up, and the planner is told why.

The brief: `Kind`, `Serves`, `Deliverable` (files in backticks, not directories, for the producing kinds; the tasks
for a brief; the verdict for a review), `Reviews` (a review task: the task it reviews), `Acceptance`, `Inputs`,
`Decided`, `Plan` (at least two numbered steps: each one's purpose and output, the sources it rests on by name, what
it depends on, where its check falls), `Yours`, `Planner's`, `While checks run`, `Size` (an estimate in tokens of
work, within the room its session's base leaves, `v2.room_of`: on the bases of 2026-09-20 about 364K for a build or
fix and 383K for the other kinds; a task beyond it is refused and split). It stays at the level its writer knows
without reading details: which lines, which lemmas and how to prove are the implementer's.

The result (`.build/tasks/ID/result.md`): `Status: done | partial | blocked`, `Produced`, `Decisions`, `Plan as
followed`, `Remains`, `Questions`, `Follow-ups`. A partial or blocked result goes to the planner, who splits or
re-plans the task.

## Producing, and reading in batches

The guards (`work_meter.py`, PreToolUse) refuse; they do not remind; they hold for every working role. Production is a
change to the role's own deliverable (the implementer's theories and code, the designer's decision, the investigator's
findings, the task designer's proposal, the reviewer's verdict, the planner's HANDOFF.md, notes and graph
edits, a consultation's reply) that adds or changes content: in a theory a command added or changed, comments and
layout aside, or 40 words of commentary; in a document 40 words added or rewritten; in code 5 lines (as multisets:
moved or deleted words do not count).

**Reading** (the owner, 2026-09-21) is counted in reads, and a read is a batch: one request, however many calls it
holds — that is the point of batching. A batch reads at most 50K bytes (`BATCH_BYTES`: past it the rest of the batch
is refused and goes in the next), and each call in it shows at most 5K (`READ_BYTES`), so that a large chunk is read
deliberately, in pieces: a read of a file's lines whose size is known (`sed -n A,Bp`, `head`, `tail`, `cat`)
and is longer is refused with the lines that fit named; every other command — a search, a listing, a script, a check,
a write, the harness's own — is rewritten through `cut.py` by the guard's `updatedInput` (`work_meter.bounded`), which
shows the first 5K of its output (a check or a failed command: the last, where it says how it ended or what went
wrong, quoting a failure line that stood before that end), keeps the whole under `.build/outputs/SESSION/N.txt` (the
newest 50 a session; a session's go when it is released), says how to read the rest
by its lines, and ends with the command's own status. `v2.py read` bounds itself. Grep, Glob, WebFetch and WebSearch,
whose output no hook can bound, are no session's tools (below). In two tiers: between two productions a session may make 3 reads; past that each read draws one from a reserve
of 10 (`READ_RESERVE`), and each production restarts the first tier and gives one back to the reserve, never beyond
10. Writing, asking and a refused read count for nothing. After every read the session is told what it has left in
both. The meter reads the count from the transcript, per batch (`reading_requests`), and keeps its state under a lock.
Replayed on impl-8 to impl-30 (421 stretches between writes), 3 rounds would have bound in 42% of the stretches and
held back 68% of the requests that read (6 rounds: 30% and 47%). Reading was also bounded in tokens (20K a production)
until the owner had it taken out on 2026-09-21: every call being bounded in bytes, it bound nothing they did not.

Any source is read by `v2.py read SOURCE...`, a read like any other: files and ranges, facts by name, the session's
task's `diff`, `result` and `log` (a reviewer's: the task it reviews), a task's brief (`task:ID`) and a proposal
(`proposal:ID[:KEY]`), each nameable by its lines (`path:A-B`, `diff:A-B`, `task:ID:A-B`, `proposal:ID:KEY:A-B`,
`Theory.name:A-B`). One call shows at most 5K and names the sources it had no room for. It was the gather, `v2.py step
ID N SOURCE...`, the only door to those sources, open once a step had produced and free of the tiers; the owner found
it redundant, and it was: a production restarts the tiers, so the first read after one is always allowed, and a batch
is already one read. A session still works in steps, each opened by one batch. For the planner, the task designer and
consultations of the knowledge base `v2.py read` serves statements only (a theory's statements digest), which keeps
their reading at their level; those roles are refused proof text, code, logs and diffs throughout, and listing names
is free. A read of lines partly in context already, and unchanged since, is filtered: it shows the rest through
`lines.py` and says which lines it left out; one wholly in context shows only that note and counts as no read. `v2.py
read` filters its files the same way and records as read exactly the lines it printed.

**A tree per task.** A producing task works in a tree of its own, `.build/trees/ID` (a git worktree on the branch
`task/ID`, made from HEAD, with `.build` linked to the one `.build`), so that nothing another task leaves unfinished
holds it out: its session is forked there, told so (`{TREE}`), checked there, committed on its branch and merged into
`main` by the finalizer, and the tree is taken away once its work has landed. `ORCH_TREES=0` turns this off. Trees
were withdrawn on 2026-09-20 after their first live run, and the three faults it found are repaired where they arise:
a session in a tree is listed under that tree and Claude Code keeps its transcript under the tree's own directory, so
`session_row.py` accepts a cwd under `.build/trees/` and every reader of a transcript goes through
`v2.transcript`/`transcript_dirs`; a tree carries a copy of the harness, whose scripts hand every call to the one
tree's copy (`_one_harness`, on top of `_one_tree` for the state), and a tree is not made from a HEAD whose copy does
not; and a tree made from a HEAD that lacks what stands uncommitted in the one tree refuses every check, so a new tree
is checked (`tree_trouble`) before a session is put in it and taken away if it fails. Where a task works is decided
once (`task_tree`) and its message is written from that answer: in the one tree when its own installed work stands
there or its brief names a path that stands uncommitted there (`in_main_tree`, with the reason it is told), otherwise
in its tree, and in the one tree with the reason said to it and the planner when no sound tree can be made. A task
that would start from HEAD without the work of a task it waits on — directly or through the tasks between — waits for
that work to land (`landing_wait`: `deps_done`, `startable` and the width agree). The one tree's holds reach nobody in
a tree (`tree_holder`, `finalizing`, `check_isolation`); a session in a tree may not write the repository's own
directory, and no session writes another task's tree (the write guard); `v2.py finalize` looks for the files in the
task's tree and refuses a check that names the one tree's path, since `tools/incremental_check.py` takes its project
from its own path, and a brief that names the repository by its absolute path is not in form; `v2.py read` reads
the tree the task's work stands in; and a reviewer of work in a tree is started in that tree.

**HEAD is never made worse, and main moves by one checked landing at a time.** A commit that would leave HEAD with
trouble it does not already have (`v2.new_trouble`: `tree_trouble` of the staged index or a commit, read from git
into a temporary directory, against HEAD's) is refused — by the finalizer for every commit the orchestration makes,
and by `commit_gate.py` as git's `pre-commit` and `pre-merge-commit` hook for every other (`.git/hooks/pre-commit` and
`.git/hooks/pre-merge-commit` link to it; `--no-verify` passes it by; a fault of the gate lets the commit through and
says so). On 2026-09-20 a commit took ROOT whole with two declarations whose theories stayed uncommitted, and every
tree made from HEAD refused every check. Every commit and landing holds `state/landing.lock`. A task in its own tree
lands by bringing main into its branch (`finalize.land`); when that brought anything, the repository's check of the
two together (`v2.LANDING_CHECK`, in the task's tree, output `.build/tasks/ID/landing-N`) runs before main moves; a
combination that fails goes back to the task as a failed check (`v2.landing_failed`: its quick fix, in the tree that
now holds both), and main is read again before the merge so that a commit made outside the finalizer is brought in
and checked too. What follows holds for the one tree, which the tasks that must work there still share.

**One working tree, one machine.** The working tree has one owner at a time: the task whose finalization is in flight
(`v2.tree_holder`: checking, reviewing, fixing or committing, with files to commit), the unfinished task whose
installed work stands in it until it commits (`v2.tree_writer`: a second change beside it would leave no check able to
say whose failure it was), and otherwise the producing task.
While a finalization is in flight every other session writes only under `.build/` (new files as drafts, edits of
existing files kept for after), so its check, its review's diff and its commit see its changes alone, and nothing is
ever moved under a running session; a refused session is told when the tree is free (`tree_care`), and with nothing
productive left parks for it (`v2.py park tree`); a final job is handed over only while the tree is the session's own,
so finalizations run one at a time. A task parked for its own run also holds the tree while the run reads its changes;
when the run has ended the tree is free for the producing session (`parking_care`), and its changes stay in it. The
guard records which task wrote each path (`state/tree-owners.json`) and refuses every git
command that changes the index, the working tree or the history: the finalizer alone stages, commits and pushes (git
failures and timeouts are results, never exceptions; an index lock is waited for; no credentials prompt). A task that
leaves unfinished (parked, back to the planner, lost, dropped, interrupted) leaves its changes in the working tree,
whole, until it commits or the planner re-plans over them (`v2.leave`, which names them to the planner): a change here
is a set of parts — a theory, the ROOT line that declares it, the import that reaches it, its row — and until
2026-09-20, when the harness set a task's changes aside under `.build/tasks/ID/shelf/`, moving files moved parts and
left trees that refused every task's check. Nothing makes a shelf now; `v2.py unshelve ID` brings back only one made
before then, merged (`git merge-file`) onto what has landed since, while no finalization is in flight. A task's commit takes HANDOFF.md as it stands, as every commit before v2
did; HANDOFF.md is written by the planner only. At most two Isabelle runs go at once (three have filled the machine's 60 GiB); a final check that advances the
base heap (`--advance-base`, `adopt`) waits until none runs and holds the machine (`state/isabelle-exclusive`), and
every other check is refused meanwhile. A session is never stopped (sealed, or resumed) while a background job of its
own runs: its mail waits for the job's completion, which runs its turn, and `v2.py result`, after which it is stopped,
is refused until its jobs have ended. A producing session parked for its run is not stopped either: the run keeps
going, and if its completion wakes the session early, every tool is refused until the harness resumes it.

A check that fails with the same failure after a fix three times in a row is refused until an answer on the
obstruction has come; failures that move are progress. A check a session runs — in the foreground or the background
— goes to its end and ends by listing every error it reported, one line each with where it stands, to be fixed
together (the owner, 2026-09-21: all the errors at once rather than one run for each). The guard runs it through
`check_errors.py`, which passes its output through and, when it has ended, gathers Isabelle's `***` messages from
that output and from the logs the check wrote meanwhile (a probe's under `--work`, a check's under `--output`: the
repository's checks log Isabelle's messages and print only a summary), and prints them last, where the check's cut
shows its end; a list longer than about 4K (`check_errors.ROOM`: a read's bytes, less room for the note that heads the
cut) is kept whole in the session's outputs and named. The repository's tools
are not changed for it: `tools/build.py`, where they run Isabelle, is in the execution closure of all 52 recipes, and
changing it would have had every recipe executed again. (For an hour on 2026-09-21 a check stopped at its first
error instead; the owner judged it the wrong trade — each fix then costs a run — and it was taken back.) What a
session keeps under `.build/outputs/SESSION/` — cut outputs, commands, error lists — goes when the session is
released, with its meter (the reads it holds, its counts) and the meter's lock; the newest 50 outputs and commands and
10 lists stand while it lives. Waiting (sleep, wait loops, `tail -f`, a running job's output) and subagents are
refused.

**Changing files** (the owner, 2026-09-21) is one command, `v2.py change`, its changes in a quoted heredoc of the same
call: `=== write PATH` and the whole file, or `=== replace PATH` (`replace-all`) and blocks of `<<<<<<< SEARCH`, the
text as it stands, `=======`, its replacement, `>>>>>>> REPLACE`. It takes any number of changes to any number of
files, applies them in order in memory, and writes all or none; a SEARCH that does not occur exactly once refuses the
whole call, said change by change, with where its first line stands. The guard reads the same blocks
(`v2.change_blocks`), so the write guard, the ownership of the tree and the production measure know every file
exactly. A call that makes one change is told to batch. Every other way of writing a file's content — a redirection
into a file, `tee`, `sed -i`, a script that writes — is refused and pointed to it, whatever else the command is,
except under `.build/` (`work_meter.scratch`): there any command may write a program's output, generated data or a
draft — not into a task's tree (`.build/trees/`) nor into `.build/outputs/`, the harness's records. Where a command
writes is judged before how. Moving, copying and removing files stand. Edit and Write had been batched in 10 of the
268 requests that held them, and a command's writes fail silently when they match nothing.

**A command that went wrong is fixed, not written again** (the owner, 2026-09-21). The guard keeps every Bash command
a session makes, refused ones included, numbered, under `.build/outputs/SESSION/commands/N.sh`. `v2.py again N
<<'EOF'` sends only a correction — SEARCH/REPLACE blocks on command N's text (N left out: the last; no block: as it
was) — which the guard applies, keeps as the next command, and guards and runs as if it had been typed; it is counted
as the command it runs (`resolved`). A refused call says its number and how to fix it, and so does a command that ended
failing (cut.py, told its number) — not a check, whose fault is in what it checks. A refused `v2.py change` exits
failing, so that it is told the same. Of the first runs' 1,799 commands 146 failed and 40 were followed by a
near-copy of themselves: 88K characters written again, the largest 12K.

**What the restrictions left undoable** (a pass the owner asked for, 2026-09-21: every restriction read against the
work each role must do). Found and repaired: the planner was told to put the owner's questions in the owner ledger,
which is the harness's file and refused to every session — `v2.py ledger` puts them there, numbered; a failed check
listed Isabelle's messages alone, so a native execution's error, a recipe's exception or a tool's reached nobody but by
reading logs one by one — `check_errors.py` lists, for a failed check, each part its output names as failed with the
failure its log ends on, each log written meanwhile that ends on one, and the check's summary error (none of the 276
logs of an accepted check ends on such a line); the finalizer's check gave its quick fix the log's last 30 lines, and
runs through the same runner now, so they hold the list; a failed command's cut showed its beginning, and shows its end
now, quoting the failure where it came earlier (a program's buffered output follows its unbuffered error); a program's
output could be written nowhere, generated data only pasted through `v2.py change` — under .build/ (not a task's tree,
not the harness's records) any command may write; the planner and the task designer could not read their own drafts,
a refused edit or proposal they must correct; `v2.py read` gave no way to read a long fact by its lines; git's reading
forms (`stash list`, `worktree list`, `tag -l`, `notes show`) were refused with its writing ones; a comparison in
shell arithmetic or `[[ ]]` read as a redirection, and `&>` did not; a search that found nothing was told it failed.
Left as they are, knowingly: a script a session writes and runs is not read by the guard (the finalizer and the commit
gate stand behind it); the knowledge base's reading is neither cut nor metered, as it loads what it is to hold; a
consultation forked from a released session no longer finds that session's kept outputs.

**Performance problems** have their own channel (the owner, 2026-09-19): the session that meets one does not fix it
itself or work around it; it reports it, measured (`v2.py escalate --efficiency "..."`, any working session), and goes
on with whatever does not depend on the fix, the slow run going on. The planner makes the fix a task and names it for
the reporting task (`v2.py after ID TASK`): the task is told when it lands. With nothing productive left, a producing
session parks for the run itself (`v2.py park run`), usually sooner than a fix can land, or for the fix (`v2.py park
fix`) when the run cannot finish on the path. A parked session is held warm for 3 hours (the owner's choice); past that
it is resumed to record a partial result.

## Consultation and mail

`v2.py ask --to kb|planner|designer|task-designer|reviewer "..."` routes by the asker's task: the author of the design
it builds on (the designer of a task it is blocked by), the task designer that briefed it, the reviewer that judged it,
the knowledge base, or the planner. A question to a warm, sealed author is answered by a fork of it
(`ask-qN`), several side by side; to an author whose cache has expired, by a fork of the knowledge base with the author's
written work as input. The answer (`v2.py reply QID TEXT [--decision]`) goes to the asker's mailbox; an answer that
decides something new becomes an event for the planner and a note for the knowledge base. The asker continues with
what does not depend on the answer. With nothing independent left, a producing session parks for the answer (`v2.py
park answer`: the slot is the next task's meanwhile, and it is resumed with the answer when the slot is free); any
other session ends its turn while its question is open (it is then `waiting`, held warm until the answer resumes it;
gone cold, or unanswered for 3 hours, its task goes back to the planner).

Mail (`state/mail/<name>.jsonl`) reaches a busy session at its next tool call (the gauge adds it to the context) or
when its turn would end (the Stop hook continues the turn with it); a waiting session is resumed with it while warm.
A resume that fails carries nothing, so the messages go back into the box each with its own sender, before whatever
arrived meanwhile. A box whose session is no longer in the state, or an empty one of a session that reads nothing ever
again, is swept. Everything the harness says to a session begins with `[harness]` or `Message from`, and is never
collected as the owner's words.

## Warmth

A session's last hit (`state/hits/<name>`, and for a base `<who>-base.hit`) is refreshed by its own tool calls and by
those of every fork of it, down its origins to the base. A sealed session is warm while its last hit is younger than
55 minutes (the cache lives an hour). The watchdog keeps held sessions warm with a throwaway fork before 45 minutes
(`v2.py ping`, as `base.sh warm`: about 0.1 of its context per hour, against about 2.0 for one cold resume): the
knowledge base always; a task's session while its task is checked, reviewed, fixed or committed; its reviewer while a
re-review may come; a parked session, and one waiting on its question, for 3 hours; a task designer or a designer while tasks it briefed or designed are
open, for at most 3 hours. Everything else is released. The planner keeps a task that may consult an author close
after that author's task.

## Finishing a task

`v2.py finalize ID --check CMD --files ... --message FILE` hands over the final job; `v2.py result ID` records the
result. Then, without cycles: the finalizer's check (`finalize.py check`, a process group killed past
`ORCH_FINAL_MAX`) → the reviews (the task's review tasks for builds and fixes, all of which must accept; the planner
for designs and investigations) → the
commit of exactly the named files and the push (`finalize.py commit`) → the task completed, its summary and follow-ups
an event for the planner. A failed check or a rejection gets one quick fix: every blocking finding at once, to the
task's own session resumed while warm (a fixer otherwise), under a budget of 15 minutes and 8 rounds; the re-review
judges only the listed findings and what the fix broke. A second failure or rejection goes to the planner.

## The watchdog

`watchdog.py`, once a minute while the orchestration is active, and within seconds of a request from inside the
sandbox (see "The sandbox"): a session gone three runs in a row is lost and its piece
of work goes back (a producing session's task to the planner, a review or brief to be started again, what a planner
had not handled to the next one, a question to be asked again, the knowledge base rebuilt); an idle session with mail
is resumed with it; after a usage-limit stop it is resumed once the limit has reset; one at the end of its window is
lost; one whose piece of work has ended, or that waits, is sealed; the planner, whose turn ends with the events it was
given, is sealed between them and held warm, and lost if it goes cold there; one whose turn ended without any of that
is resumed after five minutes. Then the held sessions are pinged or released, parked ones past their hold resumed, a fix past its budget
given to the planner, and a finalizer given up when its process has ended without reporting or has outlived its wait
for Isabelle and its check (it and its check's process group are then ended); a late report is then only an event.
Each part, and each part of the dispatch, runs on its own: one that fails is logged and holds up nothing else. What nothing refers to any more (sessions released a
day ago whose task is done, questions answered a day ago) moves to `state/v2-archive.jsonl`, so that the state every
hook reads stays small. The watchdog's care and the dispatch run under one lock. Every action is a line in
`state/v2.log`.

## Hooks

`planner-settings.json` (the planner) and `worker-settings.json` (every other session) wire
the same scripts; they differ in one thing only, `CLAUDE_CODE_TASK_LIST_ID`, which puts a session on the shared task
list that is the graph. Every session on it sees the others' edits to it injected into its context, so only the one
role that edits the graph is given it — the knowledge base was on it until 2026-09-20, could not edit it, and
passed what was injected on to every session forked from it; the task designer was on it until 2026-09-21, when it
stopped writing tasks and began proposing them. Every other session's task list is its own, named by
its own session, and the bases have none. Both wire the same scripts, which act by role (`v2.role_of`, from `state/v2.json`): PreToolUse `work_meter.py guard`
— whose matcher must name every tool of `work_meter.GUARDED_TOOLS`, because a tool left out of it never reaches the
guard at all and that guard's refusals and records simply do not happen (the write tools stood outside it for the
whole first live run of 2026-09-20, and the tests, which call the guard directly, all passed meanwhile);
PostToolUse `ctx_gauge.py gauge` (mail, the notice near the window's end at 907K and the end mark at 942K, below the
972K the API has accepted, the session's reading and production, the warmth marks); Stop `ctx_gauge.py stop` (a
session ends its turn only when its piece of work has ended, while it waits, or, for the knowledge base, the planner
between its events and a session the owner speaks to, always); PreCompact `ctx_gauge.py tripwire`; SessionStart sleeps ten seconds, which holds a
fork's first request until its tools have loaded.

## The bases and their layers

Each base's load list is split by a `# === layer ===` line. Above it is the **stable reference** — the founding
theories and the central ideas — which the owner builds and seals and which changes only when the library's
vocabulary does: it moved by nothing at all in the twelve hours the layers moved by 84K, 95K and 122K tokens. Below
it is the **frontier layer**: the generated indexes, the working frontier, the tools, the decisions by name, the
reasoning inventory, the plan and the owner's words last. The harness builds the layer as a fork of the sealed
stable base (`base.sh WHO layer`), seals it, and records it; from then on every role of that base forks the *layer*,
and `v2.py start` refuses while a split base has none, since its roles would fork a reference with nothing that
steers them.

A fork of the layer reads the whole prefix under it from cache — measured on 2026-09-20: a fork of the sealed
knowledge base read 538,051 of its 538,044 tokens and wrote 62 — so one keep-warm ping serves the layer and the base
under it. The layer is refreshed when the files it holds have changed by `ORCH_LAYER_STALE` (20%) of its tokens, or
when `state/<who>-layer.refresh` asks; a refresh re-measures the working frontier from the sessions of the roles
that fork that base, writes 112K to 234K instead of rebuilding 473K to 518K, and leaves the reference untouched. The
layer it replaces is stopped but not removed, and its snapshot is kept while any session still holds it, so a session
forked before a refresh is told what changed against the load it actually has. Only the layer is pinged; whether that
keeps the stable base's own entry warm for the next refresh (itself a fork of the base) has not been measured, so each
sealed layer records in `state/warm.log` whether it read its base from cache (`layer WHO: OK|MISS …`), and `health.py`
names a miss there as a layer that wrote its base cold.

A load is complete when every chunk has arrived whole in the session's tool results and the session then replies
`LOADED <pack id>`; the id may carry one slipped character, since the chunks are what is checked exactly (on
2026-09-21 the max layer loaded all four chunks and mistyped its 64-character id, and was refused). A layer session
that loaded and was not recorded is recorded as it stands with `base.sh WHO layer --adopt NAME PACK` — the same
checks, and only a fork of the recorded base — instead of being loaded again.

## How the base is loaded

`base.sh max build` (also `build-packed`) runs `base_pack.py build`: it freezes every file of the load list as
its digest, checks that each digest can be restored byte for byte, and splits the bundle into chunks of at most
120,000 bytes: a Bash result is shown whole up to `bashOutputMaxChars` (128,000 characters, set in every settings file;
Claude Code's default is 30,000, past which it saves the output to a file and shows a preview), which does not enter
the cached prefix (verified 2026-09-19: forks with and without the setting read their origin's whole prefix). The base session receives them through one Bash call per chunk (`base_pack.py emit`), so the load
carries none of the Read tool's line numbers or per-file calls. The loaded form is `all-but-fact-groups`: every
reversible layer except the grouping of fact names. Isabelle symbols appear as glyphs, omission notes are short
(`(* proof:12 *)`), indentation outside strings, cartouches and comments is removed, the theory-name index
shares prefixes, and a theory's header omits the path its `theory X` line already gives. Lemma names stay
written out, because they show what each founding theory can do. A short legend says how to read all of this,
and that theory files spell symbols as escapes: Isabelle rejects a glyph in a theory file with an inner lexical
error on that line (checked 2026-09-19), and the system prompt says the same. Each tier gets a subject
heading; the curation notes of a load list never reach the loaded text.

The base and every session forked from it start lean: `session-flags` gives exactly the tools the sessions have —
Bash, TaskCreate, TaskUpdate and TaskStop — no MCP connectors and no skills list. The rest went on 2026-09-21 (the
owner), and the guard refuses each should one ever be called, saying where its work goes (`REMOVED_TOOLS`): Grep,
Glob, WebFetch and WebSearch show what no hook can bound (a hook rewrites a call before it runs, and replaces only an
MCP tool's result after); Read, Edit and Write were one file a call where Bash and `v2.py change` take many; Agent,
TaskOutput and Monitor were always refused and never used; and ToolSearch is what made Claude Code defer tools at
all — with it in the list, TaskCreate, TaskUpdate, TaskStop and the rest were names to load first (a request over the
whole context each time, 42 of them), and without it every tool loads at the start (measured on Opus 5, 2026-09-21).
Every settings file a session starts with (`base-settings.json`, `worker-settings.json`, `planner-settings.json`) sets
`DISABLE_GROWTHBOOK=1`: EndConversation comes behind a GrowthBook feature flag that one session's start fetches in time
and another's not, so bases and forks started with the same flags were sent four tools or five, and a fork that drew
otherwise than its base read none of it from cache. With the flags off every session is sent the same four and forks
read their base whole (five probes, 2026-09-21: `.build/probe-*.sh`; `--disallowedTools` did not take the tool out;
the sandbox was not the cause). Flag-gated behaviour runs at Claude Code's built-in defaults in these sessions.
`base.sh` (build, warm) and `v2.py` (fork) pass the flags; the flags must be identical for a fork to read the base
from cache, so a base and a started session record the flags they were started with, and nothing forks, pings or
layers over one started with others (`v2.other_tools`, `base.sh`'s `lean_as`): each such fork would write the whole
prefix again. A change to `session-flags` therefore means building every base again (`base.sh WHO build`, `seal`);
the knowledge base follows its base by itself. A bare `claude --bg --resume`, as a session is woken,
keeps them: a woken lean session listed the same tools and read its whole prefix from cache (verified 2026-09-19).

Verified 2026-09-19 through the real scripts with the real model, effort and flags: a small packed base built by
`base.sh max build` loaded through Bash, `check-load` accepted its transcript, and a fork started by the v1
launcher read it from cache on its first request, `cache_read=20062 cache_write=97` against a base context of
20,064.

`seal` accepts a packed load only when `base_pack.py check-load` finds every chunk, complete, in the main
transcript and the final `LOADED <pack id>` after them; a model's claim or a context size is not enough. Claude
Code stores a Bash result without its trailing newline, so the chunk envelopes are matched without it
(verified 2026-09-19 with a real two-chunk load; the earlier exact match found none). A packed base is not
extended: change the list and build again. The older loader, in which the session read every listed file with the Read
tool, and `extend` went when the Read tool did (2026-09-21): the pack is the one loader.

Every pack also holds the other combinations of layers for comparison, including the plain bundle and the fact
grouping of `pack_notation.py`; none of them is loaded. Sizes are estimated from byte-per-token ratios measured
on Opus 5 on 2026-09-19 with one-word runs over samples: theory text 2.41 bytes per token in every written form,
Markdown 3.98, the theory-name index 2.41 (the prefixed index 2.59); the lean session 11.5K tokens with the
role prompt. Measured on 27 theories against the plain bundle: glyphs −7.3%, short notes −2.4%, compact layout
−1.7%, fact groups −1.4%, compact headers −0.9%; the prefixed index −33%. `base_pack.py count DIR` measures
payloads exactly and free with Anthropic's token-count endpoint; it needs `ANTHROPIC_API_KEY` and does not use
Claude Code's login.

## The owner's directions

**How to give them.** Speak to the planner for anything about what is done, in which order and why: `talk.sh` joins
the planner that lives (or opens one, a fork of the knowledge base); it waits for your words, acts on
them in the graph, the order and the decisions, writes them into HANDOFF.md and its notes, and ends when you are done;
the knowledge base integrates its notes, so every later planner, and every knowledge base rebuilt from HANDOFF.md,
holds them. Speak to a working session (`attach.sh producer|support|fix|consultant`) for its own piece of work: a
correction to what an implementer is writing, a concern for a reviewer. It acts within its task, and what you said
reaches the planner as an event at once, so that anything beyond the task is planned. The answer to an open
question of the ledger goes to the planner like any direction. Whatever you type is recorded, verbatim and
dated, with the session and task it went to, in `owner-ledger.md` (ctx_gauge.py owner, the UserPromptSubmit hook of
every orchestrated session: the harness's own words, launch prompts and notifications are never taken for yours).
Directions meant to hold for every session, always, go into what the bases load (the owner's words and the operating
rules: the memory, AGENTS.md, DEVELOPMENT_WORKFLOW.md, the curated directions), which a base rebuild carries to every
fork; `library-prompt.md` holds the standing goal and the two directions of 2026-09-19.

**What the bases hold of them.** The base holds the curated selections, `owner-directions.md` (Claude sessions) and `codex-owner-directions.md`
(the foundational Codex session): verbatim excerpts, each checked against its transcript record
(`extract_owner_directions.py --verify`; the selections and hashes are in the two `*-selection.json` files).
What the owner says after those were collected — `reviewed_through` in `owner-directions-selection.json` — is
loaded by every knowledge base: `v2.py` runs `extract_owner_directions.py --new`, which writes the owner's typed
words since then, from Claude sessions and interactive Codex sessions of this repository, to
`state/owner-directions-new.md`, what the owner typed while a session was working included (Claude Code records
that as a queued command, not as a message). Sessions that work on the orchestration itself are left out: a
session of no role (and no v1 implementer) whose own tool calls name anything in this directory
beyond the ledger, the directions and `show.py`. A fork's copy of its base's load is not its own, and a session of a
role that looks up the orchestration's state still works on the library. Launch prompts, what the
harness says to its sessions and automated Codex runs are left out too. When the selections are curated again,
move `reviewed_through` with them.

## Orchestration notes stay out of the content

The project memory (`~/.claude/projects/-home-julius-structure-and-semantics/memory/`) is loaded into every
Claude session of this repository, the base and its forks included, and the load list holds it as well. Notes
about the orchestration — its design history, costs, cache behaviour, what to improve — therefore live in
`notes/`, never in the project memory, and nothing loaded or read at start comments on the orchestration.

## What the base is for, and how its list is chosen

The base sets direction; it is not a lookup cache. What a fork has in view is what it thinks with, so the base holds
the owner's words, the operating rules, the plan, the reasoning inventory, the name of every theory (so that it
knows what exists before it invents), and the *founding* theories of the library's own ideas — small theories where
a notion and its locally owned contract are established, not their downstream mass. Each load list has hand-kept
`# pinned…` tiers for these, a generated `# measured` tier for the frontier and tools recent sessions actually worked
in (density-ranked; v1 implementers and the sessions of every role, forks included, their copied base part skipped,
sessions that work on the orchestration left out), and an `# optional` tier that is never loaded. Every run of
`select_base_load.py`, `--dry-run` included, regenerates the generated indexes (`state/held/theory-names.md`,
`decisions-index.md`, and `theory-map-index.md` without the theories the list holds, when the list holds it);
`base.sh` regenerates them before it freezes a new pack. The target is `ORCH_BASE_TARGET` (`manifest.TARGET`), 530K
loaded with everything included, the owner's request of 2026-09-19; `select_base_load.py` sizes the measured tier
against it in the loaded form, and the pack report and `seal` say when a load exceeds it. The first full packed load
(2026-09-19, base 32f5e011) measured 560,299 tokens against an estimate of 526,647; the estimator's constants in
`base_pack.py` are calibrated on it. At 530K the selector would keep 22 of the 41 working-frontier files; the base
was sealed with all 41.

Theories and tools are held as statements, not as files (`digest.py`): every command of a theory verbatim —
header, commentary, definitions, locales and their assumptions, interpretations, and the statements of all
lemmas — with each proof replaced by one comment giving its length and the library facts it cites (which
contracts the result consumes), and ML bodies likewise; a tool is its docstrings, signatures and command-line
arguments. It is a mechanical projection, verbatim where it keeps anything, and carries no authority; whatever
is edited is read from its source. Checked over all 1,757 theories: every kept line occurs verbatim and in
order, no lemma or theorem statement is lost, 61% of the text remains (tools: 14–30%).

Nothing is discarded; ideas are held at three resolutions. Every theory of the library by name. The founding
theory of every notion of the library's vocabulary (244 of them) as *definitions*: commentary, definitions,
locales and declarations verbatim, and the names of everything proved there — generated into the
`# every other founding theory` tier. And the theories in the hand-kept `# pinned idea` tiers as full
*statements*, for the ideas whose lemma statements are themselves the point (uniqueness, locality, exactness).
Moving a theory between the two is moving its line. A tier's header names its level (`as definitions`, or
`as signatures`: each definition by its name and type up to `where`, its equations omitted); the drafts for the
next three bases hold the founding theories at signatures (`notes/bases-design.md`). Measured: all 244 as definitions 265K tokens, as
statements 542K; with 49 pinned as statements the base loads at about 611K. A cut by usage was tried and
rejected: holding only the lemmas that other theories cite would have dropped `selection_at_unique` and
`selection_environment_locality`, which carry the idea and are cited by no one by name.

The idea tiers are the owner's to curate. `idea_candidates.py` writes `idea-candidates.md`: every notion of
the library's own vocabulary (a word carried by four or more theory names), its founding theory by import
order, size, number of dependents, and the map's description — 262 notions, 1.1M tokens if all were pinned.

Evidence behind this, from the first run: every correction the implementers needed was about an idea the
library already has — admission and selection conflated, history conflated with adoption, a locus used as a
payload, publication that belonged in a transaction, a contract storing what its request's context holds, a
non-local reading, a silent empty result, new index notions where four existed — and what they then went and
read were exactly the founding theories (`RRA_Selection`, `RRA_Replacement`, `Ordered_Member_Trees`,
`Binary_Relation_Stores`, `Generation_Structures`). Their searches were for `selection_lookup`, `transact`,
`generation_core`. A first, hand-made list had been wrong in the other direction: `DECISIONS.md`,
`ADMISSION.md` and `README.md` were never consulted, and only 41 of the 180 theories implementers touched
belonged to the families it loaded.

Sizes use characters per token measured on this project's Opus 5 transcripts — Markdown 3.05, Isabelle 2.46,
Python 2.54 (an earlier 3.9 from a Haiku run understated by a third); a loaded base measured 690K against an
estimate of 699K, and Fable tokenized the same material to within a thousand tokens.

## Parts

| File | Role |
|---|---|
| `start.sh`, `stop.sh`, `talk.sh`, `attach.sh` | start or rejoin; stop every session; speak to the planner; open and follow a role |
| `v2.py` | the state, the roles and slots, forks, resumes, sealing and warmth, the knowledge base, the dispatch, and every command of the sessions and the harness |
| `protocols/` | each role's first message (`<role>.md`) and the shared parts (`_*.md`) |
| `planner-settings.json`, `worker-settings.json` | the hooks, and the task list of the roles that carry it |
| `finalize.py` | a task's check, and after its verdict its commit and push |
| `warm_daemon.sh`, `watchdog.py` | the daemon: the sessions, what is held warm, the dispatch; keep-warm pings of the bases when no fork is using them |
| `work_meter.py`, `show.py` | the guards and the production meter; named facts whole, or as statements |
| `cut.py`, `lines.py` | the cut of a command's output to a read's bytes, kept whole; the missing spans of a filtered read |
| `check_errors.py` | a check run to its end, every error it reported listed last with where it stands |
| `commit_gate.py` | git's `pre-commit` and `pre-merge-commit` hook: no commit leaves HEAD with trouble it does not have |
| `ctx_gauge.py` | context gauge (what the next request carries at least), the notices at 907K and 942K below the 972K the API has accepted, mail delivery, the Stop rule, warmth marks, the compaction tripwire |
| `session_row.py`, `session_fork_check.py` | a named session's listing row; whether a fork's first request read its origin from cache (logged by `v2.py`) |
| `efficiency.py` | how each session spent its window and what it produced, by role |
| `base.sh`, `base_pack.py`, `base-settings.json` | pack the list, load it chunk by chunk, check the load, seal, warm and drop the base; `pack_notation.py` holds the comparison notations |
| `base-load-max.txt`, `base-load-xhigh.txt`, `base-load-high.txt` | the load list of each base: the planner's and the knowledge base's (max), the middle one (xhigh), the implementation one (high); `notes/bases-design.md` is why each holds what it holds |
| `library-prompt.md` | the system prompt of every base, which every fork inherits: the standing goal, what the session holds, the settled distinctions, the owner, the harness |
| `select_base_load.py`, `idea_candidates.py`, `idea-candidates.md`, `manifest.py`, `digest.py` | the lists' generated tiers and indexes, the owner's curation table, the snapshot that names held files changed since the load, the statement digests |
| `owner-ledger.md` | the owner's directions verbatim, and open questions with the provisional choice made |
| `owner-directions.md`, `codex-owner-directions.md`, `*-selection.json`, `extract_owner_directions.py` | the owner's curated directions held in the base, verified against the transcripts; `--new` writes what the owner said since, which every knowledge base loads |
| `notes/` | the orchestration's own notes (design history, measured costs, cache and transcript behaviour); never loaded |
| `fakes.py`, `test_*.py` | a throwaway world with a fake `claude`, and the tests: the flows of `v2.py`, the finalizer, the guards, the gauge, the watchdog, following, start and stop, lookups, measurement, the collection of new directions, packing; no session is launched. Run them by name (`python3 -m pytest -q test_*.py`), since `state/held` holds digests of repository tests |
| `health.py`, `state/` | report; the state, mail, hits, flags, base records, manifests, logs (ignored by git) |
| `../settings.json` | `worktree.bgIsolation: none` — without it a background session edits a worktree copy, losing the uncommitted tree and breaking the path-bound Isabelle heaps |

## Verified (2026-09-18, Claude Code 2.1.273)

- A session-level fork of a stopped base (`--bg --resume <base> --fork-session`, same model, effort and launch
  mode) reads the base from cache: at full size `cache_read=690311 cache_write=469`; two real rotations each
  `cache_read=690406 cache_write=1823`. A sealed session resumed bare continues under the same id; with flags it
  starts a copy. (`base.sh extend` grew a sealed base that way; it went with the Read tool on 2026-09-21.)
- What keeps a base warm (TTL forced to five minutes): a fork started 456 s after the base's last direct hit,
  while another fork worked, read it all; after 400 s of silence a fork wrote all 81,528 tokens cold. A ping
  whose text repeats an earlier one matches that fork's entry, not the base: pings carry a timestamp.
- One fork read nothing of its base (`cache_read=0`) although prompt and tools were byte-identical; its
  flag-gated tools and the connector were still loading at its first request. Every settings file now has a
  `SessionStart` hook sleeping ten seconds, which holds the first request back; no miss since.
- Waking: `claude stop` plus a bare `claude --bg --resume <id> "prompt"` keeps id, name, saved options, hooks
  and cache. Nothing else restarts a background session after "You've hit your session limit".
- Background sessions do not inherit the launching shell's environment (use `--settings` `env`). In
  `claude agents --json`, `status` (busy/idle) is live; `state` lags. Auto permission mode needs Opus 4.6+,
  Sonnet 4.6+ or Fable. A harness kills a session's background commands when the machine runs short of memory
  (three concurrent Isabelle runs reached 59 of 60 GiB), so nothing essential lives in a session's background.
- The Read tool: 25K tokens a call, 256KB a file, lines cut at 2,000 characters — which is what the older loader
  worked around; it and the tool are gone (2026-09-21). No tool result was ever cleared from context in sessions up to 955K.

## Verified (2026-09-19, Claude Code 2.1.273)

- The ceiling is below the window. The API accepted impl-23's request of 972,479 tokens and refused the next,
  of about 979K, as "Prompt is too long": Claude Code retries a request whose input and max_tokens exceed the
  context limit with a smaller max_tokens, but not below 3,000, and starts its own compaction of a 1M window
  only at 987K, so it never runs first. impl-23 never reached its handoff; the compaction tripwire rotated it.
  The gauge works against 972K.
- When the gauge's hook runs, the request that made the tool call is sometimes not recorded yet (impl-23's
  notice said 956K while that request carried 972K), so the gauge counts what the next request carries at
  least. Replayed over the 2,558 tool calls of impl-8 to impl-26, that count is within 50 tokens (median) when
  the calling request is recorded, never more than 12K high, and short by at most the unrecorded request's
  output (p99 25K). One request has grown the context by up to 35K, four by 53K at p99.
- Every fork of the packed base 32f5e011, impl-8 to impl-26, read it from cache on its first request
  (`cache_read=560516`), and the watchdog rotated them eighteen times by its own timer, every 35–50 minutes at
  about 945K; no keep-warm ping and no wake was needed.
- A task list named in a session's settings (`env.CLAUDE_CODE_TASK_LIST_ID`) is the one its TaskCreate writes,
  metadata included (a probe session). Whether it leaves a fork's cached prefix intact shows at the first planner's
  start (its cache line in `state/v2.log`). SendMessage is not in the forks' tool set (`session-flags`, part of the
  base's cached prefix), hence the mailboxes.

## Cost, measured

The plan meter fits API-style weights on this account's own limit windows within ±15%: cache reads 0.10,
one-hour writes 2.0, output 5 per input token, Fable about 3× Opus; "reads are free" does not fit. So the cost
of any design is Σ over sessions of model weight × context per request × requests per hour. With a 700K base
and a Fable knowledge base the first run used about 32M Opus-equivalents an hour (42% of a window) against 11M
for a single plain session; the knowledge base and a Fable maintenance session were 44% of it. Implementers
alone on a 700K base: about 17.7M an hour, rotating every 16–19 minutes. A 540K base gives about 460K of room.
On the 560K packed base, impl-8 to impl-25 used about 17M an hour over 11.7 hours, with no usage-limit stop.

## What has run live, and what not yet

v2 ran live on 2026-09-20, in several runs from 00:15 to 22:36 (71 sessions started; from 20:04 on the layered bases
and one long-lived planner, whose first run reviewed, accepted and committed task 7 as `44738c20` in ten minutes),
each stopped by the owner to repair what it showed; it has not run since. Verified there: a fork of the knowledge base under `planner-settings.json`'s task-list variable reads
it from cache (`plan-29`: `cache_read=485372`, `state/v2.log`); sealed sessions other than a base resumed (the
knowledge base, implementers); the keep-warm pings of the layers.

Built and tested since, against a fake `claude` (`fakes.py`), and not yet run by a harness session: `v2.py read`,
`change` and `again`; the cut of every output (`cut.py`) and the filtered reads (`lines.py`); `check_errors.py`; the
four-tool set and the refusal of every other tool; `v2.py ledger`. The rewrites they rest on — a PreToolUse
`updatedInput` is what runs, and what the hook after the call is given — were probed with real sessions outside the
harness (2026-09-21). Every base must be built again before they can run, since each was started with the old tool
list. Still unverified with real sessions: the watchdog resuming a session after a usage-limit stop or a lost turn;
`attach.sh` following a real role.
