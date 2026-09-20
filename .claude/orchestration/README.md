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
    .claude/orchestration/health.py             # one screen; lines that need someone start with ATTENTION
    .claude/orchestration/v2.py status          # the slots and the queue; `v2.py graph` the task graph
    .claude/orchestration/efficiency.py         # how each session spent its window and what it produced, by role

`start.sh` refuses without a sealed base. `stop.sh` makes the orchestration inactive; what it interrupted is an event
for the planner, and `start.sh` resumes with the sealed knowledge base. A wake writes
`state/<name>.woken` before it stops a session, so that `attach.sh` tells a wake from leaving the view on purpose.
What you type to any orchestrated session is recorded verbatim and dated in `owner-ledger.md` by its
UserPromptSubmit hook, and (but in the planner itself) becomes an event that reaches the planner at once; what is
yours to decide the planner decides provisionally, records there as an open question with its basis, and the work
continues (see "The owner's directions").

## Roles

| Role | Session | Does | Forks, effort |
|---|---|---|---|
| knowledge base | `kb-N` | holds what the development knows beyond the library: HANDOFF.md, the owner's words, every planner's notes; never works | the planner's base (`max`), max |
| planner | `plan-N` | one long-lived session: every event as it happens, the graph, the order, the high-level decisions, verdicts on designs and investigations, and at the end of its window the notes for the knowledge base | the knowledge base, max |
| designer | `design-ID` | a conceptual decision, written into the plan or DECISIONS.md | the knowledge base, max |
| task designer | `brief-ID` | a brief task: the planner's plan of a detailing, carried out as build and fix tasks, each with its review tasks | the middle base (`xhigh`), xhigh |
| investigator | `investigate-ID` | measures and finds out; findings written | the middle base, xhigh |
| reviewer | `review-ID` | a review task: a finished build or fix judged by the review's plan; one complete verdict, a summary for the planner, follow-ups | the middle base, xhigh |
| implementer | `implement-ID` | a written design built | the implementation base (`high`), high |
| fixer | `fix-ID` | a failed check or a rejected review repaired, when the task's own session cannot take it | the implementation base, high |
| consultation | `ask-qN` | one question answered by a fork of the consulted session | the consulted session |

A fork runs at its origin's effort: an effort change invalidates the messages cache (API documentation, prompt
caching, invalidation hierarchy), so choosing a task's effort is choosing what its session forks. Until the base topic
builds `xhigh` and `high`, their roles fork the present base at max. Each role's first message is its protocol
(`protocols/<role>.md`, with the shared parts `protocols/_*.md`): its name, its piece of work, the held files changed
since the load, and the rules it works under. A role is given only the parts that hold for it: `_tree.md` and
`_checks.md` go to the sessions that write the working tree and run checks, and not to the planner, the task designer
or a consultation, which have neither a tree nor a check — until 2026-09-20 every role was told it had a git worktree
of its own, which four of them never have, and `{TREE}` now says where the session really works, its own tree or the
one it shares. The base's system prompt describes the v1 implementer; every protocol
names what of it does not apply, and the hooks behave exactly as the protocols say.

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
tokens) because every knowledge base holds it and every designer reads it whole; what was done and how goes to
`PLANNING_LOG.md`, which no base holds, nothing reads to plan from, and nothing bounds. `v2.py status` tells the
planner what its state weighs and which section carries it, so the pressure runs both ways: it grew from 6.5K
characters to 81K in a day when nothing measured it. `start.sh --fresh` leaves the one that stands behind on purpose — the planner that lives
goes with it, so the next forks the new one — and charges the first planner to take stock before it queues anything:
what has been produced and is not yet carried, what the graph no longer needs and why, and what its structure should
be under the harness as it now is. What the old knowledge base held and HANDOFF.md does not is lost to that, which
is the point of writing HANDOFF.md as the state and not as a log. A designer forks the middle base, which holds the working frontier a design needs, opening
its first gather with HANDOFF.md and the ledger: the most recent details are not the most important, and HANDOFF.md
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
edited by the planner and the task designers and by nobody else (the guard refuses TaskCreate and TaskUpdate
to the other roles that carry that setting). `v2.py queue ID...` is the order. `v2.py` marks a task in progress with
its session when it starts, and completed when it is done, under Claude Code's own lock on the task file
(proper-lockfile's `<file>.lock` directory, stale after 10 s, read from Claude Code 2.1.273).

Every piece of work beyond a question is a task of the graph with a brief in form, planned by the same machinery
(`protocols/_brief.md`); only consultations and the planner, which are driven by events, are not. The
kinds: design, investigate, build, fix (the producing slot), brief and review (the supporting slot). The planner
writes the design and investigation tasks and the brief tasks, a brief task being the plan of a detailing; its task
designer writes the build and fix tasks and, for each, its review tasks, whose plans are the reviews' courses
(`v2.py briefed BRIEFID NEW...` refuses a build or fix without one, and queues the new tasks after the brief task).
A task is committed only when all its review tasks accept; a build or fix nobody briefed a review for gets one the
harness plans from its brief. A task not in form is not taken up, and the planner is told why.

The brief: `Kind`, `Serves`, `Deliverable` (files in backticks, not directories, for the producing kinds; the tasks
for a brief; the verdict for a review), `Reviews` (a review task: the task it reviews), `Acceptance`, `Inputs`,
`Decided`, `Plan` (at least two numbered steps: each one's purpose and output, the sources it rests on by name, what
it depends on, where its check falls), `Yours`, `Planner's`, `While checks run`, `Size` (an estimate in tokens of
work, within the room its session's base leaves, for every kind alike: about 327K on the present 560K base; a task
beyond it is refused and split). It stays at the level its writer knows without reading
details: which lines, which lemmas and how to prove are the implementer's.

The result (`.build/tasks/ID/result.md`): `Status: done | partial | blocked`, `Produced`, `Decisions`, `Plan as
followed`, `Remains`, `Questions`, `Follow-ups`. A partial or blocked result goes to the planner, who splits or
re-plans the task.

## Producing, and reading in batches

The guards (`work_meter.py`, PreToolUse) refuse; they do not remind; they hold for every working role. Production is a
change to the role's own deliverable (the implementer's theories and code, the designer's decision, the investigator's
findings, the task designer's briefs and graph edits, the reviewer's verdict, the planner's HANDOFF.md, notes and graph
edits, a consultation's reply) that adds or changes content: in a theory a command added or changed, comments and
layout aside, or 40 words of commentary; in a document 40 words added or rewritten; in code 5 lines (as multisets:
moved or deleted words do not count). Between two productions a session takes at most 3 requests and reads at most 20K
tokens; after every read, search or check it is told what it has left; past either limit, reads, searches and checks
are refused. Replayed on impl-8 to impl-30 (421 stretches between writes), 3 rounds would have bound in 42% of the
stretches and held back 68% of the requests that read (6 rounds: 30% and 47%): v1 implementers read one slice per
request, and 3 rounds, the owner's choice, force a step's reads into one or two requests.

The batching is structural: every step opens with one gather, `v2.py step ID N SOURCE...`, which prints every source
the step names (files and ranges, facts by name, and for a finished task `diff`, `result`, `log`) in one response,
free of the limits, and records the ranges as read; the next step's gather opens only after this one has produced.
The session decides what to read; the structure decides that it is read at once. For the planner, the task designer
and consultations of the knowledge base a gather serves statements only (a theory's statements digest), which keeps
their reading at their level; those roles are refused proof text, code, logs and diffs throughout, and listing names
is free.

**One working tree, one machine.** The working tree has one owner at a time: the task whose finalization is in flight
(`v2.tree_holder`: checking, reviewing, fixing or committing, with files to commit), and otherwise the producing task.
While a finalization is in flight every other session writes only under `.build/` (new files as drafts, edits of
existing files kept for after), so its check, its review's diff and its commit see its changes alone, and nothing is
ever moved under a running session; a refused session is told when the tree is free (`tree_care`), and with nothing
productive left parks for it (`v2.py park tree`); a final job is handed over only while the tree is the session's own,
so finalizations run one at a time. A task parked for its own run also holds the tree while the run reads its changes;
when the run has ended its changes are set aside (`parking_care`) and the tree is free. The guard records which task wrote each path (`state/tree-owners.json`) and refuses every git
command that changes the index, the working tree or the history: the finalizer alone stages, commits and pushes (git
failures and timeouts are results, never exceptions; an index lock is waited for; no credentials prompt). A task that
leaves unfinished (parked, back to the planner, lost, dropped, interrupted) has its changes set aside under
`.build/tasks/ID/shelf/` once its session has stopped, and the producing session is told; they come back, merged (`git
merge-file`) onto what has landed since, when the parked task is woken or a task continuing it runs `v2.py unshelve
ID`, only while no finalization is in flight. A task's commit takes HANDOFF.md as it stands, as every commit before v2
did; HANDOFF.md is written by the planner only. At most two Isabelle runs go at once (three have filled the machine's 60 GiB); a final check that advances the
base heap (`--advance-base`, `adopt`) waits until none runs and holds the machine (`state/isabelle-exclusive`), and
every other check is refused meanwhile. A session is never stopped (sealed, or resumed) while a background job of its
own runs: its mail waits for the job's completion, which runs its turn, and `v2.py result`, after which it is stopped,
is refused until its jobs have ended. A producing session parked for its run is not stopped either: the run keeps
going, and if its completion wakes the session early, every tool is refused until the harness resumes it.

A check that fails with the same failure after a fix three times in a row is refused until an answer on the
obstruction has come; failures that move are progress. Waiting (sleep, wait loops, `tail -f`, TaskOutput, a running
job's output) and subagents are refused, and so is a read of lines already in context and unchanged.

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

`watchdog.py`, once a minute while the orchestration is active: a session gone three runs in a row is lost and its piece
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

`planner-settings.json` (the planner and the task designers) and `worker-settings.json` (every other session) wire
the same scripts; they differ in one thing only, `CLAUDE_CODE_TASK_LIST_ID`, which puts a session on the shared task
list that is the graph. Every session on it sees the others' edits to it injected into its context, so only the two
roles that edit the graph are given it — the knowledge base was on it until 2026-09-20, could not edit it, and
passed what was injected on to every session forked from it. Every other session's task list is its own, named by
its own session, and the bases have none. Both wire the same scripts, which act by role (`v2.role_of`, from `state/v2.json`): PreToolUse `work_meter.py guard`;
PostToolUse `ctx_gauge.py gauge` (mail, the notice near the window's end at 907K and the end mark at 942K, below the
972K the API has accepted, the session's reading and production, the warmth marks); Stop `ctx_gauge.py stop` (a
session ends its turn only when its piece of work has ended, while it waits, or, for the knowledge base, the planner
between its events and a session the owner speaks to, always); PreCompact `ctx_gauge.py tripwire`; SessionStart sleeps ten seconds, which holds a
fork's first request until its tools have loaded.

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

The base and every session forked from it start lean: `session-flags` gives exactly the tools the sessions use
(Bash, Read, Edit, Write, Glob, Grep, Agent, ToolSearch, the task and background-task tools, WebFetch,
WebSearch), no MCP connectors and no skills list. `base.sh` (build, warm) and `v2.py` (fork) pass it; the flags
must be identical for a fork to read the base from cache. A bare `claude --bg --resume`, as a session is woken,
keeps them: a woken lean session listed the same tools and read its whole prefix from cache (verified 2026-09-19).

Verified 2026-09-19 through the real scripts with the real model, effort and flags: a small packed base built by
`base.sh max build` loaded through Bash, `check-load` accepted its transcript, and a fork started by the v1
launcher read it from cache on its first request, `cache_read=20062 cache_write=97` against a base context of
20,064.

`seal` accepts a packed load only when `base_pack.py check-load` finds every chunk, complete, in the main
transcript and the final `LOADED <pack id>` after them; a model's claim or a context size is not enough. Claude
Code stores a Bash result without its trailing newline, so the chunk envelopes are matched without it
(verified 2026-09-19 with a real two-chunk load; the earlier exact match found none). A packed base is not
extended: change the list and build again. `base.sh max build-files` is the older loader, in which the session
reads every listed file with the Read tool; its printed list carries the tier comments.

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
| `ctx_gauge.py` | context gauge (what the next request carries at least), the notices at 907K and 942K below the 972K the API has accepted, mail delivery, the Stop rule, warmth marks, the compaction tripwire |
| `session_row.py`, `session_fork_check.py` | a named session's listing row; whether a fork's first request read its origin from cache (logged by `v2.py`) |
| `efficiency.py` | how each session spent its window and what it produced, by role |
| `base.sh`, `base_pack.py`, `base-settings.json` | pack the list, load it chunk by chunk, check the load, seal, warm and drop the base; `pack_notation.py` holds the comparison notations; `base-bootstrap.txt` belongs to `build-files` |
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
  `cache_read=690406 cache_write=1823`. `base.sh extend` grows a sealed base under the same id (resume it bare:
  with flags a sealed session starts a copy).
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
- The Read tool: 25K tokens a call, 256KB a file, lines cut at 2,000 characters — `manifest.py list` names part
  sizes and substitutes folded copies. No tool result was ever cleared from context in sessions up to 955K.

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

Not yet exercised: v2 has not run live; everything above the base is tested only against a fake `claude`
(`fakes.py`). Unverified with real sessions: that a setting's task-list variable leaves a fork's cache hit intact
(the first fork of the knowledge base shows it in `state/v2.log`); resuming a sealed session other than a base; the
watchdog resuming a session after a usage-limit stop or a lost turn; `attach.sh` following a real role.
