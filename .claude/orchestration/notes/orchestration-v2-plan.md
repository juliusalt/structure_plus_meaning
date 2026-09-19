# Orchestration v2: a planner above one worker per task (plan of 2026-09-19)

The owner's decisions of 2026-09-19 (this session): a planner above the workers, which waits for their handoffs,
does not work on details and still knows enough to decide tasks precisely; one worker per task, the task planned so
that the reasoning it needs and its dependencies on other tasks are isolated in it and it finishes as its context
runs out; one worker at a time, consulting the planner on big decisions, the planner answering its questions (the
owner first set the workers at xhigh; since a fork runs at its base's effort, workers run at their base's effort, max
for now: see Worker); the native machinery integrated into planning as it is built, evaluated and improved while it is used,
without ever upgrading half-made machinery ahead of higher-level problems whose solution would make those upgrades
cheaper. The owner's further decisions: the planner's effort is max; workers commit and push validated tasks;
HANDOFF.md is the planner's state and holds everything a successor planner needs to understand the whole task
graph, so it is not kept small; the task graph uses Claude Code's tasks; nothing in this plan touches the base,
which is a separate topic.

Why: under v1 an implementer spent about 35 of 40 minutes generating, made 1.08 calls per request, read about 140K
tokens in slices, re-derived the high-level reasoning every rotation, and carried one batch across five rotations
(notes/efficiency-baseline.md); the first-message work protocol did not change its turns, because every fork carries
the implementer prompt of the base, whose stop hook and "never wait" leave polling as the only way to wait (impl-31:
half its requests during a probe were polls).

## Roles

**Planner** — one Opus session forked from the base, at effort max. It keeps the task graph in its Claude Code task
list and its reasoning about the graph in HANDOFF.md, forms and orders tasks, dispatches one worker at a time,
reviews each result, answers the worker's questions, and escalates to the owner through the ledger only what is the owner's. It is event-driven: it
ends its turn after every action and is woken by a worker's result or question, by the owner, or by the watchdog;
it never polls. It does not work on details: it reads theories only through their statements (a statement view:
digest.py's projection, proofs and code left out), task results, the plan, the ledger and git's record, never proof
text, logs or code bodies; the read guard enforces this. It knows what exists from the base (every theory name, the
founding theories' definitions and statements, the plan, the reasoning inventory, the owner's words). When its own
window nears the end it brings HANDOFF.md up to date and a successor planner is forked, which starts from the task
list and HANDOFF.md alone.

**Worker** — a fresh fork of a base per task. Design and investigation tasks run on the planner's base at max;
build tasks, which implement a written design, and fixes that run as new tasks run at high on an implementation base specialized
for implementing: more detail on what build tasks touch (the full statements of the working theories, the tools'
interfaces and the check workflow, the proof-engineering lessons) and less of the broad direction, which the brief
carries. Each base is forked only at its own effort: a top-level effort change invalidates the messages cache (API
documentation, prompt caching, invalidation hierarchy), and a base's whole load sits in messages, so a fork at
another effort would write it cold. What the implementation base holds is decided in the base topic; until it
exists, build tasks run on the present base at max. Its first message is the worker protocol and
the task's brief; it reads nothing to orient itself beyond the brief's inputs. It owns the task end to end: design
within the brief, write, prove, check. It never waits and never idles: checks run in the background and their
completion arrives in the running turn while it continues with what follows from the content being checked or with
the task's independent parts. When all that remains is the final job (the acceptance check, then commit and push),
it hands that job to the finalizer with the commit message it wrote, writes its result and ends; the next worker
starts at once. It consults the planner on a big decision (a new notion, a change of a statement other tasks use, a
choice between presentations, anything the brief marks as the planner's) and continues meanwhile with what does not
depend on the answer; when nothing independent is left it ends its turn waiting, and the planner's answer wakes the
same worker, which continues with its context intact. A question that is the owner's to decide is answered by the
planner with the best-reasoned provisional choice, stated with its basis in the ledger's open questions, and the work
continues on it (the owner's standing direction: never wait for the owner's authorization). Only when the answer is that the
task must be re-planned does the worker write a partial result and end. Its turn ends only with a result in form (done,
partial or blocked, with what remains and why) or while a recorded question to the planner is unanswered: the stop
hook refuses any other end. At the context notice it writes a partial result.

## Tasks

The graph is the planner's alone: a Claude Code task list (`CLAUDE_CODE_TASK_LIST_ID` set in the planner's settings;
stored in ~/.claude/tasks/<list>/) in which each task's description is its brief, `blockedBy` and `blocks` are its
dependencies, `owner` is the worker that takes it, `status` is pending, in progress or completed, and `metadata`
carries its kind, why it stands where it stands, its acceptance and where its result is. The planner creates and
updates the tasks itself (TaskCreate and TaskUpdate are in the forks' tool set). v2.py reads the task files
to start a worker on the task the planner queues (`v2.py next`) and marks it in progress with its owner; the planner
marks it completed once the finalizer has passed it; a successor planner receives the graph rendered from those files
in its first message, with HANDOFF.md.

A worker does not see the graph, which would invite it to reason about other tasks: it sees its own task, the brief
in its first message, and keeps that task's plan as its own session task list, created from the brief with
TaskCreate and updated as it changes the plan, so that its progress is visible in its session.

HANDOFF.md, the planner's state, holds what the task list does not: why the graph has its shape and order, the
decisions taken and pending with where they are written, what each finished task delivered, the open questions,
and what the planner was doing. It is as long as a successor planner needs to take the whole graph over from it;
its form is checked, its size is not capped.

The brief of a task (planner → worker): identifier and kind (design, build, integrate, investigate); what it serves
and why now; the deliverable (artifacts: files, statements, a written decision); the acceptance (a check); the
inputs (artifacts only, each named precisely: files and ranges, facts, decisions and where they are written);
what is decided and must be respected; the plan of the task, not one step but its logical course in order (the
steps, what each produces, what each rests on, where the design choices lie and what the planner already
reasoned about them); what the worker may decide itself and what it must bring to the planner; what may proceed
while checks run; a size estimate against one window (about 400K of room).

The plan is malleable: the worker follows it while it holds and changes it when the work shows a better course,
reordering, splitting, merging or replacing steps, and says in its result what it changed and why. A change that
alters the deliverable, a decided statement, or what other tasks rely on is a big decision and goes to the planner
first.

Isolation: a task depends on artifacts, never on a predecessor's reasoning; a conceptual decision is a design task
whose deliverable is the decision written into the plan or DECISIONS.md, and the tasks that use it take it as input.
A task that returns partial is split by the planner into tasks over the artifacts that exist.

The result of a task (worker → planner, `.build/tasks/<id>/result.md`): status (done, partial, blocked); the
artifacts and statements produced; the decisions made, with reasons; what remains, as artifacts; the commit;
questions; the plan as it was actually followed, with the changes and their reasons. The planner accepts it,
re-plans, or asks, and learns from the changes how to plan the next tasks. A partial result means the task did not
fit its window: the planner splits it; effort does not enter.

## Production, enforced

Production is a change to one of the task's deliverables (the files its brief names and its draft directory) that
adds or changes content: in a theory, a definition, statement, locale or proof added or changed (the digest's command
parser; a changed proof counts, whitespace or a comment does not); in a deliverable document, some forty words added
or rewritten; in code, some five non-blank, non-comment lines. Scratch probes, logs and the handoff never count.
Between two production events the worker may take at most about four rounds (model requests) and read at most about
20K tokens, the brief's named inputs not counting on their first read; past either limit, reads, searches and check
runs are refused, and what remains is to produce, to ask the planner, or to write a partial or blocked result that
says why, which the planner reviews; there is no other way out, and a pattern of such results shows in each task's
measures. A check that fails again with the
same failure (theory, command and error) after a fix, three times in a row, is refused: the fixes are not working and
the obstruction goes to the planner. Failures that move (further on, a different command, fewer of them) are progress
and unlimited. When a check reports several failures, they are fixed together before the next check. Sleeping, wait loops and progress
reads of the worker's own running jobs are refused. The limits are
calibrated by replaying the recorded implementer sessions before they are deployed, and are stated in the worker's
first message as they are enforced.

Order: the owner's latest directions and the ledger; dependency; uncertainty first; then size. Each task says why it
stands where it stands; choices outside the owner's directions are marked provisional and recorded as residuals.

## The native machinery (goal 4)

The planner uses the loop's machinery wherever it can already carry planning, and only there: the task graph presented as native
problems with their dependencies, readiness evaluated by the native readiness program (Development_Native_Readiness,
committed), the next task selected as the loop's selection question selects. Where the machinery cannot yet express
a planning choice, the planner decides and records the choice as a residual. Every gap met this way becomes a task,
ordered like every other task: a gap in half-made machinery waits behind the higher-level problems whose solution
makes filling it cheaper, and the planner never turns aside to upgrade machinery for its own convenience. How the
task graph is presented to the loop is such a task, placed where the order puts it.

## Harness

- **Base**: not part of this plan (a separate topic). Until it changes, every fork inherits the implementer prompt
  of the present base; each role's first message therefore names the parts of that prompt that do not apply to it
  (rotation, the stop hook as described there, the handoff), and the hooks behave exactly as the role's protocol
  says, so that what the fork believes about the harness is true. A role-neutral base prompt is the base topic's.
- **Launchers**: v2.py (fork of the base with the role's protocol and, for a worker, its brief; a background
  cache check; the result's form); the planner started and rotated by v2.py and the watchdog.
- **Messages**: mailboxes (state/mail/): a busy addressee receives its mail through its hooks at its next tool call
  or when its turn would end, an idle one is woken with it (stop, then a bare resume). SendMessage is not in the
  forks' tool set, which is part of the base's cached prefix.
- **Finalizer**: a mechanical job, no model: it runs a task's acceptance check, commits the task's files with the
  worker's message and pushes on success, and on failure records the task for repair and wakes the planner.
- **Quick fixes in parallel**: a worker stays, idle, after its result until the finalizer has passed its task, and is
  stopped then. When the finalizer reports a failure that the planner judges quick and simple (one failing proof with
  a clear error, say), the failure wakes that same worker, which has the whole context of what it produced and keeps
  its base and effort (a design worker stays on the planner's base at max); it runs beside the producing worker under
  a small hard budget (about fifteen minutes and a few rounds). Only when it can no longer take the fix (its window
  spent, its session gone) does the fix become a new task for a fixer on the implementation base at high. At most one
  fix runs at a time. A fix that outgrows its budget stops with a partial result and becomes an ordinary task in the
  queue, so that in effect never more than one worker runs constantly. Anything else goes into the queue directly.
- **Always one worker producing**: the planner keeps at least one task ready ahead; when a worker ends, the next is
  started at once on the next ready task, and the planner reviews the finished result meanwhile, messaging the
  running worker if the review changes its task.
- **Watchdog**: supervises the planner and the worker; wakes the planner on a result, a partial result, a vanished
  worker; wakes either after a usage-limit stop; rotates the planner at its notice; never rotates a worker.
- **Hooks**: the gauge by role (worker: write the result, partial if need be, and end; planner: write the state and
  end); the stop hook lets a worker end its turn only with its result in form or while its recorded question to the
  planner is unanswered, and lets the planner end its turn always; the read guard refuses the planner proof text (theory sources through the
  statement view only) and keeps the worker's reading rules; the production meter stays for workers.
- **Measure**: efficiency.py by role, against the v1 baseline.

## Steps

0. Settled without probe bases: a fork at another effort than its base cannot read the base from cache (the API
   documentation: a top-level effort change invalidates the messages cache), so each base is forked only at its own
   effort; a task list named in a session's settings is the one its TaskCreate writes (verified with a probe
   session; whether it leaves a fork's cached prefix intact shows at the first planner's start); SendMessage is not
   in the forks' tool set, hence mailboxes.
1. Protocols: planner-protocol.md, worker-protocol.md, the brief and result forms. (A role-neutral base prompt
   belongs to the base topic.)
2. Harness: v2.py and finalize.py, watchdog and hooks by role, the planner's statement view and guard,
   efficiency by role; tests without sessions (fakes.py).
3. Migration: impl-31's HANDOFF queue (T2–T8) becomes the planner's initial graph; the planner's first act is to
   re-form it into isolated tasks by these rules, then dispatch the first.
4. A first live task, measured; then continuous operation, measured after every few tasks.

## Next: roles, bases, consultation, warmth (2026-09-19; decided and built, not yet run live)

The owner's directions of 2026-09-19, in order: more roles than planner and worker (implementer, fixer, designer,
investigator, task designer, reviewer); the planner spending its context as slowly as possible, serving mainly as the
knowledge base of the other roles and the integrator of work and high-level decisions, not reviewing finalizations
itself; a third base at xhigh between the planner's and the implementers', each base tailored to its roles; sessions
consulting the author of what they work on, never waking a session whose cache is cold. Then: the planner split into a
knowledge base and a planner; the reviewer also finding further tasks and efficiency problems in the new work; an
implementer that meets an efficiency problem escalating it and waiting, the problem becoming a task that is fixed
before the implementer continues, so that it neither fixes locally what needs higher-level reasoning and planning nor
is bogged down waiting for tools; batching made structural in the task definitions rather than expected of the
workers; the fixer and the implementer two roles.

**Knowledge base and planner.** The knowledge base is one session forked from the planner's base that never works:
its context is the base plus what has been integrated into it (the decisions with their reasons, a summary of what each
task delivered, the owner's new directions, why the graph has its shape). It is sealed between integrations and
answers nothing itself: every question to it is answered by a fork of it, which reads its context from cache and is
discarded, so questions never grow it. It grows only by integration: short notes appended by a bare resume, one at a
time. When its window fills it is rebuilt from the base and the written decision register. The planner decides: the
graph, the order, the high-level decisions. Proposed: a planning episode is a fork of the knowledge base, started on a
batch of events (verdicts, escalations, the owner's words), which updates the graph, writes its decisions and the
integration notes, and ends; its deliberation is discarded, and what it decided persists in the task list, the
decision register and the knowledge base. (The alternative, a long-lived planner consulting the knowledge base, keeps
its reasoning between events but spends its window on it.)

**Roles and bases.** A role's effort is its base's (a fork at another effort writes the base cold), so choosing the
effort of a task is choosing what its session forks.

| Role | Does | Forks, effort |
|---|---|---|
| knowledge base | the integrated knowledge; answers through forks of itself | planner base, max |
| planner | episodes on batched events: graph, order, high-level decisions, integration | knowledge base, max |
| designer | a conceptual decision, written into the plan or DECISIONS.md | knowledge base, max |
| task designer | a planner's task made into briefs with their read and check batches | middle base, xhigh |
| investigator | measures and finds out, efficiency problems included; findings written | middle base, xhigh |
| reviewer | a finished task against its brief, its decided statements and the principles: the verdict, a summary of about 150 words, and follow-ups (tasks the work shows are needed, efficiency problems in it) proposed to the planner | middle base, xhigh |
| implementer | a written design built: theories, proofs, code | implementation base, high |
| fixer | a failed check or a rejected review repaired, nothing designed, under a budget, when the implementer cannot take it | implementation base, high |

What the middle and implementation bases hold is the base topic's; until they exist every role forks the present
base at max.

**Batching in the task.** A brief stays at the level its task designer knows without reading: each step's purpose and
output, the sources it rests on by name (theories, notions, facts, decisions, as the task designer holds them from its
base; the statements of a few facts it is unsure of it looks up), the decisions taken, and where the checks fall (one
check after a group of steps). Which lines, which lemmas to reuse, how to prove are the implementer's to find. The
structure makes the batching: a step opens with one gather (`v2.py step ID N`), a request in which the implementer
issues every read the step needs, the named sources free; after it the step produces, and further reads count against
the limits (3 requests, 20K tokens between productions, told after every read). A check runs at the brief's check
points and after a repair, not after every edit. (Owner, 2026-09-19: at the level of files and ranges the brief would
be redundant, since writing it would take all the reading; it must leave the details to the implementer.)

**Efficiency problems.** An implementer does not optimize what its brief does not name. A check or run that exceeds
the time its brief expects, or a cost the step cannot bear, it escalates (`v2.py escalate ID --efficiency "..."`:
what is slow, measured, where) and ends its turn waiting: the stop hook accepts that while the escalation is open. The
planner makes the problem a task (an investigator measures, a designer or implementer fixes), ordered before the
rest of the waiting task; the waiting implementer is sealed and held warm, and woken with the fix once it has landed,
its context intact. If the wait outlasts the holding horizon, it records a partial result instead. The reviewer's
efficiency follow-ups become tasks the same way.

**Consultation by fork.** A knowledge-bearing session (the knowledge base, a designer, a task designer, a reviewer)
answers questions through forks of itself once it is sealed: its context stays as it is, it is not interrupted, and
questions are answered in parallel. An answer that amounts to a new decision is recorded with its author and goes to
the planner's next batch. `v2.py ask ID --to kb|planner|designer|task-designer|reviewer "..."` routes by the task's
relations: the author of its design input, the task designer that briefed it, the reviewer that judged it. Forks of a
sealed session, extending a sealed session by a bare resume, and keeping it warm with forked pings are the verified
mechanisms of the bases (README, 2026-09-18).

**Warmth.** A session whose cache has expired is never woken or forked. A finished knowledge-bearing session is
sealed and held warm while something may consult it: while tasks that take its artifacts as inputs are queued or
running, or an implementer waits on it, and at most for a bounded horizon. The daemon pings a held session as it pings
a base (a throwaway fork before the hour is out: about 0.1 of its context per hour, against about 2.0 for one cold
resume, so holding pays when a consultation within the hour is more likely than one in twenty) and releases it when
nothing refers to it. A question for a released session goes to a fresh fork of its role's base with its written
artifacts as inputs, or to the knowledge base. The planner keeps the consulted close in time: a task that may
consult an author follows that author's task soon after.

**The finalization, without cycles.** The finalizer's check passes, then the reviewer judges, then the commit and
push. A review is one complete verdict: every blocking finding at once, each resting on the brief (its acceptance,
its decided statements) or on a principle; what does not block is a follow-up, proposed to the planner as a task, never
a rejection. A rejection goes to the kept implementer (or a fixer when it cannot take it) for one fix round; the
re-review judges the listed findings and whatever the fix itself broke, and adds nothing else. A second rejection does
not go back: the planner decides between accepting with follow-ups, a fixer's task and re-planning (a brief that
asked for the wrong thing). The finalizer's check likewise gets one quick fix; a second failure is the planner's.
(Owner, 2026-09-19: the rejection may not fall into a loop of something bad, a fix, something bad, a fix.)

**Parallel roles.** One implementer produces at a time; beside it at most one task designer briefs the next task and
at most one reviewer judges the last, each bounded by its one task, and a fixer as before. (This relaxes "one worker at
a time"; the owner's decision.)

**The owner's decisions of 2026-09-19 on this section.** Planning episodes are forks of the knowledge base: every
self-contained piece of work is a fork (a planning episode, a brief, a review, a consultation, a ping); a resume only
continues the same piece of work (a quick fix, a re-review, an implementer woken after an efficiency fix). Beside the
producing session at most one supporting session runs: a task designer or a reviewer, not both. A waiting implementer
is held warm for at most 3 hours, then records a partial result.

**Batching for every role.** Every role that works reads, so the same rules hold for all of them: production is a
change to the role's own deliverable (the implementer's theories and code, the fixer's repair, the designer's decision,
the investigator's findings, the task designer's briefs, the reviewer's verdict, the planning episode's graph and
notes, a consultation's reply); between two productions at most 3 requests and 20K tokens of reading, told after every
read; and each unit of work opens with one gather, `v2.py step ID N SOURCE...`: the session names every source its
step needs (files and ranges, facts, documents) and the harness prints them in one response, free of the limits, once
the previous step has produced. The session decides what to read; the structure decides that it is read at once. For
the planner, the task designer and the knowledge base's consultations the gather serves statements only, which keeps
their reading at their level.

**Built (2026-09-19, session f4318413), tested against a fake `claude` only.** `v2.py` (roles, slots, the knowledge
base, planning episodes, the dispatch, consultations, warmth, every command), `protocols/` (a first message per role
from shared parts), `finalize.py` (check, then commit after the verdict), `watchdog.py` (live sessions, what is held
warm, finishing, the dispatch), `work_meter.py` and `ctx_gauge.py` by role, `health.py`, `attach.sh`, `talk.sh`; README
rewritten. To be seen live: that a fork of the knowledge base (planner-settings.json's task-list variable) reads its
cache; that a sealed session other than a base resumes and is pinged warm as a base is; the first episode's re-forming
of impl-31's work order.

**The knowledge base's limit and rebuild (the owner, 2026-09-19: "what happens when knowledge base context runs out
or becomes too small for forked planners to operate on"; "the base rebuild should be done by me").** The limit is its
forks' room, not its window: a fork starts with its whole context, so it is rebuilt before it leaves a planning
episode 150K or a consultation 60K before the notice (757K); a designer forks it while it leaves 300K, the planner's
base otherwise. A rebuild loads HANDOFF.md, not the notes history, so HANDOFF.md holds, condensed, whatever must
outlast a knowledge base. When a fresh one loads within 50K of its limit, the planner is asked to condense HANDOFF.md
and the owner is told a base rebuild is due; the base rebuild is the owner's. An episode at its window's end writes
what it has not handled under `## Now`, which every episode is shown. (Built; the rooms are estimates, to be measured.)

**Every piece of work planned by the same machinery (the owner, 2026-09-19: "if the work that needs to be done in a
single task by the role is big enough then maybe it itself should get a planned task graph rather than go without a
plan"; "I mean produced by the same machinery that produces implementer tasks").** Every piece of work beyond a
question is a task of the graph with a brief in form, sized to one window: the kinds design, investigate, build, fix,
brief and review. The planner writes design and investigation tasks and brief tasks (the plan of a detailing); a task
designer carries a brief task out by writing the build and fix tasks and, for each, its review tasks (the review's
plan: what to check per step, the decided statements, the principles most at risk), a review beyond one window being
several review tasks; a task is committed only when all its review tasks accept. Only consultations and planning
episodes stay outside, being small and event-driven; a question too big for a consultation becomes a task. A brief's
Size is an estimate in tokens of work, and a task beyond one window is refused and split. (Built.)

**The designer's room (the owner, 2026-09-19).** A single design decision fits in 230K: a design task is at most
that, and a designer forks the knowledge base while it leaves 230K, the planner's base otherwise, reading HANDOFF.md
in its first gather ("the most recent details might not be the most important and can be read off handoff"). The
knowledge base is not condensed early: it is rebuilt when it would leave a planning episode or a consultation too
little room (757K). (An intermediate version, a 200K designer with the knowledge base condensed and rebuilt to keep
it forkable, was withdrawn by the owner.)

**No cap on design tasks (the owner, 2026-09-19, session 212840df: "design tasks are still capped at 230K - no longer
do we need a cap on this").** The 230K came from designers forking the knowledge base; since they fork the middle base,
a design task has the room its base leaves, like every other kind. (Built: `v2.room_of`, the brief form, the test.)

**Review before the first run (the owner, 2026-09-19, session 212840df: "review the orchestration try to find any
issues before we start everything"; "it is allowed for more than one consultation to work as it makes sense").**
Found and fixed, each with a test: a final check saw the whole working tree, other tasks' uncommitted work included (an
`--advance-base` check could take it into the base): the working tree now has one owner at a time, the task whose
finalization is in flight (other sessions write only under .build/ meanwhile and are told when it is free) and
otherwise the producing task, finalizations run one at a time, every change is attributed to its task, no session
changes the index or the history, and a task that leaves unfinished has its changes set aside once its session has
stopped (a first fix set other tasks' changes aside during each check; the owner asked whether that was isolated from
the running workers, and it was not: a producer's background jobs and indirect reads, and a second finalization's
review and commit, would have met a changed tree; it was replaced before anything ran); a session waiting on its question was never
held warm and, gone cold, kept its slot for ever: it is now `waiting`, held and given back when cold or unanswered; the
watchdog emptied a mailbox before a resume that could fail; it gave a finalizer up at 70 minutes while the finalizer may
wait an hour for Isabelle and check for another, and a late report then overwrote the planner's handling; consultations
ran one at a time, and one waiting for the knowledge base held up every other; the planner's `queue` dropped tasks a
task designer queued during the episode; the graph in first messages grew with every completed task; the finalizer's
git calls could hang (push) or fail on another process's index lock, and one failing part stopped the whole watchdog
every minute; the knowledge base was rebuilt only after it had outgrown its forks' room, not when its base was rebuilt, and an episode could fork it
before the last notes were integrated; the state every hook reads grew without bound; the watchdog and the dispatch
could act on one session at once; HANDOFF.md was committed by no one; commands of the planner and the task designer
were open to every session. Open: the Isabelle limit is checked before a run starts (two runs starting together can
exceed it); a parked session past its hold writes its partial result beside the producing one; concurrent TaskCreate by
a planning episode and a task designer relies on Claude Code's own locking (unverified live).

**The first episode (the owner, 2026-09-19, session 212840df: "make a custom prompt asking it to build a new task graph
where the commit history that shows the previous repository development together with the handoff can inform the new
task graph but it may choose to change it to something else").** `protocols/_first.md`, rendered into the first
planning episode's message while there is no task graph and no episode has ended: build the graph anew from the plan,
DECISIONS.md and the owner's words, informed by the commit history (messages and file lists) and HANDOFF.md's old work
order, which do not bind it; write HANDOFF.md anew saying where the graph departs from the old queue; the uncommitted
changes no task owns are listed, to be given to the task they belong to or left to the owner.

**Performance problems have their channel (the owner, 2026-09-19, session 212840df: "the one thing I want you to add to
the my original comment is regarding fixing performance issues as that now has proper channel through which that needs
to be done rather than doing it themselves they send a message and wait to be woken up").** `library-prompt.md` quotes
the standing goal as it stands and adds, as the owner's addition of that day, that the session meeting a performance
problem does not fix it itself or wait on it: a producing session escalates it (`v2.py escalate --efficiency`) and is
woken when the fix has landed, any other reports it to the planner; the fix is a task like any other.

**No producing session waits holding its slot (the owner, the same day: "It only waits if there is nothing else to do
that does not require fixing the problem and in general probably it should not even wait then as it can at that point
wait for the slow tool if there is nothing else to do in takes fixing takes longer than just using the tool"; "what we
need to enforce however is that if there is nothing productive that it can do and it must wait then it must become
parked so that another worker can then be started to do productive work").** Reporting a performance problem
(`v2.py escalate --efficiency`) no longer parks: the session goes on. With nothing productive left a producing session
parks (`v2.py park run|fix|tree|answer`): for its own run, which keeps the working tree while it reads the task's changes
and whose early completion wakes the session only to be refused until the harness resumes it; for a fix; for the working
tree; for an answer. The slot goes to the next task; the parked task is resumed first when its wait is over and the slot
and tree are free. The Stop hook lets a producing session end its turn only with its result recorded or parked.

**The owner's words reach the planner mechanically (the owner, the same day: "how do i now pass my directions to which
role or what mechanism?").** A UserPromptSubmit hook on every orchestrated session (`ctx_gauge.py owner`) records what
the owner types, verbatim and dated with the session and task, in the owner ledger, and (but in a planning episode) makes
it an event for the next planning episode; before, a session was only asked to record it, and nothing told the planner.
The channels: `talk.sh` for what is done, in which order and why; `attach.sh ROLE` for a session's own piece of work;
what the bases load for what holds always.
