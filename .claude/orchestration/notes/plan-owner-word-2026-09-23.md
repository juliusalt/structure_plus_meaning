# The owner's word of 2026-09-23 morning: the tasks and the plan

The owner (verbatim, in the conversation): "Regarding the proposals, C7 - yes, C10 - yes, C15 - yes if it can be done
in a way where information quality statys the same or increases." Then: "Ruse the batch check's build, design and
build the per-role reasoning layer which I will then either activateor not(and in general will test rather than
speculate) FOr the per-session pass do not go through each session go through the last session of each role. Make a
task list and a plan for everything that you need to do now, then implement the coherent and adequate changes. Do not
stop until you implement them."

Working rules as before (notes/plan-orchestrator-concepts.md): nothing committed; each change built in the dev copy,
tested, mutation-checked, the suite run, then deployed with a backup and an entry in notes/v2-build-handoff.md.

## Tasks

Status: `[ ]` open, `[~]` in progress, `[x]` done.

1. [x] **The last session of each role, read for the harness's problems and for batching** — implement-192,
   fix-279, review-251, design-258, investigate-254, brief-230, plan-47, kb-13, ask-q33. Per session: every request,
   what it read and wrote and why; each place where the harness refused, misled, delayed or cost a request; each
   place where reads or writes could have been one request and what kept them apart. Findings written below.
2. [x] **The fixes those findings call for**, each with its test and mutation case.
3. [x] **C10, the landing reuses the batch check's build.** See the design below.
4. [x] **C7, the reviewer corrects words.** A reviewer who finds a commit message, a result or a row misstating the
   work writes the corrected text and accepts, rather than rejecting for words.
5. [x] **C15, a follow-up's brief begun by the harness**, only where information quality stays or rises.
6. [x] **The per-role reasoning layer**, behind a switch the owner turns on to test.
7. [x] **Coherence**: protocols, README, the concepts plan's state, run-report measures for each new mechanism, the
   whole suite, a full mutation run, the handoff.

## Designs

**C10 — one heavy check where the content allows it.** Measured: both the batch check (a median 186 s of proof,
2.88 h on 09-22's afternoon) and the landing train's check (216 s, 2.58 h) spend nearly all their time proving the
members' theories; recipes and host tests take 11 s. Isabelle cannot merge two heaps, so a batch's build can stand in
for the landing's exactly when the landing checks the same content: nothing landed in between and the members are the
same. Then the batch's proof verified what lands, and its heap — kept — becomes the next base by `adopt`, as the
train's own heap would have. Pieces: (a) `incremental_check.py check --keep-heap`: the rebuilt theories' heap is
stored, as `--advance-base` stores it, but not selected; the report says `kept_context`. (b) A batch keeps its heap,
its output in the lasting store (.build/bases/, where the trains' are, since heaps are path-bound), and records the
content it checked by a key: the tree its integration branch holds, planning documents aside (HANDOFF.md,
PLANNING_LOG.md, which the harness commits with landings and no check reads). (c) A train whose tree has that key,
on the base the batch stood on, lands on the batch's build: no check, the batch's heap adopted, its receipts
retained, the lineage recorded, the commit's Validation paragraph naming the batch's check of the same content.
Otherwise the train checks as now. (d) A base part nobody adopts keeps its reports and loses its heap and bulk after
BASE_KEEP. The hit rate rises with C9 on (the review beside the check shortens the interval in which main moves).
run-report counts landings that reused their batch's build.

**C7 — the reviewer corrects words.** About 12 of 31 rejections were a commit message, a result or a row misstating
the work, each a fix round (about 1.7M and 45 minutes). The reviewer may write, in the reviewed task's own files:
its commit message and its result (.build/tasks/ID/commit.md, result.md), and by `=== row` the rows of the theories
the task changed; nothing else — never a theory, code or a decision entry. Its verdict says `Verdict: accept` with a
`## Corrected` section naming each file it corrected and why; the harness refuses a verdict whose `## Corrected`
names a file the reviewer may not write, and records the corrections with the verdict; a finding about a theory,
code or a decision stays a rejection. The finalizer commits as now (the message is read at commit time; THEORY_MAP.md
is among the task's files when it changed rows).

**C15 — a follow-up's brief begun by the harness.** `v2.py follow-up TASK ITEM...` writes a draft brief, in form,
from the review of TASK: its Kind (fix), Serves (the review and its follow-ups by number), the follow-ups' text
verbatim, the files and facts they name exactly as they name them, Inputs (the review file and those names),
Acceptance (the repository's check), and `continues: TASK` in its metadata when C13 is on; Plan, Decided and Size
are left marked for the planner, who completes and places it. Quality: every line the harness writes is a copy of
what the review says or a name it gives, nothing summarized; the form check refuses a draft whose marked parts were
left unfilled.

**The per-role reasoning layer (behind `state/role-layers`, off).** A role's forks start from a layer made for the
role: a fork of the role's base as its forks fork it now (the delta, or the layer), whose one message holds the
role's protocol and what the run has shown about the role — the blocking findings its tasks' reviews made lately,
the refusals and notes the harness gave its sessions most often, its measured request pattern — and asks it to
reason, once for every session of the role, how to do the role's work well here, and to write its conclusions as a
short list of practices with the evidence each answers. Its reasoning and its list stand in the cached prefix of
every fork of the role. Built on demand by the dispatch when the switch is on, in the background; until it is ready,
the role forks its base as now. Rebuilt when its base is rebuilt, when it has gone cold, or when it is older than
ROLE_LAYER_AGE and its delta has moved; a fork of it is told what changed since the load it holds (stale_of follows
origins). The owner tests it: run-report sets the sessions of each role that forked a role layer beside those that
did not (requests, before the first change, rejections, cost).

## Findings of the per-session pass

Read: implement-192 (5 requests), fix-279 (12), review-251 (7), design-258 (10), investigate-254 (16), brief-230 (11),
plan-47 (47), kb-13 (2), ask-q33 (10) — every request, its calls, what the harness answered, its notes and refusals.

Harness problems still standing, each with its session:
1. **The small-read note miscounts** (implement-192, request 3: "your last request read 3,966 bytes" after a request
   that read about 33K in three calls; fix-279, request 9: a probe's 831 bytes counted as a read). It reads the bytes
   the post-hook recorded per batch, which misses a call whose batch it could not place, and it counts every call,
   a probe's output included. To read the previous request's reading calls and their results from the transcript,
   and to say nothing of a request that did more than read.
2. **A batched `ask` refuses a group that names its target bare** (implement-192: `ask --to planner "…" -- planner
   "…"` asked the first question, refused the second, and exited 1). A group takes a bare target word, or the
   previous group's.
3. **A queued measurement does not say what to do meanwhile** (fix-279 tried `v2.py end`, refused, a request lost):
   to say "continue with what needs no machine; with nothing left, park (`v2.py park machine`)".
4. **A done result refused for its repository deliverables does not say which are unwritten**, and names the old
   hand-over form (investigate-254: two refusals, a question and five minutes); the finalizer's refusal of a `.build/`
   file does not say that the task's folder is its record, never committed. To name each deliverable still unwritten,
   give `v2.py finalize ID`, and explain `.build/`.
5. **An append to PLANNING_LOG.md by SEARCH/REPLACE is refused when its text recurs** (plan-47, request 37: the whole
   batch — its mail, HANDOFF.md, the log — refused for one ambiguous SEARCH, redone in the next request). A change verb
   `=== append PATH` appends its text at the end: nothing to match.
6. **"One change in this call" is noise for a single write of a session's own record** — a verdict, a result, a note,
   a measurement, under .build/ (fifteen times in the nine sessions, never followed by a batched change). Kept for
   edits of the repository's files.

Batching the harness could do for the sessions:
7. **A brief's decision entries by their lines** (design-258: three of its nine reading requests found the entries
   its brief names by grepping headings, then read them): the first message gives each DECISIONS.md entry a brief names
   by its heading, with its line range, for the first batch to read.
8. **A re-review's first read with its resume** (review-251, request 6: result and log read again): the message that
   resumes a reviewer after a fix carries the result, the check's log and the probes, as a first review's does.

Already repaired by the harness on 09-22 evening, met by these sessions before: `tell --file` delivered as text
(brief-230), a planner's plan file refused to a statements reader (brief-230), the result refusal naming its files.
Measurement holds blocking every other run (implement-192, fix-279: task 278's 30-minute hold): C14, behind its switch.

## As built (each deployment in notes/v2-build-handoff.md: C10 08:31, C7 08:40, C15 08:46, the role layer 09:05)

**C7** differs from the design in one place, on the data: every reviewer since 09-19 wrote diffs, row lists and
merge simulations under the reviewed task's folder (and in rid-named folders when reviews had ids of their own), and
scratch under $TMPDIR. So a reviewer writes its own record and the reviewed task's `.build/tasks/ID/` whole — but not
the harness's records there (finalize.json, brief.json) — and anything outside the repository; in the repository
nothing else but a THEORY_MAP.md row by `=== row` of a theory the task changed, when the task hands the map over.
`## Corrected` names files in backticks; a word of the file form other than commit.md, result.md, THEORY_MAP.md is
refused. The guard closes what stood open before: a reviewer works in the reviewed task's tree, which no guard kept it
from writing.

**C15** as designed, and: the follow-ups are copied quoted (`> `), so that a line of them reading like a field of the
form is not taken for one, under a new optional form field `From the review:`; the names are the backticked ones
with `_`, `.` or `/` (review-272's `exact`, `obtain`, `unfold` are words) and theories named bare that the tree holds;
`--kind` for a follow-up that is not a fix. Found on the way, a gap of C13: `v2.py edit` could not set `"continues"`,
and the planner places tasks by edits — it can now (create and rewrite, checked to name a task).

**The role layer** as designed, with these choices. Its evidence is read from the transcripts (role_evidence.py), not
from a log the harness would have had to start keeping: the rejections' findings come from the verdict's own change
in each reviewer's transcript (the review file is overwritten by a re-review, and is read only when it still says
reject). The measured request pattern is requests, requests before the first change, and cost. The harness's notes
exclude its counters (the read budget, "Production recorded") and mail, which drowned the rest (116 and 52 of the
implementers' last 12 sessions' notes). The layer is held warm while its role is wanted and let go after two hours
without — its pings are its largest running cost. Its reply ends its turn (the Stop rule would have refused it, as it
refuses any role but the knowledge base and the planner). Its forks count in the delta's carried cost. Built only on
demand, and never in the dispatch: the evidence is read in the background and the layer forked at the next pass.
