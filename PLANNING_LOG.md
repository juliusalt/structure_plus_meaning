# Planning log

What was done and how: the course the work took, what was tried, what was abandoned and why, what a task turned out
to cost. The planner appends to it as work lands and never rewrites it.

This is not a state and nothing plans from it. `HANDOFF.md` is the state a planner needs to act now and is held by
every knowledge base; this file is held by no base, read by no role, and bounded by nothing. It is the record — for
the owner, and for whoever comes after.

Decisions of the development itself belong in `DECISIONS.md`, what a theory offers for reuse in its row of
`THEORY_MAP.md`, and what a task must respect in that task's brief. What is left is this.

---

## 2026-09-20 — what HANDOFF.md had become, kept whole

Everything below stood in HANDOFF.md up to this date. It had grown from 6,486 characters to 81,482 in a day, four fifths of it a record of what had been done rather than what a planner needed to act on, and the owner moved it here: it is a log, so it lives in the log. Nothing of it is lost, nothing of it is loaded by a base any more, and the state it left behind is written afresh by the planner that comes next.

The sections below are as they stood; their `##` headings are the planner-state form of the time.

---

# Handoff

The history of every rotation is in git and in `.build/handoff-archive/` (the last long form:
`HANDOFF-impl30-20260919.md`); what is settled is in native_control_plan.md, DECISIONS.md and THEORY_MAP.md. The
owner's directions and open questions are in `.claude/orchestration/owner-ledger.md`. Each batch records what it
settles once, where it is read (DEVELOPMENT_WORKFLOW.md): its decisions as an entry of DECISIONS.md, a theory's reuse
in its THEORY_MAP.md row, the evidence also in its commit message, what remains in the graph; the plan changes only
with its structure, the stages' standing or the direction of the work.

## Graph

Three lines, and the owner's two directions of 2026-09-19 order them.

**The engine line (5 committed, 7, 8).** T2 measured a native definition whose argument is a whole state: it
re-verifies the context every call carries — the machinery's reach at 171.8 s natively against 0.99 s in HOL
(DECISIONS.md, "A native definition over a state re-verifies its context in every call"). Every remaining notion of
the Q7 order is a definition of that shape, so the cost is on the critical path of the owner's direction that native
definitions are normative, and of condition 5a; the owner's standing direction is that such a cost is fixed now at its
cause. #5 delivered the first of the two decided refinements (constructed applications) and its own check accepted it;
its session was then lost before the handover, the harness finalized the batch from its artifacts by the owner's
decision (**#18** dropped), review-6 accepted the work and rejected three phrase-level claims of its two documents,
and **#19** committed what was left as `6227819a`; **#6**, its review, is closed (Decisions: a review task is
alive only while its subject can still commit). What it leaves is measured, and is what #7 must close: the
machinery's reach **44.6 s against a bound of 5 s**, the seeded state's 0.417 s against 0.2 (seed evaluation 0.403 s
from 1.224). #7 is the second refinement (evaluate over the positions of the demanded calls), and review-6 added what
it must attribute first: the refinement just landed removes formation traversals and not pattern traversals, while
`finite_interface_fits` scans the interface table with `fBex` for every instantiated premise of every clause of every
demanded call — a linear scan that is itself an index candidate under #4's notion (carrier the interface table, key
the definition site). Whether the positions renaming or that lookup dominates is a measurement, and it was #7's first
step rather than an assumption; its brief predates the finding, so the finding is in its metadata. **The measurement
is in, and the line is closed but for #8.** #7's refinement is proved and loading, its contract exact on the whole
domain with the renaming's formedness premise established for every program rule table rather than worked around, and
its claimed run — the machine held for the whole of it, probe certified, no profiler in it, each side evaluated once
and the two answers compared directly and equal — puts the machinery's reach at **4.35 s against a bound of five**,
about 5.8 s scaled to the machine that recorded the 43.812 s keyed baseline (the run's own 1.33x), and the seed's at
0.074 s against 0.2. The in-run ratios, **9.3x** at the machinery's scale and 6.2x at the seed's, are the
machine-independent part: the two refinements together took 44.6 s to about 5, a factor of ten. The earlier interim
figure is superseded; it was measured beside another worker's run and only its ratio was ever recorded. What the
measurement leaves is the line's honest bound, and it is stage 2's open cost item in place of the old one: one
judgment of the verdict is about four reaches, so a *stage* of 224 answer states is still of the order of 3,900 s
against 22.4 s for the HOL stage. #7 therefore makes no attribution run, two of #8's three questions are decided
(Decisions), and #8 judges the contract's premises, the measurement's provenance and word equality. **#49** then
brings the plan's two standing sections current, which is what a line closing is for.

**The Q7 line (16, 11, 14, 10, then the further builds).** #3 designed the verdict of a kind as a native definition
over structural rows and is committed; what the verdict needs of the paused structural-Isabelle-state work is the
first step of its own build. #9 designed the development notions themselves as structure — the octet direction's
task 3, promoted because three lines need it — and found them one notion: **a row at a locus of the development's
published state**, the locus a path, a kind and a role prefixes of it, origin and authority families of citations.
Nothing builds that presentation, so **#16** briefed it, and its ten tasks are in the graph and queued: **#22–#31**,
five builds each with its review — the locus (a path of role, kind and the subject's key), the presentation relation
for development rows, the request at a locus as one search rather than a name lookup, the row presenters with their
injectivity, and the retirement of the six tagged presentations with the recipe words re-established once, the one
task of the line whose check cannot accept by word equality. Every definition of that line takes the state's
constant-key assignment as a parameter with an injectivity premise, so it is independent of the verdict's line
(Decisions). #11 briefs the verdict's build from #3's entry, whose first step is the state's own
rows; of the tasks it creates only those ranging over the *development* rows — a request's subject and support, an
answer at a locus — are blocked by #30, the rest being over the state's own rows, which #9's entry consumes
unchanged. #14 restates a native question's candidates over the locus #9 assigns — design-9 found the last read of octets
as structure on the loop's path, the filtered development question stating each candidate as a payload of binary
digits while its scope program distinguishes candidates by those digits, and every contract decision of the seed and
of the machinery made by that question — and since the locus it assigns is a *state* row's, its build waits on the
verdict build's first step. #10 briefs the decomposition's build, its build tasks blocked by #30. **#15** is the one append neither #9 nor #12 could
make while another task's finalization held DECISIONS.md; it settles two lines of that file besides — task 5's closing
hash, and the one repair of review-6's findings that no reviewer saw — and **#21** judges the file it leaves.

**The structural-implementation line (4 delivered, 13).** #4 stated the notion behind the engine's refinements — an
index of a carrier by a key, with one contract, three laws and four obligations — and found the argument standing at
its fifth use with no single statement, four carriers each proving its laws separately. #13 briefs its theory: the
statement checked once and interpreted by those carriers, the uses re-cited, nothing meaning anything new. It follows
#8, so that #7's instance is in and the uses are re-cited once rather than twice.

**#20 is committed (`91979be0`) and #48 succeeds it**, both outside every line as #12 and #17 were. #20 made the
replay report a run that produced no judgment apart from a word that was compared and differed, and put the run's
elapsed seconds beside the counts. Its own report then named three gaps in the group it introduced, and **#48**
closes them: the commonest way a run produces no judgment — a harness run outliving its timeout — raises inside the
worker pool, aborts the whole replay and writes no summary, so one bad run still costs sixteen answers and about five
minutes; the group's name is a word a row's own `status` already uses for a different notion; and nothing but reading
the code establishes either. The replay runs in the acceptance of every build still ahead, so each gap is paid twelve
more times, and the measured 14% tail that #20's retained per-answer seconds first expose rides with them
(Decisions). Like its predecessors it takes the tree's free window before the engine line's long build.

Order (queue `7 8 46 47 21 22 23 48 50 49 24-45 14 10 13`): the tree first, then the owner's latest directions, then
dependency, then what can change other tasks, then size. **Five batches stand installed and uncommitted in one tree, so they finalize one at a time -- 7, 46, 22, 48, 50 --
and no new build starts until they have landed** (Decisions, Now). #7 leads because its import cycle is the one thing
in the tree that refuses every check; the tree's other inconsistency, which a shelf caused, is repaired by the
harness (Now).
#15 led and is committed (`2edcabd3`); **#21**, its review, runs beside it: #15 needed
the free tree for minutes where a build behind it would have held the tree for hours, and the file it wrote is what
every brief after it reads. #48 runs beside it — its
only dependency is the free tree, which parking manages. The engine line is then contiguous, because it bounds what every native definition
over a state costs and its finalization holds the tree until it ends. **#22–#31** lead the Q7 line's remainder: the
presentation they build is what #11, #14 and #10 all build over, and a brief written after #16 can name its build
tasks as dependencies, which a brief written before it cannot. Ten tasks stand there by that dependency alone and
not by priority. #11 before #14 and #10 — the verdict is the Q7 order's next
notion, its build's first step is the state's rows that #14's build needs, and it establishes the presentation
relation with its key and invariance lemmas that the decomposition's schema then reuses rather than re-deciding. #14
no longer precedes the two briefs: the constraint that made plan-7 put it there — no build may introduce a new use of
the packed index — is carried by #9's entry, which every brief after it reads. No brief is blocked on #8 in substance:
#3's build order puts `unreached`, the one field that composes the reach, last, and design-9 measured the
decomposition's schema off the engine's path, so #10's recorded dependency on #8 is the queue's order alone. #13 last
of the three lines: it unlocks nothing, and a use written meanwhile instantiates the notion by citing #4's entry and
is re-cited once when the theory lands.

**The verdict's build is sixteen tasks, and one seam carries their dependency.** brief-11 made #11 into eight builds
with a review each, in the entry's own build order: the state's own rows and their presentation (#46/#47), the
request's subject and support as keys (#32/#33), statements and malformed (#34/#35), excess and undeclared
(#36/#37), roots with the permitted removed and added rows (#38/#39), `unreached` over the native reach (#40/#41),
the entry rule with its contract and the two instances (#42/#43), and store absence with every witness relation
(#44/#45). plan-20's correction -- only the tasks ranging over the *development* rows carry the retirement blocker --
arrived after the first task had been blocked by #30/#31, and a blocker cannot be removed, so brief-11 split at the
seam instead: #46 is the new unblocked task over the state's own rows, which #9's entry leaves unchanged, and #32 is
the one task that genuinely carries #27/#30/#31, every later field inheriting it through that single edge. Confirmed,
and better than the blanket it replaces. #40 is the only task ordered after #8, running beside #38/#39 off #37, so the
engine review gates one field and nothing else. Order `7 8 46 47 21 22 23 48 50 49 24-45 14 10 13`: **#7 first**, for its cycle repair and then its own
finalization (Now), with #8 beside it; then #46, its theory written and proved; #47 behind it, judging that theory against
`.build/tasks/46/result.md`, its author gone (its metadata); then #22 with #23, the two other uncommitted batches and #50; then the development rows line, whose #27, #30 and #31
gate the seam; then the verdict's fields.


**Task 7's import cycle leads the order, and task 7 now finalizes first rather than last.** The cycle, whole, as
task 50's own new refusal text names it: `Native_Execution_Refinements` imports `Positioned_Native_Evaluation`
imports `Keyed_Native_Evaluation` imports `Factor_Workflow_Execution_Sharing` imports
`Native_Execution_Refinements` -- a third edge none of the three hand attributions of 2026-09-20 had found. Only the
first edge is #7's, so the repair is its author's, and until it lands no batch in this tree can pass a check. Why it
now finalizes first as well: the reason for putting its check last was that its entry's cycle-time seconds should be
its batch's own, and that reason is void while five batches stand uncommitted -- a check rebuilds every theory
changed since the base, so each one builds all of them whatever the order. What *is* its own is the two recipe
seconds, and those are order-independent. Against that, "7 last" cost a deadlock: every other batch can only be named
for a task that lands. A probe on the base heap cannot see such a cycle: it loads the new theory against the heap's
boundary theory and not the tree's.

## Decisions

Taken by the planning episodes, where they are not entries of DECISIONS.md:

- **An answer to a producing session's question is written into that task's Planner line as it is sent.** A session
  that asks without blocking may have ended before the answer comes, and a session that has ended reads no mail: four
  answers reached nobody on 2026-09-20 (q13, q14, q18, q19), and two of them left their tasks parked with no release,
  since a task parked for an answer records no `after`. The mail wakes the asker if it still lives; the task's
  metadata is what a fresh session on that task reads, and it is the only half that survives. Read with the rule that
  an unanswered question to the planner is a parked session, and that the status line's `questions:` list is read
  against its `parked:` list every episode.

- **The Q7 order stands provisionally, with the engine's cost before its second step.** Basis: T2's measurement and
  the owner's 2026-09-18 direction on inevitable costs. An owner answer to Q7 reorders the whole graph.
- **Order is the queue's; a blocker records a dependency on an artifact, not a wish about order.** A design is not
  blocked on a measurement it does not consume: what #3 had to respect is that the verdict is a definition over a
  whole state, not the number. The number decides whether its *build* can follow.
- **The verdict's build is not blocked on the engine measurement; only its `unreached` field is.** #3's build order
  is by what of the state a field demands, and `unreached` alone composes the reach and carries its cost. Every other
  field is built and checked before #8 reports.
- **The structural state the verdict demands is the verdict's build's first step, not a task of its own.** What is
  demanded is the relational skeleton — constants as atoms, rows in families by kind, three citation relations, the
  statement inert — with its presentation relation and the key and invariance lemmas; it is smaller than the paused
  task 2 by the whole of the term structure, and separating it would split one contract from its only consumer.
- **The incremental assessment of an edited state is planned after the verdict's build.** #3 found that a *stage* of
  judgments is not affordable at either measured figure (224 answer states at about four reaches each, of the order
  of 4,500 s against 22.4 s for the HOL stage) and named the structural remedy: read an edited state's reach and
  declaredness from the state's own assessment and the edit. It is additive and not a prerequisite of a native
  *judgment*, and the verdict's build supplies both its subject and the measured cost that says how much it must save.
- **No new native definition of a development notion is built over the tagged-tree presentation.** The decomposition
  entry presupposes the presentation its schema ranges over and does not define it; building over the present one
  would put a new use of octets as structure into new code, against the owner's direction of 2026-09-19 07:34. Hence
  #9 before #10 and #11. The verdict itself is clear of this: #3's rows are structure and its statement is carried
  inert, which the owner's direction expressly permits where no structure is used.
- **Q2 is extended rather than split.** The decomposition raises three policy criteria of Q2's own family; they are
  recorded in the ledger under Q2 with their provisional choices, not asked as a new question.
- **The index notion gets a theory, planned after the engine line (#13).** #4 answered the planner's question by
  measuring the cost — the four carriers re-proved against a common statement and every use re-cited, a rebuild of
  everything above `Ordered_Member_Trees`, most of the engine — and the repository's own first-use rule is what is
  overdue at a fifth use. Doing it before #7 would re-cite twice and collide with the engine line's tree; doing it
  never would leave the owner's "structurally presented idea" stated in prose while each carrier re-makes the
  argument. Meanwhile a use cites the entry and proves the four obligations for its key, as the entry provides.
- **The store search taking its store before its key is not a refinement and not an index instance.** #4 settled
  this before #7's measurement arrived: its carrier and key are unchanged, and it changes the conclusion patterns of
  three search rules, hence the readiness and reach programs and the recorded recipe words, so word equality cannot
  accept it. If #8 reports key comparisons dominant, what follows is two pieces of work and not one refinement — the
  second notion (an argument ordered so that comparison meets what differs first, `Right_Ordered_Terms` with
  `native_call_key`) factored at its second use, and then the change, whose entry must state why the words changed.
  **It is not taken (plan-23).** #7's claimed measurement puts the reach inside its bound, so the gain is bounded
  above by a fraction of a second on a number already inside while the cost is a second notion and an entry for the
  changed words. It is reopened only if #40's measurement of one judgment shows key comparisons dominating. Recorded
  with its reasons in #7's entry, so the decision stands where the measurement does.
- **#4's criterion stands for what is written after it: a refinement applies a notion.** Word equality of every report
  word remains the acceptance; structurality is the second condition. It does not condemn what met the acceptance
  before — three of the engine line's own steps already meet it through other notions — which is what makes the four
  unstated code equations a backlog rather than a defect in flight.
- **A host-transport fix carries no review task.** Its subject has no native semantics and its acceptance is
  mechanical: the command as written stays within the machine's limit, and every outcome and word equals the retained
  replay's. #12, #17 and #20 are written that way; recorded so that the absence reads as a decision.
- **The machine's two-run limit is one fact, named once in the tool; no mechanism is built to derive it (q4).** The
  harness's interface to a session has no budget query and the limit reaches sessions as prose, so
  `ISABELLE_RUN_LIMIT` in `tools/replay_development_answers.py` is where it stands, with its reason beside it (heavy
  runs share one machine of 60 GiB), and another tool that spawns Isabelle imports it rather than restating it. A
  second mechanism written now would be superseded when the checks, the harness and the tools get their notions in
  the native state (Not yet planned, item 9), which is where the limit becomes a datum of an account rather than a
  constant in each tool. If the harness later exposes a budget, one named constant reads it.
- **A per-tool default cannot hold the machine's limit; the sum across tools is the harness's or the account's (q5).**
  fix-17 surveyed the three tools a task's acceptance runs: only the replay held Isabelle builds above the limit, and
  `incremental_check` (one build; `--threads` proof threads within it, `--jobs` a pool of recipe executions) and
  `probe_theories` (one `ML_process`; `--parallel-proofs` a thread count within it) are unchanged with that reason —
  the distinction between concurrency over builds and concurrency within one was the survey's point. What no tool can
  hold is the sum: a replay at 2 beside a check at 1 is 3, which implement-5 measured and which the finalizer's own
  scheduling then repeated (see Now). No second mechanism is built for it now; item 9 is where it belongs.
- **An acceptance step is runnable as written, within the machine's limits, at the time it is written**, and **its
  acceptance runs the replay alone and never beside a check** (`--workers 1` if it must run beside one), because two
  bounded commands still exceed one two-run machine.
- **A check names an output directory that does not exist**, and a repeat after a repair names another. The harness no
  longer counts a check that cannot run as a failed check; it goes back to the session to correct the command, so the
  cost is the round alone.
- **A fix task's brief states what failed**, in Serves and in its first step, whatever the handoff protocol carries.
  The `{WHAT}` placeholder that made this necessary is repaired; the rule stands because a fixer must not repair
  blind.
- **A Deliverable names files, so a scope that cannot be named as files becomes a survey that reports.** There are two
  hundred tools and no reading of their bodies is open to a planner, so **the bound of such a survey is the set of
  tools a task's Acceptance actually runs**, each named in the Deliverable and each changed only where the rule
  applies, with "unchanged, and why" an expected outcome; anything found beyond that set is reported to the planner
  and not repaired there.
- **A fix that needs the working tree is queued where the tree is free, not merely named for the task that met it.**
  `v2.py after ID FIXTASK` tells a task when a fix lands; it does not give the fix the tree. #12 was named for #5 and
  could not land at all. So a tree-needing task is ordered after a finalization (#15 and #20 after #6).
- **A task's record follows its deliverable when the record's file is held (q6).** DECISIONS.md belongs to whichever
  task's finalization is in flight, and that hold outlasts the tree's: #17's append was refused four times across two
  parks, twice after the tree was its own, and #9's twice before it. So a finished task hands its substantive
  deliverable over at the first opportunity and its entry goes to the next window the file is free, in the one task
  whose subject is that append (#15, carrying both entries); the record is not lost, because that task's acceptance
  reads every entry back and its commit names every task whose entry it carries. Two corollaries: **a review's
  artifact is not changed under it** — which is why #15 waits on #6 — and an entry that cannot land never holds a
  session with nothing else to produce, which is how #5 was lost.
- **A closing line names the commit where the change it records landed.** A build or fix entry's change lands
  elsewhere, so its closing line names that commit — #12's names `9bb1dd7a`, not #15's append. A design task's entry
  *is* its change, so its closing line names its own append and the finalizer's filler closes it. A trailing entry's
  `…` can only ride the next batch that touches the file, which is why #15 sweeps for one.
- **A design task's deliverable is its entry file; its append is split off when the tree was held.** #9 ended partial
  for that reason alone and the work was complete. So a design task delivers `.build/tasks/ID/entry.md`, its
  acceptance is the planner's verdict on that file, and where the file was held the planner creates the install as a
  small fix (#15).
- **A review's finding names the claim, and the repair reaches every place the batch records it.** Review-6's
  findings 1 and 2 were stated against DECISIONS.md and the THEORY_MAP.md row; the identical claims in the commit
  message survived both the quick fix and #19's brief and had to be repaired by hand at the finalization. The batch
  records its evidence in three places by the workflow's own rule, so a finding that names one leaves the other two.
  The structural repair — the commit message's evidence paragraph as a presentation of the batch's record rather than
  a third hand-written copy — is an instance under Not yet planned, item 9: it is the irredundancy point of
  problems.txt on the development layer rather than on the theories.
- **The finalizer's correction of #5's commit message stands; it is not overruled.** It handed
  `.build/tasks/19/commit.md`, task 5's message with three corrections and nothing else: the conditional-premises
  claim review-6 rejected, replaced by "the two installed equations are unconditional and total, carrying their
  formation tests in their own guards"; the closing-line paragraph; and the recipe count 33 of 52 with 19 reused.
  DEVELOPMENT_WORKFLOW.md puts the batch's evidence in the commit message as well as in the entry, so committing task
  5's text would have put a rejected claim into the permanent record beside an entry that denies it.
- **A brief that names a predecessor's artifact names that predecessor's review too.** #19's brief named
  `.build/tasks/5/commit.md`, which carried the claim review-6 had rejected, and described an entry as the file's last
  when another had landed after it; nothing was lost only because the fixer checked both. A predecessor's directory is
  read with the reviews landed against it, or the brief is stale.
- **A lost session's completed work is finalized from its artifacts (the owner's decision, 2026-09-20).** A planner
  splits a lost task over what exists only where the work is *incomplete*; where it is complete and recorded, the
  finalization proceeds from the artifacts and the review judges the committed content, with no author to consult and
  none needed. No check is re-run when the check ran on exactly that content, and a discrepancy is reported rather
  than repaired blind. A review is not duplicated; but re-pointing it does not make it completable (the next decision).
- **A review task is alive only while its subject can still commit.** A review is completed by the commit of the task
  it reviews, so when a returned batch is committed under a continuation task the original's review can never
  complete: #6 stood with every blocker satisfied, no dispatch could start it, and the whole graph stood behind it,
  the producing slot the only one working. plan-15's `addBlockedBy 19` recorded the dependency and did not move the
  completion. So the planner closes such a review at the moment it creates the continuation, against the
  continuation's own review, and carries what the first pass left open into the continuation's brief. #6 is closed
  against review-19's verdict; the one thing no reviewer had seen — finding 1's repair, made by a quick fix in
  DECISIONS.md and in the THEORY_MAP.md row — is read back in #15 and judged in #21, because #7's cost attribution
  reads that claim.
- **A shelf takes a path, so a partial task's shelf can revert another task in flight.** #46's only tracked change was
  `ROOT`; setting it aside took task 7's declaration of `Positioned_Native_Evaluation` with it, both tasks declaring a
  theory in that one file. ROOT then declared neither theory the tree carries, every tool building the source graph
  failed with a missing local theory, the documented replay's sixteen runs all failed in 10.4 s, and two tasks parked
  on it. So: **when a task ends partial, the planner checks whether the shelved paths are shared with another task in
  flight, and the continuation's first step restores the tree.** The repair of a shared file is the restoration of what
  it held, never a revert of the other task's work — reverting task 7's import line and setting its theory aside was
  the alternative offered and refused. The mechanism's half, a shelf that takes a hunk or warns that a shelved path
  carries another task's change, is the orchestration's (Now).
- **A partial task whose deliverables are written is re-planned, not split.** Splitting creates a continuation whose
  commit the original's review cannot follow — the trap above — while re-planning keeps the review pointed at the work
  it was written for, with the lost author's `result.md` as the reviewer's input in place of the author. Splitting is
  for work that is genuinely incomplete and divides. #46 is the first case: theory written and proved on the base heap,
  row, ROOT entry and commit message written, final job prepared, and one unattributed check failure left.
- **A numeric expectation in an acceptance, written before the work chose its cases, is an estimate and not a target
  (q11).** #48's acceptance asked for "one more than the 177 tool tests" and nine named test methods make it 186. What
  the acceptance asks is that the new tests are run by the check and pass; the session reports the actual number with
  its reason. Per-case attribution is what a classification's evidence is for, and one table-driven method would trade
  it for the round number the brief guessed.
- **Who closes a trailing entry is the filler's, not a session's (review-19's follow-up 3).** An entry's closing hash
  could never land in its own commit while the filler asked `git blame` which commit introduced the line: blame
  follows a line's text, so #19's restored line was attributed to `47dcda77`, a commit carrying none of what the entry
  records, and the paragraph above it then contradicted the line below. The harness's repair answers it — a commit
  that leaves an entry open records which entry and its own hash, and the next commit touching DECISIONS.md closes it
  with that hash, the commit where the change landed, which is the rule above. One line of content is left, and #15
  carries it.
- **A task whose check advanced the base returns to the planner with its batch, and the graph owns the window.** The
  harness now refuses to set aside a path the active base was advanced with, which closes the tree's half. The
  planner's half: such a task may return — the disagreement is one-way, a base *behind* the tree being harmless
  because a check rebuilds what changed since it — but from that moment the graph holds **exactly one open task whose
  deliverable is that batch's commit**, and it leads the queue; no other task takes the tree until it lands. If such a
  task is abandoned rather than finished, the base is moved off its content before the tree is reverted. Advancing
  only at the end of a finalization was weighed and refused: a check reuses only from the active base, so a later
  check that advanced instead would re-pay the whole batch's rebuild (153 theories, 341 s for #5). What moves the base
  and when is a host choice with no notion in the state, a recorded residual under item 9; what that account must
  express is that the uncommitted work the base holds is exactly what one open task will commit.
- **No task rests on reasoning not yet written.** Request construction, native problems and the translation wait for
  #11's tasks; what follows the store-search question waits for #8's report.
- **The decomposition's build is off the engine's critical path.** design-9 measured that its schema matches on
  problems and the library, not on a whole state, so its cost is the key length alone: a locus of about 14 bits
  against readiness's 8, about 1.75x on a table that is essentially its keys. This corrects design-2's premise, on
  which #10's dependency on #8 was created; the dependency stays as the queue's order, and #10's build confirms the
  argument in its first step and comes back if it is a whole state after all. The verdict and request construction
  stay on the engine's path.
- **A native question's candidates are stated structurally, and that change is not a refinement (#14).** The digits of
  `finite_development_index` are read as structure by the settled criterion, because the scope program's clauses
  distinguish candidates by them; the candidate's structural statement is #9's locus, not a new notion; the recorded
  recipe words change, so word equality cannot accept it and its entry must say why; and if the locus costs
  measurably, the index notion is applied rather than the payload kept.
- **Transport stays a task of its own and is not a design.** #9 settles its subject and not its construction: a packet
  is not a notion but the presentation of a request row, so the octet direction's task 6 becomes a transport task with
  a reader contract, the reading the inverse of the presentation.
- **The development rows' presentation is briefed once and separately (#16), not folded into a build.** #9 leaves four
  contracts to restate and the presentations to replace; three lines consume them. A shared foundation briefed once is
  the first-use rule applied to the graph. It does not overlap #11's first step: that presents the *state's* rows,
  which #9's entry expressly consumes unchanged and leaves to #3.
- **A decision that cites rather than carries is the engine's measurement from the other side.** #9's closing
  finding: today every candidate of a question carries the rows it refers to, and a citing row refers to them by a
  locus the callee can descend. It is not a task yet, and it does **not** wait for #8's report after all (plan-23):
  that measurement is of a *reach*, a definition whose argument is a whole state, while this is about a question's
  candidates carrying their rows — a different subject. It waits for the locus that makes citing possible (#22–#24)
  and for a measured need in a question that is then expensive.
- **#8's three questions are decided but one, from #7's claimed measurement (plan-23).** Whether the positions
  renaming closed the engine's gap: it did — 44.6 s to 4.35 s against a bound of five, about 5.8 s on the machine that
  recorded the baseline. Whether the store search's second notion is needed: no, and it is not taken (above). Whether
  the interface lookup dominates and takes an index under #4's notion: unmeasured, and deliberately so — review-6's
  `finite_interface_fits` finding stands as the **named candidate for a next refinement**, its attribution owed at a
  measured need rather than speculatively now, which would be optimization ahead of a need and the detour the owner's
  standing rule forbids. A cost inside the bound its planner set is not a performance problem; if a later consumer's
  measurement puts it outside, it is fixed then, at its cause, with the attribution aimed at a real need. So #8 judges
  what a review is for: the contract's premises against the rule table, the provenance against the probe, both numbers
  and the scale factor rather than the flattering one alone, and word equality.
- **The cycle's cost is the loop's own recipes.** Of #5's 341.51 s check the proof phase is 170.04 s and the recipes
  carry the rest, dominated by `native-development-seed` at 159.7 s and `native-development-machinery` at 46.79 s.
  Every batch that touches the export boundary pays both, so they are the cycle time this whole line pays and what
  its refinements move; #7 records them with its measurement, where the owner's single-digit-minute cycle is judged.

- **A run whose result is a timing claims the machine, and a number measured beside another run is not evidence.**
  #7's first measurement was launched and then parked with another worker's run beside it, and the same keyed
  evaluation came out at 153.7 s against the 43.8 s a claimed probe had measured — 3.5x, on the very number a bound of
  5 s is judged against. So its absolutes are not recorded and its ratio inside one run is (seed 1.63x). Every brief
  whose acceptance includes a measurement says that the run claims the machine (`v2.py measuring`) and that the report
  says it did; a refused claim is the protocol working, not a licence to measure anyway. Its second half, from #7's
  claimed run: **a run re-measuring a quantity recorded elsewhere states the scale factor it measured and gives its
  absolutes in both forms.** #7 measured the keyed evaluation at 33.012 s where 43.812 s stood recorded, so its
  machine is 1.33x the baseline's and its reach is 4.35 s there and about 5.8 s here; the ratio inside the one run is
  what depends on neither.
- **The plan's standing and direction sections are brought current when a line closes, not at a periodic
  condensation (#49).** They are two of the three things the plan is kept for, and every session loading the library
  reads them: since the condensation of 2026-09-19 eight decisions landed while those sections still said the engine
  cost was being removed before the verdict was designed, that the decomposition had no generation, and that the
  loop's notions were only posed as residual problems. #49 does it for the engine line, after #8, with the standing
  stated by the planner in its Decided and written by the session from the entries; a claim the entries do not
  support, or another section the new standing contradicts, comes back to the planner rather than being rewritten.
- **A design entry is not rewritten when the implementation narrows what it predicted.** The entry is the record of
  what was decided, with its reasons and limits, and the plan's adequacy account keeps a decision's historical basis;
  but a claim of fact that a later task reads must not stand alone once it is false. So the sentence stays and gains a
  marked correction naming the entry that states the fact, in the form the file already uses for corrections. T2's cell
  ending "no check traverses a value the construction placed" is the first case, and #20 carries it: what is never
  established again is the *formation* of a constructed value and of a constructed premise call, while one pattern
  traversal per premise per clause remains. It is the third pass over one cluster of phrase-level claims (a quick fix,
  #19, now #20), which is the cost of the shortfall item 9's account removes.
- **An appending brief closes every entry whose change has landed and leaves at most one open closing line.** The
  finalizer's filler takes the file's last open line, so a two-entry append with an open earlier entry and a closed
  later one would record the wrong heading and close the wrong line; #15 was safe by arithmetic, not by design. The
  mechanism's half is the orchestration's (Now).

- **A partial presentation is honest; a total one that maps the omitted case somewhere is not (q8).** #9 leaves two
  cases its presentation does not reach, and neither is instantiated today: a problem whose authority is
  `Development_Truth`, and a problem whose subject is not exactly one constant. Both are answered by one rule: the
  presentation stays partial and the partiality is a **premise**, never a total map onto a neighbouring case, which
  would conflate; and the computed observation naming the omitted case is owed **at the first real instance**, of the
  kind `development_without_subject` already provides, not before, because today it would name the empty set. #22's
  partial `development_problem_locus_at` and #24's relation over located rows are right as briefed, and #25 judges
  that the partiality is a premise. The second case arises, if at all, from the decomposition — #2's entry decomposes
  a multi-constant refinement precisely so that it never reaches an executor, so such a parent is a problem over
  several constants — and #10 carries the two shapes it may take (a locus whose subject component is not a single
  key, or retention unlocated with the library row citing it otherwise).
- **`Development_Truth` is kept, presented partially, and its retirement is not a task (q8).** Truth is not an
  authority a problem carries: the order truth-owner-generated says what may override what, while a problem's
  authority records who put it there, and only the owner and the process do. So the two-case optional citation #22
  builds is complete for every problem that exists. It is not retired, because it names a case the plan states and
  has not implemented — a proved contradiction between truth and an owner-level element retained as a conflict for
  the owner — and deleting it would delete that placeholder. If something ever assigns it, what it cites is the
  derivation establishing the contradiction and not an owner record: a design question at the first real instance,
  and not a thing to invent now.
- **The development rows' definitions take the state's constant-key assignment as a parameter (q8, brief-16's
  decision, confirmed).** With an injectivity premise, as `readiness_presents` takes `key` and asks only
  `inj_on key`. It is the library's local-contract pattern, it makes #22–#30 independent of the verdict's line
  instead of waiting on the structural state, and a key assignment fixed inside a locus would be the very nominality
  #9's entry removes.

Watch: an empty result and a failed one are kept apart. #20's entry is the rule's **third application** and cites the
two before it, `Finite_Prepared_Results` and `Native_Path_Stores`; store absence is built inside the verdict's build
(#44). Item 5 — the refusal that cannot tell an absent certified generation from an unavailable input — is where the
rule is *not* applied, so its repair is the fourth application and must cite #20's entry, keeping the instances
findable from one another. The replay is host transport and is repaired where it stands (#20, #48); the factoring, if
it is ever one statement, belongs with the native instances.

Settled and written elsewhere: DECISIONS.md holds every batch's decisions in order, 193 entries plus the two #15
appends; the newest are "A refinement applies a notion; an index is one" (#4), "The verdict of a kind is a native
definition over a state's rows" (#3), "A problem is decomposed through the constants its answer needs" (#2), "A formed
call's applications are constructed, not verified again" (#5).

- **A detailing that could not verify a source against the artifact says so, and makes the artifact win in every task
  it writes.** brief-11 truncated its own gather of the verdict entry with a shell pipe and could not re-read it, so
  its sixteen briefs rest on its own brief's verbatim statement of the build order, the five binding conditions and
  the field names; every task's first gather reads the entry whole, and each Decided gives the entry's wording
  precedence where it is more specific, theory names included. A task departing from its brief's names is following
  that rule rather than breaking it, and its review reads it so.
- **A session does not create tasks; the planner splits.** #44 reports to the planner if the verdict entry names more
  witness relations than one window holds, saying which are in and which are left (its metadata).
- **Pending, and the planner's: what #40 measures.** The first seconds of one native judgment of the verdict, which
  decide whether the incremental assessment of an edited state (Not yet planned, item 1) becomes a task. Its
  provenance rule is in #40's and #41's metadata: a timing run claims the machine and the report says the claim was
  made.
- **Two notions do not share a word, in a host report as in a theory (#20's follow-up 2).** The replay's summary
  named its new group `failed` while a row's own `status: "failed"` means something else — that the harness judged
  that build failed — and the retained `failed-proof` record is exactly where they part: its status is `failed`, it
  is reconstructed, and it produced a judgment. Non-conflation is the owner's principle and the library's own rule,
  and a host tool is not exempt, because the planner reads its summaries to decide: a reader of `failed: []` takes it
  for "no answer failed". Renamed `unproduced` in #48, matching its decider `produced`, with the classification put
  under a host test rather than established by reading two inline comprehensions.
- **Acceptance cost is on the planner's list, but only as a reduction taken with a batch already open on the file.**
  The owner's standing requirement is a single-digit-minute cycle, and every acceptance now pays about eight minutes
  (a 284 s replay and a 180–205 s check). #20 retained the per-answer seconds that make the replay's tail measurable
  for the first time — 495.8 s of serial work, a two-worker floor of 247.9 s, 35.7 s of tail because the order is
  alphabetical and the longest answer starts last — so #48 takes the ordering while it is in that file. It is not a
  reason to open a batch: the standing rule stands that plan items come before executor-side and fixture
  optimization, and a cost the end package itself pays is a different matter, fixed at its cause.

- **The tree serializes by ownership when several batches stand installed at once, and the shelf is the mechanism.**
  The planner sets the order of their finalizations; the one finalizing owns the tree alone, the others park and their
  changes are set aside under their directories and come back with `unshelve` when they are resumed. A session never
  lists, moves or removes another task's file, never adds another task's ROOT entry, and nothing is split at commit:
  the finalizer commits by path and each batch's record is its own. Reason: attribution. A check whose failure could
  belong to any of three tasks cost four sessions most of 2026-09-20, and serializing keeps the base's uncommitted
  content to exactly what one open task will commit, which is the invariant plan-16 settled. A joint check over
  several batches was weighed and refused: it is cheaper by one check and it makes every failure and every changed
  word ambiguous between tasks, which is the whole of the cost just paid.
- **No new build starts while installed work stands uncommitted.** Each further uncommitted batch multiplies the ways
  a check can fail for a reason that is not its task's. So the four batches of 2026-09-20 finalize before the build
  lines resume at #24.
- **A session parked for the tree with its work complete records its result fully** -- what is installed, what
  remains, the commit message drafted -- so that a loss costs a handover and no work. That is how task 5's batch
  survived its session (the owner's decision, above), and it is told to every session parked in such a queue.
- **Installing a new theory in `theories/` while the tree is yours is right; the drafts rule is not what failed.**
  Both untracked theories of 2026-09-20 were installed by their tasks while the tree was theirs, which the rule
  permits and which a probe and a check need; what failed was the shelf's granularity. Recorded because the opposite
  inference -- that sessions are dropping drafts into `theories/` -- would have sessions keep installed theories out
  of the one place a probe and a check read.
- **A report a session reads to decide names what it found (#50).** #20 applied it to the replay's summary; the
  check's refusals before it builds are the second application, and the assertion at `tools/incremental_check.py:243`
  the instance -- message-free, `"phases": {}`, attributed by hand three times in one day. It is the same rule as
  non-conflation in a host report, for the same reason: the planner and the reviewer read these summaries to decide.
  #50 changes no condition, only what a refusal says, and puts each case under a test.


**A cycle between a new theory and the boundary theory that imports it is the new theory's, and no probe sees it.**
A probe loads against the base heap, where the boundary theory is the committed one; the cycle exists only in the
working tree's source graph. So a theory imported by a boundary theory verifies the source graph before it parks, and
the repair belongs to the task both edges belong to (plan-26, 2026-09-20).

**A batch verifies the source graph before it spends a check.** `check.source_checks()` and
`investigate.source_graph(ROOT, [], theory_names(ROOT))` are seconds and name the tree's inconsistency; a check is
about 340 s and a failure round. It is the standing last step before any finalization hands over, and it is what four
refused checks of 2026-09-20 would each have cost seconds instead (plan-26).

**While several batches with new theories stand uncommitted, each one's check builds the others' theories.** The
shelf keeps a not-in-HEAD theory in the tree, so isolation by parking is not available for a new theory file and a
tree consistent enough to check is one holding every batch's pieces. Attribution is then carried by the order, by
each batch's own review, and by the rule that a session reports a refusal on another task's input and never repairs
it under cover of its own check (plan-26; the shelf's remaining half is the orchestration's, under Now).

**A refusal names what it found; a missing condition is not a missing message.** q17 found the source graph naming
the theory it could not resolve but not the importer that demanded it -- #50's subject exactly, and in its plan now.
That `source_checks` passes while `source_graph` refuses is a condition the check does not have, which is a judgment
of what the check accepts rather than a wording, so it is item 10 of Not yet planned and is not built there (plan-26).

- **An unanswered question to the planner is a parked session.** Task 7, the task four others waited on, stood
  parked with `"for": "answer"` on q14 for 74 minutes with its work otherwise complete, while two episodes mentioned
  that question in passing and neither replied; nothing else in the graph could move. So the status line's
  `questions:` list is read against its `parked:` list every episode, and a question whose subject has been overtaken
  is still answered, because the answer is what wakes its asker -- a session does not infer that its question lapsed.
- **`Native_Execution_Refinements` can collect only refinements of constants declared before it; a refinement
  attaches where the exports that consume its code reach it.** #7's import of a theory that refines
  `Keyed_Native_Evaluation`, declared after that boundary, closed a cycle and refused every check in the tree, and
  moving its `ROOT` line cannot help. Which attachment is the author's, who knows which export theories need the
  code; if none makes the code equations live without restructuring the boundary theory itself, the alternatives and
  their costs come to the planner rather than a new structure being chosen alone. #13's detailing carries the same
  constraint for the index notion's four carriers.
- **Word equality cannot certify where a refinement attaches, so a refinement's acceptance carries liveness
  evidence.** A theory out of scope at the exports leaves the recipe words *unchanged*, the check accepts, and the
  refinement is dead code -- the one failure mode a refinement's own criterion cannot see. The evidence is that the
  export theories of the recipes it refines reach it in the source graph (seconds, no Isabelle run) and that those
  recipes' seconds actually moved. In #8's metadata to judge, #7's to produce, #13's to detail.

## Delivered

- **#1 (brief)** produced the engine line, #5 through #8.
- **#2 (design), accepted and committed 2026-09-20 as `0ac9502e`** — DECISIONS.md, 191st entry, 157 lines. A
  decomposition is a row of the development library that is an obligation reduction of the parent's contract to its
  subproblems', presented as an application of one Factor schema over the native presentation of problems; `L` was
  merely empty and `development_loop_issue` already takes it. Composition is `obligation_reduction_discharge`,
  `inference_sound` with `inference_closure_sound`, `obligation_reduction_compose` with `obligation_substitution` for
  depth, and `schema_graph_development_complete` for the tree. Soundness is the schema's, proved once and consumed by
  every application. It corrected its own brief: `development_request_context_least` proves no decomposition shrinks
  a one-constant request, so an oversized context decomposes the problem instead. The answer frame's one-equation
  limit stays unlifted by design. Its six follow-ups are #10's subject. Verdict: `.build/tasks/2/verdict.md`.
- **#3 (design), accepted and committed 2026-09-20 as `47dcda77`** — DECISIONS.md, 192nd entry, 163 lines, no theory
  changes. What later work needs from it: a kind is **the family that holds a row**, never a datum it carries, so no
  octet distinguishes a definition from a code equation and the refinement and definition verdicts stay instances of
  one definition at their family selections. The verdict reads five things of an entity — kind, declared constant,
  subjects, mentions, identity — and nothing inside a statement, so it demands the **relational skeleton** of a state
  and no more, the statement carried inert as its local presentation (`isabelle_local_entities`, invariant by
  `isabelle_local_entities_renamed`). A row's key is determined by its identity and the two presentations share one
  key assignment, so `isabelle_state_embedding` never appears in the decision. **Acceptance is positive and needs no
  absence** — every field an `every` or a `some` with membership decided by a search, "removed implies permitted"
  written as a disjunction — and absence is built only for the witnesses, neither side the other's negation. The line
  it draws: reading which constant a term is an equation of is *presentation* of Isabelle content, whose fidelity
  Isabelle verifies; whether mentions lie in the support, whether a removal was permitted, whether the state is
  closed is the *decision*, and is native. Nine fields as native programs, the contract against
  `development_verdict_accepted (development_constant_verdict replaceable demanded S r S')` in the shape of
  `native_development_ready`, a build order smallest-first, and three conditions named with their owner rather than
  assumed (distinct names, the vacuity of unknown positions, the reduction of an edit). Not built, and demanded by
  translation and installation instead: terms as citation graphs, base constants as cited anchors,
  `.build/impl22/t2/Finite_Structural_Graphs.thy` (stays uninstalled). Verdict: `.build/tasks/3/verdict.md`.
- **#4 (design), accepted and committed 2026-09-20 as `524a3ab3`** — DECISIONS.md's 193rd entry with a
  REASONING_REUSE.md section; no theory changed and no check was run. What later work needs from it: **a refinement
  applies a notion**, which is the second condition beside word equality; **an index of a carrier by a key** is such a
  notion, stated once with its three constituents, one contract, three laws and four obligations, carried already by
  `Ordered_Member_Trees`, `Keyed_Finite_Sets`, `Binary_Relation_Stores` with `Binary_Path_Stores`, and
  `Finite_Functional_Enumeration` with `Finite_Ordered_Representatives`, whose first law already stands there for a
  functional relation. Of the engine's three steps, calls keyed where they differ and the evaluation over positions
  are its two instances; the closure that keeps no applications is not, and is the better exemplar, because
  `finite_demanded_sites_readings` states the traversal's projection once over the general traversal and
  `finite_program_call_closure_sites` instantiates it. **Which key to choose is outside the contract**: two keys that
  both satisfy it differed tenfold in one evaluation, which is what makes the idea applicable in the owner's sense. It
  names four code equations that state no notion (`Factor_Formation_Once_Readings` with
  `Factor_Formation_Once_Definitions`, `Factor_Invariant_Evaluation_Sharing`, `RRA_Inserted_Attachments`,
  `RRA_Linked_Record_Candidates`) and a second notion at its second use. Verdict: `.build/tasks/4/verdict.md`.
- **#9 (design), accepted 2026-09-20; its entry awaits #15's append** — `.build/tasks/9/entry.md`, to be
  DECISIONS.md's 194th entry, "The development notions are structure; a kind is a family and an identity is a path".
  What later work needs from it: problem, request, answer, issue and incumbent are **one notion, a row at a locus of
  the development's published state**; a **locus is a path**, so finding a row is `native_store_search_program.exact`
  and "at most one per locus" is `path_store_lookup`'s single-valuedness — nothing added, the locus an instance of the
  key readiness's tables are already built on. A **kind and a role are prefixes** of the locus, consuming #3: five
  contract kinds and five roles become families, `development_contract_data`'s tags and `development_issue_locus`'s
  `[1]` go, and selecting a family is descending a prefix. What remains of a locus is **the subject constant's key
  under #3's assignment**, so a problem, its issue, its request and its answer stand at one locus; a problem whose
  subject is not one constant has no locus and is retained. **Origin and authority are families of citations**: a
  residual cites nothing, and a problem citing no owner record is generated — the owner authority order with the
  forgery removed. The **request cites where the packet carries**, and the packet is not a notion but the presentation
  of a request row, so `development_named_request`'s lookup of an executor-supplied name is retired: an answer stands
  at a locus or nowhere. `Development_Problems`' datatypes are unchanged and `readiness_presents`,
  `finite_native_readiness`'s rules and `Native_Table_Reach` are consumed unchanged; four contracts are restated (the
  locus and its injectivity, the presentation relation, the request at a locus, the new presentations' injectivity)
  and the recipe words are re-established once. Cost: about 1.75 times the key on a table that is its keys, and no
  measured figure claimed — the growth buys finding a row instead of comparing it, which is 43 percent of the
  profile. Its three residuals: `Development_Truth` without a counterpart, a non-singleton subject, and the packed
  index (#14). Verdict: `.build/tasks/9/verdict.md`.
- **#5 (build), reviewed, repaired and committed 2026-09-20 as `6227819a` (with #19).**
  `theories/Factor_Constructed_Program_Applications.thy` (new, 418 lines), its `ROOT` entry after `Listed_Set_Unions`
  and its import at the end of `Native_Execution_Refinements`: the applications of a formed call at a covered head are
  *constructed* by matching and instantiation and are exactly its admitted applications
  (`finite_constructed_applications_exact`, `finite_constructed_requests_exact`, carried by
  `finite_pattern_accepts_fits`, `finite_constructed_instance`, `finite_requested_constructed`,
  `finite_admitted_constructed`); a demand's applications are listed call by call without being compared
  (`finite_program_applications_listed`); premise functionality is a relation's (`finite_premise_functional_rows`).
  With a `THEORY_MAP.md` row and DECISIONS.md's entry "A formed call's applications are constructed, not verified
  again". Its check (`.build/check-20260920a`, 341.51 s) proved 153 of 1,797 theories and reused 1,644, executed 33 of
  the 52 recipes with every word equal and reused the other 19, passed 177 tool and 35 kernel tests and advanced the
  base. Review-6 accepted the theory, its `ROOT` entry, its one import and its map row against the check's own
  `incremental.json`, and rejected three phrase-level claims: a cell contradicting itself about what the theory proves
  (what the construction replaces is `finite_schema_call_formed`, so what is never established again is the
  *formation* of a constructed value and of a constructed premise call, while one pattern traversal per premise per
  clause remains — which #7 must know); both installed equations called conditional when each is unconditional and
  total, the premises named being the exactness theorems'; and the closing line's hand-written hash. All three are
  repaired, two by a quick fix and the third by #19. What it leaves, and what #7 must close: the machinery's reach
  44.6 s against a bound of 5, the seed's 0.417 s against 0.2.
- **#12 (fix, partial, closed) and #17 (fix), committed 2026-09-20 as `9bb1dd7a`.** `ISABELLE_RUN_LIMIT = 2` stands in
  `tools/replay_development_answers.py` with the reason for the number beside it; `--workers` takes it as its default;
  a supplied value above it is warned about, not refused, because the limit is the harness's property and not the
  tool's; and the replay states on the error stream how many Isabelle runs it will hold before it begins. #12 wrote it
  and could not install it (task 5 held the tree its whole session); #17 installed it byte-identical as four hunks
  with no fifth change, met both halves of the acceptance in one run of the documented command written with no flags
  (`replay holds 2 Isabelle run(s) at once`, exit 0, sixteen replayed, fifteen reconstructed, none differing, the
  adopted walk judged as the published state's unchanged answer), and delivered the survey of the three tools a task's
  acceptance runs (Decisions, q5). Its entry could not be appended and lands with #15, its closing line naming
  `9bb1dd7a`. Its own follow-ups are taken up in #20 and in Now.
- **#19 (fix), committed 2026-09-20 as `6227819a`** — the last of #5's batch: review-6's finding 3's second half (the
  entry's early arrival in `47dcda77`, a commit carrying none of the theory, `ROOT` entry, import or row it records,
  with the cause named as gone) as its own paragraph before the closing line, which keeps the neighbours' form for the
  finalizer's filler; and the reviewer's recipe count (33 of 52 executed, the other 19 reusing their accepted
  executions) in the Evidence paragraph. Its check ran on `.build/check-20260920t19` without advancing the base and
  accepted. One departure, confirmed by the planner and not overruled: the commit message handed over is
  `.build/tasks/19/commit.md`, task 5's text with three corrections (Decisions).
- **#6 (review), first pass delivered, closed by the planner 2026-09-20.** `.build/tasks/6/review.md` accepted #5's
  theory, its `ROOT` entry, its one import and its map row against the check's own `incremental.json`, and blocked on
  three phrase-level claims (see #5). It could not complete — its subject returned to the planner and was committed
  under #19 — and is closed against `.build/tasks/19/review.md`, which judged the repairs and the committed content
  and accepted. Its four non-blocking follow-ups are all placed: #7's attribution in #7's metadata,
  `ffilter_singleton` at item 6, the misattributed early commit repaired by the harness, and the check's own cost in
  Decisions. The one repair no reviewer saw is #15's step 4 and #21's judgment.
- **#15 (fix), committed 2026-09-20 as `2edcabd3`** — the one append neither #9 nor #12 could make while another task's
  finalization held DECISIONS.md: task 9's entry (397 lines, its draft's exact length, and the file's only open closing
  line, so the filler reaches it) and task 12's (46 lines, closing `9bb1dd7a`), one blank apart in the file's own
  separation, with task 5's closing hash corrected from `47dcda77` to `6227819a` and the paragraph above it untouched —
  two hunks, and the arithmetic leaves no room for an edited body. Its step 4, the read-back of the one repair no
  reviewer had seen, repaired nothing and said why: both places already state finding 1's fact and `THEORY_MAP.md` is
  untouched. Its third finding — the same rejected sentence still standing in T2's own entry — it handed to the
  planner, as its brief assigned, and #20 carries it (Decisions). #21 judges the file it leaves.
- **#16 (brief), delivered 2026-09-20** — #9's four contracts as **#22–#31**, five builds each with its review,
  chained 22 → 23 → 24 → 25 → {26, 28} → {27, 29} → 30 → 31: the locus, the presentation relation, the request at a
  locus, the row presenters, and the retirement with the one-off word change. Two decisions of its own that later
  work needs: every definition takes the state's constant-key assignment as a **parameter** with an injectivity
  premise (Decisions), which is what makes the line independent of the verdict's; and `Development_Problems`'
  datatypes are not changed, so a retirement of a constructor would be a task after this line. It reserved #9's two
  residuals for the planner rather than deciding them itself (q8, answered in Decisions).

- **#11** (brief): the verdict's build detailed into sixteen tasks -- eight builds with a review each, in the entry's
  build order -- with the three carried conditions split by owner (distinct names and the vacuity of unknown
  positions in #46, the reduction of an edit in #38, where the difference is computed and consumed) and every witness
  relation held to the last task, so that acceptance being positive and needing no absence is not blurred in #36, the
  first fields at risk. Its grouping and its check against its own Acceptance are in
  `.build/tasks/11/brief/grouping.md`.
- **#20 (fix), committed 2026-09-20 as `91979be0`** — `tools/replay_development_answers.py` and DECISIONS.md. What
  later work needs from it: the replay now decides **per answer whether its harness run produced a judgment at all**
  (`produced`: the run left `answer.json`), reports those that produced none with the error the run left, and
  `differing` means only a word that was compared and differed; both summaries carry the two groups apart and both
  carry the run's elapsed wall seconds beside the counts, with each answer's own seconds in its row. Two guards close
  a defect the brief did not name: a record whose retained status is `failed` with null words could be counted a
  reconstruction by a run that never ran, and `--rerecord` could re-record from one. Its acceptance reproduced the
  numbers exactly (16 replayed, 15 reconstructed, `adopted: ["indexed-data-walk"]`, nothing differing, 283.6 s) with
  the check after it accepted, 1,797 theories reused, 33 recipes' words equal, 177 tool and 35 kernel tests. It
  carries the marked correction of T2's cell (Decisions). Six follow-ups: four are #48's subject, the fifth splits
  (the finalizer's own acceptance summary to Now, the `tools/` consumers to #48's survey), and the sixth is the
  fourth-application citation now in Watch.
- **#46 (build), written and proved 2026-09-20; partial, re-planned, its check unattributed.**
  `theories/Development_State_Rows.thy` with its `THEORY_MAP.md` row, its `ROOT` entry and its commit message: a
  checked state's own rows as the verdict of a kind reads them. It loads on the base heap in 5.4 s with
  `--parallel-proofs 0`, every proof checked in place. What later work needs from it: `entity_kind` and
  `entity_kind_of`, a kind read on the source side and indexing families; `state_key` a **path**; `'i state_row`
  (declared, subjects, mentions, identity) in `'i state_family`, with `state_rows` and `presented_rows`; the citations
  `entity_declared`, `entity_mentions`, `root_mentions`; **`keyed_agree` one notion instantiated twice** — atoms by
  name, rows by identity, a family against itself for "distinct and determined by identity" and across two
  presentations for `keys_shared`; and `state_presents`, which carries every condition of #3's entry as a premise and
  **computes none**, with its recovery, its positions lemmas ("no reference outside the state's atoms" one premise,
  the citation families derived), `kinds_present`, and the renaming invariance over
  `isabelle_table_correspondence`. Two of #3's three carried conditions are discharged here with their owner named:
  `state_presents_distinct_names` (the verdict's ninth field) and `state_presents_unknown_positions` (the vacuity of
  the assessment's unknown positions). Its decisions, in `.build/tasks/46/result.md`: families and atoms are keyed
  lists, so the store's single-valuedness stays a condition on the list; the row type is parameterized by the
  presentation of its own value, so a root carries no kind tag; a root's local presentation is the **same** notion at a
  term, derived from `isabelle_local_entities_renamed` at a one-entity list; the atoms are the whole name table's
  positions, not only the constants a row cites, which is what makes the ninth field a lemma here; the key assignment
  is a parameter per state. Two follow-ups: the two kind-selection instances when the verdict's kind arguments are
  instantiated, and `keyed_agree` over path stores if a later field wants it (the same notion at the store's decoded
  rows). One point for #36, in its metadata: a root row cites its head constant only. What remains is the check it
  ended on — 0.22 s, `"phases": {}`, a message-free `AssertionError` before any proof ran, with the structural source
  checks and the base's stored declaration already eliminated — and the handover.


10. A pre-build condition the check does not have: `source_checks` passes while the source graph refuses, so a tree
    whose modified theories do not resolve their imports is found only at the source graph, one refusal at a time and
    after a batch has already been handed over. Making the structure check answer for the imports of the theories the
    tree modifies changes what the check accepts and is judged on its own; #50 names it and does not build it.

## Open

The owner's questions, each with the provisional choice that stands meanwhile, are in the ledger; where each bites now:

- **Q1** the admission rule of a bootstrap adoption and OD-2. Bites when an admitted native answer is installed as
  Isabelle material — the request class the Q7 order names last.
- **Q2** authority of the first loop's problems and its selection criterion, extended 2026-09-20 with the
  decomposition's three policy criteria (which decomposition when several apply; when one is demanded rather than
  applicable; whether a derived subproblem inherits its parent's authority). Bites in #10's builds and in any
  selection beyond readiness.
- **Q3** what Isabelle establishes about adequacy. Bites when DEVELOPMENT_WORKFLOW.md and plan.md §0.1 are next
  touched; unplanned.
- **Q4** an agent executor confined to its packet. Bites at the plan's stage 3 gate; unplanned.
- **Q5** how far the native residual record reaches. #9 answered its own side of it provisionally and kept it apart:
  a notion is presented structurally when a *decision reads* it, not when a definition mentions it, which is narrower
  than Q5's demand about which constants get residual problems, and a wider record would add problems, not decisions.
  Bites now in #22–#31 and in whatever next grows the notions.
- **Q7** the order of work under the direction that native definitions are normative. It orders this whole graph; an
  answer reorders it.

Not yet planned, in the order they are expected to be planned:

1. **The incremental assessment of an edited state** — its reach and declaredness read from the state's own
   assessment and the edit, with a contract against the assessment of the edited state. #3 measured why and #7's
   claimed measurement sharpens it: one native judgment is affordable — about four reaches, so about 17 s — and a
   verification stage is not, 224 answer states being of the order of 3,900 s against 22.4 s for the HOL stage,
   about 170 times. Until it exists the loop judges one
   answer natively and cannot run a stage natively — which is condition 5a's path. After #11's tasks land, so that
   its subject and the measured cost of a judgment are both in.
2. **Request construction** natively over the verdict's rows (support as the constants the refined entities mention,
   and the least context), the Q7 order's step after the verdict; contract against `development_refinement_request`.
   After #16's and #11's tasks (same rows, same presentation).
3. Problems whose subjects are native definitions, answered natively, and the translation of admitted native content
   into Isabelle material — the owner's direction of 2026-09-19 06:21 and the last step of the Q7 order.
4. A proof request class, and with it the decomposition of a proof problem, which the decomposition entry names and
   leaves undesigned for want of it (refinement and definition problems are requested and judged; a proof problem is
   not). It needs request construction (item 2) for its support and least context, and its first question is what the
   native content of a proof answer is: the library holds native derivations, certificates and replay for calls of
   native programs, while a contract proved against a HOL counterpart is Isabelle material by nature. That question is
   the owner's direction of 2026-09-19 06:21 met head-on, and it is where Q1 bites.
5. The refusal that an absent certified generation cannot tell from an unavailable input: an empty result and a
   failed one are kept apart everywhere else in the library, and not here. One instance of the same rule as store
   absence, which the verdict's build carries (#44), and as the replay's summary, which #20 repaired and #48
   completes. Its repair is the rule's fourth application and cites #20's entry, so the instances stay findable from
   one another (Watch).
6. The four code equations #4 names that state no notion, judged against its criterion — one decision each, none of
   them blocking anything. Their place is after #13, so that a notion found among them is stated the way the index is.
   Review-6 adds a fifth at small scale: `ffilter_singleton`, a general fact about `ffilter` with no connection to
   constructed applications, stated in the client theory where a second use would restate it — the same shortfall #4
   names, and it belongs with the fset facts a later use reaches for.
7. A persistent native published state for the refinement layer: without one, an adoption records the transaction of
   its judgment rather than one against a history, and a later selection cannot supersede an earlier one.
8. The octet direction's task 6, transport: packets and answers travelling as the complete data of their artifacts,
   the word inert carriage. #9 settled its subject and not its construction — a packet is the presentation of a
   request row, not a notion — so it is a transport task with a reader contract (the reading the inverse of the
   presentation), no longer a design and no longer conditional on #9.
9. The plan's stages 4 (policy extended from owner directions) and 5 (the machinery improving itself through the
   process), not begun beyond the machinery's notions posed as residual problems; the harness, the adoption tool and
   the checks still have no notion in the state. Three instances are in hand, all recorded under Decisions and all
   held meanwhile by a planning rule: what moves the active base and when; the machine's run limit, a constant in one
   tool that every other tool spawning Isabelle should take from one place; and the commit message's evidence
   paragraph, a third hand-written copy of what the entry and the map row already record, which a review's finding
   must therefore name three times. That account is what supplies them properly.

## Now

- **Task 7 repairs the import cycle and finalizes first; 46, 22, 48 and 50 follow it**, each named for it (`after 46
  7`, `after 22 7`, `after 50 7`; 48 after 46), so each is resumed or restarted when task 7's batch lands. Task 7 was
  checking at plan-28. The whole cycle: `Native_Execution_Refinements -> Positioned_Native_Evaluation ->
  Keyed_Native_Evaluation -> Factor_Workflow_Execution_Sharing -> Native_Execution_Refinements`; only the first edge
  is task 7's to remove. What it is told, and what stands in its metadata for a fresh session:
  `Native_Execution_Refinements` cannot hold the import and moving the `ROOT` line will not help; the attachment and
  its reason go in its entry; liveness is evidenced in the source graph and by the two recipes' seconds against
  159.7 s and 46.79 s, because word equality cannot see a dead refinement; its check runs with four other batches in
  the tree, so its entry says the proof-phase seconds are not its batch's alone while the recipe seconds are; the
  standing last step (`source_checks` and `investigate.source_graph`, seconds) before any handover; and if no
  attachment makes the code equations live without restructuring the boundary theory itself, it names the
  alternatives with their costs and asks rather than choosing a new structure alone.
- **The four answers that reached nobody are carried**: q13 and q18 into task 22's Planner line, q19 into task 50's,
  q14 into task 7's metadata, all with HANDOFF. What they decide, in one sentence: nothing of the unlisted theories
  or of the cycle was task 22's or 50's, reporting and not repairing was right, and the order now releases them.
  **Both had stood parked with no release** (`after ?`), each parked for an answer its session never read; both are
  now named for task 7. Their work is complete and installed and nothing is re-proved: each runs the standing last
  step, its check and its handover, and reports rather than repairs a refusal on another task's input. The practice
  that follows is in Decisions.
- **The tree is consistent for files.** `check.source_checks()` is clean at 1800 declared names against 1800 files
  (its `refusals` field is new -- task 50's fix stands in the tree), and the harness restored every task's pieces at
  13:21 on 2026-09-20. Only the cycle refuses, and it refuses at `investigate.source_graph` in 0.0 s.
- **Task 46 was not parked for a performance problem**, whatever the park channel said: it parked for task 7's
  repair, so `after 46 7` and no fix task. Its batch is complete -- `Development_State_Rows.thy` proved on the base
  heap in 5.4 s with `--parallel-proofs 0`, the `ROOT` entry, the `THEORY_MAP.md` row in the table's form, the commit
  message, and the finalize line in its handover and result. Its continuation runs only the standing last step and
  hands over. Task 50's corrected handover line is in its metadata: `--files` must include
  `tools/execution_support.py`, which the first finalize omitted.
- **The harness's defects.** Eleven repaired, the newest being the shelf's whole-file revert of `ROOT` and the
  keeping of a base-held tracked theory while the theory it imported went. One of that family is left and it was the
  day's cause: **a shelf must take a new theory file together with the `ROOT` line that declares it, or neither** --
  it keeps the untracked file, so a parked task's theory can stand unlisted and refuse every check in the tree. Until
  it is repaired, isolation by parking is not available for a new theory (Decisions). Six others stand: the
  cross-tool run sum the harness cannot count, the finalizer being itself such a launcher and having broken it once,
  discarding a sixteen-answer replay; DECISIONS.md held for a whole finalization though an append conflicts with no
  append; a review completable only by its subject's commit; the filler recording only the file's last open closing
  line; the tree hold refusing read-only calls and a task's own drafts; and the finalizer's replay summary reporting
  counts without the unproduced group or the seconds.
- `tools/__pycache__/build.cpython-314.pyc` is still tracked and `tools/__pycache__/` still unignored; a session may
  write the ignore line but only the finalizer may stage, and a commit-message instruction alone has now failed
  twice. #48 writes the line, names the untracking in its message and says whether it landed; a third failure makes
  it a task of its own with the finalizer's confirmation in its acceptance. Not a question for the owner.
- **An open closing line in DECISIONS.md is the filler's to close** at the next commit touching that file, by the
  repaired mechanism (the commit that leaves an entry open records which entry and its own hash). #48 is next on the
  file and says whether it closed; a hash is never written by hand by a session.
- **The standing refusals, so they are not re-derived.** The cross-tool run sum (the harness's half; otherwise item
  9's account); the filler's last-open-line and the tree hold (the orchestration repairs its own); the retirement of
  `Development_Truth`; an observation naming problems with a non-singleton subject (today it names the empty set, and
  #10 carries the case); re-opening #16's key-assignment parameter (the library's own local-contract pattern); the
  attribution run #7 offered and the interface index as a task (the named candidate, at a measured need); item 1 (on
  #40's measurement) and item 2 (on the rows now being built).
- **plan-28 created no task** and refused two candidates: a fix task to release tasks 22 and 50 (their work is
  complete, their sessions' successors need only the standing last step and a check, and naming them for task 7 does
  it without a window), and any brief at all (seventeen open build and fix tasks against a cap of six). Its whole
  production was carrying the four lost answers, releasing the two parks, and the rule in Decisions.

