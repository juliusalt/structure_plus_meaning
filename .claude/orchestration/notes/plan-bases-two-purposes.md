# The bases for both purposes, with layers ordered by their dependencies and change (2026-09-23)

The owner (verbatim, ~13:30): "what do you think the target of the bases are? it is not just to give what will be used
to change it is also to allign the content produced with the goals and intent of the repository. Thus it is a two fold
problem - reduce reading by already having the necessary information in the context and reduce writing and mistakes and
improve the content by having the information necessary to steer the correct changes." And: "It does not mean however
that we need to keep the bases and layers as they were before it just means that we need to improve them and optimize
with the twofold objective." Before that: "the layers need to be ordered by the expected churn and be fine grained
enough so that they have actual value while being coarse enough to not have to ping to many of them and for their churn
rate to be actually different. But if we expect some material to be churned then why place it in a layer that is going
to be updated only once in a while and then have to keep the difference." And: "base layers also drift but we expect
less but that needs to also be available."

Nothing committed (the owner's hold of 10:10, which binds the sessions developing the orchestrator, not the run). The
reasoning in force is **Revision while finishing: responsibilities before measurements**, below, as corrected by **The
review of the delivered redesign, and its corrections** at the end, which supersedes the working-material part and
the build figures of **Completion and owner build order**. The
preceding numeric designs, measurements and proposed checks are retained as history of the discussion, not instructions
to rank content. The checks corrected C1 and C5; their stronger predictions are explicitly withdrawn below.

## What was wrong

- **Selection by use alone** (plan-bases-upgrade D1, D2, D4): use — a session reads a file or names what it defines —
  measures the first purpose only. Steering leaves no trace in use: a session that never saw a notion does not show
  that it missed it, so "no review blamed a missing founding notion" (D2's evidence) proves nothing. A hold-versus-read
  cost model (reads saved against 0.1 a token a request) says the same wrong thing: it counts reads saved and nothing
  else, so it may decide *where* and *at what depth* a thing is held, never *whether* intent is held.
- **The layer holds the hot material**: the medium layer is the frontier — what the roles used lately, filling what the
  target leaves — and use is not churn. It is the hottest part of the base, the largest, below the role layers (its
  refresh builds them all again), and its changes are carried in a delta every request pays.

## Measured (the last 7 days; 27 active hours; at the level each base holds each file)

| base | part (list as it stood 13:15) | tokens | churned in 7 d | moved an active hour | changed in the last 2 d |
|---|---|---|---|---|---|
| high | stable | 149K | 18% | 0.9K | 3K |
| high | layer | 380K | 80% | 16.5K | 262K |
| xhigh | stable | 144K | 20% | 1.0K | 3K |
| xhigh | layer | 325K | 84% | 17.5K | 254K |
| max | stable | 356K | 16% | 1.3K | 12K |
| max | layer | 129K | 68% | 6.8K | 78K |

(scratchpad churn.py over git history, digest.held_text before and after each commit, manifest.units for what moved.)
The order is right — the stable part is quiet, the layer hot — but the "medium" layer is the hot set. The stable
reference drifts about 1K tokens an active hour, as the owner expected (manifest.py stable-share, in the console).

~~Steering failures are measurable: 32 of 249 tasks exist to repair content made without what it needed~~ **Withdrawn (checked 14:35): the largest of them (#74, #76, #117, the index notion) re-cite uses written before the notion existed (Carrier_Indexes added 09-21 23:55, the store theories long before) — the factoring the workflow prescribes once a pattern is recognized, not content made without what a base could have held. A count of subjects matching a pattern is not evidence of missing context.** The first form: — re-cite a
law instead of a copy re-derived, state a fact once where copies were made, switch proofs onto contracts — and their
own sessions cost **47.5M of 441.8M (10.8%)**, before the writing they redo and the reviews that caught it. The notions
they name: the index notion (#74, #76, #117: 13M), the native rule family's law (#230, #233, #235), the established
premise (#130), the rearranging program's contract (#275), the placed forest's union forms (#251), the position facts
(#276). Each is a notion a base should have carried to the sessions that re-made it.

Request rates forking each base, an active hour: high 141, xhigh 67, max 24 (every request reads the whole prefix).

## The objective

Least total cost for correct, aligned work: what the prefix costs every request (0.1 a token), plus what is read on
demand, plus what is written again — the repairs, rejected rounds and re-made notions that information in context
would have prevented — plus what churn costs (a stale copy carried, a layer rebuilt with everything above it, the pings
of each entry). Reading is priced by use; writing and mistakes by steering evidence; intent is the owner's, not priced.

## The design

1. **What is held, by both purposes.**
   - *Intent* (the owner's, held whatever its use): the owner's words, the operating rules, the plan, the decisions by
     heading, the central ideas.
   - *Vocabulary* (steering: what exists, so nothing is re-made): every notion of the library — founding and built
     since — by name and signature, at the most compact depth that still says what it is (the outline or signature
     digest), so all of it fits.
   - *Contracts that steer the work*: the statements of the notions the repairs cite (the evidence above: index notion,
     rule family's law, …), of those the open tasks' briefs name as inputs or must consume (the work ahead), and of
     those reviews cite in rejections — at statement depth.
   - *Reading material*: what the roles read (use), within what the budget leaves.
   Depth per item, not all-or-nothing: the presentation-depth idea — the more an item steers or is read, the deeper.
2. **Where it is held, by expected churn** (measured churn at the held depth, and predicted: named by open tasks):
   - *Stable* (the owner's, rebuilt rarely): intent, vocabulary, the quiet contracts. Drift about 1K an active hour.
   - *Medium* (refreshed rarely, the role layers over it): reading material and contracts held unchanged for N days.
   - *Role layer* (per role, rebuilt every few hours at most).
   - *Top* (rebuilt as it moves): what is being changed now. Held as the delta/churn over the layers below — its size
     decides whether a per-role copy pays (xhigh has four roles), or whether what is hot is held at a shallower depth
     (a signature moves less than a statement) or read by the sessions that work on it (their brief names it).
   Three shared entries at most and one or two per role: few enough to ping, each with its own churn rate.
3. **The budget** (the owner's 530K): intent and vocabulary first, then the steering contracts, then reading material.

## Tasks

1. Steering evidence: from the repair tasks' briefs, the reviews' rejection findings and the open briefs' inputs, the
   theories (and names) they point to, weighted by what the repair cost; kept per base.
2. Depth candidates: each notion's tokens at outline, signature and statement depth (digest.held_text), and each depth's
   measured churn.
3. The selection: intent pinned; the vocabulary whole at the compact depth; contracts by steering evidence; reading
   material by use; within the budget, by value per token, deepening items as room allows.
4. The placement: each item to the lowest layer its churn allows; the top's size and a per-role copy's cost computed.
5. base.sh and manifest: more than one layer mark (a layer per mark, each a fork of the one below), a snapshot per
   layer, the watchdog's refresh rule per layer, the pings per entry; the console's two layouts from it.
6. Tests, mutation cases, the suite; the projection in the console; the owner builds and seals.

## The owner's answer (~13:55) and what it settles

"Yes but maybe more than three - this depends on the domain and data analysis not random layering. The steering
evidence is part of it but not the full data. It gives some signal but it depends on factors which are fundamentally
constrained by what was run and how not by the problem at hand, thus further analysis is needed, The depth should
probably be non uniform and be computed depending on the content creating a coherent and adequate selection for the
budget and goals. regarding how material this needs to be considered - maybe for some roles it makes sense to get the
hot material layer under the role such that the role can reason about it to, for others its the other way around again
focusing on the objectives, the budget and teh costs."

So: the number of layers and their boundaries are an optimization over the measured and predicted churn, not a fixed
count; observed signals (use, repairs, rejections) are biased by what was run, and the value of an item is computed
from the problem itself as well — the repository's structure (which notions rely on which), the work ahead, the intent;
each item's depth is chosen per item, for the budget and both goals; and where a role's layer stands against the hot
material is decided per role, by what reasoning over it is worth to that role against what rebuilding costs.

### The tool (base_plan.py): stages

1. Data: every theory at each depth (index line, signatures, definitions, statements) with its tokens; the reference
   graph (theory → the theories whose names it uses); the work ahead per role (open tasks' briefs: the theories they
   name, their deliverables); centrality (how many theories rely on one); intent (the pinned tiers, the founding ideas);
   observed use per role and the steering evidence (repairs, rejections), each as a biased signal; churn per theory and
   depth, measured over the history and predicted from the deliverables.
2. Value per item, depth and role: what it saves in reads and what it prevents in rework, from the domain signals and
   the observed ones; its cost in every request, and in churn by where it stands.
3. Selection: each item's depth chosen together within the budget (a multiple-choice knapsack by value per token).
4. Layers: the chosen items ordered by churn and cut into layers where the cuts lower the total — a rebuild with
   everything above it, a stale copy carried until then, each entry's pings — so the count comes out of the data.
5. The roles: for each, its layer below or above the hot layers, by what reasoning over them is worth to it against
   the rebuilds that placement costs.
6. The console shows the optimized layout beside the current one and the one built from scratch; nothing is built.

## The owner's to decide (earlier questions)

- Is the steering evidence (repairs, rejections, the work ahead) with intent pinned the right measure of the second
  purpose, or is there another the owner wants weighed?
- The vocabulary's depth: every notion at signature depth, or the outline (smaller, names and kinds)?
- What is hot: held per role as it moves, held shallower, or read by the sessions that work on it?

## The owner's further words (~14:00–14:10) and the first computation

"Also the token budgets are not fixed, they should be deliberated - higher cost and smaller tasks is not a problem if it
is coherent and adequate." And: "Also do not over fixate on the data as it did mostly one part of the plan not the whole
plan make sure to account for that." So: no budget is imposed — a base's size is where one more token's value stops
exceeding what it costs in every request, and the curve is shown; and the whole plan weighs in its own right — every
section of native_control_plan.md and every condition of problems.txt shares a weight among the theories it names (a
quarter reaching what they rely on), so the part the run worked on does not crowd out the rest.

base_plan.py (standalone; nothing uses it yet): `data` gathers (8 s: tokens at each depth for 1,837 theories, the
reference graph, the work ahead of 92 open role-tasks, the rates over 27 active hours, the evidence, use, churn of 715
theories at three depths, the plan's 30 parts); `plan` computes. Every assumption is ASSUME, said in the code.

First result (assumptions as written: rework spared 11K a relevant session and notion, a read a quarter of a turn):

| base | size | theories (depths) | layers by churn | plan coverage (median, lowest) |
|---|---|---|---|---|
| max | 281K | 145K (46 statements, 193 definitions, 42 signatures) | 234K quiet + 32K hot | 0.52; Stage 3 0.0 |
| xhigh | 721K | 558K (239 / 402 / 66) | 590K quiet + 115K hot (refreshed ~1.5 h) | 0.94; Stage 3 0.0 |
| high | 313K | 207K (78 / 193 / 37) | 240K quiet + 59K hot (refreshed ~1.1 h) | 0.88; Stage 3 0.0 |

Two layers are least at these weights (three within 1%); the depth comes out per item. Roles: the xhigh reviewer's layer
under the hot layer (reasoning over what it reviews worth ~173K an hour against the rebuilds), high's implementer and
fixer over it (within 3%: the model cannot tell them apart).

**What decides the size** — the rework a held notion spares (the second purpose), far more than the read (the first):

| rework spared | read's share of a turn | max | xhigh | high |
|---|---|---|---|---|
| 3K | 0.10–0.50 | 147–173K | 304–435K | 151–219K |
| 11K | 0.10–0.50 | 267–303K | 681–802K | 281–352K |
| 30K | 0.10–0.50 | 634–666K | 1,429–1,533K | 668–715K |

The run shows only its repairs (11K is calibrated from them); rejected rounds and work aligned wrongly do not show. So
the budget is the owner's deliberation on what steering is worth, and the analysis's next step is a better measure of it
from the problem (not only from what was run).

## Withdrawn: the numeric model (the owner, ~14:30)

"Ok cost is not really that much of a concern and using this numeric based approach is not very smart - the constants
are pretty much meaningless just some aggregate notion - the methodology you use is completely backwards - first you
need to reason, understand and prove your reasoning and then a number is just an operational way to execute the idea not
the idea and not the measure used to steer the decisions."

base_plan.py's `plan` (weighted values, constants for rework and reads, a knapsack) decided what a base is for by
numbers that stood for nothing understood, and its "steering evidence" was a count of subjects I had not read (see the
correction above). It is withdrawn; `data` stays as a source of facts (tokens at each depth, what relies on what, the
open tasks' targets, what changed when). What follows is the reasoning; numbers come only after it, as the way a rule
is carried out.

## The reasoning

It starts where notes/bases-design.md §1 and §4 started — "a base … sets direction and saves orientation; it is not a
lookup cache. What a session has in view is what it thinks with, so a base holds what its roles must reason from, and
leaves to a gather what a piece of work needs in detail" — which §18b (by use) abandoned.

### Premises, and how each is known

- **P1. What a fork can use.** A fork reasons with what is in its context. Anything else it must read, and it reads
  only what it knows to look for: a notion it does not know exists is never sought. (How a session works; its reads
  follow its brief and what its context points to.)
- **P2. What a brief carries.** A brief names the piece of work: its targets, inputs, deliverable, what is decided
  (protocols/_brief.md). It cannot name everything the work must agree with — 1,837 theories, the owner's words, the
  rules, 190-odd decisions, the plan's direction.
- **P3. What makes work right and aligned**, by the repository's own account (DEVELOPMENT_WORKFLOW.md, the owner's
  directions, the memory of standing rules): the aim — the owner's directions, the standing goal, the plan's direction;
  the constraints — native semantics normative, a generalizable argument factored at its first use and instantiated
  after, contracts owned by their notion and consumed rather than re-proved, no conflation of distinct notions, the
  decisions; and building on what exists — reuse, instantiation, the contracts of what the work stands on.
- **P4. What changes, and why.** The owner's words and the rules change when the owner changes them; the central ideas
  and the established library by deliberate refactors; the decisions grow with every batch; the plan's structure when
  the direction changes; the notions under work at every landing in their area; the task graph and HANDOFF.md at every
  planning episode. These are different causes on different clocks.
- **P5. What holding does.** Everything held is in view of every request — which is what it is for; it takes room a
  session needs for its own work; and a held copy whose source changed misleads, unless the session is told and reads it
  again. (Cost is not the concern — the owner; staleness is a correctness concern, room a capability one.)

### What follows

- **C1. What a base holds: what a session must reason from and cannot know to seek** (P1–P3): the aim and the
  constraints, whole; the existence and purpose of every notion — the vocabulary, without which a notion is re-made or
  conflated because it is never sought; and the contracts of what the work stands on, which a brief names only by its
  targets while the work must consume what those targets rely on.
- **C2. What a session knows to seek is read, not held**: the brief's own inputs, the sources it edits, the details —
  a read gives what holding would, and it is where change concentrates (the targets move with the work). Except where a
  role's judgment is about that material as a whole (C6).
- **C3. Depth follows a notion's relation to the role's work, each depth for what it makes possible** — the digest's
  depths: an index line (that it exists and what it is for: it can be sought); signatures (every definition's name and
  type, the commentary: it can be recognized as fitting and told apart from look-alikes); definitions (definitions
  whole, lemmas by name: its meaning can be reasoned about); statements (definitions and every lemma statement: its
  contract can be consumed without re-deriving it).
  - every notion: its index line (all roles);
  - what the work's targets relate to, and the notions of the same kind near them: signatures;
  - what the work's targets rely on, and the central ideas: statements;
  - what a role must reason about the meaning of (a designer near what it designs, a reviewer on what a change touches):
    definitions or statements;
  - for the roles that steer by the plan (planner, designers, task designers, reviewers): the notions each part of the
    plan names, at least at signatures — the whole plan, not the part the run is on (the owner).
- **C4. Each role's work fixes its relations**: the implementer and fixer consume contracts and must not re-make; the
  reviewer judges aim, constraints and reuse; the designer designs notions within the plan and must not duplicate; the
  task designer decomposes along the plan and what exists; the investigator measures; the planner holds the whole.
- **C5. Layers follow the kinds of change** (P4, P5): material that changes for different reasons at different times
  does not share a layer — the frequent part would rebuild the rare part with it, or the rare part's layer would carry
  stale copies of the frequent one. Layers are ordered by how rarely their cause acts (a layer's rebuild rebuilds what
  stands on it). Their number is the number of such kinds actually present in what is held; a boundary needs a different
  cause, not a different count.
- **C6. A role's layer stands above exactly what its reasoning is about.** A reviewer's judgment is about the work in
  its area as it now stands: that material belongs under the reviewer's layer, rebuilt when it changes. An implementer's
  reasoning is about its practice and the work ahead at the level of tasks: the moving material stands above its layer,
  or is read.
- **C7. Numbers only carry these out**: "relies on" is the reference graph (a relation, no weight); "the work" is the
  open tasks' targets; "a kind of change" is a cause, recognized in the history; sizes are outcomes, and if what C1–C6
  require leaves a fork too little room, that is reasoned about (which relation's depth gives way), not averaged.

### The owner's additions (~14:45), and what they change

"one thing to note is that there was no layering back then now some layers can be used for one purpose while others are
used for another and others used for both essentially any mix is allowed. Also regarding layers maybe even makes sense to
add more than one reasoning block so that each layer(or aggregate layers) are reasoned rather than the whole stack fully.
But in general the reasoning is good you can use it as the base to work from."

- **C8. A layer serves a purpose, or both.** bases-design.md §1 and §4 were written for a base that was one block, where
  everything served both purposes at once. With layers, each layer's content can serve reading, steering or both; what
  orders the layers is still how rarely their content's cause of change acts (C5), and a layer's purpose decides what it
  holds and which roles need it, not where it stands.
- **C9. Reasoning blocks where their material is.** A reasoning block stands directly over the material it reasons
  about, so it is rebuilt when that material changes and not when anything above it does: a role-neutral understanding
  of the stable reference over it (rebuilt when the owner rebuilds it), a reasoning over the work area over that layer
  (rebuilt when the area moves), a role's own reasoning at the top — the single role layer generalized, each block placed
  by what it reasons about (C6), shared where its reasoning is the same for every role, per role where it is not.

### How each could be wrong, and the checks

- C1 predicts that work which should have used an existing notion did not have it in view, or not at the depth that
  shows its contract. Checked once, and it corrected me (above): the largest re-citations are factoring, not failure. The
  real test: rejections for re-making or misusing a notion that existed at the time — was it held, at which depth?
  Begun (14:50): of 43 rejections the run's reviewers made with findings, 26 name a re-made or unconsumed existing thing
  (39 findings): theory contracts re-proved instead of consumed, lemmas duplicated under the same name, tool functions
  re-written beside the module that has them, one duplication of HOL-Library. Each is to be read for what existed, where,
  and whether the producing session had it in view and at which depth — some are within the very file the session edited
  (not a base's matter), some outside the repository's theories (no base holds HOL-Library).
- C3's depths: a re-made notion held at signatures but not statements would show that consuming needs statements.
- C5: over the history, does what one proposed layer holds change for one cause?
- C6: does a reviewer's rejection turn on material that changed around the task (other landings), which its layer did
  not hold?

## State, and the tasks to finish (2026-09-23 ~15:00, for whoever continues)

The owner's words, verbatim and in order, with what each answered: notes/bases-discussion.md. The principles they set,
which govern every task below:

- a base serves two purposes — fewer reads, and steering the work to the repository's goals and intent (fewer mistakes,
  less rewriting, better content); never select its content by use alone;
- reason first, understand and prove the reasoning; a number is only the operational way to carry out a rule, never the
  idea or the measure that decides (no weighted constants);
- the run's data shows mostly one part of the plan: the whole plan weighs in its own right;
- budgets are deliberated, not fixed; cost is not the main concern; higher cost and smaller tasks are fine if coherent;
- layers ordered by expected churn (by the cause of change), their number from the domain and the data (more than three
  if the kinds of change call for it); any mix of purposes per layer (C8); more than one reasoning block, each over the
  layer or aggregate it reasons about (C9); per role, the hot material under or over its layer by what serves it (C6).

### What stands (deployed, the whole suite passing: 786)

- The founding tiers of high and xhigh put back (226 founding theories as signatures, as the built stable bases hold
  them); the frontiers chosen again within the room left (still by use: a holding state, replaced by task 3).
- select_base_load.py: frontier_choice and founding_choice return their choices (frontier() and founding() write them);
  projection(who) is a from-scratch build's content (the stable part as written, the frontier chosen again); a test runs
  the command as base.sh does.
- manifest.py stable_share (`stable-share`): the stable reference's drift and what it holds of files the list no longer
  names.
- v2.role_churn_care(role, force=True): the owner's hand builds a churn its rule would not yet.
- base_plan.py `data`: the facts (tokens at each depth for every theory, the reference graph, the work ahead per role,
  churn per depth, the plan's parts and the theories each names, use and the rates). Its `plan` is withdrawn.
- The console (dashboard.py/html): Bases & layers — both layouts at one scale (as built, with each part's drift; from
  scratch), each base's parts, entries, pings and staleness (the stable drift included), what the rules call for
  ("What it should be") with build controls (base.sh layer / delta / restable; a role's layer or churn), the roles'
  layers, the sessions held warm; Costs.
- protocols/base-reasoning.md: the reasoning block's message (thinking only, reply `{DONE}`) — a draft, nothing uses it.

### The tasks

1. **The check of C1**, case by case: the 13 rejections for re-making something that existed elsewhere in the
   repository (their findings: `role_evidence.rejections`, REVIEWS large; the re-making ones listed in this plan's check
   note). For each: what existed and since when (git log), whether the producing session's base held it at its start and
   at which depth (the list at that commit: `git show <rev>:.claude/orchestration/base-load-<who>.txt`, its tier
   headers giving the depth; the layer's seal time in warm.log). What it shows decides C1 and C3 (e.g. held at
   signatures and re-proved: consuming needs statements). The earlier attempt was stopped by a safety classifier while
   reading the reviewers' transcripts; work from the findings text `rejections` returns and the lists' history, in small
   steps, and continue around a stop.
2. **The check of C5**: over the last week, for each item a base holds, the cause of each change of its held text (a
   landing of a task working on it, a refactor re-citing to it, an owner edit, a generated index's growth, the plan's or
   decisions' growth) — the commits' tasks tell which. The kinds of change actually present decide the layers and their
   number.
3. **Selection by relation** (C1–C4, C8), in select_base_load.py, replacing the use-based frontier (the tier base.sh
   re-measures at every layer refresh): the open tasks of the base's roles (the reviewer's: every producing task) — the
   theories their briefs name; what those rely on (the reference graph: move base_plan.references and names_in into
   select_base_load) at the depth consumption needs (statements on high, definitions on xhigh); their neighbourhood (what
   relies on them) at signatures; for the roles that steer by the plan (planner, designer, task designer, reviewer) the
   notions each part of native_control_plan.md and each condition of problems.txt names, at signatures. One tier per
   relation, each with its own header and depth; the central ideas and the founding tier (the owner's) untouched; the
   size an outcome, and if a fork's room would be too small, reasoned about (which relation's depth gives way). Rewrite
   test_select's FrontierTests for the rule; mutation cases.
4. **The reasoning block over each stable base** (C9): a fork of the stable base that reasons over the stable reference
   and writes nothing (protocols/base-reasoning.md), recorded as state/WHO-reasoning.json with the stable base it stands
   on; the layer forks it when it stands on the recorded stable base and its entry is warm, and builds it first
   otherwise (over the stable base just loaded again, when base.sh reloads one), falling back to the stable base if the
   build fails; its own entry pinged like the stable base's (warm_daemon.sh: `base.sh WHO warm reasoning --if-due`);
   forgotten by `drop`; its line in warm.log (`reasoning WHO: OK|MISS …`, which the console's warm_log reads). Prefer
   reusing the harness's existing session launch (v2.launch with an origin resolving to the stable record — a
   `WHO:stable` name in v2.origin_of/base_part — or base.sh's existing fork of `$under` with the record swapped) over
   writing a new launch: an attempt to add one to base.sh was stopped by the classifier. Tests in the style of
   test_delta's DeltaScriptTests (its fake claude replies what the prompt asks).
5. **More reasoning blocks where the layering calls for them** (C9, after task 2): which layers or aggregates get a
   block of their own — shared where the reasoning is the same for every role, per role where not — each directly over
   what it reasons about.
6. **The reviewer's layer over the changes** (C6): a reviewer's judgment is about the work as it stands, so its role
   layer forks the base's forked part (the delta) instead of the medium layer (v2.role_layer_build's origin `who` for the
   reviewer, `WHO:layer` for the rest), is due again when the delta it stands on is replaced (role_layer_due), has no
   churn (role_churn_care skips it), and its forks are told what changed after the delta (stale_of, through the delta's
   snapshot). Reason the other roles' placements the same way (the implementer's and fixer's reasoning is about their
   practice and the tasks ahead: over the medium layer, the changes above in their churn). Tests.
7. **Purposes in the lists** (C8): each tier says what it serves (reading, steering, both), and the console shows it.
8. **The console**: the from-scratch projection from task 3's rule; the reasoning block as a part of each base; each
   role's placement; the "what it should be" steps for reasoning blocks.
9. **Coherence**: README (the bases and the console), bases-design.md §19 (this redesign, pointing here), the first
   planner's queued event (notes/fresh-start-2026-09-23.md and the event in state/v2.json, written under v2.state()) says
   what changed; the whole suite and the mutation check; a handoff entry per deployment.
10. **Ready for the owner**: the lists regenerated by the new rule (`select_base_load.py --frontier WHO`, what base.sh
    runs), checked within a fork's room; the build order written for the owner — for each of max, xhigh, high:
    `sh .claude/orchestration/base.sh WHO layer` (it loads a cold stable base again first, then the reasoning block,
    then the layer), then `sh .claude/orchestration/start.sh --fresh` — and what to look at in the console after.

How to work (as this session did): change a copy of .claude/orchestration outside the tree (the tests run from there:
`nice python3 -B notes/run-tests.py`; mutation cases: `MUTATION_ORCH=<copy> python3 -B notes/mutation-check.py KEYS`),
deploy file by file with a backup under state/dev-patches/predeploy-<time>, run the suite on the live code, write the
handoff entry. Nothing is committed (the owner's hold of 2026-09-23 ~10:10).


## Revision while finishing: responsibilities before measurements (2026-09-23)

The owner clarified that the previous agent's checks are proposals, and that statistics are derivatives used to
check a hypothesis, never the foundation of the design. The historical numeric designs above stay withdrawn. The
following supersedes the literal implementation prescriptions in the ten tasks wherever they conflict.

### The hypothesis and its obligations

A session needs (a) the owner's aim and constraints, (b) a discoverable vocabulary of the whole repository, (c) the
meaning of the notions relevant to its role, and (d) the exact contracts and current sources needed for its particular
judgment. A shared prefix supplies a–c; the task's named-input delivery and deliberate source reads supply d. Holding
something does not establish that it is understood or used correctly. Review still judges that. A generated reasoning
block interprets its recorded inputs; it has no authority to replace them or the task's independently stated conditions.

Selection therefore starts with explicit responsibilities and source relations, never a usage ranking. The reference
pins remain the owner's. The whole plan and its unresolved conditions remain visible independently of the current
queue. The working selection follows the work that can actually be undertaken and the work already under way; blocked
future work remains discoverable in the complete vocabulary and plan. It enters the working selection when its
prerequisites are settled. Taking every future brief's transitive neighbourhood as the current context would conflate
knowing the plan with doing all its future tasks at once. Task inputs stay explicit even when a base happens to hold them.

A source-reference graph is an aid to finding material, not a semantic dependency proof. File and theory references,
qualified names and unambiguous declared names in explicit quotations are evidence of reference. Ordinary prose words
that happen to name a lemma are not. Direct imports supply a conservative additional relation; an unresolved name is
reported rather than silently assigned a meaning. The target's immediate suppliers explain its basis, its direct
consumers expose the distinctions its users need, and the plan's named notions keep the wider purpose in view. These
are distinct relations with distinct purposes, retained separately in the selection report.

Depth follows what the role does with that relation. Implementers/fixers need supplier statements to consume their
contracts. The middle roles need supplier definitions to understand the subject; exact facts a particular review or
design relies on still arrive through its brief and source reads. Targets and neighbours need signatures for recognition,
not all their proofs in every prefix. The complete vocabulary includes purpose, not names alone. Size is then checked
against the window and the room left for work; it never removes an obligation through a score or truncates a required
tier silently. The task form must use the actual room of the built prefix, so larger coherent bases imply smaller tasks.

### Check 1: what the rejections actually establish

The 43 retained rejections were read through `role_evidence.rejections`, preserving their original findings. The
case records inspect ordinary inherited tool results in the producing session's transcript, not its private reasoning.
They distinguish those actual loads from historical committed lists: the lists were regenerated between commits, so
`git show` alone cannot establish what a session inherited. An absent retained snapshot is unknown, not proof of absence.

The stronger prediction attached to C1 is refuted. Task 163 inherited the complete definition of
`development_problems_present`, including the four conditions it duplicated. Task 255 inherited the signature of
`build.interruption_signals` and `RunInterrupted`. Other cases lack the relevant declaration in the recorded inherited
load (249's `map_filter_member`, 128's sibling publication contract, 26's row contract, and the tool suppliers of 145,
229 and 271). Tasks 72, 173 and 221 concern content that was not on main when the producing session began: a refreshed
base alone cannot account for content introduced during a task or in a sibling branch. Consolidation and incomplete
conversion are distinct from never knowing a notion. The previous unexplained count of thirteen is not an adequacy
criterion. The evidence supports discovery and timely contract delivery, but proves neither that missing context caused
all these failures nor that increasing depth would prevent them. C1 and C3 are responsibility-based requirements, not
an experimentally established guarantee of model behaviour.

### Check 2: changes and invalidation

The check follows main's first-parent integration history, counting each integrated change once, and compares the
held projection at each actual depth. A proof edit under unchanged statements does not count as changed held content.
It inspected 380 currently held paths: 414 integrated file changes, of which 367 changed a held projection. Categories
observed include library development, contract refactoring, tool development, knowledge/catalogue publication, plan
revision and direction/rule publication. A commit's subject describes a publication, not proof that its cause was an
owner decision. Thirty-six external-memory or generated-index paths lack complete Git history. No rate is invented for
those. These observations reject an immutable-reference assumption and leave universal causal rate claims unproved.

C5's absolute wording is too strong: different causes do not by themselves require distinct cache entries, and rates
can overlap. The deciding argument is whether a part can change while a substantial predecessor remains valid and
whether a consumer can state exactly which inputs its reasoning depends on. The current domain calls for independently
reusable reference, direction, catalogue and working-material parts. Their order follows their dependencies: the
reference is the owner-kept library basis; direction interprets the development's purpose; the catalogue makes its
accumulated content discoverable; working material follows currently actionable tasks. Each part is reused only with
its same parent and exact inputs. Nothing assumes a fixed universal number of layers: named boundaries admit further
parts if a new independently changing responsibility needs one.

### Decisions to implement and verify

- Keep the founding and central-idea content; replace use-ranked frontier selection by the explicit relations above.
  No numerical value scores, knapsack, use floor or 530K selection ceiling. Report the resulting size and room.
- Put a shared reference reasoning block directly over the stable reference. It reasons only about what is actually
  there, not unseen directions or the pending task graph. Catalogue lookup needs no model interpretation of its own.
  The existing per-role block reasons over the working aggregate and its role's duties; together these are multiple
  reasoning blocks at their respective boundaries, without gratuitous model passes over every index.
- Reviewers, designers and task designers reason over the current changed material and therefore fork the delta when
  it stands; an updated delta invalidates that role understanding. Implementers, fixers and investigators retain their
  methodological understanding below the changes and receive updates above it or in current source reads. No role's
  reasoning is allowed to disguise a stale or different source snapshot as current.
- Record direct parent, source snapshot, prompt identity, purpose and layer kind. Reuse with identical parent and inputs
  follows by induction along that chain: it reconstructs the same input prefix. This proves input preservation only,
  not the correctness or usefulness of the model's reasoning. Missing/failed reasoning is reported and falls back to
  its material parent; it is never marked complete by an empty reply.
- Every retained entry has its own warmth. Reading a longer prefix does not certify a shorter entry's cache lifetime.
  A changed lower part invalidates descendants; a changed upper part does not rebuild unchanged lower reasoning.
- The console and builder consume the same ordered part descriptions and selection. Projection is read-only and names
  unmeasured reasoning separately; it must not show an old role's measured context as a prediction for a new parent.
- Test parent changes, failed and cold reasoning, stale snapshots, role placement, whole-plan coverage, absent usage
  evidence, depth upgrades, and unchanged lower parts. Baseline console tests require blocked loopback networking in
  this environment; use an in-process request transport to exercise the same handlers. Development-copy path assumptions
  in six existing layer tests are also test defects, corrected without weakening their content assertions.

State at the start of construction: checks complete with the limits above; implementation and validation next. All work remains under the
owner's no-commit/no-push hold. No live model sessions or run are started by this work.


### Construction and validation decisions from the first batch

The active use-ranking code and its arbitrary floors/caps are removed, including the withdrawn weighted model.
Historical measurement readers remain observations. Catalogue purposes are quoted as complete first clauses, not cut
at a character quota; every source remains discoverable regardless of which base last generated the catalogue. A
projection computes those generated texts virtually, from current sources, and writes nothing. This avoids both
cross-base omissions and a supposedly fresh projection of stale generated files.

A part's reuse fingerprint comes from the actual frozen pack. A source changing between initial selection and packing
therefore cannot make a later reuse mistake different bytes for the held input. A changed file list is refused. Stable
reference depth/order and the appended prompt are also inputs: the prompt is frozen alongside its pack, and a changed
layout or prompt requires a stable reload. Repeated material names are refused rather than silently regrouped. The
published chain retains all ancestor snapshots; redundant temporary snapshots are removed.

Warmth is keyed by actual session identity. A candidate's hit neither warms nor invalidates the older published entry.
Every reusable prefix remains individually pingable; neither a child's read nor an unrelated alias proves its parent
warm. Reference reasoning uses the existing registered launcher and no-tool guard, not merely a post-hoc check. Its own
completion marker and positive measured context are required. Failure preserves the material parent, is recorded, and
automatic retries use the existing retry interval; an explicit owner build can retry immediately.

The actual role/churn context determines task room, and launch checks the declared task size again against its actual
origin. A brief admitted before a larger prefix existed is returned for resizing before a model is started. This is a
physical capability check, not a token budget that chooses content. Reasoning sizes and any benefit to content quality
remain unmeasured until the owner builds and runs the system.

The mutation pass exposed two inadequate assertions: suffix names could still match the *previous* build when no
rebuild happened. They now also require a new dependent chain and the corresponding additional constructions. Mutants
for revoked use-based selection rules are retired because those rules are removed, and replaced by mutants of the
responsibility-based inclusion, whole-plan coverage, depth, frozen inputs, parents, warmth, inert reasoning and room
checks. Existing guards changed only in representation keep their behavioural tests with updated mutation anchors.

Validation uses a fixed isolated copy of the final code, lists, prompts and tests for a full suite, the complete
mutation set, real pack construction/reconstruction and the console renderer check. Nothing here claims a live cache experiment or that the larger context improves model judgment by
itself; those hypotheses remain for the owner's first run.


## Completion and owner build order

The ten tasks are complete under the revised reasoning above. The implementation, lists and console are installed in
`.claude/orchestration`; the run remains stopped. No model bases were built, and nothing was committed or pushed.

| Task | Result and reason |
|---|---|
| 1. Check C1 | Retained rejection findings and inherited loads distinguish absent context from misuse of held content and later publication. C1's blanket prediction is refuted; discovery and delivery remain requirements for their independently stated purposes. |
| 2. Check C5 | Held-text changes and incomplete histories test invalidation assumptions. Absolute causal/rate claims are withdrawn; independently reusable inputs and their dependencies justify the boundaries. |
| 3. Selection | Explicit subject/supplier/consumer/plan relations set inclusion and depth; complete purposes and vocabulary remain visible. Use-ranked selection, arbitrary floors and weighted constants are removed. |
| 4. Reference reasoning | A registered, inert shared reasoning role stands directly over the actual reference, with exact parent/prompt identity, measured context, independent warmth and explicit failure status. |
| 5. Other reasoning | Per-role reasoning interprets its working aggregate. Deterministic catalogues require no extra model reasoning pass. More named material boundaries are supported when independently justified. |
| 6. Role placement | Reviewer/designer/task-designer reasoning stands above current changes; implementer/fixer/investigator reasoning below. Replacing the actual parent invalidates dependent understanding. |
| 7. Purposes | Each tier declares reading, steering or both. Required sources cannot disappear through a size ranking. |
| 8. Console | Named parts, purposes, reference reasoning, role placement, independent warmth, unknown reasoning size and required build steps share the builder's descriptions and selection. |
| 9. Coherence | README, design §19, superseded upgrade decisions and the first planner's note agree. The queued harness-change event is updated under `v2.state()`. Full validation and deployment evidence are retained below. |
| 10. Owner readiness | All lists regenerated from the rule; twelve real material packs built and reconstructed exactly. Physical room is checked again with measured context, and task launch returns an oversized brief for resizing. Build order follows below. |

Two final checks corrected construction rather than the selection rule. A generated xhigh tier left stale by an earlier
test was regenerated with all three lists and checked for exact agreement with the current relation choice. Generated
reference, role and churn priming messages are excluded from the owner-direction extractor: an interpretation must
never acquire authority by appearing as a transcript's user message. A direct test and mutation exercise that boundary.
The first planner's note replaces its old use-selection paragraph rather than carrying contradictory directions into
a new session.

The fixed validation copy passed **804 tests** and **929 mutation cases**. The suite includes fake-session chain
construction and invalidation, actual HTTP handlers over a pipe transport, and the organization renderer in a stand-in
DOM. Loopback networking is unavailable in this environment; no browser screenshot or live cache experiment is claimed.
All twelve material packs passed byte-for-byte reconstruction. Source hashes before/after validation were unchanged.
The delivered tree's suite result is recorded in the retained deployment report and handoff.

Superseded by the review's corrections below (no working part; a task's relations are its own): the figures that
follow are the first delivery's.

| Base | Source projection | Packed-load estimate | Room before reasoning, task protocol allowance already deducted |
|---|---:|---:|---:|
| max | 590,715 | 609,662 | 277,338 |
| xhigh | 750,151 | 772,042 | 114,958 |
| high | 712,829 | 728,328 | 158,672 |

The source projection and the pack estimate measure different presentations: packing includes its framing and load
traffic. Neither is the final measured context. Reference and role reasoning consume additional room; their size is
unknown until built. These numbers test physical feasibility, not importance or an allocation rule. The actual launch
guard handles the resulting task sizes. Adequacy of generated understanding and practical benefit to the work remain
hypotheses for the next run; fixtures cannot settle them. This harness work establishes no native semantic operation
or resolution of `problems.txt`.

Evidence: `state/analysis/bases-redesign-20260923/` retains the hypothesis checks and inputs, pack verification, source
hashes, suite/mutation logs and deployment report. File-by-file originals are in
`state/dev-patches/predeploy-bases-20260923-170301/`; unrelated existing work is preserved. Temporary pack bulk and obsolete validation copies
are removed after retaining the evidence needed to reproduce the checks.

With the run stopped, the owner builds in this order:

```sh
sh .claude/orchestration/base.sh max layer
sh .claude/orchestration/base.sh xhigh layer
sh .claude/orchestration/base.sh high layer
sh .claude/orchestration/start.sh --fresh
```

Each `layer` command reloads a cold or changed reference as needed, builds/reuses its reasoning and material suffix,
and records the complete chain. If a stable record is absent, first `base.sh WHO build`, wait for completion with
`status`, and `seal`. A `no-launch` hold is never removed automatically. Before starting, inspect all three complete
chains in the console, reference-reasoning status, actual context/room, and each prefix's warmth. After starting, inspect
role placement against its actual parent, first-fork cache results, and the planner's resized tasks. The owner's
commit/push hold binds the sessions developing the orchestrator, not the run (the owner, below).

Final documentation check: the three load-list preambles now describe the delivered named layout. Their old use-based
selection text and historical size targets were removed; parsed held entries compare equal, so no loaded content changed.


## The review of the delivered redesign, and its corrections (2026-09-23 evening)

A review of the delivered work (the owner asked for one) found the reasoning sound and the construction careful, and
four things to correct before a build: the working part's selection rule, the rebuilds it caused, a list written
before its chain, and a fix sent back to the planner. The owner answered (verbatim): "The owner's hold on commits and
pushes remains - this is only true for the orchestrator development sessions it has nothing to do with the runs. Do
all the fixes". Each finding, what checked it, and the decision:

**1. The working part was the union of every current task's relations** (`relation_choice`: the suppliers, subjects
and consumers of every actionable task of every role that forks the base). Its size followed the queue, not any
session's need. Measured over the graph as it stands (source-projection tokens, xhigh depths): 1 task 42K, the 5
current tasks 280K, 10 open tasks 450K, 20 620K. At about ten actionable tasks xhigh and high would no longer fit, and
the build would refuse. The redesign's own argument rules this out: "taking every future brief's transitive
neighbourhood as the current context would conflate knowing the plan with doing all its future tasks at once" — it
was applied to blocked tasks and not to concurrent ones, so an implementer of task A carried the contracts of B to E.
A refinement was checked before it was adopted: hold only what two or more current tasks share. It is refuted too —
for 20 tasks the shared suppliers (233K at statements), all subjects (168K) and shared consumers (81K) come to about
480K: the library is densely related, and sharing grows with the queue as well.

*Decision.* Nothing a base holds depends on the queue. A task's own relations are its own sessions': each is given, as
it starts, what the theories its brief names stand on (statements on high, definitions on xhigh — the redesign's
depths, unchanged), those theories and what uses them (signatures), less what its base holds at that depth or deeper
(`select_base_load.task_relations`, `v2.relations_read`). C1 holds for that session: it is given what it could not
know to seek; C2 holds: what the work names is read, the harness reading it for the session. They are written as the
task's tree holds them to `.build/tasks/ID/relations-WHO/N.md` in pieces a Bash call shows whole (a first message is
one command-line argument, at most 128 KiB; a Bash result is shown whole up to 128,000 characters), and the first
message names them for the first batch. The other current work on the same theories is named with them: tasks 72, 173
and 221 re-made content a sibling was introducing (check 1), which no base could hold. For the five current tasks the
delivery is 11–108K (xhigh) and 18–152K (high); task 192's 114K of supplier statements (14 theories named) is the
largest.

**2. Every change of the queue rebuilt the chain.** `refresh_reason` ran each minute and asked a rebuild whenever the
relation tiers differed — any task added, unblocked or landed — bypassing the rule the watchdog keeps (refresh when what
the delta has cost the forks reaches what a refresh costs, D7), whose own comments record that a count trigger
refreshed far too often. Each rebuild also invalidated up to six role layers above it. A change of the direction's text
did the same. *Decision.* Only a change of the chain's structure rebuilds at once: the list's parts, or the entries a
part holds, differ from what the chain loaded (an edit of the list; a list and a chain that disagree), or the
reference reasoning is absent. A change of what the parts hold, the direction's text included, is the delta's — it
stands at the top of every fork's context, so the owner's new words reach every fork before any rebuild — and D7
decides the refresh, now pricing a chain's rebuild from its lowest changed part (`base_stack.rebuild_cost`: the
catalogue at least, whose indexes every refresh regenerates). A list that cannot be built as it stands (a required
source gone) is said once an hour and not rebuilt every minute.

**3. The list was written before its chain was built.** `build()` rewrote the base's list first; a build that then
failed left a list describing material never loaded, `refresh_reason` then saw nothing to do, and the delta —
which compares the list with what the parts loaded — carried every newly listed file whole. *Decision.* A build works
on a candidate copy (`state/WHO-load-next.txt`) and installs it only once the chain it describes is published. If
anything ever parts them, the layout check of finding 2 sees it and rebuilds.

**4. A fix was handed back to the planner.** The room check at launch compared the brief's Size with the fork's room
for every producing role; a fixer is launched with the built task's id, so a fix whose brief was large — or whose room
had shrunk with the delta — moved a built task from `fixing` to `planner`, where nothing moves it. *Decision.* The
check is made at a task's first start only (no session has taken it up), never for a fix, and counts the relations
the task is given. The brief form check counts them too, so the task designer sizes the task with them.

**5. Room, checked against what the roles use.** The sessions of 09-19/23 grew above the base they forked by (median,
90th percentile): designer 175K/255K, task designer 108K/138K, reviewer 53K/84K, investigator 69K/98K, implementer
81K/166K, fixer 45K/134K. The first delivery left xhigh 135K for reasoning, delta and task together — a typical design
did not fit. With finding 1 the projected bases are max 591K, xhigh 549K, high 431K, leaving 296K, 338K and 456K before
reasoning. A typical session's work with its relations fits within that, less the reasoning still to be measured
(the designer's median 175K with up to 108K of relations in 338K); the largest designs are split at their brief's form
check. Nothing had to give way. These are checks of feasibility, not what decides content. A role layer's measured context is the input of its own last request, which leaves out its own
thinking; the room its forks have now counts that thinking (`thought`), as a churn over it already did.

**6. Placement by cause.** The whole-plan notions (signatures of what the plan names) and the pinned tool contracts
stood in the working part, rebuilt with the queue; they change with the plan and the library's publication, the
catalogue's cause. Both are now in the catalogue, the generated block holding the whole-plan tier alone.

**7. The rest.** A judging role's reasoning stands on the delta whenever one stands, warm or not: a parent chosen by
warmth made the layer invalid whenever the delta cooled and the one built instead invalid when it warmed; its build
forks the delta even cold (it writes it once). A failed reference reasoning is retried automatically once; a second
failure over the same reference and prompt is said and left to the owner, whose build retries at once. Whether the
reasoning's thinking reaches its forks is the model API's behaviour, not the harness's, and the whole value of a block
that writes nothing, so it is measured at the part built over it and said when less than half of it arrives. The use
readers kept "as diagnostics" and `--founding` (a no-op) are removed with their tests; the redesign's compressed code
is written in the harness's style; bases-design's two §18s are 18 and 18b.

**8. The first planner's note** said the owner's hold bound accepted work and that it authorized no release of the
graph — contradicting the fresh-start charge, and wrong by the owner's answer. Its landing statement is restored and
the hold is not mentioned to the run.

Validation (an isolated copy, `ORCH_PROJECT` the repository): the suite and the complete mutation check, results in
the handoff entry of this deployment. Build order unchanged: `base.sh max layer`, `base.sh xhigh layer`, `base.sh high
layer`, then `start.sh --fresh`. After the builds, warm.log's `reasoning WHO: carried …` or `ATTENTION … is not
carried into its forks` says whether the reference reasoning does anything; the console's projection gives each
current task's delivery.

**The window, after this review (the owner, 2026-09-23 evening).** Asked why max's room was only 296K of a 1M window:
it is the window less the base (591K), the ceiling the harness then kept (972K, from 09-19), its 65K wrap-up margin
and a 20K first message. Claude Code 2.1.280 itself holds back 20K for each reply and sends nothing past 977K; its
auto-compact ran at 967K. The owner ordered Claude Opus 5.5 for the bases, auto-compact off, the ceiling raised and a
30K wrap-up margin, with a tracker that says if that ever becomes a problem (`window_watch.py`). The notice is now at
947K, so the rooms before reasoning are max 336K, xhigh 378K, high 496K (347K, 388K and 506K once the memory left
the bases, below); nothing in the selection changes.

**What each base holds, reviewed before the build (the owner, 2026-09-23 evening).** The owner: "for example I think
memory is included in the bases, but clearly raw memory includes orchestrator session information which should never
be shown to any of the content producing bases". Checked: every base's direction held Claude Code's whole memory
directory, and Claude Code's auto-memory put its index into every run session besides (all 60 latest sessions of every
role carried it); of its 31 entries twelve were the orchestrator's own operation (the commit hold, the autonomous
order, the harness's concepts, the sandbox, subagents, callbacks). The knowledge base's collected owner words were 30
machine prompts in 34 (probes, delta hold messages with theory diffs), all from background sessions. *Decisions.* No
list names the memory; auto-memory is off in every settings file; a run session is refused the memory and the
orchestrator's notes; eleven entries whose subject is the library (the owner's words on native definitions, local
contracts, presentation depth, reuse, performance at its cause, plan focus and detail, the fast cycle; the Isabelle
lessons on fact labels, proof search and probes) are held as the library's working practice, by an explicit list; the
collector leaves background sessions out; the base prompt says a task is given its relations; the first planner's note
no longer points at the orchestrator's notes. The rest was checked and holds: the reference pins, the direction's
plan, reasoning inventory, owner words and rules (their solo-session mechanics named as the harness's by the base
prompt), the catalogue, the tools, the ledger, the role layers' evidence, and nothing else Claude Code injects (no
skills, no user CLAUDE.md).

**Every channel, and every piece once (the owner, 2026-09-23 evening).** "Ok generalize this and try to find other
similar problems with the bases content", then "Ok now generalize even further and review the rest of the content find
what is incorrect, what is redundant and what can be cut and what is misplaced and see if all of the layers are
adequate and coherent and their content is too and that every piece of content is required and irredundant". The
question asked of every channel into a run session — the lists, what Claude Code adds by itself, the first messages,
the role layers, the knowledge base: whose content it is, what authority it claims, whether it is current, whether it
is there once. Found and decided (README, "Every channel into a run session"): Claude Code's git status and commit
guidance off; its notes on summarization and a closing report named as not holding here; each base's opening read by
window_watch; the fresh charge the harness's; a role layer's evidence of practice from the current model's sessions
only; the designer's protocol corrected; the catalogue without what each base holds (about 20K tokens a request); the
plan's map for high only; decisions as `##` entries with their first sentence whole; the practice per base, without
two entries that were harness mechanics (one contradicted the probe rule) and one said already in the owner's words;
the owner's paragraph and the standing goal's second half held once; a role layer's forks given their values, not the
protocol again (about 7K tokens a request); a brief's facts not stated again where the session holds their theory at
statements. Held and found right: the reference pins, the reasoning prompts, the direction's plan, reasoning inventory,
owner words and rules, the decisions and tool indexes, the knowledge base's layer, the relations. For the planner (the
first planner's note): 25 theories without a THEORY_MAP row, and a DECISIONS.md state record held as a decision. The owner
asked then whether AGENTS.md and DEVELOPMENT_WORKFLOW.md are needed at all: every paragraph of both was set against what
a session holds besides. AGENTS.md is held no more — it is a solo agent's entry (read the workflow first, use the
sixteen cores); its rule, gates and batches are DEVELOPMENT_WORKFLOW.md's and the owner's own words (the Codex
selection, §10–§13); its note on the closed native workflow is REASONING_REUSE.md's two sections on it, and those
theories are the owner's pinned central idea. DEVELOPMENT_WORKFLOW.md was kept at first, as the only precise statement of what the standing rule excludes and of
what a content cycle retains; the owner asked again, and that was refuted (the next paragraph). And the base prompt's "The owner added on 2026-09-19" paragraph
on the performance channel is the harness's statement of a rule whose words were not found in the retained
transcripts. Projected: max 558K, xhigh 517K, high 402K; rooms before reasoning 369K, 410K, 525K.

**DEVELOPMENT_WORKFLOW.md, paragraph by paragraph (the owner, 2026-09-23 evening).** "Is the rest of
development_workflow.md content still needed? Is it not in protocols, briefs or other parts that are in the layers
already". Every paragraph was set against what every base holds besides (the curated owner words, problems.txt, the
protocols, the base prompt, the pinned reference):

| The workflow document says | Held, in every base, by |
|---|---|
| read it before work and after every compaction | the harness: a session holds its protocol, and there is no compaction; problems.txt calls that reading "the symptom, not the repair" |
| the standing rule; Isabelle's bootstrap role through genesis | codex-owner-directions §10, both messages verbatim; owner-directions §2 (OD-2) |
| the rule's reach: prose, host code, judgments, metadata, digests and supplied tables add no semantics; a missing operation is an unmet requirement, never a fallback; no verdict authorizes its own handoff | codex §7 (a supplied observation has no structural boundary; a receipt binds a description to a run, never to what the function computes) and §10 ("or anything else … anywhere"); problems.txt, conditions 1–2 and "What does not meet them" (a prose rule, a document, a metadata dictionary, a digest); OD-2 (no successor justifies its own adoption); REASONING_REUSE.md's opening (max, xhigh) |
| every problem, the machinery's own included, through the machinery before the dependent decision; the first-use rule; criticism of every result | codex §6 (the list verbatim, and "not blindly follow the machinery"), §4, §9; owner-directions §4, §5, §8; problems.txt (the first-use rule quoted; conditions 4 and 6) |
| what a content cycle retains | the closed native workflow's contract (Factor_Development_Cycle; Factor_Development_Admission: a missing phase refuses admission), pinned in every base's reference; problems.txt condition 2: a workflow requirement holds by construction |
| concrete structural subjects, computed observations | codex §7, nearly word for word; problems.txt condition 1 |
| host scheduling: batches, parallel problems, one agent, background runs | codex §6, §11, §12; owner-directions §12; carried out by `_production.md` (one batch a step), `_checks.md` (runs in the background, every error fixed together, parking) and the harness |
| substantial candidate batches, grouped repair | codex §13 verbatim; problems.txt, "Development scheduling"; `_checks.md` |
| condition 5's two gates | problems.txt 5a and 5b; codex §13 |
| temporary files cleaned | codex §15; owner-directions §10; the harness sweeps a task's outputs |
| where a batch's decisions are recorded | `_finishing.md`, "Recording", nearly word for word; the designer's and planner's protocols |
| the reasoning inventory, the review rule | REASONING_REUSE.md (max, xhigh; a build task is given what it needs of it under Decided); the plan links GENERALIZATION_REVIEW.md's continuing review rule itself |

*Decision.* No base holds DEVELOPMENT_WORKFLOW.md. Every requirement it states is held in every base by the owner's
own words — which outrank a generated restatement of them — by problems.txt, the protocols or the pinned theories, and
its mechanics are the harness's. problems.txt, which every base holds, names the document itself as the defect
("DEVELOPMENT_WORKFLOW.md is discharged by remembering it"; condition 2, a workflow requirement holds by
construction; a further prose rule or document "restate[s] the defect"). The one statement it alone makes, that
Isabelle establishes the bootstrap account's adequacy, is what the owner questioned (owner-directions §3; the ledger's
open Q3 since 09-18): held, it would steer every session by a contested generated reading. The file stays in the
repository, the entry of a session working alone (AGENTS.md points to it). The base prompt says that it and AGENTS.md
are not a run session's to read, so that one meeting them in a document (DECISIONS.md, the plan, HANDOFF.md name it)
does not; `_finishing.md` no longer points to it; neither the base prompt nor the reference reasoning names "the
operating rules" as held. About 2.4K tokens a base.

**The same question of every source (the owner, 2026-09-23 evening).** "Ok now generalize this method and search for
other redundant information and files for example is generalization_review.md and all of its content required -
having too little information is bad but having noise and contradictions and multiple sources is just as bad". The
method, for every text a run session holds or can meet as a file: is it needed, by which roles and for which purpose;
is it held elsewhere for the same sessions; does it contradict what is held, or is it stale; does it claim an
authority it has not; can a session meet a stale second copy of it. Measured with it (the 320 run sessions of
09-21/23: 124 reviewers, 71 fixers, 65 implementers, 27 knowledge bases, 15 task designers, 10 designers, 8
investigators):

- *The base prompt paraphrased the owner under the owner's name.* "The owner added on 2026-09-19: a performance
  problem has its own channel …" was the harness's rendering; the words are recorded verbatim in
  `notes/orchestration-v2-plan.md` (session 212840df), which the review above wrongly said could not be found. The base
  prompt now quotes them; their mechanics are `_efficiency.md`'s and `_checks.md`'s, for the roles they concern.
- *The base prompt said again what every tool-using role's protocol says* — the tools and `v2.py change`
  (`_production.md`, which every role but the knowledge base and the reasoning blocks receives, and those use no tool),
  how a check ends and the machine's limits (`_checks.md`) — and said the finalizer's commits and parking twice. Each is
  said once now, where its sessions are. A scan of every role's message, its protocol with its parts, for runs of ten
  words it shares with the base prompt or holds twice found two more: the planner's protocol said the base prompt's
  sentence on the ledger again, and the designer's said `_finishing.md`'s rule on where a decision is recorded again;
  each now refers to the other.
- *Stale copies.* `state/held/` kept files no list names and no code reads, written 09-18/20 by designs since
  replaced: OBLIGATIONS.md, REASONING_REUSE.md and owner-directions.md as they stood then, ADMISSION.md,
  founding-index.md, a copy of an orchestrator note, and the old depth folders. No run session read them; they go.
  The whole-library indexes and practice (`theory-map-index.md`, `tool-index.md`, `library-practice.md`) are current
  and generated for a reader of the whole library; they stay.
- *Repository documents* are the library's, so the run settles them: GENERALIZATION_REVIEW.md (a dated review whose
  continuing review rule the plan restates), ADMISSION.md and proposal.txt (named by nothing held), OBLIGATIONS.md and
  plan.md (the predecessor plan, cited by the plan for §0 and D-9), and the plan's citation of the workflow document
  for the standing rule — none read by any run session. They are in the first planner's note.
- *Checked and found right:* no run session read the orchestrator's evidence or backups (`state/analysis`,
  `state/dev-patches`), so no guard is added for them; the knowledge base's collected owner words leave the sessions
  on the orchestration out (two Codex questions of 09-19 since the curated ones); REASONING_REUSE.md is read by 26 run
  sessions, and a section of it sampled against THEORY_MAP.md adds what stays open to what the rows say, so it stays.
- *The discussion record* (`notes/bases-discussion.md`) is the harness's development record of the owner's words on
  the bases; no list names it, and a run session is refused any read of the orchestrator's notes
  (`work_meter.PRIVATE`).

**Every layer of every base, for what it holds twice (the owner, 2026-09-23 evening: "Ok continue on checking every
base layers for redundancy").** Every entry of each base rendered as it is held (the generated catalogue files as a
build makes them) and measured for a source held at two depths, a catalogue line for what the base holds, and runs of
twelve words an entry says again of an earlier one in load order; then the layers above a base the same way.

- *No source is held twice* in any base, and no catalogue line names a theory or tool its base holds.
- *The reference.* Theories share their premise lists and equalities (Factor_Current_Entries with
  Factor_Current_Programs the most, 106 runs): the library states a theorem's premises in each theorem, which is not a
  notion stated twice; duplicates are judged where they are written (the restatement hints, the reviews).
- *The direction (max, xhigh).* owner-directions.md §3–§5 and §7 (33–55% each, about 450 tokens) and two practice
  entries (16–22%) are what the plan quotes as its basis: a citation of its source, which high, holding no plan, needs
  whole. Kept.
- *The catalogue.* The decisions index shares 34 runs with the plan and REASONING_REUSE.md (their citations of
  decisions); two tools share a configuration line. Nothing to change.
- *The knowledge base's layer over max.* HANDOFF.md (38K tokens) repeats nothing of the base. The ledger's owner
  directions (2K tokens) are 62% the plan's verbatim quotations of three statements of 09-19 (its citations, kept) and
  one entry the curated selection holds (86 tokens; the ledger is the record, and is not cut). The collected owner
  words repeated the ledger's two Codex questions of 09-19, read one file after the other. *Decision:* the collector
  leaves out what the ledger records (`extract_owner_directions.ledger_quotes`, compared as words however wrapped), so
  each owner statement reaches the knowledge base once; on the data of now it collects none.
- *A task's first message.* A fact its brief names is not stated again when its theory is given at statements, by the
  base or by its relations (`relations_read`'s `stated`), so its statements and its relation files hold nothing twice.
- *The reasoning blocks* (the reference's, the role layers') are generated thinking, measured after the build — whether
  it reaches the forks — not before.

**The order of the parts, measured (the owner, 2026-09-23 evening).** "REASONING_REUSE.md is in direction, but does it
not change often? is the layer ordering based on churn?" The owner's rule is that layers are ordered by the cause and
rate of change of what they hold; the redesign's Check 2 had restated the order as one of dependencies (reference,
then direction, then catalogue), with rates only as evidence. Measured over the run's 472 commits (09-19/23), the
commits that changed each part's held text at the depth it is held (a proof edit under an unchanged statement is no
change; `state/analysis/bases-content-20260923/audit/churn.py`):

| Held | max | high | cause |
|---|---|---|---|
| the owner's words, problems.txt, the practice | 0 | 0 | the owner speaks; the selection is curated again |
| the plan | 2 | — | the direction of the work is revised |
| REASONING_REUSE.md | 6 | — | a landing publishes a pattern of reasoning (92 commits since 09-10, when every batch did) |
| the stable reference (270 theories) | 10 | 10 | founding notions revised: 18 changes in 15 theories, all on 09-22, two consolidations |
| the catalogue | 187 | 186 | every landing: THEORY_MAP 152, the tools 61, decisions' headings 25, whole-plan theories 11 |

*Decision.* REASONING_REUSE.md is a part of its own, `inventory`, between the direction and the catalogue on max and
xhigh (high does not hold it): its cause is the catalogue's — publication with a landing — but it acts about thirty
times less often, so inside the catalogue it would be loaded again with every catalogue refresh, and inside the
direction every change of it rebuilt the direction with it (the plan and the owner's words, which changed twice). Each
part is now ordered above the direction by how rarely its cause acts. The builder, the refresh rule and the console
take a list's named parts as they come (no part name is written in their code); the base prompt and the reference
reasoning's prompt name the inventory.

*For the owner.* By rate alone the direction (0–2) would stand under the stable reference (10). It stands above it by
the owner's words of 2026-09-19 that recent tokens weigh more ("put what should steer last") and because the reference
reasoning sits directly over the reference; the direction is small (12–73K), so its place costs little either way, and
a change of it reaches every fork at once through the delta. That trade is the owner's to confirm.

**Dependency order and churn order made one (the owner, 2026-09-23 evening).** "Idealy we would want to make the
dependency and churn based orders coincide that would optimize both quality and cost. - try to find what else you can
move around so that this is achieved if it is possilbe." and "Also some things like decisions and probably reuse too
are append based more so than modification - so what can happen is we could put them lower and then have their
changes seperate and only the changes updated and consolidated once they get big enough and similarly for everything
else that is append based."

*What a change costs, and so what churn has to mean.* A part's change rebuilds it and everything over it, so for two
parts A under B the order costs less exactly when A's changes per token held are fewer than B's (changes × the size
rebuilt, exchanged pairwise): the order that lowers cost ranks parts by changes per token held, not by changes. And
the delta already carries a change by its units — a theory's changed commands, a document's changed or added
sections, an index's changed lines (`manifest.units`) — refreshing when carrying has cost what a rebuild would (D7).
An appended unit leaves everything held valid and is carried as itself; a modified or removed one leaves its old form
held under the new until the part is rebuilt. So what places a part is how often it *modifies* what it holds, per
token held; appends are consolidated by D7 wherever the part stands.

*Measured* over the run's 472 commits (units appended, modified, removed at the depth each is held;
`audit/kinds.py`, `audit/churn.py`): the decisions index 84 appended, none modified — append-only; REASONING_REUSE.md
1 appended, 13 modified, 23 removed (the run consolidated it); the plan 40 sections removed in one restructuring; the
theory map 126 appended, 248 modified (rows rewritten); the tools 324 appended, 80 removed; the stable theories 35
appended, 34 modified or removed; the owner's words and problems.txt nothing. Commits that modified held text, per
thousand tokens held: the owner's words and the practice 0, the decisions 0, the reference 0.05, the plan 0.08,
REASONING_REUSE.md 0.14, the plan's notions 0.25, the theory map 0.9, the tools 1.1.

*The order of dependencies* — what a part must be read after to be read rightly: the owner's intent rests on nothing;
the reference realizes it; the plan names the reference's notions; the decisions are taken within the plan; the plan's
notions are what it names, and the reasoning inventory reasons about them; the catalogue indexes all of it. The two
orders coincide (the decisions, modifying nothing, stand where they depend at no cost):

| Part | max, xhigh | high | modified per 1K |
|---|---|---|---|
| stable | the owner's words, problems.txt, the practice; then the reference | the same | 0, then 0.05 |
| (reasoning) | over the owner's words and the reference | the same | — |
| direction | the plan, the decisions | the plan's map, the decisions, the tool index | 0.08; 0; 0.1 |
| inventory | the tool index, the plan's notions, REASONING_REUSE.md | — | 0.1; 0.25; 0.14 |
| catalogue | the theory map (and xhigh's tools held whole) | the same, and the tools held whole | 0.9; 1.1–1.6 |

*Not more parts.* Every part is kept warm on its own (`warm_daemon.sh`: a descendant's reads do not keep it alive),
a ping reading its whole prefix, several hundred thousand tokens an hour a part; sources with rates this close share a
part instead (the plan and the decisions; the plan's notions and REASONING_REUSE.md), which reloads the smaller
neighbour at a change, tens of thousands of tokens a few times a day.

*What it changes for quality.* The owner's words stand first and the reference reasoning reasons over them with the
reference; the owner's words of 2026-09-19 that recent tokens weigh more ("put what should steer last") are served
by the delta, which carries any change of them at the top of every fork at once, and by the role reasoning and the task
above everything. The delta names where a change is held ("the stable part", "the parts over it"): it had called
everything over the reference "the working frontier", which has not stood since the named parts.

*Every source by its own units (the owner, the same evening: "And same is true for reuse no? Have you not found other
append structures? Also you never clarified regarding the tools, where do they go? because clearly they also do not
churn and would make little sense to reload").* A first count keyed a file's lines by their text, so a changed line
counted as one removed and one appended, and "tools" mixed the index with the tools held whole; measured again, each
source by its own units (`audit/appends.py`), in the run and in the nine days before it:
REASONING_REUSE.md, by section: 1 appended, 31 modified, 23 removed in the run; 84 appended and 98 modified before —
83 of its 85 commits revised existing sections, each new pattern rewriting what the others said stays open. It is
revised, not appended: its place is by its modifications, where it stands. The decisions: their entries were edited
(123 modifications in the run), but what a base holds of them, heading and first sentence, only grew — append-only as
held. The tool index, a line a tool: 6 appended and 1 changed in the run, 234 appended and 3 changed before — a second
append structure, moved from the catalogue to stand right over the decisions (the inventory's first tier on max and
xhigh, the direction's last on high), so the theory map's frequent rewrites no longer reload it. The tools held whole
(the check workflow and the native development tools, by function and docstring): 42 appended and 28 modified in 16
of 20 commits in the run (incremental_check.py in 7) — the most modified per token of anything held, so they stay on
top. THEORY_MAP.md was append-built before the run (1,041 rows added, 119 changed) and rewritten in it (126 added, 512
changed): on top by the run's practice, which the next run continues. The catalogue's tools are the repository's own
`tools/`; the harness's (`v2.py`, `show.py`) are taught by each session's protocol and held by no base.

**Each part on its own schedule (the owner, 2026-09-23 evening).** "The rule needs to be revised - the layers must be
ordered by churn and dependency and so update cschedules also should differ." and "And then sometimes consolidation
for the lower parts rather than carrying their changes in a higher layer." The refresh rule (D7) kept one account for
the whole chain — what the delta had cost since the chain sealed, against rebuilding from the lowest part whose
sources changed — and counted any part holding a generated index as changed at every refresh. With the appended
indexes placed low, every refresh would have started there (about 192K where the theory map's refresh loads 69K), and
a refresh reset the one account, so a low part's appends would either force every refresh or never be consolidated.
*Decision*, the same rent-or-buy rule per part: the delta's text is counted by the part holding each change
(`manifest.delta_parts`, recorded with the delta), each fork records the shares of the delta it carries
(`v2.delta_shares`), each part keeps its own account from its own load (`watchdog.carried_parts`: a fork's cost,
0.1 a token a request, and each delta build's write, 2 a token, divided by those shares), and a refresh starts from
the lowest part whose account, with those of the parts over it, has reached what loading them again costs
(`watchdog.refresh_plan`, `base_stack.suffix_costs`, `base.sh WHO layer --from PART`). The parts under it keep what they
loaded — the builder reuses them warm on the same parent whatever changed in their sources — and their changes stay in
the delta; so the theory map and the tools are refreshed often, the direction and the inventory when their own changes
have paid for it, and a refresh from a higher part leaves a lower part's account running. The stable part's account is
kept the same way, in place of a fixed 15K line; when it has paid for loading the base again it is said to the owner,
whose reload it stays (the owner's word of 2026-09-19, "The base rebuild itself is the owner's"). For the owner: whether
the stable part's reload should also follow the rule by itself.

On REASONING_REUSE.md the owner added: "Ok that does make sense reasoning reuse should be heavily modified as it should
be mostly redundant due to faulty previous reasoning and generalization." Its place follows its modifications, as it
stands; the owner's words are in the first planner's note, since revising it is the library's work.

**The delta as a chain, and the stable part by the rule (the owner, 2026-09-23 evening).** "delta is rebuilt once at
least 4k tokens - does this make sense if we do append only and then refresh it in every rebuild that makes for a lot
of waste no - should the delta not be layered(maybe just two layers I'm not sure)? Also the 4k number needs to somehow
depend on the size of the delta. should the stable part's reload also follow the rule automatically once its account
has paid - yes and retire them yourself." A delta build forked the chain's top with the whole change text, so every
rebuild wrote every earlier change again; the line for a build was a fixed 4K tokens moved, looked at every 20
minutes. *Decision.* Not two layers but a chain of messages each written once: the consolidated message over the
parts, then increments, each forking the one before with what changed since the chain's messages took each file in
(two layers would write the upper one whole at every build — the same waste, smaller). The fixed line gives way to
rent against purchase: a message is built once what the pending changes have cost the forks started since the last
(each is told only which files changed, and holds a change by reading it: 2 a token, then 0.1 a token a request)
reaches what the message costs (2 a token, over one read of the prefix it forks, 0.1 a token) — so how much waits
depends on the prefix and on how often forks come; measured every five minutes. The chain is written anew as one
message once the forms its increments superseded have cost the forks what that costs; only its top is forked, so only
its top is kept warm. A role's churn takes the chain's messages after the one it holds, forking itself. The stable
part's reload follows the rule (`--from stable`: the stable reference loaded again, every part over it rebuilt).

*The documents.* The owner said to retire them, then, as the plan's absorbing them was being prepared: "native_control_plan.md no do not do that. That changes what the goal is" and "Do not carry it into native_control_plan.md it is the current plan with a current scope."; asked which to retire, the owner chose the two nothing current cites. ADMISSION.md and proposal.txt are deleted from the working tree (uncommitted, the owner's; README.md's one link to ADMISSION.md points at git history); plan.md, OBLIGATIONS.md and GENERALIZATION_REVIEW.md stay, cited by the plan. The review had understated the two plans: OBLIGATIONS.md tracks 85 obligations of which 44 are open or partial, stated in plan.md.

Two corrections found reviewing the chain before its installation: a message's cost includes rebuilding the reasoning
layers of the roles that judge over the chain's top (reviewer, designer, task designer), which each new top makes due
(`watchdog.judging_layers_cost`); and a chain standing on parts refreshed since is orphaned, its recorded texts not
measured from (`manifest.stack_held` checks the layer as `v2.delta_record` does), so the next message is written whole.

**The refresh logic reviewed with every part of the layering it touches, before installation (the owner, 2026-09-23:
"do one more review of the logic for refreshing the layers its adequacy and coherence before we deploy it. make sure
it works with every other part of the layering machinery").** Each consumer of the chain and of the delta was read
against the new rules. Found and corrected: the sweep of old delta texts kept only the chain's top message — a churn
built whole reads every message, so the chain's earlier ones are kept (`v2.tidied`); `moved_since_delta` compared the
top increment's text with a whole delta built now, meaningless for a chain — removed with its console use, the
pending measure in its place; the console's follower took its first reading of its sources after it began serving,
so a change made in between was taken for the start and never followed (the console test's intermittent failures) —
the reading is taken in `main` before anything is served. Found coherent: a change of a list's structure still
rebuilds the chain whole before any per-part rule is looked at (`refresh_reason`); forks of each message are told only
what changed after it (each message's own snapshot); only the top message is forked and pinged; the snapshots of
every part a fork holds are kept; a refresh from a part keeps the parts under it warm on their parent, and a cold one
under it is loaded again with everything over it (costing more than priced, as a cold entry must be written anyway);
the three rules — a message, the chain's consolidation, a part's refresh — price alike (a token read 0.1, written 2)
and each counts what it makes due (role layers standing on the chain for a refresh, the judging roles' layers for a
message). Limits kept in view: a delta build's write is divided among the parts by the standing delta's shares, and a
churn's write goes to the top part; the pending rule counts every fork as reading every pending change, an upper
bound that brings a message somewhat early; after a refresh the judging roles' layers are built over the chain's top
and again over the next message, as before. *For the owner:* max runs without a delta (decided 2026-09-22: four forks
a day, a delta's builds not worth it), so none of this applies to it — its parts are refreshed together once 20% of
their held text has moved, from the lowest part changed, which with the decisions index now in its direction is its
direction. With a message built only once its pending changes have paid for it, a delta over max would cost nothing
while its forks are few; switching max to deltas brings it under the same schedule.

**Consolidation and forking, the whole graph (the owner, 2026-09-23: "Is the logic for consolidation/forking adequate
and coherent? and yes you should switch.").** For each way the forked state moves — a new message, the chain written
anew, a refresh of the parts — every session was traced that moves with it at once, and every fork it relieves. What
moves at once: new forks (they fork the new top); the judging roles' reasoning layers standing on the delta (built again
at a new top); every role layer at a refresh; and the knowledge base, built again whenever what max's roles fork
changes (kb_care's `rebased`) — which no rule counted. The accounts were short as well: a fork recorded the delta it
carries only when its origin was a base or a role layer or churn — a planner, forked from the knowledge base, carried
max's delta in every request and counted for nothing; and a fork recorded what is pending only when it forked the base
itself, though forks of a judging layer and of the knowledge base are moved onto the next message as surely. *Decision*,
one principle for all three rules: a rule's cost counts everything its event moves at once, and its account every fork
that move relieves. The knowledge base records what building it costs, and max's message, rewrite and refresh count
it (`watchdog.kb_cost`); the rewrite counts the judging layers as a message does; a fork of any session carrying the
delta carries it (`v2.launch`); a fork whose origin moves with a base's next message — the base, a judging layer on its
delta, the knowledge base for max — records what is pending there (`v2.top_rider`). Churns move by their own rule (a
fork behind its churn is weighed there), so they are not counted in a message's. Max is switched to deltas (the
owner's word): it comes under the same schedule, the knowledge base with it.

**The arithmetic review's fixes, and the judging roles' churn (the owner, 2026-09-23 ~22:10, answering "Should the
judging roles move to churns over their layer, with re-reasoning at consolidation and refresh?": yes).** *The judging
roles*: their layer reasons over the chain's top as it stands when built, records the chain (`digest`, `stack_base`,
`stack_len`, `delta_size`) and stands while that chain stands (`v2.layer_stands`: its origin one of the chain's
messages); the chain's later messages are a churn over it, grown from the layer itself by the churn's rule (a fork of
the layer behind the top counts in `behind_forks`); the chain written anew or orphaned by a refresh makes it due. A
message no longer counts their rebuilds (`pending_paid`); the rewrite and the refresh still do. *A* — a pending change
costs a fork its write (2 a token) and a message spares only that: carried after, it costs the same in either place;
`pending_paid` charges 2 a pending token a fork, and `STALE_READ` is 2. *C* — a part's account is its own load's
waste: its old forms carried (0.1 a token a request, `manifest.old_forms` recorded in each message and inherited by
forks, churns and judging layers), and its changes written again at each whole rewrite (`state/WHO-delta-builds.jsonl`,
a churn's `whole_parts`). *D* — the refresh starts where the accounts from a part up most exceed its cost, the stable
part one candidate among them. *B* stays an explicit assumption (every fork reads every pending change). Found while
making these: *the riders* — with every role on a reasoning layer, no fork of high recorded what is pending (only forks
of the base itself, of the knowledge base and of the judging layers did), so high's messages would never have paid and
its churns never grown: every fork descending from a chain now records it (`top_rider` walks the origins); *the sweep*
kept only the top message's snapshot, and a judging layer serving across increments tells its forks what changed since
the message it forked: every message of a standing chain, and every standing layer's origin, keeps its snapshot; *a
churn's digest guard* was redundant with what holds the chain to its top, and kept a role on its bare layer after its
churn was let go (idle past its pings' worth) until the delta moved: removed. Validated: suite 869, mutation check
1078 caught.

**The simulation of the run of 09-21/22 (the owner, 2026-09-23 ~22:10: "build a simulation from the existing data and
execute the current machinery on it fully end to end to evaluate its adequacy and coherence and economics and
logic").** The machinery run for real — base.sh, base_stack.py, manifest.py, select_base_load.py, v2.py's launch, role
layers, churns, knowledge base and sweep, watchdog.py's holds, layers and deltas, the daemon's pings — on a simulated
clock, over main's 339 commits of 09-21 21:50 – 09-22 23:00 at their times and the run's 315 recorded sessions of the
forking roles, a fake claude answering with the prompt cache modelled (notes/sim; its findings, assumptions and the
comparisons in notes/sim/FINDINGS.md). What it found in the machinery, and its corrections: *the generated indexes*
the parts hold were made only by a build, so every rule was blind to them — the theory map's rows, what changes most —
and forks were not told they had changed: they are made again for each commit of main (`watchdog.held_indexes`);
*a judging layer over the parts* was made due by the chain's first message (the rebuild the judging churn was to
remove) and its forks never counted behind: the parts the chain stands on count as held (`layer_stands`), and a fork
is behind whenever its origin's digest is not the top's; *warm entries judged cold*: the layer's entry was read by
the base's mark, which nothing touches once every role has a layer, and a part's by the mark only a build sets — the
high layer and its stable base were loaded again at 00:47 with two role layers, every entry warm: an entry's age is
now its latest read under any mark naming it, and an OK ping marks the entry's own.

**What the simulation showed of the economics, and two more corrections (2026-09-23 night).** Over the day of 09-21/22
the harness deployed before tonight cost 528.7M (input-equivalent), the round of 22:46 537.5M (warm entries judged
cold: stable reloads doubled; indexes invisible), the round of 23:17 531.5M — about 92% of each the sessions' own
work, 57% the prefix every request carries, upkeep 5–9%. What moved was freshness: a fork starts lacking 2,061 tokens
of the held content on average against 7,224, and is told exactly what it lacks (125 of 282 forks were not). Two
corrections from it, in this round: *every churn by its rule* — an executing role's first churn was built at once, and
the investigator's twice in the night for no fork, 71K each; forks of a bare layer now count behind, and the first
build is priced as it is; *a part pinged while worth keeping* (`base_stack.worth_keeping`) — pings of every part of
every base were 17M of the day's 41M of upkeep, while no refresh read an intermediate part. With both the day costs
519.0M (upkeep 30.4M, pings of the bases' parts 9.2M against 17.2M), a fork lacking 2,774 on average (the churns wait
for their rule). The comparisons, the checks and what the model assumes: notes/sim/FINDINGS.md. For the owner: with
every role on a layer, 8 of 15 delta messages were forked by nobody (the churns take their text) — a message could be
a text for the churns, a session only where something forks it; and role layers cost about 20M of the day (4%), a
price for a priming the simulation cannot measure.
