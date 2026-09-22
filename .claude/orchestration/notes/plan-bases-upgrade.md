# The bases, their layers and what the roles are given: the upgrade of 2026-09-22/23

The owner, 2026-09-22 ~23:00, leaving for a while: review the bases — their content, their layering, how they were
used — against the data of every session run today; decide how to optimize for cost and, most of all, for the quality
of the content produced; fix every issue found (those already seen included); write this plan first and improve it
while implementing; test everything with tests and mutation cases; back every decision with data; leave the repository
ready for the owner to build and seal the bases and restart the run with `--fresh`, with the first planner's charge
considered. Then, if there is time: every session, prompt and protocol for read/write batching and information
delivery. And reason through a further layer that primes a role (the role's material interpreted before any task),
on top of the delta or elsewhere, by what it costs. Everything coherent and adequate, shown to be so before it is
implemented. Tasks divide the work; this file keeps the decisions and is updated as understanding grows.

Rules for this work (standing): no commit of the run's own state; every command sandboxed; no subagents; the run
is stopped (state/stopped 22:37:06), so harness files may be deployed directly after the dev-copy cycle (dev copy
`$TMPDIR/dev/orch` → tests → mutation cases → `notes/run-tests.py` → backup `state/dev-patches/predeploy-*` → live
→ `notes/v2-build-handoff.md`). Commits at milestones, owner's style, no attribution.

## Cost model (confirmed 2026-09-22 from the pricing reference)

Input-equivalent tokens: cache read 0.1, 1-hour cache write 2 (every write here is 1-hour: 92.6M 1-hour tokens and
none of 5 minutes in the last 60 transcripts), fresh input 1, output 5. A read refreshes an entry's hour. Every request
of a fork reads its whole context from cache, the base prefix first: a base token costs 0.1 per fork request.

## Tasks

Status: `[ ]` open, `[~]` in progress, `[x]` done (with where), `[-]` decided against (with why).

1. [x] Data: every session of 2026-09-22 — role, base, requests, cost anatomy (first write = launch text, base read,
   own growth, output), what it read (source, size, whether its base held it). Dataset `state/analysis/`.
2. [x] Data: each base's content by part and section (stable, layer, delta), tokens; which sections forks re-read,
   which files forks read that no base holds; the frontier's measure against a day of sessions instead of 7.
3. [x] Decide: per base, the budget and the inclusion rule (what holding a section costs a fork against what it
   saves it, and what quality needs held regardless); the layering rules (refresh by carried cost, delta rebuild
   threshold, stable drift); the generated indexes; the memory directory.
4. [x] Decide: the role-priming layer (the owner's suggestion) — cost and quality, placement, against the
   alternatives (the role text in the first message, as now).
5. [x] Implement: the frontier chosen within a token budget, from a day of sessions, by the cost rule; a layer seal
   over target said (base.sh), the base target checked for split bases.
6. [x] Implement: the layer refreshed when the carried cost of its delta reaches a refresh's cost; the frontier
   trigger gone; DELTA_MIN from the data; stable drift apart.
7. [x] Implement: the load lists (max, xhigh, high) as task 3 decides; the indexes.
8. [-] Implement: what task 4 decides (D9: no priming layer); the launch texts are task 11's.
9. [x] Fresh start: the first planner's charge (FRESH_CHARGE) for this run; the in-flight work carried (trees of 44,
   278, 192, 279, 276; 128 and 147 committed by rule); the build/seal/start sequence written for the owner; xhigh
   switched to deltas if task 3 decides it.
10. [x] Tests, mutation cases, suite, deploy, handoff note, commit (3f758c6b, edf999cb and after; the suite 701 on the live code).
11. [x] Then: every role's sessions for read/write batching and information delivery; every protocol and prompt (below).

## What it is worth, at 2026-09-22's volume (435M input-equivalent, 94 landings)

- Smaller worker bases: high 601,541 → ~530K, xhigh 542,564 → ~460K; the base-prefix reads were 169M (high roles)
  and 75M (xhigh roles): about **20M + 12M a day**, with the budgets now holding what the roles used.
- The reviewer's first read in its first message: about **5.4M a day** (a request of 109), and each review a turn
  sooner on the landing path.
- Layers refreshed by carried cost instead of about hourly: at ~700K (high) and ~540K (xhigh) a refresh, roughly
  **4–5M a day**; xhigh's forks told only what changed after its delta.
- Deltas built at 4K moved: about **1–2M a day**.
- An accepted task left in review committed by rule: the orphans of the day cost **~5M** in pings alone, and held
  the head of the planner's order for eight hours.
Together about 45–50M a day, some 11%, before the quality gains: frontier theories used by 17.6% of forks where the
held ones averaged 13.3%, xhigh's frontier from 40 to 55 theories in use, and no reference the roles never used.

## For the owner: build, seal and start

The lists are ready (high and xhigh name a new stable reference; max's is unchanged but its entry is cold). One command
a base does all of it now — the layer build reloads the stable base itself when the list names another reference
(manifest.py stable-listed) or its entry is cold, then selects the frontier within the budget, loads and seals:

    .claude/orchestration/base.sh high layer
    .claude/orchestration/base.sh xhigh layer
    .claude/orchestration/base.sh max layer
    .claude/orchestration/start.sh --fresh

(`base.sh WHO restable` then `base.sh WHO layer` is the same in two steps.) A layer sealed over the 530K target says so
in state/warm.log. Deltas are on for high and xhigh (state/deltas); the watchdog builds each base's first delta once
4K tokens have moved (D11). The first planner receives the fresh charge (FRESH_CHARGE, now naming the task trees) and the
note `notes/fresh-start-2026-09-23.md`, queued as an event: what changed in the harness, what is in flight in which
tree, and the two trees whose work never landed (143, 176). To start without that note: remove the event of kind
`harness-change` from state/v2.json.

**Yours to read**: `library-prompt.md`, the system prompt of every base, now says which founding theories a base holds (every one on the planner's base, those its roles use on the others, the rest named in an index) — it said every base held all of them, which the founding tiers made false; you read changes to that file (bases-design §9).

**Yours to decide** (data in D3, D5): whether the central ideas nobody used in a week stay pinned ("authority and
currentness", "proofs and replay", "admission", "base causes": 0 sessions); whether the theory map's index (77K on high
after the cut) stays, or the names-only index (18K) replaces it; whether the 530K target itself stays (at 2026-09-22's
rates every 10K of a worker base costs its forks about 150K an hour on high, 70K on xhigh).

## Task 11: what the sessions show (read/write batching, information delivery)

Examined on the day's 6,669 tool calls (reports J–M), and what came of each:

- **Refusals and failures.** 369 over the day, but the largest classes belong to rules since changed: all 43 refusals
  of a change joined to other commands fell between 00:14 and 09:40, before the owner's "any batch of commands" (the
  guard allows it now). On the evening's harness (from 18:00) about 25 of 1,015 calls failed or were refused, several
  of them only output containing the word, the rest scattered model slips. No class left to fix.
- **The reviewer's first batch.** Every reviewer (104 of 104) opened with `read result log probes diff`, a request
  each before it could judge: now given in its first message (v2.first_read). About 50K a review on xhigh.
- **Orientation.** Implementers make their first change at request 7 of 33, reviewers 5 of 9; before it they read the
  theories they edit (96%), DECISIONS.md entries (65%; ranges 113 times, greps 44, the end 40), THEORY_MAP rows (43%).
  Briefs cite decisions informally ("the verdict entry's Affordability subsection"), so no delivery of them is sound
  without a brief form that names headings exactly — the planner's form, put to the owner. Entries are added through
  drafts mostly (30 direct changes to DECISIONS.md in the day, one refused): an `append` verb would save little.
- **Files a brief names** (`.build/tasks/*`): fixers read 47% of those their brief names before the first change,
  implementers 30%; delivering all of them would put about two files into each launch, half unread. Not done.
- **The launch texts** are 22–36K characters, 38–55% shared by a role's forks. The checks section goes to reviewers
  too, and 10 of 109 ran a probe or a check with it: kept.
- **Pings of held sessions**: 108 in the day, 11.7M, 3.3M of it implement-147 held and orphaned from 11:33 (fixed,
  0dbcd1e7) and most of the rest before the one-miss rule. The hold limits (3 hours for a parked worker, the owner's)
  sit at the break-even of holding against restarting (a ping about 70K, a restart about 200–300K). Kept.
- **Stale lines** (D11): forks name 17% (high) and 8% (xhigh) of the files their stale line lists: DELTA_MIN 4K.

## Decisions (with their data)

(A decision revised later keeps its first form, struck through, and says why. Data: `state/analysis/` — the datasets
`sessions-*.jsonl`, `names-*.jsonl` (notes/session-data.py) and the reports `report-A…I`.)

**D1. What a base is for, and its budget.** Reading the base prefix is 62% of all the run spent on 2026-09-22 (435M
input-equivalent: implementers 71% of their cost, fixers 69%, investigators 77%, reviewers 56%). A held theory pays
for itself in tokens alone only if a large share of forks need it (holding costs 0.1 × tokens × requests per fork;
getting it on demand ≈ 7 × tokens for a fork that needs it — its source is read, written at 2 and re-read — so the
break-even share is 0.1 R / 7: 41% on high, R = 29; 16% on xhigh, R = 11.5), and the frontier's theories average 13%.
So the base is a quality instrument — knowledge in context without depending on a fork's reading — and its budget,
the owner's 530K (bases-design §12), is to be spent on the content most likely to be used, per token, with a floor
under which nothing is held however much room remains (5% of the forks: about 3 of 60).

**D2. The founding tier (high, xhigh): only what is used.** Over the week to 2026-09-22 (347 library sessions:
163 implementers and fixers, 157 middle roles; report-E), 176 of the 226 founding theories (144K tokens) were used by
none of the implementer family and 175 (146K) by none of the middle roles; 13 and 15 more by one session. No review
of 110 blamed a duplication on a founding notion that was not known (all 20 reviews naming a duplication name one within
the task or map rows a merge doubled). Kept: those used by at least 2 sessions of the base's roles over the week
~~(37 for high, 36 for xhigh)~~ and left unchanged by main for 3 days — 27 for high, 26 for xhigh: a founding theory in
use can be work in progress (13 on high had changed that day), and the stable part stands until the owner rebuilds it,
so the frontier holds those (findings 23:42); the window reaches into v2's archive (findings 00:23). The rest stay findable: on high each re-enters the theory map's index (which leaves out only
what the list holds); on xhigh a generated founding index gives each its map line. The founding theories were chosen by
a naming heuristic (idea_candidates.founding_theories: the first theory whose name carries a word several theory names
share), not by use. max is left as the owner chose it (founding theories at definitions; 20 forks a day; bases-design
§12 A).

**D3. The central ideas are the owner's pins and stay.** Their use over the week is put to the owner (report-E):
"structure without names" and "positive meaning" are used by up to 38 sessions a theory, "artifacts" and "index
notions" regularly; "authority and currentness", "proofs and replay", "admission" and "base causes" by no session in a
week; "presentations", "loci", "history" and "the generalization machinery" by a handful. Whether to keep all of them is
the owner's.

**D4. The frontier: chosen within the layer's budget, by use per token, from 60 sessions.** At each layer refresh
(select_base_load --frontier) the frontier is the theories outside the stable part that the last 60 sessions of the
base's roles used — a session uses a theory when it reads it or its own writing names one of the names the theory
defines (report-D) — ranked by use per token at the list's level and taken until the layer's budget (the target less
the stable part as measured, the layer's fixed entries and its session overhead) or the 5% floor. It was a fixed 40
theories measured from 7 sessions (which collapsed to 1 of 40 on 2026-09-20), with no budget: the high base grew
524,836 → 601,541 in a day (report in the findings). ~~Simulated on 2026-09-22: high about 45 theories (mean use 17.6%
against 13.3% for the 40 held), xhigh about 68, both totals near 530K.~~ Chosen: high 71 theories within its 273K room
(the room grew as the founding tier shrank and the index was cut), xhigh 55 — every theory 5% of its forks used, the
floor binding before its 223K room; estimated loaded high ~529K, xhigh ~461K, and the packs verify (findings 00:30).

**D5. The theory map's index (high) is capped at 90 characters of first clause.** It is 100.9K tokens of the high
layer (31%) where the design measured 56K (1,462 rows, 2026-09-19); 1,772 rows now, median 138 characters, growing with
every theory. Capped at the whole word under 90 characters of clause it keeps every theory and the opening of what it
holds, about 77K. A names-only index (theory-names.md, 18K) would save about 0.9M an hour more at today's rate: the
owner's to decide, since the index is the owner's C″.

**D6. A layer sealed over the target is said** (base.sh), so a base that outgrows the owner's target is seen when it
happens rather than a day later.

**D7. The layer is refreshed when its delta has carried a refresh's cost.** Carried: for every fork of the delta since
the layer sealed, 0.1 × the delta's tokens × the fork's own requests, and 2 × each delta build's write; a refresh costs
2 × the layer's tokens + 0.1 × the stable part's. The frontier trigger (FRONTIER_MOVED, which asked a refresh 1h24m after
the last, the old whole-file pace) and the 8% share rule go; a cold layer entry, a missed fork and a refresh asked by hand
still refresh. The stable part's drift is not counted (a layer refresh does not remove it); its notice to the owner at
15K stays. Optimum at 2026-09-22's rates: every 3.5–5 hours.

**D8. xhigh runs on deltas** once D7 is in: its forks carry a delta at half high's per-token cost (71 requests an hour
against 151) and its whole-file rule refreshed it every 1–1.5 hours.

**D9. No role-priming layer (the owner's suggestion, reasoned through).** A role's launch text is 22–36K characters, of
which 38–55% (about 3.3–4.6K tokens) is the same in every fork of the role (report-H); a layer holding it would save
at most about 8K tokens of writes a fork (high: about 42K an hour) and cost, per role, a rebuild at every delta build
(about 69K: the delta's prefix read and the role text written), or, placed under the delta, one delta per role. The
orientation it would shorten is task-specific: forks read for a median of 5–7 requests before their first change
(implementers 7 of 33, reviewers 5 of 9), and no role-level text can read the task's files in advance. An interpretation
written by the model and held as context would stand in every fork as if it were a source, and go stale with each
delta. It would pay only with several times today's forks per role and deltas rarer than one in two hours.

**D10. MEMORY.md is not held** (the memory files are): the index repeats their descriptions and, being one file, enters
every delta whole when any memory changes (1,118 of the 2,066 tokens of the high delta at 22:36). The lists hold
`memory/[a-z]*.md`; memory files are named in lower-case kebab-case.

**D11. DELTA_MIN is 4K.** ~~Stays 2K until the share of changed files a fork actually reads is measured.~~ Measured
(report-M): of the files a fork's stale line listed, high forks named 17% in their own calls (24% as forks of the
layer), xhigh forks 8%. A delta build costs the layer's read (~60K) and its write; what it buys is those re-reads, so
the optimum is a build every ~44 minutes on high (~3.7K tokens moved) and ~62 on xhigh (~5.2K). One threshold of 4K
serves both (the cost is flat near the optimum); the 20-minute floor stays.

## Findings log

- 2026-09-23 00:30 pre-flight: `base.sh WHO pack` for both parts of high and xhigh builds and verifies (high stable
  71 sources / layer 114, xhigh 70 / 108); high's layer holds the capped theory map index, xhigh's the founding index,
  neither MEMORY.md.
- 2026-09-23 00:23 the evidence window reaches into v2's archive (a session goes there a day after its release):
  founding tiers chosen again, high 27 (133 sessions), xhigh 26 (156).
- 2026-09-23 00:21 library-prompt.md said every base holds the founding theory of every notion: corrected (yours to
  read). 00:03 a layer was built over the recorded stable base whenever its entry was warm, even once the list named
  another reference (~665K on high): manifest.py stable-listed. And `date -d ""` is midnight today: a base record
  with no seal time made yesterday's misses look answered after midnight — found by the clock, fixed.

- 2026-09-22 23:42 the selection deployed (select_base_load --founding / --frontier, handoff 23:42); the lists
  rewritten: high 530K and xhigh 457K estimated. Found while doing it: a theory that entered the founding tier and had
  been in the frontier was chosen again (the frontier counted "elsewhere" by name): now by position. And a founding
  theory in use can be work in progress (13 on high, changed today): the founding tier keeps only what main left
  unchanged for 3 days, the frontier holds the rest — the stable part is rebuilt by the owner only, and a change there
  stands in every delta until then. Consequence: high's layer grows to ~389K measured, a refresh ~780K; D7's rule sets
  the refreshes by it.

- 2026-09-22 22:50 `notes/delta-measure.py` counted the requests a fork's transcript copies from its origin, and
  weighted writes at 1.25: fixed (own requests only, writes at 2). Corrected: a high layer refresh ~644K, xhigh
  ~536K, max ~362K; a delta build ~70K; high's upkeep before the delta 341K/hour.
- 2026-09-22 23:00 the high base is 601,541 tokens against the 530K target: the layer grew 251.7K → 325.2K in a
  day (frontier turned over to larger theories +41K; generated indexes and tool digests +16K, the THEORY_MAP index
  alone +9K; kept theories grown +16K); the stable part +3K. The frontier is re-picked as a fixed 40 theories with no
  token budget (select_base_load.frontier); the budget applies only to the full regeneration, which no layer refresh
  runs.
- 2026-09-22 22:45 fork load: high 151 requests an active hour (5.2 forks × 29), xhigh 71 (6.2 × 11.5; 109 of 136
  forks reviews at 8.9 requests). A base token costs high's forks 15.1 an hour, xhigh's 7.1.
- 2026-09-22 22:40 the frontier trigger (FRONTIER_MOVED 5) asked a refresh 1h24m after the last one, the old whole-file
  rule's pace; the delta held 2,066 tokens of which 1,577 were the memory directory (MEMORY.md enters whole).
