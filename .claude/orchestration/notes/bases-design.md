# The bases: what they hold, for which roles, and what is to be decided (2026-09-19)

First version: session f4318413. Revised in session 212840df after the owner's answers to its nine decisions: the
answers are recorded in section 12, the owner's four questions (5 to 8) are answered in sections 7 to 10, and two
errors of the first version are corrected (section 0). A draft of this revision also claimed that the forks of a
layer do not keep the stable base under it warm; the measurement of 2026-09-18 shows they do (section 8). The owner's
directions: work on the base context in depth; start with the planner and knowledge base's base and reduce it to about 500K; design the bases of the xhigh tier
(designer, task designer, investigator, reviewer) and the high tier (implementer, fixer) and judge their adequacy for
their roles; the order in which a base presents its material matters (the most recent tokens weigh most); the base
rebuild is the owner's. Nothing here is built as a base: these are the designs, the measurements, the drafts and the
decisions.

## 0. Corrections to the first version

1. **Sizes.** The first version multiplied the pack's estimates by 1.063 to calibrate them on the present base, but
   the pack's ratios had already been recalibrated on that base: its frozen pack now estimates 560,298 tokens against
   560,299 measured. Every "measured" size there was about 6% too high (A″ was 462K, not 493K; B 581K, not 620K).
   Every size below is the loaded estimate of a real pack built from the design (`base_pack.py build`), which is
   calibrated.
2. **Reading cost.** A fork reads its whole base from cache at 0.1 of its size on every request. At about 120 requests
   an implementer session, a 560K base costs 6.7M plan-equivalents in base reads, not 0.67M: about six times the
   session's output (about 200K output tokens weighed five times, 1.0M), not the same order. Base size is therefore the
   largest cost lever for the roles that make many requests (implementer, fixer), and 10K of base costs about 0.12M per
   implementer session.

## 1. What a base is for, and what it costs

A base is the context every fork of it starts with: its system prompt, then the loaded library, then the fork's own
first message (its protocol and its piece of work). It sets direction and saves orientation; it is not a lookup cache.
What a session has in view is what it thinks with, so a base holds what its roles must reason from, and leaves to a
gather (`v2.py step`) what a piece of work needs in detail.

- **Room.** A fork's room for work is the notice (907K; 947K since 2026-09-23 evening) less the base less its first message (about 20K).
- **Reading.** 0.1 of the base per request of every fork: 40K a request at 404K, 54K at 536K; about 4.8M and 6.4M over
  an implementer session of 120 requests.
- **Writing.** The present base's build, measured from its transcript: 1.56M (writes 1.11M, reads 0.39M over 16
  requests, output 0.06M) for 560K. A cold base is written again at 2.0 of its size after every hour nothing read it.
- **Staleness.** A fork that reads a held file again because its held copy is stale carries it twice for the rest of
  its session: about 2 of its size to write it and 0.1 of it per remaining request, about 12 times its size over an
  implementer session. Reading the present plan (59K) again costs about 0.7M.

## 2. Method

- **Consultation evidence**: every file named in a tool call of the last 24 v1 implementer sessions (impl-8 to
  impl-31), how many sessions touched it and the characters its results pulled (`select_base_load.measure`).
- **Sizes**: each design is written as a load list and packed (`base_pack.py build`, 2 seconds); its loaded estimate
  and its tiers' shares are read from the pack. The throwaway harness is in session 212840df's scratchpad; the three
  drafts are packed and verified (`base_pack.py verify`) as they stand.
- **Digest levels**: *statements* (every statement), *definitions* (definitions verbatim, lemmas by name),
  *signatures* (built: a definition by its name and type up to `where`, its equations omitted), and *outline*
  (prototyped in the harness only: a definition by its first line, commentary by its first sentence).
- **Costs**: the build model is calibrated on the present base's build (it reproduces 1.55M against 1.56M measured):
  requests of about 4.75 chunks, each reading its prefix at 0.1, writing its new part at 2.0.

## 3. What is held now, by part (measured on today's sources)

| Part | Level | Tokens |
|---|---|---|
| theory names (1,797) | index | 16.6K |
| founding theories (226) | definitions / signatures / outline | 239.1K / 170.9K / 118.3K |
| central ideas (44 theories, the owner's pins) | statements / definitions | 103.6K / 56.1K |
| current additions (6, the 2026-09-18 refresh) | statements / definitions | 25.8K / 18.3K |
| working frontier (the 40 most consulted) | statements / definitions / signatures | 140.9K / 104.4K / 72.5K |
| check and measurement tools | 14 / the check workflow's 8 | 11.4K / 7.4K |
| decision index (generated) | 155 decisions / 194 after the condensation | 7.2K / 9.4K |
| theory map index (the theories a base holds left out) | index | 56.0K |
| REASONING_REUSE.md | before / after the condensation (section 10) | 49.3K / 33.6K |
| native_control_plan.md | before / after the condensation (section 10) | 58.9K / 22.8K |
| the owner's words and the operating rules | whole | 24.1K |
| HANDOFF.md, owner-ledger.md | whole | 2.2K, 3.4K |

No tier overlaps another (a file listed twice is held once, at its first tier's level; none is). The present base
(32f5e011, 560K) holds the owner's words first and the generic founding theories and tool digests last, the v1
implementer's system prompt, and 36 files that changed since it was loaded.

## 4. What the roles need

| Role (base) | Must reason from | Reads in detail by gathering | Room it needs |
|---|---|---|---|
| knowledge base (A) | the owner's words, the principles, the plan, the reasoning, the decisions, what exists | nothing: it holds; its forks gather | its forks' |
| planning episode (A) | the same, and HANDOFF.md, the ledger, the notes (from the knowledge base) | statements, results, verdicts | 150K |
| designer (B, since the owner's answer 1) | the owner's intent, the plan, the reasoning, the decisions, the library's ideas and the working frontier | the statements and definitions its decision touches | what its base leaves (no cap) |
| task designer (B) | the plan and the decisions, what exists and its statements, the check workflow | statements of the node's area | ~150K |
| reviewer (B) | the principles and settled distinctions, what exists at the level of its definitions, the central ideas' statements | the task's diff, result, log | ~150K |
| investigator (B) | the check and measurement tools, the working frontier, the plan's current area | logs, profiles, sources | ~250K |
| implementer, fixer (C) | the principles and lessons, what exists, the central ideas' and the frontier's statements, the check workflow | the sources it edits, the facts it uses | ~350K |

The v1 evidence: reading pulled 3.3M characters in 24 sessions (theories 2.2M, documents 0.6M, tools 0.5M); read in
nearly every session were `tools/probe_theories.py` (24), HANDOFF.md (24), `tools/incremental_check.py` (22),
THEORY_MAP.md (21, 204K pulled), native_control_plan.md (21) and REASONING_REUSE.md (20), the last two although the base
held them, because the held copies were stale.

## 5. The designs as decided, measured

Rooms are before the notice (907K then; 947K since 2026-09-23 evening), less a first message of 20K. Loaded in chunks of 120,000 bytes (section 11) the
decided designs measure about 11K less: A 470K, B 519K, C″ 524K, loaded in 11 to 12 parts instead of 70 to 76 (the
rows below were measured with 20,000-byte chunks).

| Base (effort) | Design | Loaded | Room |
|---|---|---|---|
| **A** planner, knowledge base (max) | A″ with the plan and the reasoning as they are | 462K | 425K |
| | A″ with both condensed (section 10) | 404K | 483K |
| | **the same, founding theories at definitions (the owner's choice)**: measured after the condensation | **481K** | 406K |
| **B** designer, task designer, investigator, reviewer (xhigh) | B with the plan and the reasoning as they are | 581K | 306K |
| | **B with both condensed**: measured after the condensation | **530K** | 357K |
| | the same, central ideas at definitions (B*) | 475K | 412K |
| | the same, the frontier at signatures | 490K | 397K |
| **C″** implementer, fixer (high) | **map index, founding at signatures** | **536K** | 351K |
| | map index, founding at outline | 482K | 405K |
| | map index only, no founding tier | 367K | 520K |

**A″**: the theory names, the founding theories at signatures, the central ideas' statements, the decision index, the
reasoning inventory, the plan, the owner's words last; the current additions dropped. Under the owner's aim of about
500K already (462K); condensing the plan and the reasoning inventory takes it to 404K. The owner chose the founding
theories at definitions (the planner and the knowledge base keep every founding definition's equations in view): 481K
as measured after the condensation, which leaves the knowledge base 276K to grow into before its 757K limit.

**B**: A's reference tiers, the working frontier at definitions, the 14 check and measurement tools, then the
direction tiers of A. At 581K before; with the plan and the reasoning condensed, 530K as measured, the owner's aim of
about 530K, with no other cut: nothing else in it is redundant by measure (no tier overlaps another; the theory names repeat the
names of the 310 held theories, about 3K). A design task has the room its base leaves, like every other kind (the owner removed the 230K cap).

**C″**: the theory map's index (1,462 rows: the theories C″ holds are left out), the founding theories at signatures
(section 7), the central ideas' statements, the frontier's statements, the check workflow's 8 tools, the owner's words
and rules last; no plan, no reasoning inventory. A build or fix brief states what of them it rests on under Decided, or
names the section its first gather reads; a task that needs more is a design task (`protocols/_brief.md`, added).

Draft lists: `base-load-max.txt` (A″), `base-load-xhigh.txt` (B), `base-load-high.txt` (C″); each packs and verifies
as it stands (462K, 581K, 536K; A and B fall to 404K and 523K once the plan and the reasoning are condensed).

## 6. Levers, measured

| Lever | Effect |
|---|---|
| order every base from reference to direction | no size change; steering where recency weighs most (the drafts do this) |
| founding theories at signatures instead of definitions | −68K (239K → 171K) |
| founding theories at outline instead of signatures | −53K (171K → 118K); section 7 |
| central ideas at definitions instead of statements | −48K; loses the lemma statements the owner pinned |
| current additions dropped | −26K; stale, and the knowledge base's HANDOFF.md and gathers carry what is new |
| the plan condensed (section 10) | −38K (59K → 21K) |
| REASONING_REUSE.md condensed (section 10) | −18K (49K → 31K) |
| the frontier at definitions (B) or signatures | −37K / −68K against statements |
| the decision index | +7K: the 155 decisions known by name |
| the theory map index | +56K (the held theories left out; implementers looked the map up in 21 of 24 sessions) |

## 7. Question 5: would signatures alone be enough (no outline level)?

Yes. Only the implementation base used the outline level (A and B hold the founding theories at signatures), and
there:

| C″'s founding tier | Loaded | Room | Base read per request | Per implementer session (120 requests) |
|---|---|---|---|---|
| signatures | 536K | 351K | 54K | 6.43M |
| outline | 482K | 405K | 48K | 5.78M |
| none (their map rows only) | 367K | 520K | 37K | 4.40M |

What outline loses: a definition keeps only its first line, which in this library is often `definition name ::` with
the type on the next line, and each commentary keeps its first sentence. With the map index beside it, outline adds to
the index little but the definitions' and lemmas' names. Signatures keep each notion's name and type and its whole
commentary: what reuse needs to know whether a notion fits, and what non-conflation needs to tell two notions apart.
The price of signatures over outline is 54K per request of every implementer and fixer, about 0.65M per implementer
session (11% more base reads), and 54K of room (351K against the implementer's ~350K). Recommended: signatures only;
the outline level is not built (it exists as a measured prototype). If the room proves short, the lever is the frontier
tier (141K at statements, to be re-measured from v2's own consultations), not a lossier founding level. The last row is
the cost bound: the whole founding tier costs the implementer 2.0M per session; dropping it leaves an implementer only
one line per founding theory to find what to reuse.

## 8. Question 6: a stable base with a frontier layer refreshed on its own

**The design.** Each base splits at the end of its reference tiers.
- **The stable base** (the owner builds it, rarely): what exists, the founding theories, the central ideas. A's is the
  theory names, the founding theories at definitions and the central ideas' statements (about 384K); B's the same with
  the founding theories at signatures (316K); C's the map index, the founding theories at signatures and the central
  ideas (357K). The system prompt belongs to it.
- **The layer** (the harness builds it): a fork of the stable base that loads the current frontier and direction, then
  is sealed; every role forks the layer. B's layer: the frontier at definitions, the tools, the decision index, the
  reasoning inventory, the plan, the owner's words last (about 223K). C's: the frontier's statements, the check tools,
  the owner's words last (194K). A's layer is the knowledge base itself: it loads the decision index, the reasoning
  inventory, the plan and the owner's words, then HANDOFF.md, the ledger and the owner's new words (about 109K), then
  grows by integration notes.
- **Totals**: A about 478K, B 530K, C 536K, the sizes of section 5: layering changes who refreshes what and when, not
  what a fork carries or pays per request.
- **Steering stays last.** The owner's words and the direction tiers are the layer's last part, so they stay last in
  every fork and are current at every refresh. The system prompt, fixed with the stable base, carries nothing that
  changes.
- **HANDOFF.md is read fresh, not held** in B's and C's layers: the planner rewrites it at every episode, so a held copy
  would be stale at once (the v1 implementers' HANDOFF.md, 14K to 19K tokens, changed in every one of the 30 commits of
  2026-09-19). A designer reads the current one in its first gather (2K now).

**Warmth.** The forks of a layer keep the stable base warm: every request of a fork reads a prefix that contains the
stable base, and the measurement of 2026-09-18 (README, "What keeps a base warm") showed a base read whole by a fork
started 456 seconds after its last direct hit, with a five-minute lifetime, while another fork worked on its own
longer context; after 400 seconds of silence a fork wrote it cold. So while a run is active the stable bases need no
pings; the warm daemon pings a layer (which also keeps its stable base warm) only while nothing forks it.

**Costs** (plan-equivalents, calibrated on the measured build):

| Operation | Cost |
|---|---|
| whole base built cold: A (474K) / B / C | 1.27M / 1.42M / 1.48M |
| stable base built cold: A's / B's / C's | 0.97M / 0.75M / 0.90M |
| layer refreshed on a warm stable base: A's (the knowledge base's rebuild) / B's / C's | 0.35M / 0.74M / 0.61M |
| the same on a cold stable base (after an idle hour; it is rewritten at 2.0 of its size first) | 1.12M / 1.37M / 1.33M |
| for comparison: one implementer hour | about 11M |

**How often a layer is refreshed.** Replaying the 30 commits of 2026-09-19 (01:21 to 16:55, v1's pace) against each
layer's held files at the level each holds them, with the plan and the reasoning inventory taken as condensed (they
change only with their structure): a refresh whenever the changed files make up 15% of the layer's tokens comes 6
times for B's layer and 7 times for C's in those 15.5 hours, 5 times each at 20% or 25%; that is every 2.5 to 3 hours,
every 4 to 6 commits, 8 to 10 times a day of continuous work, about 5 to 7M a day per layer. Per commit a median of
3K (B) and 4K (C) of the held files change, the frontier theories being worked on. The owner accepted this frequency.
Rule: the harness refreshes a layer at the start of a run and when the held files changed since it was loaded reach
20% of its tokens, checked after each commit; the knowledge base is rebuilt at its limit as before.

To build: the load lists mark where the layer begins; `base.sh` builds the stable bases of `max`, `xhigh` and `high`
(each with its list, `library-prompt.md`, its model and effort) and a layer (fork the sealed stable base, load the
layer's pack, seal, record it); `v2.py` forks a base's layer when its record exists, and the knowledge base loads A's
layer part; `manifest.py` snapshots and reports stale files per layer, with their share; the warm daemon pings layers;
the watchdog refreshes a layer by the rule; `health.py` reports each layer's stale share. The API lets Opus 5 change
effort by a message without invalidating the cached messages (a beta); if Claude Code ever passes effort that way, one
stable base could serve all three efforts.

## 9. Question 7: the system prompt

**What it is.** The text `base.sh` appends to Claude Code's own system prompt when it builds a base
(`--append-system-prompt-file`). Claude Code records it with the base session, and every fork (every episode, task
and consultation) inherits it: forks are started without the flag and still read the base from cache, which they
could not if their system prompt differed. It is rendered before all messages (tools, then system, then messages), so
it is the first thing in every fork's context and the most authoritative, and it is cached with the base: changing it
changes the prefix, so every base built with it must be rebuilt. In the layered design it belongs to the stable
bases.

**Why v2 needs a new one.** The present one, `implementer-prompt.md`, is the v1 implementer's. It tells every fork
that it is "the single implementer" and works alone with "no other agent to ask"; to read HANDOFF.md, the ledger and
the owner's new directions at its start; to keep HANDOFF.md current at every batch; to rotate with `impl_state.sh`
(deleted) near its window's end; to end a blocked turn with `impl_state.sh waiting`; to decide itself how many heavy
Isabelle runs go at once; and to commit only when the owner says. In v2 every role contradicts it: sessions consult
each other, the planner keeps HANDOFF.md, nothing rotates, the harness limits Isabelle runs, the finalizer commits.
Each protocol now opens by saying which of it does not apply (`protocols/_inherited.md`), in every first message, and
the contradiction still sits at the most authoritative place of every context.

**What the draft holds** (`library-prompt.md`, revised): that the session is one of many, forked for one piece of work,
its role and rules in its first message; the standing goal verbatim; what the base holds and in which order, for any of
the three bases, and that the projections carry no authority (read the source before editing or relying on a proof);
the glyphs and escapes; the stale list; the owner's two directions of 2026-09-19 (native definitions are normative;
structure is explicit and octets are inert: the owner, "they should be in, repeating such important information is not
a problem"); the settled distinctions and the rule that nothing generated is a decision or evidence; the owner's authority, the ledger, provisional choices; the harness in general terms. Nothing role-specific.

**The standing goal's scheduling sentences.** "Run commands in the background", "fix its performance issues rather
than waiting", "work on more than one problem in parallel": the orchestration now carries these out (tasks sized to a
window, one gather per step, checks in the background at the brief's check points, efficiency problems escalated as
tasks and fixed first, the finalizer), and read literally some pull against a role's rules (an implementer does not
optimize what its brief does not name; one session produces). The options: (a) the quote alone; (b) the quote, then one
paragraph saying that the orchestration carries out the scheduling parts and how, and that the first message says which
are the session's (the draft holds this); (c) the owner's rewording. Recommended: (b): the owner's words stay intact,
and the paragraph resolves the apparent conflict where it would otherwise arise.

## 10. Question 8: condensing the plan and the reasoning inventory, and where each part goes

**Are they redundant?** Not as text: 1% or less of either shares 10-word runs with the other, with DECISIONS.md or with
THEORY_MAP.md. In content, largely: each batch since 2026-09-18 is written four times, in the plan's dated section, in
REASONING_REUSE.md's dated table, in THEORY_MAP.md's rows and in its commit message, and in none of them as a decision
by topic: DECISIONS.md has not changed since 2026-09-13.
- The plan's 39 dated sections (39K tokens of its 59K) are correction tables (48%), evidence paragraphs (20%), open
  items (9%) and introductions and residual notes (22%). Of their 245 fact names, 9 are in DECISIONS.md, 166 in
  THEORY_MAP.md and 179 in REASONING_REUSE.md; the evidence and the open items are also in the batch's commit message,
  nearly verbatim.
- REASONING_REUSE.md's per-theory tables (97 rows, 12.5K tokens) state what each theory offers for reuse: 60% of their
  fact names are in the theory's THEORY_MAP.md row and 87% in the theory itself. The rest of the file is prose, the
  reasoning patterns, partly dated by batch.

**Where each part goes, as the one using the context.** What I reason from is the current state of each topic. A dated
log makes me replay it and leaves superseded corrections beside their successors, so every part goes where it is read
by topic, and the base holds the part that steers:

| Part | Goes to | Held in the bases as |
|---|---|---|
| a correction table (earlier proposal → correction) | DECISIONS.md under its topic heading (the 155 headings; a new one where none fits), in the same two-column form, naming the commit | its line in the decision index; the full text a read away |
| an evidence paragraph | nowhere new: it is the commit message | nothing |
| an open item | the task graph (a task, or HANDOFF.md's open list until it is one); dropped from the plan once taken up | the layer's HANDOFF.md |
| a residual note (a choice made outside the loop) | the machinery's residual record where it has one, HANDOFF.md's open list otherwise | as above |
| an introduction | dropped (the commit message holds it) | nothing |
| a per-theory reuse row | THEORY_MAP.md's row for the theory, completed where it lacks the row's facts; the theory's own commentary when the theory is next edited (edited now, it would re-check the theory and its dependents for a comment) | the map index (C) and the held digests, which keep commentary |
| a reasoning pattern | REASONING_REUSE.md, merged into the general section it instantiates; the batch narrative dropped | the condensed inventory |
| the plan's structure (its 29 undated sections) | stays | the plan, last before the owner's words |

Measured after condensation: the plan 58.9K → 20.7K (its structure and one line per settled batch pointing to its
decision), REASONING_REUSE.md 49.3K → 31.3K (the tables out; 28.8K if the dated prose also merges away). A falls from
462K to 404K and B from 581K to 523K.

**Almost mechanical, the agent and the owner together.** The split is by form: in every dated section, tables,
paragraphs opening "Evidence" and paragraphs opening "Open" are recognized mechanically. What needs judgment is small
and reviewable at once: one table mapping each of the 39 batches to its DECISIONS.md topic, and which reasoning
patterns are new rather than instances of a general section. Proposed course: the agent drafts that mapping and the
moved text in one change; the owner reviews the mapping; the change lands with nothing lost (every removed paragraph is
in DECISIONS.md, THEORY_MAP.md, the commit messages or the graph).

**So that they do not regrow.** Each batch writes its decision into DECISIONS.md, its per-theory reuse into the theory
map's row, its evidence into its commit message and its open items into the graph; the plan changes only when its
structure does, REASONING_REUSE.md only for a new pattern. This belongs in DEVELOPMENT_WORKFLOW.md and in the
designer's and implementer's result forms (to write once the owner agrees).

**Done (2026-09-19, session 212840df, the owner's "ok" and "do not hold off").** Different from the proposal where the
material showed it: the evidence paragraphs are only partly in the commit messages (several batches share a commit, and
the messages summarize), and the open items are each batch's limits, so every dated section moved whole.
- native_control_plan.md: its 39 dated sections (T2's uncommitted one included) are DECISIONS.md entries, whole, in
  order, each closing with its date and commit (links into the plan re-pointed); the plan keeps its structure, gains the
  owner's three directions of 2026-09-19 verbatim from the ledger, "Where the stages stand" (what the batches amount to
  for each stage and what they leave open) and "The direction of the work" (the six tasks and both orders, moved
  verbatim). 59K → 23K tokens. A script checked that every moved paragraph is in DECISIONS.md or the plan.
- REASONING_REUSE.md: 109 per-theory rows moved into their theories' THEORY_MAP.md rows (as "Reuse (section): …",
  the 58 sentences whose facts the row already names left out); rows naming tools stay, as does the table of repeated
  arguments; 23 sections left empty went. 49K → 34K tokens.
- The rule is in DEVELOPMENT_WORKFLOW.md, `protocols/_finishing.md`, the designer's and planner's protocols; HANDOFF.md
  re-points T2 to T10 at DECISIONS.md entries and records the condensation for T3's commit (commit it on its own first).

## 11. What must be built or updated before the next run

Done in session 212840df: chunks of 120,000 bytes (`bashOutputMaxChars` 128,000 in every settings file: a Bash result
is shown whole up to it, and the setting leaves the cached prefix unchanged, verified with a fork with and without it);
the `signatures` level in `digest.py`, `manifest.py` (a tier header names its level) and
`base_pack.py` (the short `(* equations:N *)` note, the legend), with tests; the generated indexes regenerated at
pack time by `base.sh` (`select_base_load.refresh_indexes`: the theory names, the decision index, and the theory map
index without the theories the list holds, when the list holds it), with a test; the three drafts at the decided
designs, packed and verified; the brief form's rule for the implementation base; `library-prompt.md` for all three
bases; no cap on design tasks (`v2.room_of`, the brief form, the test); the condensation (section 10).

To build:
1. **The layered bases** (section 8): the lists' layer mark, `base.sh` for `max`, `xhigh` and `high` and their layers,
   `v2.py`'s forks of layers and the knowledge base's load of A's layer part, `manifest.py` per layer, the warm
   daemon, the refresh rule in the watchdog, `health.py`.
2. **The frontier, measured anew at each layer refresh**, from the sessions of the roles that use it:
   `select_base_load.py` per list (it still regenerates only `base-load.txt`'s measured tier, at the definitions
   level).
3. **The protocols after the new prompt**: `_inherited.md` goes once the bases carry `library-prompt.md`.
4. **Rebuild triggers reported to the owner**: the knowledge base near its limit (built); a stable base whose reference
   tiers have gone stale (to add to `health.py`).
5. The present base's leftovers: memory entries that record project state rather than direction ("Native speedup
   batch state") are the owner's to prune.

## 12. The owner's answers (2026-09-19) and what remains the owner's

The answers to the first version's nine decisions:
1. Three bases; the designer moves to the middle base (xhigh), since it needs the working frontier; this also ends the
   knowledge base's size problem for designers (built in `v2.py` and `protocols/designer.md`).
2. The planner's base at about 500K, reduced by the plan and the reasoning inventory if they are truly redundant:
   section 10.
3. The middle base: cut redundant information, aim at about 530K: 530K after the condensation.
4. The implementation base: C″, with the theory map's index, holding no plan and no reasoning inventory as long as the
   tasks enforce that nothing needing them is required of it (the brief form's rule).
5. Would signatures alone be enough: section 7.
6. Refreshing the frontier as a separate layer: section 8.
7. The system prompt: section 9.
8. The condensation, almost mechanical, done together, and where the parts go: section 10.
9. Rebuild cadence: future work.

The answers to this revision (2026-09-19):
- Design tasks: no cap ("no longer do we need a cap on this"). Built.
- Signatures only, the outline level not built.
- The layered bases, at the refresh frequency of section 8 ("that frequency of refreshing the frontier is
  acceptable"). To build.
- The condensation: "ok", and "do not hold off": done (section 10), written into HANDOFF.md for T3.
- A's founding theories at definitions.
- The system prompt: the owner reads the updated `library-prompt.md` before deciding.

## The working tree, and whether it must be one (2026-09-20)

Measured, not inferred. A check never builds from the working tree: it assembles a copy under
`.build/check-*/proof/` with its own ROOT and theory sources rewritten to qualified imports, and builds a session
named `Incremental_<random hex>`. Heaps live under `/tmp/structural-isabelle/.isabelle/*/heaps/*/<session>` and are
found **by session name**; the lineage is a chain of proof-context directories recorded by absolute path. The project
root is `Path(__file__).resolve().parents[1]`, so it follows the tools.

A check run inside a `git worktree` at `/tmp/orch-worktree-probe`, against the base of the main checkout:

    "base": ".../check-20260920a/proof", "theories": 1797, "reused_theories": 1797,
    "phases": {"base_and_impact": 0.25, "recipes_and_host_tests": 165.43}, "seconds": 172.88, "status": "accepted"

Every theory reused, nothing rebuilt. **Heaps are not bound to the working tree's path.** The rule they seemed to
follow — "a copy at another path rebuilds and deletes the heap" — is a rule about *session names*: a copy that
carries `.build` with it carries the same names, and Isabelle keeps one heap per name, so the copy overwrites the
original's. A fresh worktree has no `.build` (it is ignored), generates new names, and collides with nothing.

So a worktree per producing task is open, and it would replace the shelf with `git merge`. What that buys, and what
it does not, is measured too (`test_two_tasks_hold_their_own_trees_and_git_merges_their_lines`): three tasks branching
from one commit, each installing a theory and a ROOT line. Lines written in different places merge cleanly and both
stand in one file, the harness moving nothing. **Lines written at the same place do not merge**: git names the file,
the merge is undone rather than resolved, and each task's line still stands on its own branch. That is a conflict a
task or the planner resolves, where the old harness silently deleted the line of whoever was still working — but it
is not free, and a brief that has two tasks appending at the same anchor will meet it.

What stays global and must stay exclusive: the heap directory, `/tmp/structural-active-context.json`, and the base
advance itself.

Built and off (`ORCH_TREES=1`, 2026-09-20): `worktree(tid)`, `worktree_of(tid)`, `worktree_gone(tid)` and
`merged(tid)` — the lifecycle and the merge, with their test. Not built: the rewiring that would use them — a
session's working directory (five `cwd=PROJECT` sites), the guard's path rules (seventeen references to
`v2.PROJECT`), the finalizer committing on a task's branch and merging, and where `.build` lives for a session whose
theories are elsewhere. That is the part that changes what every running session may do, and the day's lesson is not
to change it under a live run.

---

## 13. The layered bases, built (2026-09-20, the owner: enable it for xhigh)

**The warmth assumption is measured and holds.** Section 8 assumed every request of a fork of the layer reads a
prefix containing the stable base, so the stable base needs no pings of its own; the handoff listed it as unverified.
The sealed knowledge base is a layer over `max` in all but name, so forking it measures exactly this. A fork of kb-1
(538,044 tokens over max's 472,310), made from the project root, read **538,051 from cache and wrote 62** — the whole
prefix, the stable base included. Pinging the layer therefore keeps everything under it alive, and one ping serves
both. Note for whoever repeats it: a fork started from another working directory shares no prefix at all (the first
attempt, launched from `.claude/orchestration`, read 11,374 and wrote 526,874) — `base.sh` cds to the project first,
and anything measuring by hand must too.

**Measured split** (real packs, 2026-09-20): xhigh stable 310,066 tokens over 271 files in 7 chunks, xhigh layer
214,637 over 89 files in 6 chunks. Section 8 predicted 316K and 223K.

**Built** (nothing built or sealed live; the owner says when):
- `# === layer ===` in `base-load-xhigh.txt` and `base-load-high.txt`, above the working frontier: below it the
  frontier, the tools, the decision index, the reasoning inventory, the plan and the owner's words; above it the
  stable reference. `base-load-max.txt` is not split — A's layer is the knowledge base itself.
- `manifest.py`: `has_layer`, `held_files(part)` and `ORCH_BASE_PART`; `changed` reads both snapshots, since a fork
  holds both parts; `stale-share` is what the refresh rule reads. A layer's estimate counts no fresh session
  (`base_pack.SESSION_TOKENS` is 0 for it), because it is loaded by a fork that already carries one.
- `base.sh WHO build` packs only the stable part of a split list; `base.sh WHO layer` re-measures the frontier, packs
  what stands below the mark, forks the sealed stable base (no `--append-system-prompt-file`: a fork inherits the
  prompt, and any difference would cost the whole base a cold write), loads it, verifies it with `check-load`, seals
  it and records `state/WHO-layer.json`, stopping the layer it replaces. `drop` takes both.
- `v2.base_file`/`base_record`: every role of a base forks its layer when one is recorded, and `room_of` reads the
  layer's context, which is the whole of it.
- `watchdog.layers()`: refreshed at the start of a run and when `stale-share` reaches `ORCH_LAYER_STALE` (20%);
  `health.py` reports each layer's size, when it was sealed and its stale share.
- `select_base_load.py --frontier WHO`: the tier re-measured from the sessions of the roles that fork that base
  (`v2.ROLES[role]["origin"] == WHO`), not from the v1 implementers.

**The frontier does not shrink on thin evidence.** Measured today: the xhigh roles' sessions qualify **1** theory
(they read statements through gathers, not whole theories), the high roles' **6**. A tier rebuilt from that alone
would have collapsed from 40 to 1. So the measurement promotes what it found and the previous frontier fills the
rest in its own order: the tier keeps its size and changes only where there is evidence. Today's dry runs: xhigh 40
(1 measured, 39 carried; 1 new, 1 dropped), high 40 (6 measured, 34 carried; 5 new, 5 dropped).

**`high` holds the frontier too**, at statements where xhigh holds it at definitions, and it is the one that moves:
the work of an implementer or fixer *is* in those theories, while the xhigh roles read them. Section 8's own replay
said the same — a median of 4K of C's held files change per commit against 3K of B's, 7 refreshes against 6 in 15.5
hours. Its list is marked and its layer builds by the same command; whether to turn it on is the owner's.

**Found while doing it.** `base.sh` honoured an inherited `ORCH_LOAD_LIST`, so a caller carrying one would have had
another base's content packed into the base it asked for — and the warm daemon was carrying max's. The base named on
the command line now wins; `BASE_LOAD_LIST` is the deliberate override. The daemon must be restarted from a clean
environment before any base is built.

## 14. The edges of a layered base (2026-09-20, the owner: test the edge cases)

Seven of them, six defects. All fixed and tested (`test_layer.py`, `test_base_warm.py`, `test_watchdog.py`).

1. **The ping went to the wrong session.** `base.sh WHO warm` pinged the stable base, so the layer — what every role
   actually forks — would have gone cold while the base under it stayed warm, and the first fork after that would
   have paid a cold write of the layer's whole 525K. The ping now goes to the layer when one is recorded; a fork of
   it reads the base under it anyway, so one ping still serves both.
2. **An old layer's session kept the new one looking warm.** Warmth is marked per base name and a session's origin
   is recorded as that name, so a worker still running on the layer it forked refreshed the mark that now stands for
   the layer that replaced it — the new layer could go cold with the harness believing it warm, and again the first
   fork would pay 525K. Each session now records the session it actually forked (`origin_sid`), and `hit_chain`
   marks the base only for a session whose origin is still what is forked.
3. **A session was told what changed since a load it never had.** `manifest.py changed` read the layer standing now,
   so a session forked before a refresh was measured against a snapshot it does not hold, and the files that moved
   before that refresh — the frontier theories being worked on — were left out of its stale list. Each layer's
   snapshot is now kept under its own session (`state/layer-<sid>-manifest.json`), `manifest.py changed WHO
   --since-layer SID` measures against it, and every role's first message is rendered with the session's own
   (`v2.stale_of`). A session whose snapshot has been swept falls back to the one standing rather than saying
   nothing.
4. **A refresh could race a fork of the layer it replaced.** It stopped *and removed* the old layer; a fork launched
   from it meanwhile would have found nothing. It is now stopped and not removed — a sealed session is exactly what a
   base is — and its snapshot is kept while any session still holds it (`tidied` sweeps the rest).
5. **Two refreshes could run at once.** The guard was the watchdog's ping marker, which expires in 600 s, while a
   refresh may take 900. `base.sh` now holds `state/WHO-layer.building` for the length of the build and gives it up
   on exit; the watchdog and `health.py` read it.
6. **An orphaned layer.** Once the owner rebuilds the stable base, the layer over it is a fork of a session that is
   gone. `v2.layer_record` and `base.sh` both refuse it — the roles fork the stable base instead — and `health.py`
   says so and asks for it to be built again.
7. **A worker on the old layer is otherwise unaffected**: a fork is a copy, so stopping the layer it came from does
   not touch it, and its own requests keep its own entry alive. That one needed no change, only the test.

Found while testing: `base.sh` compared the layer's recorded base with the stable base's id one line *before*
`field()` was defined, so both sides came back empty and every layer passed as current. The test caught it.

## 15. The levels, measured (2026-09-20, the owner: does high need more than statements?)

**The names invert the order.** `statements` is the richest level, not the leanest: every command verbatim with each
proof replaced by one comment. `definitions` is the same with each lemma and theorem reduced to its name in place
(77% of statements, measured over three frontier theories); `signatures` is the same again with each definition
reduced to its name and type (57%).

So the implementation base already holds the frontier at the **richest** level, and more of it than the middle base:

| | founding theories | working frontier |
|---|---|---|
| max (planner, knowledge base) | definitions, 272,568 | — |
| xhigh (designer, task designer, investigator, reviewer) | signatures, 200,926 | **definitions**, 117,057 |
| high (implementer, fixer) | signatures, 200,926 | **statements**, 162,211 |

An implementer therefore sees every definition and every lemma statement of the 40 frontier theories, and only the
proofs are gone. Raising xhigh's frontier to statements would add 45,154 tokens to a base already at 519K with the
plan and the reasoning inventory on it, which the implementation base does not carry.

**Where an implementer is actually thin** is the 226 founding theories, held at signatures by both worker bases: a
definition's name and type, a lemma's name, no bodies and no statements. Raising them to definitions costs +71,642,
to statements +355,351 (impossible). The design's answer is the frontier: what a session keeps reaching for is
promoted into the frontier tier at statements at the next layer refresh. That is a stronger argument for turning the
layer on for `high` than for changing any level.

**Found while checking it.** The re-measure only counted file *paths* in a tool call, but a gather and `show.py` name
facts (`Theory.fact`, or a bare `foo_def`) — which is the reading the protocols prescribe. So the reading style of
the roles that read statements by name was invisible to the measurement, which is why the xhigh roles measured one
theory and the implementers, who open whole files, six. Counting a fact name for its theory (`FACT_THEORY`, built
from the theory sources) raises it to 4 and 13, and 3 and 6 of those are new to the frontier.

## 16. The planner's base is layered too (2026-09-20, the owner)

The owner, on `REASONING_REUSE.md` being stale: it *should* change as material is added, if the machinery is
working. That is the whole argument, and it holds for more than one file. Measured over the six days to 2026-09-20:
`REASONING_REUSE.md` 57 commits, `native_control_plan.md` 32, `DECISIONS.md` seven — all of today, 646K to 723K
characters in twelve hours. Against that, over the twelve hours since the `max` base was sealed:

| tier | tokens | moved |
|---|---:|---:|
| the 226 founding theories, as definitions | 272,568 | **0** |
| the 13 central-idea tiers | 127,859 | **0** |
| the generated indexes, the reasoning inventory, the plan, the owner's voice | 126,415 | 66,526 |

So the material designed to grow was sitting in the part that can only be refreshed by rebuilding 474K, while the two
thirds that never moves was rebuilt with it each time. `max` is split now, as section 8 said A should be:

- **stable, about 400K**: the founding theories at definitions and the central ideas. It moved by nothing.
- **layer, about 144K**: `state/held/theory-names.md`, the decision index, `REASONING_REUSE.md`,
  `native_control_plan.md` and the owner's voice and operating rules.

`# pinned: what exists` (the theory-name index) moved down next to the other generated index, so that the reference
holds nothing that is regenerated: it is what makes the stable part move by nothing at all rather than whenever a
theory is added. The order within the layer is unchanged — reference, then direction, the owner's words last.

Two things this turned up, both fixed before any build:

- **A layer need not hold a frontier.** `base.sh WHO layer` re-measures the frontier first, and
  `select_base_load --frontier max` returned failure because the planner's list has no such tier — which would have
  aborted every refresh of `max`'s layer. Nothing to re-measure is not a failure.
- **`layerless()` read the manifest before asking whether the layer held anything**, so a list whose layer part
  matches no file was reported as a base missing its layer. It asks in the right order now.

The three splits as they now measure (files, then loaded tokens):

| | stable | layer |
|---|---|---|
| max | 270 files, ~472K | 36 files, ~147K |
| xhigh | 271 files, ~419K | 89 files, ~263K |
| high | 271 files, ~487K | 80 files, ~209K |

## 17. The review before the build (2026-09-20)

**The sizes I had quoted were the wrong measure.** `manifest.py size` estimates from the raw digest text and ignores
the pack's compression; it runs about a third high. Packed, and scaled by each base's own measured estimator bias
(from what its whole pack actually sealed at):

| base | stable | layer | both, expected | sealed whole |
|---|---:|---:|---:|---:|
| max | 361,864 | 112,720 | **472,786** | 472,310 |
| xhigh | 293,229 | 229,088 | **496,685** | 498,607 |
| high | 293,229 | 240,953 | **518,207** | 510,838 |

Each split base lands within a few thousand tokens of the whole base it replaces, so splitting costs nothing. A fork
has 434K / 410K / 388K of room before its notice, and a refresh writes 112K / 218K / 234K instead of rebuilding.

**The division was wrong in two of the three, and the review found it by measurement.** Against the sealed manifests,
`xhigh`'s stable part moved by 17,846 tokens (`theory-names.md`) and `high`'s by 86,160 (`theory-map-index.md`):
each had a *generated* index in its reference, exactly the flaw already fixed in `max`. Both moved below the mark.
Now every stable part moves by **nothing**, and xhigh's and high's are the same 328,785 tokens of source, as they
should be — the same founding theories at signatures and the same central ideas.

**The ordering holds**: reference then direction, the owner's words last in the loaded text of all three. Within each
layer: what exists, then the frontier and the tools where there are any, then the decisions, the reasoning, the plan,
and the owner's voice. `high` carries no plan and no reasoning inventory, by design C″.

**One fragility, mine, fixed**: the layer mark was a five-line comment block, and `manifest.held_files` reads every
comment line as a tier header — so a file listed straight after the mark would have taken a nonsense tier and with it
the wrong digest level. The mark is one line now. (The lists' own header blocks are read the same loose way; that is
older and harmless, since no file follows them before a real tier.)

**Contents**: 306 / 360 / 351 files, no duplicate, nothing missing, nothing held that is always read fresh
(HANDOFF.md, PLANNING_LOG.md, THEORY_MAP.md, the ledger), and every theory at its intended level — 226 founding at
definitions for max and signatures for the others, 44 central ideas at statements, 40 frontier at definitions for
xhigh and statements for high.

**Builds**: all six packs verify; each bootstrap names exactly the chunk count its pack has (8/4, 6/7, 6/7); the
largest chunk is 108,296 bytes against the 128,000 a Bash result shows whole. `seal` writes `<who>-manifest.json`
for a stable base and `layer` writes `<who>-layer-manifest.json` and a copy under the layer's own session.

### The build itself (2026-09-20 20:00)

Sealed, all six parts, each verified by `check-load` against its pack:

| base | stable | with its layer | room a fork has | chunks |
|---|---:|---:|---:|---|
| max | 348,004 | **478,130** | 428K | 8 + 4 |
| xhigh | 274,147 | **503,712** | 403K | 6 + 7 |
| high | 274,258 | **523,233** | 383K | 6 + 7 |

`xhigh` and `high` packed their stable parts to the *same* hash — their references are identical by construction,
which is the coherence check passing in the strongest form. The knowledge base built on the max layer came to
485,374: its own load is about 7K now that HANDOFF.md is 479 tokens rather than 27,090.

One fault, found by it happening: `cmd_start` marked every layer for refresh at the start of a run, so three layers
that had just been built were rebuilt immediately. The staleness rule already refreshes a layer whose files have
moved, within a minute of starting, so the mark was redundant as well as wasteful. It is gone; a refresh happens on
staleness, or when `state/<who>-layer.refresh` asks for one by hand.


## 18. The delta: a third part holding the changes (2026-09-22, the owner)

The layer's refresh rule counted every changed file whole, on the reasoning that a fork told "this file is stale"
reads it again whole. Measured on the refreshes of 2026-09-22: the high layer's of 19:25 read 23.4% by that count and
1.4% by the lines that changed (4.9K of 344K tokens; `Development_Native_Readiness` counted 9,537 tokens for about 12
changed); the xhigh layer's of 19:17, 23.1% and about 3.5%. A refresh costs 720–810K input-equivalent (four requests,
520–590K written), and the high layer was refreshed five times from 15:06 to 19:25. Telling each fork the changed
lines in its first message was proposed and dropped: every fork would write them (1.25×). The delta is a fork of the
layer holding the changes as its one message, written once per build and read by every fork from cache (0.1×); a
build is one request (about 58K of cached prefix read and the delta written, 70–100K for 10–25K tokens). The layer is
then refreshed only when the delta holds 8% of it or its frontier moves, and the stable reference's drift is carried
by the delta and said to the owner past 15K tokens. Its plan and tasks: notes/plan-delta-layer.md and
notes/plan-delta-layer-tasks.md; its rollout: high first, xhigh after a day's measurement, max not at all (4 forks a
day, and the knowledge base integrates HANDOFF.md itself).

## 18b. The bases chosen by use (2026-09-22/23, the owner: review the bases against the day's sessions)

Measured on the sessions of 2026-09-22 and the week before (notes/plan-bases-upgrade.md, its decisions D1-D11 and
the datasets under state/analysis/): reading the base prefix is 62% of what the run spends; 176 of the 226 founding
theories held at signatures were used by no implementer or fixer in a week, 175 by no middle role, while theories no
base held were used by 15-25 forks a day; the frontier, a fixed 40 theories measured from 7 sessions with no budget, had
taken the high base from 525K to 602K in a day; the theory map's index had grown from the 56K measured here (§5) to
100.9K. What changed: the founding tier holds what its roles use and main leaves unchanged (27 on high, 23 on xhigh);
the frontier is chosen within the layer's room by use per token from 60 sessions (71 theories on high, 55 on xhigh);
the index keeps 90 characters of first clause; xhigh holds a founding index of the founding theories it no longer
holds. Estimated loaded: high 530K, xhigh 457K. The central ideas (the owner's pins, §3) and max (§12: the founding
theories at definitions) are unchanged; what the week's data says of the pins is put to the owner (plan D3).



## 19. Bases for both purposes, with explicit reasoning dependencies (2026-09-23)

The reasoning in §§1 and 4 remains the starting point: a role must have the material it needs to understand and align
its work, as well as material that saves reading. The use-only choices of §18b are superseded. The owner's
words, including the correction that data tests hypotheses rather than deciding the design, are in
`bases-discussion.md`. `plan-bases-two-purposes.md` records the resulting responsibilities, checks, corrections and
implementation decisions; it is the current account.

The implementation preserves the owner's reference pins, supplies a complete purpose-bearing catalogue and whole-plan
discovery, selects working content by explicit relations and assigns depth by what a role does with it. It supports
named material boundaries, a shared reasoning block directly over the reference, and role reasoning above the material
its judgment concerns. The current boundaries are reference, direction, catalogue and working material. They are not a
universal count: a new independent input/consumer justifies a new boundary. No content priority is inferred from churn
counts or a value-per-token score. A changed lower input rebuilds dependent reasoning; an upper change leaves lower
understanding intact. Exact frozen inputs and direct parent identities establish reuse of the same input prefix, not
correctness of the model's interpretation.

The build and console share this account. Projections derive current catalogue text without writing it, actual records
retain measured contexts and inherited snapshots, and unknown reasoning sizes stay unknown until built. Task size is
bounded by the prefix actually forked. The owner builds all three chains with `base.sh WHO layer`, then starts with
`start.sh --fresh`; README gives the order and what to inspect. No build or run was started by this implementation work,
and the no-commit/no-push hold remains in force. Quality benefit is still to be observed in that run.

**Corrected after its review (2026-09-23 evening; `plan-bases-two-purposes.md`, its last section).** The working part
— the union of every current task's relations — is gone: it grew with the queue (280K tokens for 5 tasks, 620K for 20)
and every change of the queue rebuilt it and the role layers over it. A base's parts are reference, direction and
catalogue, none of them dependent on the queue; the whole-plan notions and the tools' contracts stand in the catalogue.
A task's own relations are given to its sessions as they start (`v2.relations_read`), counted in its room at its form
check and at its first start. A chain is rebuilt at once only when its structure changes; the delta and the watchdog's
cost rule carry everything else. A build installs its list only with the chain it describes.
