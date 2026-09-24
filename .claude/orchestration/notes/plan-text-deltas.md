# Text deltas, sessions on demand (the owner, 2026-09-24 ~00:10: "yes do this")

Owner's approval of: "write the text on every change, as now, but build the session only when something is about to
start from it. Every message whose session nobody uses would save its 50–60K."

Work copy: scratchpad/orch7 (from live, which = orch6 not yet deployed? NO — live = orch5; orch6 = live + idle-rule
fix, validating in background as task b6yeykn25; build orch7 FROM orch6).

## Design
- WHO-delta.json keeps the chain `stack` of nodes {id, text, digest, tokens, superseded, parts, kind, sealed,
  sessionId?}; record `top` = last node id; `sessionId` = the latest MATERIALIZED session (absent if none);
  `session_len` = nodes it holds; `context` its measured context; session_parts/superseded/old_forms at materialization.
- A text node: `base_stack.py delta WHO --text [--whole]` (manifest delta / delta-increment → text file, counts, held;
  snapshot-delta → layer-<node id>-manifest.json; builds log kind text-delta/text-increment). No session. Node id
  `text-<stamp>` (or the session id once materialized? keep text id; node.sessionId added when materialized).
- Materialize: `base_stack.py delta WHO` (base.sh delta execs it; --ask stays in base.sh): cut pending first; fork the
  materialized session if it holds a beginning of this chain, else the layer; prompt = texts of nodes after it; HELD
  check; snapshot-delta → layer-<sid>-manifest.json; record sessionId, session_len=len(stack), context; builds log kind
  session / session-whole (whole = over the layer: counts as the parts' changes written again, carried_parts).
- v2: base_file → delta.json only if record has sessionId; delta_pending = uncut + tokens of nodes after session_len;
  top_rider = direct riders only (BASES, base parts, kb→max); a separate stands_on(origin) (descendant walk) for the
  idle-rule use marks (copy six); layer_stands: origin in materialized node sessions ∪ {d.layer}; role_layer_build chain
  fields stack_len=session_len when over the session, 0 over the layer; churn care: moved includes uncut pending; cut
  text before growing; node id = node.id or node.sessionId (old fixtures); tidied keeps node ids' snapshots + texts.
- watchdog.deltas: pending file {"top": top node id or layer sid, tokens: uncut}; consolidation (stack_waste) → cut a
  whole text (new chain); materialization by pending_paid with direct riders, lacking = uncut + unmaterialized; cold
  layer check only before a materialization.
- manifest.stack_held: held["top"] == delta["top"] (node id), not sessionId.
- Then: tests (test_delta base.sh delta tests, rules; test_v2 churn/judging tests), mutation cases, docs, sim run vs
  full-idle, deploy, handoff.

## The owner, 2026-09-24 ~00:15: "In general everything should be done lazy when its better not just this part."
(memory: lazy-when-better.) The audit of what is still made ahead of need:
1. Delta sessions — this round (step 1).
2. The knowledge base rebuilt at every new max session (kb_care `rebased`), planner or not: lazily it takes max's new
   texts by integration (resume with the texts, as the planner notes are integrated), by the churn's rule over the
   planners lacking them; rebuilt only when cold, grown or lost (step 2).
3. Generated indexes made at every commit by the watchdog: made by whoever reads them (a fork's stale line, a text cut,
   a build) when main moved since (step 3; also closes the gap between a commit and the next pass).
Already demand-driven: churns (rule), role layers (built when wanted), refreshes (accounts), pings (horizon).

The owner, right after: "No being eger on deterministic computation is fine being eger on something that costs is
not." Step 3 dropped (index regeneration is local and deterministic: eager is fine). Texts may be cut eagerly; only
sessions (tokens) wait for a consumer.

## The owner, 2026-09-24 ~00:20, mid-build: "the knowledge base is rebuilt on every max session make this lzay too."
Step 2 folded into this round. And: "You do not need to run the simulation every deployment only I will tell you when to
run it." — this round is validated by the suite and the mutation check; the simulator is kept in step (its fake CLI reads
a resumed `[harness] Integrate …` as the knowledge base's, its report counts cuts, sessions made and texts taken in).

## As built (copy orch7, 2026-09-24)
- `base_stack.cut(who, whole=False)` (`base.sh WHO delta --text [--whole]`, before the sandbox and hold checks: it starts
  nothing): a text node {id `WHO-text-<stamp>`, text, digest, tokens, superseded, parts, kind, sealed} with its snapshot
  `layer-<id>-manifest.json`; an increment while `WHO-delta-held.json` names the chain's top, else a whole text that
  begins a new chain holding no session; skipped while a build holds `WHO-layer.building` (its end orphans the chain).
  The record's read-modify-write under `WHO-delta.lock` (flock). Builds log kinds `text-delta`, `text-increment`.
- `base_stack.materialize(who, whole, over_layer)` (`base.sh WHO delta [--whole|--over-layer]`; `--ask` stays in base.sh
  and needs a session): cut first; fork the chain's session when it holds the chain's first texts (`session_base`) and
  is warm (`v2.warm(who)`), with only the texts after it, else the layer with them all; HELD with the top text's digest,
  or chunks past DELTA_ARG; its snapshot is the top text's; recorded on the chain: `sessionId`, `session_len`,
  `session_base`, `sealed`, `session_tokens/superseded/parts/old_forms`, and the node's `sessionId`. Builds log kinds
  `session` (over the session) and `session-whole` (over the layer: every part's changes written again).
- Deviation from the plan, by the design's own rule: texts are cut when a consumer takes them, not at every measure —
  a cut per pass would multiply superseded forms for every holder. The watchdog measures what is not cut every
  DELTA_EVERY (`WHO-delta-pending.json` {top: the chain's top text or the layer, tokens}).
- Deviation, for the owner's decision of 09-23 (judging roles reason over the changes): the judging roles' layers and
  the knowledge base hold the chain's texts past what they fork in their own first message (`v2.chain_carried`,
  `{CHANGES}` in role-layer.md before "## Your reasoning", in kb.md after the stale line) — the plan's "stack_len 0 over
  the layer" would have left their reasoning without the changes once no shared session is made. Same writes as a churn
  holding them; no shared session made for them.
- Who awaits a session (`v2.top_rider`): forks of the base itself or its medium layer, never a layer role, a churn or
  the knowledge base. `v2.stands_on` keeps the descendant walk for the idle rule's use marks (copy six).
- The knowledge base (step 2): built with max's texts carried; stands while max's parts stand (`layer_sid`,
  `v2.kb_stands`; one built before by the session it forked); takes later texts in by integration, with the planners'
  notes or alone once its planners' `kb_lacking` has paid (`v2.kb_texts_paid`, the churn's rule); its snapshot is the
  last text's, copied under its own session (planners' stale lines). `watchdog.kb_cost` stays only in refresh costs.
- `watchdog.deltas`: a session by `pending_paid` over direct forks (cost 2 × lacking + 0.1 × what it forks, no knowledge
  base); consolidation (`stack_waste`: holders — standing churns, the knowledge base, the chain's session — each 2 ×
  whole + 0.1 × its read, and the judging layers) is a whole cut in process; a fork that missed the session's entry has
  it made over the layer (`--over-layer`), one that missed the layer's while no session stands has the layer refreshed;
  the cold-layer check only before a session over the layer.
- `v2.role_churn_care`: what is not cut counts in `moved`, is cut before the churn is built, and a churn is not built
  for texts it holds when nothing was cut; a fork is behind while changes wait to be cut.
