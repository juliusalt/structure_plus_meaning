# Plan: a third layer that holds the changes (the owner, 2026-09-22 19:30; decided 19:45)

## Why

A base is two cached prefixes: the stable reference (loaded rarely, by the owner) and the frontier layer (a fork of it,
refreshed by the harness). Every role forks the layer and reads both from cache. What changed after the layer loaded
reaches a fork only as the stale line in its first message, which names files; the refresh rule counts every changed
file whole (a fork is assumed to read it again whole) and refreshes the layer at 20%.

Measured 2026-09-22:
- The high layer's 19:25 refresh: 23.4% by that rule, 1.4% by the lines that changed (4.9K of 344K tokens);
  `Development_Native_Readiness` counted 9,537 tokens for about 12 changed, `Native_Table_Reach` 8,448 for 44. The
  xhigh layer's 19:17 refresh: 23.1% by the rule (reproduced exactly), about 3.5% by changed lines.
- A layer refresh costs 720–810K input-equivalent (4 requests, 520–590K tokens written). The high layer was refreshed
  five times from 15:06 to 19:25 (about 4M), xhigh three times since 14:55.
- Forks started today: high 98, xhigh 122, max 4.

A delta layer — a fork of the frontier layer whose one message is what changed since the loads under it — puts the
changes where the prefix cache serves them: each fork reads them from cache at a tenth of the input price instead of
being told file names and reading files again, the delta is rebuilt cheaply and often, and the frontier layer is
refreshed only when the delta grows large. It is better than giving each fork the changed lines in its first message
(this afternoon's proposal): there every fork writes them (1.25×); here they are written once per build and read by
every fork after.

## What it costs, and the risks

- A delta build: one fork of the layer, the delta as its first message, a one-word reply — one request reading the
  layer's prefix from cache (about 58K input-equivalent) and writing the delta (about 1.25× its tokens): 70–100K for a
  delta of 10–25K tokens, against 720–810K for a layer refresh.
- One more cache entry per base: the delta is what roles fork, so it is what the daemon pings when idle; the layer's
  own entry is then read only by delta builds and needs its own ping when no build read it within the interval, under
  the stable ping's rule (while warm, stopping after two misses).
- Forks hold superseded text beside its replacement. The delta gives every changed statement in its new form whole
  (never a diff to apply), under a header saying it supersedes what the fork holds of those files, and its size is
  bounded; a canary question at deployment checks that a fork answers from the delta.
- Estimated for high at today's pace: builds at most every 20–30 minutes (200–300K an hour), a layer refresh every
  6–10 hours (about 100K an hour), against about 880K an hour today — about half, with forks current to within a
  build rather than holding up to an hour of changes named only as files.

## The plan

Built in the dev copy, tested there, deployed with a backup, as every harness change; mutation cases for every rule.
Behind `ORCH_DELTAS` (the bases it applies to), first `high`.

1. **The delta's text** — `manifest.py delta WHO`: what every held file of the base (stable and layer parts) holds now
   that differs from what its part loaded (the pack's text, as `layer_texts` restores it; the stable part's from its
   own pack), by held text:
   - a theory's digest by command: each command added or changed, in its new held form; each removed, by name; a
     "proved here" list by the names that moved in or out;
   - a Python digest by definition; a Markdown document by section; a generated index by its changed lines;
   - a file new to the list, whole; a file gone, named.

   Headed by the loads it follows, the main commit and time it is as of, and that what it shows supersedes what the
   fork holds of those files and everything else it holds is current. It reports its own token count. Tests over
   theories, tools, documents, indexes, new and gone files.
2. **The delta session** — `base.sh WHO delta`: fork the recorded layer with the delta as the fork's first message
   (one request; above the argument limit, 120K, it is packed and loaded by chunks as a layer is, reusing
   `prepare_pack` and `check-load`); verify the reply and that the transcript holds the delta's digest; snapshot every
   held file's digest as `state/layer-<sid>-manifest.json` (so a stale line measures from the delta); measure the
   context; stop it; record `state/WHO-delta.json` (session, layer, base, head, tokens, digest, sealed). The delta it
   replaces is stopped, never removed. It holds the layer's building lock. A fake-world test of the whole mode.
3. **Forks start from the delta** — `v2.base_file` names the delta when its layer is the recorded layer and its base
   the recorded base (the orphan rule of `layer_record`), the layer otherwise; `origin_sid` is the delta's, so the
   stale line says only what changed after it; the hit marks are the delta's entry. Tests: the delta preferred, an
   orphan ignored, the stale line residual.
4. **When a delta is built** — the watchdog's `deltas()` beside `layers()`: when the changes since the standing delta
   (by changed-line tokens) reach DELTA_MIN (2K), at least DELTA_EVERY (20 minutes) after the last build, no layer or
   delta build running, and the layer's entry warm (else a layer refresh, which writes it anyway). A layer refresh is
   followed by a delta only when there is a change (the stable part's drift). Tests: the threshold, the debounce, the
   lock, the cold layer.
5. **When the layer is refreshed** — by the delta's size, not the whole-file share: when what the delta holds of the
   layer part reaches LAYER_DELTA_MAX (8% of the layer's tokens, about 25K), or when the frontier selection, re-measured
   as a dry run at each delta build, differs by FRONTIER_MOVED (5) theories. What the delta holds of the stable part
   refreshes nothing: past STABLE_DELTA_MAX (15K) it is an ATTENTION for the owner, whose restable it is. The
   whole-file share is logged beside the new measure during the trial. Tests.
6. **Keeping the entries warm** — the delta, as what the roles fork, is pinged by the daemon's existing path when no
   fork read it; the layer gets `warm WHO layer --if-due` under the stable ping's rule, skipped when a delta build read
   it within the interval. Tests in `test_base_warm`.
7. **Documents** — README's bases section, `notes/bases-design.md` (the third part and its measures), this note's
   outcome, the handoff note. No protocol changes: the delta's header says what it is, and the stale line keeps its
   form.
8. **Deployment and the canary** — build the first high delta by hand, fork it with a question whose answer changed
   in the delta (a statement the layer holds in its old form), and check the answer uses the new form; then switch
   `ORCH_DELTAS=high` on.
9. **Measure after a day, then decide xhigh** — layer refreshes, delta builds and their cost, pings, forks'
   first-request reads and writes, delta sizes, the residual stale lines, and forks' reads of files named stale,
   against today's baseline. The trial succeeds if high's upkeep an hour (refreshes, builds, pings) falls by at least
   30% and forks read fewer stale files; then xhigh. max stays as it is: 4 forks a day, and the knowledge base
   integrates HANDOFF.md itself.

## Decided (the owner, 2026-09-22 19:45)

- The delta carries the stable part's drift too: it makes that drift visible and served to every fork; the restable
  stays the owner's, prompted by the ATTENTION past STABLE_DELTA_MAX.
- The first thresholds as proposed — DELTA_MIN 2K tokens, DELTA_EVERY 20 minutes, LAYER_DELTA_MAX 8% of the layer,
  FRONTIER_MOVED 5 theories, STABLE_DELTA_MAX 15K tokens — estimates the day's measurement adjusts.
- The rollout: high first, xhigh after a day's measurement, max not at all.
- The implementation task plan, with its tests and mutation cases: `notes/plan-delta-layer-tasks.md`.
