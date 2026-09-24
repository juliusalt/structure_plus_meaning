# Implementation tasks: the delta layer (notes/plan-delta-layer.md, decided 2026-09-22 19:45)

## Standing orders (the owner, 2026-09-22 ~20:05, before leaving for some time)

1. Finish this implementation (tasks 1–7) and deploy it if the sandbox allows (each task deployed dormant, with a
   backup; task 8's build, canary and switch go through the watchdog's request files, since base.sh starts sessions
   and only the daemon, outside the sandbox, may).
2. Monitor the state of the run: the batched log monitor, the memory and heavy-runs monitor, the 25-minute review
   (`notes/session-review.py`), each re-armed on expiry.
3. While there is time, take the sessions as they finish, review each for read/write batching and for harness errors,
   and fix the errors found (dev copy, test, mutation case, deploy with a backup, the handoff note), then continue.
4. No commit or push until the owner says so (memory: commit-push-at-milestones is suspended).

Progress (kept here as it goes): tasks 1–7 written, tested (test_delta.py, 27 tests) and their mutation cases all
caught (one daemon wiring line has no test: warm_daemon.sh's layer ping, its loop not under test); deployed dormant at
20:12:35 (backup predeploy-201235) — no base in state/deltas. warm_daemon.sh's new line takes effect at the daemon's
next start (its loop is parsed whole). Task 8 begun 20:13: state/high-delta.build asked; the high layer had sealed at
20:12:37, so the first delta may be empty until something lands — then asked again, the canary, the switch. Done: the delta built at 20:14:22 (1,187 tokens, stable drift; 64K
input-equivalent), the canary answered from the delta at 20:15:53, high switched on at 20:17. Task 9 (the measurement)
due after a day of steady state, then xhigh: `notes/delta-measure.py SINCE [UNTIL]` (written 20:20). Its baseline,
2026-09-22 10:00-20:00: high 5 layer refreshes (3,848K) and 5 pings (184K), upkeep 403K an hour, 55 forks reading 551K
and writing 11.6K at their first request; xhigh 4 refreshes (2,802K), 14 pings (433K), 324K an hour, 72 forks; max 2
refreshes (1,383K), 20 pings (856K), 224K an hour. (This afternoon's estimate of 880K an hour for high was high; the
trial's line is 30% under 403K, about 280K an hour.)
First reading, 20:17-21:03 (the quiet window before the account-wide eviction of 21:03-21:40): high 0 refreshes,
0 builds, 2 pings — upkeep 123K an hour against the 403K baseline, its 7 forks reading 604K and writing 11.8K at
their first request; xhigh (no delta) 42K an hour over the same window, max 122K. It is 46 minutes with no refresh
in it, so it is a reading, not the measurement: what task 9 asks for is a day of steady state, and the window since
(20:17 to 22:13, 853K an hour for high) is all eviction fallout — the 21:15 delta build cost 1,561K because the
layer it forked had been evicted, not because a delta costs that.

Each task is built in the dev copy (`$TMPDIR/dev/orch`), its tests written with it, its mutation cases added to
`notes/mutation-check.py` and run on a copy, the suite run (`notes/run-tests.py`), then deployed with a backup
(`state/dev-patches/predeploy-HHMMSS`) and recorded in `notes/v2-build-handoff.md`. The code stays dormant until task 8
switches a base on; nothing is committed until the owner lifts the hold.

Two facts every task respects:
- **Sessions are started and stopped only outside Claude Code's sandbox** (base.sh's own note): by the daemon, which
  runs the watchdog, or from the owner's terminal. A delta is built by the watchdog, and anything asked by hand goes
  through a request file the watchdog reads, as `state/<who>-layer.refresh` does.
- **A request reads the longest prefix cached, and no shorter entry under it stays alive by that read** (v2.hit): the
  delta's entry, the layer's and the stable base's are each kept warm by what reads them, or pinged.

Names: `WHO` is `max`, `xhigh` or `high`; the delta's record is `state/WHO-delta.json`, its text
`state/WHO-delta-<stamp>.md`, its snapshot `state/layer-<sid>-manifest.json`. The bases a delta is built for are the
lines of `state/deltas` (a state file, so that it is switched without restarting the daemon), `ORCH_DELTAS` overriding
it in tests.

## Task 1 — the delta's text (manifest.py)

What changed in every file a base holds, since the part holding it loaded, given in its new form.

- `loaded_texts(who, part)`: `{path: held text as loaded}` from the part's pack — the stable base's
  (`state/WHO-base.json` "pack") or the layer's (`state/WHO-layer.json` "pack") — through `base_pack.sources_from_pack`;
  `layer_texts` becomes `loaded_texts(who, "layer")`. `{}` when the pack is gone (then that part's changed files are
  given whole, and said to be).
- `delta_entries(who)`: for each held file of both parts (`held_files()`, its level from its tier), comparing the held
  text now (`digest.held_text`) with the loaded one:
  - a theory: its commands (`digest.chunks` over the held text), keyed by command and name (`digest.NAMED`); unnamed
    commands (text, section, notes) by their text. Each command added or changed, in its new held form; each removed,
    by its key. A "proved here" note belongs to the command before it, which is then given with it.
  - a Python digest: its lines (a definition's signature and docstring is a line group), added or changed ones given,
    removed ones named.
  - a Markdown document: its sections (a heading and the text to the next heading), keyed by heading; added or changed
    sections whole, removed headings named.
  - a generated index (`manifest.INDEXES`): its added lines, and its removed lines named.
  - a file in the list that its part did not load: whole. A file loaded and gone from the list or the disk: named.
  Each entry: path, part, kind (`changed`, `new`, `gone`), the text to show, its tokens (`manifest.tokens`' ratio).
- `delta_text(who)`: the header, then one section per file, stable part first:
  "What you hold has changed since it loaded: the stable reference at T1, the frontier at T2. As of main C at T3, the
  text below is the current form of each part it names, and it supersedes what you hold of those parts; everything
  else you hold is current. Nothing here asks for work." Returns `(text, layer_tokens, stable_tokens)`.
- CLI: `manifest.py delta WHO` prints the text; `manifest.py delta-share WHO` prints `layer_share stable_tokens total`
  (what the watchdog reads, task 4 and 5).

Tests (`test_delta.py`, `DeltaTextTests`, a fake world with a split list and packs built by `base_pack.py build`):
- one lemma's statement changed in a 40-command theory: the delta holds that command alone, in its new form;
- a lemma removed: named, its old statement absent; a lemma added: whole;
- a "proved here" list changed: the command before it, with the new list;
- a Markdown section changed: that section whole, the document's other sections absent;
- an index line added: that line alone;
- a new file in the list: whole; a file gone: named;
- a change in the stable part: in the delta, counted in `stable_tokens`, not in `layer_tokens`;
- nothing changed: an empty delta (no header), tokens 0;
- a pack gone: that part's changed files whole, and the header says so.

Mutation cases (key `DeltaText` test names):
- the command comparison replaced by "the file changed: give it whole" — caught by the one-lemma test;
- removed commands not named — caught by the removal test;
- the stable part skipped — caught by the stable test;
- new files skipped — caught by the new-file test;
- the stable tokens counted as layer tokens — caught by the stable test.

## Task 2 — the delta session (base.sh WHO delta)

- Refuses unless the list is split, the stable base and a layer standing on it are recorded, and the layer was started
  with today's flags (`lean_as`). Takes the layer's building lock (`WHO-layer.building`); refuses while a layer build
  holds it.
- Writes the text (`manifest.py delta WHO`) to `state/WHO-delta-<stamp>.md`; an empty delta builds nothing and says so.
- At most DELTA_ARG (120,000 bytes, under Linux's 128K argument) the fork's first message is a short instruction —
  "Hold these changes to what you hold; do no work. Reply with exactly HELD <digest12> and end your turn." — then the
  text; above it, the text is packed (`BASE_LOAD_LIST` naming the file, `prepare_pack`) and loaded by the pack's
  bootstrap, as a layer is.
- `claude --bg --resume <layer sid> --fork-session $LEAN --model … --effort … -n WHO-delta-HHMMSS`; waits for it as a
  layer build waits.
- Verifies: its last reply is `HELD <digest12>` (one character's slip allowed, as `acknowledges`), and the transcript's
  first user message holds the text's digest — or, packed, `base_pack.py check-load`. A delta that fails either is not
  recorded (the session is stopped, the reason in warm.log).
- Snapshots every held file's digest, both parts, as `state/layer-<sid>-manifest.json` with `"delta": true` (so a stale
  line measures from the delta, task 3).
- Records `state/WHO-delta.json`: `sessionId, name, layer, base, model, effort, flags, head, tokens, layer_tokens,
  stable_tokens, digest, text, sealed, context` — then stops the session; the delta it replaces is stopped, never
  removed (a fork launched from it meanwhile must find it). Touches `WHO-base.hit` and `WHO-base.used` (what roles fork
  is read) and `WHO-layer.hit` (the build read the layer's entry). Writes `delta WHO: <session_fork_check's verdict of
  its read of the layer>` to warm.log.
- `base.sh WHO delta --ask QUESTION`: forks the standing delta with QUESTION, waits, writes its reply to
  `state/WHO-delta-answer.txt`, stops and removes the fork (the canary, task 8).

Tests (`test_delta.py`, on `test_base_warm.py`'s harness — a fake `claude` recording its calls and writing the fork's transcript — class
`DeltaScriptTests`):
- the fork resumes the layer's session, not the stable base's, with the flags, model and effort recorded;
- a HELD reply with the digest: the record, the snapshot (`"delta": true`, both parts' files), the hit marks; the
  delta it replaces stopped, not removed;
- a wrong reply: nothing recorded, the session stopped, warm.log says why;
- an empty delta: no session started;
- the lock held by a layer build: refused, nothing started;
- a text over DELTA_ARG: the pack's bootstrap is the first message (not the text);
- `--ask`: the fork of the delta, the answer file, the fork removed.

Mutation cases: resuming the stable base instead of the layer; the reply's check dropped; the snapshot's `"delta"`
mark dropped; the replaced delta not stopped; the lock check dropped; the DELTA_ARG branch inverted.

## Task 3 — forks start from the delta (v2.py, manifest.py)

- `delta_record(who)`: the record when its `layer` is `layer_record(who)`'s session and its `base` the stable base's,
  None otherwise (an orphan: its layer was refreshed or its base rebuilt).
- `base_file(who)`: the delta when `delta_record`, else the layer, else the stable base — so `base_record`,
  `origin_of`, a fork's `origin_sid` and the daemon's ping all follow.
- `tidied`: a delta's snapshot is kept while a session holds it or it is the standing one (`holding` gains
  `delta_record`'s session); a delta's text file goes with its snapshot.
- `manifest.stale_line`: a snapshot marked `"delta"` is the one record, for both parts ("since the delta at T"), so a
  fork of the delta is told only what changed after it — not the stable part's changes the delta already holds.

Tests (`test_delta.py`, `DeltaForkTests`): the delta preferred; an orphan delta (layer replaced,
or base rebuilt) not forked, the layer forked instead; the delta's snapshot kept while held and swept after; a session
on the delta told only the change made after it; a session on the layer (before the delta) told what changed since
the layer.

Mutation cases: `base_file` ignoring the delta; the orphan rule dropped; the `"delta"` record read as the layer's
alone (the stale line then names the stable part's changes the delta holds); the snapshot swept while held.

## Task 4 — when a delta is built (watchdog.py)

`deltas()`, run each pass beside `layers()`, for each base in `state/deltas`:
- nothing while a layer or delta build holds the lock, or the base has no recorded layer;
- nothing within DELTA_EVERY (1,200 s) of the last build (`WHO-delta.looked`, touched at each look that decides);
- the change since the standing delta: the would-be delta's text against the standing delta's text (difflib over the
  two, in tokens); against nothing when there is no delta. Below DELTA_MIN (2,000) nothing;
- the layer's own entry cold (`WHO-layer.hit` older than WARM_MAX): the layer is refreshed instead (a delta build would
  write the layer anyway; the refresh re-measures the frontier too);
- else `base.sh WHO delta` in the background (as `layers()` starts a refresh), logged: "the WHO delta is rebuilt: N
  tokens moved since HH:MM (it holds L of the frontier's and S of the stable reference's)";
- a request by hand, `state/WHO-delta.build`, builds one at the next pass whatever the thresholds (the lock still
  holds); `state/WHO-delta.ask` (a question) runs `base.sh WHO delta --ask` (task 8).

Tests (`test_delta.py`, `DeltaTriggerTests`, `base.sh` replaced by a recorder): built past DELTA_MIN; not within
DELTA_EVERY; not below DELTA_MIN; not while the lock is held; a cold layer entry asks for a layer refresh instead; a
request file builds at once; a base not in `state/deltas` is left alone.

Mutation cases: the DELTA_EVERY check dropped; DELTA_MIN compared the wrong way; the cold-layer branch dropped; the
lock check dropped; `state/deltas` ignored.

## Task 5 — when the layer is refreshed (watchdog.py, select_base_load.py)

For a base in `state/deltas`, `layers()` decides by the delta, not the whole-file share:
- `layer_share` (`manifest.py delta-share`) at LAYER_DELTA_MAX (0.08) or more: refreshed, logged with both measures
  ("the high layer is refreshed: the delta holds 9% of it (the whole-file share 31%)");
- the frontier moved: `select_base_load.py --frontier WHO --dry-run` names the theories the frontier would hold now;
  FRONTIER_MOVED (5) or more differing from the list's frontier tier: refreshed, logged with the theories. Measured at
  a delta build, not every pass (it reads sessions' transcripts);
- `stable_tokens` at STABLE_DELTA_MAX (15,000) or more: no refresh — an ATTENTION once a day: "the high delta holds N
  tokens of the stable reference's changes: loading it again (base.sh high restable) is the owner's";
- a base not in `state/deltas` keeps today's rule.
- `select_base_load.py --frontier WHO --dry-run` prints the theories it would choose, one a line, and writes nothing
  (it exists; its output is made machine-readable if it is not).

Tests: refreshed at the share; not below it however high the whole-file share; refreshed for a frontier moved by 5,
not by 4; the stable ATTENTION with no refresh; a base without deltas refreshed by today's rule.

Mutation cases: the whole-file share still deciding; FRONTIER_MOVED's comparison off by one; the stable part
refreshing the layer; the ATTENTION dropped.

## Task 6 — keeping the entries warm (base.sh, warm_daemon.sh, session-review.py, health.py)

- `base.sh WHO warm` pings what roles fork: the delta when `delta_record` holds (the same rule, read by a
  `python3 -c` over the two records), else the layer, else the base.
- `base.sh WHO warm layer --if-due`: under a delta only, pings the layer's own entry while it is warm and due
  (`WHO-layer.hit` older than ORCH_WARM_EVERY, younger than ORCH_WARM_MAX, fewer than two misses in `WHO-layer.miss`),
  as `warm stable` pings the stable base; marks `WHO-layer.hit` on a hit.
- `warm_daemon.sh` runs it beside the stable ping.
- The review's and health's "standing" lines name the delta: its age, its tokens (frontier and stable), its last hit.

Tests (`test_delta.py`, `DeltaWarmTests`): the ping goes to the delta when one stands on the layer; to the layer when the delta is an
orphan; the layer's ping only under a delta, only when due, recorded where health reads it; a delta build's read marks
the layer's entry.

Mutation cases: the ping going to the layer under a standing delta; the layer's ping without a delta; the due window
dropped.

## Task 7 — documents

README's section on the bases (three parts: stable reference, frontier layer, delta; who builds each and when; what a
fork holds and is told), `notes/bases-design.md` (a section "The delta" with the measures that decided it and the
thresholds), `notes/plan-delta-layer.md`'s outcome, the handoff note. No protocol changes.

## Task 8 — deployment, the canary, the switch

1. Deploy tasks 1–7 with `state/deltas` empty: nothing changes in the run (the suite and the mutation check green on
   live).
2. `state/high-delta.build` by hand: the watchdog builds the first high delta; check its record, its snapshot, its
   warm.log line (its read of the layer from cache, 98% or more), its tokens against `manifest.py delta high`.
3. The canary: a statement the high layer holds in its old form and the delta in its new one (chosen from the delta's
   text); `state/high-delta.ask` with a question only the new form answers; the answer in
   `state/high-delta-answer.txt` must give the new form. If it gives the old one, stop: the header and the form are
   reworked before anything forks the delta.
4. `echo high > state/deltas`: forks of high start from the delta; watch the first forks' cache lines ("cache of …":
   the delta read from cache) and their stale lines (only what changed after the delta).

## Task 9 — the measurement, after a day

`notes/delta-measure.py SINCE`: from v2.log, warm.log and the transcripts — layer refreshes and delta builds per base
and their cost in input-equivalent (the build sessions' usage), pings, forks' first requests (cache read and write),
delta sizes (frontier and stable), the residual stale lines' length, and forks' reads of files their stale line named;
the same over 2026-09-22 10:00–20:00 as the baseline. The trial succeeds if high's upkeep an hour (refreshes, builds,
pings) falls by at least 30% and forks read fewer stale files; then `xhigh` joins `state/deltas`. The thresholds are
adjusted from what it shows.

## Order and size

1 → 2 → 3 → 6 → 4 → 5 → 7 → 8 → 9. Tasks 1 and 2 are the bulk (the text and the session); 3, 4 and 6 are small and
lean on what the layer already does; 5 is a rule. Each is deployed on its own, dormant until task 8.
