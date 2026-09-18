# The rotating implementer

One Opus implementer at a time carries out `native_control_plan.md` at max effort, alone. It is a fork of a
sealed, loaded base session, so it starts with the base's whole context delivered from the prompt cache; it
works until its window is nearly full, brings `HANDOFF.md` current, and is replaced by the next fork. No model
supervises it: a small daemon rotates it, restarts it after a usage-limit stop, and keeps the base's cache
entry alive. The owner speaks to it directly. (A first design with a Fable knowledge base answering the
implementer's questions ran on 2026-09-18 and was dropped; its findings are at the end.)

## Use

    .claude/orchestration/base.sh impl build    # freeze base-load.txt into a verified pack and start loading it; returns at once
    .claude/orchestration/base.sh impl status   # until the load has ended its turn (the measured context)
    .claude/orchestration/base.sh impl seal     # check every chunk arrived, snapshot the frozen sources, stop it, start the daemon
    .claude/orchestration/start.sh              # start (or rejoin) the implementer, open it here and follow it through rotations
    .claude/orchestration/attach.sh             # only open and follow the live implementer; starts nothing
    .claude/orchestration/stop.sh               # stop everything: daemon, implementer, the runs it left behind
    .claude/orchestration/health.py             # one screen; lines that need someone start with ATTENTION

`build` refuses while a base is recorded: `base.sh impl drop` first. The terminal follows the implementer
(`attach.sh`): when a rotation or a wake stops the attached session, `claude attach` exits ("Session … has
exited") and the successor named in `state/current-impl` is opened as soon as it is live. The watchdog marks
`rotated` or `<name>.woken` before it stops a session, so leaving the session view on purpose while the
implementer runs is told apart and ends the following; `stop.sh` ends it too. Without a sealed base everything still works, with a
plain implementer that reads for itself. Directions you give an implementer go, by its instructions, verbatim
into `owner-ledger.md`, which every successor reads first; what is yours to decide it records there as an open
question and proceeds provisionally.

## How the base is loaded

`base.sh impl build` (also `build-packed`) runs `base_pack.py build`: it freezes every file of the load list as
its digest, checks that each digest can be restored byte for byte, and splits the bundle into chunks of at most
20,000 bytes. The base session receives them through one Bash call per chunk (`base_pack.py emit`), so the load
carries none of the Read tool's line numbers or per-file calls. The loaded form is `all-but-fact-groups`: every
reversible layer except the grouping of fact names. Isabelle symbols appear as glyphs, omission notes are short
(`(* proof:12 *)`), indentation outside strings, cartouches and comments is removed, the theory-name index
shares prefixes, and a theory's header omits the path its `theory X` line already gives. Lemma names stay
written out, because they show what each founding theory can do. A short legend says how to read all of this,
and that theory files spell symbols as escapes: Isabelle rejects a glyph in a theory file with an inner lexical
error on that line (checked 2026-09-19), and the implementer prompt says the same. Each tier gets a subject
heading; the curation notes of `base-load.txt` never reach the loaded text.

The base and every session forked from it start lean: `session-flags` gives exactly the tools implementers use
(Bash, Read, Edit, Write, Glob, Grep, Agent, ToolSearch, the task and background-task tools, WebFetch,
WebSearch), no MCP connectors and no skills list. `base.sh` (build, warm) and `rotate.sh` (fork, plain) pass it;
the flags must be identical for a fork to read the base from cache. A bare `claude --bg --resume`, as the
watchdog wakes a session, keeps them: a woken lean session listed the same tools and read its whole prefix from
cache (verified 2026-09-19).

Verified 2026-09-19 through the real scripts with the real model, effort and flags: a small packed base built by
`base.sh impl build` loaded through Bash, `check-load` accepted its transcript, and a fork started by `rotate.sh`
read it from cache on its first request, `cache_read=20062 cache_write=97` against a base context of 20,064.

`seal` accepts a packed load only when `base_pack.py check-load` finds every chunk, complete, in the main
transcript and the final `LOADED <pack id>` after them; a model's claim or a context size is not enough. Claude
Code stores a Bash result without its trailing newline, so the chunk envelopes are matched without it
(verified 2026-09-19 with a real two-chunk load; the earlier exact match found none). A packed base is not
extended: change the list and build again. `base.sh impl build-files` is the older loader, in which the session
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

The base holds the curated selections, `owner-directions.md` (Claude sessions) and `codex-owner-directions.md`
(the foundational Codex session): verbatim excerpts, each checked against its transcript record
(`extract_owner_directions.py --verify`; the selections and hashes are in the two `*-selection.json` files).
What the owner says after those were collected — `reviewed_through` in `owner-directions-selection.json` — is
read by every implementer at start: `rotate.sh` runs `extract_owner_directions.py --new`, which writes the
owner's typed words since then, from Claude sessions and interactive Codex sessions of this repository, to
`state/owner-directions-new.md`. Sessions that work on the orchestration itself (a tool call naming anything in
this directory beyond the ledger, the directions and `impl_state.sh`) are left out, as are launch prompts and
automated Codex runs. When the selections are curated again, move `reviewed_through` with them.

## Orchestration notes stay out of the content

The project memory (`~/.claude/projects/-home-julius-structure-and-semantics/memory/`) is loaded into every
Claude session of this repository, the base and its forks included, and the load list holds it as well. Notes
about the orchestration — its design history, costs, cache behaviour, what to improve — therefore live in
`notes/`, never in the project memory, and nothing loaded or read at start comments on the orchestration.

## What the base is for, and how its list is chosen

The base sets direction; it is not a lookup cache. What the implementer has in view is what it thinks with, so
the base holds the owner's words, the operating rules, the plan, the reasoning inventory, the name of every
theory (so that it knows what exists before it invents), and the *founding* theories of the library's own
ideas — small theories where a notion and its locally owned contract are established, not their downstream
mass. `base-load.txt` has hand-kept `# pinned…` tiers for these, a generated `# measured` tier for the frontier
and tools recent implementers actually worked in (density-ranked, forks included, their copied base part
skipped), and an `# optional` tier that is never loaded. The target is `ORCH_BASE_TARGET` (`manifest.TARGET`),
530K loaded with everything included, the owner's request of 2026-09-19; `select_base_load.py` sizes the
measured tier against it in the loaded form, and the pack report and `seal` say when a load exceeds it. The
first full packed load (2026-09-19, base 32f5e011) measured 560,299 tokens against an estimate of 526,647; the
estimator's constants in `base_pack.py` are calibrated on it. At 530K the selector would keep 22 of the 41
working-frontier files; the base was sealed with all 41.

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
Moving a theory between the two is moving its line. Measured: all 244 as definitions 265K tokens, as
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
| `start.sh`, `stop.sh` | start or rejoin and attach; stop everything |
| `base.sh`, `base_pack.py`, `base-settings.json` | pack the list, load it chunk by chunk, check the load, seal, warm and drop the base; `pack_notation.py` holds the comparison notations; `base-bootstrap.txt` belongs to `build-files` |
| `base-load.txt`, `select_base_load.py`, `idea_candidates.py`, `idea-candidates.md`, `manifest.py` | the load list, its generated tier, the owner's curation table, and the snapshot that names held files changed since the load |
| `attach.sh` | open the live implementer in this terminal and follow it through rotations and wakes |
| `rotate.sh`, `session_row.py`, `session_fork_check.py` | replace the implementer (`rotate.sh auto`), and verify that the fork's first request read the base from cache |
| `warm_daemon.sh`, `watchdog.py` | the daemon: rotation when `state/rotate` stands, a vanished implementer, wake after a usage-limit stop or a lost turn; keep-warm pings of the base when no verified fork is using it |
| `implementer-prompt.md`, `implementer-bootstrap*.txt`, `impl-settings.json` | standing goal and protocol (recorded in the base), first message, hooks |
| `ctx_gauge.py`, `impl_state.sh` | context gauge and the one handoff notice (window − 60K), backstop flag (window − 10K), compaction tripwire, stop control, declared waiting |
| `owner-ledger.md` | the owner's directions verbatim, and open questions with the provisional choice made |
| `owner-directions.md`, `codex-owner-directions.md`, `*-selection.json`, `extract_owner_directions.py` | the owner's curated directions held in the base, verified against the transcripts; `--new` writes what the owner said since, read by every implementer at start |
| `notes/` | the orchestration's own notes (design history, measured costs, cache and transcript behaviour); never loaded |
| `test_base_pack.py`, `test_owner_directions.py`, `test_attach.py` | packing, load checks and the collection of new directions, without launching sessions |
| `health.py`, `state/` | report; flags, base record, manifests, logs (ignored by git) |
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
  `SessionStart` hook sleeping ten seconds, which holds the first request back; no miss since. Only a fork
  verified by `rotate.sh` counts as keeping the base warm.
- Waking: `claude stop` plus a bare `claude --bg --resume <id> "prompt"` keeps id, name, saved options, hooks
  and cache. Nothing else restarts a background session after "You've hit your session limit".
- Background sessions do not inherit the launching shell's environment (use `--settings` `env`). In
  `claude agents --json`, `status` (busy/idle) is live; `state` lags. Auto permission mode needs Opus 4.6+,
  Sonnet 4.6+ or Fable. A harness kills a session's background commands when the machine runs short of memory
  (three concurrent Isabelle runs reached 59 of 60 GiB), so nothing essential lives in a session's background.
- The Read tool: 25K tokens a call, 256KB a file, lines cut at 2,000 characters — `manifest.py list` names part
  sizes and substitutes folded copies. No tool result was ever cleared from context in sessions up to 955K.

## Cost, measured

The plan meter fits API-style weights on this account's own limit windows within ±15%: cache reads 0.10,
one-hour writes 2.0, output 5 per input token, Fable about 3× Opus; "reads are free" does not fit. So the cost
of any design is Σ over sessions of model weight × context per request × requests per hour. With a 700K base
and a Fable knowledge base the first run used about 32M Opus-equivalents an hour (42% of a window) against 11M
for a single plain session; the knowledge base and a Fable maintenance session were 44% of it. Implementers
alone on a 700K base: about 17.7M an hour, rotating every 16–19 minutes. A 540K base gives about 460K of room.

Not yet exercised: a full-size packed load and a fork's cache read of a packed base; the watchdog rotating or
waking a real session by its own timer; `start.sh` attaching.
