# The simulation of the run of 09-21/22 — findings, as they come

The world: notes/sim (simrun.py, fakeclaude.py, simreport.py). The replay window 2026-09-21 21:50 – 09-22 23:00: 339
commits of main at their times, the 315 recorded sessions of the forking roles (timeline.jsonl) started through
v2.launch at their times with their requests.

## Machinery (harness) findings

1. **Adequacy — the generated indexes were blind to every rule.** The parts hold generated indexes (decisions,
   theory map, tools, plan map, theory names, practice), made only by a build of a base (`select_base_load
   .refresh_indexes` from `base_stack.build_chain` and `base.sh prepare_pack`). Between builds what the parts hold of
   them never changed on disk: the delta carried none of their changes, no fork was told they were stale, what was
   pending never counted them, no part's account grew from them. First shakedown: 5 of 7 forks not told of a change
   they lacked, every one an index. Fix E: `watchdog.held_indexes` makes them again once for each commit of main,
   before the layers' and deltas' rules read them (0.3–0.7 s).
2. **Logic — a judging layer over the parts was made due by the chain's first message.** Built before the chain had a
   message (over the medium layer), its origin was not a message of the chain, so the first whole message
   "replaced its material": a rebuild of about 200K a judging role, after every refresh — the cost the owner's yes was
   to remove. And its forks were never counted behind (it holds no digest), so its churn would never have been built.
   Fix: `layer_stands` counts the parts the chain stands on (`delta.layer`) as held; a fork of a judging layer is
   behind whenever its digest is not the chain's top's, none included.
3. **Logic — warm entries judged cold, whole chains reloaded.** (a) `watchdog.layer_entry_age` read `WHO-base.hit`
   for a chain whose roles all fork role layers: nothing forks the base, its mark aged while the top part's pings
   answered, and the layer was refreshed "cold" at 00:47 (and 00:27 in another run). (b) `base_stack.warm` preferred
   `entry-hits/SID`, set only at a build, over the part's mark that base.sh's pings touch: the stable base, pinged every
   forty minutes, looked cold 56 minutes after its build and was loaded again with its whole chain and two role
   layers. Fixes: an entry's age is its latest read under any mark naming it (both functions); an OK ping in base.sh
   marks `entry-hits/SID` too.

## Simulation (world) corrections, not the harness's

- The project is a plain directory the replay writes each commit's changes into (`git diff`/`git show`), never git's
  work tree: a checkout took the harness copy back to the old commit's (git clears a sparse bit for files present).
- One forward-only clock file for every process; a session's replies are stamped just after the listing that confirms
  its start, and the clock moves past a session's last reply when a caller first sees it finished — as real sessions
  take time between a confirmed start, their replies, and whatever starts after them.
- Loads counted by the pack's own ratio (its estimate), everything else at 2.9 characters a token.
- `select_base_load.held_dir()` ignores `ORCH_HELD_DIR` (manifest honours it): coherent in the live layout, where both
  are the harness's `state/held`; the simulation leaves the variable unset.

## Assumptions of the model

- No role layer or reference reasoning has been built live: their thinking is assumed (15K and 20K output tokens).
- The prompt cache: an entry per request's prefix, one hour past its last write or read, a request reading the
  longest prefix alive within 20 blocks back (the API's lookback); the rest written.
- The recorded sessions' own growth is the same in every configuration (their reads happened under the old prefixes);
  what a fork lacks at its start is measured from git (the changed held units) and priced as the review's B: written
  once (2 a token).

## More machinery findings (the full runs)

4. **Economics — an executing role's churn built at once, forked by nobody.** The investigator's churn was built at
   00:38 and 02:09, 71K each, no fork of either. Every churn now follows the rule (copy five): forks of a bare layer
   count behind, and the first build is priced as it is (0.1 of the layer read, 2 of the chain written).
5. **Economics — pings of parts nothing reads.** Every part of every base pinged every forty minutes: 17–20M a day,
   the largest item of upkeep in every configuration, while in the whole day no refresh read an intermediate part.
   Copy five keeps a part warm only while its pings since its last use (a build over it, a fork of it) cost less than
   making it again — its own load for an intermediate part, the whole chain for the stable reference; the top part
   always.
6. **Structure — with every role on a layer, the delta's sessions serve almost nobody directly.** In the final
   configuration 9 of 16 messages were never forked: the churns take the messages' texts, and only judging layers'
   builds and the knowledge base fork the top. Each message still costs a fork of the layer (about 50–60K). Not
   changed: for the owner — messages could be texts for the churns, a session only where something forks it.
7. **Open, harmless:** 29 forks of high's churns were told plan-index changed while it had not (a transient; the held
   plan index equals a fresh one at the end of the run) — an over-report, a file read again.

## The day, by configuration (input-equivalent tokens; work is the replayed sessions' own requests)

| | before (live 20:57) | now (live 22:46) | final (live 23:17) | final, no deltas | final, no role layers |
|---|---|---|---|---|---|
| total | 528.7M | 537.5M | 531.5M | 525.9M | 511.1M |
| upkeep | 42.3M | 46.7M | 41.5M | 39.0M | 26.0M |
| pings (bases/parts + sessions) | 23.7M | 27.2M | 26.0M | 20.0M | 18.2M |
| stable reloads | 3.7M | 6.8M | 2.9M | 2.1M | 2.9M |
| role layers | 9.6M (32) | 4.9M (34) | 5.2M (36) | 10.0M (35) | — |
| churns / delta messages | 0.1M / 0.1M | 0.8M / 0.5M | 2.2M / 1.1M | — | — / 0.8M |
| work (prefix carried) | 486.5M (297.4M) | 490.9M (301.0M) | 490.0M (301.6M) | 486.9M (297.9M) | 485.1M (288.6M) |
| lacking at a fork's start, mean | 7,224 | 2,051 | 2,061 | 4,156 | 1,398 |
| forks not told a change they lack | 125 / 282 | 187 / 282 | 4 / 282 (truth drift) | 8 / 282 | 14 / 282 |

Reading it: work is ~92% of every day and the prefix carried in it ~57%; upkeep 5–9%. "now" was worse than "before"
(warm entries judged cold: the stable reloads doubled; the indexes invisible). "final" tells every fork exactly what it
lacks. Role layers cost about 15M of upkeep and 5M of carried prefix a day (~4%), a price for the priming the
simulation cannot measure; without them forks fork the delta's top and are the freshest. No deltas is ~6M cheaper
here but forks lack twice as much, and the model prices lacking at its changed units written once — a fork told a
file changed reads it again whole, which this undercounts.

## Copy five over the same day (deployed 23:51): every churn by its rule, parts pinged while worth keeping

total 519.0M (−12.5M against the round of 23:17), upkeep 30.4M (−27%): pings of the bases' parts 9.2M (from 17.2M),
churns 1.1M (from 2.2M), role layers 4.6M; a fork lacks 2,774 tokens at its start on average (2,061), the churns
waiting for their rule — about 0.4M more under B. One more reload of a stable reference than before (xhigh's at 22:30,
some twenty hours after its last use: the rent-or-buy's price, the pings it spared about equal to it). The max layer's
cold refresh at 15:52 is in every configuration since 23:17: the daemon's twelve-hour rule stops all of a base's pings
once `WHO-base.used` is that old, and planners fork the knowledge base, not max — left as it is, noted.

Reproduce: `simrun.py ORCH OUT --daemon-every 600` (about 15 minutes a day, five in parallel), `indexcache.py ORCH
RUN…` (the truth's indexes, seconds), `simreport.py OUT` (seconds).
