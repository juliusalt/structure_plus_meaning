**Checks.** A change that writes a theory says, each time, whether it is probed: `v2.py change --probe <<'EOF'` probes
the theories it wrote as the change leaves them, and its reply says what the probe found — complete or not, its errors,
its time, its log — in the same request, so the probe after a change is not a request of its own; `v2.py change
--no-probe <<'EOF'` when more changes are to come before the theory can load, the last change of the step then
`--probe`. There is no default: a change that writes a theory and says neither is refused, nothing written. A probe of your own — other theories, a `--load`, a longer bound as a measurement —
runs in the foreground in the change's own call, on the line after it (it runs only if the change went through): it
takes seconds, where a probe in the background costs a request to park for it and another to read it. The proof base a probe or a check stands on is named by `.build/tasks/base-lasting/active-context.json`
(`tools/isabelle_places.py`); `/tmp/structural-active-context.json` is the older trees' and names an older base. A probe
is bounded at {PROBE_SECONDS} seconds, the probe tool's own default; where your tree holds an older
tool, name `--timeout {PROBE_SECONDS}` (a probe that would get longer is refused, naming what it would get). A probe's
proofs are forked: one run reports every proof of a theory that fails, and you fix them all before the next probe
(`--parallel-proofs 0`, which stops at the first, is left out of a probe). One that runs longer has a proof method that
did not terminate: run it again with `--parallel-proofs 0` and the call led by `IN_PLACE=1`, and its log names the
command it stopped at; a run that needs longer is a measurement, claimed first as exclusive or shared (`v2.py measuring --exclusive|--shared`). The repository's check
(`tools/incremental_check.py check`) of a task in a tree of its own is the harness's: ask for it with
`.claude/orchestration/v2.py check` where your plan puts one and after a repair, not after every edit. Your tree's work
as it stands is checked with main and the work of every other task waiting for one, once for all; you are parked, the
producing slot free, and resumed with its result — what failed that is yours, with its errors, or that it passed — and
the same tree handed over later is not checked again. Run any other heavy run (a replay, a build) — and the
repository's check of a task in the one tree — in the background where your plan puts it and after a repair, not after
every edit; continue meanwhile with what follows or with an independent part, and the completion arrives while you
work. A producing
session (designer, investigator, implementer, fixer) never waits holding the producing slot: when nothing productive
is left before a run of its own completes, it parks for it (`.claude/orchestration/v2.py park run`), and the producing
slot is free for another worker meanwhile; the run keeps going, your changes stay in the working tree while it reads
them, and you are resumed, your context intact, once the run has ended and the slot is free. Any other session ends
its turn while its run goes on, and the completion wakes it.

At most {ISABELLE_MAX} heavy Isabelle runs (checks, replays, builds) and {PROBE_MAX} probes go at once on this machine,
none while less than {MEM_MARGIN} GiB of its memory is free, and none beside a final check that advances the base
heap: a run is refused meanwhile, so continue with what needs none. When nothing else is left, a producing session
parks for the machine (`v2.py park machine`) and any other ends its turn: either is resumed, its context intact, when a
run may start, rather than trying again. A producing session's probe refused so is better led by `QUEUE=1` when it has
nothing else to do until it runs: it is queued and runs as soon as the machine has room, the session parked meanwhile
and resumed with its output; a change before a refused check in the same call goes through either way. A check runs
to its end and ends by listing every error it reported, one line each with where it stands and, while there is room,
what fixing it needs under it (a failed proof's goal, a type error's term and type) — Isabelle's messages, and for a check that failed whatever else failed:
a native execution, a recipe, a tool that raised (a long list is kept whole, and named). Fix them all together — and
what the same cause breaks elsewhere — before the next check: a check after each single fix spends a whole run on
each. When the same failure comes back after fixes {CIRCLING} times in a row, further checks are refused until an
answer on the obstruction has come: bring it to its author or the planner.
