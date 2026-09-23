**The working tree.** {TREE}

**A check that advances the base writes outside your task's directory.** The base it leaves is the whole
repository's, and everything checked after it chains from it: under `.build/tasks/{ID}/` it would go with your task
if that task were dropped, re-planned, or its run output swept. Give such a check an `--output` under `.build/`
directly (`.build/check-<date><letter>`), as the repository's own checks do. `v2.py finalize` refuses one that names
a path of a task's directory, and a job recorded with one does not run.

A run whose result is a **timing** is claimed before you launch it, and you say each time how it shares the machine
— there is no default:

- `.claude/orchestration/v2.py measuring --exclusive "what you measure"` holds the whole machine while your run goes:
  a neighbour distorts the number as surely as it exceeds the memory. **A held measurement is extremely expensive:**
  while it runs, no check, probe or landing of any task starts, so every other session and every landing waits on it.
  Make it quick: time only the part the number is for (its theories loaded before the timing begins, which needs no
  hold), and size it to fit within {MEASURE_MINUTES} minutes — fewer repetitions, a smaller input, one judgment rather
  than a replay; the hold lapses at {MEASURE_MINUTES} minutes, and what it times after that is not a held number. The
  supervisor, which sees every run on the machine, answers by message within seconds: yours at once when nothing else
  runs, and otherwise queued — no new run of another task starts meanwhile, and once the machine is empty it is yours,
  said by message, or with your resume if you have parked for the machine (`v2.py park machine`), as you do when
  nothing else is left. Launch only once it says the machine is yours, and claim once; the hold ends with your run.
- `.claude/orchestration/v2.py measuring --shared "what you measure"` holds nothing: your next check, in the
  foreground, is the measurement, admitted as any run of its kind — a heavy slot for a heavy run, a probe slot for a
  probe, in the machine's order — and fitted to the same {MEASURE_MINUTES} minutes. When contention does not matter
  for what you measure (two variants run in the same conditions and compared, an order of magnitude, a cost you judge
  with the load), this is the one to use. When it ends you are told the machine's load while it ran — the CPU's share
  busy, the share of the time runnable work waited for a CPU (the direct sign that contention slowed it), memory in
  use on average and at its peak, memory stalls — and what that says of the number.

Each measurement is recorded in `.build/tasks/{ID}/measurements.log` (when, how long, what for, how it shared the
machine, the load), where its review reads it. A run that only checks proofs needs no claim and may go beside another.
