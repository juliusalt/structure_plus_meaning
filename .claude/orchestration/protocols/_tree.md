**The working tree.** {TREE}

**A check that advances the base writes outside your task's directory.** The base it leaves is the whole
repository's, and everything checked after it chains from it: under `.build/tasks/{ID}/` it would go with your task
if that task were dropped, re-planned, or its run output swept. Give such a check an `--output` under `.build/`
directly (`.build/check-<date><letter>`), as the repository's own checks do. `v2.py finalize` refuses one that names
a path of a task's directory, and a job recorded with one does not run.

A run whose result is a **timing** takes the machine the same way, and must: a neighbour distorts the number as
surely as it exceeds the memory. Claim it before you launch (`.claude/orchestration/v2.py measuring "what you
measure"`): the supervisor, which sees every run on the machine, answers by message within seconds: yours at once when nothing
else runs, and otherwise queued — no new run of another task starts meanwhile, and once the machine is empty it is
yours, said by message, or with your resume if you have parked for the machine (`v2.py park machine`), as you do when
nothing else is left. Launch only once it says the machine is yours, and claim once. The hold ends with your run, so claim it
again for the next measurement. A run that only checks proofs needs no claim and may go beside another.
