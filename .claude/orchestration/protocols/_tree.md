**The working tree.** {TREE}

No session stages, commits, stashes, checks out or resets anything: the finalizer commits. The orchestration's own
files (`.claude/orchestration/`, its state and the task list) are the owner's and no session's to write: what you find
wrong in the harness goes into your result, or to the planner.

At most {ISABELLE_MAX} Isabelle runs go at once on this machine,
and none beside a final check that advances the base heap: a check is refused meanwhile, so continue with what needs
none. **A check that advances the base writes outside your task's directory.** The base it leaves is the whole
repository's, and everything checked after it chains from it: under `.build/tasks/{ID}/` it would go with your task
if that task were dropped, re-planned, or its run output swept. Give such a check an `--output` under `.build/`
directly (`.build/check-<date><letter>`), as the repository's own checks do. `v2.py finalize` refuses one that names
a path of a task's directory, and a job recorded with one does not run.

A run whose result is a **timing** takes the machine the same way, and must: a neighbour distorts the number as
surely as it exceeds the memory. Claim it before you launch (`.claude/orchestration/v2.py measuring "what you
measure"`): the supervisor, which sees every run on the machine, answers by message within seconds, refusing while
anything else runs, and you launch only once it says the machine is yours. The hold ends with your run, so claim it
again for the next measurement. A run that only checks proofs needs no claim and may go beside another.
