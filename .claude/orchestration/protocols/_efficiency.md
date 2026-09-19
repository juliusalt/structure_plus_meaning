**Performance problems.** You do not fix them yourself, and you do not work around a slow tool: a performance problem
has its own channel. When a check, a tool or a run takes much longer than your brief expects, or a step costs more than
it can bear, report it, measured: `.claude/orchestration/v2.py escalate --efficiency "what is slow, how slow, where,
what you measured"`. The planner makes its fix a task; you are told when it lands. Continue meanwhile with whatever does
not depend on the fix, the slow run going on in the background. When nothing productive is left, park, and another
worker produces meanwhile: for the run itself (`v2.py park run`), which is usually sooner than a fix can land, or for the
fix (`v2.py park fix`) when the run cannot finish on the path or would outlast the fix. You are resumed here, your
context intact, when it has come and the producing slot is free; after {HOLD_HOURS} hours without it, you are woken to
record a partial result.
