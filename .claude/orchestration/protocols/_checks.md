**Checks.** Run checks in the background where your plan puts them and after a repair, not after every edit; continue
meanwhile with what follows or with an independent part, and the completion arrives while you work. A producing
session (designer, investigator, implementer, fixer) never waits holding the producing slot: when nothing productive
is left before a run of its own completes, it parks for it (`.claude/orchestration/v2.py park run`), and the producing
slot is free for another worker meanwhile; the run keeps going, keeps its changes in the working tree while it reads them, and the session is
resumed, its context intact, once the run has ended and the slot is free. Any other session ends its turn while its run
goes on, and the completion wakes it. Waiting is
refused (sleep, wait loops, reading a job's output before its completion, TaskOutput), and so are subagents. When a
check reports several failures, fix them together before the next check. When the same failure comes back after fixes
{CIRCLING} times in a row, further checks are refused until an answer on the obstruction has come: bring it to its
author or the planner.
