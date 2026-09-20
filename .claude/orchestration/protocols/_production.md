**Production and reading.** Production is a change to your deliverable that adds or changes content: a definition,
statement, locale or proof in a theory, about forty words of a document, about five lines of code (what counts for
your role is said above). Between two productions you may take at most {ROUNDS} requests and read at most {READ}K
tokens; after every read, search or check you are told what you have left, and past either limit reads, searches and
checks are refused: produce from what you hold, ask, or record what you have. A read of lines already in your context
and unchanged since is refused.

**Steps and their gathers.** Work in the steps of your plan. Open each step with its gather:
`.claude/orchestration/v2.py step {ID} N SOURCE...` prints, in one response and free of the limits, every source the
step needs, named at once: files (`path` or `path:FIRST-LAST`), facts and definitions by name (`Theory.name` or
`name`), and for a finished task `diff`, `result`, `log`. You decide what to name; name everything the step needs, so
that you then write from it. The next step's gather opens once this step has produced. `.claude/orchestration/show.py
NAME...` prints named facts whole outside a gather (it counts as reading).

**The working tree.** It has one owner at a time: while another task's finalization is in flight (its check, review,
fix and commit), that task owns it, so that its check, review and commit see its changes alone. Meanwhile you read the
working tree freely but write only under your task's directory: write new files there as drafts and probe them there,
and keep your edits of existing files for after; you are told when the tree is yours, then install your drafts and
continue. A producing session with nothing productive left meanwhile parks for it (`.claude/orchestration/v2.py park
tree`); a final job is handed over only while the tree is the session's own. No session stages, commits, stashes, checks out or
resets anything: the finalizer commits. A finalization holds the files it will commit while its check runs, while a
quick fix repairs them, and while it commits — not while it is reviewed: a review reads what was checked and writes
nothing, so that window is when an append to a shared record (DECISIONS.md, THEORY_MAP.md, ROOT) lands. If yours is
refused, you are told when the file is free. A task that leaves unfinished (parked, partial, lost) leaves its
installed work **in the working tree, whole** — the harness moves none of it. A change here is a set of parts (a
theory, the ROOT line declaring it, the import reaching it, its row, its entry) and a part taken out refuses every
task's check, not only its own. While such work stands, the tree is that task's: draft under
`.build/tasks/{ID}/`, and install when you are told it is free. If your brief says you continue that task's work,
it is already there to continue. At most two Isabelle runs go at once on this machine,
and none beside a final check that advances the base heap: a check is refused meanwhile, so continue with what needs
none. A run whose result is a **timing** takes the machine the same way, and must: a neighbour distorts the number as
surely as it exceeds the memory. Claim it before you launch (`.claude/orchestration/v2.py measuring "what you
measure"`), which is refused while anything else runs; the hold ends with your run, so claim it again for the next
measurement. A run that only checks proofs needs no claim and may go beside another.

**Checks.** Run checks in the background where your plan puts them and after a repair, not after every edit; continue
meanwhile with what follows or with an independent part, and the completion arrives while you work. A producing
session (designer, investigator, implementer, fixer) never waits holding the producing slot: when nothing productive
is left before a run of its own completes, it parks for it (`.claude/orchestration/v2.py park run`), and another worker
produces meanwhile; the run keeps going, keeps its changes in the working tree while it reads them, and the session is
resumed, its context intact, once the run has ended and the slot is free. Any other session ends its turn while its run
goes on, and the completion wakes it. Waiting is
refused (sleep, wait loops, reading a job's output before its completion, TaskOutput), and so are subagents. When a
check reports several failures, fix them together before the next check. When the same failure comes back after fixes
{CIRCLING} times in a row, further checks are refused until an answer on the obstruction has come: bring it to its
author or the planner.
