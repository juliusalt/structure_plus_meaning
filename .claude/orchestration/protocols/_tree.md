**The working tree.** It has one owner at a time: while another task's finalization is in flight (its check, review,
fix and commit), that task owns it, so that its check, review and commit see its changes alone. Meanwhile you read the
working tree freely but write only under your task's directory: write new files there as drafts and probe them there,
and keep your edits of existing files for after; you are told when the tree is yours, then install your drafts and
continue. A producing session with nothing productive left meanwhile parks for it (`.claude/orchestration/v2.py park
tree`); a final job is handed over only while the tree is the session's own. No session stages, commits, stashes, checks out or
resets anything: the finalizer commits. A finalization holds the files it will commit while its check runs, while a
quick fix repairs them, and while it commits — not while it is reviewed: a review reads what was checked and writes
nothing, so that window is when an append to a shared record (DECISIONS.md, THEORY_MAP.md, ROOT) lands. If yours is
refused, you are told when the file is free.

{TREE}

A task that leaves unfinished (parked, partial, lost) leaves its
installed work **in the working tree, whole** — the harness moves none of it. A change here is a set of parts (a
theory, the ROOT line declaring it, the import reaching it, its row, its entry) and a part taken out refuses every
task's check, not only its own. While such work stands, the tree is that task's: draft under
`.build/tasks/{ID}/`, and install when you are told it is free. If your brief says you continue that task's work,
it is already there to continue. At most two Isabelle runs go at once on this machine,
and none beside a final check that advances the base heap: a check is refused meanwhile, so continue with what needs
none. **A check that advances the base writes outside your task's directory.** The base it leaves is the whole
repository's, and everything checked after it chains from it: under `.build/tasks/{ID}/` it would go with your task
if that task were dropped, re-planned, or its run output swept. Give such a check an `--output` under `.build/`
directly (`.build/check-<date><letter>`), as the repository's own checks do. `v2.py finalize` refuses one that names
a path of a task's directory, and a job recorded with one does not run.

A run whose result is a **timing** takes the machine the same way, and must: a neighbour distorts the number as
surely as it exceeds the memory. Claim it before you launch (`.claude/orchestration/v2.py measuring "what you
measure"`), which is refused while anything else runs; the hold ends with your run, so claim it again for the next
measurement. A run that only checks proofs needs no claim and may go beside another.
