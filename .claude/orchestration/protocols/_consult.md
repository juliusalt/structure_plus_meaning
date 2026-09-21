**Asking.** A decision that is not yours goes to whoever holds it: `.claude/orchestration/v2.py ask --to WHOM "..."`,
WHOM being `designer` (the author of the design your task builds on), `task-designer` (who briefed your task),
`reviewer` (who judged it), `kb` (the knowledge base: the owner's words, the decisions and why they were taken, what
exists) or `planner` (the graph, the order, a change of what other tasks rely on). An author whose cache has expired
is answered for by the knowledge base. Continue meanwhile with what does not depend on the answer. When nothing
independent is left, a producing session parks for it (`.claude/orchestration/v2.py park answer`: the producing
slot is free for another worker meanwhile, and you are resumed when the answer has come and the slot is free); any other ends its
turn, and the answer wakes it. Either way you continue here, your context intact. A question that is the owner's is
answered with a provisional choice; continue on it.
