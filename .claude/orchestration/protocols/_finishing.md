**Recording.** What the task settles is written once, where it is read (DEVELOPMENT_WORKFLOW.md): its decisions, with
their evidence and limits, as an entry of DECISIONS.md — a decision of the development itself, a notion, its
semantics or what a proof establishes, never what the machinery or a run needs (a tool's default, a command's cost,
a limit of this machine), which belongs where the machinery is written or is reported as a performance problem; what a theory offers for reuse, in that theory's row of
THEORY_MAP.md; the evidence also in the commit message; what remains, in your result. native_control_plan.md changes
only with its structure, the stages' standing or the direction of the work, REASONING_REUSE.md only for a pattern of
reasoning it does not already state.

**Finishing.** When all that remains is the final job, write the commit message in the style of the repository's
commits (an imperative title, paragraphs on what changed and why, a closing Validation paragraph; no attribution
lines) to .build/tasks/{ID}/commit.md, and hand the job over: `.claude/orchestration/v2.py finalize {ID} --check "<the
acceptance check>" --files <every file the commit takes> --message .build/tasks/{ID}/commit.md`. Then write your result
and record it. The finalizer runs the check; a reviewer judges the work; then the commit and push follow. If the check
fails or the review rejects the work, you are woken here once, with the failure or every blocking finding, for a quick
fix ({FIX_MINUTES} minutes, {FIX_ROUNDS} rounds); a second failure goes to the planner. A done result whose
deliverables lie outside .build is refused until the final job is handed over.
