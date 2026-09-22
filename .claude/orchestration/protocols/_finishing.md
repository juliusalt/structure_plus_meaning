**Recording.** What the task settles is written once, where it is read (DEVELOPMENT_WORKFLOW.md): its decisions, with
their evidence and limits, as an entry of DECISIONS.md — a decision of the development itself, a notion, its
semantics or what a proof establishes, never what the machinery or a run needs (a tool's default, a command's cost,
a limit of this machine), which belongs where the machinery is written or is reported as a performance problem; what a theory offers for reuse, in that theory's row of
THEORY_MAP.md; the evidence also in the commit message; what remains, in your result. native_control_plan.md changes
only with its structure, the stages' standing or the direction of the work, REASONING_REUSE.md only for a pattern of
reasoning it does not already state.

**Finishing.** When all that remains is the final job, hand it over in one call. Every request reads your whole
context again, several hundred thousand tokens, so a hand-over made one step a request — the row, the entry, the
commit message, the job, the result, each alone — costs four or five of those for nothing. One `v2.py change` writes what the
recording above still needs (THEORY_MAP.md's row, the DECISIONS.md entry), the commit message in the style of the
repository's commits (an imperative title, paragraphs on what changed and why, a closing Validation paragraph of what
you verified yourself — probes, measurements, a `v2.py check` you asked for; the harness adds the outcome of its own
checks of the work itself, so neither state nor promise them; no
attribution lines) and your result; the job and the record follow it in the same call, each only if what came before
went through:

    .claude/orchestration/v2.py change <<'EOF'
    === write .build/tasks/{ID}/commit.md
    …
    === write .build/tasks/{ID}/result.md
    …
    EOF
    .claude/orchestration/v2.py finalize {ID} --check "<the acceptance check>" --files <every file the commit takes> --message .build/tasks/{ID}/commit.md && .claude/orchestration/v2.py result {ID}

A commit of Markdown documents alone — none in theories/, tools/ or validation/, as a design's or an investigation's
decisions and records — is handed over without `--check`: the finalizer checks the documents and the sources itself,
in seconds and with no machine. The repository's check handed over as `--check "python3 -B tools/incremental_check.py
check --output DIR"` is run by the harness with every other check waiting, and not at all when the tree is the one its
`v2.py check` passed. The finalizer runs the check; a reviewer judges the work; then the commit and push follow. If the check
fails or the review rejects the work, you are woken here once, with the failure or every blocking finding, for a quick
fix ({FIX_MINUTES} minutes, {FIX_ROUNDS} requests, a refused one not counted); a second failure goes to the planner. A done result whose
deliverables lie outside .build is refused until the final job is handed over.
