# Repository instructions

Before starting repository work, and immediately after every context compaction,
read [DEVELOPMENT_WORKFLOW.md](DEVELOPMENT_WORKFLOW.md) in full from the repository.
Do this before resuming task-specific planning, tool calls, or edits. A retained
summary or remembered version does not replace this read.

Standing owner rule: no outside semantics, reasoning, or anything else is
allowed anywhere. It applies to the system and all development activity.
The owner explicitly preserves Isabelle/HOL's normative bootstrap role through
genesis. Follow that boundary and the complete rule in DEVELOPMENT_WORKFLOW.md;
a missing internal account creates no ad hoc external fallback permission.

Follow all requirements in that document, including preparing the largest useful
group of related work, requesting independent information together, and reviewing
combined validation and diagnostics before dependent follow-up. Continue
independent next problems while checks run, keeping their checked inputs fixed.

The owner's CPU has 16 cores and 32 hardware threads; use available parallelism for independent
work while keeping timing evidence and validation inputs reliable. Thread-count
settings alone do not satisfy this direction: structurally expose independent
computations so the runtime can actually execute them concurrently, where that
can be achieved without a lengthy detour.

Current owner priority: proceed directly to the high-level goals in problems.txt. Prioritize
establishing the complete workflow by construction over deep exploration of
individual components. Once that workflow is enforced, use component 6 to work
out the remaining details. Preserve the standing native-account, reusable
reasoning, criticism, and proof requirements while pursuing those high-level
goals; do not let component-level work become a tangent after compaction.

The closed native workflow and computed producer dispatcher are implemented in
Factor_Development_Cycle, Factor_Development_Steering and Factor_Steered_Development.
Use that path for covered native questions while pursuing the remaining
high-level conditions in problems.txt. Its finite scopes do not establish
broader adequacy; scope extensions require actual subjects, computed criticism
and review.

Condition 5 has two gates: demonstrate practical usefulness on real development
work before declaring problems.txt resolved; defer theoretical cost bounds
until after genesis. Prioritize actual use of the available workflow and
observed benefit. Availability and successful fixtures do not establish that
development is being driven through it.

Prepare substantial candidate batches and exercise them promptly. Individual
first-pass mistakes are acceptable; collect and repair exposed failures in
groups. Limit prolonged analysis of individual small changes. Adoption still
requires the complete applicable semantic account and validation.
