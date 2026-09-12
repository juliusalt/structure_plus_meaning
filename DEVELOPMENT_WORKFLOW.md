# Development workflow

Before starting repository work, and immediately after every context compaction,
read this document in full from the repository before resuming task-specific work.
A retained summary or remembered version does not replace this read. Restore the
active problem, outstanding requirements, and the current batch from the retained
context only after rereading these operating requirements.

The owner's standing rule is:

> No outside semantics or reasoning or anything else is allowed anywhere.

This governs the system and its entire development, including bootstrap,
candidate construction, observation, criticism, selection, validation,
implementation, and retention. Every subject, relation, requirement, rule,
operation, and judgment must have its complete RRA account and Factor meaning.
Prose, host code, external models or proof procedures, manual judgment,
metadata, digests, and supplied satisfaction tables cannot supply a missing
internal account. Storage and execution mechanisms receive no exemption.

A missing internal representation, operation, or justification remains an unmet
requirement. It does not authorize an external substitute, an interim fallback,
or a bootstrap exception. This rule supersedes earlier permissions for outside
candidate generation, criticism, development decisions, and semantic or proof
authority. Recording this rule does not establish that the repository already
complies with it.

The owner's instructions apply to every problem encountered during the work,
including questions about the generalization machinery itself. A generalizable
argument must be factored into reusable content at its first use. A later use
should instantiate that content, with its actual prerequisites, rather than
reconstruct the argument. A case-specific exception needs an explicit reason.

For every problem of interest, run the generalization machinery and use its
results to guide the work. Before making the dependent decision or change,
state the problem and its requirements, submit the applicable reasoning and
candidates to the machinery, execute it, inspect the complete results and
reasons, and use them to select or revise the next action. Recording a plan,
describing a candidate, or running an investigation after acting does not
satisfy this requirement.

This applies to choosing which problems to work on, choosing approaches,
identifying needed information, deciding how to use it, deciding what to change
and how, deciding what reasoning to generalize, evaluating the machinery's
value and adequacy, and improving the machinery itself. These examples are not
exhaustive. Proof repairs, validation choices, workflow changes, and other
development decisions are included; the scope is not limited to entries in
OBLIGATIONS.md.

Independently criticize the question, candidate scope, observations, reusable
reasoning, evidence, and returned results. Execution does not certify their
adequacy, accuracy, reliability, or usefulness. When criticism exposes a gap,
submit that gap and the proposed correction through the same process. Candidate
generation and independent criticism are themselves subject to the standing
rule. A manually selected answer cannot replace an internally derived decision.
Quality remains paramount, and criticism is part of this workflow, not an
exemption from using it.

Each content cycle must retain the independently stated problem, applicable
reusable reasoning, instantiated premises, generated candidates or proposed
changes, evidence for settled premises, remaining conditions, and a critical
assessment against the original problem. When a required reasoning operation
is missing, its absence is itself an explicit development problem. A manually
chosen answer or a descriptive table must not be reported as machinery-driven
construction.

Problems, candidates, conditions, and observations must have concrete structural
subjects. A computed observation needs an exact contract connecting its actual
operation and complete input to the independently stated condition. If indices
present those subjects, their maps and the observation equation must establish
that connection. A retained description or digest establishes which bytes
accompanied an execution; it does not establish what the computation means.
A supplied observation table establishes no satisfaction claim about another
subject. That subject, the observation operation, and its satisfaction boundary
must be internally established. Evaluation of a supplied table cannot replace
derivation of the required observations.

Incomplete native admission does not suspend the standing rule. A conditional
result retains every unresolved premise and cannot discharge it through an
outside judgment. A missing representation or reasoning operation becomes a
development problem in the machinery. Source-readiness investigations
answer questions about proof dependencies; they do not by themselves choose
or justify a problem, approach, decomposition, or proposed change.

For host scheduling, prepare the largest useful group of related work that
preserves quality. Determine its information needs first, then request all
independent reads together. Use that information to prepare the complete group
of changes. Submit those changes together with the applicable validation and
the diagnostics needed to plan the next group. Inspect the combined results
before preparing the next batch. Avoid separate polling, one-file reads, and
one-fix proof retries when independent useful work can be included. Dependencies
within the batch remain ordered. Quality takes precedence over batch size.

After preserving the source, proof, and execution evidence needed for continued
work or repository validation, remove generated files and temporary build
copies that are no longer needed. Record the retained evidence that replaces
those copies. Keep temporary storage bounded throughout the work, including
after failed runs; do not accumulate obsolete files under `/tmp`.

Current implementation boundaries and the accumulated reasoning inventory are
recorded in [REASONING_REUSE.md](REASONING_REUSE.md). The continuing content review
rule and historical evidence are in [GENERALIZATION_REVIEW.md](GENERALIZATION_REVIEW.md).
This workflow document states the operating requirement; it does not claim that
every needed native decision procedure has already been implemented.
