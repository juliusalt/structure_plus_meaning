# Answers to development requests

Each record retains an executor's answer exactly as submitted (the declared presentation: new
definitions, the equation and its proof, and the request it answers, named by its state and the
subject's name), the outcome of `tools/development_answer.py` on it, the digest of the harness and
the receipt of the accepted base context it was checked against. The framing theories, the proof
session, the export and the presented word are reproduced from these by running the harness again
on that base; they are not retained. A judged answer's `verdict_word` is the size and SHA-256 of
the presented verdict and repair, and `summary` is the harness's diagnostic reading of them.

These five answers exercise the loop on the seeded request for
`Factor_Digit_Replay_Methods.digit_replay_inspect`: the subject's current equation restated
(accepted), a proof Isabelle refuses, an added axiom (refused; not repairable), an equation using a
constant outside the issued support (refused; the extension adds its declaration and the same
answer is accepted against the request issued again), and an equation through a helper the answer
introduces (refused; the extension adds the helper's declaration, definition and code equation,
one definition problem is derived, and the same answer is accepted against the request issued
again). They are controls of the process, not refinements to adopt.

`deterministic.json` is the answer `tools/development_executor.py` computed from the packet of the
same request alone (`tools/development_answer.py packet`; the record keeps the packet's digest and
the executor's): it restates the demanded statement and proves it by the frame's fact
`development_demanded_code`. Its admission word is identical to that of `identity.json`, the same
equation stated by an agent, and to the word retained for it: an answer is admitted by the state it
defines, not by who states it.

`python3 -B tools/replay_development_answers.py --output DIR` runs the harness again on every
retained answer against the active base and compares outcome and verdict word with the record. A
differing word marks a record whose requested state or verdict changed since it was made; that
answer is then a re-evaluation for the process.

`demanded-identity.json` answers a request derived on demand in the refinement layer (state
`refinement_layer`): the harness exports the state of `Ordered_Member_Trees.ordered_member_tree`
alone from `Native_Execution_Refinements`, and the answer restates its code equation. It is accepted,
and its successor answers the one problem that state poses.
