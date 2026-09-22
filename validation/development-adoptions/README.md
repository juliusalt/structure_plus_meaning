# Adoptions of accepted answers

An adoption carries an accepted answer to a request of the refinement layer into the published
repository state. `tools/development_adoption.py --record R --output DIR` judges the retained answer
again and requires its retained verdict and publication words (nothing the answer read has moved) and
that its admitted, certified generation publishes over the incumbent it was judged against, installs the theory
Isabelle accepted when the answer was judged, byte for byte, as a repository theory imported by the
layer's boundary `Native_Execution_Refinements`, runs the ordinary incremental check (every report
word equal to its retained word), and then checks the adoption's evidence with the receipt it retains
and that the check's accepted context records the installed theory at the judged frame's digest
(`frame_sha256`). It refuses a theory of the answer's name that already stands and a tree whose
`theories/`, `ROOT` or `tools/` differ from its commit, which it retains as `revision`, and writes its
receipt here itself. Until task 265 its last step judged the answer once more in the adopted workspace,
which defined the answer state as the request state and judged the published state against itself
(DECISIONS.md, "An adoption is established by its evidence; the published state is never judged against
itself"): the `published` step of both receipts below is that self-comparison, kept as it ran, and it
established nothing about either answer. A refused step withdraws the installation.

An answer is adopted exactly when its evidence holds (`development_answer.adoption_evidence`): the
request's state adopts through the boundary, exactly one receipt here binds the answer's `answer_digest`
(the SHA-256 of its canonical content, which its theory name abbreviates) as adopted, not a control and not
withdrawn, the theory the receipt names at installation has the digest it retained there, and ROOT declares
it once and the boundary imports it. Receipts are found by `answer_digest`, not by their file name. Both
receipts gained that digest after they were written (task 263, named `answer_digest` since task 265): each
is derived from the answer of its record and marked so under `derived`; no step was rewritten. What no
workspace content establishes, that the published state is the answer state the judgment produced, is
reported as `unverified` wherever an adoption is. The receipt keeps every step and the measured seconds of
every executed recipe beside its retained seconds, as observations: no ranking or selection is derived from them, because no
internal account of a physical measurement exists yet.

Answers are framed where they are adopted: their theory imports exactly the boundary's imports, and
the request state is defined beside it, so the adopted theory is the theory Isabelle accepted and
there is one acceptance. The theory is named by the answer's canonical content; that name is a
transport choice that makes the theory unique and stable across replays, not a correspondence.

`--control` withdraws an established adoption again: the answer is a control of the process, not a
refinement to adopt. Controls are run in an isolated working copy of the repository, so the
published state never holds them; only their receipts are retained here.

`Development_Answer_5aba3385cee9.json` is the receipt of the control `demanded-reformulated`
(`ordered_member_tree` restated through `map (\<lambda>y. y)`). It was first adopted and withdrawn in an
isolated copy; on 2026-09-19 it was adopted again through the publication gate in the working tree and
withdrawn by the tool (the working tree held it only while the adoption ran): the precondition judged it
accepted and published (26.9 s), the check proved 151 theories again (170 s of proof, 315 s in all),
executed 48 recipes with every word equal and reused 3, and the published state was judged against
itself (27.3 s; the self-comparison above). `control` and `withdrawn` keep this receipt from ever
establishing an adoption.

`Development_Answer_0ccf746fe2cf.json` is the first adoption of a real answer: the indexed complete data
walk answering the request for `Factor_Complete_Data_Walks.finite_data_walk`
([indexed-data-walk.json](../development-answers/indexed-data-walk.json)). The retained verdict refused it
for its six introduced constants and its repair accepted it over the extension defining them, so it was
adopted through the repaired request: the precondition reproduced the retained word, the judged theory
was installed at the boundary, the check proved 150 theories again (166 s of proof, 205 s in all),
executed the 11 recipes the change reaches with every word equal to its retained word and reused 40,
and the published state was judged against itself (the self-comparison above). It stays in the published
state, and its evidence holds: the installed theory's digest is `9102596f…`, the digest the receipt
retained and the base's accepted context records, ROOT declares it and the boundary imports it. Its
`revision` is not recoverable, so the reproduction of its precondition is a residual of this receipt.
The recipes that read recorded causes back ran in 10.9 against 26.5 s (certified causes), 27.7 against
44.7 s (digit replay), 16.6 against 25.0 s (constructed history) and 16.3 against 23.8 s (quoted
history); the others within about a second. These seconds were measured under the check's concurrent
load and are observations, not a ranking.
