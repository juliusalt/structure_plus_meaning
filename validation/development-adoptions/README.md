# Adoptions of accepted answers

An adoption carries an accepted answer to a request of the refinement layer into the published
repository state. `tools/development_adoption.py --record R --output DIR` judges the retained answer
again and requires its retained verdict word (nothing the answer read has moved), installs the theory
Isabelle accepted when the answer was judged, byte for byte, as a repository theory imported by the
layer's boundary `Native_Execution_Refinements`, runs the ordinary incremental check (every report
word equal to its retained word), and judges the answer once more in the adopted workspace, where its
theory is part of the published state and must be an unchanged answer. A refused step withdraws the
installation. The receipt keeps every step and the measured seconds of every executed recipe beside
its retained seconds, as observations: no ranking or selection is derived from them, because no
internal account of a physical measurement exists yet.

Answers are framed where they are adopted: their theory imports exactly the boundary's imports, and
the request state is defined beside it, so the adopted theory is the theory Isabelle accepted and
there is one acceptance. The theory is named by the answer's canonical content; that name is a
transport choice that makes the theory unique and stable across replays, not a correspondence.

`--control` withdraws an established adoption again: the answer is a control of the process, not a
refinement to adopt. Controls are run in an isolated working copy of the repository, so the
published state never holds them; only their receipts are retained here.

`Development_Answer_5aba3385cee9.json` is the receipt of the control `demanded-reformulated`
(`ordered_member_tree` restated through `map (\<lambda>y. y)`), adopted and withdrawn in an isolated copy.

`Development_Answer_0ccf746fe2cf.json` is the first adoption of a real answer: the indexed complete data
walk answering the request for `Factor_Complete_Data_Walks.finite_data_walk`
([indexed-data-walk.json](../development-answers/indexed-data-walk.json)). The retained verdict refused it
for its six introduced constants and its repair accepted it over the extension defining them, so it was
adopted through the repaired request: the precondition reproduced the retained word, the judged theory
was installed at the boundary, the check proved 150 theories again (166 s of proof, 205 s in all),
executed the 11 recipes the change reaches with every word equal to its retained word and reused 40,
and the published state judged the answer as an unchanged answer. It stays in the published state.
The recipes that read recorded causes back ran in 10.9 against 26.5 s (certified causes), 27.7 against
44.7 s (digit replay), 16.6 against 25.0 s (constructed history) and 16.3 against 23.8 s (quoted
history); the others within about a second. These seconds were measured under the check's concurrent
load and are observations, not a ranking.
