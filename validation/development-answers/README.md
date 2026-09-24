# Answers to development requests

Each record retains an executor's answer exactly as submitted (the declared presentation: new
definitions, the equation and its proof, and the request it answers, named by its state and the
subject's name), the outcome of `tools/development_answer.py` on it, the digest of the harness and
the receipt of the accepted base context it was checked against. The framing theories, the proof
session, the export and the presented words are reproduced from these by running the harness again
on that base; they are not retained. A judged answer's `verdict_word` is the size and SHA-256 of
the presented verdict and repair, its `publication_word` those of the presented publication (below),
and `summary` is the harness's diagnostic reading of them.

Since 2026-09-19 the harness also presents the publication of every judged answer as its own report
(`Development_Admitted_Publication`): the incumbent of the request state and, when the answer is
admitted, the answer recorded beside it, both as generations whose causes are certified under the
policy that lists their family, and the transaction that publishes the answer over the incumbent it
was judged against. A repaired answer is admitted, and published, against the request issued again
over the extension. The summary's `published` reads whether that transaction applied; admission and
selection stay separate words, and a refused answer publishes nothing while its incumbent is still
judged. Since the loop's decisions are admitted generations (`Development_Decision_Generations`), the
publication also records the issue of the request, made on demand and so citing no selection, at the
problem's issue locus, citing the incumbent; the answer cites the issue, the issue is admitted where no
issue stood and the answer then replaces the incumbent. The six judged answers were re-recorded then:
their publication words changed and their verdict words did not.

Since 2026-09-19 Isabelle also reads every framed answer's declared parts, before the answer's theory
exists, with the outer syntax of the answer's frame (`Development_Answer_Parts`). An answer whose parts
hold anything but definitional commands, theorem statements with their proofs and document text, one
proposition and one proof is `refused`, with Isabelle's reason as its `refusal`, and its theory is never
processed. Five controls on the seeded request exercise that reading, each refused with its reason:
`injected-ml.json` (definitions that run ML), `escaped-equation.json` (an equation that closes its quotes
and continues with commands), `continued-proof.json` (a proof followed by a command that runs ML),
`declared-attribute.json` (a lemma declared as a simplification rule, which would act on every theory
importing the adopted answer) and `ml-method.json` (a proof by a method that runs ML). `axiom.json`, which
had reached the verdict and been refused for its axiom, is now refused at its parts, because
`axiomatization` is not a declared part; the verdict's refusal of axioms stays exercised natively by the
seed's derived answer states. A failed judgment (Isabelle refused the answer's theory or its
verification) is a different outcome: `failed-proof.json` retains its failure as `error`, the
harness's field, and the replay compares it as it compares a refusal.

These five answers exercise the loop on the seeded request for
`Factor_Digit_Replay_Methods.digit_replay_inspect`: the subject's current equation restated
(accepted), a proof Isabelle refuses, an added axiom (refused; not repairable), an equation using a
constant outside the issued support (refused; the extension adds its declaration and the same
answer is accepted against the request issued again), and an equation through a helper the answer
introduces (refused; the extension adds the helper's declaration, definition and code equation,
one definition problem is derived, whose contract is the helper as the extension declares it, and the
same answer is accepted against the request issued again). They are controls of the process, not refinements to adopt.

`deterministic.json` is the answer `tools/development_executor.py` computed from the packet of the
same request alone (`tools/development_answer.py packet`; the record keeps the packet's digest and
the executor's): it restates the demanded statement and proves it by the frame's fact
`development_demanded_code`. Its admission word is identical to that of `identity.json`, the same
equation stated by an agent, and to the word retained for it: an answer is admitted by the state it
defines, not by who states it.

`python3 -B tools/replay_development_answers.py --output DIR` runs the harness again on every
retained answer against the active base and compares outcome, verdict word and publication word with
the record. A differing word marks a record whose requested state, verdict or publication changed
since it was made; that answer is then a re-evaluation for the process. An adopted answer's record is
the judgment that admitted it before adoption; the harness now judges the published state instead, so
the replay reports its present judgment beside the record and never re-records it
(`indexed-data-walk.json` keeps its admission, without a publication word). A native record is judged
from its state module exported from the active base, so its replay needs a base whose proof context
holds that module's whole import closure as the replayed sources have it. On a base that lags them
(on 2026-09-22, `Native_Execution_Refinements` once `Factor_Shared_Package_Readings` had joined its
imports) `export_proved_code.py` refuses the export and the native records come out unproduced by
construction, which is neither a differing word nor a failed build.

`demanded-identity.json` answers a request derived on demand in the refinement layer (state
`refinement_layer`): the harness exports the state of `Ordered_Member_Trees.ordered_member_tree`
alone from `Native_Execution_Refinements`, and the answer restates its code equation. It is accepted,
and its successor answers the one problem that state poses.

Since 2026-09-18 an answer's theory is named by the answer's canonical content
(`Development_Answer_<digest>`), and an answer to a refinement-layer request is framed where it would
be adopted: its theory imports exactly the imports of the layer's boundary, beside the request state,
so the theory Isabelle accepts is the theory an adoption installs
([development-adoptions](../development-adoptions/README.md)). The frame's fact
`development_demanded_code` is read by `Isabelle_Constant_Closure`, the reading the exporter uses.
A record whose answer introduces a constant presents that constant under its theory's name, so the
records made under the earlier fixed name `Development_Answer` differ in exactly that name.

`demanded-reformulated.json` is a control on the same refinement-layer request: it states
`ordered_member_tree` through `map (\<lambda>y. y)`, so the verdict reads the incumbent equation removed and
its own added, and accepts it. It was adopted and withdrawn in an isolated copy
([receipt](../development-adoptions/Development_Answer_5aba3385cee9-41e74a23a6af.json)).

`indexed-data-walk.json` is the first real answer: the request for
`Factor_Complete_Data_Walks.finite_data_walk` (two incumbent code equations) is answered by the complete
data walk stated over four readers of an artifact and its indexed instance, whose address-keyed readers
are `Binary_Relation_Stores` under `address_binary_path` and whose carrier is read through
`Ordered_Member_Trees`. The verdict refuses it for its six introduced constants; the repair extends the
request state by exactly their declarations and specifications, the extension is conservative, and the
same answer is accepted against the request issued again. It was adopted through that repaired request
([receipt](../development-adoptions/Development_Answer_0ccf746fe2cf.json)). The answer was written by an
agent from the packet without isolation, and choosing this constant rather than a seeded root was made
outside the process; both are residuals.

Since 2026-09-19 an answer can be native content instead of Isabelle text (`native: true` in its record):
the edit it makes to the request state, the entities it removes and adds presented with the names they
use (`Development_Native_Answers`). `tools/native_answers.py packet` presents the native packet of a
request (its constant, support, least context and incumbent, with their names) as a word and reads it
back; `tools/development_executor.py --native` answers it; `tools/native_answers.py judge` packs the
answer into the octets of its word and has the exported native judgment read and judge them. The record
retains the answer, the digest of its octets, the judgment word and a summary (read, accepted, the
verdict's counts, the constants outside the support, and the numbers of names, removed and added
entities). The judgment establishes admissibility for installation; installing a native answer as
Isabelle material, and Isabelle's acceptance of it, is a separate request.

`native-restating.json` is the deterministic executor's native answer to the seeded request for
`Factor_Digit_Replay_Methods.digit_replay_inspect`: it removes the packet's incumbent equation and adds it
again over the packet's thirty names, and is read and accepted. `native-dropped.json` removes the
incumbent and adds nothing; it is read and refused, the subject being left without its equation.
