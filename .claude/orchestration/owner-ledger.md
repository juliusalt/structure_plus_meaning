# Owner ledger

The owner's directions to an implementer, verbatim and dated, newest last; and the questions that are the
owner's to answer, each with the provisional choice made meanwhile and its basis. Every implementer reads
this file first and writes to it at once when the owner speaks. An entry leaves when the repository records it.

## Owner directions

**2026-09-18** (given when an agent said a stage "needs your authorization"):

> Do not wait for my authorization just continue with a choice you think fits with my intention and write it and ask if I respond differently then when I respond we will adjust.

**2026-09-18** (to impl-4, when it blocked in the foreground on an `until` loop waiting for a probe to finish):

> Once more you are making the same mistake of sitting and waiting for a tool.

**2026-09-19** (to impl-8, mid-batch, while the check of the demanded package readings was running):

> Once in a while when a milestone is reached the directory should be commited and pushed to the remote using the same style as already existing commits. Add this to memory.

**2026-09-19** (to impl-19, while the check of B11, the definition requests and verdict, was running):

> Judging from the commit notes the current workflow is the following - the problems are native, the machinery used to resolve them is native, but the packets are posed to give answers in Isabelle rather than native answers. Ofcourse in the end to verify a proof before genesis any new material needs to become Isabelle material, however it seems to me that there is a conflation between having to have the machinery that allows for the mapping and installation of native content as Isabelle machinery and having to produce that Isabelle content for every packet. That is these two steps could be seperated where packets first produce native content which can then be evaluated by native machinery allowing to use all of the existing native theory to evaluate the content and then as a seperate problem, once the content is deemed admisable by the machinery the translation and installation machinery can be used to add it as Isabelle content. I can be wrong analyze critically what I said.

**2026-09-19 06:56 UTC** (in Codex session 01a0b872, not to an implementer; recorded here by impl-21 from
`.claude/orchestration/state/owner-directions-new.md`):

> The RRA structures carry incidence and octets, but it seems to me that everything that is built on top of the foundation is using octects and not really incidence is that true? I might be completely wrong

**2026-09-19 06:59 UTC** (same Codex session, after its first answer pointed to the older foundation):

> Look into mainly the new material developed for native_control_plan.

The Codex answer (generated, not owner-level) concluded that for the native-control material the concern is
substantially justified: development notions (entity kinds, problem origins and authorities, Isabelle terms) are
Isabelle datatypes presented as trees of pairs with octet tags, incidence carries only the tree shape, references
are positions in a name table, and decisions (readiness, contracts, verdicts) are computed by proved HOL functions
and reflected into native questions as ground facets; incidence does real work in quotation, the indexed readers,
the adopted walk and generation citations. See Q6.

**2026-09-19** (to impl-21, while the confirming check of B12, the native answers, was running; answers Q6):

> The idea behind the rra structure was to seperate opaque inert data with no structure and structure by allowing atoms to carry octet payloads. On the level of allowed structure this is the best you can do, you cannot force someone using rra not to use the octets to carry actual encoded structural data. The idea was that this should be enforced by factor semantics - it is all designed to facilitate my priciples of structurlity, non-nominality, non-conflation, irredundancy, reuse, generalization by having all of these be clearly visible from the structure you are working on. Hence encoding structure as opaque data to define meaning is cardinally oposed to what I am trying to achieve. Note however that this does not imply that it can't be used this way for implementation if that is usefull - but there is even a trap here - if all implementation is non-structural then it can't itself adhere to my principles. Thus even implementation should be structural with the non-structural efficiency as a structurally presented idea that can be applied. Once you finish working on the current task reason about everything I said, see if it is correct and then make the appropriate tasks to combat this - the only time octects should be used are for trully inert opaque data with no structure - but this again needs to be nuanced and not taken literally - in some cases structural data can be carried as inert by other structures when it is truly non needed - the key is that all if structure is used then it needs to be explicit.

## Open questions to the owner

Each question below is being worked around with a provisional choice; the choice stays generated, not
owner-level, until the owner answers.

**Q1 (asked 2026-09-18 by impl-4; first raised by impl-2) — the admission rule of a bootstrap adoption and
OD-2.** The first loop admits an accepted answer as a generation whose policy is built from the entities of
the answer's own checked context (`Development_Successor.development_answer_generation_policy`); the
refinement constraint itself is the native verdict, computed by predecessor theories from the request state
and the answer state. OD-2 says no successor may justify its own adoption under rules introduced only by
itself. Provisional choice: before genesis the rule is fixed by the predecessor library (the policy
constructor and the verdict are theories of the published state; the answer supplies only the entities
Isabelle accepted, as evidence), and an answer can never supply or change that rule; after genesis only the
predecessor's amendment and transition chain admits. Basis: OD-2 (2026-09-04) and the preserved normative
role of Isabelle/HOL through genesis. Question: is Isabelle's acceptance of the answer's checked context,
judged by the predecessor-built verdict, the admission rule you intend for adoptions before genesis?

**Q2 (asked 2026-09-18 by impl-4) — authority of the first loop's problems and its selection criterion.**
The ten seeded refinement problems come from the measured paused candidates of
native_mechanism_speedup.md, a list generated outside the process; the plan gives that list owner authority
only if you authorize it. Selection among ready problems currently uses readiness alone, because any further
criterion (for example the measured cost on a path the finished process must use) would be a policy
criterion needing your authorization. Provisional choice: the list stays a recorded residual, selection
stays readiness alone, and the problem actually worked (`finite_data_walk`, whose cost dominates reading
recorded causes back) is chosen outside the process and recorded as a residual. Question: do you authorize
those candidates as first-loop problems, and a cost criterion for selection?

**Q3 (asked 2026-09-18 by impl-4) — what Isabelle establishes about adequacy.** You said: "I am not sure
how it can establish adequacy or why should it." DEVELOPMENT_WORKFLOW.md and plan.md §0.1 still say that
Isabelle establishes the bootstrap account's adequacy. Provisional choice (the plan's reading): Isabelle
establishes truth and formal adequacy between stated accounts only; adequacy to your intent is a current
basis under your authority, criticized and improved by the process. Question: is that the reading you want
the workflow document to state?

**Q4 (asked 2026-09-19 by impl-12) — an agent executor confined to its packet.** Stage 3's gate asks that
an agent, a deterministic program and a replayed retained answer yield the same admission. The harness
now confines an answer's text to its declared parts (`Development_Answer_Parts`), and the deterministic
executor and replays yield identical admissions; no agent has answered a packet as its only input, and
the one real answer (the indexed walk) was written by an unisolated implementer. Running an agent as an
executor means invoking a model (for example the `claude` command without tools, given only the packet),
which spends your usage and differs from the standing "no concurrent agents" direction of 2026-09-14,
although the plan names agents as executors. Provisional choice: no agent executor is run; the
deterministic executor and replays carry the interchangeability evidence, and the unisolated walk answer
stays a recorded residual. Question: may the harness run a model as an inert executor on packets, with no
tools and nothing but the packet as input?

**Q5 (asked 2026-09-19 by impl-18) — how far the native residual record reaches.** The plan asks every
choice generated outside the process to be a recorded residual. The native record holds the fourteen notions
of the loop as residual problems, and their definitions mention further development constants on the state's
frontier; followed transitively, the loop's notions reach about 1,500 development constants, 409 of them
declared in the 102 theories added since the plan's accepted base c4dfad1, and the whole workspace holds far
more, nearly all written before the native process existed. A native selection over more than a few hundred
residuals is not yet affordable. Provisional choice: the record grows by demand from the loop's notions, one
level of their frontier at a time, starting with the constituents their definitions mention directly, so that
a notion's residual depends on the residuals of what it is made of and the loop takes constituents first; the
theories that predate the plan stay the bootstrap library established under Isabelle's authority. Question:
should the record instead cover every constant defined since the plan's accepted base, every constant the
loop's notions reach, or the whole workspace?

Q6 (incidence versus tagged trees, asked 2026-09-19 by impl-21) was answered by the owner's direction of
2026-09-19 above; the plan section "Structure is explicit; octets are inert — 2026-09-19" records the analysis
and the tasks, taken next with the structural Isabelle state first (the order is impl-21's inference).
