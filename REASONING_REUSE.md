# Reasoning that must guide further generalization

The review of finite results is only one part of the required review. The
reasoning used to obtain the constructions must itself become reusable input
to development. The learned-schema interface now constructs conditional rules from a supplied
library and a finite frontier of possible premise calls. It retains each
constructed conclusion, complete binding, and premise occurrence. Semantic
evidence for known calls remains separate. The broader requirement is to make
the accumulated native construction arguments available to this development
process and to use it in choosing and assessing their applications.

The following is an inventory of accumulated arguments and their present
implementation boundary. A native construction already exists in several
rows. That does not mean that the machinery currently recognizes or chooses
its application.

| Repeated argument | General premises and conclusion | Existing native content | Missing use by development |
|---|---|---|---|
| Complete a computation's result class | A sound total computation witness and an exact comparison on its result class yield a function admitting every presentation of the result. | `context_result_comparison_schema` and its binary variant keep a private result and call the actual comparator; profile, loss, and complete table operations consume their contracts. | Discover the compatible witness/comparator pair from the requested contract, instantiate the construction, and return its prerequisites and candidate without my selecting the wrapper. |
| Keep the context boundary on empty traversals | Whole-context admission together with the existing contextual traversal preserves the context requirement even when no element is visited. | `admitted_context_schema` has the two actual premise calls; complete scope admission applies it. | Derive this development step from a context obligation and a traversal whose element checks do not establish that obligation in the empty case. |
| Preserve both levels of a collection | Complete element identity lifts through membership and two-sided coverage to finite-set identity; retaining an independent key prevents merging different keyed subjects. | Compared membership, related sets, and retained-key comparison generate the nested collection operations. | The admission planner now constructs pair and collection admission from nested goals, and reproduces complete investigation-input admission. Generating nested identity comparators and choosing their applicability remain separate work. |
| Compute every row, including empty results | A complete enumeration of keys and a total value computation yield the complete graph over those keys. | `keyed_calculation_schema`, complete finite-row contracts, Cartesian construction, and profile/loss table calculations. | Expand a complete-table requirement into key coverage, value totality, and complete result-class conditions, and construct the linked calculation. |
| Preserve a shared witness | Separate existential successes do not imply joint success; linked uses require one witness satisfying every participating condition. | Completion contracts and the existing compatible native construction/permission readers preserve the common source or witness. | Recognize the common intrinsic input in a development problem and keep its compatibility condition in the generated reasoning. |
| Reuse exact local contracts through products, transport, and specialization | Independently owned class and relation contracts determine when a larger construction may consume a component. | Complete product, list, finite-set, source, scope, and quotation classes; several ordinary readers implement their contracts. | Pair and collection admission goals now produce actual constructor arguments with source and component prerequisites. General transport, specialization, and applicability of the other complete contracts still need this connection. |
| Preserve actual premise and binder boundaries | A rule transformation must retain every premise socket, callee, head variable, premise-only variable, and material-only variable. | Native symbolic-call and clause-specialization checkers admit actual complete substitutions and prescribed socket presentations. | Use the admitted transformations to instantiate reusable reasoning schemas and retain their complete assertion and material boundaries. |
| Join only agreeing components | A program union preserves the intended component meanings when whole definitions agree on their actual overlap and dependencies are closed. | Shared-definition agreement, rooted groups, rebasing, and least dependency closures support the native joins. | Make agreement and closure explicit generated prerequisites of composition; do not discharge them merely from a shared component name. |
| Change an inadequate observation language | A full-language residual proves that selecting more of the same observations cannot suffice. A new observation needs its own semantic and coverage contract. | Repair obstructions and multiple newly constructed native observations exhibit this transition. | Use the failed subject relation and the reusable construction rules to generate new observation candidates, then evaluate them. |
| Preserve useful selections while revising conflicts | Withdraw unsound selections, retain the selected sound part, and recompute repair needs after withdrawal. | The new revision rule and list execution have Isabelle proofs; they have not yet received native Factor presentation and checking. | Integrate the transition with native construction and evidence, while keeping observation-language limits visible. |

The existing `Factor_Inference_Development` connection is the intended reuse
point. Admitted native schema instances already instantiate the general
inference relation, and actual conditional proof graphs supply qualified
residuals with assertion origins. Symbolic proof schemes also have a
mathematical instantiation and conditional-soundness account. The executable learned-schema interface now supplies a constructed conditional
rule family to this evaluator. Extracting a symbolic argument has a proved
mathematical boundary and soundness account. Native admission of the submitted
symbolic argument and of its mathematical justification remains open.

The next integration must therefore demonstrate a complete development use:
an independently stated problem, applicable reusable native rules, a generated
candidate, its instantiated premises, evidence for the discharged premises,
the remaining obligations, and execution against the original problem.
Hand-entering the already chosen candidate or a table saying that a technique
is suitable does not demonstrate that use. Construction, applicability,
semantic correctness, and coverage remain distinct claims.

This inventory distinguishes the implemented construction uses below from
the remaining integration work. A native planner, executable schema generation,
and an external Isabelle soundness proof are different forms of evidence.

## Generated reasoning in development

`Factor_Learned_Schemas` extracts the complete assertion and material boundary
of a checked symbolic argument. `Factor_Schema_Generation` constructs actual
applications by matching the complete ordinary premise family and retaining
all material checks. `Factor_Learned_Investigation` feeds those applications
into the existing inference machinery. This executor does not assign arbitrary
values to variables absent from the matched premises, and does not claim
complete search over unrestricted schemas or future library extensions.

The admission planner uses ordinary native recursive clauses to construct pair
and collection admission and thread their allocated identities. Its universal
installation contract preserves all original definitions, with explicit source
freshness and component support. The complete-input goal retains the original
scope and independent data relation. The generated plan reproduces the earlier
complete-input program at 336; every fresh starting counter has the same
all-term contract. Four executed starts, including a large natural identifier,
agree on all eleven input examples. Two starts outside the proved execution
range supply an explicit failed range check and no decisions.

A condensed pairing argument becomes a further conditional schema over the
actual native counter predicate. With no rule, the original goal is unresolved.
Adding the rule generates 27 applications while leaving the goal conditional
on a missing known premise. Establishing all three premises settles it. The
same library constructs applications for new counter values without a change
to the generation or inference driver. Plans still need the installation
contract's source and component prerequisites before they may be installed.

An adversarial frontier contains a formed term that the actual native counter
predicate refuses. Treating every possible premise as known settles a goal
independently proved false in the original planner. Native premise admission
retains the unresolved condition. `Factor_Learned_Execution_Soundness` proves
the general semantic bridge: generated closure inherits the library's
conditional soundness only with semantic evidence for every known call.

The machinery also compares three actual ways of using possible premises:
native admission, trusting the frontier, and establishing none. Premise
soundness alone leaves two failed comparisons. Its returned revision adds
the observation of useful settlement; executing that proposal settles this
three-method, two-workload comparison. Independent reconstruction finds native
admission alone satisfies every supplied condition. The useful-settlement
facet alone is adequate for this particular finite family; retaining the
original sound facet follows the general revision contract.

The [execution evidence](validation/generalization-review-2026-09-10/learned-reasoning/receipt.json)
checks thirty complete reports, including shared variables, separate premise
occurrences, premise-only and unbound private variables, each of the five
material operands, incomplete enumerations, socket conflicts, and malformed
unused inputs. Applications, schemas, bindings, premises, residuals, demand,
and reasons agree with an independent complete-valuation reconstruction.
Rejected inputs are not treated as semantic successes. The retained generated
module was replayed successfully using `tools/check_reasoning.py`; this review
is a host validation tool and does not supply native mathematical proofs.

Native mathematical-proof admission, complete symbolic-argument admission,
and native presentation of the whole development report remain open. The
broader library still needs private-witness completion, context boundaries,
nested comparisons, complete keyed calculations, and rules that propose and
assess development steps. The completed uses establish a working construction
and conditional-inference connection; they do not establish that every
required decision is already absorbed by the machinery.

## Complete specialization reports as reusable premises

The local symbolic-inference judgment now factors through an entire checked
clause specialization. Its equivalence to the existing scheme judgment keeps
the complete claim domain and every original discharge socket. The specialized
schema supplies all local variable and material fields. Paired determining
observations compare symbolic claims injectively and join the two premise
reports at their common socket and callee.

The ordinary rule at 342 combines the existing complete-specialization reader
at 294 with the complete schema report at 126. Both premises share the actual
target reference. Its finite schema decodes to this same ordinary rule and is
consumed by the existing generation and inference engine. The existing general
compilation contract supplies one native program before every future report.

The [complete execution evidence](validation/generalization-review-2026-09-10/specialization-report/receipt.json)
adds eight structural controls to the earlier thirty cases. Adding the rule
constructs an application with its two identified premises; a different target
constructs none. Multiple targets, alternative reports, repeated frontier
entries, separate goal occurrences, and malformed unused data retain their
declared boundaries. All complete reports match independent reconstruction.
The eight new controls establish neither reader premise: their known sets are
empty, and their goals remain unresolved. They test conditional construction,
not semantic admission of an actual submitted specialization.

This supplies local components for symbolic-argument admission. Native checking
of the complete graph, its claim table, assertion occurrences, and the final
extracted rule remains necessary. The machinery must also be used with actual
admitted source examples and the broader construction arguments identified
above. The current report rule does not discharge those remaining tasks.

## Constructed native premises for binding observations

Positioned clause specialization now has an exact inverse for its complete
bindings and ordinary and material sockets. It retains the owning use of every
source key. The complete graph and claim table can also be recovered from their
determining observations; this recovery applies to images of actual patterns.

Two native row projections instantiate the existing related-list traversal.
They construct both complete observations of one input sequence and retain its
order and repetitions. Their executable functions have an exact contract with
the native predicates. Their successful computations supply known premises,
with semantic evidence, to the unchanged inference engine. The learned report
clause joins them at their shared context and complete input. The general
clause-application theorem supplies the common soundness step for this rule and
the earlier specialization-report rule.

With the rule absent, the same established traversal premises leave the report
goal unresolved. Adding it constructs and settles the report. Wrong owners and
missing paired values produce no traversal premise. An incorrect requested
output remains unresolved despite a valid constructed alternative. Malformed
unused source fields reject the whole report even when another source supplies
a valid application. Equal first observations with different second observations
remain distinguishable; repeated rows and separate goal occurrences remain explicit.

The critical review also retains a successful conversion of a pair outside the
pattern-observation image. An empty-artifact target followed by an empty payload
cannot be the two observations of one pattern: the existing
[determining-observation theorem](theories/Factor_Substitution_Bindings.thy)
forces a literal payload pattern from the second value, contradicting the first.
The conversion correctly preserves these supplied fields. Actual use, complete
functional bindings, and pattern admission must come from the surrounding native
readers before graph-value recovery can be used.

The specialization-report operation also has a universal semantic totality
proof: every actually admitted native specialization has a complete target
report. Its inhabited instance reuses the existing actual ground-clause
construction. This semantic result is separate from executing the earlier
structural controls with unproved reader premises.

## Workflow audit and construction reuse

The review of 2026-09-11 found that the content workflow was not being followed
at its required breadth. The next problems, decompositions, relevant contracts,
and proposed native readers had been selected outside the machinery. The
source-readiness investigations tracked proof dependencies of those choices.
They did not generate or assess the choices. Prioritizing further native
admission did not make that departure necessary.

The resulting adequacy investigation asks whether the current driver can
consume a result it constructs in a subsequent construction. Its subject is
the existing native list-step clause at 345, with a scalar row premise at 343
and an empty-list premise. These are actual component predicates with existing
exact contracts. The independent native converter establishes the requested
two-row result.

In the [retained baseline](validation/generalization-review-2026-09-11/construction-chains/before/adequacy.json),
one construction succeeds, while the two- and three-step goals remain
unresolved. Supplying an intermediate call only as a possible premise allows
the existing inference closure to finish. Withholding its scalar evidence
leaves the conditions open. The nine complete reports agree with independent
reconstruction and replay from the retained code and recorded source revision.

This identifies a concrete requirement for further construction rounds that
preserve conditional evidence. It does not establish coverage of problem
selection, approach selection, information selection, or every other
development decision. Those uses remain part of the required workflow.

The bounded repair reuses the original generator through an equivalent
finite-set input interface. Additional rounds add generated calls to the
possible frontier, keeping the known facts unchanged. The original closure
soundness contract applies at every finite bound. Zero additional rounds has
exactly the original report, and the formation gate retains every original
input. The common variable-interface clause application step is now reused by
all three native construction libraries.

The [expanded investigation](validation/generalization-review-2026-09-11/construction-chains/after/adequacy.json)
contains 64 complete reports, 84 intermediate-frontier checks, nine computed
native seeds, and an independent native list comparison. Two- and three-step
goals settle from their original seeds. Missing evidence and insufficient
depth remain unresolved; malformed original inputs reject the report, and
false requested outputs remain unresolved. A two-row alphabet constructs all
14 nonempty lists through length three. The 38 earlier generic controls also
exercise the equivalent input interface at zero extra rounds.

## Native inference-specialization sources

Ordinary rules at 348, 349, and 350 connect paired bindings to an actual
replacement record, its complete target report, and the actual node's stored
table and clause citation. The programs agree on every shared definition.
Both record observations use the same source and support, and the target
report supplies the complete variable scope. The node and program share the
actual environment; the private binding-row enumeration permits independent
presentation orders.

The exact source contracts retain the actual clause, complete replacements,
all target fields, discharge occurrences, and support sets. These local
readings still need child-claim comparison and whole-graph admission before
they can admit a complete symbolic argument. Native mathematical-proof
admission and the broader development-decision workflow remain open.

## Library coverage and compilation

The next adequacy investigation asks whether the baseline construction library
can cover the new reader entries. Its eight complete reports leave entries
348, 349, and 350 unresolved through every tested depth, while existing binding
constructions succeed. Entry 342 has an application with unproved source
premises; the three missing entries have no producer in that library.

The reusable obstruction projects the actual complete schema premises to
their entry identities and retains their sockets. The existing conjunctive
inference engine computes closure, demand, and reasons. A general projection
theorem proves that every reported blocked goal remains a concrete residual
at every construction depth and for every possible frontier. Passing the
entry check supplies no converse: different terms at the same entry, shared
variables, material conditions, and unrecovered variables still matter.

The 65-case investigation checks every returned field independently. Its
report derives the next missing-constructor problems from the blocked goals
and actual library heads. The initial probes are formed terms used to test
entry coverage; they are not evidence of actual native source readings.
The universal obstruction theorem covers every term at those entries.

The resulting compiler uses the actual native clause definitions at 348–350.
Their finite representations are checked reductions of those definitions,
and their complete premise enumerations are generated from the schema fields.
All three have a conditional semantic contract in the same native program.
Malformed schema fields remain present for rejection by the whole-library gate.

Execution exposed a representation defect in singleton selection: repeating
one identical premise row caused a runtime exception, although both lists
present the same finite relation. The repair leaves the mathematical
enumeration unchanged and proves a new executable equation using an optional
singleton selector that checks every list value. Distinct sockets remain
distinct. All 50 compilation cases pass, including repeated encodings,
unordered sockets, empty families, malformed fields, and chained construction.
The exported native clause catalog is unchanged by the repair.

The [retained investigation](validation/generalization-review-2026-09-11/reader-libraries/README.md)
includes the original failure, its minimal control, proof inputs, complete
reports, and successful replays. The complete 794-theory session passes.
Using the compiled clauses to construct the new reader heads from their
actual component calls is the next content requirement. Whole argument
admission, mathematical-proof admission, and coverage of every development
decision remain open.
