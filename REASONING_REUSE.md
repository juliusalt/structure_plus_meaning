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
