theory Development_Seed_Verification
  imports Development_Seed_Loop Development_Refinement_Verification Development_Successor
begin

section \<open>The verdict is exercised on answer states derived from each request\<close>

text \<open>
  No answer to a seeded request has been verified yet, so the verdict is exercised on answer
  states computed from the seeded state and the request itself, each standing for one kind of
  answer. The unchanged state and its reversed table are answers that keep the demanded
  statement; the verdict must accept both, and the second shows that it reads no position.
  Every other control changes what a refinement may not change, or changes the subject's
  equation outside the support: stating the subject's equations as axioms, dropping the
  subject's equations, stating the equation through a constant the state does not know,
  changing the equations of the other seeded subjects, and removing the subject's kernel
  definition. Each control is derived from the request and the state, names no position of
  either list and selects no subject.
\<close>

fun isabelle_right_wrap :: "isabelle_term \<Rightarrow> isabelle_term \<Rightarrow> isabelle_term" where
  "isabelle_right_wrap g (Isabelle_Application (Isabelle_Application (Isabelle_Constant e T) l) r)=
    Isabelle_Application (Isabelle_Application (Isabelle_Constant e T) l) (Isabelle_Application g r)"
| "isabelle_right_wrap g (Isabelle_Application (Isabelle_Constant j T) p)=
    Isabelle_Application (Isabelle_Constant j T) (isabelle_right_wrap g p)"
| "isabelle_right_wrap g t=t"

definition development_absent_name :: "String.literal list \<Rightarrow> String.literal" where
  "development_absent_name names=foldr (+) names STR ''.absent''"

definition development_seed_controls :: "development_request \<Rightarrow> isabelle_rooted_context list" where
  "development_seed_controls r=(case r of (p,s,support,E) \<Rightarrow>
    let (R,C)=development_seed_state; names=fst C; es=snd C; P=problem_subject p;
      others=fset_of_list development_seed_root_constants |-| P;
      fresh=Isabelle_Constant (length names) (Isabelle_Type_Application (length names) []) in
    [development_seed_state,
     development_seed_renamed,
     (R,(names,es@map (\<lambda>e. Isabelle_Specification (the (isabelle_code_equation_proposition e)))
       (filter (development_answer_equation C P) es))),
     (R,(names,filter (\<lambda>e. \<not>development_answer_equation C P e) es)),
     (R,(names@[development_absent_name names],
       map (\<lambda>e. if development_answer_equation C P e
         then Isabelle_Code_Equation (isabelle_right_wrap fresh (the (isabelle_code_equation_proposition e))) else e) es@
       [Isabelle_Development_Constant fresh])),
     (R,(names,filter (\<lambda>e. \<not>development_answer_equation C others e) es)),
     (R,(names,filter (\<lambda>e. \<not>(isabelle_specified_proposition e\<noteq>None \<and> isabelle_code_equation_proposition e=None \<and>
       list_ex (\<lambda>c. c |\<in>| P) (isabelle_entity_subjects names (isabelle_development_constants es) e))) es))])"

type_synonym development_seed_verification = "(development_refinement_verdict\<times>bool) list list"

definition development_seed_verification :: "development_problem fset \<Rightarrow> development_seed_verification" where
  "development_seed_verification answered=Parallel.map (\<lambda>r. map (\<lambda>S'.
     let v=development_refinement_verdict development_seed_state r S' in (v,development_refinement_accepted v))
     (development_seed_controls r)) (development_seed_requests answered)"

definition development_seed_verification_data :: "development_seed_verification \<Rightarrow> finite_factor_term" where
  "development_seed_verification_data=finite_sequence_presentation (finite_sequence_presentation
    (finite_pair_presentation development_refinement_verdict_data finite_boolean_data))"

lemma development_seed_verification_data_injective [intro]: "inj development_seed_verification_data"
  unfolding development_seed_verification_data_def
  by (intro finite_sequence_presentation_injective finite_pair_presentation_injective
    development_refinement_verdict_data_injective finite_boolean_data_injective)

definition development_seed_verification_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_seed_verification_value answered=
    development_seed_verification_data (development_seed_verification answered)"

text \<open>
  The expected verdicts are fixed by the kinds of answer, not by the seeded values: both
  unchanged answers are accepted; the axiom is an added entity that is no equation of the
  subject; the dropped equations leave the subject without an equation; the unknown constant
  is an added declaration and the one constant outside the support; the other subjects'
  equations and the subject's definition are removed entities a refinement may not remove.
  These controls exercise the verdict's refusals; an actual answer is judged by the same
  verdict on the state its checked context defines.
\<close>


section \<open>An admitted answer moves the seeded development to its successor\<close>

text \<open>
  The seeded development starts from the seeded state, its problems and dependencies, nothing
  answered and no history. For every request, the unchanged answer and the answer with the
  reversed table are admitted, and the successor carries the answered problem, the generation
  and every other problem; the readiness of the successor and the currency of the other
  requests are computed on it. Both answers change nothing a request reads, so every other
  request stays current and every other problem stays ready.
\<close>

definition development_seed_loop_state :: "development_problem fset \<Rightarrow> development_loop" where
  "development_seed_loop_state answered=(development_seed_state,development_seed_problems,
    development_seed_dependencies,answered,[])"

text \<open>
  The seeded development library holds no decomposition rule, so every selected problem is a
  leaf and is issued with the reading of that absence. A control library that decomposes every
  problem into itself issues nothing: each problem is refused as a broad request, and the
  unsupported cycle settles nothing. The request of a problem is the refinement request of its one
  subject constant, read from the problem itself.
\<close>

definition development_seed_library :: development_dependencies where
  "development_seed_library={||}"

definition development_seed_cyclic_library :: development_dependencies where
  "development_seed_cyclic_library=fset_of_list (map (\<lambda>p. (p,{|(0,p)|})) development_seed_problems)"

definition development_seed_request_of :: "development_problem \<Rightarrow> development_request option" where
  "development_seed_request_of p=(case sorted_list_of_fset (problem_subject p) of
     [c] \<Rightarrow> development_refinement_request development_seed_context Development_Residual Development_Generated c
   | _ \<Rightarrow> None)"

type_synonym development_seed_succession =
  "bool\<times>(development_problem list\<times>development_request list\<times>development_problem list\<times>development_problem list\<times>
    development_request list\<times>development_request list\<times>
    (development_problem fset\<times>development_record list\<times>development_problem list\<times>bool list) option list list) option"

text \<open>
  The selection is made once, as the recorded native decision of the seeded development, and the
  admitted problems are issued once; every successor starts from the development that recorded
  both. The report presents the problems the selection admitted, whose executed packet the loop
  report already presents, the issued requests, the problems left unissued, the problems the
  cyclic control refuses, and for each successor only the records it adds. It also decides the
  premise under which the answers to the independent requests keep each other current: the seeded
  state declares every constant once. Finally it re-evaluates the issue records against the seeded
  library, where every reading still holds, and against the cyclic library, where every issued
  request relied on an absence that no longer holds.
\<close>

definition development_seed_succession :: "development_problem fset \<Rightarrow> development_seed_succession" where
  "development_seed_succession answered=(distinct (List.map_filter isabelle_declared_constant (snd development_seed_context)),
   case development_loop_selection (development_seed_loop_state answered) of
     None \<Rightarrow> None
   | Some (L,xs) \<Rightarrow> (case development_loop_issue development_seed_library development_seed_request_of L xs of
       (L2,issued,unissued) \<Rightarrow> (case development_loop_issue development_seed_cyclic_library development_seed_request_of L xs of
         (L3,control,refused) \<Rightarrow> (case L2 of (S,ps,D,done0,recorded) \<Rightarrow>
           Some (xs,issued,unissued,refused,development_reevaluations development_seed_library recorded,
             development_reevaluations development_seed_cyclic_library recorded,Parallel.map (\<lambda>r. map (\<lambda>S'. map_option (\<lambda>(S2,ps,D,closed,history).
             (closed,drop (length recorded) history,development_ready_problems D closed ps,
              map (development_request_current (snd development_seed_state) (snd S')) issued))
             (development_successor L2 r S'))
             [development_seed_state,development_seed_renamed]) issued)))))"

definition development_seed_succession_data :: "development_seed_succession \<Rightarrow> finite_factor_term" where
  "development_seed_succession_data=finite_pair_presentation finite_boolean_data (finite_option_presentation (finite_pair_presentation development_problems_data
    (finite_pair_presentation development_requests_data
      (finite_pair_presentation development_problems_data (finite_pair_presentation development_problems_data
        (finite_pair_presentation development_requests_data (finite_pair_presentation development_requests_data
        (finite_sequence_presentation (finite_sequence_presentation
          (finite_option_presentation (finite_pair_presentation (finite_collection_presentation development_problem_data)
            (finite_pair_presentation (finite_sequence_presentation (development_record_data finite_development_context_value))
              (finite_pair_presentation development_problems_data (finite_sequence_presentation finite_boolean_data))))))))))))))"

lemma development_seed_succession_data_injective [intro]: "inj development_seed_succession_data"
proof -
  have presented: "inj (development_record_data finite_development_context_value)"
    by (rule development_record_data_injective) (rule finite_development_values_injective(3))
  show ?thesis
    unfolding development_seed_succession_data_def
    by (intro finite_option_presentation_injective finite_pair_presentation_injective presented finite_boolean_data_injective
      finite_sequence_presentation_injective finite_collection_presentation_injective development_requests_data_injective
      development_problem_data_injective development_problems_data_injective finite_boolean_data_injective)
qed

definition development_seed_succession_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_seed_succession_value answered=
    development_seed_succession_data (development_seed_succession answered)"

end
