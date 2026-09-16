theory Factor_Workflow_Input_Scope
  imports Factor_Required_Workflow_Comparison Finite_Selected_Assessments
begin

fun workflow_term_kind :: "finite_factor_term \<Rightarrow> nat" where
  "workflow_term_kind (Finite_Payload x)=0"
| "workflow_term_kind (Finite_Pair x y)=1"
| "workflow_term_kind (Finite_Target (Finite_Whole A))=2"
| "workflow_term_kind (Finite_Target (Finite_Anchor A a))=3"

fun workflow_goal_kinds :: "'d admission_goal \<Rightarrow> nat list" where
  "workflow_goal_kinds (Existing_Admission d)=[0]"
| "workflow_goal_kinds (Paired_Admission p q)=1#(workflow_goal_kinds p@workflow_goal_kinds q)"
| "workflow_goal_kinds (Collected_Admission p)=2#workflow_goal_kinds p"

fun workflow_candidate_kind :: "workflow_output_scope \<Rightarrow> nat" where
  "workflow_candidate_kind Workflow_Input=0"
| "workflow_candidate_kind (Workflow_Values xs)=1"
| "workflow_candidate_kind (Workflow_Generated d)=2"

definition workflow_scope_terms where
  "workflow_scope_terms X=concat (map (finite_term_component_rows \<circ> snd) X)"

definition workflow_scope_requirements where
  "workflow_scope_requirements X=concat (map (development_workflow_requirements \<circ> fst) X)"

definition workflow_input_scope_condition :: "nat \<Rightarrow>
    (required_workflow_subject list \<Rightarrow> required_workflow_subject list) \<Rightarrow>
    required_workflow_subject list \<Rightarrow> bool" where
  "workflow_input_scope_condition f method original=(let actual=method original in
    if f=0 then take (length original) actual=original
    else if f=1 then list_all (\<lambda>k. k\<in>set (map workflow_term_kind (workflow_scope_terms actual))) [0,1,2,3]
    else if f=2 then list_ex (\<lambda>t. workflow_term_kind t\<ge>2 \<and> \<not>finite_term_formed t) (workflow_scope_terms actual)
    else if f=3 then list_all (\<lambda>k. k\<in>set (concat (map workflow_goal_kinds
      (concat (map requirement_goals (workflow_scope_requirements actual)))))) [0,1,2]
    else if f=4 then list_all (\<lambda>k. k\<in>set (map (workflow_candidate_kind \<circ> requirement_candidates)
      (workflow_scope_requirements actual))) [0,1,2] else False)"

definition workflow_scope_artifact :: finite_exact_artifact where
  "workflow_scope_artifact=finite_enumerated_artifact [[0]] [([0],[0],[0])]
    [([0],[7]),([0],[7])] [([0],[8])]"

definition workflow_scope_additions :: "required_workflow_subject list" where
  "workflow_scope_additions=(let R=workflow_repeated_requirements workflow_required_identity;
    nested=workflow_required_identity\<lparr>requirement_source:=finite_guard_source True,
      requirement_goals:=[Paired_Admission (Existing_Admission (None,[1]))
        (Collected_Admission (Existing_Admission (None,[1])))]\<rparr> in
    [(R,Finite_Pair (Finite_Target (Finite_Whole workflow_scope_artifact))
        (Finite_Target (Finite_Anchor workflow_scope_artifact [0]))),
     (R,Finite_Target (Finite_Anchor finite_empty_artifact [])),
     (R\<lparr>required_requirement_reasoning:=nested\<rparr>,Finite_Payload [1,2])])"

definition workflow_input_scope_method :: "nat \<Rightarrow> required_workflow_subject list \<Rightarrow>
    required_workflow_subject list" where
  "workflow_input_scope_method m original=(if m=1 then original@take 1 workflow_scope_additions
    else if m=2 then original@workflow_scope_additions
    else if m=3 then drop 1 original@workflow_scope_additions else original)"

definition workflow_input_scope_problem :: "nat \<Rightarrow> required_workflow_subject list" where
  "workflow_input_scope_problem w=required_workflow_case_inputs"

definition workflow_input_scope_quality where
  "workflow_input_scope_quality m w f=workflow_input_scope_condition f (workflow_input_scope_method m)
    (workflow_input_scope_problem w)"

interpretation workflow_input_scope: finite_subject_investigation "[0,1,2,3]" "[0,1,2,3,4]" "[0]"
    workflow_input_scope_method workflow_input_scope_condition workflow_input_scope_problem workflow_input_scope_quality
  by (unfold_locales) (simp only: workflow_input_scope_quality_def)

definition workflow_input_scope_investigation where
  "workflow_input_scope_investigation selected=investigation_basis [0,1,2,3] [0,1,2,3,4] selected
    (subject_investigation_observations [0,1,2,3] [0,1,2,3,4] [0] workflow_input_scope_quality)
    (subject_investigation_relation [0,1,2,3] [0,1,2,3,4] [0] workflow_input_scope_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm workflow_input_scope_investigation_def},
   equation = @{thm workflow_input_scope.observations_derived},
   formation = @{thm workflow_input_scope.maps_formed},
   observation = @{thm workflow_input_scope.observation_at_subject},
   comparison = @{thm workflow_input_scope.comparison_at_subject}}\<close>

definition workflow_input_scope_packet where
  "workflow_input_scope_packet selections=(let
    table=context_assessment_table [0,1,2,3] [0] workflow_input_scope_problem
      (\<lambda>m X. (workflow_input_scope_method m X,map (\<lambda>f. (f,workflow_input_scope_condition f
        (workflow_input_scope_method m) X)) [0,1,2,3,4]));
    comparison=context_assessment_investigation [0,1,2,3] [0,1,2,3,4] [0] table
      (\<lambda>(actual,qualities) f. map_of qualities f=Some True)
    in (table,comparison,map (investigation_cycle_report [0,1,2,3] [0,1,2,3,4]
      (fst comparison) (fst (snd comparison))) selections))"

definition selected_workflow_input_scope where
  "selected_workflow_input_scope=map_option (\<lambda>m. workflow_input_scope_method m required_workflow_case_inputs)
    (list_singleton_option (subject_investigation_adequate [0,1,2,3] [0,1,2,3,4] [0] workflow_input_scope_quality))"

theorem selected_workflow_input_scope_conditions:
  assumes selected: "selected_workflow_input_scope=Some X" and facet: "f\<in>set [0,1,2,3,4]"
  shows "workflow_input_scope_condition f (\<lambda>_. X) required_workflow_case_inputs"
proof -
  obtain m where chosen: "list_singleton_option (subject_investigation_adequate [0,1,2,3] [0,1,2,3,4]
      [0] workflow_input_scope_quality)=Some m"
    and same: "X=workflow_input_scope_method m required_workflow_case_inputs"
    using selected by (auto simp: selected_workflow_input_scope_def split: option.splits)
  have "workflow_input_scope_quality m 0 f"
    by (rule singleton_adequate_conditions(2)[OF chosen _ facet]) simp
  then show ?thesis
    by (simp add: workflow_input_scope_quality_def workflow_input_scope_problem_def workflow_input_scope_condition_def same)
qed

text \<open>
  The original complete native requests are the scope problem. Coverage is
  calculated by traversing their actual terms, goals and candidate scopes.
  Malformation is the original finite-term formation check. This addresses
  the demonstrated codec coverage gap, not the adequacy of development roles.
\<close>

end
