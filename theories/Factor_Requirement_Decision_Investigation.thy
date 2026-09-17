theory Factor_Requirement_Decision_Investigation
  imports Factor_Requirement_Decision_Assessment Finite_Assessment_Reports
begin

definition requirement_decision_prepared :: "nat\<Rightarrow>native_requirement_problem\<Rightarrow>
    (nat\<times>requirement_decision_result) list\<Rightarrow>requirement_decision_result" where
  "requirement_decision_prepared m X bases=(if m<4 then
    (case map_of bases m of None \<Rightarrow> None | Some result \<Rightarrow> result)
    else requirement_decision_mutation m
      (case map_of bases 0 of None \<Rightarrow> None | Some result \<Rightarrow> result))"

lemma requirement_decision_prepared_exact:
  "requirement_decision_prepared m X (map (\<lambda>k. (k,requirement_decision_method k X)) [0,1,2,3])=
    requirement_decision_method m X"
proof (cases "m<4")
  case True
  have member: "m\<in>set [0,1,2,3]" using True by (auto; arith)
  show ?thesis by (simp only: requirement_decision_prepared_def True if_True
    mapped_function_lookup member; simp)
next
  case False
  show ?thesis by (simp add: requirement_decision_prepared_def False mapped_function_lookup
    requirement_decision_method_original requirement_decision_base_def requirement_decision_method_def
    requirement_decision_mutation_def option.map_id split: prod.splits option.splits)
qed

definition requirement_decision_cell where
  "requirement_decision_cell m C=map_option (\<lambda>(X,(reference,details),bases).
    let result=requirement_decision_prepared m X bases in
    (X,reference,result,requirement_decision_assessment_from X reference result)) C"

lemma requirement_decision_cell_exact:
  "requirement_decision_cell m (requirement_decision_context w)=map_option (\<lambda>X.
    (X,requirement_decision_reference X,requirement_decision_method m X,
      requirement_decision_assessment_from X (requirement_decision_reference X) (requirement_decision_method m X)))
    (native_requirement_problem w)"
  by (simp only: requirement_decision_cell_def requirement_decision_context_def option.map_comp
    comp_def case_prod_conv Let_def requirement_decision_prepared_exact)

definition requirement_decision_cell_inspect where
  "requirement_decision_cell_inspect cell (f::nat)=(case cell of None \<Rightarrow> False
    | Some (X,reference,result,assessment) \<Rightarrow> requirement_decision_inspect assessment f)"

definition requirement_decision_optional_condition where
  "requirement_decision_optional_condition f method X=(case X of None \<Rightarrow> False
    | Some x \<Rightarrow> requirement_decision_condition f method x)"

definition requirement_decision_quality where
  "requirement_decision_quality m w f=requirement_decision_cell_inspect
    (requirement_decision_cell m (requirement_decision_context w)) f"

theorem requirement_decision_quality_exact:
  "requirement_decision_quality m w f=requirement_decision_optional_condition f
    (requirement_decision_method m) (native_requirement_problem w)"
  by (simp add: requirement_decision_quality_def requirement_decision_cell_exact
    requirement_decision_cell_inspect_def requirement_decision_optional_condition_def
    requirement_decision_assessment_exact split: option.splits)

interpretation requirement_decision: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11]"
    "[0,1,2,3,4,5,6,7]" ws requirement_decision_method requirement_decision_optional_condition
    native_requirement_problem requirement_decision_quality for ws
  by (unfold_locales) (rule requirement_decision_quality_exact)

definition requirement_decision_investigation where
  "requirement_decision_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11]
    [0,1,2,3,4,5,6,7] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11] [0,1,2,3,4,5,6,7] ws requirement_decision_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11] [0,1,2,3,4,5,6,7] ws requirement_decision_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm requirement_decision_investigation_def},
   equation = @{thm requirement_decision.observations_derived},
   formation = @{thm requirement_decision.maps_formed},
   observation = @{thm requirement_decision.observation_at_subject},
   comparison = @{thm requirement_decision.comparison_at_subject}}\<close>

definition requirement_decision_packet where
  "requirement_decision_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11] ws
      requirement_decision_context requirement_decision_cell;
    comparison=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11] [0,1,2,3,4,5,6,7] ws table
      requirement_decision_cell_inspect
    in (table,comparison,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11] [0,1,2,3,4,5,6,7]
      (fst comparison) (fst (snd comparison))) selections))"

theorem requirement_decision_packet_comparison:
  "fst (snd (requirement_decision_packet ws selections))=assessed_subject_investigation
    [0,1,2,3,4,5,6,7,8,9,10,11] [0,1,2,3,4,5,6,7] ws
    (\<lambda>m w. requirement_decision_cell m (requirement_decision_context w)) requirement_decision_cell_inspect"
  by (simp only: requirement_decision_packet_def Let_def fst_conv snd_conv
    context_assessment_investigation_exact)

text \<open>
  Complete original contexts precede every candidate cell. Shared base
  constructions are reused without changing any candidate operation. The
  subject registry directly instantiates the common observation and comparison
  equations. Complete native execution and independent scope criticism remain
  prerequisites for adopting this proposed requirement-decision mechanism.
\<close>

end
