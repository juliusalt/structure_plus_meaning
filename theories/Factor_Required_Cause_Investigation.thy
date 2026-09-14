theory Factor_Required_Cause_Investigation
  imports Factor_Required_Cause_Assessment
begin

definition required_cause_problem where
  "required_cause_problem w=required_cause_family w"

definition required_cause_context where
  "required_cause_context covered w=(w,covered,prepare_decision_family required_cause_report (required_cause_problem w))"

definition required_cause_cell where
  "required_cause_cell m context=(case context of (w,covered,rows) \<Rightarrow>
    assess_prepared_decision_family (required_cause_decide 0) (required_cause_decide m) (covered,rows))"

lemma required_cause_cell_exact:
  "required_cause_cell m (required_cause_context required_cause_covered w)=
    required_cause_family_assessment m (required_cause_problem w)"
  by (simp only: required_cause_cell_def required_cause_context_def required_cause_family_assessment_def
    decision_family_assessment_def case_prod_conv)

definition required_cause_quality where
  "required_cause_quality m w f=decision_family_inspect
    (required_cause_cell m (required_cause_context required_cause_covered w)) f"

lemma required_cause_quality_exact:
  "required_cause_quality m w f=required_cause_family_condition f (required_cause_method m) (required_cause_problem w)"
  by (simp only: required_cause_quality_def required_cause_cell_exact required_cause_family_assessment_exact)

interpretation required_cause: finite_subject_investigation "[0,1,2,3,4,5,6,7]" "[0,1]" ws
  required_cause_method required_cause_family_condition required_cause_problem required_cause_quality for ws
  by (unfold_locales) (rule required_cause_quality_exact)

definition required_cause_investigation where
  "required_cause_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7] [0,1] ws required_cause_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7] [0,1] ws required_cause_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm required_cause_investigation_def},
   equation = @{thm required_cause.observations_derived},
   formation = @{thm required_cause.maps_formed},
   observation = @{thm required_cause.observation_at_subject},
   comparison = @{thm required_cause.comparison_at_subject}}\<close>

definition required_cause_packet where
  "required_cause_packet ws selections=(let covered=required_cause_covered;
    table=context_assessment_table [0,1,2,3,4,5,6,7] ws (required_cause_context covered) required_cause_cell;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7] [0,1] ws table decision_family_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7] [0,1]
      (fst compared) (fst (snd compared))) selections))"

theorem required_cause_packet_comparison:
  "fst (snd (required_cause_packet ws selections))=assessed_subject_investigation
    [0,1,2,3,4,5,6,7] [0,1] ws
      (\<lambda>m w. required_cause_cell m (required_cause_context required_cause_covered w)) decision_family_inspect"
  by (simp only: required_cause_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

definition required_cause_indices :: "nat list" where "required_cause_indices=[0..<10]"

end
