theory Factor_Required_History_Investigation
  imports Factor_Required_History_Cases
begin

definition required_history_quality where
  "required_history_quality m w f=required_history_inspect (required_history_assessment m
    (required_history_context (required_history_case w))) f"

lemma required_history_quality_exact:
  "required_history_quality m w f=required_history_family_condition f
    (required_history_family_method m) (required_history_case w)"
  by (simp only: required_history_quality_def required_history_assessment_exact)

interpretation required_history: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11]" "[0,1]" ws
    required_history_family_method required_history_family_condition required_history_case required_history_quality for ws
  by (unfold_locales) (rule required_history_quality_exact)

definition required_history_investigation where
  "required_history_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws required_history_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws required_history_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm required_history_investigation_def},
   equation = @{thm required_history.observations_derived},
   formation = @{thm required_history.maps_formed},
   observation = @{thm required_history.observation_at_subject},
   comparison = @{thm required_history.comparison_at_subject}}\<close>

definition required_history_packet where
  "required_history_packet ws selections=(let table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11] ws
      (\<lambda>w. required_history_context (required_history_case w)) required_history_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws table required_history_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11] [0,1]
      (fst compared) (fst (snd compared))) selections))"

definition required_history_indices :: "nat list" where "required_history_indices=[0..<12]"

end
