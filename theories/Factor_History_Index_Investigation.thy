theory Factor_History_Index_Investigation
  imports Factor_History_Index_Cases
begin

definition history_index_quality where
  "history_index_quality m w f=history_index_inspect
    (history_index_assessment m (history_index_context (history_index_case w))) f"

lemma history_index_quality_exact:
  "history_index_quality m w f=history_index_family_condition f
    (history_index_family_method m) (history_index_case w)"
  by (simp only: history_index_quality_def history_index_assessment_exact)

interpretation history_index: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12,13]" "[0,1]" ws
    history_index_family_method history_index_family_condition history_index_case history_index_quality for ws
  by (unfold_locales) (rule history_index_quality_exact)

definition history_index_investigation where
  "history_index_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13] [0,1] ws history_index_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13] [0,1] ws history_index_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm history_index_investigation_def},
   equation = @{thm history_index.observations_derived},
   formation = @{thm history_index.maps_formed},
   observation = @{thm history_index.observation_at_subject},
   comparison = @{thm history_index.comparison_at_subject}}\<close>

definition history_index_packet where
  "history_index_packet ws selections=(let table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11,12,13] ws
      (\<lambda>w. history_index_context (history_index_case w)) history_index_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12,13] [0,1] ws table history_index_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11,12,13] [0,1]
      (fst compared) (fst (snd compared))) selections))"

end
