theory RRA_Indexed_Generation_Investigation
  imports RRA_Indexed_Generation_Cases
begin

definition indexed_generation_quality where
  "indexed_generation_quality m w f=indexed_generation_inspect
    (indexed_generation_assessment m (indexed_generation_context (indexed_generation_case w))) f"

lemma indexed_generation_quality_exact:
  "indexed_generation_quality m w f=indexed_generation_condition f (indexed_generation_method m) (indexed_generation_case w)"
  by (simp only: indexed_generation_quality_def indexed_generation_assessment_exact)

interpretation indexed_generation: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14]" "[0,1]" ws
    indexed_generation_method indexed_generation_condition indexed_generation_case indexed_generation_quality for ws
  by (unfold_locales) (rule indexed_generation_quality_exact)

definition indexed_generation_investigation where
  "indexed_generation_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1] ws indexed_generation_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1] ws indexed_generation_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm indexed_generation_investigation_def},
   equation = @{thm indexed_generation.observations_derived},
   formation = @{thm indexed_generation.maps_formed},
   observation = @{thm indexed_generation.observation_at_subject},
   comparison = @{thm indexed_generation.comparison_at_subject}}\<close>

definition indexed_generation_packet where
  "indexed_generation_packet ws selections=(let table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] ws
      (\<lambda>w. indexed_generation_context (indexed_generation_case w)) indexed_generation_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1] ws table indexed_generation_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1]
      (fst compared) (fst (snd compared))) selections))"

end
