theory RRA_Digit_Generation_Investigation
  imports RRA_Digit_Generation_Cases
begin

definition digit_generation_quality where
  "digit_generation_quality m w f=digit_generation_inspect
    (digit_generation_assessment m (digit_generation_context (digit_generation_case w))) f"

lemma digit_generation_quality_exact:
  "digit_generation_quality m w f=digit_generation_condition f (digit_generation_method m) (digit_generation_case w)"
  by (simp only: digit_generation_quality_def digit_generation_assessment_exact)

interpretation digit_generation: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]" "[0,1]" ws
    digit_generation_method digit_generation_condition digit_generation_case digit_generation_quality for ws
  by (unfold_locales) (rule digit_generation_quality_exact)

definition digit_generation_investigation where
  "digit_generation_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] [0,1] ws digit_generation_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] [0,1] ws digit_generation_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm digit_generation_investigation_def},
   equation = @{thm digit_generation.observations_derived},
   formation = @{thm digit_generation.maps_formed},
   observation = @{thm digit_generation.observation_at_subject},
   comparison = @{thm digit_generation.comparison_at_subject}}\<close>

definition digit_generation_packet where
  "digit_generation_packet ws selections=(let table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] ws
      (\<lambda>w. digit_generation_context (digit_generation_case w)) digit_generation_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] [0,1] ws table digit_generation_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] [0,1]
      (fst compared) (fst (snd compared))) selections))"

end
