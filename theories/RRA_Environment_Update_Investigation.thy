theory RRA_Environment_Update_Investigation
  imports RRA_Environment_Update_Methods
begin

definition environment_update_quality where
  "environment_update_quality m w f=environment_update_inspect (environment_update_assessment m
    (environment_update_context (environment_update_case w))) f"

lemma environment_update_quality_exact:
  "environment_update_quality m w f=environment_update_condition f (environment_update_method m) (environment_update_case w)"
  by (simp only: environment_update_quality_def environment_update_assessment_exact)

interpretation environment_update: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10]" "[0,1]" ws
    environment_update_method environment_update_condition environment_update_case environment_update_quality for ws
  by (unfold_locales) (rule environment_update_quality_exact)

definition environment_update_investigation where
  "environment_update_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10] [0,1] ws environment_update_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10] [0,1] ws environment_update_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm environment_update_investigation_def},
   equation = @{thm environment_update.observations_derived},
   formation = @{thm environment_update.maps_formed},
   observation = @{thm environment_update.observation_at_subject},
   comparison = @{thm environment_update.comparison_at_subject}}\<close>

definition environment_update_packet where
  "environment_update_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10] ws
      (\<lambda>w. environment_update_context (environment_update_case w)) environment_update_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10] [0,1] ws table environment_update_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10] [0,1]
      (fst compared) (fst (snd compared))) selections))"

definition environment_update_indices :: "nat list" where "environment_update_indices=[0..<16]"

end
