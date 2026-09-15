theory RRA_Encoded_Environment_Investigation
  imports RRA_Encoded_Environment_Assessments
begin

definition codec_environment_quality where
  "codec_environment_quality m w f=codec_environment_full_inspect (codec_environment_full_assess m
    (codec_environment_full_context (codec_environment_case w))) f"

lemma codec_environment_quality_exact:
  "codec_environment_quality m w f=codec_environment_full_condition f (codec_environment_full_candidate m) (codec_environment_case w)"
  by (simp only: codec_environment_quality_def codec_environment_full_assessment_exact)

interpretation codec_environment: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]" "[0,1,2]" ws
    codec_environment_full_candidate codec_environment_full_condition codec_environment_case codec_environment_quality for ws
  by (unfold_locales) (rule codec_environment_quality_exact)

definition codec_environment_investigation where
  "codec_environment_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2] ws codec_environment_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2] ws codec_environment_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm codec_environment_investigation_def},
   equation = @{thm codec_environment.observations_derived},
   formation = @{thm codec_environment.maps_formed},
   observation = @{thm codec_environment.observation_at_subject},
   comparison = @{thm codec_environment.comparison_at_subject}}\<close>


definition codec_environment_packet where
  "codec_environment_packet ws selections=(let
    methods=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15];
    table=context_assessment_table methods ws
      (\<lambda>w. codec_environment_full_context (codec_environment_case w)) codec_environment_full_assess;
    compared=context_assessment_investigation methods [0,1,2] ws table codec_environment_full_inspect;
    previous_scope=filter (\<lambda>w. w<20) ws;
    previous=context_assessment_investigation methods [0,1] previous_scope table codec_environment_full_inspect
    in (table,compared,
      map (investigation_cycle_report methods [0,1,2] (fst compared) (fst (snd compared))) selections,
      previous_scope,previous,
      map (investigation_cycle_report methods [0,1] (fst previous) (fst (snd previous))) [[],[0],[0,1]]))"

definition codec_environment_indices :: "nat list" where "codec_environment_indices=[0..<22]"

end
