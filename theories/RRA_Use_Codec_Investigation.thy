theory RRA_Use_Codec_Investigation
  imports RRA_Use_Codec_Cases
begin

definition use_codec_quality where
  "use_codec_quality m w f=use_codec_inspect
    (use_codec_assess (use_codec_method m) (use_codec_case w)) f"

theorem use_codec_quality_exact:
  "use_codec_quality m w f=use_codec_condition f (use_codec_method m) (use_codec_case w)"
  by (simp only: use_codec_quality_def use_codec_assessment_exact)

interpretation use_codec: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9]" "[0,1,2,3]" ws
    use_codec_method use_codec_condition use_codec_case use_codec_quality for ws
  by (unfold_locales) (rule use_codec_quality_exact)

definition use_codec_investigation where
  "use_codec_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9] [0,1,2,3] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9] [0,1,2,3] ws use_codec_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3] ws use_codec_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm use_codec_investigation_def},
   equation = @{thm use_codec.observations_derived},
   formation = @{thm use_codec.maps_formed},
   observation = @{thm use_codec.observation_at_subject},
   comparison = @{thm use_codec.comparison_at_subject}}\<close>

definition use_codec_packet where
  "use_codec_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6,7,8,9] ws use_codec_case
      (\<lambda>m X. use_codec_assess (use_codec_method m) X);
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3] ws table use_codec_inspect;
    semantics=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9] [0,1,2] ws table use_codec_inspect
    in (table,compared,semantics,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9] [0,1,2,3]
      (fst compared) (fst (snd compared))) selections))"

definition use_codec_indices :: "nat list" where "use_codec_indices=[0..<16]"

theorem use_codec_packet_comparison:
  "fst (snd (use_codec_packet ws selections))=assessed_subject_investigation
    [0,1,2,3,4,5,6,7,8,9] [0,1,2,3] ws
      (\<lambda>m w. use_codec_assess (use_codec_method m) (use_codec_case w)) use_codec_inspect"
  by (simp only: use_codec_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

theorem use_codec_packet_semantics:
  "fst (snd (snd (use_codec_packet ws selections)))=assessed_subject_investigation
    [0,1,2,3,4,5,6,7,8,9] [0,1,2] ws
      (\<lambda>m w. use_codec_assess (use_codec_method m) (use_codec_case w)) use_codec_inspect"
  by (simp only: use_codec_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

end
