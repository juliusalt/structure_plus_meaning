theory RRA_Artifact_Lookup_Investigation
  imports RRA_Artifact_Lookup_Methods
begin

definition artifact_lookup_quality where
  "artifact_lookup_quality m w f=artifact_lookup_inspect (artifact_lookup_assessment m
    (artifact_lookup_context (artifact_lookup_case w))) f"

theorem artifact_lookup_quality_exact:
  "artifact_lookup_quality m w f=artifact_lookup_condition f (artifact_lookup_method m) (artifact_lookup_case w)"
  by (simp only: artifact_lookup_quality_def artifact_lookup_assessment_exact)

interpretation artifact_lookup: finite_subject_investigation "[0,1,2,3,4,5,6]" "[0,1]" ws
    artifact_lookup_method artifact_lookup_condition artifact_lookup_case artifact_lookup_quality for ws
  by (unfold_locales) (rule artifact_lookup_quality_exact)

definition artifact_lookup_investigation where
  "artifact_lookup_investigation ws selected=investigation_basis [0,1,2,3,4,5,6] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6] [0,1] ws artifact_lookup_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6] [0,1] ws artifact_lookup_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm artifact_lookup_investigation_def},
   equation = @{thm artifact_lookup.observations_derived},
   formation = @{thm artifact_lookup.maps_formed},
   observation = @{thm artifact_lookup.observation_at_subject},
   comparison = @{thm artifact_lookup.comparison_at_subject}}\<close>

definition artifact_lookup_packet where
  "artifact_lookup_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6] ws
      (\<lambda>w. artifact_lookup_context (artifact_lookup_case w)) artifact_lookup_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6] [0,1] ws table artifact_lookup_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6] [0,1]
      (fst compared) (fst (snd compared))) selections))"

definition artifact_lookup_indices :: "nat list" where "artifact_lookup_indices=[0..<10]"

theorem artifact_lookup_packet_comparison:
  "fst (snd (artifact_lookup_packet ws selections))=assessed_subject_investigation
    [0,1,2,3,4,5,6] [0,1] ws
      (\<lambda>m w. artifact_lookup_assessment m (artifact_lookup_context (artifact_lookup_case w)))
      artifact_lookup_inspect"
  by (simp only: artifact_lookup_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

end
