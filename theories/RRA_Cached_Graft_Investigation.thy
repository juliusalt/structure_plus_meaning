theory RRA_Cached_Graft_Investigation
  imports RRA_Cached_Graft_Cases
begin

definition cached_graft_quality where
  "cached_graft_quality m w f=cached_graft_inspect
    (cached_graft_assessment m (cached_graft_context (cached_graft_case w))) f"

theorem cached_graft_quality_exact:
  "cached_graft_quality m w f=cached_graft_condition f (cached_graft_method m) (cached_graft_case w)"
  by (simp only: cached_graft_quality_def cached_graft_assessment_exact)

interpretation cached_graft: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12,13]" "[0,1]" ws
    cached_graft_method cached_graft_condition cached_graft_case cached_graft_quality for ws
  by (unfold_locales) (rule cached_graft_quality_exact)

definition cached_graft_investigation where
  "cached_graft_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13] [0,1] ws cached_graft_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13] [0,1] ws cached_graft_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm cached_graft_investigation_def},
   equation = @{thm cached_graft.observations_derived},
   formation = @{thm cached_graft.maps_formed},
   observation = @{thm cached_graft.observation_at_subject},
   comparison = @{thm cached_graft.comparison_at_subject}}\<close>

definition cached_graft_packet where
  "cached_graft_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11,12,13] ws
      (\<lambda>w. cached_graft_context (cached_graft_case w)) cached_graft_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12,13] [0,1] ws table cached_graft_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11,12,13] [0,1]
      (fst compared) (fst (snd compared))) selections))"

definition cached_graft_indices :: "nat list" where "cached_graft_indices=[0..<27]"

theorem cached_graft_packet_comparison:
  "fst (snd (cached_graft_packet ws selections))=assessed_subject_investigation
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13] [0,1] ws
      (\<lambda>m w. cached_graft_assessment m (cached_graft_context (cached_graft_case w)))
      cached_graft_inspect"
  by (simp only: cached_graft_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

end
