theory RRA_Allocated_Environment_Investigation
  imports RRA_Allocated_Environment_Cases
begin

definition allocated_update_quality where
  "allocated_update_quality m w f=allocated_update_inspect
    (allocated_update_assessment m (allocated_update_context (allocated_update_case w))) f"

theorem allocated_update_quality_exact:
  "allocated_update_quality m w f=allocated_update_condition f (allocated_update_method m) (allocated_update_case w)"
  by (simp only: allocated_update_quality_def allocated_update_assessment_exact)

interpretation allocated_update: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11]" "[0,1]" ws
    allocated_update_method allocated_update_condition allocated_update_case allocated_update_quality for ws
  by (unfold_locales) (rule allocated_update_quality_exact)

definition allocated_update_investigation where
  "allocated_update_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws allocated_update_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws allocated_update_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm allocated_update_investigation_def},
   equation = @{thm allocated_update.observations_derived},
   formation = @{thm allocated_update.maps_formed},
   observation = @{thm allocated_update.observation_at_subject},
   comparison = @{thm allocated_update.comparison_at_subject}}\<close>

definition allocated_update_packet where
  "allocated_update_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11] ws
      (\<lambda>w. allocated_update_context (allocated_update_case w)) allocated_update_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws table allocated_update_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11] [0,1]
      (fst compared) (fst (snd compared))) selections))"

definition allocated_update_indices :: "nat list" where "allocated_update_indices=[0..<16]"

theorem allocated_update_packet_comparison:
  "fst (snd (allocated_update_packet ws selections))=assessed_subject_investigation
    [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws
      (\<lambda>m w. allocated_update_assessment m (allocated_update_context (allocated_update_case w)))
      allocated_update_inspect"
  by (simp only: allocated_update_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

end
