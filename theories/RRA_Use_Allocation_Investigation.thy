theory RRA_Use_Allocation_Investigation
  imports RRA_Use_Allocation_Methods
begin

definition use_allocation_quality where
  "use_allocation_quality m w f=use_allocation_inspect
    (use_allocation_assess (use_allocation_method m) (use_allocation_case w)) f"

theorem use_allocation_quality_exact:
  "use_allocation_quality m w f=use_allocation_condition f (use_allocation_method m) (use_allocation_case w)"
  by (simp only: use_allocation_quality_def use_allocation_assessment_exact)

interpretation use_allocation: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9]" "[0,1,2,3,4]" ws
    use_allocation_method use_allocation_condition use_allocation_case use_allocation_quality for ws
  by (unfold_locales) (rule use_allocation_quality_exact)

definition use_allocation_investigation where
  "use_allocation_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] ws use_allocation_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] ws use_allocation_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm use_allocation_investigation_def},
   equation = @{thm use_allocation.observations_derived},
   formation = @{thm use_allocation.maps_formed},
   observation = @{thm use_allocation.observation_at_subject},
   comparison = @{thm use_allocation.comparison_at_subject}}\<close>

definition use_allocation_packet where
  "use_allocation_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6,7,8,9] ws use_allocation_case
      (\<lambda>m X. use_allocation_assess (use_allocation_method m) X);
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] ws table use_allocation_inspect;
    semantics=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3] ws table use_allocation_inspect
    in (table,compared,semantics,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4]
      (fst compared) (fst (snd compared))) selections))"

definition use_allocation_indices :: "nat list" where "use_allocation_indices=[0..<14]"

theorem use_allocation_packet_comparison:
  "fst (snd (use_allocation_packet ws selections))=assessed_subject_investigation
    [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] ws
      (\<lambda>m w. use_allocation_assess (use_allocation_method m) (use_allocation_case w))
      use_allocation_inspect"
  by (simp only: use_allocation_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

theorem use_allocation_packet_semantics:
  "fst (snd (snd (use_allocation_packet ws selections)))=assessed_subject_investigation
    [0,1,2,3,4,5,6,7,8,9] [0,1,2,3] ws
      (\<lambda>m w. use_allocation_assess (use_allocation_method m) (use_allocation_case w))
      use_allocation_inspect"
  by (simp only: use_allocation_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

end
