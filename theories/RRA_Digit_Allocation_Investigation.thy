theory RRA_Digit_Allocation_Investigation
  imports RRA_Digit_Allocation_Paths
begin

definition digit_allocation_quality where
  "digit_allocation_quality m w f=digit_allocation_inspect
    (digit_allocation_assessment m (digit_allocation_context (digit_allocation_case w))) f"

theorem digit_allocation_quality_exact:
  "digit_allocation_quality m w f=digit_allocation_condition f (digit_allocation_method m) (digit_allocation_case w)"
  by (simp only: digit_allocation_quality_def digit_allocation_assessment_exact)

interpretation digit_allocation: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11]" "[0,1]" ws
    digit_allocation_method digit_allocation_condition digit_allocation_case digit_allocation_quality for ws
  by (unfold_locales) (rule digit_allocation_quality_exact)

definition digit_allocation_investigation where
  "digit_allocation_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws digit_allocation_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws digit_allocation_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm digit_allocation_investigation_def},
   equation = @{thm digit_allocation.observations_derived},
   formation = @{thm digit_allocation.maps_formed},
   observation = @{thm digit_allocation.observation_at_subject},
   comparison = @{thm digit_allocation.comparison_at_subject}}\<close>

definition digit_allocation_packet where
  "digit_allocation_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11] ws
      (\<lambda>w. digit_allocation_context (digit_allocation_case w)) digit_allocation_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws table digit_allocation_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11] [0,1]
      (fst compared) (fst (snd compared))) selections))"

definition digit_allocation_indices :: "nat list" where "digit_allocation_indices=[0..<16]"

theorem digit_allocation_packet_comparison:
  "fst (snd (digit_allocation_packet ws selections))=assessed_subject_investigation
    [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws
      (\<lambda>m w. digit_allocation_assessment m (digit_allocation_context (digit_allocation_case w)))
      digit_allocation_inspect"
  by (simp only: digit_allocation_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

end
