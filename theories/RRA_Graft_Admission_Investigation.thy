theory RRA_Graft_Admission_Investigation
  imports RRA_Graft_Admission_Methods
begin

definition graft_admission_quality where
  "graft_admission_quality m w f=graft_admission_inspect
    (graft_admission_assessment m (graft_admission_context (graft_admission_case w))) f"

theorem graft_admission_quality_exact:
  "graft_admission_quality m w f=graft_admission_condition f (graft_admission_method m) (graft_admission_case w)"
  by (simp only: graft_admission_quality_def graft_admission_assessment_exact)

interpretation graft_admission: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12]" "[0,1]" ws
    graft_admission_method graft_admission_condition graft_admission_case graft_admission_quality for ws
  by (unfold_locales) (rule graft_admission_quality_exact)

definition graft_admission_investigation where
  "graft_admission_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12] [0,1] ws graft_admission_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12] [0,1] ws graft_admission_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm graft_admission_investigation_def},
   equation = @{thm graft_admission.observations_derived},
   formation = @{thm graft_admission.maps_formed},
   observation = @{thm graft_admission.observation_at_subject},
   comparison = @{thm graft_admission.comparison_at_subject}}\<close>

definition graft_admission_packet where
  "graft_admission_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11,12] ws
      (\<lambda>w. graft_admission_context (graft_admission_case w)) graft_admission_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12] [0,1] ws table graft_admission_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11,12] [0,1]
      (fst compared) (fst (snd compared))) selections))"

definition graft_admission_indices :: "nat list" where "graft_admission_indices=[0..<22]"

theorem graft_admission_packet_comparison:
  "fst (snd (graft_admission_packet ws selections))=assessed_subject_investigation
    [0,1,2,3,4,5,6,7,8,9,10,11,12] [0,1] ws
      (\<lambda>m w. graft_admission_assessment m (graft_admission_context (graft_admission_case w)))
      graft_admission_inspect"
  by (simp only: graft_admission_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

end
