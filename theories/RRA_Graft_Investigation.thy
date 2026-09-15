theory RRA_Graft_Investigation
  imports RRA_Graft_Methods
begin

definition graft_quality where
  "graft_quality m w f=graft_inspect (graft_assess (graft_method m) (graft_case w)) f"

lemma graft_quality_exact:
  "graft_quality m w f=graft_condition f (graft_method m) (graft_case w)"
  by (simp only: graft_quality_def graft_assessment_exact)

interpretation graft_comparison: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9]" "[0,1,2,3,4]" ws
    graft_method graft_condition graft_case graft_quality for ws
  by (unfold_locales) (rule graft_quality_exact)

definition graft_investigation where
  "graft_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] ws graft_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] ws graft_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm graft_investigation_def}, equation = @{thm graft_comparison.observations_derived},
   formation = @{thm graft_comparison.maps_formed}, observation = @{thm graft_comparison.observation_at_subject},
   comparison = @{thm graft_comparison.comparison_at_subject}}\<close>

definition graft_packet where
  "graft_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6,7,8,9] ws graft_case
      (\<lambda>m X. graft_assess (graft_method m) X);
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] ws table graft_inspect;
    semantics=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3] ws table graft_inspect
    in (table,compared,semantics,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4]
      (fst compared) (fst (snd compared))) selections))"

definition graft_indices :: "nat list" where "graft_indices=[0..<16]"

end
