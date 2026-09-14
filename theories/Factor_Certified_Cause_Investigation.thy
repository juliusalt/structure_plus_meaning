theory Factor_Certified_Cause_Investigation
  imports Factor_Certified_Cause_Assessment
begin

definition certified_cause_context_from where
  "certified_cause_context_from seed covered w=(seed,w,covered,
    prepare_decision_family certified_cause_report (certified_cause_family seed w))"

definition certified_cause_cell where
  "certified_cause_cell m context=(case context of (seed,w,covered,rows) \<Rightarrow>
    assess_prepared_decision_family (certified_cause_decide 0) (certified_cause_decide m) (covered,rows))"

lemma certified_cause_cell_exact:
  "certified_cause_cell m (certified_cause_context_from seed (certified_cause_covered seed) w)=
    certified_cause_family_assessment m (seed,w)"
  by (simp only: certified_cause_cell_def certified_cause_context_from_def certified_cause_family_assessment_def
    decision_family_assessment_def case_prod_conv)

definition certified_cause_problem where
  "certified_cause_problem w=(literal_replay_seed,w)"

definition certified_cause_quality where
  "certified_cause_quality m w f=decision_family_inspect (certified_cause_cell m
    (certified_cause_context_from literal_replay_seed (certified_cause_covered literal_replay_seed) w)) f"

theorem certified_cause_quality_exact:
  "certified_cause_quality m w f=certified_cause_family_condition f
    (certified_cause_method m) (certified_cause_problem w)"
  by (simp only: certified_cause_quality_def certified_cause_cell_exact
    certified_cause_family_assessment_exact certified_cause_problem_def)

interpretation certified_cause: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11]" "[0,1]" ws
    certified_cause_method certified_cause_family_condition certified_cause_problem certified_cause_quality for ws
  by (unfold_locales) (rule certified_cause_quality_exact)

definition certified_cause_investigation where
  "certified_cause_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws certified_cause_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws certified_cause_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm certified_cause_investigation_def},
   equation = @{thm certified_cause.observations_derived},
   formation = @{thm certified_cause.maps_formed},
   observation = @{thm certified_cause.observation_at_subject},
   comparison = @{thm certified_cause.comparison_at_subject}}\<close>

definition certified_cause_packet where
  "certified_cause_packet ws selections=(let seed=literal_replay_seed; covered=certified_cause_covered seed;
    table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11] ws
      (certified_cause_context_from seed covered) certified_cause_cell;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws table decision_family_inspect
    in (seed,table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11] [0,1]
      (fst compared) (fst (snd compared))) selections))"

theorem certified_cause_packet_comparison:
  "fst (snd (snd (certified_cause_packet ws selections)))=assessed_subject_investigation
    [0,1,2,3,4,5,6,7,8,9,10,11] [0,1] ws
      (\<lambda>m w. certified_cause_cell m (certified_cause_context_from literal_replay_seed
        (certified_cause_covered literal_replay_seed) w)) decision_family_inspect"
  by (simp only: certified_cause_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

definition certified_cause_indices :: "nat list" where
  "certified_cause_indices=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14]"

export_code certified_cause_packet checking SML

end
