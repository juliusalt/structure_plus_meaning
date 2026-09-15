theory Factor_Digit_Replay_Investigation
  imports Factor_Digit_Replay_Cases
begin

definition digit_replay_quality where
  "digit_replay_quality m w f=digit_replay_family_inspect
    (digit_replay_family_assessment m (digit_replay_family_context (digit_replay_case w))) f"

lemma digit_replay_quality_exact:
  "digit_replay_quality m w f=digit_replay_family_condition f (digit_replay_family_method m) (digit_replay_case w)"
  by (simp only: digit_replay_quality_def digit_replay_family_assessment_exact)

interpretation digit_replay: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]" "[0,1]" ws
    digit_replay_family_method digit_replay_family_condition digit_replay_case digit_replay_quality for ws
  by (unfold_locales) (rule digit_replay_quality_exact)

definition digit_replay_investigation where
  "digit_replay_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] [0,1] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] [0,1] ws digit_replay_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] [0,1] ws digit_replay_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm digit_replay_investigation_def},
   equation = @{thm digit_replay.observations_derived},
   formation = @{thm digit_replay.maps_formed},
   observation = @{thm digit_replay.observation_at_subject},
   comparison = @{thm digit_replay.comparison_at_subject}}\<close>

definition digit_replay_packet where
  "digit_replay_packet ws selections=(let table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] ws
      (\<lambda>w. digit_replay_family_context (digit_replay_case w)) digit_replay_family_assessment;
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] [0,1] ws table digit_replay_family_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] [0,1]
      (fst compared) (fst (snd compared))) selections))"

end
