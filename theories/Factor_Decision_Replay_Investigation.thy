theory Factor_Decision_Replay_Investigation
  imports Factor_Decision_Replay_Correctness
begin

definition decision_replay_cell where
  "decision_replay_cell m C=map_option (\<lambda>(X,(reference,details),bases).
    let result=decision_replay_prepared m X bases in
    (X,reference,result,decision_replay_assessment_from X reference result)) C"

lemma decision_replay_cell_exact:
  "decision_replay_cell m (decision_replay_context w)=map_option (\<lambda>X.
    (X,requirement_decision_reference X,decision_replay_method m X,
      decision_replay_assessment_from X (requirement_decision_reference X) (decision_replay_method m X)))
    (native_requirement_problem w)"
  by (simp only: decision_replay_cell_def decision_replay_context_def option.map_comp
    comp_def case_prod_conv Let_def decision_replay_prepared_exact)

definition decision_replay_cell_inspect where
  "decision_replay_cell_inspect cell (f::nat)=(case cell of None \<Rightarrow> False
    | Some (X,reference,result,assessment) \<Rightarrow> decision_replay_inspect assessment f)"

definition decision_replay_optional_condition where
  "decision_replay_optional_condition f method X=(case X of None \<Rightarrow> False
    | Some x \<Rightarrow> decision_replay_condition f method x)"

definition decision_replay_quality where
  "decision_replay_quality m w f=decision_replay_cell_inspect
    (decision_replay_cell m (decision_replay_context w)) f"

theorem decision_replay_quality_exact:
  "decision_replay_quality m w f=decision_replay_optional_condition f
    (decision_replay_method m) (native_requirement_problem w)"
  by (simp add: decision_replay_quality_def decision_replay_cell_exact
    decision_replay_cell_inspect_def decision_replay_optional_condition_def
    decision_replay_assessment_exact split: option.splits)

interpretation decision_replay: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11]"
    "[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]" ws decision_replay_method decision_replay_optional_condition
    native_requirement_problem decision_replay_quality for ws
  by (unfold_locales) (rule decision_replay_quality_exact)

definition decision_replay_investigation where
  "decision_replay_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11]
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] ws decision_replay_quality)
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] ws decision_replay_quality)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm decision_replay_investigation_def},
   equation = @{thm decision_replay.observations_derived},
   formation = @{thm decision_replay.maps_formed},
   observation = @{thm decision_replay.observation_at_subject},
   comparison = @{thm decision_replay.comparison_at_subject}}\<close>

definition decision_replay_packet where
  "decision_replay_packet ws selections=(let
    table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11] ws decision_replay_context decision_replay_cell;
    comparison=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] ws table
      decision_replay_cell_inspect
    in (table,comparison,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]
      (fst comparison) (fst (snd comparison))) selections))"

theorem decision_replay_packet_comparison:
  "fst (snd (decision_replay_packet ws selections))=assessed_subject_investigation
    [0,1,2,3,4,5,6,7,8,9,10,11] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18] ws
    (\<lambda>m w. decision_replay_cell m (decision_replay_context w)) decision_replay_cell_inspect"
  by (simp only: decision_replay_packet_def Let_def fst_conv snd_conv context_assessment_investigation_exact)

end
