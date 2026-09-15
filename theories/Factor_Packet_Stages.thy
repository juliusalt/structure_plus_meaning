theory Factor_Packet_Stages
  imports Factor_Prepared_Replay_Assessments Factor_Shared_History_Construction
begin

definition replay_stage_table where
  "replay_stage_table=prepared_replay_table"

definition replay_stage_compare where
  "replay_stage_compare ws table=context_assessment_investigation
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] [0,1] ws table digit_replay_family_inspect"

definition replay_stage_cycles where
  "replay_stage_cycles compared selections=map (investigation_cycle_report
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] [0,1]
    (fst compared) (fst (snd compared))) selections"

theorem replay_packet_stages_exact:
  "digit_replay_packet ws selections=(let table=replay_stage_table ws;
    compared=replay_stage_compare ws table
    in (table,compared,replay_stage_cycles compared selections))"
  by (simp only: replay_stage_table_def replay_stage_compare_def replay_stage_cycles_def
    digit_replay_packet_prepared_causes_code)

definition history_stage_table where
  "history_stage_table ws=context_assessment_table constructed_history.methods ws
    (\<lambda>w. constructed_history_shared_context (digit_history_case w)) constructed_history.assessment"

definition history_stage_compare where
  "history_stage_compare ws table=context_assessment_investigation constructed_history.methods
    [0,1] ws table digit_history_question_inspect"

definition history_stage_cycles where
  "history_stage_cycles compared selections=map (investigation_cycle_report constructed_history.methods
    [0,1] (fst compared) (fst (snd compared))) selections"

theorem history_packet_stages_exact:
  "constructed_history_packet ws selections=(let table=history_stage_table ws;
    compared=history_stage_compare ws table
    in (table,compared,history_stage_cycles compared selections))"
  by (simp only: history_stage_table_def history_stage_compare_def history_stage_cycles_def
    constructed_history_packet_shared_code)

text \<open>The exported stages reconstruct the complete original packet for
  arbitrary requested indices and selections. This decomposition makes physical
  timing of construction, comparison and revision possible without dropping any
  context, candidate, observation or reason. Timing supplies no semantic verdict.\<close>

end
