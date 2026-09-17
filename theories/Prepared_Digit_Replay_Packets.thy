theory Prepared_Digit_Replay_Packets
 imports Prepared_Digit_Cause_Assessments Factor_Digit_Replay_Investigation
begin

declare digit_replay_packet_def[code del]
lemma digit_replay_prepared_causes_code [code]:
"digit_replay_packet ws selections=(let table=prepared_context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] ws
      (\<lambda>w. digit_replay_family_context (digit_replay_case w)) (digit_prepare_cause_assessments [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]);
    compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] [0,1] ws table digit_replay_family_inspect
    in (table,compared,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] [0,1]
      (fst compared) (fst (snd compared))) selections))"
proof -
  have table: "prepared_context_assessment_table ms workloads make_context
      (digit_prepare_cause_assessments ms)=context_assessment_table ms workloads make_context
        digit_replay_family_assessment" for ms workloads make_context
    by (rule prepared_context_assessment_table_exact; rule digit_prepare_cause_assessments_exact)
  show ?thesis by (simp only: table digit_replay_packet_def)
qed


end
