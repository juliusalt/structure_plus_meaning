theory Factor_Packet_Observation_Readings
  imports Factor_Digit_Replay_Investigation Factor_Constructed_History_Investigation
    Finite_Assessed_Observation_Readings
begin

theorem digit_replay_packet_cell_observation:
  assumes packet: "digit_replay_packet ws selections=(table,compared,cycles)"
    and subject: "(w,C,cells)\<in>set table" and cell: "(c,A)\<in>set cells" and facet: "f\<in>set [0,1]"
  shows "read_assessed_observation (fst compared) c w f=digit_replay_family_inspect A f"
proof -
  have table: "table=context_assessment_table [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] ws
      (\<lambda>w. digit_replay_family_context (digit_replay_case w)) digit_replay_family_assessment"
    and compared: "compared=context_assessment_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]
      [0,1] ws table digit_replay_family_inspect"
    using packet by (auto simp: digit_replay_packet_def Let_def)
  show ?thesis unfolding compared table
    by (rule context_assessment_observation_at_cell[OF subject[unfolded table] cell facet])
qed

theorem constructed_history_packet_cell_observation:
  assumes packet: "constructed_history_packet ws selections=(table,compared,cycles)"
    and subject: "(w,C,cells)\<in>set table" and cell: "(c,A)\<in>set cells" and facet: "f\<in>set [0,1]"
  shows "read_assessed_observation (fst compared) c w f=digit_history_question_inspect A f"
proof -
  have table: "table=context_assessment_table constructed_history.methods ws
      (\<lambda>w. constructed_history.make_context (digit_history_case w)) constructed_history.assessment"
    and compared: "compared=context_assessment_investigation constructed_history.methods [0,1] ws table
      digit_history_question_inspect"
    using packet by (auto simp: constructed_history_packet_def constructed_history.packet_def Let_def)
  show ?thesis unfolding compared table
    by (rule context_assessment_observation_at_cell[OF subject[unfolded table] cell facet])
qed

end
