theory Concurrent_Replay_Presentation
 imports Digit_Replay_Presentation Factor_Parallel_Packet_Cycles
begin

declare digit_replay_report_def[code del]
lemma digit_replay_report_concurrent_code [code]:
 "digit_replay_report ws selections=(let table=replay_stage_table ws;
   compared=replay_stage_compare ws table; packet=(table,compared,replay_stage_cycles compared selections) in
   (digit_replay_indices,ws,
     (literal_replay_seed,required_history_seed_replays,digit_replay_initial_material_source),
     (digit_replay_literal_sources,digit_replay_history_sources),
     packet,digit_replay_presented_qualities (fst packet),digit_replay_source_scope ws,
     digit_replay_presented_sources (fst packet)))"
 by (simp only: digit_replay_report_def replay_packet_stages_exact Let_def)

end
