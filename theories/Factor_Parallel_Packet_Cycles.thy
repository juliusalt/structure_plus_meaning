theory Factor_Parallel_Packet_Cycles
  imports Parallel_Assessment_Execution Factor_Packet_Stages Shared_Investigation_Cycles
begin

declare replay_stage_cycles_def[code del]
declare history_stage_cycles_def[code del]

lemma replay_stage_cycles_parallel_code [code]:
  "replay_stage_cycles compared selections=Parallel.map (investigation_cycle_report
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] [0,1]
    (fst compared) (fst (snd compared))) selections"
  by (simp only: replay_stage_cycles_def Parallel.map_def)

lemma history_stage_cycles_parallel_code [code]:
  "history_stage_cycles compared selections=Parallel.map (investigation_cycle_report constructed_history.methods
    [0,1] (fst compared) (fst (snd compared))) selections"
  by (simp only: history_stage_cycles_def Parallel.map_def)

declare digit_replay_packet_prepared_causes_code[code del]
declare constructed_history_packet_shared_code[code del]

lemma digit_replay_packet_parallel_stages_code [code]:
  "digit_replay_packet ws selections=(let table=replay_stage_table ws;
    compared=replay_stage_compare ws table
    in (table,compared,replay_stage_cycles compared selections))"
  by (rule replay_packet_stages_exact)

lemma constructed_history_packet_parallel_stages_code [code]:
  "constructed_history_packet ws selections=(let table=history_stage_table ws;
    compared=history_stage_compare ws table
    in (table,compared,history_stage_cycles compared selections))"
  by (rule history_packet_stages_exact)

text \<open>Each requested initial selection produces its complete cycle
  independently. Isabelle's parallel map preserves the exact list order and
  every repeated selection. The ordinary packet entry points use these same
  established stages; parallel execution does not supply a semantic verdict.\<close>

end
