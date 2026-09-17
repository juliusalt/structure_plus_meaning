theory Concurrent_History_Presentation
 imports Constructed_History_Presentation Factor_Parallel_Packet_Cycles Finite_Presented_Assessments
begin

definition concurrent_history_presented_packet where
 "concurrent_history_presented_packet ws selections=(let table=history_stage_table ws;
   compared=history_stage_compare ws table in (table,compared,history_stage_cycles compared selections))"

lemma concurrent_history_presented_packet_exact:
 "concurrent_history_presented_packet ws selections=constructed_history_packet ws selections"
 by (simp only: concurrent_history_presented_packet_def history_packet_stages_exact)

definition concurrent_history_presented_report where
 "concurrent_history_presented_report ws selections=(let packet=concurrent_history_presented_packet ws selections in
   (digit_history_indices,ws,packet,assessment_truth_rows digit_history_question_inspect [0,1] (fst packet),
     digit_history_source_scope ws,digit_history_source_rows ws))"

definition concurrent_history_report_value where
 "concurrent_history_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_investigation_packet_value finite_candidate_context_value finite_digit_assessment_value) (finite_pair_presentation finite_assessment_truth_value (finite_pair_presentation finite_index_sequence_value (finite_sequence_presentation finite_digit_source_value)))))) (concurrent_history_presented_report ws selections)"

definition concurrent_history_report_selections :: "nat list list" where
 "concurrent_history_report_selections=[[],[0],[0,1]]"
export_code concurrent_history_report_value checking SML
end
