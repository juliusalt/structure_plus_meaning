theory Generation_Record_Presentation
 imports Finite_Presented_Storage_Notions Finite_Term_Words
begin

definition generation_record_presented_report where
 "generation_record_presented_report ws selections=(let packet=generation_record_packet ws selections in
   (generation_record_indices,ws,packet,assessment_truth_rows generation_record_cell_inspect [0..<9] (fst packet)))"

definition generation_record_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
 "generation_record_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_investigation_packet_value finite_generation_record_context_value finite_generation_record_cell_value) finite_assessment_truth_value))) (generation_record_presented_report ws selections)"

definition generation_record_report_selections :: "nat list list" where
 "generation_record_report_selections=[[],[0..<7],[0..<9]]"
end
