theory Digit_Allocation_Presentation
 imports Finite_Presented_Storage_Notions Finite_Term_Words
begin

definition digit_allocation_presented_report where
 "digit_allocation_presented_report ws selections=(let packet=digit_allocation_packet ws selections in
   (digit_allocation_indices,ws,packet,assessment_truth_rows digit_allocation_inspect [0,1] (fst packet),map (\<lambda>w. (w,allocation_case_views w,allocation_case_views_equal w,allocation_original_context w,allocation_case_result_pairs w)) ws,map (\<lambda>n. (n,allocated_environment_chain_paths n,digit_allocation_chain_paths n)) [0,32,128]))"

definition digit_allocation_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
 "digit_allocation_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_investigation_packet_value (finite_reader_context_presentation finite_digit_allocation_subject_value (finite_option_presentation finite_allocation_state_value)) (finite_reader_assessment_presentation (finite_option_presentation finite_allocation_state_value))) (finite_pair_presentation finite_assessment_truth_value (finite_pair_presentation (finite_sequence_presentation (finite_pair_presentation finite_natural_data (finite_pair_presentation (finite_pair_presentation finite_viewed_allocation_subject_value finite_viewed_allocation_subject_value) (finite_pair_presentation finite_boolean_data (finite_pair_presentation (finite_reader_context_presentation finite_viewed_allocation_subject_value (finite_option_presentation finite_allocation_state_value)) (finite_sequence_presentation (finite_pair_presentation finite_natural_data (finite_pair_presentation (finite_collection_presentation (finite_option_presentation finite_allocation_state_value)) (finite_pair_presentation (finite_collection_presentation (finite_option_presentation finite_allocation_state_value)) finite_boolean_data))))))))) (finite_sequence_presentation (finite_pair_presentation finite_natural_data (finite_pair_presentation finite_allocation_chain_paths_value finite_allocation_chain_paths_value)))))))) (digit_allocation_presented_report ws selections)"

definition digit_allocation_report_selections :: "nat list list" where
 "digit_allocation_report_selections=[[],[0],[0,1]]"
export_code digit_allocation_report_value checking SML
end
