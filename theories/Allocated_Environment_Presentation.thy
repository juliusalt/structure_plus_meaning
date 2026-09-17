theory Allocated_Environment_Presentation
 imports Finite_Presented_Storage_Notions Finite_Term_Words
begin

definition allocated_environment_presented_report where
 "allocated_environment_presented_report ws selections=(let packet=allocated_update_packet ws selections in
   (allocated_update_indices,ws,packet,assessment_truth_rows allocated_update_inspect [0,1] (fst packet),map (\<lambda>n. (n,allocated_environment_chain_paths n)) [0,32,128]))"

definition allocated_environment_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
 "allocated_environment_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_investigation_packet_value (finite_reader_context_presentation finite_allocated_subject_value (finite_option_presentation finite_allocation_state_value)) (finite_reader_assessment_presentation (finite_option_presentation finite_allocation_state_value))) (finite_pair_presentation finite_assessment_truth_value (finite_sequence_presentation (finite_pair_presentation finite_natural_data finite_allocation_chain_paths_value)))))) (allocated_environment_presented_report ws selections)"

definition allocated_environment_report_selections :: "nat list list" where
 "allocated_environment_report_selections=[[],[0],[0,1]]"
end
