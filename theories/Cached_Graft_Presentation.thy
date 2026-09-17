theory Cached_Graft_Presentation
 imports Finite_Presented_Storage_Notions Finite_Term_Words
begin

definition cached_graft_presented_report where
 "cached_graft_presented_report ws selections=(let packet=cached_graft_packet ws selections in
   (cached_graft_indices,ws,packet,assessment_truth_rows cached_graft_inspect [0,1] (fst packet),cached_graft_source_scope ws,map (\<lambda>w. (w,cached_graft_source_report w,cached_graft_sources_equal w)) (cached_graft_source_scope ws),map (\<lambda>(i,grow,n). (i,grow,n,cached_graft_chain_report grow n)) [(0,True,0),(1,True,32),(2,True,128),(3,False,3)]))"

definition cached_graft_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
 "cached_graft_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_investigation_packet_value (finite_reader_context_presentation finite_cached_graft_subject_value (finite_option_presentation finite_formed_allocation_state_value)) (finite_reader_assessment_presentation (finite_option_presentation finite_formed_allocation_state_value))) (finite_pair_presentation finite_assessment_truth_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_sequence_presentation (finite_pair_presentation finite_natural_data (finite_pair_presentation (finite_pair_presentation finite_graft_subject_value finite_graft_subject_value) finite_boolean_data))) (finite_sequence_presentation (finite_pair_presentation finite_natural_data (finite_pair_presentation finite_boolean_data (finite_pair_presentation finite_natural_data (finite_option_presentation finite_formed_allocation_state_value))))))))))) (cached_graft_presented_report ws selections)"

definition cached_graft_report_selections :: "nat list list" where
 "cached_graft_report_selections=[[],[0],[0,1]]"
end
