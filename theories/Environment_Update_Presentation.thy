theory Environment_Update_Presentation
 imports Finite_Presented_Storage_Notions Finite_Term_Words
begin

definition environment_update_presented_report where
 "environment_update_presented_report ws selections=(let packet=environment_update_packet ws selections in
   (environment_update_indices,ws,packet,assessment_truth_rows environment_update_inspect [0,1] (fst packet),map (\<lambda>n. (n,environment_update_chain_report n)) [0,32,128]))"

definition environment_update_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
 "environment_update_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_investigation_packet_value (finite_reader_context_presentation finite_environment_update_subject_value finite_environment_presentation) (finite_reader_assessment_presentation finite_environment_presentation)) (finite_pair_presentation finite_assessment_truth_value (finite_sequence_presentation (finite_pair_presentation finite_natural_data finite_environment_chain_value)))))) (environment_update_presented_report ws selections)"

definition environment_update_report_selections :: "nat list list" where
 "environment_update_report_selections=[[],[0],[0,1]]"
end
