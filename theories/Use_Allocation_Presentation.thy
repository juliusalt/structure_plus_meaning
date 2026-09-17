theory Use_Allocation_Presentation
 imports Finite_Presented_Storage_Notions Finite_Term_Words
begin

definition use_allocation_presented_report where
 "use_allocation_presented_report ws selections=(let packet=use_allocation_packet ws selections in
   (use_allocation_indices,ws,packet,assessment_truth_rows use_allocation_inspect [0..<5] (fst packet)))"

definition use_allocation_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
 "use_allocation_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_dual_comparison_packet_value finite_use_allocation_subject_value finite_use_allocation_assessment_value) finite_assessment_truth_value))) (use_allocation_presented_report ws selections)"

definition use_allocation_report_selections :: "nat list list" where
 "use_allocation_report_selections=[[],[0],[0,1,2,3],[0,1,2,3,4]]"
export_code use_allocation_report_value checking SML
end
