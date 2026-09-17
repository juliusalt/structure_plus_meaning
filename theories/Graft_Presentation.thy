theory Graft_Presentation
 imports Finite_Presented_Storage_Notions Finite_Term_Words
begin

definition graft_presented_report where
 "graft_presented_report ws selections=(let packet=graft_packet ws selections in
   (graft_indices,ws,packet,assessment_truth_rows graft_inspect [0..<5] (fst packet)))"

definition graft_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
 "graft_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_dual_comparison_packet_value finite_graft_subject_value finite_graft_assessment_value) finite_assessment_truth_value))) (graft_presented_report ws selections)"

definition graft_report_selections :: "nat list list" where
 "graft_report_selections=[[],[0],[0,1,2,3],[0,1,2,3,4]]"
export_code graft_report_value checking SML
end
