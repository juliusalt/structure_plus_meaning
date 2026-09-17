theory Graft_Admission_Presentation
 imports Finite_Presented_Storage_Notions Finite_Term_Words
begin

definition graft_admission_presented_report where
 "graft_admission_presented_report ws selections=(let packet=graft_admission_packet ws selections in
   (graft_admission_indices,ws,packet,assessment_truth_rows graft_admission_inspect [0,1] (fst packet),map (\<lambda>w. (w,graft_admission_requirements (graft_admission_case w))) ws))"

definition graft_admission_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
 "graft_admission_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_investigation_packet_value (finite_reader_context_presentation finite_graft_subject_value (finite_option_presentation finite_formed_environment_value)) (finite_reader_assessment_presentation (finite_option_presentation finite_formed_environment_value))) (finite_pair_presentation finite_assessment_truth_value (finite_sequence_presentation (finite_pair_presentation finite_natural_data finite_graft_requirements_value)))))) (graft_admission_presented_report ws selections)"

definition graft_admission_report_selections :: "nat list list" where
 "graft_admission_report_selections=[[],[0],[0,1]]"
export_code graft_admission_report_value checking SML
end
