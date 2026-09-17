theory Artifact_Lookup_Presentation
 imports Finite_Presented_Storage_Notions Finite_Term_Words
begin

definition artifact_lookup_presented_report where
 "artifact_lookup_presented_report ws selections=(let packet=artifact_lookup_packet ws selections in
   (artifact_lookup_indices,ws,packet,assessment_truth_rows artifact_lookup_inspect [0,1] (fst packet),map (\<lambda>(w,C,cells). (w,artifact_lookup_path_report (fst C))) (fst packet)))"

definition artifact_lookup_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
 "artifact_lookup_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_investigation_packet_value (finite_reader_context_presentation finite_artifact_lookup_subject_value finite_artifact_term) (finite_reader_assessment_presentation finite_artifact_term)) (finite_pair_presentation finite_assessment_truth_value (finite_sequence_presentation (finite_pair_presentation finite_natural_data finite_artifact_lookup_path_value)))))) (artifact_lookup_presented_report ws selections)"

definition artifact_lookup_report_selections :: "nat list list" where
 "artifact_lookup_report_selections=[[],[0],[0,1]]"
end
