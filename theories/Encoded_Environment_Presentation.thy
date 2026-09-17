theory Encoded_Environment_Presentation
 imports Finite_Presented_Storage_Notions Finite_Term_Words
begin

definition encoded_environment_presented_report where
 "encoded_environment_presented_report ws selections=(let packet=codec_environment_packet ws selections in
   (codec_environment_indices,ws,packet,assessment_truth_rows codec_environment_full_inspect [0,1,2] (fst packet),
     map (\<lambda>n. (n,codec_environment_path_comparison n)) [1,2,33,129]))"

definition encoded_environment_report_value where
 "encoded_environment_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_pair_presentation (finite_assessment_table_value (finite_pair_presentation (finite_reader_context_presentation finite_environment_update_subject_value finite_environment_presentation) finite_environment_presentation) (finite_pair_presentation (finite_reader_assessment_presentation finite_environment_presentation) (finite_pair_presentation finite_environment_presentation finite_environment_presentation))) (finite_pair_presentation finite_investigation_comparison_value (finite_pair_presentation (finite_sequence_presentation finite_investigation_cycle_value) (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_investigation_comparison_value (finite_sequence_presentation finite_investigation_cycle_value)))))) (finite_pair_presentation finite_assessment_truth_value (finite_sequence_presentation (finite_pair_presentation finite_natural_data (finite_pair_presentation finite_storage_path_result_value finite_storage_path_result_value))))))) (encoded_environment_presented_report ws selections)"

definition encoded_environment_report_selections :: "nat list list" where
 "encoded_environment_report_selections=[[],[0],[0,1],[0,1,2]]"
export_code encoded_environment_report_value checking SML
end
