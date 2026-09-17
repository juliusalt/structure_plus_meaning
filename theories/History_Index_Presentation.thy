theory History_Index_Presentation
 imports Finite_Presented_Generation_Queries Finite_Term_Words
begin

definition finite_history_index_subject_row_value where
 "finite_history_index_subject_row_value=(finite_pair_presentation (finite_option_presentation finite_history_certificate_value) (finite_option_presentation finite_history_index_subject_value))"

definition finite_history_index_prepared_value where
 "finite_history_index_prepared_value=(finite_pair_presentation finite_history_index_subject_value (finite_pair_presentation (finite_option_presentation finite_history_index_view_value) (finite_pair_presentation (finite_option_presentation finite_history_index_state_value) (finite_option_presentation finite_history_index_state_value))))"

definition finite_history_index_context_value where
 "finite_history_index_context_value=(finite_pair_presentation (finite_collection_presentation finite_history_index_subject_row_value) (finite_pair_presentation (finite_collection_presentation (finite_pair_presentation (finite_option_presentation finite_history_certificate_value) (finite_option_presentation finite_history_index_prepared_value))) (finite_collection_presentation finite_history_index_result_row_value)))"

definition finite_history_index_assessment_value where
 "finite_history_index_assessment_value=(finite_pair_presentation (finite_collection_presentation finite_history_index_result_row_value) (finite_collection_presentation finite_history_index_result_row_value))"

definition finite_history_index_source_value where
 "finite_history_index_source_value=(finite_pair_presentation finite_natural_data (finite_pair_presentation (finite_collection_presentation finite_history_subject_value) (finite_pair_presentation (finite_collection_presentation finite_history_subject_value) finite_boolean_data)))"

definition history_index_presented_sources where
 "history_index_presented_sources table=map (\<lambda>(w,C,cells).
   let subjects=fst C; previous=required_history_case w
   in (w,previous,history_index_original_family subjects,history_index_source_equal subjects previous))
   (filter (\<lambda>row. fst row<12) table)"

definition history_index_presented_coverage where
 "history_index_presented_coverage table=map (\<lambda>(w,C,cells).
   (w,required_history_subject_coverage (history_index_original_family (fst C)))) table"

definition history_index_report where
 "history_index_report ws selections=(let packet=history_index_packet ws selections in
   (history_index_indices,ws,packet,assessment_truth_rows history_index_inspect [0,1] (fst packet),
     history_index_presented_coverage (fst packet),history_index_source_scope ws,
     history_index_presented_sources (fst packet)))"

definition history_index_report_value where
 "history_index_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_investigation_packet_value finite_history_index_context_value finite_history_index_assessment_value) (finite_pair_presentation finite_assessment_truth_value (finite_pair_presentation (finite_sequence_presentation (finite_pair_presentation finite_natural_data (finite_pair_presentation finite_natural_data finite_natural_data))) (finite_pair_presentation finite_index_sequence_value (finite_sequence_presentation finite_history_index_source_value))))))) (history_index_report ws selections)"

definition history_index_report_selections :: "nat list list" where "history_index_report_selections=[[],[0],[0,1]]"
export_code history_index_report_value checking SML
end
