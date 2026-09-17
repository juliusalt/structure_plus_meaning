theory Digit_Generation_Presentation
 imports Finite_Presented_Generation_Queries Finite_Term_Words
begin

definition finite_digit_generation_context_value where
 "finite_digit_generation_context_value=(finite_pair_presentation finite_digit_generation_subject_value (finite_pair_presentation (finite_collection_presentation finite_bounded_generation_value_value) (finite_sequence_presentation (finite_pair_presentation finite_natural_data (finite_collection_presentation finite_bounded_generation_value_value)))))"

definition finite_digit_generation_assessment_value where
 "finite_digit_generation_assessment_value=(finite_pair_presentation (finite_collection_presentation finite_bounded_generation_value_value) (finite_pair_presentation (finite_collection_presentation finite_bounded_generation_value_value) (finite_collection_presentation finite_digit_generation_original_value)))"

definition finite_digit_generation_source_value where
 "finite_digit_generation_source_value=(finite_pair_presentation finite_natural_data (finite_pair_presentation finite_generation_problem_value (finite_pair_presentation finite_bounded_generation_subject_value (finite_pair_presentation finite_digit_generation_subject_value (finite_pair_presentation finite_natural_data finite_boolean_data)))))"

definition digit_generation_presented_sources where
 "digit_generation_presented_sources table=map (\<lambda>(w,C,cells).
   let subject=fst C; original=bounded_generation_case w
   in (w,digit_generation_source_problem w,original,subject,digit_generation_chain_length w,
     digit_generation_source_equal subject original)) table"

definition digit_generation_report where
 "digit_generation_report ws selections=(let packet=digit_generation_packet ws selections in
   (digit_generation_indices,ws,packet,assessment_truth_rows digit_generation_inspect [0,1] (fst packet),
     digit_generation_source_scope ws,digit_generation_presented_sources (fst packet)))"

definition digit_generation_report_value where
 "digit_generation_report_value ws selections=(finite_pair_presentation finite_index_sequence_value (finite_pair_presentation finite_index_sequence_value (finite_pair_presentation (finite_investigation_packet_value finite_digit_generation_context_value finite_digit_generation_assessment_value) (finite_pair_presentation finite_assessment_truth_value (finite_pair_presentation finite_index_sequence_value (finite_sequence_presentation finite_digit_generation_source_value)))))) (digit_generation_report ws selections)"

definition digit_generation_report_selections :: "nat list list" where "digit_generation_report_selections=[[],[0],[0,1]]"
export_code digit_generation_report_value checking SML
end
