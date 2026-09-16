theory Quoted_History_Presentation
  imports Known_History_Presentation Factor_Quoted_History_Investigation
begin

section \<open>Additional producers keep every produced result family\<close>

definition finite_candidate_context_value where
  "finite_candidate_context_value=finite_pair_presentation finite_digit_context_value
    (finite_sequence_presentation (finite_collection_presentation finite_digit_result_row_value))"

definition quoted_history_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
  "quoted_history_report_value ws selections=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation (finite_investigation_packet_value finite_candidate_context_value finite_digit_assessment_value)
      (finite_sequence_presentation finite_digit_source_value)) (digit_history_report quoted_history_packet ws selections)"

definition quoted_history_report_selections :: "nat list list" where
  "quoted_history_report_selections=[[],[0],[0,1]]"

export_code quoted_history_report_value checking SML

text \<open>
  A context of the additional-producer framework keeps the digit history
  context and the complete result family of every additional producer in order.
\<close>

end
