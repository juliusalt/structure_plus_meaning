theory Known_History_Presentation
  imports Digit_History_Presentation Factor_Known_History_Investigation
begin

section \<open>A known history context adds its admitted predecessor results\<close>

definition finite_known_context_value where
  "finite_known_context_value=finite_pair_presentation finite_digit_context_value
    (finite_collection_presentation finite_digit_result_row_value)"

definition known_history_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
  "known_history_report_value ws selections=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation (finite_investigation_packet_value finite_known_context_value finite_digit_assessment_value)
      (finite_sequence_presentation finite_digit_source_value)) (digit_history_report known_history_packet ws selections)"

definition known_history_report_selections :: "nat list list" where
  "known_history_report_selections=[[],[0],[0,1,2]]"

text \<open>
  The known history report reuses the digit history presentations and adds the
  admitted predecessor result rows of every context.
\<close>

end
