theory Constructed_History_Presentation
  imports Quoted_History_Presentation Factor_Constructed_History_Investigation
begin

section \<open>A constructed history report keeps every producer family\<close>

definition constructed_history_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
  "constructed_history_report_value ws selections=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation (finite_investigation_packet_value finite_candidate_context_value finite_digit_assessment_value)
      (finite_sequence_presentation finite_digit_source_value)) (digit_history_report constructed_history_packet ws selections)"

definition constructed_history_report_selections :: "nat list list" where
  "constructed_history_report_selections=[[],[0],[0,1]]"

export_code constructed_history_report_value checking SML

end
