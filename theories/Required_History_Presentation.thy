theory Required_History_Presentation
  imports Finite_Presented_Investigations Finite_Presented_Histories Finite_Term_Words
    Factor_Required_History_Investigation
begin

section \<open>The whole required-history report has one injective presentation\<close>

definition required_history_context_value where
  "required_history_context_value=finite_pair_presentation (finite_collection_presentation finite_history_subject_value)
    (finite_collection_presentation finite_history_result_value)"

definition required_history_assessment_value where
  "required_history_assessment_value=finite_pair_presentation (finite_collection_presentation finite_history_result_value)
    (finite_collection_presentation finite_history_result_value)"

lemma required_history_family_values_injective [intro]:
  "inj required_history_context_value" "inj required_history_assessment_value"
  unfolding required_history_context_value_def required_history_assessment_value_def
  by (intro finite_pair_presentation_injective finite_collection_presentation_injective finite_history_rows_injective)+

definition required_history_report_selections :: "nat list list" where
  "required_history_report_selections=[[],[0],[0,1]]"

definition required_history_coverage_rows where
  "required_history_coverage_rows table=map (\<lambda>(w,C,cells). (w,required_history_subject_coverage (fst C))) table"

definition required_history_report where
  "required_history_report ws selections=(let packet=required_history_packet ws selections
    in (ws,packet,required_history_coverage_rows (fst packet)))"

definition required_history_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
  "required_history_report_value ws selections=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation (finite_investigation_packet_value required_history_context_value required_history_assessment_value)
      (finite_sequence_presentation finite_index_triple_value)) (required_history_report ws selections)"

theorem required_history_report_value_exact:
  "required_history_report_value ws selections=required_history_report_value vs choices \<longleftrightarrow>
    required_history_report ws selections=required_history_report vs choices"
  unfolding required_history_report_value_def
  by (intro inj_eq finite_pair_presentation_injective finite_index_values_injective
      finite_investigation_packet_value_injective required_history_family_values_injective
      finite_sequence_presentation_injective)

theorem required_history_report_word_exact:
  "finite_term_shared_word (required_history_report_value ws selections)=
      finite_term_shared_word (required_history_report_value vs choices) \<longleftrightarrow>
    required_history_report ws selections=required_history_report vs choices"
  by (simp only: finite_term_shared_word_injective required_history_report_value_exact)

export_code required_history_report_value checking SML

text \<open>
  The report retains the requested scope, the complete packet of context tables,
  comparison and investigation cycles, and the certificate position coverage of
  every context. Its presentation and the digit word of that presentation are
  injective, so equal words identify equal reports. The word is a transport of
  the presented subject: its chosen collection order carries no meaning of its
  own, and the report subjects keep their original contracts.
\<close>

end
