theory Decision_Replay_Presentation
  imports Finite_Presented_Decisions Finite_Presented_Assessments Finite_Term_Words
    Factor_Decision_Replay_Investigation
begin

definition decision_replay_report where
  "decision_replay_report ws selections=(let packet=decision_replay_packet ws selections in
    (requirement_decision_indices,ws,packet,
      assessment_truth_rows decision_replay_cell_inspect [0..<19] (fst packet)))"

definition decision_replay_report_value :: "nat list \<Rightarrow> nat list list \<Rightarrow> finite_factor_term" where
  "decision_replay_report_value ws selections=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation finite_index_sequence_value
      (finite_pair_presentation
        (finite_investigation_packet_value finite_decision_replay_context_value finite_decision_replay_cell_value)
        finite_assessment_truth_value)) (decision_replay_report ws selections)"

theorem decision_replay_report_value_exact:
  "decision_replay_report_value ws selections=decision_replay_report_value vs choices \<longleftrightarrow>
    decision_replay_report ws selections=decision_replay_report vs choices"
  unfolding decision_replay_report_value_def
  by (intro inj_eq finite_pair_presentation_injective finite_index_values_injective
      finite_investigation_packet_value_injective finite_decision_replay_context_value_injective
      finite_decision_replay_cell_value_injective finite_assessment_truth_value_injective)

theorem decision_replay_report_word_exact:
  "finite_term_shared_word (decision_replay_report_value ws selections)=
    finite_term_shared_word (decision_replay_report_value vs choices) \<longleftrightarrow>
    decision_replay_report ws selections=decision_replay_report vs choices"
  by (simp only: finite_term_shared_word_injective decision_replay_report_value_exact)

definition decision_replay_report_selections :: "nat list list" where
  "decision_replay_report_selections=[[],[0,1,2,3,4,5,6,7,17],[0..<19]]"

text \<open>
  Original requirements, environments, evaluation applications and rules,
  certificate inspections, every replay graph and retained environment, all
  candidate and per-replay conditions and every revision remain actual native
  outputs. The presentations compose through their complete constituent notions;
  the generic word transports them without reading generated representations.
\<close>

end
