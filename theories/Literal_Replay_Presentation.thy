theory Literal_Replay_Presentation
  imports Finite_Presented_Decision_Families Finite_Presented_Replays Finite_Presented_Native_Construction
    Finite_Term_Words Factor_Literal_Replay_Investigation
begin

section \<open>Literal replay specializes the decision investigation packet\<close>

definition finite_literal_replay_report_value where
  "finite_literal_replay_report_value=finite_pair_presentation (finite_collection_presentation finite_native_system_value)
    (finite_pair_presentation (finite_collection_presentation finite_application_reading_value)
      (finite_pair_presentation (finite_collection_presentation finite_assertion_readings_value) finite_artifact_term))"

lemma finite_literal_replay_report_value_injective [intro]: "inj finite_literal_replay_report_value"
  unfolding finite_literal_replay_report_value_def
  by (intro finite_pair_presentation_injective finite_collection_presentation_injective
      finite_native_system_value_injective finite_application_reading_value_injective
      finite_assertion_readings_value_injective finite_artifact_term_injective)

definition finite_literal_replay_packet_value where
  "finite_literal_replay_packet_value=finite_decision_investigation_packet_value finite_literal_seed_value
    finite_history_certificate_value finite_literal_replay_value finite_literal_replay_report_value"

lemma finite_literal_replay_packet_value_injective [intro]: "inj finite_literal_replay_packet_value"
  unfolding finite_literal_replay_packet_value_def
  by (intro finite_decision_investigation_packet_value_injective finite_literal_seed_value_injective
      finite_history_certificate_value_injective finite_literal_replay_value_injective
      finite_literal_replay_report_value_injective)

definition literal_replay_presented_report where
  "literal_replay_presented_report ws selections=(let packet=literal_replay_packet ws selections
    in (literal_replay_indices,ws,packet,
      assessment_truth_rows literal_replay_family_inspect [0,1] (fst (snd packet))))"

definition literal_replay_report_value where
  "literal_replay_report_value ws selections=finite_scoped_report_value finite_literal_replay_packet_value
    (literal_replay_presented_report ws selections)"

theorem literal_replay_report_value_exact:
  "literal_replay_report_value ws selections=literal_replay_report_value vs choices \<longleftrightarrow>
    literal_replay_presented_report ws selections=literal_replay_presented_report vs choices"
  unfolding literal_replay_report_value_def
  by (intro inj_eq finite_scoped_report_value_injective finite_literal_replay_packet_value_injective)

theorem literal_replay_report_word_exact:
  "finite_term_shared_word (literal_replay_report_value ws selections)=
    finite_term_shared_word (literal_replay_report_value vs choices) \<longleftrightarrow>
    literal_replay_presented_report ws selections=literal_replay_presented_report vs choices"
  by (simp only: finite_term_shared_word_injective literal_replay_report_value_exact)

definition literal_replay_report_selections :: "nat list list" where
  "literal_replay_report_selections=[[],[0],[0,1]]"

text \<open>
  The literal replay report of a subject keeps its package systems, application
  readings, assertion readings and requested artifact. The packet specializes the
  decision investigation packet with the literal seed, certificate keys, literal
  replay subjects and those reports. The presented report keeps the complete
  scope, the executed scope, the packet and every actual family inspection.
\<close>

end
