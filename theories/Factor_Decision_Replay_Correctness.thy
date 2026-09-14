theory Factor_Decision_Replay_Correctness
  imports Factor_Decision_Replay_Assessment Factor_Native_Replay_Correctness
begin

lemma decision_certificate_replay_conditions:
  assumes facet: "f<10"
  shows "native_replay_condition f (\<lambda>X. finite_certificate_replay F v [] c)
    (decision_certificate_subject (d,F,v,Q,D,A,T,Ys) c)"
proof -
  obtain e t p where shape: "c=((e,t),p)" by (cases c) auto
  show ?thesis using native_replay_constructor_all_conditions[OF facet,
      of "decision_certificate_subject (d,F,v,Q,D,A,T,Ys) c"]
    by (simp only: native_replay_condition_def Let_def native_replay_method_original
      native_replay_base_def finite_certificate_replay_def decision_certificate_subject_def
      shape case_prod_conv)
qed

theorem decision_replay_constructed_family_conditions:
  assumes facet: "f<11"
  shows "decision_replay_family_condition f Z (snd (finite_decision_replay_body Z))"
proof -
  obtain d F v Q D A T Ys where shape: "Z=(d,F,v,Q,D,A,T,Ys)" by (cases Z) auto
  have each: "native_replay_condition (f-1) (\<lambda>X. finite_certificate_replay F v [] c)
    (decision_certificate_subject Z c)" if "f\<noteq>0" for c
    by (simp only: shape; rule decision_certificate_replay_conditions; use facet that in arith)
  show ?thesis using facet each
    by (auto simp: decision_replay_family_condition_def shape finite_decision_replay_body_def
      finite_certificate_replays_exact graph_map_dom graph_map_single_valued graph_map_member)
qed

text \<open>
  The composition instantiates the existing universal replay-constructor
  contract at every complete certificate. Its family domain and functionality
  come from the original finite function graph. The independent original
  decision conditions remain required: a correctly refused invalid certificate
  is not evidence for admission of a term or adequacy of its requirements.
\<close>

end
