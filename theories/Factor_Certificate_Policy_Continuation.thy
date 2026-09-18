theory Factor_Certificate_Policy_Continuation
  imports Factor_Finite_Native_Certificate_Replay Factor_Known_Replay_Policy
begin

section \<open>One complete certificate-to-policy composition\<close>

definition certificate_policy_record where
  "certificate_policy_record K ku entry p R H l rows =
    (case finite_native_certificate_replay K ku [] p entry (Finite_Target (Finite_Whole R)) of
      None \<Rightarrow> None
    | Some replay \<Rightarrow> (case replay of (A,M,root,G,au,I,W,B) \<Rightarrow>
        map_option (\<lambda>following. (replay,following))
          (policy_record_replay_from_source finite_construct_generation_record
            K ku entry H l rows B ku [] au [] root R)))"

lemma certificate_policy_record_fields:
  "certificate_policy_record K ku entry p R H l rows =
      Some ((A,M,root,G,au,I,W,B),(F,fu,g)) \<longleftrightarrow>
    finite_native_certificate_replay K ku [] p entry (Finite_Target (Finite_Whole R)) =
      Some (A,M,root,G,au,I,W,B) \<and>
    policy_record_replay_with id finite_construct_generation_record
      K ku entry H l rows B ku [] au [] root R = Some (F,fu,g)"
  by (auto simp: certificate_policy_record_def
    original_generation_backend.policy_record_replay_from_source_exact split: option.splits prod.splits)

theorem certificate_policy_record_original_cause:
  assumes result: "certificate_policy_record K ku entry p R H l rows =
    Some ((A,M,root,G,au,I,W,B),(F,fu,g))"
  shows "certified_policy_cause_at (decode_finite_environment K) ku [] entry
    (decode_finite_environment F) fu [] (decode_finite_generation g)
    (decode_finite_environment B) root (decode_finite_object R)"
  using result
  by (simp only: certificate_policy_record_fields policy_record_replay_with_result
    id_apply finite_certified_policy_cause_exact; blast)

theorem certificate_policy_record_source:
  assumes result: "certificate_policy_record K ku entry p R H l rows =
    Some ((A,M,root,G,au,I,W,B),(F,fu,g))"
  obtains P where "finite_native_source K ku []=Some P"
    "finite_checks_schema_proof P p entry (Finite_Target (Finite_Whole R))"
    "finite_environment_formed A"
    "environment_included (decode_finite_environment K) (decode_finite_environment A)"
    "finite_environment_agrees_on K A (finite_environment_uses K)"
    "finite_native_source A ku []=Some P"
    "P |\<in>| finite_native_package_readings B ku []"
    "G |\<in>| finite_native_graph_readings B root"
    "((entry,Finite_Target (Finite_Whole R)),I,W) |\<in>| finite_application_readings B au []"
    "{||} |\<in>| finite_native_replay_readings B ku [] au [] root"
proof -
  have replay: "finite_native_certificate_replay K ku [] p entry (Finite_Target (Finite_Whole R)) =
      Some (A,M,root,G,au,I,W,B)"
    using result by (simp only: certificate_policy_record_fields; blast)
  obtain P where source: "finite_native_source K ku []=Some P"
    and checked: "finite_checks_schema_proof P p entry (Finite_Target (Finite_Whole R))"
    using replay finite_native_certificate_replay_domain by blast
  show thesis by (rule that[OF source checked])
    (rule finite_native_certificate_replay_correct[OF replay source])+
qed

theorem certificate_policy_record_history:
  assumes previous: "finite_required_history_valid q"
    and policy: "required_history_policy q=K" "required_history_policy_use q=ku"
      "required_history_entry q=entry" "required_history_material q=H"
    and result: "certificate_policy_record K ku entry p R H l rows =
      Some ((A,M,root,G,au,I,W,B),(F,fu,g))"
  shows "finite_required_history_valid (finite_required_history_append q F fu g)"
proof -
  have accepted: "policy_record_replay_with id finite_construct_generation_record
    (required_history_policy q) (required_history_policy_use q) (required_history_entry q)
    H l rows B ku [] au [] root R=Some (F,fu,g)"
    using result by (simp only: certificate_policy_record_fields policy; blast)
  show ?thesis
    using policy_record_replay_append_valid[OF original_generation_backend.generation_record_backend_axioms
      previous _ accepted] policy(4)
    by simp
qed

definition certificate_policy_attempt where
  "certificate_policy_attempt K ku entry witness R H l rows =
    (case witness of None \<Rightarrow> None | Some p \<Rightarrow>
      certificate_policy_record K ku entry p R H l rows)"

lemma certificate_policy_missing [simp]:
  "certificate_policy_attempt K ku entry None R H l rows=None"
  by (simp add: certificate_policy_attempt_def)

text \<open>The original source, submitted complete certificate, literal payload,
  replay environment and policy-aligned generation all remain in this composition.
  Success is checked by the existing original policy operation. No source value,
  certificate, policy alignment, previous history validity or owner authorization
  is manufactured by the wrapper; a missing witness refuses the attempt.\<close>

end
