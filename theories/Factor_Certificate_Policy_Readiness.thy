theory Factor_Certificate_Policy_Readiness
  imports Factor_Certificate_Policy_Continuation Factor_Quoted_Policy_Attempts
begin

section \<open>A replayed certificate is ready to be recorded\<close>

text \<open>
  Recording a replayed judgment checks that the replay environment proves the call without
  assertions and that the call's argument is the whole payload. In the certificate-to-policy
  composition that environment is the one the certificate replay has just constructed, and the
  replay's contract already states both facts of it: the empty assumption family is among its
  replay readings, and the certified call is among its application readings. The composition
  therefore records the replay by the quotation attempt alone, which is exactly the original
  operation on every input.
\<close>

lemma certificate_replay_literal_ready:
  assumes replay: "finite_native_certificate_replay K ku [] p entry (Finite_Target (Finite_Whole R))=
      Some (A,M,root,G,au,I,W,B)"
  shows "finite_literal_replay_ready B ku [] au [] root R"
proof -
  have "\<exists>P. finite_native_source K ku []=Some P \<and>
      finite_checks_schema_proof P p entry (Finite_Target (Finite_Whole R))"
    using replay finite_native_certificate_replay_domain by blast
  then obtain P where source: "finite_native_source K ku []=Some P" by blast
  note correct=finite_native_certificate_replay_correct[OF replay source]
  have proves: "finite_native_replay_proves B ku [] au [] root"
    using correct(15) by (simp only: finite_native_replay_proves_def)
  have literal: "finite_literal_application_ready B au [] R"
    using correct(14) by (auto simp: finite_literal_application_ready_def)
  show ?thesis using proves literal by (simp only: finite_literal_replay_ready_def)
qed

lemma certificate_policy_record_ready_code [code]:
  "certificate_policy_record K ku entry p R H l rows=
    (case finite_native_certificate_replay K ku [] p entry (Finite_Target (Finite_Whole R)) of
      None \<Rightarrow> None
    | Some replay \<Rightarrow> (case replay of (A,M,root,G,au,I,W,B) \<Rightarrow>
        map_option (\<lambda>following. (replay,following))
          (quoted_policy_attempt finite_construct_generation_record K ku entry H l rows B ku [] au [] R)))"
proof (cases "finite_native_certificate_replay K ku [] p entry (Finite_Target (Finite_Whole R))")
  case None
  then show ?thesis by (simp add: certificate_policy_record_def)
next
  case (Some replay)
  obtain A M root G au I W B where shape: "replay=(A,M,root,G,au,I,W,B)" by (cases replay) auto
  have ready: "finite_literal_replay_ready B ku [] au [] root R"
    by (rule certificate_replay_literal_ready[OF Some[unfolded shape]])
  show ?thesis
    by (simp add: certificate_policy_record_def Some shape policy_record_replay_from_source_factored ready)
qed

end
