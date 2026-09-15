theory Factor_Replay_Generation_Certification
  imports Factor_Finite_Generation_Replay
begin

theorem finite_literal_replay_generation_certified:
  assumes ready: "finite_literal_replay_ready E pu pr au ar root R"
    and quoted: "finite_native_judgment_quote E pu pr au ar=Some (J,C)"
    and generation: "generation_at A u [] G"
    and payload: "generation_payload G=Whole_Artifact (decode_finite_object R)"
    and cause: "generation_cause G=Whole_Artifact (decode_finite_object C)"
  shows "certified_base_cause_at A u [] G (decode_finite_environment E) root (decode_finite_object R)"
proof -
  have replay: "native_replay_at (decode_finite_environment E) pu pr au ar root {}"
    using ready by (simp only: finite_literal_replay_ready_at; blast)
  obtain d I K where app: "native_application_at (decode_finite_environment E) au ar d
    (Target_Term (Whole_Artifact (decode_finite_object R))) I K"
    using ready by (simp only: finite_literal_replay_ready_at; blast)
  obtain P where package: "native_package_at (decode_finite_environment E) pu pr P"
    using replay by (auto simp: native_replay_at_def)
  have scoped: "decode_finite_environment J=native_judgment_environment (decode_finite_environment E) pu pr au ar"
    and minimal: "decode_finite_environment J=native_judgment_environment (decode_finite_environment J) pu pr au ar"
    and included: "environment_included (decode_finite_environment J) (decode_finite_environment E)"
    and quote: "judgment_value_quoted_at (decode_finite_object C) [] (decode_finite_environment J) pu pr au ar"
    by (rule finite_native_judgment_quote_correct[OF quoted])+
  have kept_package: "native_package_at (decode_finite_environment J) pu pr P"
    and kept_app: "native_application_at (decode_finite_environment J) au ar d
      (Target_Term (Whole_Artifact (decode_finite_object R))) I K"
    using native_judgment_environment_recovers(1,2)[OF package app] by (simp_all only: scoped)
  have scope: "generation_judgment_scope_at A u [] G (decode_finite_environment J) pu pr au ar"
    by (rule generation_judgment_scope_from_core[OF generation cause quote])
  show ?thesis using certified_base_cause_with_reads[OF scope kept_package kept_app included]
    minimal payload replay by blast
qed

text \<open>
  Certification depends on the actual replay and its complete judgment quote,
  the generation reading, and the exact payload and cause. Its proof is
  independent of the allocator, storage layout and construction algorithm.
  Backend instances must supply these actual facts before using the join.
\<close>

end
