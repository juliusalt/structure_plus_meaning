theory Factor_Finite_Generation_Replay
  imports RRA_Finite_Generation_Construction Factor_Finite_Judgment_Quotation
    Factor_Finite_Literal_Replay Factor_Certified_Base_Cause
begin

definition finite_record_native_replay where
  "finite_record_native_replay H l rows E pu pr au ar root R=(
    if finite_literal_replay_ready E pu pr au ar root R then
      (case finite_native_judgment_quote E pu pr au ar of None \<Rightarrow> None
      | Some (J,C) \<Rightarrow> map_option (\<lambda>(A,u,G). (A,u,G,J,C))
          (finite_construct_generation_record H l (Finite_Whole R) (Finite_Whole C) rows))
    else None)"

lemma finite_record_native_replay_result:
  "finite_record_native_replay H l rows E pu pr au ar root R=Some (A,u,G,J,C) \<longleftrightarrow>
    finite_literal_replay_ready E pu pr au ar root R \<and>
    finite_native_judgment_quote E pu pr au ar=Some (J,C) \<and>
    finite_construct_generation_record H l (Finite_Whole R) (Finite_Whole C) rows=Some (A,u,G)"
  by (auto simp: finite_record_native_replay_def split: option.splits prod.splits if_splits)

theorem finite_record_native_replay_certified:
  assumes result: "finite_record_native_replay H l rows E pu pr au ar root R=Some (A,u,G,J,C)"
  shows "certified_base_cause_at (decode_finite_environment A) u [] (decode_finite_generation G)
    (decode_finite_environment E) root (decode_finite_object R)"
proof -
  have ready: "finite_literal_replay_ready E pu pr au ar root R"
    and quoted: "finite_native_judgment_quote E pu pr au ar=Some (J,C)"
    and generated: "finite_construct_generation_record H l (Finite_Whole R) (Finite_Whole C) rows=Some (A,u,G)"
    using result by (simp only: finite_record_native_replay_result; blast)+
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
  have checked: "finite_check_generation G A u []"
    by (rule finite_construct_generation_record_correct(6)[OF generated])
  have generation: "generation_at (decode_finite_environment A) u [] (decode_finite_generation G)"
    using checked by (simp only: finite_check_generation_exact)
  have core: "G=finite_generation_record_core l (Finite_Whole R) (Finite_Whole C) rows"
    by (rule finite_construct_generation_record_correct(2)[OF generated])
  have payload: "generation_payload (decode_finite_generation G)=Whole_Artifact (decode_finite_object R)"
    and cause: "generation_cause (decode_finite_generation G)=Whole_Artifact (decode_finite_object C)"
    by (simp_all add: core finite_generation_record_core_def decode_finite_generation_node)
  have scope: "generation_judgment_scope_at (decode_finite_environment A) u []
    (decode_finite_generation G) (decode_finite_environment J) pu pr au ar"
    by (rule generation_judgment_scope_from_core[OF generation cause quote])
  show ?thesis using certified_base_cause_with_reads[OF scope kept_package kept_app included]
    minimal payload replay by blast
qed

corollary finite_record_native_replay_admitted:
  assumes "finite_record_native_replay H l rows E pu pr au ar root R=Some (A,u,G,J,C)"
  shows "recorded_base_cause_at (decode_finite_environment A) u []
    (decode_finite_generation G) (decode_finite_object R)"
  by (rule certified_base_cause_sound[OF finite_record_native_replay_certified[OF assms]])

corollary finite_record_native_replay_preserves_history:
  assumes "finite_record_native_replay H l rows E pu pr au ar root R=Some (A,u,G,J,C)"
  shows "finite_environment_agrees_on H A (finite_environment_uses H)"
    "finite_environment_formed A"
proof -
  have generated: "finite_construct_generation_record H l (Finite_Whole R) (Finite_Whole C) rows=Some (A,u,G)"
    using assms by (simp only: finite_record_native_replay_result; blast)
  show "finite_environment_agrees_on H A (finite_environment_uses H)"
    by (rule finite_construct_generation_record_correct(5)[OF generated])
  show "finite_environment_formed A" by (rule finite_construct_generation_record_correct(3)[OF generated])
qed

text \<open>
  The original payload must be the whole artifact named by the actual call,
  and the native replay must close without assertions. Only then is its least
  judgment scope quoted and recorded as the cause of that same payload.
  The existing certified-base-cause contract proves the join, and its existing
  soundness theorem supplies recorded admission. Earlier generation material
  and bindings are preserved. This does not establish historical permission
  or adequate original requirements for an arbitrary development workflow.
\<close>

end
