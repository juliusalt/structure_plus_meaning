theory Factor_Finite_Literal_Replay
  imports Factor_Executable_Replay Factor_Executable_Judgment_Retention
begin

definition finite_literal_application_ready where
  "finite_literal_application_ready E au ar R=fBex (finite_application_readings E au ar)
    (\<lambda>((d,t),I,K). t=Finite_Target (Finite_Whole R))"

theorem finite_literal_application_ready_at:
  "finite_literal_application_ready E au ar R \<longleftrightarrow>
    (\<exists>d I K. native_application_at (decode_finite_environment E) au ar d
      (Target_Term (Whole_Artifact (decode_finite_object R))) I K)"
proof
  assume ready: "finite_literal_application_ready E au ar R"
  obtain d I K where row: "((d,Finite_Target (Finite_Whole R)),I,K) |\<in>| finite_application_readings E au ar"
    using ready by (auto simp: finite_literal_application_ready_def Bex_def split_paired_Ex)
  have app: "native_application_at (decode_finite_environment E) au ar d
    (Target_Term (Whole_Artifact (decode_finite_object R))) (fset I) (fset K)"
    using row by (simp only: finite_application_readings_correct decode_finite_term.simps decode_finite_target.simps)
  show "\<exists>d I K. native_application_at (decode_finite_environment E) au ar d
    (Target_Term (Whole_Artifact (decode_finite_object R))) I K" using app by blast
next
  assume "\<exists>d I K. native_application_at (decode_finite_environment E) au ar d
    (Target_Term (Whole_Artifact (decode_finite_object R))) I K"
  then obtain d I K where app: "native_application_at (decode_finite_environment E) au ar d
    (Target_Term (Whole_Artifact (decode_finite_object R))) I K" by blast
  obtain T F W where row: "((d,T),F,W) |\<in>| finite_application_readings E au ar"
    and decoded: "decode_finite_term T=Target_Term (Whole_Artifact (decode_finite_object R))"
    using finite_application_readings_complete[OF app] by blast
  have same: "T=Finite_Target (Finite_Whole R)"
    using decoded by (simp only: decode_finite_term_injective[symmetric]
      decode_finite_term.simps decode_finite_target.simps)
  show "finite_literal_application_ready E au ar R"
    using row same by (auto simp: finite_literal_application_ready_def)
qed

definition finite_literal_replay_ready where
  "finite_literal_replay_ready E pu pr au ar root R=(finite_native_replay_proves E pu pr au ar root \<and>
    finite_literal_application_ready E au ar R)"

theorem finite_literal_replay_ready_at:
  "finite_literal_replay_ready E pu pr au ar root R \<longleftrightarrow>
    native_replay_at (decode_finite_environment E) pu pr au ar root {} \<and>
    (\<exists>d I K. native_application_at (decode_finite_environment E) au ar d
      (Target_Term (Whole_Artifact (decode_finite_object R))) I K)"
  by (simp only: finite_literal_replay_ready_def finite_native_replay_proves_correct
    finite_literal_application_ready_at)

lemma finite_literal_replay_ready_properties:
  assumes ready: "finite_literal_replay_ready E pu pr au ar root R"
  shows "finite_native_judgment_ready E pu pr au ar" "finite_exact_formed R"
proof -
  have replay: "native_replay_at (decode_finite_environment E) pu pr au ar root {}"
    using ready by (simp only: finite_literal_replay_ready_at; blast)
  obtain d I K where app: "native_application_at (decode_finite_environment E) au ar d
    (Target_Term (Whole_Artifact (decode_finite_object R))) I K"
    using ready by (simp only: finite_literal_replay_ready_at; blast)
  obtain P where package: "native_package_at (decode_finite_environment E) pu pr P"
    using replay by (auto simp: native_replay_at_def)
  show "finite_native_judgment_ready E pu pr au ar"
    using package app by (simp only: finite_native_judgment_ready_correct; blast)
  show "finite_exact_formed R"
    using native_application_properties[OF app] by (simp add: finite_exact_formed_correct)
qed

text \<open>
  The whole requested payload is compared with the actual native call argument.
  Its complete native proof must close without assertions at the supplied root.
  The two exact conditions share the existing readers and retain the original
  program and call sites. Quotation by itself supplies neither condition.
\<close>

end
