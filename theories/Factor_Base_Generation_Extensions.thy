theory Factor_Base_Generation_Extensions
  imports Factor_Generation_Scope_Extensions Factor_Closed_Base_Programs
begin

theorem base_admission_generation_extension:
  fixes E A :: "local_address option artifact_environment" and n :: nat
  assumes admitted: "base_admission_judgment_at E pu pr au ar R"
    and existing: "environment_formed A" and locus: "target_formed l"
    and distinct: "inj_on g {..<n}"
    and predecessors: "\<forall>i<n. generation_at A (v i) (a i) (g i)"
  shows "\<exists>F C B u H root.
    judgment_value_quoted_at C [] F pu pr au ar \<and>
    F=native_judgment_environment F pu pr au ar \<and>
    native_package_environment F pu pr=native_package_environment E pu pr \<and>
    environment_formed B \<and> environment_included A B \<and>
    generation_at B u [] (Generation l (Abs_fset (g ` {..<n})) (Whole_Artifact R) (Whole_Artifact C)) \<and>
    generation_judgment_scope_at B u []
      (Generation l (Abs_fset (g ` {..<n})) (Whole_Artifact R) (Whole_Artifact C)) F pu pr au ar \<and>
    recorded_base_cause_at B u [] (Generation l (Abs_fset (g ` {..<n})) (Whole_Artifact R) (Whole_Artifact C)) R \<and>
    certified_base_cause_at B u []
      (Generation l (Abs_fset (g ` {..<n})) (Whole_Artifact R) (Whole_Artifact C)) H root R"
proof -
  obtain F C where quote: "judgment_value_quoted_at C [] F pu pr au ar"
    and minimal: "F=native_judgment_environment F pu pr au ar"
    and kept: "base_admission_judgment_at F pu pr au ar R"
    and program: "native_package_environment F pu pr=native_package_environment E pu pr"
    using base_admission_recordable[OF admitted] by blast
  have payload: "target_formed (Whole_Artifact R)" using base_admission_formed[OF admitted] by simp
  obtain B u where formed: "environment_formed B" and included: "environment_included A B"
    and gen: "generation_at B u [] (Generation l (Abs_fset (g ` {..<n})) (Whole_Artifact R) (Whole_Artifact C))"
    and scope: "generation_judgment_scope_at B u []
      (Generation l (Abs_fset (g ` {..<n})) (Whole_Artifact R) (Whole_Artifact C)) F pu pr au ar"
    using generation_judgment_scope_extension[OF existing quote locus payload distinct predecessors] by blast
  have valid: "recorded_base_cause_at B u []
      (Generation l (Abs_fset (g ` {..<n})) (Whole_Artifact R) (Whole_Artifact C)) R"
    using recorded_base_cause_with_scope[OF scope] minimal kept by simp
  obtain H root where certificate: "certified_base_cause_at B u []
      (Generation l (Abs_fset (g ` {..<n})) (Whole_Artifact R) (Whole_Artifact C)) H root R"
    using recorded_base_certification_total[OF valid] by blast
  show ?thesis by (rule exI[of _ F], rule exI[of _ C], rule exI[of _ B],
    rule exI[of _ u], rule exI[of _ H], rule exI[of _ root])
    (use quote minimal program formed included gen scope valid certificate in blast)
qed

context closed_base_program
begin

theorem certified_extension:
  fixes A :: "local_address option artifact_environment" and n :: nat
  assumes holds: "(d,Target_Term (Whole_Artifact R))\<in>positive_meaning Q"
    and existing: "environment_formed A" and locus: "target_formed l"
    and distinct: "inj_on g {..<n}"
    and predecessors: "\<forall>i<n. generation_at A (v i) (a i) (g i)"
  shows "\<exists>F C B u au H root.
    F=native_judgment_environment F pu [] au [] \<and> native_package_environment F pu []=E \<and>
    environment_formed B \<and> environment_included A B \<and>
    generation_at B u [] (Generation l (Abs_fset (g ` {..<n})) (Whole_Artifact R) (Whole_Artifact C)) \<and>
    generation_judgment_scope_at B u []
      (Generation l (Abs_fset (g ` {..<n})) (Whole_Artifact R) (Whole_Artifact C)) F pu [] au [] \<and>
    recorded_base_cause_at B u [] (Generation l (Abs_fset (g ` {..<n})) (Whole_Artifact R) (Whole_Artifact C)) R \<and>
    certified_base_cause_at B u []
      (Generation l (Abs_fset (g ` {..<n})) (Whole_Artifact R) (Whole_Artifact C)) H root R"
proof -
  have formed: "exact_formed R"
    using schema_call_formed_target[OF positive_meaning_formed[OF holds]] by simp
  obtain K au where admitted: "base_admission_judgment_at K pu [] au [] R"
    and program: "native_package_environment K pu []=E"
    using future_payload[OF formed] holds by blast
  show ?thesis using base_admission_generation_extension[OF admitted existing locus distinct predecessors]
    program by blast
qed

end

text \<open>
  The actual native judgment admits this payload before recording. The record
  extends the existing generation environment through its predecessor uses,
  preserves the fixed closed cause program, and has separate replay evidence.
  Local record construction avoids invoking the recursive presentation-totality
  theorem on the predecessor cores. Allocation, lookup, and replay costs still
  need their own execution accounts before an overall cost claim is justified.
\<close>

end
