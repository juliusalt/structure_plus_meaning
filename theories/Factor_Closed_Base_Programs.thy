theory Factor_Closed_Base_Programs
  imports Factor_Compiled_Applications Factor_Certified_Base_Cause
begin

section \<open>A previously closed program judges future literal payloads\<close>

locale closed_base_program =
  fixes E :: "local_address option artifact_environment" and pu :: "local_address option"
    and Q :: "local_address option native_system"
    and d :: "local_address option definition_site"
  assumes closed: "closed_native_package_at E pu [] Q"
    and canonical: "native_package_environment E pu []=E"
    and member: "d\<in>system_definitions Q"
begin

theorem future_payload:
  assumes formed: "exact_formed R"
  shows "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
    au\<notin>environment_uses E \<and> native_package_at F pu [] Q \<and>
    native_application_at F au [] d (Target_Term (Whole_Artifact R)) I K \<and>
    native_package_environment F pu []=E \<and>
    (base_admission_judgment_at F pu [] au [] R \<longleftrightarrow>
      (d,Target_Term (Whole_Artifact R))\<in>positive_meaning Q) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>S. artifact_at F v S \<longleftrightarrow> artifact_at E v S) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
proof -
  have package: "native_package_at E pu [] Q" using closed by (simp add: closed_native_package_at_def)
  have argument: "term_formed (Target_Term (Whole_Artifact R))" using formed by simp
  obtain F au I K where parts: "environment_formed F" "environment_included E F"
    "au\<notin>environment_uses E" "native_package_at F pu [] Q"
    "native_application_at F au [] d (Target_Term (Whole_Artifact R)) I K"
    "native_package_environment F pu []=native_package_environment E pu []"
    "\<forall>v\<in>environment_uses E. \<forall>S. artifact_at F v S \<longleftrightarrow> artifact_at E v S"
    "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w"
    using native_application_extension_total[OF package member argument]
    by (elim exE conjE) (rule that; assumption)
  show ?thesis by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
    (use parts canonical base_admission_with_reads[OF parts(4,5)] in auto)
qed

theorem certified_generation:
  assumes holds: "(d,Target_Term (Whole_Artifact R))\<in>positive_meaning Q"
    and locus: "target_formed l" and predecessors: "\<forall>G\<in>fset previous. generation_formed G"
  shows "\<exists>C. \<exists>A :: local_address option artifact_environment. \<exists>u F au H root.
    generation_at A u [] (Generation l previous (Whole_Artifact R) (Whole_Artifact C)) \<and>
    generation_environment_closed A {(u,[])} \<and>
    generation_judgment_scope_at A u [] (Generation l previous (Whole_Artifact R) (Whole_Artifact C)) F pu [] au [] \<and>
    F=native_judgment_environment F pu [] au [] \<and> native_package_environment F pu []=E \<and>
    recorded_base_cause_at A u [] (Generation l previous (Whole_Artifact R) (Whole_Artifact C)) R \<and>
    certified_base_cause_at A u [] (Generation l previous (Whole_Artifact R) (Whole_Artifact C)) H root R"
proof -
  have formed: "exact_formed R"
    using schema_call_formed_target[OF positive_meaning_formed[OF holds]] by simp
  obtain F au where admitted: "base_admission_judgment_at F pu [] au [] R"
    and program: "native_package_environment F pu []=E"
    using future_payload[OF formed] holds by blast
  obtain B C and A :: "local_address option artifact_environment" and u
    where quote: "judgment_value_quoted_at C [] B pu [] au []"
    and minimal: "B=native_judgment_environment B pu [] au []"
    and kept: "native_package_environment B pu []=native_package_environment F pu []"
    and gen: "generation_at A u [] (Generation l previous (Whole_Artifact R) (Whole_Artifact C))"
    and closed: "generation_environment_closed A {(u,[])}"
    and valid: "recorded_base_cause_at A u [] (Generation l previous (Whole_Artifact R) (Whole_Artifact C)) R"
    using base_admission_generation_total[OF admitted locus predecessors] by blast
  have scope: "generation_judgment_scope_at A u []
      (Generation l previous (Whole_Artifact R) (Whole_Artifact C)) B pu [] au []"
    by (rule generation_judgment_scope_from_core[OF gen _ quote]) simp
  obtain H root where certified:
    "certified_base_cause_at A u [] (Generation l previous (Whole_Artifact R) (Whole_Artifact C)) H root R"
    using recorded_base_certification_total[OF valid] by blast
  show ?thesis by (rule exI[of _ C], rule exI[of _ A], rule exI[of _ u], rule exI[of _ B],
    rule exI[of _ au], rule exI[of _ H], rule exI[of _ root])
    (use gen closed scope minimal kept program valid certified in blast)
qed

end

text \<open>
  The closed program is fixed before any future payload. Extending it with a
  literal call preserves all existing artifacts and bindings. A successful
  call gives an actual generation whose cause retains that same complete
  program scope and whose payload is the artifact judged by the call.
  Replay evidence is separate from the unchanged generation core.

  Predecessor formation is retained as an explicit premise. This theorem
  does not turn it into historical permission or an execution-cost bound.
\<close>

end
