theory Factor_Judgment_Scopes
  imports Factor_Judgment_Values Factor_Judgment_Retention
begin

section \<open>Recording the minimal scope of any native program and call\<close>

theorem native_judgment_recordable:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "\<exists>F C. judgment_value_quoted_at C [] F pu pr au ar \<and>
    F=native_judgment_environment F pu pr au ar \<and>
    native_package_at F pu pr P \<and> native_application_at F au ar d t I K \<and>
    native_package_environment F pu pr=native_package_environment E pu pr"
proof -
  let ?F = "native_judgment_environment E pu pr au ar"
  have kept: "native_package_at ?F pu pr P" "native_application_at ?F au ar d t I K" "environment_formed ?F"
    using native_judgment_environment_recovers[OF package app] by blast+
  have canonical: "?F=native_judgment_environment ?F pu pr au ar"
    using native_judgment_environment_idempotent[OF package app] by simp
  have program: "native_package_environment ?F pu pr=native_package_environment E pu pr"
    by (rule native_judgment_program_environment[OF package app])
  have sites: "(pu,pr)\<in>environment_positions ?F" "(au,ar)\<in>environment_positions ?F"
    by (rule native_judgment_positions[OF kept(1,2)])+
  obtain C where quote: "judgment_value_quoted_at C [] ?F pu pr au ar"
    using judgment_value_quoted_total[OF kept(3) sites] by blast
  show ?thesis by (rule exI[of _ ?F], rule exI[of _ C])
    (use quote canonical kept(1,2) program in blast)
qed

text \<open>
  A complete finite data quotation records the least environment of an actual
  native program and call, with both sites and every required binding. This
  representation is independent of a judgment's later role, truth, or proof.
\<close>

end
