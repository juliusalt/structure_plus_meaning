theory Factor_Native_Amendment
  imports Factor_Amendment Factor_Compiled_Applications
begin

section \<open>Every complete future argument has an actual call at the selected entry\<close>

theorem current_acceptance_application_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and frame: "current_frame_quoted_at C q D qu qr bu br N v root"
    and invariant: "amendment_permission_invariant P d"
    and present: "amendment_value_presents D qu qr bu br N v root H c t"
  shows "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
    au\<notin>environment_uses E \<and> native_package_at F pu pr P \<and>
    native_application_at F au [] d t I K \<and> native_package_environment F pu pr=E \<and>
    (native_application_formed F pu pr au []\<longleftrightarrow>schema_call_formed P d t) \<and>
    (current_accepts_at C q F au [] H c\<longleftrightarrow>factor_accepts P d D qu qr bu br N v root H c) \<and>
    (current_accepts_at C q F au [] H c\<longleftrightarrow>native_positive_holds F pu pr au []) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R\<longleftrightarrow>artifact_at E w R) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>k z. binds_slot F w k z\<longleftrightarrow>binds_slot E w k z)"
proof -
  have closed: "closed_native_package_at E pu pr P" and canonical: "native_package_environment E pu pr=E"
    and member: "d\<in>system_definitions P" using current_entry_scope_closed[OF current] by auto
  have package: "native_package_at E pu pr P" using closed by (simp add: closed_native_package_at_def)
  have tf: "term_formed t" using amendment_value_presents_formed[OF present] by blast
  obtain F au I K where future: "environment_formed F" "environment_included E F"
    "au\<notin>environment_uses E" "native_package_at F pu pr P" "native_application_at F au [] d t I K"
    "native_package_environment F pu pr=native_package_environment E pu pr"
    "native_application_formed F pu pr au []\<longleftrightarrow>schema_call_formed P d t"
    "\<forall>w\<in>environment_uses E. \<forall>R. artifact_at F w R\<longleftrightarrow>artifact_at E w R"
    "\<forall>w\<in>environment_uses E. \<forall>k z. binds_slot F w k z\<longleftrightarrow>binds_slot E w k z"
    using native_application_extension_total[OF package member tf] by blast
  have permission: "current_accepts_at C q F au [] H c\<longleftrightarrow>factor_accepts P d D qu qr bu br N v root H c"
    and truth: "current_accepts_at C q F au [] H c\<longleftrightarrow>native_positive_holds F pu pr au []"
    by (rule current_acceptance_at_presentation[OF current frame future(1,2,5) invariant present])+
  have fixed: "native_package_environment F pu pr=E" using future(6) canonical by simp
  show ?thesis by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
    (use future(1-5,7-9) fixed permission truth in blast)
qed

theorem current_acceptance_presentations_agree:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and frame: "current_frame_quoted_at C q D qu qr bu br N v root"
    and first: "environment_formed F" "environment_included E F" "native_application_at F au ar d t I K"
    and second: "environment_formed M" "environment_included E M" "native_application_at M cu cr d w J L"
    and invariant: "amendment_permission_invariant P d"
    and left: "amendment_value_presents D qu qr bu br N v root H c t"
    and right: "amendment_value_presents D qu qr bu br N v root H c w"
  shows "native_application_formed F pu pr au ar\<longleftrightarrow>native_application_formed M pu pr cu cr"
    and "current_accepts_at C q F au ar H c\<longleftrightarrow>current_accepts_at C q M cu cr H c"
proof -
  show "native_application_formed F pu pr au ar\<longleftrightarrow>native_application_formed M pu pr cu cr"
    using current_entry_scope_future_application(3)[OF current first]
      current_entry_scope_future_application(3)[OF current second]
      amendment_permission_invariantD(1)[OF invariant left right] by blast
  show "current_accepts_at C q F au ar H c\<longleftrightarrow>current_accepts_at C q M cu cr H c"
    by (simp only: current_acceptance_at_presentation(1)[OF current frame first invariant left]
        current_acceptance_at_presentation(1)[OF current frame second invariant right])
qed

section \<open>One compilation retains a policy for all complete future subjects\<close>

theorem native_amendment_program_compilation:
  fixes P :: "('a,'s,'d,'c) schema_system"
  assumes formed: "schema_system_formed P" and member: "d\<in>system_definitions P"
    and invariant: "amendment_permission_invariant P d"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu Q e.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    e\<in>system_definitions Q \<and> amendment_permission_invariant Q e \<and>
    (\<forall>t. (schema_call_formed Q e t\<longleftrightarrow>schema_call_formed P d t) \<and>
      ((e,t)\<in>positive_meaning Q\<longleftrightarrow>(d,t)\<in>positive_meaning P)) \<and>
    (\<forall>D qu qr bu br N v root H c.
      factor_accepts Q e D qu qr bu br N v root H c\<longleftrightarrow>
      factor_accepts P d D qu qr bu br N v root H c)"
proof -
  obtain g :: "'d \<Rightarrow> local_address option definition_site" and E pu Q where compiled:
    "inj_on g (system_definitions P)" "closed_native_package_at E pu [] Q"
    "native_package_environment E pu []=E" "system_alpha_variant (rename_system g P) Q"
    "positive_meaning Q=image (map_prod g id) (positive_meaning P)"
    using program_compilation_total[OF formed] by metis
  have boundary: "\<And>t. schema_call_formed Q (g d) t\<longleftrightarrow>schema_call_formed P d t"
    by (rule compiled_system_call_boundary[OF formed compiled(1,4) member])
  have meaning: "\<And>t. (g d,t)\<in>positive_meaning Q\<longleftrightarrow>(d,t)\<in>positive_meaning P"
    by (rule compiled_system_meaning_at[OF compiled(1) member compiled(5)])
  have admitted: "amendment_permission_invariant Q (g d)"
    using amendment_permission_invariant_transport[OF boundary meaning] invariant by blast
  have inside: "g d\<in>system_definitions Q"
    using compiled(4) member by (auto simp: system_alpha_variant_def renamed_system_definitions)
  have permission: "\<And>D qu qr bu br N v root H c.
      factor_accepts Q (g d) D qu qr bu br N v root H c\<longleftrightarrow>
      factor_accepts P d D qu qr bu br N v root H c"
    using admitted invariant by (simp add: factor_accepts_def meaning)
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g d"])
       (use compiled(2,3) inside admitted boundary meaning permission in blast)
qed

text \<open>
  The program is fixed before future candidate and certificate data are
  supplied. Every complete argument has a native application at the exact
  selected entry. Its canonical program scope and every old artifact and
  binding remain unchanged in the constructed call environment.

  Different complete presentations give the same formed-call boundary and
  permission under the explicit invariance condition. Native compilation
  preserves that condition and the policy on all subjects. These construction
  and locality results introduce no privileged acceptance definition and do
  not supply evidence that an arbitrary policy satisfies the amendment protocol.
\<close>

end
