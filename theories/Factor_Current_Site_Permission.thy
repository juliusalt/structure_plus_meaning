theory Factor_Current_Site_Permission
  imports Factor_Site_Permission Factor_Current_Entries Factor_Compiled_Applications
begin

section \<open>The current purpose selects the site-permission entry\<close>

definition current_permits_site_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "current_permits_site_at C q F au ar N u r \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d t I K.
      current_entry_scope_quoted_at C q A l G p E pu pr P d \<and>
      environment_formed F \<and> environment_included E F \<and>
      native_application_at F au ar d t I K \<and> native_site_permission_at F pu pr au ar N u r)"

theorem current_site_permission_at_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
  shows "current_permits_site_at C q F au ar N u r\<longleftrightarrow>
    environment_formed F \<and> environment_included E F \<and>
    (\<exists>t I K. native_application_at F au ar d t I K) \<and> native_site_permission_at F pu pr au ar N u r"
proof
  assume "current_permits_site_at C q F au ar N u r"
  then obtain A' l' G' p' E' qu qr Q e t I K where other:
    "current_entry_scope_quoted_at C q A' l' G' p' E' qu qr Q e"
    "environment_formed F" "environment_included E' F" "native_application_at F au ar e t I K"
    "native_site_permission_at F qu qr au ar N u r"
    unfolding current_permits_site_at_def by blast
  have same: "E=E' \<and> pu=qu \<and> pr=qr \<and> d=e"
    using current_entry_scope_unique[OF current other(1)] by blast
  show "environment_formed F \<and> environment_included E F \<and>
    (\<exists>t I K. native_application_at F au ar d t I K) \<and> native_site_permission_at F pu pr au ar N u r"
    using other(2-5) same by blast
next
  assume "environment_formed F \<and> environment_included E F \<and>
    (\<exists>t I K. native_application_at F au ar d t I K) \<and> native_site_permission_at F pu pr au ar N u r"
  then show "current_permits_site_at C q F au ar N u r"
    using current unfolding current_permits_site_at_def by blast
qed

theorem current_site_permission_with_reads:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and formed: "environment_formed F" and included: "environment_included E F"
    and app: "native_application_at F au ar d t I K"
  shows "current_permits_site_at C q F au ar N u r\<longleftrightarrow>
    site_permission_invariant P d \<and> site_value_presents N u r t \<and> (d,t)\<in>positive_meaning P"
proof -
  have package: "native_package_at F pu pr P"
    by (rule current_entry_scope_future_application(1)[OF current formed included app])
  have exists: "\<exists>t I K. native_application_at F au ar d t I K" using app by blast
  show ?thesis
    by (simp only: current_site_permission_at_scope[OF current] formed included exists
      native_site_permission_with_reads[OF package app] simp_thms)
qed

theorem current_site_permission_at_presentation:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and formed: "environment_formed F" and included: "environment_included E F"
    and app: "native_application_at F au ar d t I K"
    and invariant: "site_permission_invariant P d" and present: "site_value_presents N u r t"
  shows "current_permits_site_at C q F au ar N u r\<longleftrightarrow>factor_permits_site P d N u r"
    and "current_permits_site_at C q F au ar N u r\<longleftrightarrow>native_positive_holds F pu pr au ar"
proof -
  have exact: "current_permits_site_at C q F au ar N u r\<longleftrightarrow>(d,t)\<in>positive_meaning P"
    by (simp only: current_site_permission_with_reads[OF current formed included app] invariant present simp_thms)
  show "current_permits_site_at C q F au ar N u r\<longleftrightarrow>factor_permits_site P d N u r"
    by (simp only: exact factor_site_permission_at_presentation[OF invariant present])
  show "current_permits_site_at C q F au ar N u r\<longleftrightarrow>native_positive_holds F pu pr au ar"
    by (simp only: exact current_entry_scope_future_application(4)[OF current formed included app])
qed

theorem current_site_permission_requires_selected_entry:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and app: "native_application_at F au ar e t I K"
    and permitted: "current_permits_site_at C q F au ar N u r"
  shows "e=d"
proof -
  obtain v J L where selected: "native_application_at F au ar d v J L"
    using current_site_permission_at_scope[OF current] permitted by blast
  show ?thesis using native_application_unique[OF app selected] by blast
qed

theorem current_site_permission_program_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and permitted: "current_permits_site_at C q F au ar N u r"
  shows "environment_formed F \<and> environment_included E F \<and>
    native_package_at F pu pr P \<and> native_package_environment F pu pr=E \<and>
    native_site_permission_at F pu pr au ar N u r \<and> native_positive_holds F pu pr au ar"
proof -
  obtain t I K where parts: "environment_formed F" "environment_included E F"
    "native_application_at F au ar d t I K" "native_site_permission_at F pu pr au ar N u r"
    using current_site_permission_at_scope[OF current] permitted by blast
  show ?thesis using parts current_entry_scope_future_application(1,2)[OF current parts(1-3)]
    native_site_permission_truth[OF parts(4)] by blast
qed

theorem current_site_permission_subject_unique:
  assumes first: "current_permits_site_at C q F au ar N u r"
    and second: "current_permits_site_at D s F au ar M v a"
  shows "N=M \<and> u=v \<and> r=a"
proof -
  obtain pu pr qu qr where permission:
    "native_site_permission_at F pu pr au ar N u r" "native_site_permission_at F qu qr au ar M v a"
    using first second unfolding current_permits_site_at_def by blast
  show ?thesis by (rule native_site_permission_subject_unique[OF permission])
qed

section \<open>Every future permitted site value has an actual call\<close>

theorem current_site_permission_application_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and permitted: "factor_permits_site P d N u r" and present: "site_value_presents N u r t"
  shows "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
    au\<notin>environment_uses E \<and> native_package_at F pu pr P \<and>
    native_application_at F au [] d t I K \<and> native_package_environment F pu pr=E \<and>
    current_permits_site_at C q F au [] N u r \<and>
    (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R\<longleftrightarrow>artifact_at E v R) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w\<longleftrightarrow>binds_slot E v k w)"
proof -
  have closed: "closed_native_package_at E pu pr P"
    and fixed: "native_package_environment E pu pr=E" and member: "d\<in>system_definitions P"
    using current_entry_scope_closed[OF current] by auto
  have package: "native_package_at E pu pr P" using closed by (simp add: closed_native_package_at_def)
  have tf: "term_formed t" using site_value_presents_formed[OF present] by blast
  have invariant: "site_permission_invariant P d" using permitted by (simp add: factor_permits_site_def)
  obtain F au I K where future: "environment_formed F" "environment_included E F"
    "au\<notin>environment_uses E" "native_package_at F pu pr P" "native_application_at F au [] d t I K"
    "native_package_environment F pu pr=native_package_environment E pu pr"
    "\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R\<longleftrightarrow>artifact_at E v R"
    "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w\<longleftrightarrow>binds_slot E v k w"
    using native_application_extension_total[OF package member tf] by blast
  have allowed: "current_permits_site_at C q F au [] N u r"
    using current_site_permission_at_presentation(1)[OF current future(1,2,5) invariant present] permitted by blast
  have canonical: "native_package_environment F pu pr=E" using future(6) fixed by simp
  show ?thesis using future allowed canonical by blast
qed

text \<open>
  The permission entry is recovered from the actual adopted purpose. Its
  native calls retain the exact current program and every existing binding.
  The submitted environment is complete ordinary data; its definitions do
  not become rules of the permission call.

  Every permitted complete presentation has a future selected call. No
  certificate, definition-role assignment, or dependency-coverage condition
  is part of this raw permission. The higher dependency join supplies those
  separate requirements.
\<close>

end
