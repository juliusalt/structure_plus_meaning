theory Factor_Current_Construction
  imports Factor_Current_Entries Factor_Cause Factor_Native_Construction
begin

section \<open>Construction at the entry selected by an actual current frame\<close>

definition current_constructs_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> exact_artifact list \<Rightarrow>
    (local_address\<times>exact_artifact) set \<Rightarrow> addressed_construction \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "current_constructs_at C q F au ar xs B W Z \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d t I K.
      current_entry_scope_quoted_at C q A l G p E pu pr P d \<and>
      environment_formed F \<and> environment_included E F \<and>
      native_application_at F au ar d t I K \<and>
      construction_judgment_at F pu pr au ar xs B W Z)"

theorem current_construction_at_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
  shows "current_constructs_at C q F au ar xs B W Z \<longleftrightarrow>
    environment_formed F \<and> environment_included E F \<and>
    (\<exists>t I K. native_application_at F au ar d t I K) \<and>
    construction_judgment_at F pu pr au ar xs B W Z"
proof
  assume "current_constructs_at C q F au ar xs B W Z"
  then obtain A' l' G' p' E' qu qr Q e t I K where other:
    "current_entry_scope_quoted_at C q A' l' G' p' E' qu qr Q e"
    "environment_formed F" "environment_included E' F" "native_application_at F au ar e t I K"
    "construction_judgment_at F qu qr au ar xs B W Z"
    unfolding current_constructs_at_def by blast
  have same: "E=E' \<and> pu=qu \<and> pr=qr \<and> d=e"
    using current_entry_scope_unique[OF current other(1)] by blast
  show "environment_formed F \<and> environment_included E F \<and>
    (\<exists>t I K. native_application_at F au ar d t I K) \<and>
    construction_judgment_at F pu pr au ar xs B W Z"
    using other(2-5) same by blast
next
  assume "environment_formed F \<and> environment_included E F \<and>
    (\<exists>t I K. native_application_at F au ar d t I K) \<and>
    construction_judgment_at F pu pr au ar xs B W Z"
  then show "current_constructs_at C q F au ar xs B W Z"
    using current unfolding current_constructs_at_def by blast
qed

theorem current_construction_with_reads:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and formed: "environment_formed F" and included: "environment_included E F"
    and app: "native_application_at F au ar d t I K"
  shows "current_constructs_at C q F au ar xs B W Z \<longleftrightarrow>
    construction_claim_presents xs B W Z t \<and> factor_constructs P d xs B W Z"
proof -
  have package: "native_package_at F pu pr P"
    by (rule current_entry_scope_future_application(1)[OF current formed included app])
  have exists: "\<exists>t I K. native_application_at F au ar d t I K" using app by blast
  show ?thesis
    by (simp only: current_construction_at_scope[OF current] formed included exists
      construction_judgment_with_reads[OF package app] simp_thms)
qed

theorem current_construction_requires_selected_entry:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and app: "native_application_at F au ar e t I K"
    and permitted: "current_constructs_at C q F au ar xs B W Z"
  shows "e=d"
proof -
  obtain v J L where selected: "native_application_at F au ar d v J L"
    using current_construction_at_scope[OF current] permitted by blast
  show ?thesis using native_application_unique[OF app selected] by blast
qed

theorem current_construction_program_scope:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and permitted: "current_constructs_at C q F au ar xs B W Z"
  shows "environment_formed F \<and> environment_included E F \<and>
    native_package_at F pu pr P \<and> native_package_environment F pu pr=E \<and>
    construction_judgment_at F pu pr au ar xs B W Z \<and> native_positive_holds F pu pr au ar"
proof -
  obtain t I K where parts: "environment_formed F" "environment_included E F"
    "native_application_at F au ar d t I K" "construction_judgment_at F pu pr au ar xs B W Z"
    using current_construction_at_scope[OF current] permitted by blast
  show ?thesis using parts current_entry_scope_future_application(1,2)[OF current parts(1-3)]
    construction_judgment_truth[OF parts(4)] by blast
qed

theorem current_construction_account_unique:
  assumes first: "current_constructs_at C q F au ar xs B W Z"
    and second: "current_constructs_at D r F au ar ys B' W' Z'"
  shows "xs=ys \<and> B=B' \<and> W=W' \<and> Z=Z'"
proof -
  obtain pu pr qu qr where judgments:
    "construction_judgment_at F pu pr au ar xs B W Z"
    "construction_judgment_at F qu qr au ar ys B' W' Z'"
    using first second unfolding current_constructs_at_def by blast
  show ?thesis by (rule construction_judgment_account_unique[OF judgments])
qed

section \<open>Every permitted account presentation has an actual current call\<close>

theorem current_construction_application_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and permitted: "factor_constructs P d xs B W Z"
    and present: "construction_claim_presents xs B W Z t"
  shows "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and>
    au\<notin>environment_uses E \<and> native_package_at F pu pr P \<and>
    native_application_at F au [] d t I K \<and> native_package_environment F pu pr=E \<and>
    current_constructs_at C q F au [] xs B W Z \<and>
    (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R\<longleftrightarrow>artifact_at E v R) \<and>
    (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w\<longleftrightarrow>binds_slot E v k w)"
proof -
  have closed: "closed_native_package_at E pu pr P"
    and fixed: "native_package_environment E pu pr=E" and member: "d\<in>system_definitions P"
    using current_entry_scope_closed[OF current] by auto
  have package: "native_package_at E pu pr P" using closed by (simp add: closed_native_package_at_def)
  have built: "source_constructs xs B W Z" and coords: "construction_coordinates_formed B W"
    and invariant: "construction_permission_invariant P d"
    using permitted by (auto simp: factor_constructs_def)
  obtain F au I K where future: "environment_formed F" "environment_included E F"
    "au\<notin>environment_uses E" "native_package_at F pu pr P" "native_application_at F au [] d t I K"
    "native_package_environment F pu pr=native_package_environment E pu pr"
    "\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R\<longleftrightarrow>artifact_at E v R"
    "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w\<longleftrightarrow>binds_slot E v k w"
    using native_construction_application_total[OF package member built coords invariant present] by blast
  have allowed: "current_constructs_at C q F au [] xs B W Z"
    using present permitted by (simp only: current_construction_with_reads[OF current future(1,2,5)])
  have canonical: "native_package_environment F pu pr=E" using future(6) fixed by simp
  show ?thesis using future canonical allowed by blast
qed

text \<open>
  The current purpose fixes the construction entry and its complete native
  program. The existing construction judgment supplies the full account,
  structural assembly validity, presentation invariance, and ordinary
  permission. Neither an auxiliary entry nor a successor program can replace
  that selected entry.

  Every permitted complete account has an actual native call retaining the
  original program environment and every old binding. Input order, repeated
  input occurrences, base entries, selected pieces, and origins remain the
  existing distinct fields. This raw current judgment contains no proof,
  historical succession, or adoption of its output.
\<close>

end
