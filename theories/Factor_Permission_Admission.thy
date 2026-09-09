theory Factor_Permission_Admission
  imports Factor_Permission_Invariance Factor_Related_Test_Admission
begin

section \<open>The subject class and comparison meaning precede candidate admission\<close>

locale presented_permission_admission =
  fixes presents :: "'v \<Rightarrow> factor_term \<Rightarrow> bool" and subject admissible
    and C :: "local_address option artifact_environment" and k :: "local_address option definition_site"
    and c :: factor_term and cu cr R
  assumes class_contract: "presentation_class presents subject admissible"
    and value_formed: "\<And>a t. presents a t \<Longrightarrow> term_formed t"
    and reference: "native_package_at C cu cr R"
    and reference_value: "environment_value_presents C c"
    and entry: "k\<in>system_definitions R"
    and comparison: "\<And>p q. (k,Pair_Term p q)\<in>positive_meaning R \<longleftrightarrow>
      presentation_transport presents presents p q"
begin

lemma reference_fields: "term_formed c" "term_formed (definition_site_value k)"
proof -
  have formed: "environment_formed C" using environment_value_presents_formed[OF reference_value] by blast
  have position: "k\<in>environment_positions C" by (rule native_package_entry_position[OF reference entry])
  show "term_formed c" using environment_value_presents_formed[OF reference_value] by blast
  show "term_formed (definition_site_value k)" using environment_position_address[OF formed position] by simp
qed

sublocale checker: related_test_admission c "definition_site_value k"
  by (rule related_test_admission.intro[OF reference_fields])

theorem profile_permission:
  assumes package: "native_package_at E pu pr P"
    and profile: "native_related_test_package C k E pu pr d"
  shows "presented_program_invariant presents P d"
    "schema_call_formed P d z \<longleftrightarrow> term_formed z"
    "\<exists>test\<in>system_definitions P. (\<lambda>z. (d,z)\<in>positive_meaning P)=
      saturate_observation presents (\<lambda>z. (test,z)\<in>positive_meaning P)"
proof -
  have boundary: "schema_call_formed P d z \<longleftrightarrow> term_formed z" for z
    by (rule native_related_test_package_saturation(1)[OF reference entry comparison package profile])
  have saturation: "\<exists>test\<in>system_definitions P. (\<lambda>z. (d,z)\<in>positive_meaning P)=
      saturate_observation presents (\<lambda>z. (test,z)\<in>positive_meaning P)"
    by (rule native_related_test_package_saturation(2)[OF reference entry comparison package profile])
  obtain test where equation: "(\<lambda>z. (d,z)\<in>positive_meaning P)=
      saturate_observation presents (\<lambda>z. (test,z)\<in>positive_meaning P)"
    using saturation by blast
  show "presented_program_invariant presents P d"
    by (rule presented_program_from_saturation[OF class_contract value_formed boundary equation])
  show "schema_call_formed P d z \<longleftrightarrow> term_formed z" by (rule boundary)
  show "\<exists>test\<in>system_definitions P. (\<lambda>z. (d,z)\<in>positive_meaning P)=
      saturate_observation presents (\<lambda>z. (test,z)\<in>positive_meaning P)"
    by (rule saturation)
qed

theorem admitted_permission:
  assumes package: "native_package_at E pu pr P"
    and source: "program_entry_value_presents E pu pr d p"
    and checked: "(264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
  shows "presented_program_invariant presents P d"
    "schema_call_formed P d z \<longleftrightarrow> term_formed z"
    "\<exists>test\<in>system_definitions P. (\<lambda>z. (d,z)\<in>positive_meaning P)=
      saturate_observation presents (\<lambda>z. (test,z)\<in>positive_meaning P)"
proof -
  have presented: "program_entry_presents ((E,(pu,pr)),d) p" using source by simp
  have profile: "native_related_test_package C k E pu pr d"
    using checked by (simp only: checker.on_presentations[OF reference_value refl presented] fst_conv snd_conv)
  show "presented_program_invariant presents P d"
    "schema_call_formed P d z \<longleftrightarrow> term_formed z"
    "\<exists>test\<in>system_definitions P. (\<lambda>z. (d,z)\<in>positive_meaning P)=
      saturate_observation presents (\<lambda>z. (test,z)\<in>positive_meaning P)"
    by (rule profile_permission[OF package profile])+
qed

theorem candidate_completion:
  assumes package: "native_package_at E pu pr P" and retained: "environment_included C E"
    and callees: "k\<in>system_definitions P" "test\<in>system_definitions P"
  shows "\<exists>F u Q d. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
    d\<notin>system_definitions P \<and> system_definitions Q=insert d (system_definitions P) \<and>
    native_related_test_package C k F u [] d \<and> presented_program_invariant presents Q d \<and>
    (\<forall>z. schema_call_formed Q d z \<longleftrightarrow> term_formed z) \<and>
    (\<lambda>z. (d,z)\<in>positive_meaning Q)=saturate_observation presents (\<lambda>z. (test,z)\<in>positive_meaning P) \<and>
    (\<forall>p. program_entry_value_presents F u [] d p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))) \<and>
    (\<forall>e\<in>system_definitions P. \<forall>z.
      (schema_call_formed Q e z \<longleftrightarrow> schema_call_formed P e z) \<and>
      ((e,z)\<in>positive_meaning Q \<longleftrightarrow> (e,z)\<in>positive_meaning P))"
proof -
  have cf: "environment_formed C" using environment_value_presents_formed[OF reference_value] by blast
  have ef: "environment_formed E" using native_package_projection(1)[OF package]
    by (simp add: native_package_formed_def)
  have fixed: "native_package_at E cu cr R" by (rule native_package_included[OF reference retained ef])
  have compared: "(k,Pair_Term p q)\<in>positive_meaning P \<longleftrightarrow>
      presentation_transport presents presents p q" for p q
    by (simp only: native_packages_shared_meaning[OF package fixed callees(1) entry] comparison)
  obtain F u Q d where built:
    "closed_native_package_at F u [] Q" "native_package_environment F u []=F"
    "d\<notin>system_definitions P" "system_definitions Q=insert d (system_definitions P)"
    "native_related_test_package C k F u [] d"
    "\<forall>z. schema_call_formed Q d z \<longleftrightarrow> term_formed z"
    "\<forall>z. (d,z)\<in>positive_meaning Q \<longleftrightarrow>
      (\<exists>q. (k,Pair_Term z q)\<in>positive_meaning P \<and> (test,q)\<in>positive_meaning P)"
    "\<forall>e\<in>system_definitions P. \<forall>z.
      (schema_call_formed Q e z \<longleftrightarrow> schema_call_formed P e z) \<and>
      ((e,z)\<in>positive_meaning Q \<longleftrightarrow> (e,z)\<in>positive_meaning P)"
    using native_related_test_package_completion[OF cf retained package callees] by blast
  have candidate: "native_package_at F u [] Q" using built(1) by (simp add: closed_native_package_at_def)
  have invariant: "presented_program_invariant presents Q d" by (rule profile_permission(1)[OF candidate built(5)])
  have completed: "(\<lambda>z. (d,z)\<in>positive_meaning Q)=
      saturate_observation presents (\<lambda>z. (test,z)\<in>positive_meaning P)"
    by (intro ext; simp only: built(7)[rule_format] compared saturate_observation_def)
  have accepted: "(264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
    if "program_entry_value_presents F u [] d p" for p
    using built(5) checker.on_presentations[OF reference_value refl, of "((F,(u,[])),d)" p] that by simp
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ Q], rule exI[of _ d])
    (use built(1-6,8) invariant completed accepted in blast)
qed

theorem candidate_total:
  assumes package: "native_package_at E pu pr P" and retained: "environment_included C E"
    and callees: "k\<in>system_definitions P" "test\<in>system_definitions P"
  shows "\<exists>F u Q d. closed_native_package_at F u [] Q \<and> native_package_environment F u []=F \<and>
    d\<notin>system_definitions P \<and> system_definitions Q=insert d (system_definitions P) \<and>
    presented_program_invariant presents Q d \<and>
    (\<forall>p. program_entry_value_presents F u [] d p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))) \<and>
    (\<forall>e\<in>system_definitions P. \<forall>z.
      (schema_call_formed Q e z \<longleftrightarrow> schema_call_formed P e z) \<and>
      ((e,z)\<in>positive_meaning Q \<longleftrightarrow> (e,z)\<in>positive_meaning P))"
  using candidate_completion[OF package retained callees] by blast

theorem inhabited_admission:
  "\<exists>F u Q d p. closed_native_package_at F u [] Q \<and> program_entry_value_presents F u [] d p \<and>
    presented_program_invariant presents Q d \<and>
    (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
proof -
  obtain F u Q d where built: "closed_native_package_at F u [] Q"
    "system_definitions Q=insert d (system_definitions R)" "presented_program_invariant presents Q d"
    "\<forall>p. program_entry_value_presents F u [] d p \<longrightarrow>
      (264,p)\<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
    using candidate_total[OF reference environment_included_refl entry entry] by blast
  have package: "native_package_at F u [] Q" using built(1) by (simp add: closed_native_package_at_def)
  have formed: "environment_formed F"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have root: "(u,[])\<in>environment_positions F"
    by (rule native_package_root_position[OF package])
  have member: "d\<in>system_definitions Q" using built(2) by simp
  have position: "d\<in>environment_positions F" by (rule native_package_entry_position[OF package member])
  obtain p where presented: "program_entry_value_presents F u [] d p"
    using program_entry_value_presents_total[OF formed root position] by blast
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ Q], rule exI[of _ d], rule exI[of _ p])
    (use built(1,3,4) presented in blast)
qed

end

text \<open>
  One complete finite profile is shared by every supplied presentation class.
  Its ordinary checker retains the actual candidate, its complete definition,
  both callees, and a common formed environment containing the fixed reference.
  The independently established comparison meaning entails invariance through
  the generic saturation contract.

  The reference's native syntax and actual site are fixed before future
  submissions. The subject relation and its semantic proof are mathematical
  conditions on that reference; they are not parameters installed as native
  truth callbacks. Every compatible pair of existing callees has a constructed
  admitted candidate preserving every old call boundary and positive meaning.
  Admission of this sufficient profile does not decide arbitrary original code.
\<close>

end
