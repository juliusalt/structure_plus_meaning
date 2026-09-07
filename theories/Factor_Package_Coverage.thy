theory Factor_Package_Coverage
  imports Factor_Package_Slot_Reading
begin

section \<open>The package grammar accounts for every stored row\<close>

lemma native_package_closed_fixed_iff:
  assumes package: "native_package_at E u r P"
  shows "environment_closed E {u} (native_package_demands E u r) \<longleftrightarrow>
    native_package_environment E u r=E"
proof
  assume closed: "environment_closed E {u} (native_package_demands E u r)"
  have raw: "closed_native_package_at E u r P"
    using package closed by (simp add: closed_native_package_at_def)
  show "native_package_environment E u r=E"
    by (rule native_package_closed_environment_fixed[OF raw])
next
  assume same: "native_package_environment E u r=E"
  show "environment_closed E {u} (native_package_demands E u r)"
    using native_package_environment_closed[OF package] by (simp only: same)
qed

lemma native_package_closed_coverage:
  assumes package: "native_package_at E u r P"
  shows "environment_closed E {u} (native_package_demands E u r) \<longleftrightarrow>
    rel_dom (environment_bindings E)\<subseteq>native_package_demands E u r \<and>
    environment_uses E\<subseteq>native_package_sources E u r\<union>rel_ran (environment_bindings E)"
  by (simp only: native_package_closed_fixed_iff[OF package] native_package_environment_def
    read_environment_fixed_coverage)

abbreviation package_source_list_result :: "factor_term \<Rightarrow> bool" where
  "package_source_list_result z \<equiv> \<exists>c xs. z=Pair_Term c (data_list_term xs) \<and> term_formed c \<and>
    (\<forall>x\<in>set xs. package_source_reading_result (Pair_Term c x))"

definition package_source_list_system :: "(nat,nat,nat,nat) schema_system" where
  "package_source_list_system=add_view_definition package_slot_reading_system 120 data_x (context_list_clauses 118 120)"

lemma package_source_list_system_formed [simp]: "schema_system_formed package_source_list_system"
  unfolding package_source_list_system_def
  by (rule add_recursive_definition_formed[OF package_slot_reading_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma package_source_list_definitions [simp]:
  "system_definitions package_source_list_system=insert 120 (system_definitions package_slot_reading_system)"
  by (simp add: package_source_list_system_def)

lemma package_source_list_call:
  "schema_call_formed package_source_list_system d t \<longleftrightarrow>
    d\<in>system_definitions package_source_list_system \<and> term_formed t"
  using added_variable_calls[OF package_slot_reading_system_formed
    package_source_list_system_formed[unfolded package_source_list_system_def] package_slot_reading_call]
  by (simp only: package_source_list_system_def[symmetric])

lemma package_source_list_old_meaning:
  assumes "d\<in>system_definitions package_slot_reading_system"
  shows "(d,t)\<in>positive_meaning package_source_list_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning package_slot_reading_system"
  using added_definition_preserves_old(2)[OF package_slot_reading_system_formed
    package_source_list_system_formed[unfolded package_source_list_system_def], of d t] assms
  by (auto simp: package_source_list_system_def)

lemma package_source_list_clause [simp]:
  "((120,c),S)\<in>system_clauses package_source_list_system \<longleftrightarrow> (c,S)\<in>(context_list_clauses 118 120)"
proof -
  have owned: "((d,c),S)\<in>system_clauses package_slot_reading_system \<Longrightarrow>
    d\<in>system_definitions package_slot_reading_system" for d c S
    using package_slot_reading_system_formed unfolding schema_system_formed_def by blast
  have absent: "((120,c),S)\<notin>system_clauses package_slot_reading_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: package_source_list_system_def)
qed

lemma package_source_list_element:
  "(118,t)\<in>positive_meaning package_source_list_system \<longleftrightarrow>
    (118,t)\<in>positive_meaning package_source_reading_system"
  using package_source_list_old_meaning[of 118 t] package_slot_reading_old_meaning[of 118 t] by auto

interpretation package_source_list_profile: context_list_profile package_source_list_system 118 120
  by (rule context_list_profile.intro) (auto simp: package_source_list_call)

theorem package_source_list_exact:
  "(120,z)\<in>positive_meaning package_source_list_system \<longleftrightarrow> package_source_list_result z"
  by (simp only: package_source_list_profile.exact package_source_list_element package_source_reading_exact)

corollary package_source_list_at_read:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
  shows "(120,Pair_Term (package_context_term e (use_data_term pu) (Payload_Term pr)) (data_list_term xs))
      \<in>positive_meaning package_source_list_system \<longleftrightarrow>
    (\<forall>x\<in>set xs. \<exists>v. x=use_data_term v \<and>
      v\<in>native_package_sources E pu pr\<union>rel_ran (environment_bindings E))"
  by (simp only: package_source_list_profile.lists package_source_list_element
    package_source_reading_at_read[OF source package] package_context_formed[OF source package]; simp)

abbreviation package_slot_list_result :: "factor_term \<Rightarrow> bool" where
  "package_slot_list_result z \<equiv> \<exists>c xs. z=Pair_Term c (data_list_term xs) \<and> term_formed c \<and>
    (\<forall>x\<in>set xs. package_slot_reading_result (Pair_Term c x))"

definition package_slot_list_system :: "(nat,nat,nat,nat) schema_system" where
  "package_slot_list_system=add_view_definition package_source_list_system 121 data_x (context_list_clauses 119 121)"

lemma package_slot_list_system_formed [simp]: "schema_system_formed package_slot_list_system"
  unfolding package_slot_list_system_def
  by (rule add_recursive_definition_formed[OF package_source_list_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma package_slot_list_definitions [simp]:
  "system_definitions package_slot_list_system=insert 121 (system_definitions package_source_list_system)"
  by (simp add: package_slot_list_system_def)

lemma package_slot_list_call:
  "schema_call_formed package_slot_list_system d t \<longleftrightarrow>
    d\<in>system_definitions package_slot_list_system \<and> term_formed t"
  using added_variable_calls[OF package_source_list_system_formed
    package_slot_list_system_formed[unfolded package_slot_list_system_def] package_source_list_call]
  by (simp only: package_slot_list_system_def[symmetric])

lemma package_slot_list_old_meaning:
  assumes "d\<in>system_definitions package_source_list_system"
  shows "(d,t)\<in>positive_meaning package_slot_list_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning package_source_list_system"
  using added_definition_preserves_old(2)[OF package_source_list_system_formed
    package_slot_list_system_formed[unfolded package_slot_list_system_def], of d t] assms
  by (auto simp: package_slot_list_system_def)

lemma package_slot_list_clause [simp]:
  "((121,c),S)\<in>system_clauses package_slot_list_system \<longleftrightarrow> (c,S)\<in>(context_list_clauses 119 121)"
proof -
  have owned: "((d,c),S)\<in>system_clauses package_source_list_system \<Longrightarrow>
    d\<in>system_definitions package_source_list_system" for d c S
    using package_source_list_system_formed unfolding schema_system_formed_def by blast
  have absent: "((121,c),S)\<notin>system_clauses package_source_list_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: package_slot_list_system_def)
qed

lemma package_slot_list_element:
  "(119,t)\<in>positive_meaning package_slot_list_system \<longleftrightarrow>
    (119,t)\<in>positive_meaning package_slot_reading_system"
  using package_slot_list_old_meaning[of 119 t] package_source_list_old_meaning[of 119 t] by auto

interpretation package_slot_list_profile: context_list_profile package_slot_list_system 119 121
  by (rule context_list_profile.intro) (auto simp: package_slot_list_call)

theorem package_slot_list_exact:
  "(121,z)\<in>positive_meaning package_slot_list_system \<longleftrightarrow> package_slot_list_result z"
  by (simp only: package_slot_list_profile.exact package_slot_list_element package_slot_reading_exact)

corollary package_slot_list_at_read:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
  shows "(121,Pair_Term (package_context_term e (use_data_term pu) (Payload_Term pr)) (data_list_term xs))
      \<in>positive_meaning package_slot_list_system \<longleftrightarrow>
    (\<forall>x\<in>set xs. \<exists>u k. x=Pair_Term (use_data_term u) (Payload_Term k) \<and>
      (u,k)\<in>native_package_demands E pu pr)"
  by (simp only: package_slot_list_profile.lists package_slot_list_element
    package_slot_reading_at_read[OF source package] package_context_formed[OF source package]; simp)

lemma package_lists_previous_meaning:
  assumes "d\<in>system_definitions package_slot_reading_system"
  shows "(d,t)\<in>positive_meaning package_slot_list_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning package_slot_reading_system"
  using package_slot_list_old_meaning[of d t] package_source_list_old_meaning[OF assms, of t] assms by auto

lemma package_stored_coverage:
  assumes source: "environment_value_presents E (Pair_Term a b)" and package: "native_package_at E pu pr P"
    and artifact_keys: "(51,Pair_Term a us)\<in>positive_meaning row_keys_system"
    and binding_keys: "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
  shows "((120,Pair_Term (package_context_term (Pair_Term a b) (use_data_term pu) (Payload_Term pr)) us)
      \<in>positive_meaning package_source_list_system \<and>
    (121,Pair_Term (package_context_term (Pair_Term a b) (use_data_term pu) (Payload_Term pr)) ks)
      \<in>positive_meaning package_slot_list_system) \<longleftrightarrow>
    environment_closed E {pu} (native_package_demands E pu pr)"
proof -
  obtain xs where uses: "us=data_list_term xs" "set xs=image use_data_term (environment_uses E)"
    using environment_artifact_keys[OF source artifact_keys] by blast
  obtain ys where slots: "ks=data_list_term ys" "set ys=image definition_site_value (rel_dom (environment_bindings E))"
    using environment_binding_keys[OF source binding_keys] by blast
  show ?thesis
    by (simp only: uses(1) slots(1) package_source_list_at_read[OF source package]
      package_slot_list_at_read[OF source package] native_package_closed_coverage[OF package] uses(2) slots(2))
      (auto simp: site_data_term_def inj_eq[OF use_data_term_injective] subset_iff)
qed

corollary package_source_list_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(120,Pair_Term (package_context_term e pu pr) xs)\<in>positive_meaning package_source_list_system \<longleftrightarrow>
    (120,Pair_Term (package_context_term f pu pr) xs)\<in>positive_meaning package_source_list_system"
proof -
  have lists: "(120,Pair_Term c xs)\<in>positive_meaning package_source_list_system \<longleftrightarrow>
    (\<exists>ys. xs=data_list_term ys \<and> term_formed c \<and>
      (\<forall>x\<in>set ys. (118,Pair_Term c x)\<in>positive_meaning package_source_reading_system))" for c
    by (simp only: package_source_list_profile.exact factor_term.inject package_source_list_element; blast)
  have formed: "term_formed (package_context_term e pu pr) \<longleftrightarrow> term_formed (package_context_term f pu pr)"
    using environment_value_presents_formed[OF assms(1)] environment_value_presents_formed[OF assms(2)] by auto
  show ?thesis by (simp only: lists formed package_source_reading_presentation_invariance[OF assms])
qed

corollary package_slot_list_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(121,Pair_Term (package_context_term e pu pr) xs)\<in>positive_meaning package_slot_list_system \<longleftrightarrow>
    (121,Pair_Term (package_context_term f pu pr) xs)\<in>positive_meaning package_slot_list_system"
proof -
  have lists: "(121,Pair_Term c xs)\<in>positive_meaning package_slot_list_system \<longleftrightarrow>
    (\<exists>ys. xs=data_list_term ys \<and> term_formed c \<and>
      (\<forall>x\<in>set ys. (119,Pair_Term c x)\<in>positive_meaning package_slot_reading_system))" for c
    by (simp only: package_slot_list_profile.exact factor_term.inject package_slot_list_element; blast)
  have formed: "term_formed (package_context_term e pu pr) \<longleftrightarrow> term_formed (package_context_term f pu pr)"
    using environment_value_presents_formed[OF assms(1)] environment_value_presents_formed[OF assms(2)] by auto
  show ?thesis by (simp only: lists formed package_slot_reading_presentation_invariance[OF assms])
qed

text \<open>
  The same two generic list profiles inspect every supplied key and the final
  boundary. Projecting keys from the actual complete environment lists makes
  coverage equivalent to the existing closed package environment and to
  equality with the grammar's canonical restriction.

  Whole artifact values are retained. An extra occurrence inside a needed
  artifact is not an extra environment use. Every stored binding, including
  bindings whose target value is otherwise needed, must itself be read.
  No truth, application, or proof-graph premise enters this characterization.
\<close>

end
