theory Factor_Site_Link_Vector
  imports Factor_Application_Vector
begin

section \<open>Every premise-link root retains both actual endpoint sites\<close>

abbreviation site_link_vector_result :: "factor_term\<Rightarrow>bool" where
  "site_link_vector_result z \<equiv> boundary_rows_result site_link_reading_result z"

definition site_link_vector_system :: "(nat,nat,nat,nat) schema_system" where
  "site_link_vector_system=add_view_definition application_vector_system 91 data_x (boundary_list_clauses 89 91)"

lemma site_link_vector_system_formed [simp]: "schema_system_formed site_link_vector_system"
  unfolding site_link_vector_system_def
  by (rule add_recursive_definition_formed[OF application_vector_system_formed])
    (auto simp: boundary_list_clauses_def boundary_list_nil_schema_def boundary_list_cons_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma site_link_vector_definitions [simp]:
  "system_definitions site_link_vector_system=insert 91 (system_definitions application_vector_system)"
  by (simp add: site_link_vector_system_def)

lemma site_link_vector_call:
  "schema_call_formed site_link_vector_system d t \<longleftrightarrow>
    d\<in>system_definitions site_link_vector_system \<and> term_formed t"
  using added_variable_calls[OF application_vector_system_formed
    site_link_vector_system_formed[unfolded site_link_vector_system_def] application_vector_call]
  by (simp only: site_link_vector_system_def[symmetric])

lemma site_link_vector_old_meaning:
  assumes "d\<in>system_definitions application_vector_system"
  shows "(d,t)\<in>positive_meaning site_link_vector_system \<longleftrightarrow> (d,t)\<in>positive_meaning application_vector_system"
  using added_definition_preserves_old(2)[OF application_vector_system_formed
    site_link_vector_system_formed[unfolded site_link_vector_system_def], of d t] assms
  by (auto simp: site_link_vector_system_def)

lemma site_link_vector_clause [simp]:
  "((91,c),S)\<in>system_clauses site_link_vector_system \<longleftrightarrow> (c,S)\<in>(boundary_list_clauses 89 91)"
proof -
  have owned: "((d,c),S)\<in>system_clauses application_vector_system \<Longrightarrow>
    d\<in>system_definitions application_vector_system" for d c S
    using application_vector_system_formed unfolding schema_system_formed_def by blast
  have absent: "((91,c),S)\<notin>system_clauses application_vector_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: site_link_vector_system_def)
qed

lemma site_link_vector_base_meaning:
  assumes "d\<in>system_definitions admitted_instantiation_system"
  shows "(d,t)\<in>positive_meaning site_link_vector_system \<longleftrightarrow> (d,t)\<in>positive_meaning admitted_instantiation_system"
  using site_link_vector_old_meaning[of d t] application_vector_base_meaning[OF assms, of t] assms by auto

lemma site_link_vector_element:
  "(89,t)\<in>positive_meaning site_link_vector_system \<longleftrightarrow> (89,t)\<in>positive_meaning site_link_reading_system"
  using site_link_vector_old_meaning[of 89 t] application_vector_old_meaning[of 89 t] by auto

lemma site_link_vector_components:
  "(46,t)\<in>positive_meaning site_link_vector_system \<longleftrightarrow> (46,t)\<in>positive_meaning data_append_system"
  "(6,t)\<in>positive_meaning site_link_vector_system \<longleftrightarrow> (6,t)\<in>positive_meaning bag_comparison_system"
  "(48,t)\<in>positive_meaning site_link_vector_system \<longleftrightarrow> (48,t)\<in>positive_meaning data_union_system"
  "(49,t)\<in>positive_meaning site_link_vector_system \<longleftrightarrow> (49,t)\<in>positive_meaning payload_disjoint_system"
  using site_link_vector_base_meaning[of 46 t] metadata_reading_components(7)[of t]
    site_link_vector_base_meaning[of 6 t] metadata_reading_components(8)[of t]
    site_link_vector_base_meaning[of 48 t] metadata_reading_components(9)[of t]
    site_link_vector_base_meaning[of 49 t] metadata_reading_components(10)[of t] by auto

interpretation site_link_vector_profile: boundary_list_profile site_link_vector_system 89 91
  by (rule boundary_list_profile.intro)
    (auto simp: site_link_vector_call site_link_vector_components site_link_vector_element site_link_reading_exact)

theorem site_link_vector_exact:
  "(91,z)\<in>positive_meaning site_link_vector_system \<longleftrightarrow> site_link_vector_result z"
  by (simp only: site_link_vector_profile.exact site_link_vector_element site_link_reading_exact)

corollary site_link_vector_empty:
  "(91,boundary_reading_argument ctx (Payload_Term []) (Payload_Term []) (Payload_Term []) (Payload_Term []))
    \<in>positive_meaning site_link_vector_system \<longleftrightarrow> term_formed ctx"
  by (rule site_link_vector_profile.empty)

corollary site_link_vector_presentation_invariance:
  assumes "environment_value_presents E e" "environment_value_presents E f"
  shows "(91,term_quotation_argument e u r q i k)\<in>positive_meaning site_link_vector_system \<longleftrightarrow>
    (91,term_quotation_argument f u r q i k)\<in>positive_meaning site_link_vector_system"
proof -
  have row: "site_link_reading_result (term_quotation_argument e u a b j l) \<longleftrightarrow>
    site_link_reading_result (term_quotation_argument f u a b j l)" for a b j l
    by (simp only: site_link_reading_exact[symmetric]) (rule site_link_reading_presentation_invariance[OF assms])
  have formed: "term_formed (Pair_Term e u) \<longleftrightarrow> term_formed (Pair_Term f u)"
    using environment_value_presents_formed[OF assms(1)] environment_value_presents_formed[OF assms(2)] by auto
  show ?thesis by (simp only: site_link_vector_exact)
    (rule boundary_rows_result_context_cong[where R=site_link_reading_result and S=site_link_reading_result
      and ctx="Pair_Term e u" and other="Pair_Term f u", OF formed row])
qed

text \<open>
  The same list clauses now call the two-endpoint link reader. Root and result
  order correspond exactly, while metadata enumeration remains independent.
  Distinct links may have a shared target or shared external slots. Their
  physical interiors remain separate. The enclosing table adds its complete
  family and decoded-key conditions.
\<close>

end
