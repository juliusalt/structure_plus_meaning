theory Factor_Discharge_Table_Reading
  imports Factor_Binding_Table_Reading
begin

section \<open>Complete premise links retain each required socket site\<close>

abbreviation discharge_rows_term where
  "discharge_rows_term qs \<equiv> keyed_rows_term (\<lambda>d. definition_site_value d) (\<lambda>d. definition_site_value d) qs"

abbreviation discharge_table_reading_result :: "factor_term\<Rightarrow>bool" where
  "discharge_table_reading_result z \<equiv> \<exists>E e u r qs Is Ks.
    z=term_quotation_argument e (use_data_term u) (Payload_Term r) (discharge_rows_term qs)
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)) \<and>
    environment_value_presents E e \<and> distinct qs \<and> distinct Is \<and> distinct Ks \<and>
    native_discharge_table_at E u r (set qs) (set Is) (set Ks)"

definition discharge_table_reading_system :: "(nat,nat,nat,nat) schema_system" where
  "discharge_table_reading_system=add_view_definition binding_table_reading_system 93 data_x {(0,table_reading_schema 91)}"

lemma discharge_table_reading_system_formed [simp]: "schema_system_formed discharge_table_reading_system"
  unfolding discharge_table_reading_system_def
  by (rule add_recursive_definition_formed[OF binding_table_reading_system_formed])
    (auto simp: table_reading_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma discharge_table_reading_definitions [simp]:
  "system_definitions discharge_table_reading_system=insert 93 (system_definitions binding_table_reading_system)"
  by (simp add: discharge_table_reading_system_def)

lemma discharge_table_reading_call:
  "schema_call_formed discharge_table_reading_system d t \<longleftrightarrow>
    d\<in>system_definitions discharge_table_reading_system \<and> term_formed t"
  using added_variable_calls[OF binding_table_reading_system_formed
    discharge_table_reading_system_formed[unfolded discharge_table_reading_system_def] binding_table_reading_call]
  by (simp only: discharge_table_reading_system_def[symmetric])

lemma discharge_table_reading_old_meaning:
  assumes "d\<in>system_definitions binding_table_reading_system"
  shows "(d,t)\<in>positive_meaning discharge_table_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning binding_table_reading_system"
  using added_definition_preserves_old(2)[OF binding_table_reading_system_formed
    discharge_table_reading_system_formed[unfolded discharge_table_reading_system_def], of d t] assms
  by (auto simp: discharge_table_reading_system_def)

lemma discharge_table_reading_clause [simp]:
  "((93,c),S)\<in>system_clauses discharge_table_reading_system \<longleftrightarrow> (c,S)\<in>{(0,table_reading_schema 91)}"
proof -
  have owned: "((d,c),S)\<in>system_clauses binding_table_reading_system \<Longrightarrow>
    d\<in>system_definitions binding_table_reading_system" for d c S
    using binding_table_reading_system_formed unfolding schema_system_formed_def by blast
  have absent: "((93,c),S)\<notin>system_clauses binding_table_reading_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: discharge_table_reading_system_def)
qed

lemma discharge_table_reading_base_meaning:
  assumes "d\<in>system_definitions admitted_instantiation_system"
  shows "(d,t)\<in>positive_meaning discharge_table_reading_system \<longleftrightarrow> (d,t)\<in>positive_meaning admitted_instantiation_system"
  using discharge_table_reading_old_meaning[of d t] binding_table_reading_base_meaning[OF assms, of t] assms by auto

lemma discharge_table_reading_components:
  "(37,t)\<in>positive_meaning discharge_table_reading_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
  "(32,t)\<in>positive_meaning discharge_table_reading_system \<longleftrightarrow> (32,t)\<in>positive_meaning family_admission_system"
  "(51,t)\<in>positive_meaning discharge_table_reading_system \<longleftrightarrow> (51,t)\<in>positive_meaning row_keys_system"
  "(59,t)\<in>positive_meaning discharge_table_reading_system \<longleftrightarrow> (59,t)\<in>positive_meaning row_values_system"
  "(21,t)\<in>positive_meaning discharge_table_reading_system \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
  "(46,t)\<in>positive_meaning discharge_table_reading_system \<longleftrightarrow> (46,t)\<in>positive_meaning data_append_system"
  "(6,t)\<in>positive_meaning discharge_table_reading_system \<longleftrightarrow> (6,t)\<in>positive_meaning bag_comparison_system"
  "(49,t)\<in>positive_meaning discharge_table_reading_system \<longleftrightarrow> (49,t)\<in>positive_meaning payload_disjoint_system"
  using discharge_table_reading_base_meaning[of 37 t] metadata_reading_components(1)[of t]
    discharge_table_reading_base_meaning[of 32 t] metadata_reading_components(2)[of t]
    discharge_table_reading_base_meaning[of 51 t] metadata_reading_components(12)[of t]
    discharge_table_reading_base_meaning[of 59 t] metadata_reading_components(13)[of t]
    discharge_table_reading_base_meaning[of 21 t] metadata_reading_components(11)[of t]
    discharge_table_reading_base_meaning[of 46 t] metadata_reading_components(7)[of t]
    discharge_table_reading_base_meaning[of 6 t] metadata_reading_components(8)[of t]
    discharge_table_reading_base_meaning[of 49 t] metadata_reading_components(10)[of t] by auto

lemma discharge_table_reading_rows:
  "(91,t)\<in>positive_meaning discharge_table_reading_system \<longleftrightarrow> boundary_rows_result site_link_reading_result t"
  using discharge_table_reading_old_meaning[of 91 t] binding_table_reading_old_meaning[of 91 t]
    site_link_vector_exact[of t] by auto

interpretation discharge_table_reading_profile: table_reading_profile discharge_table_reading_system 93 91 site_link_reading_result
  "(\<lambda>E u a q J A. native_site_link_at E u a (fst q) (snd q) J A)" "(\<lambda>d. definition_site_value d)" "(\<lambda>d. definition_site_value d)"
proof -
  have row: "site_link_reading_result (term_quotation_argument e u r q i k) \<longleftrightarrow>
      (\<exists>v a x Js As. u=use_data_term v \<and> r=Payload_Term a \<and>
        q=Pair_Term (definition_site_value (fst x)) ((\<lambda>d. definition_site_value d) (snd x)) \<and>
        i=data_list_term (map Payload_Term Js) \<and> k=data_list_term (map Payload_Term As) \<and>
        distinct Js \<and> distinct As \<and> native_site_link_at E v a (fst x) (snd x) (set Js) (set As))"
    if source: "environment_value_presents E e" for E e u r q i k
    using site_link_reading_at_source[OF source, of u r q i k]
    by (simp only: site_link_reading_exact split_paired_Ex fst_conv snd_conv)
  have unique: "q=z \<and> J=L \<and> A=B"
    if "native_site_link_at E u a (fst q) (snd q) J A" "native_site_link_at E u a (fst z) (snd z) L B"
    for E u a q J A z L B
    using native_site_link_unique[OF that] by (cases q; cases z) auto
  have finite: "finite J \<and> finite A" if "native_site_link_at E u a (fst q) (snd q) J A" for E u a q J A
    using native_site_link_properties[OF that] by blast
  show "table_reading_profile discharge_table_reading_system 93 91 site_link_reading_result
      (\<lambda>E u a q J A. native_site_link_at E u a (fst q) (snd q) J A) (\<lambda>d. definition_site_value d) (\<lambda>d. definition_site_value d)"
    by (rule table_reading_profile.intro)
      (fact discharge_table_reading_system_formed, fact discharge_table_reading_clause,
       simp add: discharge_table_reading_call, fact discharge_table_reading_rows,
       fact row, fact unique, fact finite, fact definition_site_value_injective,
       fact definition_site_value_injective, simp,
       fact discharge_table_reading_components(1), fact discharge_table_reading_components(2),
       fact discharge_table_reading_components(3), fact discharge_table_reading_components(4),
       fact discharge_table_reading_components(5), fact discharge_table_reading_components(6),
       fact discharge_table_reading_components(7), fact discharge_table_reading_components(8))
qed

theorem discharge_table_reading_exact:
  "(93,z)\<in>positive_meaning discharge_table_reading_system \<longleftrightarrow> discharge_table_reading_result z"
  by (rule discharge_table_reading_profile.exact)

theorem discharge_table_reading_complete:
  assumes source: "environment_value_presents E e" and order: "distinct qs" "distinct Is" "distinct Ks"
    and raw: "native_discharge_table_at E u r (set qs) (set Is) (set Ks)"
  shows "(93,term_quotation_argument e (use_data_term u) (Payload_Term r) (discharge_rows_term qs)
    (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning discharge_table_reading_system"
  by (rule discharge_table_reading_profile.complete[OF source raw order])

corollary discharge_table_reading_on_values:
  assumes source: "environment_value_presents E e"
  shows "(93,term_quotation_argument e (use_data_term u) (Payload_Term r) (discharge_rows_term qs)
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning discharge_table_reading_system \<longleftrightarrow>
    distinct qs \<and> distinct Is \<and> distinct Ks \<and> native_discharge_table_at E u r (set qs) (set Is) (set Ks)"
  by (rule discharge_table_reading_profile.on_values[OF source])

lemmas discharge_table_reading_at_source=discharge_table_reading_profile.at_source
lemmas discharge_table_reading_presentation_invariance=discharge_table_reading_profile.presentation_invariance
lemmas discharge_table_reading_orders=discharge_table_reading_profile.orders
lemmas discharge_table_reading_result_unique=discharge_table_reading_profile.result_unique
lemmas discharge_table_reading_empty=discharge_table_reading_profile.empty
lemmas discharge_table_reading_physical_key_unique=discharge_table_reading_profile.physical_key_unique

corollary discharge_table_reading_reject_repeated_keys:
  assumes source: "environment_value_presents E e" and repeated: "\<not> distinct (map fst qs)"
  shows "\<not> (93,term_quotation_argument e (use_data_term u) (Payload_Term r) (discharge_rows_term qs)
    (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning discharge_table_reading_system"
proof
  assume holds: "(93,term_quotation_argument e (use_data_term u) (Payload_Term r) (discharge_rows_term qs)
    (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))\<in>positive_meaning discharge_table_reading_system"
  have parts: "distinct qs \<and> distinct Is \<and> distinct Ks \<and>
      native_discharge_table_at E u r (set qs) (set Is) (set Ks)"
    using holds by (simp only: discharge_table_reading_on_values[OF source])
  have distinct: "distinct qs" and raw: "native_discharge_table_at E u r (set qs) (set Is) (set Ks)"
    using parts by blast+
  have functional: "single_valued (set qs)" by (rule native_discharge_table_properties(2)[OF raw])
  show False using distinct functional repeated by (simp add: distinct_keys_iff)
qed

text \<open>
  Every premise socket and supplied proof site is recovered from its actual
  link row. Shared proof targets remain possible, while repeated socket keys
  are rejected. This uses the same complete family and boundary proof as
  binding-table reading. The operation recovers structural metadata; the
  independent derivation checker determines which socket links are required.
\<close>

end
