theory Factor_Construction_Query
  imports Factor_Construction_Comparison Factor_Positive_Admission Factor_Environment_Inclusion_Contracts
begin

section \<open>Common rows survive each restriction and independent group\<close>

lemma construction_components_query_agreement:
  "systems_agree_on construction_components_system positive_query_system
    (system_definitions construction_components_system\<inter>system_definitions positive_query_system)"
proof -
  have overlap: "system_definitions construction_components_system\<inter>system_definitions positive_query_system=
      system_definitions row_values_system" by auto
  have query: "systems_agree_on row_values_system positive_query_system (system_definitions row_values_system)"
    by (rule whole_agreement_transitive[OF environment_inclusion_row_values_agreement positive_query_base_agreement])
  show ?thesis unfolding overlap
    by (rule systems_agree_on_transitive[OF systems_agree_on_sym[OF construction_components_row_agreement] query])
qed

lemma construction_admission_query_agreement:
  "systems_agree_on construction_admission_system positive_query_system
    (system_definitions construction_admission_system\<inter>system_definitions positive_query_system)"
proof -
  have base: "systems_agree_on construction_admission_base_system positive_query_system
      (system_definitions construction_admission_base_system\<inter>system_definitions positive_query_system)"
    unfolding construction_admission_base_system_def
    by (rule rooted_overlap_agreement[OF construction_components_query_agreement])
  have fresh: "system_definitions construction_admission_group_system\<inter>system_definitions positive_query_system={}"
    using positive_query_definition_bound by auto
  show ?thesis unfolding construction_admission_system_def
    by (rule construction_admission_group.extended_overlap_agreement[OF base fresh])
qed

lemma construction_comparison_query_agreement:
  "systems_agree_on construction_comparison_system positive_query_system
    (system_definitions construction_comparison_system\<inter>system_definitions positive_query_system)"
proof -
  have base: "systems_agree_on construction_comparison_base_system positive_query_system
      (system_definitions construction_comparison_base_system\<inter>system_definitions positive_query_system)"
    unfolding construction_comparison_base_system_def
    by (rule rooted_overlap_agreement[OF construction_admission_query_agreement])
  have fresh: "system_definitions construction_comparison_group_system\<inter>system_definitions positive_query_system={}"
    using positive_query_definition_bound by auto
  show ?thesis unfolding construction_comparison_system_def
    by (rule construction_comparison_group.extended_overlap_agreement[OF base fresh])
qed

definition construction_query_components :: "(nat,nat,nat,nat) schema_system" where
  "construction_query_components=system_union construction_comparison_system positive_query_system"

lemma construction_query_components_formed [simp]: "schema_system_formed construction_query_components"
  unfolding construction_query_components_def
  by (rule system_union_agree_formed[OF construction_comparison_system_formed positive_query_system_formed
    construction_comparison_query_agreement])

lemma construction_query_components_definitions [simp]:
  "system_definitions construction_query_components=
    system_definitions construction_comparison_system\<union>system_definitions positive_query_system"
  by (simp add: construction_query_components_def)

lemma construction_query_components_call:
  "schema_call_formed construction_query_components d z \<longleftrightarrow>
    d\<in>system_definitions construction_query_components \<and> term_formed z"
  using system_union_agree_call[OF construction_comparison_system_formed positive_query_system_formed
    construction_comparison_query_agreement, of d z]
  by (simp only: construction_query_components_def system_union_definitions
    construction_comparison_call positive_query_call Un_iff; blast)

lemma construction_query_component_meanings:
  "(261,z)\<in>positive_meaning construction_query_components \<longleftrightarrow>
    (261,z)\<in>positive_meaning construction_comparison_system"
  "(114,z)\<in>positive_meaning construction_query_components \<longleftrightarrow>
    (114,z)\<in>positive_meaning positive_query_system"
  using system_union_agree_left_locality(2)[OF construction_comparison_system_formed positive_query_system_formed
      construction_comparison_query_agreement, of 261 z]
    system_union_agree_right_locality(2)[OF construction_comparison_system_formed positive_query_system_formed
      construction_comparison_query_agreement, of 114 z]
  by (simp_all add: construction_query_components_def)

section \<open>The reference retains only the two entries' actual dependency closure\<close>

definition construction_query_system :: "(nat,nat,nat,nat) schema_system" where
  "construction_query_system=rooted_system construction_query_components {114,261}"

lemma construction_query_system_formed [simp]: "schema_system_formed construction_query_system"
  unfolding construction_query_system_def by (rule rooted_system_formed[OF construction_query_components_formed])

lemma construction_query_roots: "{114,261}\<subseteq>system_definitions construction_query_system"
  unfolding construction_query_system_def by (rule rooted_system_roots[OF construction_query_components_formed]) auto

lemma construction_query_least:
  assumes "{114,261}\<subseteq>U" "system_dependency_closed construction_query_components U"
  shows "system_definitions construction_query_system\<subseteq>U"
  unfolding construction_query_system_def
  by (rule rooted_system_least[OF construction_query_components_formed _ assms]) auto

lemma construction_query_definition_bound:
  "system_definitions construction_query_system\<subseteq>{..261}"
proof -
  have bound: "system_definitions construction_query_components\<subseteq>{..261}"
    using construction_comparison_definition_bound positive_query_definition_bound by auto
  show ?thesis unfolding construction_query_system_def by (rule subset_trans[OF rooted_system_subdomain bound])
qed

lemma construction_query_call:
  "schema_call_formed construction_query_system d z \<longleftrightarrow>
    d\<in>system_definitions construction_query_system \<and> term_formed z"
  unfolding construction_query_system_def
  by (rule rooted_system_variable_calls[OF construction_query_components_formed construction_query_components_call])

lemma construction_query_meaning:
  assumes "d\<in>{114,261}"
  shows "(d,z)\<in>positive_meaning construction_query_system \<longleftrightarrow>
    (d,z)\<in>positive_meaning construction_query_components"
proof -
  have member: "d\<in>system_definitions construction_query_system" using assms construction_query_roots by blast
  show ?thesis using rooted_system_meaning_at[OF construction_query_components_formed
      member[unfolded construction_query_system_def], of z]
    by (simp only: construction_query_system_def)
qed

theorem construction_query_exact:
  "(261,z)\<in>positive_meaning construction_query_system \<longleftrightarrow>
    (\<exists>p q. z=Pair_Term p q \<and> presentation_transport construction_account_presents construction_account_presents p q)"
  "(114,z)\<in>positive_meaning construction_query_system \<longleftrightarrow> positive_query_result z"
  by (simp_all add: construction_query_meaning construction_query_component_meanings
    construction_comparison_exact positive_query_exact)

theorem native_construction_query_reference:
  "\<exists>C :: local_address option artifact_environment. \<exists>cu R k query.
    closed_native_package_at C cu [] R \<and> native_package_environment C cu []=C \<and>
    k\<noteq>query \<and> {k,query}\<subseteq>system_definitions R \<and>
    (\<forall>d\<in>{k,query}. \<forall>z. schema_call_formed R d z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. (k,z)\<in>positive_meaning R \<longleftrightarrow>
      (\<exists>p q. z=Pair_Term p q \<and> presentation_transport construction_account_presents construction_account_presents p q)) \<and>
    (\<forall>z. (query,z)\<in>positive_meaning R \<longleftrightarrow> positive_query_result z)"
proof -
  obtain g :: "nat\<Rightarrow>local_address option definition_site"
    and C :: "local_address option artifact_environment" and cu R where compiled:
    "inj_on g (system_definitions construction_query_system)"
    "closed_native_package_at C cu [] R" "native_package_environment C cu []=C"
    "system_alpha_variant (rename_system g construction_query_system) R"
    "positive_meaning R=map_prod g id ` positive_meaning construction_query_system"
    using program_compilation_total[OF construction_query_system_formed]
    by (elim exE conjE) (rule that; assumption)
  have roots: "261\<in>system_definitions construction_query_system" "114\<in>system_definitions construction_query_system"
    using construction_query_roots by blast+
  have separate: "g 261\<noteq>g 114" using inj_onD[OF compiled(1) _ roots] by auto
  have members: "{g 261,g 114}\<subseteq>system_definitions R"
    using roots compiled(4) by (auto simp: system_alpha_variant_def renamed_system_definitions)
  have calls: "schema_call_formed R (g d) z \<longleftrightarrow> term_formed z"
    if "d\<in>{114,261}" for d z
  proof -
    have member: "d\<in>system_definitions construction_query_system" using that construction_query_roots by blast
    show ?thesis by (simp only: compiled_system_call_boundary[OF construction_query_system_formed
      compiled(1,4) member] construction_query_call; use member in simp)
  qed
  have comparison: "(g 261,z)\<in>positive_meaning R \<longleftrightarrow>
      (\<exists>p q. z=Pair_Term p q \<and> presentation_transport construction_account_presents construction_account_presents p q)" for z
    by (simp only: compiled_system_meaning_at[OF compiled(1) roots(1) compiled(5)] construction_query_exact)
  have query: "(g 114,z)\<in>positive_meaning R \<longleftrightarrow> positive_query_result z" for z
    by (simp only: compiled_system_meaning_at[OF compiled(1) roots(2) compiled(5)] construction_query_exact)
  show ?thesis by (rule exI[of _ C], rule exI[of _ cu], rule exI[of _ R],
      rule exI[of _ "g 261"], rule exI[of _ "g 114"])
    (use compiled(2,3) separate members calls comparison query in auto)
qed

text \<open>
  The complete account comparator and universal positive query share their
  actual common definitions. General overlap agreement passes through both
  least restrictions and both independent recursive groups. Union therefore
  preserves each complete program's meaning without duplicating its shared
  helper definitions. The final reference is the least closure of two entries.

  One native compilation fixes both sites before any future supplied test.
  A supplied test is complete ordinary program data for the query. Its own
  environment uses need not be compatible with the reference's private uses.
  No supplied truth predicate is installed as a native semantic operation.
\<close>

end
