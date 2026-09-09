theory Factor_Data_Set_Comparison
  imports Factor_Data_List_Operations Factor_Recursive_Groups
begin

section \<open>Set comparison requires inclusion in both directions\<close>

definition data_set_comparison_schema :: "(nat,nat,nat) factor_schema" where
  "data_set_comparison_schema=data_rule (Pattern_Pair data_x data_y)
    {(0,47,Pattern_Pair data_x data_y),(1,47,Pattern_Pair data_y data_x)}"

definition data_set_comparison_group_system :: "(nat,nat,nat,nat) schema_system" where
  "data_set_comparison_group_system=\<lparr>
    system_interfaces={(219,data_x)}, system_clauses={((219,0),data_set_comparison_schema)}\<rparr>"

lemma data_set_comparison_group_definitions [simp]:
  "system_definitions data_set_comparison_group_system={219}"
  by (auto simp: data_set_comparison_group_system_def system_definitions_def rel_dom_def)

lemma data_set_comparison_group_interfaces [simp]:
  "(d,p)\<in>system_interfaces data_set_comparison_group_system \<longleftrightarrow> d=219 \<and> p=data_x"
  by (simp add: data_set_comparison_group_system_def)

lemma data_set_comparison_group_clauses [simp]:
  "((d,c),S)\<in>system_clauses data_set_comparison_group_system \<longleftrightarrow>
    d=219 \<and> c=0 \<and> S=data_set_comparison_schema"
  by (simp add: data_set_comparison_group_system_def)

lemma data_set_comparison_group_formed_over:
  "schema_system_formed_over {47} data_set_comparison_group_system"
  by (simp only: schema_system_formed_over_def data_set_comparison_group_definitions)
    (auto simp: data_set_comparison_group_system_def data_set_comparison_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma data_set_comparison_external_dependencies:
  "system_external_dependencies data_set_comparison_group_system={47}"
  by (simp only: system_external_dependencies_clauses data_set_comparison_group_definitions)
    (auto simp: data_set_comparison_group_system_def data_set_comparison_schema_def
      schema_dependencies_def rel_ran_image)

definition data_set_comparison_base_system :: "(nat,nat,nat,nat) schema_system" where
  "data_set_comparison_base_system=rooted_system data_subset_system
    (system_external_dependencies data_set_comparison_group_system)"

lemma data_set_comparison_base_formed [simp]: "schema_system_formed data_set_comparison_base_system"
  unfolding data_set_comparison_base_system_def by (rule rooted_system_formed[OF data_subset_system_formed])

lemma data_set_comparison_base_subdomain:
  "system_definitions data_set_comparison_base_system\<subseteq>system_definitions data_subset_system"
  unfolding data_set_comparison_base_system_def by (rule rooted_system_subdomain)

lemma data_set_comparison_base_roots:
  "{47}\<subseteq>system_definitions data_set_comparison_base_system"
  unfolding data_set_comparison_base_system_def data_set_comparison_external_dependencies
  by (rule rooted_system_roots[OF data_subset_system_formed]) auto

lemma data_set_comparison_base_least:
  assumes "{47}\<subseteq>U" "system_dependency_closed data_subset_system U"
  shows "system_definitions data_set_comparison_base_system\<subseteq>U"
  unfolding data_set_comparison_base_system_def data_set_comparison_external_dependencies
  by (rule rooted_system_least[OF data_subset_system_formed _ assms]) auto

lemma data_set_comparison_base_call:
  "schema_call_formed data_set_comparison_base_system d t \<longleftrightarrow>
    d\<in>system_definitions data_set_comparison_base_system \<and> term_formed t"
proof -
  have roots: "system_external_dependencies data_set_comparison_group_system\<subseteq>system_definitions data_subset_system"
    by (simp add: data_set_comparison_external_dependencies)
  have domain: "system_definitions data_set_comparison_base_system=
      system_definition_closure data_subset_system (system_external_dependencies data_set_comparison_group_system)"
    unfolding data_set_comparison_base_system_def by (rule rooted_system_definitions[OF data_subset_system_formed roots])
  have inside: "d\<in>system_definition_closure data_subset_system (system_external_dependencies data_set_comparison_group_system)
      \<Longrightarrow> d\<in>system_definitions data_subset_system"
    using data_set_comparison_base_subdomain by (simp only: domain; blast)
  show ?thesis
    by (simp only: data_set_comparison_base_system_def rooted_system_calls[OF data_subset_system_formed]
      data_subset_call domain[unfolded data_set_comparison_base_system_def]) (use inside in blast)
qed

interpretation data_set_comparison_group:
  positive_definition_group data_set_comparison_base_system data_set_comparison_group_system
proof (rule positive_definition_group.intro)
  show "schema_system_formed data_set_comparison_base_system" by simp
  show "schema_system_formed_over (system_definitions data_set_comparison_base_system) data_set_comparison_group_system"
    by (rule schema_system_formed_over_mono[OF data_set_comparison_group_formed_over data_set_comparison_base_roots])
  show "system_definitions data_set_comparison_base_system\<inter>system_definitions data_set_comparison_group_system={}"
    using data_set_comparison_base_subdomain by auto
qed

definition data_set_comparison_system :: "(nat,nat,nat,nat) schema_system" where
  "data_set_comparison_system=system_union data_set_comparison_base_system data_set_comparison_group_system"

lemma data_set_comparison_system_formed [simp]: "schema_system_formed data_set_comparison_system"
  using data_set_comparison_group.formed by (simp only: data_set_comparison_system_def)

lemma data_set_comparison_definitions [simp]:
  "system_definitions data_set_comparison_system=system_definitions data_set_comparison_base_system\<union>{219}"
  by (simp add: data_set_comparison_system_def)

lemma data_set_comparison_call:
  "schema_call_formed data_set_comparison_system d t \<longleftrightarrow>
    d\<in>system_definitions data_set_comparison_system \<and> term_formed t"
  unfolding data_set_comparison_system_def
  by (rule data_set_comparison_group.variable_calls[OF data_set_comparison_base_call]) auto

lemma data_set_comparison_clause:
  "((219,c),S)\<in>system_clauses data_set_comparison_system \<longleftrightarrow> c=0 \<and> S=data_set_comparison_schema"
  using data_set_comparison_group.no_old_clause[of 219 c S]
  by (simp add: data_set_comparison_system_def)

lemma data_set_comparison_subset_meaning:
  "(47,t)\<in>positive_meaning data_set_comparison_system \<longleftrightarrow>
    (47,t)\<in>positive_meaning data_subset_system"
proof -
  have member: "47\<in>system_definitions data_set_comparison_base_system"
    using data_set_comparison_base_roots by blast
  have closure: "47\<in>system_definition_closure data_subset_system
      (system_external_dependencies data_set_comparison_group_system)"
    using member by (auto simp: data_set_comparison_base_system_def rooted_system_def)
  show ?thesis using data_set_comparison_group.old_meaning[OF member, of t]
    rooted_system_meaning[OF data_subset_system_formed,
      where roots="system_external_dependencies data_set_comparison_group_system" and d=47 and t=t] closure
    by (simp only: data_set_comparison_system_def data_set_comparison_base_system_def; blast)
qed

lemma data_set_comparison_equation:
  "(219,t)\<in>positive_meaning data_set_comparison_system \<longleftrightarrow>
    (\<exists>p q. t=Pair_Term p q \<and>
      (47,Pair_Term p q)\<in>positive_meaning data_set_comparison_system \<and>
      (47,Pair_Term q p)\<in>positive_meaning data_set_comparison_system)"
proof -
  have valuation: "(219,t)\<in>positive_meaning data_set_comparison_system \<longleftrightarrow>
      (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> t=Pair_Term (h 0) (h 1) \<and>
        (47,Pair_Term (h 0) (h 1))\<in>positive_meaning data_set_comparison_system \<and>
        (47,Pair_Term (h 1) (h 0))\<in>positive_meaning data_set_comparison_system)"
    by (subst ordinary_positive_entry_valuation)
      (auto simp: data_set_comparison_clause data_set_comparison_schema_def
        schema_variables_def data_set_comparison_call)
  have formed: "term_formed p \<and> term_formed q"
    if "(47,Pair_Term p q)\<in>positive_meaning data_set_comparison_system" for p q
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by auto
  show ?thesis
  proof
    assume "(219,t)\<in>positive_meaning data_set_comparison_system"
    then show "\<exists>p q. t=Pair_Term p q \<and>
        (47,Pair_Term p q)\<in>positive_meaning data_set_comparison_system \<and>
        (47,Pair_Term q p)\<in>positive_meaning data_set_comparison_system"
      by (simp only: valuation; blast)
  next
    assume "\<exists>p q. t=Pair_Term p q \<and>
        (47,Pair_Term p q)\<in>positive_meaning data_set_comparison_system \<and>
        (47,Pair_Term q p)\<in>positive_meaning data_set_comparison_system"
    then obtain p q where parts: "t=Pair_Term p q"
      "(47,Pair_Term p q)\<in>positive_meaning data_set_comparison_system"
      "(47,Pair_Term q p)\<in>positive_meaning data_set_comparison_system" by blast
    show "(219,t)\<in>positive_meaning data_set_comparison_system"
      by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then p else q"])
        (use parts formed[OF parts(2)] in auto)
  qed
qed

theorem data_set_comparison_exact:
  "(219,t)\<in>positive_meaning data_set_comparison_system \<longleftrightarrow>
    (\<exists>xs ys. data_elements xs \<and> data_elements ys \<and> set xs=set ys \<and>
      t=Pair_Term (data_list_term xs) (data_list_term ys))"
  by (auto simp: data_set_comparison_equation data_set_comparison_subset_meaning
    data_subset_exact data_list_term_injective; blast)

corollary data_set_comparison_lists:
  "(219,Pair_Term (data_list_term xs) (data_list_term ys))\<in>positive_meaning data_set_comparison_system
    \<longleftrightarrow> data_elements xs \<and> data_elements ys \<and> set xs=set ys"
  by (auto simp: data_set_comparison_exact data_list_term_injective)

text \<open>
  One ordinary clause calls the existing complete inclusion operation in
  both directions, at two distinct premise sockets. Its sole external
  dependency and the least closed base are derived from that actual clause.
  The group retains the base's complete definitions and native meanings.

  The operands remain actual lists of formed self-contained terms. The
  relation compares their sets of elements, allowing differences in order
  and repetition. It neither deduplicates an operand nor asserts equality
  of the lists or of their counted occurrences.
\<close>

end
