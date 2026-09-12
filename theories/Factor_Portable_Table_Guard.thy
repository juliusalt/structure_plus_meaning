theory Factor_Portable_Table_Guard
  imports Factor_Requirement_Installation Factor_Keyed_Table_Comparison
begin

section \<open>A complete table comparison also requires self-contained values\<close>

definition portable_table_comparison ::
  "(factor_term\<times>factor_term) list \<Rightarrow> (factor_term\<times>factor_term) list \<Rightarrow> bool" where
  "portable_table_comparison xs ys \<longleftrightarrow>
    formed_key_rows xs \<and> formed_key_rows ys \<and>
    distinct (map fst xs) \<and> distinct (map fst ys) \<and>
    (\<forall>(k,v)\<in>set xs. self_contained_term v) \<and>
    (\<forall>(k,v)\<in>set ys. self_contained_term v) \<and> set xs=set ys"

lemma keyed_table_data_supported:
  "2\<in>system_definitions keyed_table_base_system"
proof -
  have root: "28\<in>system_definitions keyed_table_base_system"
    using keyed_table_base_roots by blast
  have clause: "((28,0),key_fibre_nil_schema)\<in>system_clauses keyed_table_base_system"
    using root by (auto simp: keyed_table_base_system_def rooted_system_def
      key_fibre_system_def key_fibre_clauses_def)
  have dependencies: "schema_dependencies key_fibre_nil_schema\<subseteq>system_definitions keyed_table_base_system"
    using keyed_table_base_formed clause by (auto simp: schema_system_formed_def)
  show ?thesis using dependencies
    by (auto simp: key_fibre_nil_schema_def schema_dependencies_def rel_ran_image)
qed

lemma keyed_table_data_meaning:
  "(2,t)\<in>positive_meaning keyed_table_comparison_system \<longleftrightarrow>
    term_formed t \<and> self_contained_term t"
  by (simp only: keyed_table_source_meaning[OF keyed_table_data_supported] key_fibre_data)

definition portable_table_requirements :: "(nat\<times>nat) set" where
  "portable_table_requirements={(0,2),(1,353)}"

interpretation portable_table_installation:
  requirement_guard_extension keyed_table_comparison_system 360 portable_table_requirements
  by (rule requirement_guard_extension.intro)
    (use keyed_table_base_subdomain keyed_table_data_supported in
      \<open>auto simp: portable_table_requirements_def single_valued_def rel_ran_def\<close>)

definition portable_table_system :: "(nat,nat,nat,nat) schema_system" where
  "portable_table_system=install_requirement_guard keyed_table_comparison_system 360 portable_table_requirements"

lemma portable_table_system_formed [simp]: "schema_system_formed portable_table_system"
  using portable_table_installation.guarded_formed by (simp only: portable_table_system_def)

lemma portable_table_gate:
  "(360,t)\<in>positive_meaning portable_table_system \<longleftrightarrow>
    self_contained_term t \<and> (353,t)\<in>positive_meaning keyed_table_comparison_system"
proof -
  have formed: "term_formed t" if "(353,t)\<in>positive_meaning keyed_table_comparison_system"
    using positive_meaning_formed[OF that] by (simp only: keyed_table_comparison_call)
  show ?thesis
    by (simp only: portable_table_system_def portable_table_installation.guarded_meaning)
      (use formed in \<open>auto simp: portable_table_requirements_def keyed_table_data_meaning\<close>)
qed

theorem portable_table_gate_on_rows:
  "(360,Pair_Term (pair_list_term xs) (pair_list_term ys))\<in>positive_meaning portable_table_system
    \<longleftrightarrow> portable_table_comparison xs ys"
  by (simp only: portable_table_gate keyed_table_comparison_lists)
    (auto simp: portable_table_comparison_def
      data_list_term_self_contained case_prod_unfold)

theorem portable_table_gate_exact:
  "(360,t)\<in>positive_meaning portable_table_system \<longleftrightarrow>
    (\<exists>xs ys. t=Pair_Term (pair_list_term xs) (pair_list_term ys) \<and> portable_table_comparison xs ys)"
  using keyed_table_comparison_shapes portable_table_gate portable_table_gate_on_rows by blast

theorem portable_table_guard_rejects_reference_values:
  assumes row: "(k,Target_Term target)\<in>set xs"
  shows "(360,Pair_Term (pair_list_term xs) (pair_list_term ys))\<notin>positive_meaning portable_table_system"
proof
  assume holds: "(360,Pair_Term (pair_list_term xs) (pair_list_term ys))\<in>positive_meaning portable_table_system"
  have closed_rows: "\<forall>(a,v)\<in>set xs. self_contained_term v"
    using holds by (simp only: portable_table_gate_on_rows portable_table_comparison_def; blast)
  have "(case (k,Target_Term target) of (a,v) \<Rightarrow> self_contained_term v)"
    by (rule bspec[OF closed_rows row])
  then show False by simp
qed

text \<open>
  The two predicates have distinct duties on the same complete table pair.
  Table identity permits arbitrary formed references in values. Self-contained
  data admission prevents those external targets from being silently omitted
  from a portable retained boundary. Both complete key domains, unique keys,
  every value, and independent table orders remain explicit.

  This is a gate for actual supplied tables. A client must still identify the
  complete required table domain and justify how its operations construct the
  compared tables. It is not a general development or publication verdict.
\<close>

end
