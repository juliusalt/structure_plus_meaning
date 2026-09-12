theory Factor_Scheme_Claim_Values
  imports Factor_Scheme_Local_Readings Factor_Proof_Claim_Values Functional_Relation_Lists
begin

section \<open>Every supplied symbolic claim uses its actual node in one shared table\<close>

definition scheme_claim_values where
  "scheme_claim_values P G J xs hs \<longleftrightarrow>
    set xs\<subseteq>J \<and>
    (\<forall>n d p. (n,d,p)\<in>set xs \<longrightarrow> schema_pattern_call P d p) \<and>
    (\<forall>n q. (n,q)\<in>set xs \<longrightarrow> (\<exists>A. (n,A)\<in>fset (graph_inferences G) \<and>
      schema_scheme_local_reading P G J n A)) \<and>
    hs=filter (\<lambda>(n,q). (n,Schema_Assertion)\<in>fset (graph_inferences G)) xs"

lemma scheme_claim_values_nil [simp]:
  "scheme_claim_values P G J [] hs \<longleftrightarrow> hs=[]"
  by (simp add: scheme_claim_values_def)

lemma scheme_claim_values_cons:
  "scheme_claim_values P G J ((n,d,p)#xs) hs \<longleftrightarrow>
    (n,d,p)\<in>J \<and> schema_pattern_call P d p \<and>
    (\<exists>A. (n,A)\<in>fset (graph_inferences G) \<and> schema_scheme_local_reading P G J n A) \<and>
    (\<exists>ts. scheme_claim_values P G J xs ts \<and>
      hs=(if (n,Schema_Assertion)\<in>fset (graph_inferences G) then (n,d,p)#ts else ts))"
  by (auto simp: scheme_claim_values_def; blast)

lemma scheme_claim_values_assumptions:
  assumes "scheme_claim_values P G J xs hs"
  shows "set hs=schema_graph_assumptions G (set xs)"
  using assms by (auto simp: scheme_claim_values_def schema_graph_assumptions_def)

theorem scheme_claim_values_complete_table:
  assumes graph: "schema_graph_formed G root" and keys: "distinct (map fst xs)"
    and domain: "rel_dom (set xs)=schema_graph_nodes G" and root: "(root,d,p)\<in>set xs"
  shows "scheme_claim_values P G (set xs) xs hs \<longleftrightarrow>
    schema_scheme_reading P G root d p (set xs) \<and>
      hs=filter (\<lambda>(n,q). (n,Schema_Assertion)\<in>fset (graph_inferences G)) xs"
proof -
  have nsv: "single_valued (fset (graph_inferences G))" using graph by (simp add: schema_graph_formed_def)
  have jsv: "single_valued (set xs)" using keys by (simp only: distinct_keys_iff; blast)
  have common: "rel_dom (set xs)=rel_dom (fset (graph_inferences G))"
    by (simp only: domain schema_graph_nodes_def)
  have all_nodes: "(\<forall>n q. (n,q)\<in>set xs \<longrightarrow> (\<exists>A. (n,A)\<in>fset (graph_inferences G) \<and>
      schema_scheme_local_reading P G (set xs) n A)) \<longleftrightarrow>
      (\<forall>n A. (n,A)\<in>fset (graph_inferences G) \<longrightarrow> schema_scheme_local_reading P G (set xs) n A)"
    by (rule functional_relations_all_values[OF nsv jsv common,
      where R="\<lambda>n A q. schema_scheme_local_reading P G (set xs) n A"])
  have system: "schema_system_formed P"
    if calls: "\<forall>n e q. (n,e,q)\<in>set xs \<longrightarrow> schema_pattern_call P e q"
    using calls root by (auto simp: schema_pattern_call_def)
  show ?thesis
    by (simp only: scheme_claim_values_def schema_scheme_reading_by_local_specializations all_nodes)
      (use graph jsv domain root system in blast)
qed

theorem scheme_claim_assumption_order:
  assumes read: "schema_scheme_reading P G root d p J" and order: "distinct hs"
    and boundary: "set hs=schema_graph_assumptions G J"
  obtains xs where "set xs=J" "distinct (map fst xs)" "scheme_claim_values P G J xs hs"
proof -
  have finite: "finite J" by (rule schema_scheme_reading_finite[OF read])
  have functional: "single_valued J" using read by (simp add: schema_scheme_reading_def)
  have exact: "set hs={z\<in>J. (fst z,Schema_Assertion)\<in>fset (graph_inferences G)}"
    using boundary by (auto simp: schema_graph_assumptions_def)
  obtain xs where rows: "set xs=J" "distinct (map fst xs)"
    "filter (\<lambda>z. (fst z,Schema_Assertion)\<in>fset (graph_inferences G)) xs=hs"
    by (rule functional_filter_order[OF finite functional order exact]) (rule that; assumption)
  have graph: "schema_graph_formed G root" and domain: "rel_dom (set xs)=schema_graph_nodes G"
    and root_row: "(root,d,p)\<in>set xs"
    using read rows(1) by (auto simp: schema_scheme_reading_def)
  have checked: "scheme_claim_values P G J xs hs"
    using scheme_claim_values_complete_table[OF graph rows(2) domain root_row] read rows
    by (simp add: case_prod_unfold)
  show thesis by (rule that[OF rows(1,2) checked])
qed

text \<open>
  Whole graph formation, the full claim domain and one occurrence per key are
  independent prerequisites of the complete-table equivalence. Every claim
  must be a formed symbolic call, including claims at assertion nodes. Local
  inference checks do not imply those unrelated call conditions.

  The output retains assertion occurrences by their actual node sites. Every
  distinct enumeration of that identified boundary extends to a complete claim
  enumeration. The shared functional-filter theorem supplies the same order
  argument to the existing ground proof family. These mathematical contracts
  do not yet provide a native whole-graph symbolic traversal.
\<close>

end
