theory Factor_Graph_Reindexing
  imports Factor_Graph_Renaming Indexed_Value_Images
begin

definition reindex_schema_graph ::
    "('n\<Rightarrow>('a,'c,'v) inference_node\<Rightarrow>('b,'e,'w) inference_node)\<Rightarrow>
      ('n\<Rightarrow>'s\<Rightarrow>'t)\<Rightarrow>('a,'s,'c,'n,'v) inference_graph\<Rightarrow>
      ('b,'t,'e,'n,'w) inference_graph" where
  "reindex_schema_graph K S G=\<lparr>
    graph_inferences=fimage (indexed_pair_map K) (graph_inferences G),
    graph_discharges=fimage (map_prod (indexed_pair_map S) id) (graph_discharges G)\<rparr>"

lemma schema_graph_reindexed_node:
  "(n,A)\<in>fset (graph_inferences (reindex_schema_graph K S G)) \<longleftrightarrow>
    (\<exists>B. (n,B)\<in>fset (graph_inferences G) \<and> A=K n B)"
  by (simp only: reindex_schema_graph_def inference_graph.select_convs fimage.rep_eq
    indexed_value_image_def[symmetric] indexed_value_image_member)

lemma schema_graph_reindexed_nodes:
  "schema_graph_nodes (reindex_schema_graph K S G)=schema_graph_nodes G"
  by (simp only: schema_graph_nodes_def reindex_schema_graph_def inference_graph.select_convs
    fimage.rep_eq indexed_value_image_def[symmetric] indexed_value_image_domain)

lemma schema_graph_reindexed_discharge:
  "((n,t),m)\<in>fset (graph_discharges (reindex_schema_graph K S G)) \<longleftrightarrow>
    (\<exists>s. ((n,s),m)\<in>fset (graph_discharges G) \<and> t=S n s)"
  by (simp only: reindex_schema_graph_def inference_graph.select_convs fimage.rep_eq
    key_image_member split_paired_Ex indexed_pair_map_pair prod.inject; blast)

lemma schema_graph_reindexed_edges:
  "schema_graph_edges (reindex_schema_graph K S G)=schema_graph_edges G"
  by (auto simp: schema_graph_edges_def schema_graph_reindexed_discharge)

lemma schema_graph_reindexed_premises:
  "schema_graph_premises (reindex_schema_graph K S G) n=map_prod (S n) id ` schema_graph_premises G n"
  by (auto simp: schema_graph_premises_def schema_graph_reindexed_discharge map_prod_def)

lemma schema_graph_reindexed_assertions:
  fixes S :: "'n\<Rightarrow>'s\<Rightarrow>'t"
    and G :: "('a,'s,'c,'n,'v) inference_graph"
  assumes kinds: "\<And>n A. (n,A)\<in>fset (graph_inferences G) \<Longrightarrow>
    K n A=Schema_Assertion \<longleftrightarrow> A=Schema_Assertion"
  shows "schema_assertion_uses (reindex_schema_graph K S G)=
    indexed_value_image (\<lambda>n ps. indexed_pair_map S ps) (schema_assertion_uses G)"
proof -
  have assertion: "(n,Schema_Assertion)\<in>fset (graph_inferences (reindex_schema_graph K S G)) \<longleftrightarrow>
      (n,Schema_Assertion)\<in>fset (graph_inferences G)" for n
    using kinds by (auto simp: schema_graph_reindexed_node eq_commute)
  have member: "(n,(p,t))\<in>schema_assertion_uses (reindex_schema_graph K S G) \<longleftrightarrow>
      (\<exists>s. (n,(p,s))\<in>schema_assertion_uses G \<and> t=S p s)" for n p t
    by (simp only: schema_assertion_use_member assertion schema_graph_reindexed_discharge; blast)
  show ?thesis
  proof (rule set_eqI)
    fix z :: "'n\<times>('n\<times>'t)"
    obtain n p t where shape: "z=(n,p,t)" by (cases z) auto
    show "z\<in>schema_assertion_uses (reindex_schema_graph K S G) \<longleftrightarrow>
      z\<in>indexed_value_image (\<lambda>n ps. indexed_pair_map S ps) (schema_assertion_uses G)"
      by (simp only: shape member indexed_value_image_member split_paired_Ex indexed_pair_map_pair prod.inject; blast)
  qed
qed

theorem reindexed_schema_graph_formed:
  assumes formed: "schema_graph_formed G root"
    and kinds: "\<And>n A. (n,A)\<in>fset (graph_inferences G) \<Longrightarrow>
      K n A=Schema_Assertion \<longleftrightarrow> A=Schema_Assertion"
    and sockets: "\<And>n. inj_on (S n) (rel_dom (schema_graph_premises G n))"
  shows "schema_graph_formed (reindex_schema_graph K S G) root"
proof -
  let ?H = "reindex_schema_graph K S G"
  have source_nodes: "single_valued (fset (graph_inferences G))"
    and source_edges: "single_valued (fset (graph_discharges G))"
    and source_assertions: "single_valued (schema_assertion_uses G)"
    using formed by (simp only: schema_graph_formed_def; blast)+
  have nodes: "single_valued (fset (graph_inferences ?H))"
    by (simp only: reindex_schema_graph_def inference_graph.select_convs fimage.rep_eq
      indexed_value_image_def[symmetric]; rule indexed_value_image_functional[OF source_nodes])
  have fibres: "{s. (n,s)\<in>rel_dom (fset (graph_discharges G))}=rel_dom (schema_graph_premises G n)" for n
    by (auto simp: rel_dom_def schema_graph_premises_def)
  have keys: "inj_on (indexed_pair_map S) (rel_dom (fset (graph_discharges G)))"
    by (rule indexed_pair_map_injective) (simp only: fibres; rule sockets)
  have edges: "single_valued (fset (graph_discharges ?H))"
    using single_valued_pair_image[OF source_edges keys, where g=id]
    by (simp only: reindex_schema_graph_def inference_graph.select_convs fimage.rep_eq map_prod_def)
  have assertions: "single_valued (schema_assertion_uses ?H)"
    by (simp only: schema_graph_reindexed_assertions[OF kinds];
      rule indexed_value_image_functional[OF source_assertions])
  show ?thesis using formed nodes edges assertions
    by (simp add: schema_graph_formed_def schema_graph_reindexed_nodes schema_graph_reindexed_edges)
qed

lemma schema_graph_reindexed_assumptions:
  assumes kinds: "\<And>n A. (n,A)\<in>fset (graph_inferences G) \<Longrightarrow>
    K n A=Schema_Assertion \<longleftrightarrow> A=Schema_Assertion"
  shows "schema_graph_assumptions (reindex_schema_graph K S G) J=schema_graph_assumptions G J"
  using kinds by (auto simp: schema_graph_assumptions_def schema_graph_reindexed_node eq_commute)

export_code reindex_schema_graph checking SML

text \<open>
  Metadata and premise socket values move in the context of their actual
  source node. Every node identity and every edge endpoint remains fixed.
  Assertion status is preserved on the original node rows, and socket maps
  need be injective only on each original outgoing premise domain.
\<close>

end
