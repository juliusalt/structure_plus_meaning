theory Factor_Graph_Positioning
  imports Factor_Graph_Reindexing Factor_Positioned_Instances
begin

fun positioned_schema_graph_node :: "'u\<Rightarrow>(local_address,local_address) schema_graph_node\<Rightarrow>
    ('u definition_site,'u definition_site) schema_graph_node" where
  "positioned_schema_graph_node u Schema_Assertion=Schema_Assertion"
| "positioned_schema_graph_node u (Schema_Inference c V)=
    Schema_Inference (u,c) (fimage (map_prod (Pair u) id) V)"

lemma positioned_schema_graph_node_assertion:
  "positioned_schema_graph_node u A=Schema_Assertion \<longleftrightarrow> A=Schema_Assertion"
  by (cases A) simp_all

definition positioned_schema_graph :: "('n\<Rightarrow>'u)\<Rightarrow>
    (local_address,local_address,local_address,'n) schema_derivation_graph\<Rightarrow>
    ('u definition_site,'u definition_site,'u definition_site,'n) schema_derivation_graph" where
  "positioned_schema_graph owner G=reindex_schema_graph
    (\<lambda>n. positioned_schema_graph_node (owner n)) (\<lambda>n. Pair (owner n)) G"

lemma positioned_schema_graph_nodes:
  "schema_graph_nodes (positioned_schema_graph owner G)=schema_graph_nodes G"
  by (simp only: positioned_schema_graph_def schema_graph_reindexed_nodes)

lemma positioned_schema_graph_premises:
  "schema_graph_premises (positioned_schema_graph owner G) n=
    map_prod (Pair (owner n)) id ` schema_graph_premises G n"
  by (simp only: positioned_schema_graph_def schema_graph_reindexed_premises)

theorem positioned_schema_graph_formed:
  assumes formed: "schema_graph_formed G root"
  shows "schema_graph_formed (positioned_schema_graph owner G) root"
proof -
  show ?thesis unfolding positioned_schema_graph_def
    by (rule reindexed_schema_graph_formed[OF formed])
      (simp_all add: positioned_schema_graph_node_assertion inj_on_def)
qed

lemma positioned_schema_graph_assumptions:
  "schema_graph_assumptions (positioned_schema_graph owner G) J=schema_graph_assumptions G J"
  unfolding positioned_schema_graph_def
  by (rule schema_graph_reindexed_assumptions) (rule positioned_schema_graph_node_assertion)

lemma positioned_checks_schema_graph_node:
  assumes formed: "schema_system_formed P"
    and checked: "checks_schema_graph_node P G J n A"
    and owner: "owner n=fst (fst (rel_value J n))"
  shows "checks_schema_graph_node (positioned_program P) (positioned_schema_graph owner G) J n
    (positioned_schema_graph_node (owner n) A)"
proof (cases A)
  case Schema_Assertion
  then show ?thesis using checked
    by (simp add: positioned_schema_graph_premises positioned_program_calls[OF formed])
next
  case (Schema_Inference c V)
  let ?u = "owner n"
  obtain Q where inst: "admitted_schema_instance P (fst (rel_value J n)) c (fset V) (snd (rel_value J n)) Q"
    and domain: "rel_dom (schema_graph_premises G n)=rel_dom Q"
    and children: "\<forall>s m. (s,m)\<in>schema_graph_premises G n \<longrightarrow> (m,rel_value Q s)\<in>J"
    using checked Schema_Inference by auto
  let ?Q = "map_socket_graph (Pair ?u) id id Q"
  have copied: "admitted_schema_instance (positioned_program P) (fst (rel_value J n)) (?u,c)
    (fset (fimage (map_prod (Pair ?u) id) V)) (snd (rel_value J n)) ?Q"
    using positioned_admitted_instanceI[OF formed inst]
    by (simp add: owner rename_term_bindings_def fimage.rep_eq map_prod_def)
  have copied_domain: "rel_dom (schema_graph_premises (positioned_schema_graph owner G) n)=rel_dom ?Q"
    by (simp only: positioned_schema_graph_premises map_socket_graph_domain map_prod_def pair_image_domain
      domain id_def)
  have functional: "single_valued Q" using admitted_instance_formed[OF inst] by blast
  have injective: "inj_on (Pair ?u) (rel_dom Q)" by (auto simp: inj_on_def)
  have copied_children:
    "\<forall>s m. (s,m)\<in>schema_graph_premises (positioned_schema_graph owner G) n \<longrightarrow>
      (m,rel_value ?Q s)\<in>J"
  proof (intro allI impI)
    fix s m
    assume edge: "(s,m)\<in>schema_graph_premises (positioned_schema_graph owner G) n"
    obtain k where original: "(k,m)\<in>schema_graph_premises G n" and site: "s=(?u,k)"
      using edge by (simp only: positioned_schema_graph_premises key_image_member; blast)
    have key: "k\<in>rel_dom Q" using rel_domI[OF original] by (simp only: domain)
    have transported_value: "rel_value ?Q (?u,k)=rel_value Q k"
      by (simp only: map_socket_graph_keys; rule rel_value_key_image[OF functional injective key])
    show "(m,rel_value ?Q s)\<in>J" using children original by (simp only: site transported_value; blast)
  qed
  show ?thesis using copied copied_domain copied_children
    by (simp only: Schema_Inference positioned_schema_graph_node.simps checks_schema_graph_node.simps; blast)
qed

theorem positioned_schema_graph_reading:
  assumes formed: "schema_system_formed P"
    and read: "schema_graph_reading P G root d t J"
    and owners: "\<And>n. n\<in>schema_graph_nodes G \<Longrightarrow> owner n=fst (fst (rel_value J n))"
  shows "schema_graph_reading (positioned_program P) (positioned_schema_graph owner G) root d t J"
proof -
  have graph: "schema_graph_formed G root" using read by (simp only: schema_graph_reading_def; blast)
  have copied_graph: "schema_graph_formed (positioned_schema_graph owner G) root"
    by (rule positioned_schema_graph_formed[OF graph])
  have checked:
    "checks_schema_graph_node (positioned_program P) (positioned_schema_graph owner G) J n B"
    if row: "(n,B)\<in>fset (graph_inferences (positioned_schema_graph owner G))" for n B
  proof -
    obtain A where original: "(n,A)\<in>fset (graph_inferences G)"
      and kind: "B=positioned_schema_graph_node (owner n) A"
      using row by (simp only: positioned_schema_graph_def schema_graph_reindexed_node; blast)
    have inside: "n\<in>schema_graph_nodes G" using rel_domI[OF original]
      by (simp only: schema_graph_nodes_def)
    have node: "checks_schema_graph_node P G J n A"
      using read original by (simp only: schema_graph_reading_def; blast)
    show ?thesis by (simp only: kind;
      rule positioned_checks_schema_graph_node[where owner=owner, OF formed node owners[OF inside]])
  qed
  show ?thesis using read copied_graph checked
    by (simp only: schema_graph_reading_def positioned_schema_graph_nodes; blast)
qed

text \<open>
  Each original clause, binder and premise socket is paired with the owning
  definition use from that node's actual claim. The complete claim assignment,
  node identities, terms, callees and edge endpoints remain fixed. The existing
  exact positioned-instance theorem supplies every transformed inference.
\<close>

end
