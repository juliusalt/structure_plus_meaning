theory Factor_Proof_Reachability
  imports Factor_Proof_Inclusion
begin

section \<open>Proof edges follow actual environment references\<close>

lemma site_citation_use_path:
  assumes cite: "site_citation_at E u r d I K"
  shows "(u,fst d)\<in>(environment_edges E)\<^sup>*"
  using located_at_use_edge[OF site_citation_located[OF cite]] by auto

lemma native_site_link_target_path:
  assumes link: "native_site_link_at E u r d e I K"
  shows "(u,fst e)\<in>(environment_edges E)\<^sup>*"
proof -
  obtain b L B where cite: "site_citation_at E u b e L B"
    using link by (auto simp: native_site_link_at_def)
  show ?thesis by (rule site_citation_use_path[OF cite])
qed

lemma native_proof_node_target_path:
  assumes node: "native_proof_node_at E u r N D I K" and premise: "(s,m)\<in>D"
  shows "(u,fst m)\<in>(environment_edges E)\<^sup>*"
proof (cases rule: native_proof_node_at.cases[OF node, case_names assertion inference])
  case (assertion R)
  then show ?thesis using premise by simp
next
  case (inference R ps c b p d C A V B L D' J W)
  have table: "native_discharge_table_at E u p D' J W" and entry: "(s,m)\<in>D'"
    using inference premise by auto
  obtain a X Y where row: "native_site_link_at E u a s m X Y"
    using native_table_row_origin[OF table entry] by auto
  show ?thesis by (rule native_site_link_target_path[OF row])
qed

lemma native_graph_use_edge:
  assumes graph: "native_schema_graph_at E root G" and edge: "(m,n)\<in>schema_graph_edges G"
  shows "(fst n,fst m)\<in>(environment_edges E)\<^sup>*"
proof -
  have formed: "schema_graph_formed G root" using graph by (simp add: native_schema_graph_at_def)
  have inside: "n\<in>schema_graph_nodes G" by (rule schema_graph_edge_nodes(2)[OF formed edge])
  obtain N I K where node: "native_proof_node_at E (fst n) (snd n) N (schema_graph_premises G n) I K"
    using native_schema_graph_node[OF graph inside] by blast
  obtain s where premise: "(s,m)\<in>schema_graph_premises G n"
    using edge by (auto simp: schema_graph_edges_def schema_graph_premises_def)
  show ?thesis by (rule native_proof_node_target_path[OF node premise])
qed

lemma native_graph_use_path:
  assumes graph: "native_schema_graph_at E root G" and path: "(a,b)\<in>(schema_graph_edges G)\<^sup>*"
  shows "(fst b,fst a)\<in>(environment_edges E)\<^sup>*"
  using path
proof (induction rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have edge: "(fst z,fst y)\<in>(environment_edges E)\<^sup>*"
    by (rule native_graph_use_edge[OF graph step.hyps(2)])
  show ?case by (rule rtrancl_trans[OF edge step.IH])
qed

theorem native_graph_sources_reachable:
  assumes graph: "native_schema_graph_at E root G"
  shows "native_graph_sources G\<subseteq>environment_reachable E {fst root}"
proof
  fix u assume member: "u\<in>native_graph_sources G"
  obtain n where inside: "n\<in>schema_graph_nodes G" "u=fst n"
    using member by (auto simp: native_graph_sources_def)
  have path: "(n,root)\<in>(schema_graph_edges G)\<^sup>*"
    using graph inside(1) by (simp add: native_schema_graph_at_def schema_graph_formed_def)
  have actual: "(fst root,fst n)\<in>(environment_edges E)\<^sup>*"
    by (rule native_graph_use_path[OF graph path])
  show "u\<in>environment_reachable E {fst root}" using actual inside(2) by (simp add: environment_reachable_def)
qed

theorem native_proof_environment_closed_root:
  assumes graph: "native_schema_graph_at E root G"
  shows "environment_closed (native_proof_environment E G) {fst root}
    (native_graph_demands (native_proof_environment E G) G)"
proof -
  let ?F = "native_proof_environment E G"
  have boundary: "read_boundary_formed E (native_graph_sources G) (native_graph_demands E G)"
    by (rule native_graph_read_boundary[OF graph])
  have root: "root\<in>schema_graph_nodes G" using graph
    by (simp add: native_schema_graph_at_def schema_graph_formed_def)
  have roots: "{fst root}\<subseteq>native_graph_sources G"
    using root by (auto simp: native_graph_sources_def)
  have native: "native_schema_graph_at ?F root G" by (rule native_proof_environment_recovers[OF graph])
  have reach: "native_graph_sources G\<subseteq>environment_reachable ?F {fst root}"
    by (rule native_graph_sources_reachable[OF native])
  have closed: "environment_closed ?F {fst root} (native_graph_demands E G)"
    using read_environment_closed_from[OF boundary roots] reach
    by (simp add: native_proof_environment_def)
  show ?thesis using closed native_proof_environment_demands[OF graph] by simp
qed

text \<open>
  Each premise target is reached through its actual citation; a local target
  stays in the same use. Thus every proof source is reachable from the proof
  root's use. The grammar-derived proof retention environment is closed from
  that single root, including the exact passive targets of its references.
\<close>

end
