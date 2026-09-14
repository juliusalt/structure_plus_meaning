theory Factor_Graph_Mappings
  imports Factor_Graph_Renaming
begin

definition schema_graph_mapping where
  "schema_graph_mapping M G root H r=(single_valued M \<and>
    rel_dom M=schema_graph_nodes G \<and> (root,r)\<in>M \<and>
    fset (graph_inferences H)={(m,N). \<exists>n. (n,N)\<in>fset (graph_inferences G) \<and> (n,m)\<in>M} \<and>
    fset (graph_discharges H)={((m,s),k). \<exists>n q.
      ((n,s),q)\<in>fset (graph_discharges G) \<and> (n,m)\<in>M \<and> (q,k)\<in>M})"

theorem schema_graph_mapping_rename:
  assumes formed: "schema_graph_formed G root"
  shows "schema_graph_mapping (graph_map (schema_graph_nodes G) h) G root
    (rename_schema_graph h G) (h root)"
proof -
  have root: "root\<in>schema_graph_nodes G"
    using formed by (simp only: schema_graph_formed_def; blast)
  have node: "n\<in>schema_graph_nodes G" if "(n,N)\<in>fset (graph_inferences G)" for n N
    using that by (auto simp: schema_graph_nodes_def rel_dom_def)
  have endpoints: "n\<in>schema_graph_nodes G \<and> q\<in>schema_graph_nodes G"
    if "((n,s),q)\<in>fset (graph_discharges G)" for n s q
    using schema_graph_discharge_nodes[OF formed that] by blast
  show ?thesis
    using root node endpoints
    by (auto simp: schema_graph_mapping_def graph_map_single_valued graph_map_dom
      graph_map_member schema_graph_renamed_node schema_graph_renamed_discharge; blast)
qed

text \<open>
  The supplied relation retains one image for every original node, the exact
  root image, and all original inference metadata and indexed discharges.
  This condition permits any placement. Injectivity is a separate requirement,
  so metadata preservation cannot hide the identification of distinct nodes.
\<close>

end
