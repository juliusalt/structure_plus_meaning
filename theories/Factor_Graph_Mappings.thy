theory Factor_Graph_Mappings
  imports Factor_Graph_Transport Finite_Function_Graphs
begin

definition schema_graph_mapping where
  "schema_graph_mapping M G root H r=(single_valued M \<and>
    rel_dom M=schema_graph_nodes G \<and> (root,r)\<in>M \<and>
    fset (graph_inferences H)={(m,N). \<exists>n. (n,N)\<in>fset (graph_inferences G) \<and> (n,m)\<in>M} \<and>
    fset (graph_discharges H)={((m,s),k). \<exists>n q.
      ((n,s),q)\<in>fset (graph_discharges G) \<and> (n,m)\<in>M \<and> (q,k)\<in>M})"

lemma schema_graph_mapping_node:
  assumes "schema_graph_mapping M G root H r"
  shows "(m,A)\<in>fset (graph_inferences H) \<longleftrightarrow>
    (\<exists>n. (n,A)\<in>fset (graph_inferences G) \<and> (n,m)\<in>M)"
  using assms by (simp only: schema_graph_mapping_def mem_Collect_eq case_prod_conv; blast)

lemma schema_graph_mapping_discharge:
  assumes "schema_graph_mapping M G root H r"
  shows "((m,s),k)\<in>fset (graph_discharges H) \<longleftrightarrow>
    (\<exists>n q. ((n,s),q)\<in>fset (graph_discharges G) \<and> (n,m)\<in>M \<and> (q,k)\<in>M)"
  using assms by (simp only: schema_graph_mapping_def mem_Collect_eq case_prod_conv; blast)

lemma schema_graph_mapping_nodes:
  assumes mapping: "schema_graph_mapping M G root H r"
  shows "schema_graph_nodes H=rel_ran M"
proof -
  have domain: "rel_dom M=rel_dom (fset (graph_inferences G))"
    using mapping by (simp only: schema_graph_mapping_def schema_graph_nodes_def; blast)
  show ?thesis using domain
    by (auto simp: schema_graph_nodes_def rel_dom_def rel_ran_def
      schema_graph_mapping_node[OF mapping]; blast)
qed

theorem schema_graph_mapping_compose:
  assumes first: "schema_graph_mapping M G root H r"
    and second: "schema_graph_mapping N H r K s"
  shows "schema_graph_mapping (M O N) G root K s"
proof -
  have mf: "single_valued M" and nf: "single_valued N"
    and md: "rel_dom M=schema_graph_nodes G" and nd: "rel_dom N=schema_graph_nodes H"
    and mr: "(root,r)\<in>M" and nr: "(r,s)\<in>N"
    using first second by (simp only: schema_graph_mapping_def; blast)+
  have coverage: "rel_ran M\<subseteq>rel_dom N"
    by (simp only: nd schema_graph_mapping_nodes[OF first])
  have functional: "single_valued (M O N)" by (rule relation_join_functional[OF mf nf])
  have domain: "rel_dom (M O N)=schema_graph_nodes G"
    by (simp only: relation_join_domain[OF coverage] md)
  have root: "(root,s)\<in>M O N" using mr nr by blast
  have nodes: "fset (graph_inferences K)={(k,A). \<exists>n.
      (n,A)\<in>fset (graph_inferences G) \<and> (n,k)\<in>M O N}"
    by (rule set_eqI)
      (auto simp: schema_graph_mapping_node[OF second] schema_graph_mapping_node[OF first]; blast)
  have edges: "fset (graph_discharges K)={((k,t),l). \<exists>n q.
      ((n,t),q)\<in>fset (graph_discharges G) \<and> (n,k)\<in>M O N \<and> (q,l)\<in>M O N}"
    by (rule set_eqI)
      (auto simp: schema_graph_mapping_discharge[OF second] schema_graph_mapping_discharge[OF first]; blast)
  show ?thesis by (simp only: schema_graph_mapping_def functional domain root nodes edges simp_thms)
qed

lemma schema_graph_mapping_unique:
  fixes H K :: "('a,'s,'c,'m,'v) inference_graph"
  assumes left: "schema_graph_mapping M G root H r" and right: "schema_graph_mapping M G root K s"
  shows "H=K" "r=s"
proof -
  have nodes: "graph_inferences H=graph_inferences K"
    and edges: "graph_discharges H=graph_discharges K"
    using left right by (auto simp: schema_graph_mapping_def fset_inject[symmetric])
  show "H=K" by (rule inference_graph.equality) (rule nodes, rule edges, simp)
  show "r=s" using left right
    by (auto simp: schema_graph_mapping_def dest: single_valued_outputs)
qed

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

theorem schema_graph_mapping_derives:
  assumes derived: "schema_graph_derives P G root d t A"
    and mapping: "schema_graph_mapping M G root H r"
    and injective: "single_valued (M\<inverse>)"
  shows "schema_graph_derives P H r d t (map_prod (rel_value M) id ` A)"
proof -
  let ?N = "schema_graph_nodes G"
  let ?h = "rel_value M"
  have formed: "schema_graph_formed G root"
    using derived by (auto simp: schema_graph_derives_def schema_graph_reading_def)
  have functional: "single_valued M" and domain: "rel_dom M=?N"
    using mapping by (simp only: schema_graph_mapping_def; blast)+
  have graph: "M=graph_map ?N ?h"
    using single_valued_graph[OF functional] by (simp only: domain)
  have inverse: "single_valued ((graph_map ?N ?h)\<inverse>)"
    by (simp only: graph[symmetric]; rule injective)
  have one_to_one: "inj_on ?h ?N"
    using inverse by (simp only: graph_map_converse_functional)
  have canonical: "schema_graph_mapping M G root (rename_schema_graph ?h G) (?h root)"
    using schema_graph_mapping_rename[OF formed, where h="?h"]
    by (simp only: graph[symmetric])
  have equal: "H=rename_schema_graph ?h G" "r=?h root"
    by (rule schema_graph_mapping_unique[OF mapping canonical])+
  show ?thesis by (simp only: equal; rule schema_graph_derives_rename[OF derived one_to_one])
qed

text \<open>
  The supplied relation retains one image for every original node, the exact
  root image, and all original inference metadata and indexed discharges.
  This condition permits any placement. Injectivity is a separate requirement,
  so metadata preservation cannot hide the identification of distinct nodes.
\<close>

end
