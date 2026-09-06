theory Factor_Graph_Renaming
  imports Factor_Derivation_Recovery
begin

section \<open>Private proof-node coordinates\<close>

definition rename_schema_graph ::
  "('n \<Rightarrow> 'm) \<Rightarrow> ('a,'s,'c,'n) schema_derivation_graph \<Rightarrow>
    ('a,'s,'c,'m) schema_derivation_graph" where
  "rename_schema_graph f G =
    \<lparr>graph_inferences = fimage (map_prod f id) (graph_inferences G),
     graph_discharges = fimage (map_prod (map_prod f id) f) (graph_discharges G)\<rparr>"

lemma schema_graph_renamed_node:
  "(m,A) \<in> fset (graph_inferences (rename_schema_graph f G)) \<longleftrightarrow>
    (\<exists>n. (n,A) \<in> fset (graph_inferences G) \<and> m=f n)"
  by (auto simp: rename_schema_graph_def map_prod_def)

lemma schema_graph_renamed_discharge:
  "((m,s),k) \<in> fset (graph_discharges (rename_schema_graph f G)) \<longleftrightarrow>
    (\<exists>n q. ((n,s),q) \<in> fset (graph_discharges G) \<and> m=f n \<and> k=f q)"
  by (auto simp: rename_schema_graph_def map_prod_def intro: rev_image_eqI)

lemma schema_graph_renamed_nodes:
  "schema_graph_nodes (rename_schema_graph f G) = f ` schema_graph_nodes G"
  by (auto simp: schema_graph_nodes_def schema_graph_renamed_node rel_dom_def)

lemma schema_graph_renamed_edges:
  "schema_graph_edges (rename_schema_graph f G) = map_prod f f ` schema_graph_edges G"
  by (auto simp: schema_graph_edges_def schema_graph_renamed_discharge map_prod_def; blast)

lemma schema_graph_discharge_nodes:
  assumes formed: "schema_graph_formed G root"
    and discharge: "((n,s),m) \<in> fset (graph_discharges G)"
  shows "n \<in> schema_graph_nodes G" "m \<in> schema_graph_nodes G"
proof -
  have edge: "(m,n) \<in> schema_graph_edges G"
    using discharge by (auto simp: schema_graph_edges_def)
  show "n \<in> schema_graph_nodes G" "m \<in> schema_graph_nodes G"
    using schema_graph_edge_nodes[OF formed edge] by auto
qed

lemma schema_graph_renamed_assertion_uses:
  assumes formed: "schema_graph_formed G root" and injective: "inj_on f (schema_graph_nodes G)"
  shows "schema_assertion_uses (rename_schema_graph f G) =
    map_prod f (map_prod f id) ` schema_assertion_uses G"
proof
  show "schema_assertion_uses (rename_schema_graph f G) \<subseteq>
    map_prod f (map_prod f id) ` schema_assertion_uses G"
  proof
    fix x assume member: "x \<in> schema_assertion_uses (rename_schema_graph f G)"
    obtain n p s where shape: "x=(n,(p,s))" by (cases x) auto
    have node: "(n,Schema_Assertion) \<in> fset (graph_inferences (rename_schema_graph f G))"
      and discharge: "((p,s),n) \<in> fset (graph_discharges (rename_schema_graph f G))"
      using member shape by (simp_all add: schema_assertion_use_member)
    obtain a where assertion: "(a,Schema_Assertion) \<in> fset (graph_inferences G)" and na: "n=f a"
      using node by (auto simp: schema_graph_renamed_node)
    obtain b c where original: "((b,s),c) \<in> fset (graph_discharges G)" and pb: "p=f b" and nc: "n=f c"
      using discharge by (auto simp: schema_graph_renamed_discharge)
    have ai: "a \<in> schema_graph_nodes G" using assertion by (auto simp: schema_graph_nodes_def rel_dom_def)
    have ci: "c \<in> schema_graph_nodes G" by (rule schema_graph_discharge_nodes(2)[OF formed original])
    have same: "a=c" by (rule inj_onD[OF injective _ ai ci]) (use na nc in simp)
    have old: "(a,(b,s)) \<in> schema_assertion_uses G"
      using assertion original same by (simp add: schema_assertion_use_member)
    show "x \<in> map_prod f (map_prod f id) ` schema_assertion_uses G"
      by (rule rev_image_eqI[OF old]) (use shape na pb in simp)
  qed
  show "map_prod f (map_prod f id) ` schema_assertion_uses G \<subseteq>
    schema_assertion_uses (rename_schema_graph f G)"
    by (auto simp: schema_assertion_uses_def map_prod_def schema_graph_renamed_node schema_graph_renamed_discharge; blast)
qed

lemma schema_graph_renamed_premises:
  assumes formed: "schema_graph_formed G root" and injective: "inj_on f (schema_graph_nodes G)"
    and inside: "n \<in> schema_graph_nodes G"
  shows "schema_graph_premises (rename_schema_graph f G) (f n) =
    map_prod id f ` schema_graph_premises G n"
proof
  show "schema_graph_premises (rename_schema_graph f G) (f n) \<subseteq>
    map_prod id f ` schema_graph_premises G n"
  proof
    fix z assume member: "z \<in> schema_graph_premises (rename_schema_graph f G) (f n)"
    obtain s m where zp: "z=(s,m)" by (cases z) auto
    obtain k q where old: "((k,s),q) \<in> fset (graph_discharges G)" "f n=f k" "m=f q"
      using member zp by (auto simp: schema_graph_premises_def schema_graph_renamed_discharge)
    have k: "k \<in> schema_graph_nodes G" by (rule schema_graph_discharge_nodes(1)[OF formed old(1)])
    have same: "n=k" by (rule inj_onD[OF injective old(2) inside k])
    have premise: "(s,q) \<in> schema_graph_premises G n"
      using old(1) same by (simp add: schema_graph_premises_def)
    show "z \<in> map_prod id f ` schema_graph_premises G n"
      by (rule rev_image_eqI[OF premise]) (use zp old(3) in simp)
  qed
  show "map_prod id f ` schema_graph_premises G n \<subseteq>
    schema_graph_premises (rename_schema_graph f G) (f n)"
    by (auto simp: schema_graph_premises_def schema_graph_renamed_discharge map_prod_def; blast)
qed

lemma schema_graph_path_map:
  assumes "(a,b) \<in> (schema_graph_edges G)\<^sup>*"
  shows "(f a,f b) \<in> (schema_graph_edges (rename_schema_graph f G))\<^sup>*"
  using assms
proof (induction rule: rtrancl_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  have edge: "(f y,f z) \<in> schema_graph_edges (rename_schema_graph f G)"
    using imageI[OF step.hyps(2), of "map_prod f f"]
    by (simp add: schema_graph_renamed_edges)
  show ?case by (rule rtrancl_into_rtrancl[OF step.IH edge])
qed

theorem renamed_schema_graph_formed:
  assumes formed: "schema_graph_formed G root"
    and injective: "inj_on f (schema_graph_nodes G)"
  shows "schema_graph_formed (rename_schema_graph f G) (f root)"
proof -
  let ?N = "schema_graph_nodes G"
  let ?F = "rename_schema_graph f G"
  have nsv: "single_valued (fset (graph_inferences G))"
    and dsv: "single_valued (fset (graph_discharges G))"
    and root: "root \<in> ?N" and wf: "wf (schema_graph_edges G)"
    and source_bounds: "schema_graph_edges G \<subseteq> ?N \<times> ?N"
    and source_paths: "\<forall>n\<in>?N. (n,root) \<in> (schema_graph_edges G)\<^sup>*"
    using formed by (auto simp: schema_graph_formed_def)
  have node_inj: "inj_on f (rel_dom (fset (graph_inferences G)))"
    using injective by (simp add: schema_graph_nodes_def)
  have nodes: "single_valued (fset (graph_inferences ?F))"
    using single_valued_pair_image[OF nsv node_inj, where g=id]
    by (simp add: rename_schema_graph_def map_prod_def)
  have key_inj: "inj_on (map_prod f id) (rel_dom (fset (graph_discharges G)))"
  proof (rule inj_onI)
    fix x y assume xm: "x \<in> rel_dom (fset (graph_discharges G))"
      and ym: "y \<in> rel_dom (fset (graph_discharges G))"
      and same: "map_prod f id x=map_prod f id y"
    obtain n s where xp: "x=(n,s)" by (cases x) auto
    obtain m t where yp: "y=(m,t)" by (cases y) auto
    obtain a where left: "((n,s),a) \<in> fset (graph_discharges G)"
      using xm xp by (auto simp: rel_dom_def)
    obtain b where right: "((m,t),b) \<in> fset (graph_discharges G)"
      using ym yp by (auto simp: rel_dom_def)
    have n: "n \<in> ?N" by (rule schema_graph_discharge_nodes(1)[OF formed left])
    have m: "m \<in> ?N" by (rule schema_graph_discharge_nodes(1)[OF formed right])
    have eq: "f n=f m" using same xp yp by simp
    have nm: "n=m" by (rule inj_onD[OF injective eq n m])
    show "x=y" using same xp yp nm by simp
  qed
  have discharges: "single_valued (fset (graph_discharges ?F))"
    using single_valued_pair_image[OF dsv key_inj, where g=f]
    by (simp add: rename_schema_graph_def map_prod_def)
  have bounds: "schema_graph_edges ?F \<subseteq> (f ` ?N) \<times> (f ` ?N)"
    using source_bounds by (auto simp: schema_graph_renamed_edges map_prod_def)
  have paths: "\<forall>n\<in>schema_graph_nodes ?F. (n,f root) \<in> (schema_graph_edges ?F)\<^sup>*"
  proof (intro ballI)
    fix n assume "n \<in> schema_graph_nodes ?F"
    then obtain m where member: "m \<in> ?N" and np: "n=f m"
      by (auto simp: schema_graph_renamed_nodes)
    have path: "(m,root) \<in> (schema_graph_edges G)\<^sup>*" using source_paths member by blast
    show "(n,f root) \<in> (schema_graph_edges ?F)\<^sup>*"
      using schema_graph_path_map[OF path, of f] np by simp
  qed
  have subset: "schema_graph_edges ?F \<subseteq> inv_image (schema_graph_edges G) (inv_into ?N f)"
  proof
    fix z assume member: "z \<in> schema_graph_edges ?F"
    obtain m n where edge: "(m,n) \<in> schema_graph_edges G" and zp: "z=(f m,f n)"
      using member by (auto simp: schema_graph_renamed_edges map_prod_def)
    have mn: "m \<in> ?N" "n \<in> ?N" using schema_graph_edge_nodes[OF formed edge] by auto
    show "z \<in> inv_image (schema_graph_edges G) (inv_into ?N f)"
      using edge mn injective zp by (simp add: inv_image_def)
  qed
  have wf': "wf (schema_graph_edges ?F)" by (rule wf_subset[OF wf_inv_image[OF wf] subset])
  have source_assertions: "single_valued (schema_assertion_uses G)"
    using formed by (simp add: schema_graph_formed_def)
  have assertion_inj: "inj_on f (rel_dom (schema_assertion_uses G))"
    by (rule inj_on_subset[OF injective schema_assertion_use_domain])
  have assertions: "single_valued (schema_assertion_uses ?F)"
    using single_valued_pair_image[OF source_assertions assertion_inj, where g="map_prod f id"]
    by (simp add: schema_graph_renamed_assertion_uses[OF formed injective] map_prod_def)
  show ?thesis using nodes discharges assertions root bounds paths wf'
    by (simp add: schema_graph_formed_def schema_graph_renamed_nodes)
qed

text \<open>
  Only private proof-node coordinates move. Inference clauses, variable
  bindings, and premise socket coordinates remain exact. Every original node
  and discharge has an origin in the renamed graph, and injectivity is required
  on the actual finite node boundary, not on an unrelated ambient universe.
\<close>

end
