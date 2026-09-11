theory Factor_Proof_Flattening
  imports Factor_Proof_Positions Factor_Derivation_Recovery
begin

section \<open>Flattened node and discharge graphs\<close>

fun schema_proof_kind :: "('a,'s,'c) schema_proof \<Rightarrow> ('a,'c) schema_graph_node" where
  "schema_proof_kind (Schema_Proof c V B) = Schema_Inference c V"

lemma schema_proof_kind_not_assertion [simp]:
  "schema_proof_kind p \<noteq> Schema_Assertion"
  by (cases p) simp

lemma assertion_not_schema_proof_kind [simp]:
  "Schema_Assertion \<noteq> schema_proof_kind p"
  by (cases p) simp

definition schema_flat_discharges ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'d,'c) instantiated_proof_node set \<Rightarrow>
    ((('a,'s,'d,'c) instantiated_proof_node \<times> 's) \<times> ('a,'s,'d,'c) instantiated_proof_node) set" where
  "schema_flat_discharges P N =
    (\<Union>n\<in>N. (\<lambda>(s,m). ((n,s),m)) ` schema_proof_children P n)"

lemma schema_flat_discharge_member:
  "((n,s),m) \<in> schema_flat_discharges P N \<longleftrightarrow>
    n \<in> N \<and> (s,m) \<in> schema_proof_children P n"
  by (auto simp: schema_flat_discharges_def)

lemma schema_flat_discharges_finite:
  assumes "finite N"
  shows "finite (schema_flat_discharges P N)"
  unfolding schema_flat_discharges_def
  by (rule finite_UN_I[OF assms]) (simp add: schema_proof_children_finite)

lemma schema_flat_discharges_single_valued:
  assumes "\<And>n. n \<in> N \<Longrightarrow> instantiated_node_checked P n"
  shows "single_valued (schema_flat_discharges P N)"
proof -
  have sv: "\<And>n. n \<in> N \<Longrightarrow> single_valued (schema_proof_children P n)"
    by (rule schema_proof_children_single_valued[OF assms])
  show ?thesis using sv
    by (auto simp: single_valued_def schema_flat_discharge_member; blast)
qed

definition schema_proof_graph ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'d,'c) instantiated_proof_node \<Rightarrow>
    ('a,'s,'c,('a,'s,'d,'c) instantiated_proof_node) schema_derivation_graph" where
  "schema_proof_graph P r =
    \<lparr>graph_inferences = Abs_fset (graph_map (schema_proof_positions P r) (schema_proof_kind \<circ> fst)),
     graph_discharges = Abs_fset (schema_flat_discharges P (schema_proof_positions P r))\<rparr>"

lemma schema_proof_graph_fields:
  "fset (graph_inferences (schema_proof_graph P r)) =
    graph_map (schema_proof_positions P r) (schema_proof_kind \<circ> fst)"
  "fset (graph_discharges (schema_proof_graph P r)) =
    schema_flat_discharges P (schema_proof_positions P r)"
proof -
  have nodes: "finite (graph_map (schema_proof_positions P r) (schema_proof_kind \<circ> fst))"
    by (rule graph_map_finite[OF schema_proof_positions_finite])
  have edges: "finite (schema_flat_discharges P (schema_proof_positions P r))"
    by (rule schema_flat_discharges_finite[OF schema_proof_positions_finite])
  show "fset (graph_inferences (schema_proof_graph P r)) =
      graph_map (schema_proof_positions P r) (schema_proof_kind \<circ> fst)"
    using Abs_fset_inverse[of "graph_map (schema_proof_positions P r) (schema_proof_kind \<circ> fst)"] nodes
    by (simp add: schema_proof_graph_def)
  show "fset (graph_discharges (schema_proof_graph P r)) =
      schema_flat_discharges P (schema_proof_positions P r)"
    using Abs_fset_inverse[of "schema_flat_discharges P (schema_proof_positions P r)"] edges
    by (simp add: schema_proof_graph_def)
qed

lemma schema_proof_graph_assertion_uses [simp]:
  "schema_assertion_uses (schema_proof_graph P r) = {}"
  by (auto simp: schema_assertion_uses_def schema_proof_graph_fields graph_map_member)

lemma schema_proof_graph_nodes [simp]:
  "schema_graph_nodes (schema_proof_graph P r) = schema_proof_positions P r"
  by (simp add: schema_graph_nodes_def schema_proof_graph_fields graph_map_dom)

lemma schema_proof_graph_edges:
  "schema_graph_edges (schema_proof_graph P r) =
    {(m,n). n \<in> schema_proof_positions P r \<and> (m,n) \<in> schema_proof_edges P}"
  by (auto simp: schema_graph_edges_def schema_proof_graph_fields schema_flat_discharge_member schema_proof_edges_def)

lemma schema_proof_graph_premises:
  assumes "n \<in> schema_proof_positions P r"
  shows "schema_graph_premises (schema_proof_graph P r) n = schema_proof_children P n"
  using assms
  by (auto simp: schema_graph_premises_def schema_proof_graph_fields schema_flat_discharge_member)

lemma schema_proof_graph_path:
  assumes path: "(m,n) \<in> (schema_proof_edges P)\<^sup>*"
    and inside: "n \<in> schema_proof_positions P r"
  shows "(m,n) \<in> (schema_graph_edges (schema_proof_graph P r))\<^sup>*"
proof -
  have "\<And>m n. (m,n) \<in> (schema_proof_edges P)\<^sup>* \<Longrightarrow>
    n \<in> schema_proof_positions P r \<longrightarrow>
      (m,n) \<in> (schema_graph_edges (schema_proof_graph P r))\<^sup>*"
  proof -
    fix m n assume reach: "(m,n) \<in> (schema_proof_edges P)\<^sup>*"
    show "n \<in> schema_proof_positions P r \<longrightarrow>
      (m,n) \<in> (schema_graph_edges (schema_proof_graph P r))\<^sup>*"
      using reach
    proof (induction rule: rtrancl_induct)
      case base
      then show ?case by simp
    next
      case (step y z)
      show ?case
      proof
        assume z: "z \<in> schema_proof_positions P r"
        obtain s where child: "(s,y) \<in> schema_proof_children P z"
          using step.hyps(2) by (auto simp: schema_proof_edges_def)
        have y: "y \<in> schema_proof_positions P r" by (rule schema_proof_positions_closed[OF z child])
        have first: "(m,y) \<in> (schema_graph_edges (schema_proof_graph P r))\<^sup>*"
          using step.IH y by blast
        have last: "(y,z) \<in> schema_graph_edges (schema_proof_graph P r)"
          using step.hyps(2) z by (simp add: schema_proof_graph_edges)
        show "(m,z) \<in> (schema_graph_edges (schema_proof_graph P r))\<^sup>*"
          by (rule rtrancl_into_rtrancl[OF first last])
      qed
    qed
  qed
  then show ?thesis using path inside by blast
qed

lemma schema_proof_graph_formed:
  assumes checked: "instantiated_node_checked P r"
  shows "schema_graph_formed (schema_proof_graph P r) r"
proof -
  let ?G = "schema_proof_graph P r"
  let ?N = "schema_proof_positions P r"
  have nodes: "single_valued (fset (graph_inferences ?G))"
    by (simp add: schema_proof_graph_fields graph_map_single_valued)
  have edges: "single_valued (fset (graph_discharges ?G))"
    unfolding schema_proof_graph_fields(2)
    by (rule schema_flat_discharges_single_valued) (rule schema_proof_positions_checked[OF checked]; assumption)
  have bounds: "schema_graph_edges ?G \<subseteq> ?N \<times> ?N"
  proof
    fix z assume edge: "z \<in> schema_graph_edges ?G"
    obtain m n where zp: "z=(m,n)" by (cases z) auto
    have parent: "n \<in> ?N" and raw: "(m,n) \<in> schema_proof_edges P"
      using edge zp by (auto simp: schema_proof_graph_edges)
    obtain s where child: "(s,m) \<in> schema_proof_children P n"
      using raw by (auto simp: schema_proof_edges_def)
    have "m \<in> ?N" by (rule schema_proof_positions_closed[OF parent child])
    then show "z \<in> ?N \<times> ?N" using parent zp by simp
  qed
  have reachable: "\<forall>n\<in>?N. (n,r) \<in> (schema_graph_edges ?G)\<^sup>*"
  proof (intro ballI)
    fix n assume member: "n \<in> ?N"
    have path: "(n,r) \<in> (schema_proof_edges P)\<^sup>*"
      using member by (simp add: schema_proof_positions_def)
    show "(n,r) \<in> (schema_graph_edges ?G)\<^sup>*"
      by (rule schema_proof_graph_path[OF path schema_proof_positions_root])
  qed
  have subset: "schema_graph_edges ?G \<subseteq> schema_proof_edges P"
    by (auto simp: schema_proof_graph_edges)
  have wf: "wf (schema_graph_edges ?G)" by (rule wf_subset[OF schema_proof_edges_well_founded subset])
  have assertions: "single_valued (schema_assertion_uses ?G)" by (simp add: single_valued_def)
  show ?thesis using nodes edges assertions bounds reachable wf
    by (simp add: schema_graph_formed_def)
qed

section \<open>The flattened graph recovers the same closed proof\<close>

theorem schema_proof_graph_reading:
  assumes checked: "checks_schema_proof P tree d t"
  shows "schema_graph_reading P (schema_proof_graph P (tree,d,t)) (tree,d,t) d t
    (graph_map (schema_proof_positions P (tree,d,t)) snd)"
proof -
  let ?r = "(tree,d,t)"
  let ?G = "schema_proof_graph P ?r"
  let ?N = "schema_proof_positions P ?r"
  let ?J = "graph_map ?N snd"
  have root_checked: "instantiated_node_checked P ?r"
    using checked by (simp add: instantiated_node_checked_def)
  have formed: "schema_graph_formed ?G ?r" by (rule schema_proof_graph_formed[OF root_checked])
  have all_nodes: "\<forall>n A. (n,A) \<in> fset (graph_inferences ?G) \<longrightarrow>
    checks_schema_graph_node P ?G ?J n A"
  proof (intro allI impI)
    fix n A assume row: "(n,A) \<in> fset (graph_inferences ?G)"
    have member: "n \<in> ?N" and kind: "A=schema_proof_kind (fst n)"
      using row by (auto simp: schema_proof_graph_fields graph_map_member)
    obtain p e x where np: "n=(p,e,x)" by (cases n) auto
    obtain c V B where pp: "p=Schema_Proof c V B" by (cases p) auto
    have node_checked: "checks_schema_proof P (Schema_Proof c V B) e x"
      using schema_proof_positions_checked[OF root_checked member]
      by (simp add: instantiated_node_checked_def np pp)
    obtain Q where inst: "admitted_schema_instance P e c (fset V) x Q"
      using node_checked by (auto simp only: checks_schema_proof_node)
    have jv: "rel_value ?J n=(e,x)"
      using rel_value_graph_map[OF member, of snd] np by simp
    have local_edges: "schema_graph_premises ?G n = schema_proof_children P (Schema_Proof c V B,e,x)"
      using schema_proof_graph_premises[OF member] by (simp add: np pp)
    have domain: "rel_dom (schema_graph_premises ?G n) = rel_dom Q"
      using schema_proof_children_domain[OF node_checked inst] local_edges by simp
    have children: "\<forall>s m. (s,m) \<in> schema_graph_premises ?G n \<longrightarrow> (m,rel_value Q s) \<in> ?J"
    proof (intro allI impI)
      fix s m assume edge: "(s,m) \<in> schema_graph_premises ?G n"
      have child: "(s,m) \<in> schema_proof_children P n"
        using edge schema_proof_graph_premises[OF member] by simp
      have m_inside: "m \<in> ?N" by (rule schema_proof_positions_closed[OF member child])
      have premise: "(s,snd m) \<in> Q"
        using edge local_edges by (auto simp: schema_proof_children_at_instance[OF inst])
      have qsv: "single_valued Q" using admitted_instance_formed[OF inst] by blast
      have qv: "rel_value Q s=snd m" by (rule rel_value_eq[OF qsv premise])
      show "(m,rel_value Q s) \<in> ?J" using m_inside qv by (simp add: graph_map_member)
    qed
    show "checks_schema_graph_node P ?G ?J n A"
      using kind np pp inst domain children jv by auto
  qed
  show ?thesis using formed all_nodes graph_map_single_valued[of ?N snd]
    by (simp add: schema_graph_reading_def graph_map_dom graph_map_member)
qed

theorem schema_proof_graph_derives:
  assumes checked: "checks_schema_proof P tree d t"
  shows "schema_graph_derives P (schema_proof_graph P (tree,d,t)) (tree,d,t) d t {}"
proof -
  let ?G = "schema_proof_graph P (tree,d,t)"
  let ?J = "graph_map (schema_proof_positions P (tree,d,t)) snd"
  have read: "schema_graph_reading P ?G (tree,d,t) d t ?J"
    by (rule schema_proof_graph_reading[OF checked])
  have no_assertions: "\<And>n. (n,Schema_Assertion) \<notin> fset (graph_inferences ?G)"
    by (simp add: schema_proof_graph_fields graph_map_member eq_commute)
  have boundary: "schema_graph_assumptions ?G ?J = {}"
    using no_assertions by (auto simp: schema_graph_assumptions_def)
  show ?thesis unfolding schema_graph_derives_def
    by (rule exI[of _ ?J]) (use read boundary in simp)
qed

theorem schema_graph_complete:
  fixes P :: "('a,'s,'d,'c) schema_system"
  assumes "(d,t) \<in> positive_meaning P"
  shows "\<exists>G :: ('a,'s,'c,('a,'s,'d,'c) instantiated_proof_node) schema_derivation_graph.
    \<exists>root. schema_graph_derives P G root d t {}"
proof -
  obtain tree where certificate: "checks_schema_proof P tree d t"
    using schema_proof_complete[OF assms] by blast
  show ?thesis
    by (rule exI[of _ "schema_proof_graph P (tree,d,t)"], rule exI[of _ "(tree,d,t)"])
       (rule schema_proof_graph_derives[OF certificate])
qed

text \<open>
  Every existing closed tree certificate gives a finite rooted acyclic graph
  with the same valid conclusion and no assumptions. Its node set is exactly
  the full reachable closure, and its discharge table contains every source
  premise socket. A child is shared only with an identical certificate and
  required call. No additional proof rule, stored node claim, or truth oracle
  participates in this construction.
\<close>

end
