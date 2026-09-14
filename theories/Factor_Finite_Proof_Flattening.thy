theory Factor_Finite_Proof_Flattening
  imports Factor_Finite_Proof_Positions Factor_Proof_Flattening Factor_Graph_Transport
    Finite_Indexed_Relation_Families
begin

fun finite_schema_proof_kind :: "('a,'s,'c) finite_schema_proof\<Rightarrow>('a,'c) finite_schema_graph_node" where
  "finite_schema_proof_kind (Schema_Proof c V B)=Finite_Inference c V"

lemma finite_schema_proof_kind_correct [simp]:
  "decode_finite_graph_node (finite_schema_proof_kind p)=schema_proof_kind (decode_finite_proof p)"
  by (cases p) (simp only: finite_schema_proof_kind.simps decode_finite_graph_node.simps
    decode_finite_proof_node schema_proof_kind.simps)

definition finite_schema_flat_discharges ::
    "('a,'s,'d,'c) finite_schema_system\<Rightarrow>('a,'s,'d,'c) finite_instantiated_proof_node fset\<Rightarrow>
      ((('a,'s,'d,'c) finite_instantiated_proof_node\<times>'s)\<times>('a,'s,'d,'c) finite_instantiated_proof_node) fset" where
  "finite_schema_flat_discharges P N=finite_indexed_relation_family N (finite_schema_proof_children P)"

lemma finite_schema_flat_discharge_member:
  "((n,s),m) |\<in>| finite_schema_flat_discharges P N \<longleftrightarrow>
    n |\<in>| N \<and> (s,m) |\<in>| finite_schema_proof_children P n"
  by (simp only: finite_schema_flat_discharges_def finite_indexed_relation_family_member)

lemma finite_schema_flat_discharges_correct:
  "fset (fimage (map_prod (map_prod decode_finite_instantiated_node id) decode_finite_instantiated_node)
      (finite_schema_flat_discharges P N))=
    schema_flat_discharges (decode_finite_system P) (decode_finite_instantiated_node ` fset N)"
  unfolding finite_schema_flat_discharges_def schema_flat_discharges_def
  by (simp only: fimage.rep_eq finite_indexed_relation_family_correct;
    rule indexed_relation_family_image;
    simp only: finite_schema_proof_children_correct[symmetric] fimage.rep_eq)

definition finite_schema_proof_graph ::
    "('a,'s,'d,'c) finite_schema_system\<Rightarrow>('a,'s,'d,'c) finite_instantiated_proof_node\<Rightarrow>
      ('a,'s,'c,('a,'s,'d,'c) finite_instantiated_proof_node) finite_derivation_graph" where
  "finite_schema_proof_graph P root=(case root of (p,d,t) \<Rightarrow>
    let N=finite_schema_proof_positions P p d t in
      \<lparr>finite_graph_inferences=fimage (\<lambda>n. (n,finite_schema_proof_kind (fst n))) N,
       finite_graph_discharges=finite_schema_flat_discharges P N\<rparr>)"

theorem finite_schema_proof_graph_correct:
  "rename_schema_graph decode_finite_instantiated_node (decode_finite_graph (finite_schema_proof_graph P root))=
    schema_proof_graph (decode_finite_system P) (decode_finite_instantiated_node root)"
proof -
  obtain p d t where root: "root=(p,d,t)" by (cases root) auto
  let ?N = "finite_schema_proof_positions P p d t"
  let ?D = decode_finite_instantiated_node
  let ?G = "rename_schema_graph ?D (decode_finite_graph (finite_schema_proof_graph P root))"
  let ?H = "schema_proof_graph (decode_finite_system P) (?D root)"
  have positions: "?D ` fset ?N=schema_proof_positions (decode_finite_system P) (?D root)"
    using finite_schema_proof_positions_correct[of P p d t]
    by (simp only: root fimage.rep_eq)
  have nodes: "fset (graph_inferences ?G)=graph_map (?D ` fset ?N) (schema_proof_kind \<circ> fst)"
    by (auto simp: root finite_schema_proof_graph_def Let_def rename_schema_graph_def
      decode_finite_graph_def graph_map_def fimage.rep_eq map_prod_def comp_def
      intro: rev_image_eqI; metis imageI decode_finite_instantiated_node_pair)
  have inferences: "graph_inferences ?G=graph_inferences ?H"
    by (simp only: fset_inject[symmetric] nodes positions schema_proof_graph_fields)
  have field: "graph_discharges ?G=fimage (map_prod (map_prod ?D id) ?D) (finite_schema_flat_discharges P ?N)"
    by (simp add: root finite_schema_proof_graph_def Let_def rename_schema_graph_def)
  have edges: "fset (graph_discharges ?G)=schema_flat_discharges (decode_finite_system P) (?D ` fset ?N)"
    by (simp only: field finite_schema_flat_discharges_correct)
  have discharges: "graph_discharges ?G=graph_discharges ?H"
    by (simp only: fset_inject[symmetric] edges positions schema_proof_graph_fields)
  show ?thesis by (rule inference_graph.equality) (rule inferences, rule discharges, simp)
qed

theorem finite_schema_proof_graph_derives:
  assumes checked: "finite_checks_schema_proof P p d t"
  shows "schema_graph_derives (decode_finite_system P)
    (rename_schema_graph decode_finite_instantiated_node (decode_finite_graph (finite_schema_proof_graph P (p,d,t))))
      (decode_finite_instantiated_node (p,d,t)) d (decode_finite_term t) {}"
  by (simp only: finite_schema_proof_graph_correct decode_finite_instantiated_node_pair;
    rule schema_proof_graph_derives; use checked in \<open>simp only: finite_checks_schema_proof_exact\<close>)

theorem finite_schema_proof_graph_finite_nodes_derives:
  assumes checked: "finite_checks_schema_proof P p d t"
  shows "schema_graph_derives (decode_finite_system P)
    (decode_finite_graph (finite_schema_proof_graph P (p,d,t))) (p,d,t) d (decode_finite_term t) {}"
proof -
  have injective: "inj decode_finite_instantiated_node" by (auto simp: inj_def)
  show ?thesis
    by (rule schema_graph_derives_rename_reflect[where f=decode_finite_instantiated_node, OF _ injective])
      (simp only: image_empty; rule finite_schema_proof_graph_derives[OF checked])
qed

lemma finite_schema_proof_graph_nodes:
  "finite_graph_nodes (finite_schema_proof_graph P (p,d,t))=finite_schema_proof_positions P p d t"
  by (auto simp: finite_schema_proof_graph_def Let_def finite_graph_nodes_def
    fimage_fimage comp_def)

export_code finite_schema_proof_graph checking SML

text \<open>
  The complete finite graph retains every reachable certificate and required
  call, all original node metadata and every source-derived premise socket.
  Exact decoding recovers the existing whole proof graph. A checked root gives
  the same closed derivation. Source positioning, physical node allocation and
  replay are separate operations and require their original contracts.
\<close>

end
