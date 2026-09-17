theory Factor_Finite_Proof_Coordinate_Graphs
  imports Factor_Finite_Proof_Coordinates Factor_Finite_Proof_Flattening Factor_Finite_Graph_Mappings
begin

definition finite_schema_coordinate_graph ::
    "('a,'s::linorder,'d,'c) finite_schema_system\<Rightarrow>('a,'s,'d,'c) finite_instantiated_proof_node\<Rightarrow>
      ('a,'s,'c,'s list) finite_derivation_graph" where
  "finite_schema_coordinate_graph P root=
    finite_mapped_graph (finite_schema_proof_coordinates P root) (finite_schema_proof_graph P root)"

theorem finite_schema_coordinate_graph_mapping:
  "finite_graph_mapping (finite_schema_proof_coordinates P (p,d,t))
    (finite_schema_proof_graph P (p,d,t)) (p,d,t) (finite_schema_coordinate_graph P (p,d,t)) []"
  unfolding finite_schema_coordinate_graph_def
  by (rule finite_mapped_graph_mapping[OF finite_schema_proof_coordinates_functional])
    (simp only: finite_schema_proof_coordinates_domain finite_schema_proof_graph_nodes,
      rule finite_schema_proof_coordinates_root)

theorem finite_schema_coordinate_graph_derives:
  assumes checked: "finite_checks_schema_proof P p d t"
  shows "schema_graph_derives (decode_finite_system P)
    (decode_finite_graph (finite_schema_coordinate_graph P (p,d,t))) [] d (decode_finite_term t) {}"
proof -
  have original: "schema_graph_derives (decode_finite_system P)
    (decode_finite_graph (finite_schema_proof_graph P (p,d,t))) (p,d,t) d (decode_finite_term t) {}"
    by (rule finite_schema_proof_graph_finite_nodes_derives[OF checked])
  have mapping: "schema_graph_mapping (fset (finite_schema_proof_coordinates P (p,d,t)))
    (decode_finite_graph (finite_schema_proof_graph P (p,d,t))) (p,d,t)
    (decode_finite_graph (finite_schema_coordinate_graph P (p,d,t))) []"
    by (simp only: finite_graph_mapping_exact[symmetric]; rule finite_schema_coordinate_graph_mapping)
  show ?thesis using schema_graph_mapping_derives[OF original mapping
      finite_schema_proof_coordinates_injective[OF checked]] by (simp only: image_empty)
qed

text \<open>
  The complete relation map moves all original nodes and both endpoints of
  every indexed discharge. It preserves the certificate graph and its closed
  derivation under the same original program. Private clause, binder and socket
  metadata still require their actual source-positioning contract before
  native artifact placement.
\<close>

end
