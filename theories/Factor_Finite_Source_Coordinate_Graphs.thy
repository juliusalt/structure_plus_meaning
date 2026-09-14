theory Factor_Finite_Source_Coordinate_Graphs
  imports Factor_Finite_Proof_Positioning Factor_Finite_Proof_Coordinate_Graphs
    Factor_Finite_Graph_Inputs Factor_Finite_Native_Sources Factor_Package_Dependencies
begin

definition finite_source_coordinate_graph where
  "finite_source_coordinate_graph P root=finite_mapped_graph
    (finite_schema_proof_coordinates P root) (finite_source_proof_graph P root)"

theorem finite_source_coordinate_graph_mapping:
  "finite_graph_mapping (finite_schema_proof_coordinates P (p,d,t)) (finite_source_proof_graph P (p,d,t))
    (p,d,t) (finite_source_coordinate_graph P (p,d,t)) []"
  unfolding finite_source_coordinate_graph_def
  by (rule finite_mapped_graph_mapping[OF finite_schema_proof_coordinates_functional])
    (simp only: finite_schema_proof_coordinates_domain finite_source_proof_graph_nodes,
      rule finite_schema_proof_coordinates_root)

theorem finite_source_coordinate_graph_derives:
  assumes checked: "finite_checks_schema_proof P p d t"
  shows "schema_graph_derives (decode_finite_system (finite_positioned_program P))
    (decode_finite_graph (finite_source_coordinate_graph P (p,d,t))) [] d (decode_finite_term t) {}"
proof -
  have original: "schema_graph_derives (decode_finite_system (finite_positioned_program P))
    (decode_finite_graph (finite_source_proof_graph P (p,d,t))) (p,d,t) d (decode_finite_term t) {}"
    by (rule finite_source_proof_graph_derives[OF checked])
  have mapping: "schema_graph_mapping (fset (finite_schema_proof_coordinates P (p,d,t)))
    (decode_finite_graph (finite_source_proof_graph P (p,d,t))) (p,d,t)
    (decode_finite_graph (finite_source_coordinate_graph P (p,d,t))) []"
    by (simp only: finite_graph_mapping_exact[symmetric]; rule finite_source_coordinate_graph_mapping)
  show ?thesis using schema_graph_mapping_derives[OF original mapping
      finite_schema_proof_coordinates_injective[OF checked]] by (simp only: image_empty)
qed

theorem finite_source_coordinate_graph_ready:
  assumes source: "finite_native_source E u r=Some P"
    and checked: "finite_checks_schema_proof P p d t"
  shows "finite_graph_construction_ready E (finite_source_coordinate_graph P (p,d,t)) []"
proof -
  let ?E = "decode_finite_environment E"
  let ?P = "decode_finite_system P"
  let ?G = "decode_finite_graph (finite_source_coordinate_graph P (p,d,t))"
  have package: "native_package_at ?E u r ?P" using source by (simp only: finite_native_source_correct)
  have environment: "environment_formed ?E"
    using native_package_projection(1)[OF package] by (simp only: native_package_formed_def; blast)
  have derived: "schema_graph_derives (positioned_program ?P) ?G [] d (decode_finite_term t) {}"
    using finite_source_coordinate_graph_derives[OF checked]
    by (simp only: finite_positioned_program_correct)
  have formed: "schema_graph_formed ?G []"
    using derived by (auto simp: schema_graph_derives_def schema_graph_reading_def)
  have metadata: "graph_metadata_at ?E ?G" by (rule derived_graph_metadata[OF package derived])
  show ?thesis by (simp only: finite_graph_construction_ready_exact environment formed metadata simp_thms)
qed

export_code finite_source_coordinate_graph checking SML

text \<open>
  Source metadata is positioned before the complete original node family is
  assigned its actual path representatives. The complete map retains the
  positioned graph and the same closed derivation. An actual native package
  reading and a checked certificate supply all original metadata positions and
  prove the existing native graph constructor's full readiness condition.
\<close>

end
