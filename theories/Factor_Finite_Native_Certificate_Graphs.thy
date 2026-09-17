theory Factor_Finite_Native_Certificate_Graphs
  imports Factor_Finite_Source_Coordinate_Graphs Factor_Finite_Graph_Correspondence Factor_Package_Locality
begin

definition finite_native_certificate_graph where
  "finite_native_certificate_graph E u r p d t=(case finite_native_source E u r of None \<Rightarrow> None
    | Some P \<Rightarrow> if finite_checks_schema_proof P p d t then
      map_option (\<lambda>(F,N,s,H). (F,finite_edge_compose (finite_schema_proof_coordinates P (p,d,t)) N,s,H))
        (finite_extend_native_graph E (finite_source_coordinate_graph P (p,d,t)) [])
      else None)"

lemma finite_native_certificate_graph_result:
  "finite_native_certificate_graph E u r p d t=Some (F,M,s,H) \<longleftrightarrow>
    (\<exists>P N. finite_native_source E u r=Some P \<and> finite_checks_schema_proof P p d t \<and>
      finite_extend_native_graph E (finite_source_coordinate_graph P (p,d,t)) []=Some (F,N,s,H) \<and>
      M=finite_edge_compose (finite_schema_proof_coordinates P (p,d,t)) N)"
  by (cases s) (auto simp: finite_native_certificate_graph_def split: option.splits if_splits prod.splits)

theorem finite_native_certificate_graph_domain:
  "(\<exists>F M s H. finite_native_certificate_graph E u r p d t=Some (F,M,s,H)) \<longleftrightarrow>
    (\<exists>P. finite_native_source E u r=Some P \<and> finite_checks_schema_proof P p d t)"
proof
  assume "\<exists>F M s H. finite_native_certificate_graph E u r p d t=Some (F,M,s,H)"
  then show "\<exists>P. finite_native_source E u r=Some P \<and> finite_checks_schema_proof P p d t"
    by (simp only: finite_native_certificate_graph_result; blast)
next
  assume "\<exists>P. finite_native_source E u r=Some P \<and> finite_checks_schema_proof P p d t"
  then obtain P where source: "finite_native_source E u r=Some P"
    and checked: "finite_checks_schema_proof P p d t" by blast
  have ready: "finite_graph_construction_ready E (finite_source_coordinate_graph P (p,d,t)) []"
    by (rule finite_source_coordinate_graph_ready[OF source checked])
  obtain F N s H where placed:
    "finite_extend_native_graph E (finite_source_coordinate_graph P (p,d,t)) []=Some (F,N,s,H)"
    using ready by (simp only: finite_extend_native_graph_domain[symmetric]; blast)
  show "\<exists>F M s H. finite_native_certificate_graph E u r p d t=Some (F,M,s,H)"
    using source checked placed by (simp only: finite_native_certificate_graph_result; blast)
qed

theorem finite_native_certificate_graph_correct:
  assumes result: "finite_native_certificate_graph E u r p d t=Some (F,M,s,H)"
    and source: "finite_native_source E u r=Some P"
  shows "finite_checks_schema_proof P p d t"
    "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "finite_environment_agrees_on E F (finite_environment_uses E)"
    "finite_graph_mapping M (finite_source_proof_graph P (p,d,t)) (p,d,t) H s"
    "single_valued ((fset M)\<inverse>)"
    "image fst (fset (finite_graph_nodes H))\<inter>fset (finite_environment_uses E)={}"
    "H |\<in>| finite_native_graph_readings F s"
    "schema_graph_derives (decode_finite_system (finite_positioned_program P))
      (decode_finite_graph H) s d (decode_finite_term t) {}"
    "finite_native_source F u r=Some P"
proof -
  obtain N where checked: "finite_checks_schema_proof P p d t"
    and placed: "finite_extend_native_graph E (finite_source_coordinate_graph P (p,d,t)) []=Some (F,N,s,H)"
    and map: "M=finite_edge_compose (finite_schema_proof_coordinates P (p,d,t)) N"
    using result source by (auto simp only: finite_native_certificate_graph_result option.inject)
  show "finite_checks_schema_proof P p d t" by (rule checked)
  show "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "finite_environment_agrees_on E F (finite_environment_uses E)"
    "image fst (fset (finite_graph_nodes H))\<inter>fset (finite_environment_uses E)={}"
    "H |\<in>| finite_native_graph_readings F s"
    by (rule finite_extend_native_graph_correct[OF placed])+
  have mapping: "finite_graph_mapping M (finite_source_proof_graph P (p,d,t)) (p,d,t) H s"
    by (simp only: map;
      rule finite_graph_mapping_compose[OF finite_source_coordinate_graph_mapping
        finite_extend_native_graph_correspondence(1)[OF placed]])
  then show "finite_graph_mapping M (finite_source_proof_graph P (p,d,t)) (p,d,t) H s" .
  have injective: "single_valued ((fset M)\<inverse>)"
    by (simp only: map;
      rule finite_graph_mapping_compose_injective[OF finite_schema_proof_coordinates_injective[OF checked]
        finite_extend_native_graph_correspondence(2)[OF placed]])
  then show "single_valued ((fset M)\<inverse>)" .
  have original: "schema_graph_derives (decode_finite_system (finite_positioned_program P))
    (decode_finite_graph (finite_source_proof_graph P (p,d,t))) (p,d,t) d (decode_finite_term t) {}"
    by (rule finite_source_proof_graph_derives[OF checked])
  show "schema_graph_derives (decode_finite_system (finite_positioned_program P))
    (decode_finite_graph H) s d (decode_finite_term t) {}"
    using schema_graph_mapping_derives[OF original _ injective] mapping
    by (simp only: finite_graph_mapping_exact image_empty)
  have package: "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    using source by (simp only: finite_native_source_correct)
  have included: "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    by (rule finite_extend_native_graph_correct(3)[OF placed])
  have formed: "environment_formed (decode_finite_environment F)"
    using finite_extend_native_graph_correct(2)[OF placed]
    by (simp only: finite_environment_formed_correct)
  show "finite_native_source F u r=Some P"
    using native_package_included[OF package included formed]
    by (simp only: finite_native_source_correct)
qed

text \<open>
  The actual native source and supplied certificate determine success. Checked
  certificates are positioned, assigned actual path coordinates and installed
  through the existing native constructor. Composition retains every original
  proof-and-call node, all source metadata and every indexed edge. The resulting
  native graph has the same closed derivation and preserves the original
  environment. This operation does not require the finite demand evaluator to
  construct the supplied certificate. Application construction and replay,
  physical cost adequacy and complete native development admission remain open.
\<close>

end
