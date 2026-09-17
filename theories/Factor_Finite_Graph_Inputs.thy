theory Factor_Finite_Graph_Inputs
  imports Factor_Finite_Graph_Metadata Factor_Finite_Graph_Transport
begin

definition finite_graph_metadata_at where
  "finite_graph_metadata_at E G=fBall (finite_graph_inferences G)
    (\<lambda>(n,N). finite_graph_node_inputs_at E (finite_graph_premises G n) N)"

theorem finite_graph_metadata_at_exact:
  "finite_graph_metadata_at E G=graph_metadata_at (decode_finite_environment E) (decode_finite_graph G)"
  by (simp only: finite_graph_metadata_at_def graph_metadata_at_def decode_finite_graph_fields
    map_relation_values_member Ball_def split_paired_All case_prod_conv
    finite_graph_node_inputs_at_exact finite_graph_premises_correct; blast)

lemma finite_graph_metadata_rename:
  assumes metadata: "finite_graph_metadata_at E G" and formed: "finite_graph_formed G root"
    and injective: "inj_on h (fset (finite_graph_nodes G))"
  shows "finite_graph_metadata_at E (finite_rename_graph h G)"
  using graph_metadata_rename[of "decode_finite_environment E" "decode_finite_graph G" root h]
    metadata formed injective
  by (simp only: finite_graph_metadata_at_exact finite_rename_graph_exact
    finite_graph_formed_correct finite_graph_nodes_correct)

definition finite_graph_construction_ready where
  "finite_graph_construction_ready E G root=(finite_environment_formed E \<and>
    finite_graph_formed G root \<and> finite_graph_metadata_at E G)"

theorem finite_graph_construction_ready_exact:
  "finite_graph_construction_ready E G root=(environment_formed (decode_finite_environment E) \<and>
    schema_graph_formed (decode_finite_graph G) root \<and>
    graph_metadata_at (decode_finite_environment E) (decode_finite_graph G))"
  by (simp only: finite_graph_construction_ready_def finite_environment_formed_correct
    finite_graph_formed_correct finite_graph_metadata_at_exact)

text \<open>
  The complete graph supplies every metadata inspection. Available positions
  come from the original actual environment. These exact executable checks
  retain graph formation separately from source metadata and establish no
  inference validity or proof-claim judgment.
\<close>

end
