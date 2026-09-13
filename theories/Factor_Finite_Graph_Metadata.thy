theory Factor_Finite_Graph_Metadata
  imports Factor_Executable_Packages Factor_Executable_Graphs Factor_Graph_Metadata
begin

fun finite_graph_node_inputs_at ::
    "'u finite_artifact_environment\<Rightarrow>('u definition_site\<times>'n) fset\<Rightarrow>
      ('u definition_site,'u definition_site) finite_schema_graph_node\<Rightarrow>bool" where
  "finite_graph_node_inputs_at E D Finite_Assertion=(D={||})"
| "finite_graph_node_inputs_at E D (Finite_Inference c V)=(
    c |\<in>| finite_environment_positions E \<and> finite_relation_functional V \<and>
    fBall V (\<lambda>(a,t). a |\<in>| finite_environment_positions E \<and> finite_term_formed t) \<and>
    fimage fst D |\<subseteq>| finite_environment_positions E)"

theorem finite_graph_node_inputs_at_exact:
  "finite_graph_node_inputs_at E D N=graph_node_inputs_at (decode_finite_environment E)
    (fset D) (decode_finite_graph_node N)"
  by (cases N) (simp_all only: finite_graph_node_inputs_at.simps decode_finite_graph_node.simps
    graph_node_inputs_at.simps decode_finite_binding_set_values decode_finite_term_bindings_functional
    decode_finite_term_bindings_all finite_term_formed_correct finite_environment_positions_correct
    rel_dom_image fimage.rep_eq less_eq_fset.rep_eq fset_inject[symmetric] bot_fset.rep_eq)

export_code finite_graph_node_inputs_at checking SML

text \<open>
  Clause references, binding keys and premise sockets are checked against
  positions in the actual source environment. Complete bound terms retain
  their original formation condition. Proof targets may be placed later.
  This operation checks metadata; it does not establish a derivation.
\<close>

end
