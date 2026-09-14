theory Factor_Finite_Graph_Positioning
  imports Factor_Graph_Positioning Factor_Finite_Graph_Reindexing Factor_Executable_Positions
begin

fun finite_positioned_graph_node :: "'u\<Rightarrow>(local_address,local_address) finite_schema_graph_node\<Rightarrow>
    ('u definition_site,'u definition_site) finite_schema_graph_node" where
  "finite_positioned_graph_node u Finite_Assertion=Finite_Assertion"
| "finite_positioned_graph_node u (Finite_Inference c V)=
    Finite_Inference (u,c) (fimage (map_prod (Pair u) id) V)"

lemma finite_positioned_graph_node_correct:
  "decode_finite_graph_node (finite_positioned_graph_node u A)=positioned_schema_graph_node u (decode_finite_graph_node A)"
  by (cases A) (simp_all add: decode_finite_binding_set_def fimage_fimage comp_def map_prod_def case_prod_unfold)

definition finite_positioned_graph :: "('n\<Rightarrow>'u)\<Rightarrow>
    (local_address,local_address,local_address,'n) finite_derivation_graph\<Rightarrow>
    ('u definition_site,'u definition_site,'u definition_site,'n) finite_derivation_graph" where
  "finite_positioned_graph owner G=finite_reindex_graph
    (\<lambda>n. finite_positioned_graph_node (owner n)) (\<lambda>n. Pair (owner n)) G"

theorem finite_positioned_graph_correct:
  "decode_finite_graph (finite_positioned_graph owner G)=positioned_schema_graph owner (decode_finite_graph G)"
  unfolding finite_positioned_graph_def positioned_schema_graph_def
  by (rule finite_reindex_graph_correct) (rule finite_positioned_graph_node_correct)

lemma finite_positioned_graph_nodes:
  "finite_graph_nodes (finite_positioned_graph owner G)=finite_graph_nodes G"
  by (rule fset_inject[THEN iffD1])
    (simp only: finite_graph_nodes_correct finite_positioned_graph_correct positioned_schema_graph_nodes)

theorem finite_positioned_graph_formed:
  assumes "finite_graph_formed G root"
  shows "finite_graph_formed (finite_positioned_graph owner G) root"
  using positioned_schema_graph_formed[of "decode_finite_graph G" root owner] assms
  by (simp only: finite_graph_formed_correct finite_positioned_graph_correct)

theorem finite_positioned_graph_reading:
  assumes formed: "finite_system_formed P"
    and read: "schema_graph_reading (decode_finite_system P) (decode_finite_graph G) root d t J"
    and owners: "\<And>n. n |\<in>| finite_graph_nodes G \<Longrightarrow> owner n=fst (fst (rel_value J n))"
  shows "schema_graph_reading (decode_finite_system (finite_positioned_program P))
    (decode_finite_graph (finite_positioned_graph owner G)) root d t J"
  by (simp only: finite_positioned_program_correct finite_positioned_graph_correct;
    rule positioned_schema_graph_reading[where owner=owner, OF _ read])
    (use formed in \<open>simp only: finite_system_formed_correct\<close>,
      use owners in \<open>simp only: finite_graph_nodes_correct\<close>)

export_code finite_positioned_graph checking SML

text \<open>
  The actual finite operation pairs each clause, binder and premise socket
  with its source node's specified owner. Exact decoding recovers the complete
  positioned graph. Its meaning contract retains the whole claim assignment
  and requires every owner's agreement with that node's original claimed call.
\<close>

end
