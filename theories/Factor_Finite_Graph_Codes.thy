theory Factor_Finite_Graph_Codes
  imports Factor_Finite_Graph_Coordinates Factor_Finite_Proof_Nodes
    Factor_Executable_Realization Keyed_Option_Maps
begin

definition finite_compile_graph_node :: "local_address option finite_artifact_environment\<Rightarrow>
    local_address option finite_native_derivation_graph\<Rightarrow>local_address option definition_site\<Rightarrow>
    local_address option finite_syntax_block option" where
  "finite_compile_graph_node E G n=(case finite_relation_option (finite_graph_inferences G) n of
    None \<Rightarrow> None | Some N \<Rightarrow> finite_compile_proof_node E N (finite_graph_premises G n))"

definition finite_compile_graph_nodes where
  "finite_compile_graph_nodes E G=keyed_option_map (finite_compile_graph_node E G)
    (sorted_list_of_fset (finite_graph_nodes G))"

lemma finite_rooted_graph_node_ready:
  assumes ready: "finite_graph_construction_ready E G root"
    and roots: "\<forall>n\<in>fset (finite_graph_nodes G). snd n=[]"
    and member: "(n,N) |\<in>| finite_graph_inferences G"
  shows "finite_proof_node_ready E N (finite_graph_premises G n)"
proof -
  have ef: "finite_environment_formed E" and gf: "finite_graph_formed G root"
    and metadata: "finite_graph_metadata_at E G"
    using ready by (simp only: finite_graph_construction_ready_def; blast)+
  have graph: "schema_graph_formed (decode_finite_graph G) root"
    using gf by (simp only: finite_graph_formed_correct)
  have inputs: "finite_graph_node_inputs_at E (finite_graph_premises G n) N"
    using metadata member by (auto simp: finite_graph_metadata_at_def)
  have functional: "finite_relation_functional (finite_graph_premises G n)"
    using schema_graph_premises_functional[OF graph, of n]
    by (simp only: finite_relation_functional_correct finite_graph_premises_correct)
  have addresses: "octets_formed (snd m)" if edge: "(s,m) |\<in>| finite_graph_premises G n" for s m
  proof -
    have actual: "(s,m)\<in>schema_graph_premises (decode_finite_graph G) n"
      using edge by (simp only: finite_graph_premises_correct)
    have inside: "m\<in>schema_graph_nodes (decode_finite_graph G)"
      by (rule subsetD[OF schema_graph_premises_targets[OF graph] rel_ranI[OF actual]])
    have address: "snd m=[]" using roots inside by (simp only: finite_graph_nodes_correct; blast)
    show ?thesis by (simp add: address octets_formed_def)
  qed
  show ?thesis using ef inputs functional addresses by (auto simp: finite_proof_node_ready_def)
qed

theorem finite_compile_graph_node_correct:
  assumes functional: "finite_relation_functional (finite_graph_inferences G)"
    and member: "(n,N) |\<in>| finite_graph_inferences G"
    and compiled: "finite_compile_graph_node E G n=Some B"
  shows "finite_proof_node_ready E N (finite_graph_premises G n)"
    "proof_node_code_for (decode_finite_graph_node N) (fset (finite_graph_premises G n))
      (decode_finite_object (finite_block_artifact B))
      (map_relation_values decode_finite_object (fset (finite_block_literals B)))
      (fset (finite_block_callees B)) (fset (finite_block_interior B)) (fset (finite_block_slots B))"
proof -
  have selected: "finite_relation_option (finite_graph_inferences G) n=Some N"
    by (simp only: finite_relation_option_correct[OF functional]; rule member)
  have actual: "finite_compile_proof_node E N (finite_graph_premises G n)=Some B"
    using compiled by (simp only: finite_compile_graph_node_def selected option.case)
  show "finite_proof_node_ready E N (finite_graph_premises G n)"
    "proof_node_code_for (decode_finite_graph_node N) (fset (finite_graph_premises G n))
      (decode_finite_object (finite_block_artifact B))
      (map_relation_values decode_finite_object (fset (finite_block_literals B)))
      (fset (finite_block_callees B)) (fset (finite_block_interior B)) (fset (finite_block_slots B))"
    by (rule finite_compile_proof_node_correct[OF actual])+
qed

theorem finite_compile_graph_nodes_total:
  assumes ready: "finite_graph_construction_ready E G root"
    and roots: "\<forall>n\<in>fset (finite_graph_nodes G). snd n=[]"
  shows "\<exists>rows. finite_compile_graph_nodes E G=Some rows"
proof -
  have functional: "finite_relation_functional (finite_graph_inferences G)"
    using ready by (simp only: finite_graph_construction_ready_def finite_graph_formed_def; blast)
  have each: "\<exists>B. finite_compile_graph_node E G n=Some B" if inside: "n |\<in>| finite_graph_nodes G" for n
  proof -
    obtain N where member: "(n,N) |\<in>| finite_graph_inferences G"
      using inside by (auto simp: finite_graph_nodes_def)
    have selected: "finite_relation_option (finite_graph_inferences G) n=Some N"
      by (simp only: finite_relation_option_correct[OF functional]; rule member)
    have input: "finite_proof_node_ready E N (finite_graph_premises G n)"
      by (rule finite_rooted_graph_node_ready[OF ready roots member])
    obtain B where code: "finite_compile_proof_node E N (finite_graph_premises G n)=Some B"
      using input by (simp only: finite_compile_proof_node_domain[symmetric]; blast)
    show ?thesis by (rule exI[of _ B]) (simp only: finite_compile_graph_node_def selected option.case code)
  qed
  have available: "finite_compile_graph_nodes E G\<noteq>None"
    using each by (auto simp: finite_compile_graph_nodes_def keyed_option_map_domain)
  show ?thesis using available by (cases "finite_compile_graph_nodes E G") auto
qed

theorem finite_compile_graph_nodes_correct:
  assumes formed: "finite_graph_formed G root" and compiled: "finite_compile_graph_nodes E G=Some rows"
  shows "map fst rows=sorted_list_of_fset (finite_graph_nodes G)"
    "\<forall>n N. (n,N) |\<in>| finite_graph_inferences G \<longrightarrow>
      (let B=the (map_of rows n) in
        proof_node_code_for (decode_finite_graph_node N) (fset (finite_graph_premises G n))
          (decode_finite_object (finite_block_artifact B))
          (map_relation_values decode_finite_object (fset (finite_block_literals B)))
          (fset (finite_block_callees B)) (fset (finite_block_interior B)) (fset (finite_block_slots B)))"
proof -
  have actual: "keyed_option_map (finite_compile_graph_node E G) (sorted_list_of_fset (finite_graph_nodes G))=Some rows"
    using compiled by (simp only: finite_compile_graph_nodes_def)
  show "map fst rows=sorted_list_of_fset (finite_graph_nodes G)"
    by (rule keyed_option_map_result(1)[OF actual])
  have functional: "finite_relation_functional (finite_graph_inferences G)"
    using formed by (simp only: finite_graph_formed_def; blast)
  show "\<forall>n N. (n,N) |\<in>| finite_graph_inferences G \<longrightarrow>
      (let B=the (map_of rows n) in
        proof_node_code_for (decode_finite_graph_node N) (fset (finite_graph_premises G n))
          (decode_finite_object (finite_block_artifact B))
          (map_relation_values decode_finite_object (fset (finite_block_literals B)))
          (fset (finite_block_callees B)) (fset (finite_block_interior B)) (fset (finite_block_slots B)))"
  proof (intro allI impI)
    fix n N assume member: "(n,N) |\<in>| finite_graph_inferences G"
    have inside: "n\<in>set (sorted_list_of_fset (finite_graph_nodes G))"
      using imageI[OF member, of fst] by (simp add: finite_graph_nodes_def)
    have lookup: "finite_compile_graph_node E G n=Some (the (map_of rows n))"
      by (rule keyed_option_map_lookup[OF actual inside])
    show "let B=the (map_of rows n) in
        proof_node_code_for (decode_finite_graph_node N) (fset (finite_graph_premises G n))
          (decode_finite_object (finite_block_artifact B))
          (map_relation_values decode_finite_object (fset (finite_block_literals B)))
          (fset (finite_block_callees B)) (fset (finite_block_interior B)) (fset (finite_block_slots B))"
      by (simp only: Let_def; rule finite_compile_graph_node_correct(2)[OF functional member lookup])
  qed
qed

export_code finite_compile_graph_nodes checking SML

text \<open>
  Every original graph key selects its actual metadata through the shared
  finite relation reader. The complete keyed traversal preserves all node
  identities and compiles one actual proof-node block for each of them.
  Missing metadata cannot become an implicit assertion. Installation of the
  complete artifact and reference family remains a separate operation.
\<close>

end
