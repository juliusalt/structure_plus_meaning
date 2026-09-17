theory Factor_Finite_Graph_Installation
  imports Factor_Finite_Graph_Codes Factor_Rooted_Proof_Families
    Factor_Finite_Reference_Environments RRA_Finite_Environment_Preservation
begin

definition finite_install_graph_codes :: "local_address option finite_artifact_environment\<Rightarrow>
    (local_address option definition_site\<times>local_address option finite_syntax_block) list\<Rightarrow>
    local_address option finite_artifact_environment" where
  "finite_install_graph_codes E rows=(let B=\<lambda>n. the (map_of rows n) in
    finite_fresh_reference_sequence E (map (\<lambda>row. fst (fst row)) rows)
      (\<lambda>u. finite_block_artifact (B (u,[])))
      (\<lambda>u. finite_block_literals (B (u,[])))
      (\<lambda>u. finite_block_callees (B (u,[]))))"

theorem finite_install_graph_codes_correct:
  assumes ready: "finite_graph_construction_ready E G root"
    and roots: "\<forall>n\<in>fset (finite_graph_nodes G). snd n=[]"
    and fresh: "image fst (fset (finite_graph_nodes G))\<inter>fset (finite_environment_uses E)={}"
    and compiled: "finite_compile_graph_nodes E G=Some rows"
  shows "let F=finite_install_graph_codes E rows in
    finite_environment_formed F \<and>
    environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
    finite_environment_agrees_on E F (finite_environment_uses E) \<and>
    G |\<in>| finite_native_graph_readings F root"
proof -
  let ?G="decode_finite_graph G"
  let ?E="decode_finite_environment E"
  let ?F="finite_install_graph_codes E rows"
  let ?B="\<lambda>n. the (map_of rows n)"
  let ?ds="sorted_list_of_fset (finite_graph_nodes G)"
  let ?us="map (\<lambda>row. fst (fst row)) rows"
  let ?R="\<lambda>u. finite_block_artifact (?B (u,[]))"
  let ?L="\<lambda>u. finite_block_literals (?B (u,[]))"
  let ?C="\<lambda>u. finite_block_callees (?B (u,[]))"
  let ?I="\<lambda>u. fset (finite_block_interior (?B (u,[])))"
  let ?K="\<lambda>u. fset (finite_block_slots (?B (u,[])))"
  have ef: "finite_environment_formed E" and gf: "finite_graph_formed G root"
    and metadata: "finite_graph_metadata_at E G"
    using ready by (simp only: finite_graph_construction_ready_def; blast)+
  have environment: "environment_formed ?E" using ef by (simp only: finite_environment_formed_correct)
  have graph: "schema_graph_formed ?G root" using gf by (simp only: finite_graph_formed_correct)
  have inputs: "graph_metadata_at ?E ?G" using metadata by (simp only: finite_graph_metadata_at_exact)
  have at_roots: "\<forall>n\<in>schema_graph_nodes ?G. snd n=[]"
    using roots by (simp only: finite_graph_nodes_correct)
  have keys: "map fst rows=?ds" by (rule finite_compile_graph_nodes_correct(1)[OF gf compiled])
  have codes: "\<forall>n N. (n,N)\<in>fset (graph_inferences ?G) \<longrightarrow>
    proof_node_code_for N (schema_graph_premises ?G n)
      (decode_finite_object (?R (fst n)))
      (map_relation_values decode_finite_object (fset (?L (fst n))))
      (fset (?C (fst n))) (?I (fst n)) (?K (fst n))"
  proof (intro allI impI)
    fix n N assume row: "(n,N)\<in>fset (graph_inferences ?G)"
    obtain M where member: "(n,M) |\<in>| finite_graph_inferences G" and decoded: "N=decode_finite_graph_node M"
      using row by (simp only: decode_finite_graph_fields map_relation_values_member; blast)
    have inside: "n\<in>schema_graph_nodes ?G"
      using row by (auto simp: schema_graph_nodes_def rel_dom_def)
    have site: "(fst n,[])=n" by (rule fixed_second_shape[OF at_roots inside])
    show "proof_node_code_for N (schema_graph_premises ?G n)
      (decode_finite_object (?R (fst n)))
      (map_relation_values decode_finite_object (fset (?L (fst n))))
      (fset (?C (fst n))) (?I (fst n)) (?K (fst n))"
      using finite_compile_graph_nodes_correct(2)[OF gf compiled, rule_format, OF member]
      by (simp only: Let_def site finite_graph_premises_correct decoded)
  qed
  interpret family: rooted_proof_code_family ?E ?G root
    "\<lambda>u. decode_finite_object (?R u)"
    "\<lambda>u. map_relation_values decode_finite_object (fset (?L u))"
    "\<lambda>u. fset (?C u)" ?I ?K
    by (rule rooted_proof_code_family.intro[OF environment graph inputs at_roots codes])
  have sequence: "?us=map fst ?ds"
    using keys by (simp only: keys[symmetric] map_map comp_def)
  have uses: "set ?us=family.uses" by (simp add: sequence finite_graph_nodes_correct)
  have roots_list: "\<forall>n\<in>set ?ds. snd n=[]" using roots by simp
  have injective: "inj_on fst (set ?ds)" by (rule fixed_second_first_injective[OF roots_list])
  have unique: "distinct ?us" using injective by (simp add: sequence distinct_map)
  have separate: "set ?us\<inter>fset (finite_environment_uses E)={}"
    using fresh by (simp only: uses finite_graph_nodes_correct)
  have artifacts: "\<forall>u\<in>set ?us. finite_exact_formed (?R u)"
    using family.artifact_formation by (simp only: uses finite_exact_formed_correct)
  have profiles: "\<forall>u\<in>set ?us. reference_table_formed
    (map_relation_values decode_finite_object (fset (?L u))) (fset (?C u))"
    using family.profiles by (simp only: uses)
  have bounds: "\<forall>u\<in>set ?us. rel_dom (fset (?L u))\<union>rel_dom (fset (?C u))\<subseteq>
    fset (finite_carrier (finite_structure (?R u)))"
    using family.bounds by (simp only: uses map_relation_values_domain
      decode_finite_object_selectors decode_finite_structure_fields)
  have targets: "\<forall>u\<in>set ?us. \<forall>d\<in>rel_ran (fset (?C u)). d\<in>environment_positions ?E \<or>
    (fst d\<in>set ?us \<and> snd d\<in>fset (finite_carrier (finite_structure (?R (fst d)))))"
    using family.targets by (simp only: uses decode_finite_object_selectors decode_finite_structure_fields)
  have installation: "?F=finite_fresh_reference_sequence E ?us ?R ?L ?C"
    by (simp add: finite_install_graph_codes_def Let_def)
  have actual: "finite_environment_formed ?F"
    "environment_included ?E (decode_finite_environment ?F)"
    "\<forall>u\<in>set ?us. artifact_at (decode_finite_environment ?F) u (decode_finite_object (?R u)) \<and>
      syntax_references (decode_finite_environment ?F) u
        (map_relation_values decode_finite_object (fset (?L u))) (fset (?C u))"
    "finite_environment_agrees_on E ?F (finite_environment_uses E)"
    using finite_fresh_reference_sequence_properties[OF ef unique separate artifacts profiles bounds targets]
    by (simp only: Let_def installation[symmetric] finite_environment_agrees_on_correct; blast)+
  have formed: "environment_formed (decode_finite_environment ?F)"
    using actual(1) by (simp only: finite_environment_formed_correct)
  have components: "\<forall>u\<in>family.uses.
    artifact_at (decode_finite_environment ?F) u (decode_finite_object (?R u)) \<and>
    syntax_references (decode_finite_environment ?F) u
      (map_relation_values decode_finite_object (fset (?L u))) (fset (?C u))"
    using actual(3) by (simp only: uses)
  have recovered: "G |\<in>| finite_native_graph_readings ?F root"
    by (simp only: finite_native_graph_readings_correct; rule family.installed[OF formed components])
  show ?thesis using actual(1,2,4) recovered by (simp only: Let_def; blast)
qed

text \<open>
  Every compiled node artifact is present before its complete reference
  family is installed. References may reach original source positions or
  any new graph node, independent of installation order. The shared rooted
  proof-family contract supplies every formation and recovery prerequisite.
  The final native reader recovers the complete original graph, and all old
  artifacts and outgoing bindings agree exactly with the original environment.
\<close>

end
