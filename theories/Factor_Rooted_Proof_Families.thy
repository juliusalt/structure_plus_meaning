theory Factor_Rooted_Proof_Families
  imports Factor_Proof_Node_Code Fixed_Second_Projections
begin

locale rooted_proof_code_family =
  fixes E :: "local_address option artifact_environment"
    and G :: "local_address option native_derivation_graph"
    and root :: "local_address option definition_site"
    and R :: "local_address option\<Rightarrow>exact_artifact"
    and L :: "local_address option\<Rightarrow>(local_address\<times>exact_artifact) set"
    and C :: "local_address option\<Rightarrow>(local_address\<times>local_address option definition_site) set"
    and I :: "local_address option\<Rightarrow>local_address set"
    and K :: "local_address option\<Rightarrow>local_address set"
  assumes environment: "environment_formed E" and formed: "schema_graph_formed G root"
    and metadata: "graph_metadata_at E G"
    and roots: "\<forall>n\<in>schema_graph_nodes G. snd n=[]"
    and codes: "\<forall>n N. (n,N)\<in>fset (graph_inferences G) \<longrightarrow>
      proof_node_code_for N (schema_graph_premises G n) (R (fst n)) (L (fst n)) (C (fst n)) (I (fst n)) (K (fst n))"
begin

abbreviation uses where "uses \<equiv> fst ` schema_graph_nodes G"
abbreviation node where "node u \<equiv> rel_value (fset (graph_inferences G)) (u,[])"
abbreviation premise_rows where "premise_rows u \<equiv> schema_graph_premises G (u,[])"

lemma finite_uses: "finite uses" by simp

lemma site_shape:
  "n\<in>schema_graph_nodes G \<Longrightarrow> (fst n,[])=n"
  by (rule fixed_second_shape[OF roots])

lemma use_site:
  "u\<in>uses \<Longrightarrow> (u,[])\<in>schema_graph_nodes G"
  by (rule fixed_second_image_member[OF roots])

lemma node_entry:
  "u\<in>uses \<Longrightarrow> ((u,[]),node u)\<in>fset (graph_inferences G)"
  by (rule schema_graph_node_value[OF formed use_site])

lemma code:
  assumes "u\<in>uses"
  shows "proof_node_code_for (node u) (premise_rows u) (R u) (L u) (C u) (I u) (K u)"
  using codes node_entry[OF assms] by auto

lemma artifact_formation: "\<forall>u\<in>uses. exact_formed (R u)"
  using proof_node_code_properties(1)[OF code] by blast

lemma artifact_roots: "\<forall>u\<in>uses. []\<in>rra_carrier (object_structure (R u))"
  using proof_node_code_properties(2)[OF code] by blast

lemma profiles: "\<forall>u\<in>uses. reference_table_formed (L u) (C u)"
  using proof_node_code_properties(3)[OF code] by blast

lemma bounds:
  "\<forall>u\<in>uses. rel_dom (L u)\<union>rel_dom (C u)\<subseteq>rra_carrier (object_structure (R u))"
  using proof_node_code_properties(4)[OF code] by blast

lemma targets:
  "\<forall>u\<in>uses. \<forall>d\<in>rel_ran (C u). d\<in>environment_positions E \<or>
    (fst d\<in>uses \<and> snd d\<in>rra_carrier (object_structure (R (fst d))))"
proof (intro ballI)
  fix u d assume member: "u\<in>uses" and dependency: "d\<in>rel_ran (C u)"
  have complete: "rel_ran (C u)=proof_node_reference_sites (node u) (premise_rows u)"
    using code[OF member] by (simp only: proof_node_code_for_def; blast)
  have inputs: "graph_node_inputs_at E (premise_rows u) (node u)"
    using metadata node_entry[OF member] by (auto simp: graph_metadata_at_def)
  have scope: "proof_node_reference_sites (node u) (premise_rows u)\<subseteq>
    environment_positions E\<union>schema_graph_nodes G"
    by (rule proof_node_reference_boundary[OF inputs schema_graph_premises_targets[OF formed]])
  have alternative: "d\<in>environment_positions E \<or> d\<in>schema_graph_nodes G"
    using complete scope dependency by blast
  show "d\<in>environment_positions E \<or>
    (fst d\<in>uses \<and> snd d\<in>rra_carrier (object_structure (R (fst d))))"
  proof (cases "d\<in>schema_graph_nodes G")
    case True
    have use: "fst d\<in>uses" by (rule imageI[OF True])
    have address: "snd d=[]" using roots True by blast
    show ?thesis using use artifact_roots[rule_format, OF use] by (simp add: address)
  next
    case False
    then show ?thesis using alternative by blast
  qed
qed

lemma installed:
  assumes environment: "environment_formed F"
    and components: "\<forall>u\<in>uses. artifact_at F u (R u) \<and> syntax_references F u (L u) (C u)"
  shows "native_schema_graph_at F root G"
  unfolding native_schema_graph_at_def
proof (intro conjI allI impI)
  show "schema_graph_formed G root" by (rule formed)
  fix n N assume row: "(n,N)\<in>fset (graph_inferences G)"
  have inside: "n\<in>schema_graph_nodes G" using row by (auto simp: schema_graph_nodes_def rel_dom_def)
  have use: "fst n\<in>uses" by (rule imageI[OF inside])
  have source: "proof_node_code_for N (schema_graph_premises G n)
    (R (fst n)) (L (fst n)) (C (fst n)) (I (fst n)) (K (fst n))"
    using codes row by blast
  have art: "artifact_at F (fst n) (R (fst n))"
    and refs: "syntax_references F (fst n) (L (fst n)) (C (fst n))"
    using components use by blast+
  have native: "native_proof_node_at F (fst n) [] N (schema_graph_premises G n) (I (fst n)) (K (fst n))"
    by (rule proof_node_code_recovers[OF source environment art refs])
  have address: "snd n=[]" using roots inside by blast
  show "\<exists>I K. native_proof_node_at F (fst n) (snd n) N (schema_graph_premises G n) I K"
    using native by (simp only: address; blast)
qed

end

text \<open>
  A complete rooted graph and one exact code contract per original node
  determine the artifact, reference and recovery obligations for the whole
  family. The same content supports the original existence construction and
  an executable compiler supplying actual blocks. Installing every component
  recovers every original node and indexed premise, including shared targets.
\<close>

end
