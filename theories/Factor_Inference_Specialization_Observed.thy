theory Factor_Inference_Specialization_Observed
  imports Factor_Inference_Specialization_Contracts Factor_Specialization_Binding_Observed
    Factor_Proof_Claim_Instances Factor_Scheme_Observations
begin

section \<open>The native node and symbolic graph retain one complete specialization\<close>

theorem inference_specialization_observed:
  assumes actual: "inference_specialization_at E pu pr (fst n) (snd n) d c F v r H w t report ds NIs NKs RIs RKs"
    and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E root (map_inference_values pattern_claim_observation G)"
    and node: "(n,Schema_Inference (fst d,c) V)\<in>fset (graph_inferences G)"
    and target: "native_schema_at H w t T"
  shows "set ds=schema_graph_premises G n"
    "schema_clause_specialization (positioned_program P) d (fst d,c) (fset V)
      (rename_schema id (Pair (fst d)) id T)"
    "schema_reference_presents T report"
proof -
  obtain bs where raw: "distinct bs"
    "native_proof_node_at E (fst n) (snd n) (Schema_Inference (fst d,c) (fset_of_list bs))
      (set ds) (set NIs) (set NKs)"
    "specialization_binding_at E pu pr d c F v r H w t report (positioned_binding_rows_term bs) RIs RKs"
    using actual by (auto simp only: inference_specialization_at_def)
  obtain vs where symbolic: "schema_clause_specialization P d c (set vs) T" "distinct vs"
    "positioned_binding_rows_term bs=
      positioned_binding_rows_term (map (\<lambda>(a,p). ((fst d,a),pattern_claim_observation p)) vs)"
    "schema_reference_presents T report"
    by (rule specialization_binding_symbolic[OF raw(3) package target]) (rule that; assumption)
  have observed_node: "(n,Schema_Inference (fst d,c) (fimage (map_prod id pattern_claim_observation) V))
      \<in>fset (graph_inferences (map_inference_values pattern_claim_observation G))"
    using node by (auto simp: map_inference_values_node)
  obtain I K where at: "native_proof_node_at E (fst n) (snd n)
      (Schema_Inference (fst d,c) (fimage (map_prod id pattern_claim_observation) V))
      (schema_graph_premises G n) I K"
    using native_schema_graph_entry[OF graph observed_node] by (simp; blast)
  have same: "fset_of_list bs=fimage (map_prod id pattern_claim_observation) V"
    "set ds=schema_graph_premises G n"
    using native_proof_node_unique[OF raw(2) at] by auto
  have encoded: "bs=map (\<lambda>(a,p). ((fst d,a),pattern_claim_observation p)) vs"
    using symbolic(3) by (simp only: positioned_binding_rows_term_injective)
  have bindings: "map_relation_values pattern_claim_observation (fset V)=
      map_relation_values pattern_claim_observation (rekey_pattern_bindings (Pair (fst d)) (set vs))"
    using arg_cong[OF same(1), of fset]
    by (simp add: encoded fset_of_list.rep_eq fimage.rep_eq image_image
      map_relation_values_def rekey_pattern_bindings_def map_prod_def comp_def case_prod_unfold)
  have injective: "inj pattern_claim_observation" by (auto simp: inj_def)
  have recovered: "fset V=rekey_pattern_bindings (Pair (fst d)) (set vs)"
    using bindings by (simp only: map_relation_values_injective[OF injective])
  show "set ds=schema_graph_premises G n" by (rule same(2))
  show "schema_clause_specialization (positioned_program P) d (fst d,c) (fset V)
      (rename_schema id (Pair (fst d)) id T)"
    using positioned_clause_specializationI[OF native_package_system_formed[OF package] symbolic(1)]
    by (simp only: recovered)
  show "schema_reference_presents T report" by (rule symbolic(4))
qed

text \<open>
  Native node uniqueness fixes the entire discharge relation and binding
  relation. The paired observation's injectivity recovers the original pattern
  values, while the existing positioned-specialization theorem retains every
  ordinary and material socket at the actual definition's owning use.
\<close>

end
