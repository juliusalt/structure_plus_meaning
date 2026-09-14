theory Factor_Native_Certificate_Correctness
  imports Factor_Native_Certificate_Assessment
begin

lemma native_certificate_rows_functional:
  "finite_relation_functional (native_certificate_rows P T)"
  by (simp only: native_certificate_rows_def finite_relation_functional_correct finite_function_graph;
    rule graph_map_single_valued)

lemma native_certificate_rows_family:
  "native_certificate_family (native_certificate_rows P T)=T"
  by (simp add: native_certificate_family_def native_certificate_rows_def native_certificate_nodes_def
    fimage_fimage comp_def case_prod_unfold)

lemma native_certificate_node_conditions:
  "native_certificate_row_condition 0 P (n,native_certificate_node_result P n)"
  "native_certificate_row_condition 1 P (n,native_certificate_node_result P n)"
  "native_certificate_row_condition 2 P (n,native_certificate_node_result P n)"
  by (subst native_certificate_row_assessment_exact[symmetric]; cases n;
    auto simp: native_certificate_node_result_def native_certificate_row_assessment_def
      native_certificate_row_inspect_def finite_schema_coordinate_graph_mapping
      finite_schema_proof_coordinates_member Let_def)+

lemma native_certificate_rows_conditions:
  assumes "f<3"
  shows "\<forall>row\<in>fset (native_certificate_rows P T). native_certificate_row_condition f P row"
proof -
  have alternatives: "f=0 \<or> f=1 \<or> f=2" using assms by arith
  show ?thesis using alternatives native_certificate_node_conditions[of P]
    by (auto simp: native_certificate_rows_def finite_function_graph_member split: prod.splits)
qed

theorem native_certificate_base_from_all_conditions:
  assumes facet: "f<7"
  shows "native_certificate_condition_on f original (native_certificate_base_from original)"
proof -
  have alternatives: "f=0 \<or> f=1 \<or> f=2 \<or> f=3 \<or> f=4 \<or> f=5 \<or> f=6" using facet by arith
  from alternatives show ?thesis
    apply (elim disjE; cases original)
    apply (auto simp: native_certificate_condition_on_def native_certificate_base_from_def
      native_certificate_result_condition_def native_certificate_rows_family
      native_certificate_rows_functional finite_relation_functional_correct[symmetric]
      native_certificate_rows_conditions Let_def split: prod.splits)
    done
qed

theorem native_certificate_constructor_all_conditions:
  assumes "f<7"
  shows "native_certificate_condition f (native_certificate_method 0) X"
  by (simp only: native_certificate_condition_def native_certificate_method_original native_certificate_base_def;
    rule native_certificate_base_from_all_conditions[OF assms])

text \<open>
  The complete constructor satisfies the seven stated conditions for every
  original native source and request. Exact family recovery preserves each
  complete certificate-and-call node. Actual path representatives and complete
  graph maps preserve every original graph. This theorem does not select the
  construction among undeclared approaches or supply native artifact placement.
\<close>

end
