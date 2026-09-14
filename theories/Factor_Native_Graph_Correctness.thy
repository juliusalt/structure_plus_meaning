theory Factor_Native_Graph_Correctness
  imports Factor_Native_Graph_Assessment Factor_Finite_Graph_Correspondence
begin

lemma native_graph_constructor_result:
  assumes extended: "finite_extend_native_graph E G root=Some (F,M,r,H)"
    and facet: "f<5"
  shows "native_graph_result_condition f (E,G,root) (Some (F,M,r,H))"
proof -
  have facts:
    "finite_graph_construction_ready E G root"
    "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "finite_environment_agrees_on E F (finite_environment_uses E)"
    "M=fimage (\<lambda>n. (n,finite_graph_coordinates E G n)) (finite_graph_nodes G)"
    "r=finite_graph_coordinates E G root"
    "H=finite_rename_graph (finite_graph_coordinates E G) G"
    "inj_on (finite_graph_coordinates E G) (fset (finite_graph_nodes G))"
    "image fst (fset (finite_graph_nodes H))\<inter>fset (finite_environment_uses E)={}"
    "H |\<in>| finite_native_graph_readings F r"
    by (rule finite_extend_native_graph_correct[OF extended])+
  have mapping: "finite_graph_mapping M G root H r"
    by (rule finite_extend_native_graph_correspondence(1)[OF extended])
  have injective: "single_valued ((fset M)\<inverse>)"
    by (rule finite_extend_native_graph_correspondence(2)[OF extended])
  show ?thesis
    by (simp only: native_graph_result_condition_def case_prod_conv;
      rule finite_native_graph_result_conditions[OF facts(2) facts(10) mapping facts(3) facts(4)
        facts(9) injective facet])

qed

theorem native_graph_constructor_all_conditions:
  assumes facet: "f<6"
  shows "native_graph_condition f (native_graph_method 0) X"
proof -
  obtain E G root where input: "X=(E,G,root)" by (cases X) auto
  show ?thesis
  proof (cases "finite_graph_construction_ready E G root")
    case True
    obtain F M r H where result: "finite_extend_native_graph E G root=Some (F,M,r,H)"
      using True by (simp only: finite_extend_native_graph_domain[symmetric]; blast)
    have ready: "native_graph_ready_condition X"
      using True by (simp only: native_graph_ready_exact[symmetric] input native_graph_ready_def case_prod_conv)
    have conditions: "native_graph_result_condition k X (native_graph_method 0 X)" if "k<5" for k
      using native_graph_constructor_result[OF result that]
      by (simp only: input native_graph_method_original result)
    show ?thesis using ready conditions facet by (auto simp: native_graph_condition_def; arith)
  next
    case False
    have result: "finite_extend_native_graph E G root=None"
      using False finite_extend_native_graph_domain[of E G root]
      by (cases "finite_extend_native_graph E G root") auto
    have unready: "\<not>native_graph_ready_condition X"
      using False by (simp add: native_graph_ready_exact[symmetric] input native_graph_ready_def)
    show ?thesis using unready facet
      by (auto simp: native_graph_condition_def input native_graph_method_original result; arith)
  qed
qed

end
