theory Finite_Bijective_Relations
  imports RRA_Finite_Artifacts Finite_Function_Graphs Finite_Set_Composition
begin

lemma finite_value_image_relation:
  "fset (fimage (map_prod id f) R)=map_relation_values f (fset R)"
  by (auto simp: fimage.rep_eq map_relation_values_def map_prod_def)

definition finite_bijective_relation where
  "finite_bijective_relation A B R=(finite_relation_functional R \<and>
    finite_relation_functional (fimage prod.swap R) \<and>
    fimage fst R=A \<and> fimage snd R=B)"

theorem finite_bijective_relation_correct:
  "finite_bijective_relation A B R \<longleftrightarrow>
    exact_map (fset A) (fset B) (fset R) \<and> single_valued ((fset R)\<inverse>)"
  by (auto simp: finite_bijective_relation_def finite_relation_functional_correct
    finite_relation_converse relation_swap_image exact_map_def rel_dom_image rel_ran_image fset_inject[symmetric])

theorem finite_bijective_relation_graph:
  "finite_bijective_relation A B R \<longleftrightarrow>
    (\<exists>g. inj_on g (fset A) \<and> g ` fset A=fset B \<and> fset R=graph_map (fset A) g)"
proof
  assume exact: "finite_bijective_relation A B R"
  have functional: "single_valued (fset R)" and domain: "rel_dom (fset R)=fset A"
    and range: "rel_ran (fset R)=fset B" and inverse: "single_valued ((fset R)\<inverse>)"
    using exact by (simp only: finite_bijective_relation_correct exact_map_def; blast)+
  have graph: "fset R=graph_map (fset A) (rel_value (fset R))"
    using single_valued_graph[OF functional] by (simp only: domain)
  have inverse_graph: "single_valued ((graph_map (fset A) (rel_value (fset R)))\<inverse>)"
    using inverse graph by metis
  have range_graph: "rel_ran (graph_map (fset A) (rel_value (fset R)))=fset B"
    using range graph by metis
  show "\<exists>g. inj_on g (fset A) \<and> g ` fset A=fset B \<and> fset R=graph_map (fset A) g"
  proof (rule exI[of _ "rel_value (fset R)"], intro conjI)
    show "inj_on (rel_value (fset R)) (fset A)"
      using inverse_graph by (simp only: graph_map_converse_functional)
    show "rel_value (fset R) ` fset A=fset B"
      using range_graph by (simp only: graph_map_ran)
    show "fset R=graph_map (fset A) (rel_value (fset R))" by (rule graph)
  qed
next
  assume "\<exists>g. inj_on g (fset A) \<and> g ` fset A=fset B \<and> fset R=graph_map (fset A) g"
  then show "finite_bijective_relation A B R"
    by (auto simp: finite_bijective_relation_correct exact_map_def graph_map_dom graph_map_ran
      graph_map_single_valued graph_map_converse_functional graph_map_finite)
qed

export_code finite_bijective_relation checking SML

theorem finite_bijective_relation_value_map:
  assumes injective: "inj f"
  shows "finite_bijective_relation A (fimage f B) (fimage (map_prod id f) R)=
    finite_bijective_relation A B R"
proof -
  have mapped: "fset (fimage (map_prod id f) R)=map_relation_values f (fset R)"
    by (rule finite_value_image_relation)
  have functional: "finite_relation_functional (fimage (map_prod id f) R)=finite_relation_functional R"
    by (simp only: finite_relation_functional_correct mapped map_relation_values_functional[OF injective])
  have equal: "f x=f y \<longleftrightarrow> x=y" for x y using injective by (simp add: inj_eq)
  have inverse: "finite_relation_functional (fimage prod.swap (fimage (map_prod id f) R))=
    finite_relation_functional (fimage prod.swap R)"
    by (simp add: finite_relation_functional_def fimage_fimage equal map_prod_def prod.swap_def split_def)
  have domain: "fimage fst (fimage (map_prod id f) R)=fimage fst R"
    by (rule finite_value_image_domain)
  have range: "fimage snd (fimage (map_prod id f) R)=fimage f (fimage snd R)"
    by (rule finite_value_image_range)
  have reflect: "fimage f X=fimage f Y \<longleftrightarrow> X=Y" for X Y
    by (rule fset_image_equality[OF injective])
  show ?thesis by (simp only: finite_bijective_relation_def functional inverse domain range reflect)
qed

end
