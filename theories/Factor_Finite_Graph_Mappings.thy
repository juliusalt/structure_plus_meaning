theory Factor_Finite_Graph_Mappings
  imports Factor_Finite_Graph_Transport Factor_Graph_Mappings Finite_Indexed_Relation_Images
begin

definition finite_mapped_graph :: "('n\<times>'m) fset\<Rightarrow>('a,'s,'c,'n) finite_derivation_graph\<Rightarrow>
    ('a,'s,'c,'m) finite_derivation_graph" where
  "finite_mapped_graph M G=\<lparr>
    finite_graph_inferences=finite_edge_compose (fimage prod.swap M) (finite_graph_inferences G),
    finite_graph_discharges=finite_indexed_relation_image M (finite_graph_discharges G)\<rparr>"

definition finite_graph_mapping where
  "finite_graph_mapping M G root H r=(finite_relation_functional M \<and>
    fimage fst M=finite_graph_nodes G \<and> (root,r) |\<in>| M \<and>
    finite_graph_inferences H=finite_edge_compose (fimage prod.swap M) (finite_graph_inferences G) \<and>
    finite_graph_discharges H=finite_indexed_relation_image M (finite_graph_discharges G))"

lemma finite_mapped_graph_mapping:
  assumes functional: "finite_relation_functional M"
    and domain: "fimage fst M=finite_graph_nodes G" and root: "(root,r) |\<in>| M"
  shows "finite_graph_mapping M G root (finite_mapped_graph M G) r"
  by (simp only: finite_graph_mapping_def finite_mapped_graph_def finite_derivation_graph.select_convs
    functional domain root simp_thms)

lemma finite_graph_mapping_inferences:
  fixes G :: "('a,'s,'c,'n) finite_derivation_graph"
    and H :: "('a,'s,'c,'m) finite_derivation_graph" and M :: "('n\<times>'m) fset"
  shows
  "finite_graph_inferences H=finite_edge_compose (fimage prod.swap M) (finite_graph_inferences G) \<longleftrightarrow>
    fset (graph_inferences (decode_finite_graph H))=
      {(m,N). \<exists>n. (n,N)\<in>fset (graph_inferences (decode_finite_graph G)) \<and> (n,m)\<in>fset M}"
proof -
  let ?R="finite_edge_compose (fimage prod.swap M) (finite_graph_inferences G)"
  have inj: "inj (decode_finite_graph_node :: ('a,'c) finite_schema_graph_node\<Rightarrow>_)"
    by (auto simp: inj_def)
  have exact:
    "map_relation_values decode_finite_graph_node (fset ?R)=
      {(m,N). \<exists>n. (n,N)\<in>fset (graph_inferences (decode_finite_graph G)) \<and> (n,m)\<in>fset M}"
    by (auto simp: decode_finite_graph_fields map_relation_values_member
      finite_edge_compose_member finite_relation_converse; blast)
  show ?thesis
    apply (subst exact[symmetric])
    by (simp only: decode_finite_graph_fields
      map_relation_values_injective[OF inj] fset_inject)
qed

theorem finite_graph_mapping_exact:
  "finite_graph_mapping M G root H r=
    schema_graph_mapping (fset M) (decode_finite_graph G) root (decode_finite_graph H) r"
proof -
  have domain: "fimage fst M=finite_graph_nodes G \<longleftrightarrow>
    rel_dom (fset M)=schema_graph_nodes (decode_finite_graph G)"
    by (simp only: fset_inject[symmetric] fimage.rep_eq finite_graph_nodes_correct rel_dom_image)
  have discharges: "finite_graph_discharges H=finite_indexed_relation_image M (finite_graph_discharges G) \<longleftrightarrow>
    fset (graph_discharges (decode_finite_graph H))={((m,s),k). \<exists>n q.
      ((n,s),q)\<in>fset (graph_discharges (decode_finite_graph G)) \<and>
      (n,m)\<in>fset M \<and> (q,k)\<in>fset M}"
    by (simp only: fset_inject[symmetric] decode_finite_graph_fields finite_indexed_relation_image_correct)
  show ?thesis by (simp only: finite_graph_mapping_def schema_graph_mapping_def
    finite_relation_functional_correct finite_graph_mapping_inferences domain discharges)
qed

theorem finite_graph_mapping_compose:
  fixes G :: "('a,'s,'c,'n) finite_derivation_graph"
    and H :: "('a,'s,'c,'m) finite_derivation_graph"
    and K :: "('a,'s,'c,'k) finite_derivation_graph"
  assumes "finite_graph_mapping M G root H r" "finite_graph_mapping N H r K s"
  shows "finite_graph_mapping (finite_edge_compose M N) G root K s"
  using schema_graph_mapping_compose[of "fset M" "decode_finite_graph G" root
      "decode_finite_graph H" r "fset N" "decode_finite_graph K" s] assms
  by (simp only: finite_graph_mapping_exact finite_edge_compose_correct)

lemma finite_graph_mapping_compose_injective:
  assumes "single_valued ((fset M)\<inverse>)" "single_valued ((fset N)\<inverse>)"
  shows "single_valued ((fset (finite_edge_compose M N))\<inverse>)"
  by (simp only: finite_edge_compose_correct converse_relcomp;
    rule relation_join_functional[OF assms(2,1)])

theorem finite_graph_mapping_rename:
  assumes formed: "finite_graph_formed G root"
  shows "finite_graph_mapping (fimage (\<lambda>n. (n,h n)) (finite_graph_nodes G))
    G root (finite_rename_graph h G) (h root)"
  by (simp only: finite_graph_mapping_exact finite_function_graph
      finite_graph_nodes_correct finite_rename_graph_exact;
    rule schema_graph_mapping_rename; use formed in \<open>simp only: finite_graph_formed_correct\<close>)

export_code finite_graph_mapping finite_mapped_graph checking SML

end
