theory Factor_Finite_Native_Graph_Assessment
  imports Factor_Finite_Graph_Construction Factor_Finite_Graph_Mappings RRA_Finite_Environment_Preservation
begin

definition finite_native_graph_result_condition where
  "finite_native_graph_result_condition (f::nat) E G root result=(case result of None \<Rightarrow> False
    | Some (F,M,r,H) \<Rightarrow>
      if f=0 then environment_formed (decode_finite_environment F) \<and>
        native_schema_graph_at (decode_finite_environment F) r (decode_finite_graph H)
      else if f=1 then schema_graph_mapping (fset M) (decode_finite_graph G) root (decode_finite_graph H) r
      else if f=2 then environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
        (\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
          artifact_at (decode_finite_environment E) w A \<longleftrightarrow> artifact_at (decode_finite_environment F) w A) \<and>
        (\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
          binds_slot (decode_finite_environment E) w k v \<longleftrightarrow> binds_slot (decode_finite_environment F) w k v)
      else if f=3 then image fst (schema_graph_nodes (decode_finite_graph H))\<inter>
        environment_uses (decode_finite_environment E)={}
      else if f=4 then single_valued ((fset M)\<inverse>) else False)"

definition finite_native_graph_result_assessment_by where
  "finite_native_graph_result_assessment_by read_graph E G root result=map_option (\<lambda>(F,M,r,H).
    let readings=read_graph F r in
      (readings,finite_environment_formed F \<and> H |\<in>| readings,
        finite_graph_mapping M G root H r,
        finite_environment_included E F \<and> finite_environment_agrees_on E F (finite_environment_uses E),
        fimage fst (finite_graph_nodes H) |\<inter>| finite_environment_uses E={||},
        finite_relation_functional (fimage prod.swap M))) result"

definition finite_native_graph_result_assessment where
  "finite_native_graph_result_assessment E G root result=
    finite_native_graph_result_assessment_by finite_native_graph_readings E G root result"

definition finite_native_graph_result_inspect where
  "finite_native_graph_result_inspect A (f::nat)=(case A of None \<Rightarrow> False
    | Some (readings,recovery,mapping,source,fresh,injective) \<Rightarrow>
      if f=0 then recovery else if f=1 then mapping else if f=2 then source
      else if f=3 then fresh else if f=4 then injective else False)"

lemma finite_native_graph_fresh_exact:
  "fimage fst (finite_graph_nodes H) |\<inter>| finite_environment_uses E={||} \<longleftrightarrow>
    image fst (schema_graph_nodes (decode_finite_graph H))\<inter>
      environment_uses (decode_finite_environment E)={}"
  by (simp only: fset_inject[symmetric] inf_fset.rep_eq bot_fset.rep_eq fimage.rep_eq
    finite_graph_nodes_correct finite_environment_uses_correct)

theorem finite_native_graph_result_assessment_exact:
  "finite_native_graph_result_inspect (finite_native_graph_result_assessment E G root result) f=
    finite_native_graph_result_condition f E G root result"
  by (cases result)
    (auto simp: finite_native_graph_result_assessment_def finite_native_graph_result_assessment_by_def finite_native_graph_result_inspect_def
      finite_native_graph_result_condition_def finite_environment_formed_correct
      finite_native_graph_readings_correct finite_graph_mapping_exact finite_environment_included_correct
      finite_environment_agrees_on_correct finite_native_graph_fresh_exact finite_relation_functional_correct
      finite_relation_converse relation_swap_image Let_def split: prod.splits)

theorem finite_native_graph_result_conditions:
  assumes formed: "finite_environment_formed F"
    and graph: "H |\<in>| finite_native_graph_readings F r"
    and mapping: "finite_graph_mapping M G root H r"
    and included: "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    and agreement: "finite_environment_agrees_on E F (finite_environment_uses E)"
    and fresh: "image fst (fset (finite_graph_nodes H))\<inter>fset (finite_environment_uses E)={}"
    and injective: "single_valued ((fset M)\<inverse>)" and facet: "f<5"
  shows "finite_native_graph_result_condition f E G root (Some (F,M,r,H))"
  using assms
  by (auto simp: finite_native_graph_result_condition_def finite_environment_formed_correct
    finite_environment_agrees_on_correct finite_native_graph_readings_correct finite_graph_mapping_exact
    finite_graph_nodes_correct finite_environment_uses_correct; arith)

export_code finite_native_graph_result_assessment finite_native_graph_result_inspect checking SML

text \<open>
  Direct graph placement and certificate replay inspect the same complete
  returned environment, correspondence and graph. Original-node types remain
  arbitrary. Recovery, full mapping, old-source preservation, freshness and
  injectivity each retain their independent condition and computed evidence.
\<close>

end
