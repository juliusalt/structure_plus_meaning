theory Factor_Native_Graph_Assessment
  imports Factor_Native_Graph_Cases
begin

definition native_graph_ready :: "native_graph_problem\<Rightarrow>bool" where
  "native_graph_ready X=(case X of (E,G,root) \<Rightarrow> finite_graph_construction_ready E G root)"

definition native_graph_ready_condition :: "native_graph_problem\<Rightarrow>bool" where
  "native_graph_ready_condition X=(case X of (E,G,root) \<Rightarrow>
    environment_formed (decode_finite_environment E) \<and>
    schema_graph_formed (decode_finite_graph G) root \<and>
    graph_metadata_at (decode_finite_environment E) (decode_finite_graph G))"

lemma native_graph_ready_exact:
  "native_graph_ready X=native_graph_ready_condition X"
  by (simp add: native_graph_ready_def native_graph_ready_condition_def finite_graph_construction_ready_exact
    split: prod.splits)

definition native_graph_input_inspection :: "native_graph_problem\<Rightarrow>bool\<times>bool\<times>bool" where
  "native_graph_input_inspection X=(case X of (E,G,root) \<Rightarrow>
    (finite_environment_formed E,finite_graph_formed G root,finite_graph_metadata_at E G))"

lemma native_graph_input_inspection_exact:
  "native_graph_input_inspection (E,G,root)=
    (environment_formed (decode_finite_environment E),
      schema_graph_formed (decode_finite_graph G) root,
      graph_metadata_at (decode_finite_environment E) (decode_finite_graph G))"
  by (simp only: native_graph_input_inspection_def case_prod_conv
    finite_environment_formed_correct finite_graph_formed_correct finite_graph_metadata_at_exact)

definition native_graph_result_condition :: "nat\<Rightarrow>native_graph_problem\<Rightarrow>native_graph_result\<Rightarrow>bool" where
  "native_graph_result_condition f X result=(case X of (E,G,root) \<Rightarrow>
    case result of None \<Rightarrow> False | Some (F,M,r,H) \<Rightarrow>
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

definition native_graph_condition ::
    "nat\<Rightarrow>(native_graph_problem\<Rightarrow>native_graph_result)\<Rightarrow>native_graph_problem\<Rightarrow>bool" where
  "native_graph_condition f method X=(if f=5 then
    (\<not>native_graph_ready_condition X \<longrightarrow> method X=None)
    else if f<5 then (native_graph_ready_condition X \<longrightarrow> native_graph_result_condition f X (method X))
    else False)"

definition native_graph_assessment where
  "native_graph_assessment X result=(case X of (E,G,root) \<Rightarrow>
    (native_graph_ready X,map_option (\<lambda>(F,M,r,H).
      let readings=finite_native_graph_readings F r in
        (readings,finite_environment_formed F \<and> H |\<in>| readings,
          finite_graph_mapping M G root H r,
          finite_environment_included E F \<and> finite_environment_agrees_on E F (finite_environment_uses E),
          fimage fst (finite_graph_nodes H) |\<inter>| finite_environment_uses E={||},
          finite_relation_functional (fimage prod.swap M))) result,result=None))"

definition native_graph_inspect where
  "native_graph_inspect A (f::nat)=(case A of (ready,body,rejected) \<Rightarrow>
    if f=5 then (\<not>ready \<longrightarrow> rejected) else if f<5 then (ready \<longrightarrow>
      (case body of None \<Rightarrow> False | Some (readings,recovery,mapping,source,fresh,injective) \<Rightarrow>
        if f=0 then recovery else if f=1 then mapping else if f=2 then source else if f=3 then fresh else injective))
    else False)"

lemma native_graph_fresh_exact:
  "fimage fst (finite_graph_nodes H) |\<inter>| finite_environment_uses E={||} \<longleftrightarrow>
    image fst (schema_graph_nodes (decode_finite_graph H))\<inter>
      environment_uses (decode_finite_environment E)={}"
  by (simp only: fset_inject[symmetric] inf_fset.rep_eq bot_fset.rep_eq fimage.rep_eq
    finite_graph_nodes_correct finite_environment_uses_correct)

theorem native_graph_assessment_exact:
  "native_graph_inspect (native_graph_assessment X (method X)) f=native_graph_condition f method X"
proof -
  obtain E G root where input: "X=(E,G,root)" by (cases X) auto
  have facets: "f=0 \<or> f=1 \<or> f=2 \<or> f=3 \<or> f=4 \<or> f=5 \<or> 6\<le>f" by arith
  from facets show ?thesis
    apply (elim disjE; cases "method X")
    apply (auto simp: input native_graph_assessment_def native_graph_inspect_def native_graph_condition_def
      native_graph_ready_exact native_graph_result_condition_def
      finite_environment_formed_correct finite_native_graph_readings_correct finite_graph_mapping_exact
      finite_environment_included_correct finite_environment_agrees_on_correct
      native_graph_fresh_exact finite_relation_functional_correct finite_relation_converse relation_swap_image Let_def
      split: prod.splits)
    done
qed

export_code native_graph_assessment native_graph_inspect checking SML

text \<open>
  The actual returned environment supplies the complete native graph readings.
  The original graph and full returned correspondence independently determine
  metadata preservation. Original artifacts and outgoing bindings, freshness,
  injectivity and refusal remain separate conditions. All fields are inspected
  against the complete original input, regardless of the comparison basis.
\<close>

end
