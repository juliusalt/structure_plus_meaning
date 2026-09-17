theory Factor_Native_Graph_Assessment
  imports Factor_Native_Graph_Cases Factor_Finite_Native_Graph_Assessment
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
    finite_native_graph_result_condition f E G root result)"

definition native_graph_condition ::
    "nat\<Rightarrow>(native_graph_problem\<Rightarrow>native_graph_result)\<Rightarrow>native_graph_problem\<Rightarrow>bool" where
  "native_graph_condition f method X=(if f=5 then
    (\<not>native_graph_ready_condition X \<longrightarrow> method X=None)
    else if f<5 then (native_graph_ready_condition X \<longrightarrow> native_graph_result_condition f X (method X))
    else False)"

definition native_graph_assessment where
  "native_graph_assessment X result=(case X of (E,G,root) \<Rightarrow>
    (native_graph_ready X,finite_native_graph_result_assessment E G root result,result=None))"

definition native_graph_inspect where
  "native_graph_inspect A (f::nat)=(case A of (ready,body,rejected) \<Rightarrow>
    if f=5 then (\<not>ready \<longrightarrow> rejected) else if f<5 then
      (ready \<longrightarrow> finite_native_graph_result_inspect body f) else False)"

lemma native_graph_fresh_exact:
  "fimage fst (finite_graph_nodes H) |\<inter>| finite_environment_uses E={||} \<longleftrightarrow>
    image fst (schema_graph_nodes (decode_finite_graph H))\<inter>
      environment_uses (decode_finite_environment E)={}"
  by (rule finite_native_graph_fresh_exact)

theorem native_graph_assessment_exact:
  "native_graph_inspect (native_graph_assessment X (method X)) f=native_graph_condition f method X"
  by (cases X)
    (simp only: native_graph_assessment_def native_graph_inspect_def native_graph_condition_def
      native_graph_result_condition_def case_prod_conv native_graph_ready_exact
      finite_native_graph_result_assessment_exact)

text \<open>
  The actual returned environment supplies the complete native graph readings.
  The original graph and full returned correspondence independently determine
  metadata preservation. Original artifacts and outgoing bindings, freshness,
  injectivity and refusal remain separate conditions. All fields are inspected
  against the complete original input, regardless of the comparison basis.
\<close>

end
