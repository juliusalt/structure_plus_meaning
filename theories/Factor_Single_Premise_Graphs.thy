theory Factor_Single_Premise_Graphs
  imports Factor_Inference_Value_Maps
begin

section \<open>One inference and one identified assertion occurrence\<close>

definition single_premise_graph where
  "single_premise_graph n m s c V=\<lparr>
    graph_inferences={|(n,Schema_Inference c V),(m,Schema_Assertion)|},
    graph_discharges={|((n,s),m)|}\<rparr>"

lemma single_premise_graph_formed:
  assumes different: "n\<noteq>m"
  shows "schema_graph_formed (single_premise_graph n m s c V) n"
proof -
  have metric: "wf (measure (\<lambda>x. if x=n then 1 else 0))" by (rule wf_measure)
  have included: "{(m,n)}\<subseteq>measure (\<lambda>x. if x=n then 1 else 0)"
    using different by auto
  have terminating: "wf {(m,n)}" by (rule wf_subset[OF metric included])
  let ?G="single_premise_graph n m s c V"
  have nodes: "schema_graph_nodes ?G={n,m}"
    by (auto simp: single_premise_graph_def schema_graph_nodes_def rel_dom_def)
  have edges: "schema_graph_edges ?G={(m,n)}"
    by (auto simp: single_premise_graph_def schema_graph_edges_def)
  have uses: "schema_assertion_uses ?G={(m,(n,s))}"
    using different by (auto simp: single_premise_graph_def schema_assertion_uses_def)
  have child_reached: "(m,n)\<in>{(m,n)}\<^sup>*" by (rule r_into_rtrancl) simp
  have all_reached: "\<forall>x\<in>schema_graph_nodes ?G. (x,n)\<in>(schema_graph_edges ?G)\<^sup>*"
    using child_reached by (simp only: nodes edges) auto
  have node_function: "single_valued (fset (graph_inferences ?G))"
    using different by (auto simp: single_premise_graph_def single_valued_def)
  have link_function: "single_valued (fset (graph_discharges ?G))"
    by (auto simp: single_premise_graph_def single_valued_def)
  have assertion_function: "single_valued (schema_assertion_uses ?G)"
    by (simp only: uses) (auto simp: single_valued_def)
  show ?thesis
    unfolding schema_graph_formed_def
    using node_function link_function assertion_function all_reached terminating
    by (simp only: nodes edges) auto
qed

lemma single_premise_graph_fields:
  assumes "n\<noteq>m"
  shows "schema_graph_nodes (single_premise_graph n m s c V)={n,m}"
    "schema_graph_premises (single_premise_graph n m s c V) n={(s,m)}"
    "schema_graph_premises (single_premise_graph n m s c V) m={}"
  using assms by (auto simp: single_premise_graph_def schema_graph_nodes_def rel_dom_def schema_graph_premises_def)

lemma single_premise_graph_values:
  "map_inference_values f (single_premise_graph n m s c V)=
    single_premise_graph n m s c (fimage (map_prod id f) V)"
  by (simp add: single_premise_graph_def map_inference_values_def)

text \<open>
  The child remains an assertion occurrence with one use. Its claim is not
  stored in the node and its truth is not established by this graph geometry.
  The same constructor works for symbolic bindings and their observed values.
\<close>

end
