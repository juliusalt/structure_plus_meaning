theory Finite_Presented_Graphs
  imports Finite_Presented_Programs Factor_Executable_Graphs
begin

section \<open>Inference and assertion nodes retain their distinct constructors\<close>

fun finite_graph_node_presentation ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> ('c \<Rightarrow> finite_factor_term) \<Rightarrow>
    ('a,'c) finite_schema_graph_node \<Rightarrow> finite_factor_term" where
  "finite_graph_node_presentation fa fc Finite_Assertion=Finite_Payload []"
| "finite_graph_node_presentation fa fc (Finite_Inference c V)=Finite_Pair (fc c)
    (finite_collection_presentation (finite_pair_presentation fa id) V)"

lemma finite_graph_node_presentation_injective [intro]:
  assumes a: "inj fa" and c: "inj fc"
  shows "inj (finite_graph_node_presentation fa fc)"
proof (rule injI)
  fix n m assume same: "finite_graph_node_presentation fa fc n=finite_graph_node_presentation fa fc m"
  have bindings: "inj (finite_collection_presentation (finite_pair_presentation fa (id::finite_factor_term \<Rightarrow> _)))"
    by (intro finite_collection_presentation_injective finite_pair_presentation_injective a inj_on_id)
  show "n=m" using same by (cases n; cases m) (simp_all add: inj_eq[OF bindings] inj_eq[OF c])
qed

definition finite_graph_presentation ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> ('s \<Rightarrow> finite_factor_term) \<Rightarrow>
    ('c \<Rightarrow> finite_factor_term) \<Rightarrow> ('n \<Rightarrow> finite_factor_term) \<Rightarrow>
    ('a,'s,'c,'n) finite_derivation_graph \<Rightarrow> finite_factor_term" where
  "finite_graph_presentation fa fs fc fn G=Finite_Pair
    (finite_collection_presentation (finite_pair_presentation fn (finite_graph_node_presentation fa fc))
      (finite_graph_inferences G))
    (finite_collection_presentation (finite_pair_presentation (finite_pair_presentation fn fs) fn)
      (finite_graph_discharges G))"

lemma finite_graph_presentation_injective [intro]:
  assumes a: "inj fa" and s: "inj fs" and c: "inj fc" and n: "inj fn"
  shows "inj (finite_graph_presentation fa fs fc fn)"
proof (rule injI)
  fix G H assume same: "finite_graph_presentation fa fs fc fn G=finite_graph_presentation fa fs fc fn H"
  have nodes: "inj (finite_collection_presentation
      (finite_pair_presentation fn (finite_graph_node_presentation fa fc)))"
    by (intro finite_collection_presentation_injective finite_pair_presentation_injective
      finite_graph_node_presentation_injective a c n)
  have edges: "inj (finite_collection_presentation (finite_pair_presentation (finite_pair_presentation fn fs) fn))"
    by (intro finite_collection_presentation_injective finite_pair_presentation_injective n s)
  show "G=H"
    by (rule finite_derivation_graph.equality;
      use same in \<open>simp add: finite_graph_presentation_def inj_eq[OF nodes] inj_eq[OF edges]\<close>)
qed

theorem finite_graph_presentation_class:
  assumes "inj fa" "inj fs" "inj fc" "inj fn"
  shows "presentation_class (finite_presents (finite_graph_presentation fa fs fc fn)) (\<lambda>_. True)
    (\<lambda>t. \<exists>G. t=decode_finite_term (finite_graph_presentation fa fs fc fn G))"
  by (rule finite_presents_class[where D="\<lambda>_. True", simplified];
      rule finite_graph_presentation_injective[OF assms])

text \<open>
  The inference collection keeps every node identity, inference clause, binding
  and assertion constructor. The discharge collection keeps each source node,
  premise socket and target node. All four coordinate presentations are separate
  arguments; neither malformed graph fields nor conflicting edges are omitted.
  Presentation supplies no graph validity or proof admission assertion.
\<close>

end
