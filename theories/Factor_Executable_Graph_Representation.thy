theory Factor_Executable_Graph_Representation
  imports Factor_Executable_Recovery
begin

section \<open>Every valid graph has an exact finite representation\<close>

definition finite_binding_set_of ::
  "('a \<times> factor_term) fset \<Rightarrow> ('a \<times> finite_factor_term) fset" where
  "finite_binding_set_of V = fimage (map_prod id finite_term_of) V"

lemma decode_finite_binding_set_of:
  assumes formed: "\<And>a t. (a,t) |\<in>| V \<Longrightarrow> term_formed t"
  shows "decode_finite_binding_set (finite_binding_set_of V) = V"
proof -
  have inverse: "map_relation_values decode_finite_term (map_relation_values finite_term_of (fset V)) = fset V"
    by (rule map_relation_values_inverse) (use formed in \<open>auto intro: decode_finite_term_of\<close>)
  have equality: "fset (decode_finite_binding_set (finite_binding_set_of V))=fset V"
    using inverse by (simp add: decode_finite_binding_set_def finite_binding_set_of_def
        map_relation_values_def map_prod_def fimage.rep_eq image_image)
  show ?thesis using equality by (simp only: fset_inject)
qed

fun finite_graph_node_of :: "('a,'c) schema_graph_node \<Rightarrow> ('a,'c) finite_schema_graph_node" where
  "finite_graph_node_of Schema_Assertion = Finite_Assertion"
| "finite_graph_node_of (Schema_Inference c V) = Finite_Inference c (finite_binding_set_of V)"

definition finite_graph_of ::
  "('a,'s,'c,'n) schema_derivation_graph \<Rightarrow> ('a,'s,'c,'n) finite_derivation_graph" where
  "finite_graph_of G =
    \<lparr>finite_graph_inferences=fimage (map_prod id finite_graph_node_of) (graph_inferences G),
     finite_graph_discharges=graph_discharges G\<rparr>"

lemma decode_finite_graph_of:
  assumes formed: "\<And>n c V a t. (n,Schema_Inference c V) \<in> fset (graph_inferences G) \<Longrightarrow>
    (a,t) |\<in>| V \<Longrightarrow> term_formed t"
  shows "decode_finite_graph (finite_graph_of G)=G"
proof -
  have each: "\<And>n A. (n,A) \<in> fset (graph_inferences G) \<Longrightarrow>
      decode_finite_graph_node (finite_graph_node_of A)=A"
  proof -
    fix n A assume row: "(n,A) \<in> fset (graph_inferences G)"
    show "decode_finite_graph_node (finite_graph_node_of A)=A"
    proof (cases A)
      case Schema_Assertion
      show ?thesis by (simp add: Schema_Assertion)
    next
      case (Schema_Inference c V)
      have bindings: "decode_finite_binding_set (finite_binding_set_of V)=V"
        by (rule decode_finite_binding_set_of) (use formed row Schema_Inference in blast)
      show ?thesis by (simp add: Schema_Inference bindings)
    qed
  qed
  have inverse: "map_relation_values decode_finite_graph_node
      (map_relation_values finite_graph_node_of (fset (graph_inferences G))) = fset (graph_inferences G)"
    by (rule map_relation_values_inverse, rule each)
  have nodes: "fset (graph_inferences (decode_finite_graph (finite_graph_of G)))=fset (graph_inferences G)"
    using inverse by (simp add: finite_graph_of_def map_relation_values_def map_prod_def fimage.rep_eq)
  show ?thesis
  proof (rule schema_derivation_graph.equality)
    show "graph_inferences (decode_finite_graph (finite_graph_of G))=graph_inferences G"
      using nodes by (simp only: fset_inject)
    show "graph_discharges (decode_finite_graph (finite_graph_of G))=graph_discharges G"
      by (simp add: finite_graph_of_def)
    show "schema_derivation_graph.more (decode_finite_graph (finite_graph_of G))=schema_derivation_graph.more G"
      by simp
  qed
qed

theorem finite_graph_representation:
  assumes read: "schema_graph_reading P G root d t J"
  shows "\<exists>!C. decode_finite_graph C=G"
proof -
  have inverse: "decode_finite_graph (finite_graph_of G)=G"
    by (rule decode_finite_graph_of, rule schema_graph_reading_binding_formed[OF read])
  show ?thesis by (rule ex1I[of _ "finite_graph_of G"]) (use inverse in auto)
qed

theorem finite_derivation_representation:
  assumes read: "schema_graph_reading P G root d t J"
  shows "\<exists>PC GC tc. decode_finite_system PC=P \<and> decode_finite_graph GC=G \<and>
    decode_finite_term tc=t \<and> finite_graph_valid PC GC root d tc"
proof -
  have root: "(root,d,t) \<in> J" using read by (simp add: schema_graph_reading_def)
  have call: "schema_call_formed P d t" by (rule schema_graph_reading_call_formed[OF read root])
  have pf: "schema_system_formed P" and tf: "term_formed t"
    using call by (auto simp: schema_call_formed_def pattern_accepts_def)
  have pd: "decode_finite_system (finite_system_of P)=P" by (rule decode_finite_system_of[OF pf])
  have td: "decode_finite_term (finite_term_of t)=t" by (rule decode_finite_term_of[OF tf])
  have gd: "decode_finite_graph (finite_graph_of G)=G"
    by (rule decode_finite_graph_of, rule schema_graph_reading_binding_formed[OF read])
  have valid: "finite_graph_valid (finite_system_of P) (finite_graph_of G) root d (finite_term_of t)"
    using read by (auto simp: finite_graph_valid_correct pd gd td)
  show ?thesis using pd gd td valid by blast
qed

theorem finite_closed_derivation_representation:
  assumes derived: "schema_graph_derives P G root d t {}"
  shows "\<exists>PC GC tc. decode_finite_system PC=P \<and> decode_finite_graph GC=G \<and>
    decode_finite_term tc=t \<and> finite_graph_proves PC GC root d tc"
proof -
  obtain J where read: "schema_graph_reading P G root d t J"
    using derived unfolding schema_graph_derives_def by blast
  obtain PC GC tc where pd: "decode_finite_system PC=P" and gd: "decode_finite_graph GC=G"
    and td: "decode_finite_term tc=t" using finite_derivation_representation[OF read] by blast
  have checked: "finite_graph_proves PC GC root d tc"
    using derived by (simp add: finite_graph_proves_correct pd gd td)
  show ?thesis using pd gd td checked by blast
qed

text \<open>
  Coverage is proved for every valid abstract graph, not inferred from graph
  formation alone. Validity forces all actual binding terms and node claims
  to be formed, so they have exact finite representations. The mathematical
  inverse is used only to prove coverage; the executable checker receives
  complete finite program, graph, and root-call values.
\<close>

end
