theory Factor_Pattern_Bindings
  imports Factor_Substitution
begin

section \<open>Complete finite replacement relations\<close>

definition pattern_bindings_formed :: "'a set \<Rightarrow> ('a\<times>'b term_pattern) set \<Rightarrow> bool" where
  "pattern_bindings_formed B V \<longleftrightarrow> finite V \<and> single_valued V \<and> rel_dom V=B \<and>
    (\<forall>a p. (a,p)\<in>V \<longrightarrow> pattern_formed p)"

definition pattern_binding_variables :: "('a\<times>'b term_pattern) set \<Rightarrow> 'b set" where
  "pattern_binding_variables V=(\<Union>p\<in>rel_ran V. pattern_variables p)"

lemma pattern_binding_variables_finite:
  "finite V \<Longrightarrow> finite (pattern_binding_variables V)"
  by (simp add: pattern_binding_variables_def finite_rel_ran)

lemma pattern_bindings_graph:
  assumes "pattern_bindings_formed B V"
  shows "V=(\<lambda>a. (a,rel_value V a)) ` B"
  using assms single_valued_graph[of V]
  by (auto simp: pattern_bindings_formed_def graph_map_def)

lemma pattern_binding_at:
  assumes bindings: "pattern_bindings_formed B V" and key: "a\<in>B"
  shows "(a,rel_value V a)\<in>V" "pattern_formed (rel_value V a)"
    "pattern_variables (rel_value V a)\<subseteq>pattern_binding_variables V"
proof -
  show row: "(a,rel_value V a)\<in>V" using pattern_bindings_graph[OF bindings] key by blast
  show "pattern_formed (rel_value V a)" using bindings row by (auto simp: pattern_bindings_formed_def)
  show "pattern_variables (rel_value V a)\<subseteq>pattern_binding_variables V"
    using row by (auto simp: pattern_binding_variables_def rel_ran_def)
qed

lemma pattern_bindings_evaluation_graph:
  assumes "pattern_bindings_formed B V"
  shows "map_relation_values (evaluate_pattern h) V=
    (\<lambda>a. (a,evaluate_pattern h (rel_value V a))) ` B"
  by (subst pattern_bindings_graph[OF assms])
    (auto simp: map_relation_values_def)

lemma pattern_bindings_evaluation_formed:
  assumes bindings: "pattern_bindings_formed B V"
    and valuation: "\<forall>b\<in>pattern_binding_variables V. term_formed (h b)"
  shows "term_bindings_formed B (map_relation_values (evaluate_pattern h) V)"
proof -
  have formed_value: "term_formed (evaluate_pattern h p)" if "(a,p)\<in>V" for a p
    by (rule evaluate_pattern_formed)
      (use bindings valuation that in \<open>auto simp: pattern_bindings_formed_def pattern_binding_variables_def rel_ran_def\<close>)
  have finite_B: "finite B" using bindings finite_rel_dom[of V]
    by (auto simp: pattern_bindings_formed_def)
  have assignment: "\<forall>a\<in>B. term_formed (evaluate_pattern h (rel_value V a))"
    using formed_value pattern_binding_at(1)[OF bindings] by blast
  show ?thesis by (simp only: pattern_bindings_evaluation_graph[OF bindings] term_bindings_formed_def)
    (use finite_B assignment in \<open>auto simp: single_valued_def rel_dom_def\<close>)
qed

lemma substituted_pattern_binding_scope:
  assumes "pattern_bindings_formed (pattern_variables p) V"
  shows "pattern_variables (pattern_substitute (rel_value V) p)=pattern_binding_variables V"
proof -
  have graph: "V=graph_map (pattern_variables p) (rel_value V)"
    using assms single_valued_graph[of V] by (auto simp: pattern_bindings_formed_def)
  have range_eq: "rel_ran V=rel_value V ` pattern_variables p"
    using arg_cong[OF graph, of rel_ran] by (simp only: graph_map_ran)
  show ?thesis by (simp add: pattern_substitute_variables pattern_binding_variables_def range_eq)
qed

section \<open>A finite specialization witness respects the original interface scope\<close>

definition schema_pattern_call ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> 'b term_pattern \<Rightarrow> bool" where
  "schema_pattern_call P d p \<longleftrightarrow> schema_system_formed P \<and>
    (\<exists>q V. (d,q)\<in>system_interfaces P \<and> pattern_bindings_formed (pattern_variables q) V \<and>
      p=pattern_substitute (rel_value V) q)"

lemma schema_pattern_call_formed:
  assumes "schema_pattern_call P d p"
  shows "pattern_formed p" "d\<in>system_definitions P"
proof -
  obtain q V where system: "schema_system_formed P" and interface: "(d,q)\<in>system_interfaces P"
    and bindings: "pattern_bindings_formed (pattern_variables q) V"
    and head: "p=pattern_substitute (rel_value V) q"
    using assms by (auto simp: schema_pattern_call_def)
  have qf: "pattern_formed q" using system interface by (auto simp: schema_system_formed_def)
  have replacements: "\<forall>a\<in>pattern_variables q. pattern_formed (rel_value V a)"
    using pattern_binding_at(2)[OF bindings] by blast
  show "pattern_formed p" using pattern_substitute_formed[OF qf replacements] by (simp add: head)
  show "d\<in>system_definitions P" using interface by (auto simp: system_definitions_def rel_dom_def)
qed

lemma pattern_evaluation_accepted:
  assumes pf: "pattern_formed p" and valuation: "\<forall>a\<in>pattern_variables p. term_formed (h a)"
  shows "pattern_accepts p (evaluate_pattern h p)"
proof -
  let ?V="(\<lambda>a. (a,h a)) ` pattern_variables p"
  have bindings: "term_bindings_formed (pattern_variables p) ?V"
    using valuation by (auto simp: term_bindings_formed_def single_valued_def rel_dom_def)
  have inst: "pattern_instance ?V p (evaluate_pattern h p)"
    by (rule evaluate_pattern_instance[OF pf]) auto
  show ?thesis using bindings inst evaluate_pattern_formed[OF pf valuation]
    by (auto simp: pattern_accepts_def)
qed

theorem schema_pattern_call_evaluation:
  assumes call: "schema_pattern_call P d p"
    and valuation: "\<forall>b\<in>pattern_variables p. term_formed (h b)"
  shows "schema_call_formed P d (evaluate_pattern h p)"
proof -
  obtain q V where system: "schema_system_formed P" and interface: "(d,q)\<in>system_interfaces P"
    and bindings: "pattern_bindings_formed (pattern_variables q) V"
    and head: "p=pattern_substitute (rel_value V) q"
    using call by (auto simp: schema_pattern_call_def)
  have pf: "pattern_formed q" using system interface by (auto simp: schema_system_formed_def)
  have scope: "pattern_binding_variables V=pattern_variables p"
    using substituted_pattern_binding_scope[OF bindings] head by simp
  have formed: "\<forall>a\<in>pattern_variables q. term_formed (evaluate_pattern h (rel_value V a))"
  proof (intro ballI)
    fix a assume key: "a\<in>pattern_variables q"
    show "term_formed (evaluate_pattern h (rel_value V a))"
      by (rule evaluate_pattern_formed[OF pattern_binding_at(2)[OF bindings key]])
        (use valuation scope pattern_binding_at(3)[OF bindings key] in blast)
  qed
  have accepted: "pattern_accepts q (evaluate_pattern h p)"
    using pattern_evaluation_accepted[OF pf formed] by (simp add: head)
  show ?thesis using system interface accepted by (auto simp: schema_call_formed_def)
qed

lemma schema_pattern_call_variable:
  assumes "schema_system_formed P" "(d,Pattern_Variable a)\<in>system_interfaces P" "pattern_formed p"
  shows "schema_pattern_call P d p"
proof -
  have bindings: "pattern_bindings_formed {a} {(a,p)}"
    using assms(3) by (auto simp: pattern_bindings_formed_def single_valued_def rel_dom_def)
  have rv: "rel_value {(a,p)} a=p" by (simp add: rel_value_def)
  show ?thesis unfolding schema_pattern_call_def
    by (intro conjI[OF assms(1)], rule exI[of _ "Pattern_Variable a"], rule exI[of _ "{(a,p)}"])
      (use assms(2) bindings rv in simp)
qed

text \<open>
  Every original binder has exactly one formed replacement pattern. Its target
  variables are derived from those replacements. Evaluation produces complete
  ordinary term bindings while preserving the original keys.

  An interface witness specializes the actual interface under its own binder.
  The resulting call is admitted for every formed valuation of the resulting
  pattern. This is an explicit sufficient witness; it does not identify a
  clause binder with the independently scoped interface binder.
\<close>

end
