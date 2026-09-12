theory Factor_Clause_Specialization_Graphs
  imports Factor_Schema_Pattern_Boundary
begin

section \<open>A complete replacement function has its exact finite binding graph\<close>

theorem schema_clause_specialization_graph:
  assumes clause: "((d,c),S)\<in>system_clauses P"
    and boundary: "schema_pattern_boundary P d (schema_substitute s S)"
    and replacements: "\<forall>a\<in>schema_variables S. pattern_formed (s a)"
  shows "schema_clause_specialization P d c ((\<lambda>a. (a,s a)) ` schema_variables S) (schema_substitute s S)"
    "a\<in>schema_variables S \<Longrightarrow> rel_value ((\<lambda>a. (a,s a)) ` schema_variables S) a=s a"
proof -
  let ?V="(\<lambda>a. (a,s a)) ` schema_variables S"
  have system: "schema_system_formed P"
    using boundary by (auto simp: schema_pattern_boundary_def schema_pattern_call_def)
  have formed: "schema_formed S" using system clause by (auto simp: schema_system_formed_def)
  have bindings: "pattern_bindings_formed (schema_variables S) ?V"
    by (rule graph_pattern_bindings_formed[OF schema_variables_finite[OF formed] replacements])
  have selected_value: "rel_value ?V a=s a" if "a\<in>schema_variables S" for a
    by (rule rel_value_eq) (use that in \<open>auto simp: single_valued_def\<close>)
  have substituted: "schema_substitute (rel_value ?V) S=schema_substitute s S"
    by (rule schema_substitute_cong) (rule selected_value; assumption)
  show "schema_clause_specialization P d c ?V (schema_substitute s S)"
    unfolding schema_clause_specialization_def
    by (rule conjI[OF boundary], rule exI[of _ S], rule conjI[OF clause],
      rule conjI[OF bindings], rule sym[OF substituted])
  show "a\<in>schema_variables S \<Longrightarrow> rel_value ?V a=s a" by (rule selected_value)
qed

lemma schema_clause_specialization_unique:
  assumes first: "schema_clause_specialization P d c V S"
    and second: "schema_clause_specialization P d c V T"
  shows "S=T"
proof -
  obtain R where source: "((d,c),R)\<in>system_clauses P"
    using first by (auto simp: schema_clause_specialization_def)
  show ?thesis using schema_clause_specialization_source(2)[OF first source]
    schema_clause_specialization_source(2)[OF second source] by simp
qed

text \<open>
  The graph contains exactly the complete source binder, including variables
  used only by premises or material operands. Substitution is determined on
  that domain; function values outside it contribute no semantic choice.
\<close>

end
