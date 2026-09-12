theory Factor_Specialization_Binding_Observed
  imports Factor_Specialization_Binding_Contracts Factor_Clause_Specialization_Graphs
    Factor_Positioned_Specializations
begin

section \<open>The actual replacement record supplies the same symbolic bindings\<close>

theorem specialization_binding_symbolic:
  assumes actual: "specialization_binding_at E pu pr d c F v r H w t report bs Is Ks"
    and package: "native_package_at E pu pr P" and target: "native_schema_at H w t T"
  obtains vs where "schema_clause_specialization P d c (set vs) T" "distinct vs"
    "bs=positioned_binding_rows_term (map (\<lambda>(a,p). ((fst d,a),pattern_claim_observation p)) vs)"
    "schema_reference_presents T report"
proof -
  obtain Q S s As where raw: "native_package_at E pu pr Q" "((d,c),S)\<in>system_clauses Q"
    "distinct As" "set As=schema_variables S"
    "pattern_record_at F v (schema_variables (schema_substitute s S)) r
      (substitution_row_patterns As s) (set Is) (set Ks)"
    "native_schema_at H w t (schema_substitute s S)"
    "schema_pattern_boundary Q d (schema_substitute s S)"
    "schema_reference_presents (schema_substitute s S) report"
    "bs=positioned_binding_rows_term (map (\<lambda>a. ((fst d,a),pattern_claim_observation (s a))) As)"
    using actual by (auto simp only: specialization_binding_at_def)
  have program: "Q=P" by (rule native_package_unique[OF raw(1) package])
  have schema: "T=schema_substitute s S" by (rule native_schema_unique[OF target raw(6)])
  have replacements: "\<forall>a\<in>schema_variables S. pattern_formed (s a)"
  proof -
    have rows: "\<forall>p\<in>set (substitution_row_patterns As s). pattern_formed p"
      using pattern_record_formed[OF raw(5)] by blast
    show ?thesis using rows raw(4) by (simp only: substitution_row_formed; blast)
  qed
  let ?vs="map (\<lambda>a. (a,s a)) As"
  have relation: "schema_clause_specialization P d c (set ?vs) T"
    using schema_clause_specialization_graph(1)[OF raw(2,7) replacements]
    by (simp only: program schema raw(4) set_map)
  have order: "distinct ?vs" using raw(3) by (auto simp: distinct_map inj_on_def)
  have observations: "bs=positioned_binding_rows_term (map (\<lambda>(a,p). ((fst d,a),pattern_claim_observation p)) ?vs)"
    by (simp only: raw(9) map_map comp_def case_prod_conv)
  show thesis by (rule that[OF relation order observations]) (use raw(8) schema in simp)
qed

text \<open>
  The source relation still retains the actual replacement record, target,
  complete report and exact support lists. This theorem recovers the finite
  symbolic bindings already carried by those sources. Arbitrary native pairs
  are never taken as pattern syntax by this recovery.
\<close>

end
