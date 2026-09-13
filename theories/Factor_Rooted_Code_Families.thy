theory Factor_Rooted_Code_Families
  imports Factor_System_Clauses Factor_Definition_Code Factor_Packages
begin

section \<open>Compile a selected family from one complete source system\<close>

theorem definition_codes_on:
  fixes P :: "('a,'s,local_address option definition_site,'c) schema_system"
  assumes formed: "schema_system_formed P" and inside: "D\<subseteq>system_definitions P"
    and addresses: "\<forall>d\<in>D. \<forall>S\<in>rel_ran (system_clause_family P d).
      \<forall>e\<in>schema_dependencies S. octets_formed (snd e)"
  shows "\<exists>K. \<forall>d\<in>D. definition_code_for (system_interface P d) (system_clause_family P d) (K d)"
proof -
  have each: "\<forall>d\<in>D. \<exists>K. definition_code_for (system_interface P d) (system_clause_family P d) K"
  proof (intro ballI)
    fix d assume member: "d\<in>D"
    have source: "d\<in>system_definitions P" using inside member by blast
    have address: "\<forall>S\<in>rel_ran (system_clause_family P d). \<forall>e\<in>schema_dependencies S. octets_formed (snd e)"
      using addresses member by blast
    show "\<exists>K. definition_code_for (system_interface P d) (system_clause_family P d) K"
      by (rule definition_code_total[OF system_interface_formed[OF formed source]
        system_clause_family_finite[OF formed] system_clause_family_functional[OF formed]
        system_clause_family_formed[OF formed] address])
  qed
  show ?thesis using bchoice[OF each] by blast
qed

lemma definition_code_source_dependencies:
  assumes formed: "schema_system_formed P"
    and code: "definition_code_for (system_interface P d) (system_clause_family P d) K"
  shows "(\<Union>S\<in>rel_ran (code_clauses K). schema_dependencies S)\<subseteq>system_definitions P"
  by (simp only: definition_code_dependencies[OF code] definition_code_properties(7)[OF code])
    (rule system_clause_family_dependencies[OF formed])

locale rooted_code_family =
  fixes P :: "('a,'s,local_address option definition_site,'c) schema_system"
    and D :: "local_address option definition_site set"
    and K :: "local_address option definition_site\<Rightarrow>definition_code"
  assumes formed: "schema_system_formed P" and inside: "D\<subseteq>system_definitions P"
    and roots: "\<forall>d\<in>D. snd d=[]"
    and codes: "\<forall>d\<in>D. definition_code_for (system_interface P d) (system_clause_family P d) (K d)"
begin

abbreviation uses where "uses \<equiv> fst ` D"
abbreviation artifacts where "artifacts u \<equiv> code_artifact (K (u,[]))"
abbreviation literals where "literals u \<equiv> code_literals (K (u,[]))"
abbreviation callees where "callees u \<equiv> code_callees (K (u,[]))"

lemma finite_sites: "finite D" by (rule finite_subset[OF inside system_definitions_finite[OF formed]])
lemma finite_uses: "finite uses" using finite_sites by simp

lemma site_shape:
  assumes "d\<in>D"
  shows "(fst d,[])=d"
  using roots assms by (cases d) auto

lemma use_site:
  assumes "u\<in>uses"
  shows "(u,[])\<in>D"
proof -
  obtain d where source: "d\<in>D" "u=fst d" using assms by blast
  show ?thesis using source site_shape[OF source(1)] by simp
qed

lemma use_codes:
  assumes "u\<in>uses"
  shows "definition_code_for (system_interface P (u,[])) (system_clause_family P (u,[])) (K (u,[]))"
  using codes use_site[OF assms] by blast

lemma artifact_formation: "\<forall>u\<in>uses. exact_formed (artifacts u)"
  using use_codes definition_code_properties(1) by blast

lemma profiles: "\<forall>u\<in>uses. reference_table_formed (literals u) (callees u)"
  using use_codes definition_code_properties(5) by blast

lemma bounds: "\<forall>u\<in>uses. rel_dom (literals u)\<union>rel_dom (callees u)\<subseteq>rra_carrier (object_structure (artifacts u))"
  using use_codes definition_code_properties(6) by blast

lemma callee_source:
  assumes member: "u\<in>uses" and callee: "d\<in>rel_ran (callees u)"
  shows "d\<in>system_definitions P"
  using definition_code_properties(7)[OF use_codes[OF member]]
    system_clause_family_dependencies[OF formed, of "(u,[])"] callee by blast

lemma compiled_dependencies:
  assumes member: "d\<in>D"
  shows "(\<Union>S\<in>rel_ran (code_clauses (K d)). schema_dependencies S)\<subseteq>system_definitions P"
proof -
  have code: "definition_code_for (system_interface P d) (system_clause_family P d) (K d)"
    using codes member by blast
  show ?thesis by (rule definition_code_source_dependencies[OF formed code])
qed

lemma internal_anchor:
  assumes member: "d\<in>D"
  shows "fst d\<in>uses \<and> snd d\<in>rra_carrier (object_structure (artifacts (fst d)))"
proof -
  have code: "definition_code_for (system_interface P d) (system_clause_family P d) (K d)"
    using codes member by blast
  have root: "[]\<in>rra_carrier (object_structure (code_artifact (K d)))"
    by (rule definition_code_properties(3)[OF code])
  show ?thesis using member roots root site_shape[OF member] by auto
qed

lemma installed:
  assumes environment: "environment_formed E"
    and components: "\<forall>u\<in>uses. artifact_at E u (artifacts u) \<and> syntax_references E u (literals u) (callees u)"
  shows "\<forall>d\<in>D.
    definition_code_for (system_interface P d) (system_clause_family P d) (K d) \<and>
    artifact_at E (fst d) (code_artifact (K d)) \<and>
    syntax_references E (fst d) (code_literals (K d)) (code_callees (K d)) \<and>
    native_definition_at E (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))"
proof (intro ballI)
  fix d assume member: "d\<in>D"
  have code: "definition_code_for (system_interface P d) (system_clause_family P d) (K d)"
    using codes member by blast
  have use: "fst d\<in>uses" using member by blast
  have row: "artifact_at E (fst d) (artifacts (fst d)) \<and>
    syntax_references E (fst d) (literals (fst d)) (callees (fst d))"
    using components use by blast
  have fields: "artifact_at E (fst d) (code_artifact (K d))"
    "syntax_references E (fst d) (code_literals (K d)) (code_callees (K d))"
    using row site_shape[OF member] by simp_all
  have native: "native_definition_at E (fst d) [] (code_interface (K d)) (code_clauses (K d))"
    using definition_code_properties(8)[OF code] environment fields by blast
  show "definition_code_for (system_interface P d) (system_clause_family P d) (K d) \<and>
    artifact_at E (fst d) (code_artifact (K d)) \<and>
    syntax_references E (fst d) (code_literals (K d)) (code_callees (K d)) \<and>
    native_definition_at E (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))"
    using code fields native roots member by simp
qed

end

text \<open>
  The family selects actual interface and complete clause fields from one
  formed source system. Its code records retain those exact compilation
  contracts. Empty-root sites make the definition-to-use projection injective.
  The same local family supports closed program compilation and extensions
  whose callees also reach an existing source environment.
\<close>

end
