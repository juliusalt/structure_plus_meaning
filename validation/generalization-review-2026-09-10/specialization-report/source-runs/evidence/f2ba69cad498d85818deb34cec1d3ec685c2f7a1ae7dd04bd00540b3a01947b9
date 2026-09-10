theory Factor_System_Clauses
  imports Factor_Alpha_Semantics
begin

section \<open>Derived interface lookup and complete clause fibres\<close>

definition system_interface :: "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> 'a term_pattern" where
  "system_interface P d = rel_value (system_interfaces P) d"

definition system_clause_family ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> 'd \<Rightarrow> ('c \<times> ('a,'s,'d) factor_schema) set" where
  "system_clause_family P d = (\<lambda>((e,c),S). (c,S)) ` {q\<in>system_clauses P. fst (fst q)=d}"

lemma system_clause_member [simp]:
  "(c,S) \<in> system_clause_family P d \<longleftrightarrow> ((d,c),S) \<in> system_clauses P"
  by (auto simp: system_clause_family_def intro: rev_image_eqI)

lemma system_interface_member:
  assumes formed: "schema_system_formed P" and member: "d \<in> system_definitions P"
  shows "(d,system_interface P d) \<in> system_interfaces P"
proof -
  obtain p where actual: "(d,p) \<in> system_interfaces P" using member by (auto simp: system_definitions_def rel_dom_def)
  have sv: "single_valued (system_interfaces P)" using formed by (simp add: schema_system_formed_def)
  show ?thesis using rel_value_eq[OF sv actual] actual by (simp add: system_interface_def)
qed

lemma system_interface_unique:
  assumes formed: "schema_system_formed P" and actual: "(d,p) \<in> system_interfaces P"
  shows "system_interface P d = p"
  unfolding system_interface_def by (rule rel_value_eq[OF _ actual]) (use formed in \<open>simp add: schema_system_formed_def\<close>)

lemma system_interface_formed:
  assumes formed: "schema_system_formed P" and member: "d \<in> system_definitions P"
  shows "pattern_formed (system_interface P d)"
  using system_interface_member[OF formed member] formed by (auto simp: schema_system_formed_def)

lemma system_clause_family_finite:
  assumes "schema_system_formed P"
  shows "finite (system_clause_family P d)"
  using assms by (simp add: schema_system_formed_def system_clause_family_def)

lemma system_clause_family_functional:
  assumes "schema_system_formed P"
  shows "single_valued (system_clause_family P d)"
  using assms by (auto simp: schema_system_formed_def single_valued_def)

lemma system_clause_family_formed:
  assumes "schema_system_formed P"
  shows "\<forall>S\<in>rel_ran (system_clause_family P d). schema_formed S"
  using assms by (auto simp: rel_ran_def schema_system_formed_def)

lemma system_clause_family_dependencies:
  assumes "schema_system_formed P"
  shows "(\<Union>S\<in>rel_ran (system_clause_family P d). schema_dependencies S) \<subseteq> system_definitions P"
  using assms by (auto simp: rel_ran_def schema_system_formed_def; blast)

lemma schema_call_at_interface:
  assumes "schema_system_formed P"
  shows "schema_call_formed P d t \<longleftrightarrow> d \<in> system_definitions P \<and> pattern_accepts (system_interface P d) t"
  using assms system_interface_member[OF assms] system_interface_unique[OF assms]
  by (auto simp: schema_call_formed_def system_definitions_def rel_dom_def; blast)

definition system_alpha_variant ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('b,'t,'d,'e) schema_system \<Rightarrow> bool" where
  "system_alpha_variant P Q \<longleftrightarrow> schema_system_formed P \<and> schema_system_formed Q \<and>
    system_definitions P = system_definitions Q \<and>
    (\<forall>d\<in>system_definitions P. \<exists>f h. inj_on f (pattern_variables (system_interface P d)) \<and>
      system_interface Q d = rename_pattern f (system_interface P d) \<and>
      schema_family_variant h (system_clause_family P d) (system_clause_family Q d))"

text \<open>
  Interface lookup and per-definition clause families are derived from the two
  existing system fields. Every clause in a fibre is exactly a source table
  entry. Formation supplies finite functional fibres and their complete
  dependency boundary; no separate list of definitions or clauses is stored.
\<close>

end
