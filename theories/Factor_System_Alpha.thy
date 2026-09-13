theory Factor_System_Alpha
  imports Factor_System_Clauses Factor_Positive_Meaning
begin

section \<open>Independent positive meaning under private interface and clause renaming\<close>

lemma system_alpha_identity:
  assumes formed: "schema_system_formed P"
  shows "system_alpha_variant P P"
proof -
  have fields: "\<exists>f h. inj_on f (pattern_variables (system_interface P d)) \<and>
    system_interface P d=rename_pattern f (system_interface P d) \<and>
    schema_family_variant h (system_clause_family P d) (system_clause_family P d)" for d
    by (rule exI[of _ id], rule exI[of _ id])
      (use schema_family_variant_identity[OF system_clause_family_finite[OF formed]
        system_clause_family_functional[OF formed], of d] in simp)
  show ?thesis using formed fields by (simp add: system_alpha_variant_def)
qed

lemma system_alpha_calls:
  assumes variant: "system_alpha_variant P Q"
  shows "schema_call_formed P d t \<longleftrightarrow> schema_call_formed Q d t"
proof -
  have pf: "schema_system_formed P" and qf: "schema_system_formed Q"
    and defs: "system_definitions P = system_definitions Q" using variant by (auto simp: system_alpha_variant_def)
  show ?thesis
  proof (cases "d \<in> system_definitions P")
    case True
    obtain f h where fields: "inj_on f (pattern_variables (system_interface P d))"
      "system_interface Q d = rename_pattern f (system_interface P d)"
      "schema_family_variant h (system_clause_family P d) (system_clause_family Q d)"
      using variant True unfolding system_alpha_variant_def by blast
    have accepted: "pattern_accepts (system_interface Q d) t \<longleftrightarrow> pattern_accepts (system_interface P d) t"
      using pattern_accepts_alpha[OF fields(1)] fields(2) by simp
    show ?thesis by (simp only: schema_call_at_interface[OF pf] schema_call_at_interface[OF qf] accepted defs)
  next
    case False
    show ?thesis using False defs
      by (simp only: schema_call_at_interface[OF pf] schema_call_at_interface[OF qf]) auto
  qed
qed

lemma system_alpha_rules:
  assumes variant: "system_alpha_variant P Q" and member: "d \<in> system_definitions P"
  shows "(\<exists>c S. (c,S) \<in> system_clause_family Q d \<and> schema_rule_instance S X t) \<longleftrightarrow>
    (\<exists>c S. (c,S) \<in> system_clause_family P d \<and> schema_rule_instance S X t)"
proof -
  obtain h where family: "schema_family_variant h (system_clause_family P d) (system_clause_family Q d)"
    using variant member unfolding system_alpha_variant_def by blast
  show ?thesis by (rule schema_family_variant_rules[OF family])
qed

lemma schema_consequence_rule:
  "(d,t) \<in> schema_consequences P X \<longleftrightarrow> schema_call_formed P d t \<and>
    (\<exists>c S. (c,S) \<in> system_clause_family P d \<and>
      schema_rule_instance S {q\<in>X. schema_call_formed P (fst q) (snd q)} t)"
  by (auto simp: schema_consequences_def admitted_schema_instance_def schema_rule_instance_def; blast)

theorem system_alpha_consequences:
  fixes P :: "('a,'s,'d,'c) schema_system" and Q :: "('b,'t,'d,'e) schema_system"
  assumes variant: "system_alpha_variant P Q"
  shows "schema_consequences P = schema_consequences Q"
proof (rule ext, rule set_eqI)
  fix X :: "('d \<times> factor_term) set" and call :: "'d \<times> factor_term"
  obtain d t where shape: "call=(d,t)" by (cases call)
  have calls: "\<And>e x. schema_call_formed P e x \<longleftrightarrow> schema_call_formed Q e x"
    by (rule system_alpha_calls[OF variant])
  show "call \<in> schema_consequences P X \<longleftrightarrow> call \<in> schema_consequences Q X"
  proof (cases "d \<in> system_definitions P")
    case True
    show ?thesis by (simp only: shape schema_consequence_rule calls system_alpha_rules[OF variant True])
  next
    case False
    have pc: "\<not> schema_call_formed P d t" using False schema_call_formed_target[of P d t] by blast
    have qc: "\<not> schema_call_formed Q d t" using pc calls[of d t] by blast
    show ?thesis by (simp add: shape schema_consequence_rule pc qc)
  qed
qed

theorem system_alpha_positive_meaning:
  assumes "system_alpha_variant P Q"
  shows "positive_meaning P = positive_meaning Q"
  by (simp only: positive_meaning_def system_alpha_consequences[OF assms])

text \<open>
  Interface acceptance and complete clause rule instances are compared before
  considering derivations. Each premise argument is checked against its callee
  interface, so the comparison also preserves the application boundary. The
  two consequence operators are literally equal on every support relation;
  their independently defined least fixed points therefore agree.
\<close>

end
