theory Factor_Clause_Family_Rules
  imports Factor_Clause_Rule_Application Factor_System_Alpha
begin

section \<open>Complete clause families expose the existing rule instances\<close>

lemma ordinary_schema_rule_valuation:
  assumes formed: "schema_formed S" and ordinary: "schema_material_premises S={}"
  shows "schema_rule_instance S M t \<longleftrightarrow>
    (\<exists>f. (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and>
      t=evaluate_pattern f (schema_conclusion S) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern f p)\<in>M))"
proof
  assume "schema_rule_instance S M t"
  then obtain V Q where inst: "schema_instance S V t Q"
    and support: "\<forall>s d x. (s,d,x)\<in>Q \<longrightarrow> (d,x)\<in>M"
    by (auto simp: schema_rule_instance_def)
  obtain f where assignment: "\<forall>a\<in>schema_variables S. (a,f a)\<in>V \<and> term_formed (f a)"
    and head: "t=evaluate_pattern f (schema_conclusion S)" and evaluated: "Q=evaluate_schema_premises f S"
    using schema_instance_evaluation[OF inst] by blast
  show "\<exists>f. (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and>
      t=evaluate_pattern f (schema_conclusion S) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern f p)\<in>M)"
    by (rule exI[of _ f]) (use assignment head support evaluated in \<open>auto; blast\<close>)
next
  assume "\<exists>f. (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and>
      t=evaluate_pattern f (schema_conclusion S) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern f p)\<in>M)"
  then obtain f where assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and head: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern f p)\<in>M" by blast
  have inst: "schema_instance S ((\<lambda>a. (a,f a)) ` schema_variables S) t (evaluate_schema_premises f S)"
    using schema_evaluation_instance[OF formed assignment] head by simp
  show "schema_rule_instance S M t"
    unfolding schema_rule_instance_def
    by (rule exI[of _ "(\<lambda>a. (a,f a)) ` schema_variables S"], rule exI[of _ "evaluate_schema_premises f S"])
      (use inst ordinary support in \<open>auto simp: schema_material_satisfied_def; blast\<close>)
qed

lemma schema_two_clause_rules:
  "(\<exists>c S. (c,S)\<in>{(a,A),(b,B)} \<and> schema_rule_instance S M t) \<longleftrightarrow>
    schema_rule_instance A M t \<or> schema_rule_instance B M t"
  by auto

theorem positive_entry_rule_family:
  "(d,t)\<in>positive_meaning P \<longleftrightarrow> schema_call_formed P d t \<and>
    (\<exists>c S. (c,S)\<in>system_clause_family P d \<and> schema_rule_instance S (positive_meaning P) t)"
proof -
  have support: "{q\<in>positive_meaning P. schema_call_formed P (fst q) (snd q)}=positive_meaning P"
    using positive_meaning_formed by (auto split: prod.splits)
  show ?thesis by (subst positive_meaning_unfold) (simp only: schema_consequence_rule support)
qed

theorem positive_variable_rule_family:
  assumes call: "\<And>t. schema_call_formed P d t \<longleftrightarrow> term_formed t"
  shows "(d,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>c S. (c,S)\<in>system_clause_family P d \<and> schema_rule_instance S (positive_meaning P) t)"
proof -
  have formed: "term_formed t" if "schema_rule_instance S (positive_meaning P) t" for S
    using that schema_instance_formed by (auto simp: schema_rule_instance_def)
  show ?thesis by (simp only: positive_entry_rule_family call; use formed in blast)
qed

end
