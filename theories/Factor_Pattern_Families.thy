theory Factor_Pattern_Families
  imports Factor_Pattern_Programs Factor_System_Alpha
begin

section \<open>Complete finite families of ordinary recognition clauses\<close>

lemma recognizer_schema_rule:
  fixes p :: "'a term_pattern" and X :: "('d \<times> factor_term) set"
  shows "schema_rule_instance (recognizer_schema p :: ('a,'s,'d) factor_schema) X t \<longleftrightarrow>
    pattern_accepts p t"
proof -
  let ?S="recognizer_schema p :: ('a,'s,'d) factor_schema"
  show ?thesis
  proof
    assume rule: "schema_rule_instance ?S X t"
    obtain V and Q :: "('s \<times> ('d \<times> factor_term)) set" where inst: "schema_instance ?S V t Q"
      using rule unfolding schema_rule_instance_def by blast
    have formed: "term_formed t" using schema_instance_formed[OF inst] by blast
    show "pattern_accepts p t" using inst formed
      by (auto simp: schema_instance_def recognizer_schema_def schema_variables_def pattern_accepts_def)
  next
    assume accepts: "pattern_accepts p t"
    obtain V where bound: "term_bindings_formed (pattern_variables p) V"
      and head: "pattern_instance V p t" using accepts by (auto simp: pattern_accepts_def)
    have formed: "pattern_formed p" by (rule pattern_instance_formed_pattern[OF head])
    have inst: "schema_instance ?S V t {}"
      using bound head formed
      by (auto simp: schema_instance_def recognizer_schema_def schema_variables_def
        schema_formed_def schema_premise_instance_def single_valued_def)
    have material: "schema_material_satisfied ?S V"
      by (simp add: schema_material_satisfied_def recognizer_schema_def)
    show "schema_rule_instance ?S X t"
      using inst material unfolding schema_rule_instance_def by blast
  qed
qed

definition pattern_family_system ::
  "'a \<Rightarrow> ('c \<times> 'a term_pattern) set \<Rightarrow> ('a,unit,unit,'c) schema_system" where
  "pattern_family_system a C =
    \<lparr>system_interfaces={((),Pattern_Variable a)},
     system_clauses=(\<lambda>(c,p). (((),c),recognizer_schema p)) ` C\<rparr>"

lemma pattern_family_formed:
  assumes "finite C" "single_valued C" "\<forall>c p. (c,p)\<in>C \<longrightarrow> pattern_formed p"
  shows "schema_system_formed (pattern_family_system a C)"
  using assms by (auto simp: pattern_family_system_def schema_system_formed_def
    recognizer_schema_def schema_formed_def schema_dependencies_def system_definitions_def
    rel_dom_def rel_ran_def single_valued_def)

lemma pattern_family_definitions [simp]:
  "system_definitions (pattern_family_system a C)={()}"
  by (auto simp: pattern_family_system_def system_definitions_def rel_dom_def)

lemma pattern_family_clause:
  "(c,S)\<in>system_clause_family (pattern_family_system a C) () \<longleftrightarrow>
    (\<exists>p. (c,p)\<in>C \<and> S=recognizer_schema p)"
  by (auto simp: pattern_family_system_def intro: rev_image_eqI)

lemma pattern_family_call:
  assumes "schema_system_formed (pattern_family_system a C)"
  shows "schema_call_formed (pattern_family_system a C) () t \<longleftrightarrow> term_formed t"
  using assms by (simp add: schema_call_formed_def pattern_family_system_def)

theorem pattern_family_consequences:
  assumes formed: "schema_system_formed (pattern_family_system a C)"
  shows "((),t)\<in>schema_consequences (pattern_family_system a C) X \<longleftrightarrow>
    (\<exists>c p. (c,p)\<in>C \<and> pattern_accepts p t)"
proof
  assume consequence: "((),t)\<in>schema_consequences (pattern_family_system a C) X"
  obtain c S where clause: "(c,S)\<in>system_clause_family (pattern_family_system a C) ()"
    and rule: "schema_rule_instance S
      {q\<in>X. schema_call_formed (pattern_family_system a C) (fst q) (snd q)} t"
    using consequence by (simp only: schema_consequence_rule) blast
  obtain p where row: "(c,p)\<in>C" "S=recognizer_schema p"
    using clause by (simp only: pattern_family_clause) blast
  have accepts: "pattern_accepts p t" using rule row(2) by (simp add: recognizer_schema_rule)
  show "\<exists>c p. (c,p)\<in>C \<and> pattern_accepts p t" using row(1) accepts by blast
next
  assume "\<exists>c p. (c,p)\<in>C \<and> pattern_accepts p t"
  then obtain c p where row: "(c,p)\<in>C" and accepts: "pattern_accepts p t" by blast
  have tf: "term_formed t" using accepts by (simp add: pattern_accepts_def)
  have call: "schema_call_formed (pattern_family_system a C) () t"
    using tf by (simp only: pattern_family_call[OF formed])
  have clause: "(c,recognizer_schema p)\<in>system_clause_family (pattern_family_system a C) ()"
    by (simp only: pattern_family_clause, rule exI[of _ p]) (use row in simp)
  show "((),t)\<in>schema_consequences (pattern_family_system a C) X"
    by (simp only: schema_consequence_rule, rule conjI[OF call],
        rule exI[of _ c], rule exI[of _ "recognizer_schema p"])
      (use clause accepts in \<open>simp only: recognizer_schema_rule\<close>)
qed

theorem pattern_family_meaning:
  assumes "schema_system_formed (pattern_family_system a C)"
  shows "((),t)\<in>positive_meaning (pattern_family_system a C) \<longleftrightarrow>
    (\<exists>c p. (c,p)\<in>C \<and> pattern_accepts p t)"
  by (subst positive_meaning_unfold, rule pattern_family_consequences[OF assms])

lemma pattern_family_occurrences:
  "rel_dom (system_clauses (pattern_family_system a C)) = (\<lambda>c. ((),c)) ` rel_dom C"
  by (auto simp: pattern_family_system_def rel_dom_def image_iff; force)

lemma pattern_family_observation_free:
  "system_observation_free (pattern_family_system a C)"
  by (auto simp: system_observation_free_def pattern_family_system_def recognizer_schema_def)

lemma empty_pattern_family_formed [simp]: "schema_system_formed (pattern_family_system a {})"
  by (rule pattern_family_formed) (auto simp: single_valued_def)

corollary empty_pattern_family:
  "schema_call_formed (pattern_family_system a {}) () t \<longleftrightarrow> term_formed t"
  "positive_meaning (pattern_family_system a {})={}"
proof -
  show "schema_call_formed (pattern_family_system a {}) () t \<longleftrightarrow> term_formed t"
    by (rule pattern_family_call[OF empty_pattern_family_formed])
  show "positive_meaning (pattern_family_system a {})={}"
    by (auto simp: pattern_family_meaning[OF empty_pattern_family_formed])
qed

text \<open>
  The family contains actual finite patterns at distinct clause coordinates.
  Its complete consequence operator accepts precisely their union, for every
  support relation. Each clause has its own binding scope. Repeated equal
  patterns retain their distinct clause occurrences; an empty family has a
  formed interface and no true calls. The interface binder is independent of
  every clause binder. No semantic relation is supplied as a rule callback.
\<close>

end
