theory Factor_Argument_Packages
  imports Factor_Argument_Clauses Factor_Single_Clause_Packages
begin

section \<open>Every fixed argument pattern has a native package extension\<close>

theorem native_argument_call_package_total:
  fixes E :: "local_address option artifact_environment"
    and p :: "'a term_pattern"
  assumes package: "native_package_at E pu pr P" and callee: "k\<in>system_definitions P"
    and pattern: "pattern_formed p" and variables: "pattern_variables p\<subseteq>{x}"
  shows "\<exists>F u v Q. environment_formed F \<and> environment_included E F \<and>
    u\<notin>environment_uses E \<and> (u,[])\<notin>system_definitions P \<and>
    native_package_at F pu pr P \<and> native_package_at F v [] Q \<and>
    system_definitions Q=insert (u,[]) (system_definitions P) \<and>
    (\<forall>z. schema_call_formed Q (u,[]) z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. ((u,[]),z)\<in>positive_meaning Q \<longleftrightarrow>
      term_formed z \<and> (k,evaluate_pattern (\<lambda>_. z) p)\<in>positive_meaning P) \<and>
    (\<forall>d\<in>system_definitions P. \<forall>z.
      (schema_call_formed Q d z \<longleftrightarrow> schema_call_formed P d z) \<and>
      ((d,z)\<in>positive_meaning Q \<longleftrightarrow> (d,z)\<in>positive_meaning P)) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s a. binds_slot F w s a \<longleftrightarrow> binds_slot E w s a)"
proof -
  let ?S="argument_call_clause x () k p"
  have sf: "schema_formed ?S" using pattern by simp
  have dependencies: "schema_dependencies ?S\<subseteq>system_definitions P" using callee by simp
  obtain F u v Q T where built: "environment_formed F" "environment_included E F"
    "u\<notin>environment_uses E" "(u,[])\<notin>system_definitions P"
    "native_package_at F pu pr P" "native_package_at F v [] Q"
    "system_definitions Q=insert (u,[]) (system_definitions P)"
    "native_single_clause_at F u [] T"
    "\<forall>X t. schema_rule_instance T X t \<longleftrightarrow> schema_rule_instance ?S X t"
    "\<forall>d\<in>system_definitions P. \<forall>z.
      (schema_call_formed Q d z \<longleftrightarrow> schema_call_formed P d z) \<and>
      ((d,z)\<in>positive_meaning Q \<longleftrightarrow> (d,z)\<in>positive_meaning P)"
    "\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A"
    "\<forall>w\<in>environment_uses E. \<forall>s a. binds_slot F w s a \<longleftrightarrow> binds_slot E w s a"
    using native_single_clause_package_total[OF package sf dependencies] by blast
  have member: "(u,[])\<in>system_definitions Q" using built(7) by simp
  have read: "native_single_clause_at F (fst (u,[])) (snd (u,[])) T" using built(8) by simp
  have call: "schema_call_formed Q (u,[]) z \<longleftrightarrow> term_formed z" for z
    by (rule native_single_clause_call[OF built(6) member read])
  have callee_meaning: "(k,t)\<in>positive_meaning Q \<longleftrightarrow> (k,t)\<in>positive_meaning P" for t
    using built(10)[rule_format, OF callee, of t] by blast
  have meaning: "((u,[]),z)\<in>positive_meaning Q \<longleftrightarrow>
      term_formed z \<and> (k,evaluate_pattern (\<lambda>_. z) p)\<in>positive_meaning P" for z
    by (simp only: native_single_clause_meaning[OF built(6) member read] built(9)[rule_format]
      argument_call_rule[OF variables] pattern callee_meaning; simp)
  show ?thesis by (rule exI[of _ F], rule exI[of _ u], rule exI[of _ v], rule exI[of _ Q])
    (use built(1-7,10-12) call meaning in blast)
qed

text \<open>
  The general single-clause compiler supplies actual native syntax, including
  private binder and socket renaming. Its complete rule contract composes
  with fixed-pattern argument construction. The old package remains readable
  in the same extension and every old call, positive meaning, artifact, and
  outgoing binding is preserved. The new variable interface admits every
  formed operand; it does not claim to copy an old entry's interface.
\<close>

end
