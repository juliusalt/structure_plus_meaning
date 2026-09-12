theory Factor_Argument_Clauses
  imports Factor_Data_Comparison Factor_Pattern_Determination
begin

section \<open>One fixed pattern builds the argument of one actual call\<close>

definition argument_call_clause ::
  "'a \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> 'a term_pattern \<Rightarrow> ('a,'s,'d) factor_schema" where
  "argument_call_clause x s k p=data_rule (Pattern_Variable x) {(s,k,p)}"

lemma argument_call_formed [simp]:
  "schema_formed (argument_call_clause x s k p) \<longleftrightarrow> pattern_formed p"
  by (simp add: argument_call_clause_def schema_formed_def single_valued_def)

lemma argument_call_variables [simp]:
  "schema_variables (argument_call_clause x s k p)=insert x (pattern_variables p)"
  by (auto simp: argument_call_clause_def schema_variables_def)

lemma argument_call_dependencies [simp]:
  "schema_dependencies (argument_call_clause x s k p)={k}"
  by (auto simp: argument_call_clause_def schema_dependencies_def rel_ran_def)

lemma argument_call_sockets [simp]:
  "schema_sockets (argument_call_clause x s k p)={s}"
  by (auto simp: argument_call_clause_def schema_sockets_def rel_dom_def)

lemma argument_call_ordinary [simp]:
  "schema_material_premises (argument_call_clause x s k p)={}"
  by (simp add: argument_call_clause_def)

lemma rename_argument_call_clause [simp]:
  "rename_schema f h g (argument_call_clause x s k p)=
    argument_call_clause (f x) (h s) (g k) (rename_pattern f p)"
  by (simp add: argument_call_clause_def rename_schema_def map_socket_graph_def)

theorem argument_call_rule:
  assumes variables: "pattern_variables p\<subseteq>{x}"
  shows "schema_rule_instance (argument_call_clause x s k p) X z \<longleftrightarrow>
    pattern_formed p \<and> term_formed z \<and> (k,evaluate_pattern (\<lambda>_. z) p)\<in>X"
proof
  let ?S="argument_call_clause x s k p"
  assume rule: "schema_rule_instance ?S X z"
  obtain V Q where inst: "schema_instance ?S V z Q"
    and support: "\<forall>s d t. (s,d,t)\<in>Q \<longrightarrow> (d,t)\<in>X"
    using rule by (auto simp: schema_rule_instance_def)
  obtain h where assignment: "\<forall>a\<in>schema_variables ?S. (a,h a)\<in>V \<and> term_formed (h a)"
    and head: "z=evaluate_pattern h (schema_conclusion ?S)"
    and body: "Q=evaluate_schema_premises h ?S"
    using schema_instance_evaluation[OF inst] by blast
  have pf: "pattern_formed p" using inst by (simp add: schema_instance_def)
  have operand_value: "z=h x" using head by (simp add: argument_call_clause_def)
  have zf: "term_formed z" using assignment operand_value by simp
  have same: "evaluate_pattern h p=evaluate_pattern (\<lambda>_. z) p"
    by (rule evaluate_pattern_cong) (use variables operand_value in auto)
  have called: "(k,evaluate_pattern (\<lambda>_. z) p)\<in>X"
    using body support by (simp add: argument_call_clause_def evaluate_schema_premises_def same)
  show "pattern_formed p \<and> term_formed z \<and> (k,evaluate_pattern (\<lambda>_. z) p)\<in>X"
    using pf zf called by blast
next
  let ?S="argument_call_clause x s k p"
  assume data: "pattern_formed p \<and> term_formed z \<and> (k,evaluate_pattern (\<lambda>_. z) p)\<in>X"
  have sf: "schema_formed ?S" using data by simp
  have assigned: "\<forall>a\<in>schema_variables ?S. term_formed ((\<lambda>_. z) a)" using data by simp
  have binders: "schema_variables ?S={x}" using variables by auto
  have inst: "schema_instance ?S {(x,z)} z {(s,k,evaluate_pattern (\<lambda>_. z) p)}"
    using schema_evaluation_instance[OF sf assigned] unfolding binders
    by (simp add: argument_call_clause_def evaluate_schema_premises_def)
  have material: "schema_material_satisfied ?S {(x,z)}"
    by (simp add: schema_material_satisfied_def)
  show "schema_rule_instance ?S X z" unfolding schema_rule_instance_def
    by (rule exI[of _ "{(x,z)}"], rule exI[of _ "{(s,k,evaluate_pattern (\<lambda>_. z) p)}"])
      (use inst material data in auto)
qed

theorem argument_call_view:
  assumes "schema_system_formed P" "entry\<notin>system_definitions P"
    "k\<in>system_definitions P" "pattern_formed p"
  shows "positive_view P entry (Pattern_Variable i) {(c,argument_call_clause x s k p)}"
  by (rule positive_view.intro[OF assms(1,2)])
    (use assms(3,4) in \<open>auto simp: single_valued_def\<close>)

theorem argument_call_view_meaning:
  assumes view: "positive_view P entry (Pattern_Variable i) {(c,argument_call_clause x s k p)}"
    and variables: "pattern_variables p\<subseteq>{x}"
  shows "(entry,z)\<in>positive_meaning
      (add_view_definition P entry (Pattern_Variable i) {(c,argument_call_clause x s k p)}) \<longleftrightarrow>
    term_formed z \<and> (k,evaluate_pattern (\<lambda>_. z) p)\<in>positive_meaning P"
proof -
  interpret view: positive_view P entry "Pattern_Variable i" "{(c,argument_call_clause x s k p)}"
    by (rule view)
  have clause: "((entry,c),argument_call_clause x s k p)\<in>system_clauses
      (add_view_definition P entry (Pattern_Variable i) {(c,argument_call_clause x s k p)})"
    by simp
  have pf: "pattern_formed p" using view.formed clause by (auto simp: schema_system_formed_def)
  show ?thesis using view.view_meaning[of z]
    by (simp add: argument_call_rule[OF variables] pf)
qed

text \<open>
  The conclusion binds the future operand. The argument pattern may repeat
  that variable or omit it; it may contain arbitrary formed literal terms.
  One fixed callee and one identified socket supply the only premise.
  The exact rule holds for every supporting relation. Formation of the future
  operand remains necessary even when the argument pattern omits it.

  Fixed-result checking and fixed-scope forwarding use this same rule.
  The construction adds no term constructor, semantic callback, or dynamic
  choice of callee. Native installation uses the existing clause compiler.
\<close>

end
