theory Factor_Program_Change_Examples
  imports Factor_Program_Changes Factor_Rule_Instances Factor_Pattern_Programs
begin

section \<open>A callee changes while its caller and an independent definition keep their rows\<close>

definition change_caller_schema :: "(unit,unit,nat) factor_schema" where
  "change_caller_schema =
    \<lparr>schema_conclusion=Pattern_Variable (), schema_premises={((),0,Pattern_Variable ())},
     schema_material_premises={}\<rparr>"

definition callee_change_system :: "bool \<Rightarrow> (unit,unit,nat,unit) schema_system" where
  "callee_change_system b =
    \<lparr>system_interfaces={(0,Pattern_Variable ()),(1,Pattern_Variable ()),(2,Pattern_Variable ())},
     system_clauses={((1,()),change_caller_schema),((2,()),recognizer_schema (Pattern_Variable ()))} \<union>
       (if b then {((0,()),recognizer_schema (Pattern_Variable ()))} else {})\<rparr>"

lemma callee_change_formed: "schema_system_formed (callee_change_system b)"
  by (cases b) (auto simp: callee_change_system_def change_caller_schema_def recognizer_schema_def
    schema_system_formed_def schema_formed_def schema_dependencies_def
    system_definitions_def rel_dom_def rel_ran_def single_valued_def)

lemma callee_change_definitions [simp]: "system_definitions (callee_change_system b)={0,1,2}"
  by (auto simp: callee_change_system_def system_definitions_def rel_dom_def)

lemma callee_change_call:
  "schema_call_formed (callee_change_system b) d t\<longleftrightarrow>d\<in>{0,1,2} \<and> term_formed t"
  using callee_change_formed[of b] by (auto simp: schema_call_formed_def callee_change_system_def)

lemma callee_change_edges [simp]: "system_dependency_edges (callee_change_system b)={(1,0)}"
  by (cases b) (auto simp: system_dependency_edges_def callee_change_system_def
    change_caller_schema_def recognizer_schema_def schema_dependencies_def rel_ran_def)

lemma callee_change_changed:
  "system_changed_definitions (callee_change_system False) (callee_change_system True)={0}"
  by (auto simp: system_changed_definitions_def callee_change_system_def)

lemma callee_change_affected:
  "system_affected_definitions (callee_change_system b) {0}={0,1}"
proof -
  have upper: "system_affected_definitions (callee_change_system b) {0}\<subseteq>{0,1}"
    by (rule system_affected_least[OF callee_change_formed]) auto
  have zero: "0\<in>system_affected_definitions (callee_change_system b) {0}"
    using system_affected_seeds[where P="callee_change_system b" and U="{0}"] by auto
  have one: "1\<in>system_affected_definitions (callee_change_system b) {0}"
    by (rule system_affected_step[OF callee_change_formed _ zero]) simp
  show ?thesis using upper zero one by blast
qed

theorem callee_change_comparison_domain:
  "system_comparison_definitions (callee_change_system False) (callee_change_system True) {1,2}={0,1,2}"
  by (auto simp: system_comparison_definitions_def callee_change_changed callee_change_affected)

theorem callee_change_complete_call_domain:
  "system_comparison_calls (callee_change_system False) (callee_change_system True) {1,2} =
    {0,1,2}\<times>{t. term_formed t}"
  by (simp only: system_comparison_calls_def callee_change_comparison_domain)
     (auto simp: callee_change_call)

section \<open>The unchanged caller can change its meaning\<close>

lemma callee_change_false_only:
  assumes truth: "(d,t)\<in>positive_meaning (callee_change_system False)"
  shows "d=2"
  using truth
proof (rule positive_valuation_induct)
  fix e c S f
  assume clause: "((e,c),S)\<in>system_clauses (callee_change_system False)"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and call: "schema_call_formed (callee_change_system False) e (evaluate_pattern f (schema_conclusion S))"
    and children: "\<forall>s a p. (s,a,p)\<in>schema_premises S \<longrightarrow>
      (a,evaluate_pattern f p)\<in>positive_meaning (callee_change_system False) \<and> a=2"
  show "e=2" using clause children
    by (auto simp: callee_change_system_def change_caller_schema_def recognizer_schema_def)
qed

lemma callee_change_true_leaf:
  assumes tf: "term_formed t"
  shows "(0,t)\<in>positive_meaning (callee_change_system True)"
proof -
  let ?S="recognizer_schema (Pattern_Variable ()) :: (unit,unit,nat) factor_schema"
  let ?V="{((),t)}"
  have call: "schema_call_formed (callee_change_system True) 0 t" using tf by (simp add: callee_change_call)
  have clause: "((0,()),?S)\<in>system_clauses (callee_change_system True)"
    by (simp add: callee_change_system_def)
  have inst: "schema_instance ?S ?V t {}"
    using tf by (auto simp: schema_instance_def recognizer_schema_def schema_formed_def schema_variables_def
      schema_premise_instance_def term_bindings_formed_def single_valued_def rel_dom_def)
  have material: "schema_material_satisfied ?S ?V"
    by (simp add: schema_material_satisfied_def recognizer_schema_def)
  have admitted: "admitted_schema_instance (callee_change_system True) 0 () ?V t {}"
    using call clause inst material unfolding admitted_schema_instance_def by blast
  show ?thesis by (rule positive_meaning_step[OF admitted]) simp
qed

lemma callee_change_true_caller:
  assumes tf: "term_formed t"
  shows "(1,t)\<in>positive_meaning (callee_change_system True)"
proof -
  let ?V="{((),t)}"
  let ?Q="{((),0::nat,t)}"
  have child: "(0,t)\<in>positive_meaning (callee_change_system True)" by (rule callee_change_true_leaf[OF tf])
  have call: "schema_call_formed (callee_change_system True) 1 t" using tf by (simp add: callee_change_call)
  have child_call: "schema_call_formed (callee_change_system True) 0 t" by (rule positive_meaning_formed[OF child])
  have clause: "((1,()),change_caller_schema)\<in>system_clauses (callee_change_system True)"
    by (simp add: callee_change_system_def)
  have inst: "schema_instance change_caller_schema ?V t ?Q"
    using tf by (auto simp: schema_instance_def change_caller_schema_def schema_formed_def schema_variables_def
      schema_premise_instance_def term_bindings_formed_def single_valued_def rel_dom_def)
  have material: "schema_material_satisfied change_caller_schema ?V"
    by (simp add: schema_material_satisfied_def change_caller_schema_def)
  have admitted: "admitted_schema_instance (callee_change_system True) 1 () ?V t ?Q"
    using call clause inst material child_call by (auto simp: admitted_schema_instance_def)
  show ?thesis by (rule positive_meaning_step[OF admitted]) (use child in auto)
qed

theorem unchanged_caller_can_change:
  assumes tf: "term_formed t"
  shows "systems_agree_on (callee_change_system False) (callee_change_system True) {1} \<and>
    1\<in>system_affected_definitions (callee_change_system False)
      (system_changed_definitions (callee_change_system False) (callee_change_system True)) \<and>
    (1,t)\<notin>positive_meaning (callee_change_system False) \<and>
    (1,t)\<in>positive_meaning (callee_change_system True)"
  using callee_change_false_only[where d=1 and t=t] callee_change_true_caller[OF tf]
  by (auto simp: systems_agree_on_unchanged callee_change_changed callee_change_affected)

theorem independent_definition_preserved:
  "(2,t)\<in>positive_meaning (callee_change_system False)\<longleftrightarrow>
    (2,t)\<in>positive_meaning (callee_change_system True)"
  by (rule system_unaffected_meaning(2)[OF callee_change_formed callee_change_formed])
    (simp_all add: callee_change_changed callee_change_affected)

text \<open>
  The only changed row is the clause added at definition zero. Definition one
  keeps its complete interface and clause family but calls zero, so it belongs
  to the affected boundary and its truth changes on every formed argument.
  Definition two remains independent and retains its meaning.

  With one and two as public roots, the derived comparison domain contains all
  three definitions. Its call domain contains every formed future term at each
  one. A certificate cannot replace this boundary by the public roots alone or
  by a finite collection of test calls. The Boolean selects between two displayed
  finite clause tables; no Boolean callback occurs in either positive program.
\<close>

end
