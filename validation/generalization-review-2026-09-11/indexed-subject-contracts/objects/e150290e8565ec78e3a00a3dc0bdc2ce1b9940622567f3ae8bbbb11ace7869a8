theory Factor_SK_Program
  imports Factor_Rule_Instances
begin

section \<open>Nine ordinary clauses with their complete premises\<close>

abbreviation sk_program_s :: "nat term_pattern" where
  "sk_program_s \<equiv> Pattern_Payload []"

abbreviation sk_program_k :: "nat term_pattern" where
  "sk_program_k \<equiv> Pattern_Payload [0]"

abbreviation sk_program_x :: "nat term_pattern" where
  "sk_program_x \<equiv> Pattern_Variable 0"

abbreviation sk_program_y :: "nat term_pattern" where
  "sk_program_y \<equiv> Pattern_Variable 1"

abbreviation sk_program_z :: "nat term_pattern" where
  "sk_program_z \<equiv> Pattern_Variable 2"

abbreviation sk_rule :: "nat term_pattern \<Rightarrow>
  (nat \<times> (nat \<times> nat term_pattern)) set \<Rightarrow> (nat,nat,nat) factor_schema" where
  "sk_rule p B \<equiv> \<lparr>schema_conclusion=p, schema_premises=B, schema_material_premises={}\<rparr>"

definition sk_term_s_clause :: "(nat,nat,nat) factor_schema" where
  "sk_term_s_clause=sk_rule sk_program_s {}"

definition sk_term_k_clause :: "(nat,nat,nat) factor_schema" where
  "sk_term_k_clause=sk_rule sk_program_k {}"

definition sk_term_app_clause :: "(nat,nat,nat) factor_schema" where
  "sk_term_app_clause=sk_rule (Pattern_Pair sk_program_x sk_program_y)
    {(0,0,sk_program_x),(1,0,sk_program_y)}"

definition sk_step_k_clause :: "(nat,nat,nat) factor_schema" where
  "sk_step_k_clause=sk_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair sk_program_k sk_program_x) sk_program_y) sk_program_x)
    {(0,0,sk_program_x),(1,0,sk_program_y)}"

definition sk_step_s_clause :: "(nat,nat,nat) factor_schema" where
  "sk_step_s_clause=sk_rule
    (Pattern_Pair (Pattern_Pair (Pattern_Pair (Pattern_Pair sk_program_s sk_program_x) sk_program_y) sk_program_z)
      (Pattern_Pair (Pattern_Pair sk_program_x sk_program_z) (Pattern_Pair sk_program_y sk_program_z)))
    {(0,0,sk_program_x),(1,0,sk_program_y),(2,0,sk_program_z)}"

definition sk_step_left_clause :: "(nat,nat,nat) factor_schema" where
  "sk_step_left_clause=sk_rule
    (Pattern_Pair (Pattern_Pair sk_program_x sk_program_z) (Pattern_Pair sk_program_y sk_program_z))
    {(0,1,Pattern_Pair sk_program_x sk_program_y),(1,0,sk_program_z)}"

definition sk_step_right_clause :: "(nat,nat,nat) factor_schema" where
  "sk_step_right_clause=sk_rule
    (Pattern_Pair (Pattern_Pair sk_program_z sk_program_x) (Pattern_Pair sk_program_z sk_program_y))
    {(0,1,Pattern_Pair sk_program_x sk_program_y),(1,0,sk_program_z)}"

definition sk_refl_clause :: "(nat,nat,nat) factor_schema" where
  "sk_refl_clause=sk_rule (Pattern_Pair sk_program_x sk_program_x) {(0,0,sk_program_x)}"

definition sk_trans_clause :: "(nat,nat,nat) factor_schema" where
  "sk_trans_clause=sk_rule (Pattern_Pair sk_program_x sk_program_z)
    {(0,1,Pattern_Pair sk_program_x sk_program_y),(1,2,Pattern_Pair sk_program_y sk_program_z)}"

lemmas sk_clause_defs = sk_term_s_clause_def sk_term_k_clause_def sk_term_app_clause_def
  sk_step_k_clause_def sk_step_s_clause_def sk_step_left_clause_def sk_step_right_clause_def
  sk_refl_clause_def sk_trans_clause_def

definition sk_system :: "(nat,nat,nat,nat) schema_system" where
  "sk_system=\<lparr>system_interfaces={(0,sk_program_x),(1,sk_program_x),(2,sk_program_x)},
    system_clauses={((0,0),sk_term_s_clause),((0,1),sk_term_k_clause),((0,2),sk_term_app_clause),
      ((1,0),sk_step_k_clause),((1,1),sk_step_s_clause),((1,2),sk_step_left_clause),
      ((1,3),sk_step_right_clause),((2,0),sk_refl_clause),((2,1),sk_trans_clause)}\<rparr>"

lemma sk_system_definitions [simp]: "system_definitions sk_system={0,1,2}"
  by (auto simp: system_definitions_def sk_system_def rel_dom_def)

lemma sk_system_formed [simp]: "schema_system_formed sk_system"
  by (auto simp: schema_system_formed_def sk_system_def sk_clause_defs schema_formed_def
      schema_dependencies_def system_definitions_def rel_dom_def rel_ran_def single_valued_def octets_formed_def)

lemma sk_system_observation_free [simp]: "system_observation_free sk_system"
  by (auto simp: system_observation_free_def sk_system_def sk_clause_defs)

lemma sk_clause_members:
  "((0,0),sk_term_s_clause)\<in>system_clauses sk_system"
  "((0,1),sk_term_k_clause)\<in>system_clauses sk_system"
  "((0,2),sk_term_app_clause)\<in>system_clauses sk_system"
  "((1,0),sk_step_k_clause)\<in>system_clauses sk_system"
  "((1,1),sk_step_s_clause)\<in>system_clauses sk_system"
  "((1,2),sk_step_left_clause)\<in>system_clauses sk_system"
  "((1,3),sk_step_right_clause)\<in>system_clauses sk_system"
  "((2,0),sk_refl_clause)\<in>system_clauses sk_system"
  "((2,1),sk_trans_clause)\<in>system_clauses sk_system"
  by (simp_all add: sk_system_def)

lemma sk_system_call [simp]:
  "schema_call_formed sk_system d t \<longleftrightarrow> d\<in>{0,1,2} \<and> term_formed t"
  unfolding schema_call_formed_def
  by (simp only: sk_system_formed) (auto simp: sk_system_def)

lemma sk_clause_variables:
  "schema_variables sk_term_s_clause={}"
  "schema_variables sk_term_k_clause={}"
  "schema_variables sk_term_app_clause={0,1}"
  "schema_variables sk_step_k_clause={0,1}"
  "schema_variables sk_step_s_clause={0,1,2}"
  "schema_variables sk_step_left_clause={0,1,2}"
  "schema_variables sk_step_right_clause={0,1,2}"
  "schema_variables sk_refl_clause={0}"
  "schema_variables sk_trans_clause={0,1,2}"
  by (auto simp: schema_variables_def sk_clause_defs)

lemma sk_positive_rule:
  assumes clause: "((d,c),S)\<in>system_clauses sk_system"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning sk_system"
  shows "(d,evaluate_pattern f (schema_conclusion S))\<in>positive_meaning sk_system"
proof -
  have sf: "schema_formed S" and member: "d\<in>system_definitions sk_system"
    using sk_system_formed clause by (auto simp: schema_system_formed_def)
  have head_formed: "term_formed (evaluate_pattern f (schema_conclusion S))"
    by (rule evaluate_pattern_formed)
       (use sf assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have call: "schema_call_formed sk_system d (evaluate_pattern f (schema_conclusion S))"
    using member head_formed by simp
  have supported: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
    schema_call_formed sk_system e (evaluate_pattern f p) \<and>
    (e,evaluate_pattern f p)\<in>positive_meaning sk_system"
  proof (intro allI impI)
    fix s e p assume source: "(s,e,p)\<in>schema_premises S"
    have positive: "(e,evaluate_pattern f p)\<in>positive_meaning sk_system"
      using support source by blast
    have formed: "schema_call_formed sk_system e (evaluate_pattern f p)"
      by (rule positive_meaning_formed[OF positive])
    show "schema_call_formed sk_system e (evaluate_pattern f p) \<and>
      (e,evaluate_pattern f p)\<in>positive_meaning sk_system"
      using formed positive by blast
  qed
  show ?thesis by (rule positive_valuation_step[OF sk_system_formed sk_system_observation_free
        clause assignment call supported])
qed

text \<open>
  Definition 0 recognizes terms, definition 1 recognizes a single reduction,
  and definition 2 recognizes finite reduction. Their bodies are the explicit
  ordinary schemas above. Every recursive call names its callee occurrence and
  retains its own premise socket. All three interfaces accept a formed term;
  the membership clauses establish the smaller SK domain as positive truth.

  The two payload constants are an explicit encoding choice in this program.
  No existing meaning relation inspects them to select an SK operation. Source
  definition, clause, binder, and socket coordinates will be relocated by the
  native compiler with its existing preservation and reflection theorems.
\<close>

end
