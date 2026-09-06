theory Factor_Rule_Instances
  imports Factor_Positive_Meaning
begin

section \<open>Calculating the existing finite pattern instances\<close>

fun evaluate_pattern :: "('a \<Rightarrow> factor_term) \<Rightarrow> 'a term_pattern \<Rightarrow> factor_term" where
  "evaluate_pattern f (Pattern_Variable a)=f a"
| "evaluate_pattern f (Pattern_Target t)=Target_Term t"
| "evaluate_pattern f (Pattern_Payload b)=Payload_Term b"
| "evaluate_pattern f (Pattern_Pair p q)=Pair_Term (evaluate_pattern f p) (evaluate_pattern f q)"

lemma evaluate_pattern_instance:
  assumes "pattern_formed p" "\<forall>a\<in>pattern_variables p. (a,f a)\<in>V"
  shows "pattern_instance V p (evaluate_pattern f p)"
  using assms by (induction p) auto

lemma evaluate_pattern_formed:
  assumes "pattern_formed p" "\<forall>a\<in>pattern_variables p. term_formed (f a)"
  shows "term_formed (evaluate_pattern f p)"
  using assms by (induction p) auto

lemma pattern_instance_evaluation:
  assumes sv: "single_valued V" and inst: "pattern_instance V p t"
    and assignment: "\<forall>a\<in>pattern_variables p. (a,f a)\<in>V"
  shows "t=evaluate_pattern f p"
  by (rule pattern_instance_unique[OF sv inst evaluate_pattern_instance])
     (use pattern_instance_formed_pattern[OF inst] assignment in auto)

definition evaluate_schema_premises ::
  "('a \<Rightarrow> factor_term) \<Rightarrow> ('a,'s,'d) factor_schema \<Rightarrow>
    ('s \<times> ('d \<times> factor_term)) set" where
  "evaluate_schema_premises f S =
    (\<lambda>(s,d,p). (s,d,evaluate_pattern f p)) ` schema_premises S"

lemma evaluate_schema_premises_member [simp]:
  "(s,d,t)\<in>evaluate_schema_premises f S \<longleftrightarrow>
    (\<exists>p. (s,d,p)\<in>schema_premises S \<and> t=evaluate_pattern f p)"
proof
  assume "(s,d,t)\<in>evaluate_schema_premises f S"
  then show "\<exists>p. (s,d,p)\<in>schema_premises S \<and> t=evaluate_pattern f p"
    by (auto simp: evaluate_schema_premises_def)
next
  assume "\<exists>p. (s,d,p)\<in>schema_premises S \<and> t=evaluate_pattern f p"
  then obtain p where source: "(s,d,p)\<in>schema_premises S" and head_value: "t=evaluate_pattern f p"
    by blast
  have "(\<lambda>(s,d,p). (s,d,evaluate_pattern f p)) (s,d,p) \<in>
    (\<lambda>(s,d,p). (s,d,evaluate_pattern f p)) ` schema_premises S"
    by (rule imageI[OF source])
  then show "(s,d,t)\<in>evaluate_schema_premises f S"
    by (simp add: evaluate_schema_premises_def head_value)
qed

lemma schema_evaluation_instance:
  assumes sf: "schema_formed S" and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
  shows "schema_instance S ((\<lambda>a. (a,f a)) ` schema_variables S)
    (evaluate_pattern f (schema_conclusion S)) (evaluate_schema_premises f S)"
proof -
  let ?V = "(\<lambda>a. (a,f a)) ` schema_variables S"
  let ?Q = "evaluate_schema_premises f S"
  have bindings: "term_bindings_formed (schema_variables S) ?V"
    using schema_variables_finite[OF sf] assignment
    by (auto simp: term_bindings_formed_def single_valued_def rel_dom_def)
  have head: "pattern_instance ?V (schema_conclusion S) (evaluate_pattern f (schema_conclusion S))"
    by (rule evaluate_pattern_instance)
       (use sf in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have finite: "finite ?Q" using sf
    by (simp add: evaluate_schema_premises_def schema_formed_def)
  have sv: "single_valued ?Q" using sf
    by (auto simp: evaluate_schema_premises_def schema_formed_def single_valued_def; metis)
  have domain: "rel_dom ?Q=rel_dom (schema_premises S)"
    by (auto simp: rel_dom_def)
  have each: "\<And>s d p. (s,d,p)\<in>schema_premises S \<Longrightarrow>
    pattern_instance ?V p (evaluate_pattern f p)"
    by (rule evaluate_pattern_instance)
       (use sf in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have evaluated: "schema_premise_instance S ?V ?Q"
    using finite sv domain each
    by (auto simp: schema_premise_instance_def; blast)
  show ?thesis using sf bindings head evaluated by (simp add: schema_instance_def)
qed

lemma schema_instance_evaluation:
  fixes S :: "('a,'s,'d) factor_schema"
  assumes inst: "schema_instance S V t Q"
  shows "\<exists>f. (\<forall>a\<in>schema_variables S. (a,f a)\<in>V \<and> term_formed (f a)) \<and>
    t=evaluate_pattern f (schema_conclusion S) \<and> Q=evaluate_schema_premises f S"
proof -
  have bindings: "term_bindings_formed (schema_variables S) V"
    and head: "pattern_instance V (schema_conclusion S) t"
    using inst by (auto simp: schema_instance_def)
  have all: "\<forall>a\<in>schema_variables S. \<exists>x. (a,x)\<in>V \<and> term_formed x"
    using bindings by (auto simp: term_bindings_formed_def rel_dom_def; blast)
  obtain f where assignment: "\<forall>a\<in>schema_variables S. (a,f a)\<in>V \<and> term_formed (f a)"
    using bchoice[OF all] by blast
  have sv: "single_valued V" using bindings by (simp add: term_bindings_formed_def)
  have head_value: "t=evaluate_pattern f (schema_conclusion S)"
    by (rule pattern_instance_evaluation[OF sv head])
       (use assignment in \<open>auto simp: schema_variables_def\<close>)
  have body: "\<And>s d p. (s,d,p)\<in>schema_premises S \<Longrightarrow>
    pattern_instance V p (evaluate_pattern f p)"
    by (rule evaluate_pattern_instance)
       (use inst assignment in \<open>auto simp: schema_instance_def schema_formed_def schema_variables_def\<close>)
  have same: "Q=evaluate_schema_premises f S"
  proof (rule set_eqI)
    fix row :: "'s \<times> ('d \<times> factor_term)"
    obtain s d x where shape: "row=(s,d,x)" by (cases row) auto
    have each: "\<And>p. (s,d,p)\<in>schema_premises S \<Longrightarrow>
      pattern_instance V p x \<longleftrightarrow> x=evaluate_pattern f p"
      using pattern_instance_unique[OF sv _ body] body by blast
    show "row\<in>Q \<longleftrightarrow> row\<in>evaluate_schema_premises f S"
      using schema_instance_premise_iff[OF inst, of s d x] each by (auto simp: shape; blast)
  qed
  show ?thesis using assignment head_value same by blast
qed

section \<open>Derived valuation rules and induction\<close>

lemma schema_consequences_valuationD:
  assumes member: "(d,t)\<in>schema_consequences P X"
  shows "\<exists>c S f. ((d,c),S)\<in>system_clauses P \<and>
    (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and>
    t=evaluate_pattern f (schema_conclusion S) \<and> schema_call_formed P d t \<and>
    (\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      schema_call_formed P e (evaluate_pattern f p) \<and> (e,evaluate_pattern f p)\<in>X)"
proof -
  obtain c V Q S where clause: "((d,c),S)\<in>system_clauses P"
    and inst: "schema_instance S V t Q" and call: "schema_call_formed P d t"
    and body: "\<forall>s e x. (s,e,x)\<in>Q \<longrightarrow> schema_call_formed P e x \<and> (e,x)\<in>X"
    using member by (auto simp: schema_consequences_def admitted_schema_instance_def)
  obtain f where assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and head: "t=evaluate_pattern f (schema_conclusion S)"
    and evaluated: "Q=evaluate_schema_premises f S"
    using schema_instance_evaluation[OF inst] by blast
  have support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
    schema_call_formed P e (evaluate_pattern f p) \<and> (e,evaluate_pattern f p)\<in>X"
    using body evaluated by auto
  show ?thesis using clause assignment head call support by blast
qed

lemma ordinary_positive_valuation_step:
  assumes clause: "((d,c),S)\<in>system_clauses P"
    and ordinary: "schema_material_premises S={}"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and call: "schema_call_formed P d (evaluate_pattern f (schema_conclusion S))"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning P"
  shows "(d,evaluate_pattern f (schema_conclusion S))\<in>positive_meaning P"
proof -
  have sf: "schema_formed S" using call clause
    by (auto simp: schema_call_formed_def schema_system_formed_def)
  let ?V="(\<lambda>a. (a,f a)) ` schema_variables S"
  let ?Q="evaluate_schema_premises f S"
  have inst: "schema_instance S ?V (evaluate_pattern f (schema_conclusion S)) ?Q"
    by (rule schema_evaluation_instance[OF sf assignment])
  have material: "schema_material_satisfied S ?V"
    by (rule empty_schema_material_satisfied[OF ordinary])
  have children: "\<forall>s e x. (s,e,x)\<in>?Q \<longrightarrow>
    schema_call_formed P e x \<and> (e,x)\<in>positive_meaning P"
    using support by (auto intro: positive_meaning_formed)
  have admitted: "admitted_schema_instance P d c ?V
    (evaluate_pattern f (schema_conclusion S)) ?Q"
    using call clause inst material children unfolding admitted_schema_instance_def by blast
  show ?thesis by (rule positive_meaning_step[OF admitted]) (use children in blast)
qed

theorem positive_valuation_induct:
  assumes holds: "(d,t)\<in>positive_meaning P"
    and step: "\<And>d c S f. ((d,c),S)\<in>system_clauses P \<Longrightarrow>
      (\<forall>a\<in>schema_variables S. term_formed (f a)) \<Longrightarrow>
      schema_call_formed P d (evaluate_pattern f (schema_conclusion S)) \<Longrightarrow>
      (\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning P \<and> property e (evaluate_pattern f p)) \<Longrightarrow>
      property d (evaluate_pattern f (schema_conclusion S))"
  shows "property d t"
proof -
  let ?X="{(d,t). (d,t)\<in>positive_meaning P \<and> property d t}"
  have included: "schema_consequences P ?X \<subseteq> schema_consequences P (positive_meaning P)"
    by (rule monoD[OF schema_consequences_mono]) auto
  have stable: "schema_consequences P ?X \<subseteq> ?X"
  proof
    fix z assume member: "z\<in>schema_consequences P ?X"
    obtain e x where shape: "z=(e,x)" by (cases z)
    have positive: "(e,x)\<in>positive_meaning P"
      using included member shape positive_meaning_unfold[of P] by blast
    have source: "(e,x)\<in>schema_consequences P ?X" using member shape by simp
    obtain c S f where parts: "((e,c),S)\<in>system_clauses P"
      "\<forall>a\<in>schema_variables S. term_formed (f a)"
      "x=evaluate_pattern f (schema_conclusion S)" "schema_call_formed P e x"
      "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
        schema_call_formed P d (evaluate_pattern f p) \<and> (d,evaluate_pattern f p)\<in>?X"
      using schema_consequences_valuationD[OF source] by blast
    have call: "schema_call_formed P e (evaluate_pattern f (schema_conclusion S))"
      using parts(3,4) by simp
    have support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow>
      (d,evaluate_pattern f p)\<in>positive_meaning P \<and> property d (evaluate_pattern f p)"
      using parts(5) by auto
    have result: "property e x" using step[OF parts(1,2) call support] parts(3) by simp
    show "z\<in>?X" using shape positive result by simp
  qed
  show ?thesis using positive_meaning_least[OF stable] holds by blast
qed

theorem schema_consequences_valuation:
  assumes formed: "schema_system_formed P" and ordinary: "system_observation_free P"
  shows "(d,t)\<in>schema_consequences P X \<longleftrightarrow>
    (\<exists>c S f. ((d,c),S)\<in>system_clauses P \<and>
      (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and>
      t=evaluate_pattern f (schema_conclusion S) \<and> schema_call_formed P d t \<and>
      (\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        schema_call_formed P e (evaluate_pattern f p) \<and> (e,evaluate_pattern f p)\<in>X))"
proof
  assume member: "(d,t)\<in>schema_consequences P X"
  show "\<exists>c S f. ((d,c),S)\<in>system_clauses P \<and>
    (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and>
    t=evaluate_pattern f (schema_conclusion S) \<and> schema_call_formed P d t \<and>
    (\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      schema_call_formed P e (evaluate_pattern f p) \<and> (e,evaluate_pattern f p)\<in>X)"
    using schema_consequences_valuationD[OF member] by blast
next
  assume witness: "\<exists>c S f. ((d,c),S)\<in>system_clauses P \<and>
    (\<forall>a\<in>schema_variables S. term_formed (f a)) \<and>
    t=evaluate_pattern f (schema_conclusion S) \<and> schema_call_formed P d t \<and>
    (\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      schema_call_formed P e (evaluate_pattern f p) \<and> (e,evaluate_pattern f p)\<in>X)"
  obtain c S f where clause: "((d,c),S)\<in>system_clauses P"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and head: "t=evaluate_pattern f (schema_conclusion S)" and call: "schema_call_formed P d t"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      schema_call_formed P e (evaluate_pattern f p) \<and> (e,evaluate_pattern f p)\<in>X"
    using witness by blast
  have sf: "schema_formed S" using formed clause by (auto simp: schema_system_formed_def)
  let ?V = "(\<lambda>a. (a,f a)) ` schema_variables S"
  let ?Q = "evaluate_schema_premises f S"
  have inst: "schema_instance S ?V t ?Q" using schema_evaluation_instance[OF sf assignment] head by simp
  have material: "schema_material_satisfied S ?V"
    using ordinary clause by (auto simp: system_observation_free_def schema_material_satisfied_def)
  have admitted: "admitted_schema_instance P d c ?V t ?Q"
    using clause call inst material support by (auto simp: admitted_schema_instance_def)
  have supported: "\<forall>s e x. (s,e,x)\<in>?Q \<longrightarrow> (e,x)\<in>X"
    using support by auto
  have entry: "\<exists>c V Q. admitted_schema_instance P d c V t Q \<and>
    (\<forall>s e x. (s,e,x)\<in>Q \<longrightarrow> (e,x)\<in>X)"
    by (rule exI[of _ c], rule exI[of _ ?V], rule exI[of _ ?Q])
       (use admitted supported in blast)
  show "(d,t)\<in>schema_consequences P X" using entry by (simp add: schema_consequences_def)
qed

corollary positive_valuation_step:
  assumes formed: "schema_system_formed P" and ordinary: "system_observation_free P"
    and clause: "((d,c),S)\<in>system_clauses P"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and call: "schema_call_formed P d (evaluate_pattern f (schema_conclusion S))"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      schema_call_formed P e (evaluate_pattern f p) \<and>
      (e,evaluate_pattern f p)\<in>positive_meaning P"
  shows "(d,evaluate_pattern f (schema_conclusion S))\<in>positive_meaning P"
  by (subst positive_meaning_unfold, subst schema_consequences_valuation[OF formed ordinary])
     (use clause assignment call support in blast)

text \<open>
  Evaluation only calculates the previously defined instances. Each function
  used in these proofs is restricted to the schema's complete finite binder
  boundary when forming an instance. It supplies no semantic callback and adds
  no operation to the language. Premise sockets remain separate occurrences,
  including when their evaluated calls agree.

  The forward projection and induction also apply to programs with material
  premises. They start from actual consequences of the unchanged operator.
  The introduction rule applies to an ordinary clause inside such a program;
  it cannot bypass a material premise in the selected clause.
\<close>

end
