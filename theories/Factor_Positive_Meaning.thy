theory Factor_Positive_Meaning
  imports Factor_Interfaces
begin

section \<open>Independently fixed positive meaning\<close>

definition schema_consequences ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('d \<times> factor_term) set \<Rightarrow> ('d \<times> factor_term) set" where
  "schema_consequences P X = {(d,t). \<exists>c V Q.
    admitted_schema_instance P d c V t Q \<and>
    (\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> (e,x) \<in> X)}"

lemma schema_consequences_mono:
  "mono (schema_consequences P)"
  by (auto simp: mono_def schema_consequences_def; blast)

definition positive_meaning :: "('a,'s,'d,'c) schema_system \<Rightarrow> ('d \<times> factor_term) set" where
  "positive_meaning P = lfp (schema_consequences P)"

theorem positive_meaning_unfold:
  "positive_meaning P = schema_consequences P (positive_meaning P)"
  unfolding positive_meaning_def by (rule lfp_unfold[OF schema_consequences_mono])

theorem positive_meaning_least:
  assumes "schema_consequences P X \<subseteq> X"
  shows "positive_meaning P \<subseteq> X"
  unfolding positive_meaning_def
  by (rule lfp_lowerbound[where f="schema_consequences P" and A=X, OF assms])

lemma positive_meaning_formed:
  assumes "(d,t) \<in> positive_meaning P"
  shows "schema_call_formed P d t"
  using assms
  by (subst (asm) positive_meaning_unfold)
     (auto simp: schema_consequences_def admitted_schema_instance_def)

lemma positive_meaning_step:
  assumes "admitted_schema_instance P d c V t Q"
    "\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> (e,x) \<in> positive_meaning P"
  shows "(d,t) \<in> positive_meaning P"
  by (subst positive_meaning_unfold) (use assms in \<open>auto simp: schema_consequences_def\<close>)

lemma positive_meaning_has_formed_system:
  assumes "(d,t) \<in> positive_meaning P"
  shows "schema_system_formed P"
  using positive_meaning_formed[OF assms] by (simp add: schema_call_formed_def)

theorem unsupported_positive_cycle_is_empty:
  assumes unseeded: "\<And>d c V t Q. admitted_schema_instance P d c V t Q \<Longrightarrow> Q \<noteq> {}"
  shows "positive_meaning P = {}"
proof -
  have empty: "schema_consequences P {} \<subseteq> {}"
  proof
    fix call assume member: "call \<in> schema_consequences P {}"
    obtain d t where shape: "call = (d,t)" by (cases call) auto
    obtain c V Q where inst: "admitted_schema_instance P d c V t Q"
      and support: "\<forall>s e x. (s,e,x) \<in> Q \<longrightarrow> (e,x) \<in> {}"
      using member shape by (auto simp: schema_consequences_def)
    have "Q = {}" using support by force
    then show "call \<in> {}" using unseeded[OF inst] by blast
  qed
  show ?thesis using positive_meaning_least[OF empty] by blast
qed

section \<open>One finite definition over unbounded future terms\<close>

definition equality_schema :: "(unit,unit,unit) factor_schema" where
  "equality_schema = \<lparr>schema_conclusion = Pattern_Pair (Pattern_Variable ()) (Pattern_Variable ()),
    schema_premises = {}, schema_material_premises = {}\<rparr>"

definition equality_system :: "(unit,unit,unit,unit) schema_system" where
  "equality_system = \<lparr>system_interfaces = {((),Pattern_Variable ())},
    system_clauses = {(((),()),equality_schema)}\<rparr>"

lemma equality_system_formed [simp]:
  "schema_system_formed equality_system"
  by (auto simp: schema_system_formed_def equality_system_def equality_schema_def
      schema_formed_def schema_dependencies_def system_definitions_def rel_dom_def rel_ran_def single_valued_def)

lemma equality_schema_instance:
  assumes "term_formed t"
  shows "schema_instance equality_schema {((),t)} (Pair_Term t t) {}"
  using assms
  by (auto simp: schema_instance_def equality_schema_def schema_formed_def schema_variables_def
      schema_premise_instance_def term_bindings_formed_def single_valued_def rel_dom_def)

theorem generic_equality_holds:
  assumes "term_formed t"
  shows "((),Pair_Term t t) \<in> positive_meaning equality_system"
proof -
  have formed: "schema_call_formed equality_system () (Pair_Term t t)"
    using assms equality_system_formed by (simp add: schema_call_formed_def equality_system_def)
  have inst: "admitted_schema_instance equality_system () () {((),t)} (Pair_Term t t) {}"
    using formed equality_schema_instance[OF assms]
    by (auto simp: admitted_schema_instance_def equality_system_def
        schema_material_satisfied_def equality_schema_def)
  show ?thesis by (rule positive_meaning_step[OF inst]) simp
qed

lemma equality_instance_is_diagonal:
  assumes "schema_instance equality_schema V t Q"
  shows "\<exists>x. term_formed x \<and> t = Pair_Term x x \<and> Q = {}"
proof -
  have head: "pattern_instance V (Pattern_Pair (Pattern_Variable ()) (Pattern_Variable ())) t"
    and bindings: "term_bindings_formed (schema_variables equality_schema) V"
    and domain: "rel_dom Q = {}"
    using assms by (auto simp: schema_instance_def equality_schema_def schema_premise_instance_def rel_dom_def)
  obtain x y where terms: "t = Pair_Term x y" "((),x) \<in> V" "((),y) \<in> V"
    using head by auto
  have same: "x = y" and formed: "term_formed x"
    using bindings terms(2,3) by (auto simp: term_bindings_formed_def single_valued_def)
  have empty: "Q = {}" using domain by simp
  show ?thesis using terms same formed empty by blast
qed

theorem generic_equality_only:
  assumes "((),t) \<in> positive_meaning equality_system"
  shows "\<exists>x. term_formed x \<and> t = Pair_Term x x"
proof -
  obtain c V Q where inst: "admitted_schema_instance equality_system () c V t Q"
    using assms by (subst (asm) positive_meaning_unfold) (auto simp: schema_consequences_def)
  have schema: "schema_instance equality_schema V t Q"
    using inst by (auto simp: admitted_schema_instance_def equality_system_def)
  show ?thesis using equality_instance_is_diagonal[OF schema] by blast
qed

theorem generic_equality_exact:
  "((),t) \<in> positive_meaning equality_system \<longleftrightarrow> (\<exists>x. term_formed x \<and> t = Pair_Term x x)"
  using generic_equality_only generic_equality_holds by blast

text \<open>
  This positive schema class permits recursion only through one monotone
  operator. Its least fixed point is defined before any retained proof format.
  A cycle without a premise-free instance contributes no judgments.

  Interfaces determine application formation independently of truth. Definition,
  clause, and premise occurrences have separate identities in the mathematical
  projection. Native recovery must supply those occurrences and their explicit
  dependency locations; this theory provides no ambient name resolver.
\<close>

end
