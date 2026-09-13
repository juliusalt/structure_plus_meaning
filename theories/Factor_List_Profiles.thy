theory Factor_List_Profiles
  imports Factor_Bag_Comparison Factor_Admission_Pair_Schemas
begin

section \<open>Complete lists call one fixed element definition\<close>

definition list_profile_clauses :: "'d \<Rightarrow> 'd \<Rightarrow> (nat \<times> (nat,nat,'d) factor_schema) set" where
  "list_profile_clauses element list={(0,data_list_nil_schema),(1,list_step_schema element list)}"

lemma data_list_nil_rule_instance:
  "schema_rule_instance data_list_nil_schema M t \<longleftrightarrow> t=Payload_Term []"
  by (subst ordinary_schema_rule_valuation)
    (auto simp: data_list_nil_schema_def schema_formed_def schema_variables_def
      single_valued_def octets_formed_def)

locale list_rule_relation =
  fixes M :: "('d\<times>factor_term) set" and element list :: 'd
  assumes equation: "\<And>t. (list,t)\<in>M \<longleftrightarrow> t=Payload_Term [] \<or>
    (\<exists>x y. t=Pair_Term x y \<and> (element,x)\<in>M \<and> (list,y)\<in>M)"
begin

theorem sound:
  assumes "(list,t)\<in>M"
  shows "\<exists>xs. t=data_list_term xs \<and> (\<forall>x\<in>set xs. (element,x)\<in>M)"
  using assms
proof (induction t)
  case (Target_Term target)
  then show ?case by (simp only: equation[of "Target_Term target"]) simp
next
  case (Payload_Term bytes)
  have "bytes=[]" using Payload_Term.prems by (simp only: equation[of "Payload_Term bytes"]) simp
  then show ?case by (rule_tac x="[]" in exI) simp
next
  case (Pair_Term x y)
  have parts: "(element,x)\<in>M \<and> (list,y)\<in>M"
    using Pair_Term.prems by (simp only: equation[of "Pair_Term x y"]) simp
  have first: "(element,x)\<in>M" and tail: "(list,y)\<in>M" using parts by blast+
  obtain xs where fields: "y=data_list_term xs" "\<forall>z\<in>set xs. (element,z)\<in>M"
    using Pair_Term.IH(2)[OF tail] by blast
  show ?case by (rule exI[of _ "x#xs"]) (use first fields in simp)
qed

theorem complete:
  assumes "\<forall>x\<in>set xs. (element,x)\<in>M"
  shows "(list,data_list_term xs)\<in>M"
  using assms
proof (induction xs)
  case Nil
  show ?case by (subst equation) simp
next
  case (Cons x xs)
  show ?case by (subst equation) (use Cons in auto)
qed

theorem exact:
  "(list,t)\<in>M \<longleftrightarrow> (\<exists>xs. t=data_list_term xs \<and> (\<forall>x\<in>set xs. (element,x)\<in>M))"
  using sound complete by blast

end

theorem list_profile_rule_family:
  assumes call: "\<And>t. schema_call_formed P d t \<longleftrightarrow> term_formed t"
    and family: "\<And>t. (\<exists>c S. (c,S)\<in>system_clause_family P d \<and> schema_rule_instance S (positive_meaning P) t)
      \<longleftrightarrow> (\<exists>c S. (c,S)\<in>list_profile_clauses a d \<and> schema_rule_instance S (positive_meaning P) t)"
  shows "list_rule_relation (positive_meaning P) a d"
proof
  fix t
  have step: "list_step_schema a d=admitted_pair_schema a d"
    by (simp only: list_step_schema_def admitted_pair_schema_def)
  have rules: "(\<exists>c S. (c,S)\<in>list_profile_clauses a d \<and> schema_rule_instance S (positive_meaning P) t) \<longleftrightarrow>
      schema_rule_instance data_list_nil_schema (positive_meaning P) t \<or>
      schema_rule_instance (admitted_pair_schema a d) (positive_meaning P) t"
    by (simp only: list_profile_clauses_def schema_two_clause_rules step)
  show "(d,t)\<in>positive_meaning P \<longleftrightarrow> t=Payload_Term [] \<or>
      (\<exists>x y. t=Pair_Term x y \<and> (a,x)\<in>positive_meaning P \<and> (d,y)\<in>positive_meaning P)"
    by (subst positive_variable_rule_family[OF call], subst family)
      (simp only: rules data_list_nil_rule_instance admitted_pair_positive_rule)

qed

locale list_profile =
  fixes P :: "(nat,nat,'d,nat) schema_system" and element_site list_site :: 'd
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((list_site,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>list_profile_clauses element_site list_site"
    and call: "\<And>t. schema_call_formed P list_site t \<longleftrightarrow> term_formed t"
begin

lemma element_formed:
  assumes "(element_site,t)\<in>positive_meaning P"
  shows "term_formed t"
  using schema_call_formed_target[OF positive_meaning_formed[OF assms]] by blast

lemma rule:
  assumes clause: "(c,S)\<in>list_profile_clauses element_site list_site"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning P"
  shows "(list_site,evaluate_pattern f (schema_conclusion S))\<in>positive_meaning P"
proof -
  have member: "((list_site,c),S)\<in>system_clauses P" using clause by (simp add: family)
  have sf: "schema_formed S" using member system_formed by (auto simp: schema_system_formed_def)
  have ordinary: "schema_material_premises S={}"
    using clause by (auto simp: list_profile_clauses_def data_list_nil_schema_def list_step_schema_def)
  have tf: "term_formed (evaluate_pattern f (schema_conclusion S))"
    by (rule evaluate_pattern_formed)
      (use sf assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have head: "schema_call_formed P list_site (evaluate_pattern f (schema_conclusion S))"
    using tf by (simp add: call)
  show ?thesis by (rule ordinary_positive_valuation_step[OF member ordinary assignment head support])
qed

sublocale semantics: list_rule_relation "positive_meaning P" element_site list_site
  by (rule list_profile_rule_family[OF call]) (auto simp: system_clause_member family)

lemmas sound = semantics.sound
lemmas complete = semantics.complete

theorem exact:
  "(list_site,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>xs. t=data_list_term xs \<and> (\<forall>x\<in>set xs. (element_site,x)\<in>positive_meaning P))"
  using sound complete by blast

corollary lists:
  "(list_site,data_list_term xs)\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>x\<in>set xs. (element_site,x)\<in>positive_meaning P)"
  by (auto simp: exact data_list_term_injective)

end

section \<open>A supplied context accompanies every element call\<close>

definition context_list_nil_schema :: "(nat,nat,nat) factor_schema" where
  "context_list_nil_schema=data_rule (Pattern_Pair data_x (Pattern_Payload [])) {}"

definition context_list_step_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "context_list_step_schema element list=data_rule (Pattern_Pair data_x (Pattern_Pair data_y data_z))
    {(0,element,Pattern_Pair data_x data_y),(1,list,Pattern_Pair data_x data_z)}"

definition context_list_clauses :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> (nat,nat,nat) factor_schema) set" where
  "context_list_clauses element list={(0,context_list_nil_schema),(1,context_list_step_schema element list)}"

locale context_list_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and element_site list_site :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((list_site,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>context_list_clauses element_site list_site"
    and call: "\<And>t. schema_call_formed P list_site t \<longleftrightarrow> term_formed t"
begin

lemma element_formed:
  assumes "(element_site,Pair_Term a t)\<in>positive_meaning P"
  shows "term_formed a \<and> term_formed t"
  using schema_call_formed_target[OF positive_meaning_formed[OF assms]] by auto

lemma rule:
  assumes clause: "(c,S)\<in>context_list_clauses element_site list_site"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning P"
  shows "(list_site,evaluate_pattern f (schema_conclusion S))\<in>positive_meaning P"
proof -
  have member: "((list_site,c),S)\<in>system_clauses P" using clause by (simp add: family)
  have sf: "schema_formed S" using member system_formed by (auto simp: schema_system_formed_def)
  have ordinary: "schema_material_premises S={}"
    using clause by (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def)
  have tf: "term_formed (evaluate_pattern f (schema_conclusion S))"
    by (rule evaluate_pattern_formed)
      (use sf assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have head: "schema_call_formed P list_site (evaluate_pattern f (schema_conclusion S))"
    using tf by (simp add: call)
  show ?thesis by (rule ordinary_positive_valuation_step[OF member ordinary assignment head support])
qed

theorem sound:
  assumes holds: "(list_site,t)\<in>positive_meaning P"
  shows "\<exists>a xs. t=Pair_Term a (data_list_term xs) \<and> term_formed a \<and>
    (\<forall>x\<in>set xs. (element_site,Pair_Term a x)\<in>positive_meaning P)"
proof -
  let ?Q="\<lambda>t. \<exists>a xs. t=Pair_Term a (data_list_term xs) \<and> term_formed a \<and>
    (\<forall>x\<in>set xs. (element_site,Pair_Term a x)\<in>positive_meaning P)"
  have invariant: "list_site=list_site \<longrightarrow> ?Q t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=list_site \<longrightarrow> ?Q t"])
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses P"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
      and head: "schema_call_formed P d (evaluate_pattern f (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning P \<and>
        (e=list_site \<longrightarrow> ?Q (evaluate_pattern f p))"
    show "d=list_site \<longrightarrow> ?Q (evaluate_pattern f (schema_conclusion S))"
    proof
      assume "d=list_site"
      then have cases: "S=context_list_nil_schema \<or> S=context_list_step_schema element_site list_site"
        using clause by (auto simp: family context_list_clauses_def)
      then show "?Q (evaluate_pattern f (schema_conclusion S))"
      proof
        assume schema: "S=context_list_nil_schema"
        have formed: "term_formed (f 0)"
          using assignment by (simp add: schema context_list_nil_schema_def schema_variables_def)
        show ?thesis by (intro exI[of _ "f 0"] exI[of _ "[]"])
          (use formed in \<open>simp add: schema context_list_nil_schema_def\<close>)
      next
        assume schema: "S=context_list_step_schema element_site list_site"
        have first: "(element_site,Pair_Term (f 0) (f 1))\<in>positive_meaning P"
          using support schema by (auto simp: context_list_step_schema_def)
        obtain xs where tail: "f 2=data_list_term xs" "term_formed (f 0)"
          "\<forall>x\<in>set xs. (element_site,Pair_Term (f 0) x)\<in>positive_meaning P"
          using support[rule_format, of 1 list_site "Pattern_Pair data_x data_z"] schema
          by (auto simp: context_list_step_schema_def)
        show ?thesis by (intro exI[of _ "f 0"] exI[of _ "f 1#xs"])
          (use first tail in \<open>simp add: schema context_list_step_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem complete:
  assumes "term_formed a" "\<forall>x\<in>set xs. (element_site,Pair_Term a x)\<in>positive_meaning P"
  shows "(list_site,Pair_Term a (data_list_term xs))\<in>positive_meaning P"
  using assms
proof (induction xs)
  case Nil
  have result: "(list_site,evaluate_pattern (\<lambda>_. a) (schema_conclusion context_list_nil_schema))
    \<in>positive_meaning P"
    by (rule rule[where c=0])
      (use Nil.prems in \<open>auto simp: context_list_clauses_def context_list_nil_schema_def schema_variables_def\<close>)
  show ?case using result by (simp add: context_list_nil_schema_def)
next
  case (Cons x xs)
  have first: "(element_site,Pair_Term a x)\<in>positive_meaning P"
    and tail: "(list_site,Pair_Term a (data_list_term xs))\<in>positive_meaning P" using Cons by auto
  have formed: "term_formed x" "term_formed (data_list_term xs)"
    using element_formed[OF first] schema_call_formed_target[OF positive_meaning_formed[OF tail]] by auto
  let ?f="\<lambda>i::nat. if i=0 then a else if i=1 then x else data_list_term xs"
  have result: "(list_site,evaluate_pattern ?f (schema_conclusion (context_list_step_schema element_site list_site)))
    \<in>positive_meaning P"
    by (rule rule[where c=1])
      (use Cons.prems formed first tail in \<open>auto simp: context_list_clauses_def context_list_step_schema_def schema_variables_def\<close>)
  show ?case using result by (simp add: context_list_step_schema_def)
qed

theorem exact:
  "(list_site,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>a xs. t=Pair_Term a (data_list_term xs) \<and> term_formed a \<and>
      (\<forall>x\<in>set xs. (element_site,Pair_Term a x)\<in>positive_meaning P))"
  using sound complete by blast

corollary lists:
  "(list_site,Pair_Term a (data_list_term xs))\<in>positive_meaning P \<longleftrightarrow>
    term_formed a \<and> (\<forall>x\<in>set xs. (element_site,Pair_Term a x)\<in>positive_meaning P)"
  by (auto simp: exact data_list_term_injective)

end

text \<open>
  The complete clause families traverse every list element and the final
  empty-payload boundary. Each element and tail call has its own premise
  socket. Their meaning is exactly the actual callee's positive meaning
  at every element, including when the callee shares the positive dependency
  cycle. No external predicate is added to the operator.

  The second profile carries one supplied context into every element call.
  Its empty case still checks context formation. Context-free element
  admission uses the first profile and carries no dummy context field.
\<close>

end
