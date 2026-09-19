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

section \<open>Every element of a list, in a context, is one notion\<close>

text \<open>
  Checking every element of a list in a supplied context is one notion, whatever program presents
  it: the relation at the list's site satisfies the recursion below, and on every data list that is
  exactly the check of every element in the context. A program presents the notion by establishing the
  recursion for its own clauses, and the list semantics is then this argument, stated once.
\<close>

locale context_list_rule_relation =
  fixes M :: "('d\<times>factor_term) set" and element list :: 'd
  assumes equation: "\<And>t. (list,t)\<in>M \<longleftrightarrow> (\<exists>a. t=Pair_Term a (Payload_Term []) \<and> term_formed a) \<or>
    (\<exists>a x y. t=Pair_Term a (Pair_Term x y) \<and> (element,Pair_Term a x)\<in>M \<and> (list,Pair_Term a y)\<in>M)"
begin

lemma sound_at:
  assumes "(list,Pair_Term a r)\<in>M"
  shows "\<exists>xs. r=data_list_term xs \<and> term_formed a \<and> (\<forall>x\<in>set xs. (element,Pair_Term a x)\<in>M)"
  using assms
proof (induction r)
  case (Target_Term target)
  then show ?case by (simp only: equation[of "Pair_Term a (Target_Term target)"]) simp
next
  case (Payload_Term bytes)
  have "bytes=[] \<and> term_formed a"
    using Payload_Term.prems by (simp only: equation[of "Pair_Term a (Payload_Term bytes)"]) simp
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (Pair_Term x y)
  have parts: "(element,Pair_Term a x)\<in>M" "(list,Pair_Term a y)\<in>M"
    using Pair_Term.prems by (simp_all only: equation[of "Pair_Term a (Pair_Term x y)"]) simp_all
  obtain xs where tail: "y=data_list_term xs" "term_formed a" "\<forall>z\<in>set xs. (element,Pair_Term a z)\<in>M"
    using Pair_Term.IH(2)[OF parts(2)] by blast
  show ?case by (intro exI[of _ "x#xs"]) (use parts tail in simp)
qed

theorem sound:
  assumes holds: "(list,t)\<in>M"
  shows "\<exists>a xs. t=Pair_Term a (data_list_term xs) \<and> term_formed a \<and>
    (\<forall>x\<in>set xs. (element,Pair_Term a x)\<in>M)"
proof -
  obtain a r where t: "t=Pair_Term a r"
    using holds by (simp only: equation[of t]) blast
  show ?thesis using sound_at[OF holds[unfolded t]] t by blast
qed

theorem complete:
  assumes "term_formed a" "\<forall>x\<in>set xs. (element,Pair_Term a x)\<in>M"
  shows "(list,Pair_Term a (data_list_term xs))\<in>M"
  using assms(2)
proof (induction xs)
  case Nil
  show ?case using assms(1) by (subst equation) simp
next
  case (Cons x xs)
  have head: "(element,Pair_Term a x)\<in>M" and tail: "(list,Pair_Term a (data_list_term xs))\<in>M"
    using Cons by simp_all
  have "\<exists>a' x' y. Pair_Term a (data_list_term (x#xs))=Pair_Term a' (Pair_Term x' y) \<and>
      (element,Pair_Term a' x')\<in>M \<and> (list,Pair_Term a' y)\<in>M"
    using head tail by (intro exI[of _ a] exI[of _ x] exI[of _ "data_list_term xs"]) simp
  then show ?case by (subst equation) blast
qed

theorem exact:
  "(list,t)\<in>M \<longleftrightarrow> (\<exists>a xs. t=Pair_Term a (data_list_term xs) \<and> term_formed a \<and>
    (\<forall>x\<in>set xs. (element,Pair_Term a x)\<in>M))"
  using sound complete by blast

corollary lists:
  "(list,Pair_Term a (data_list_term xs))\<in>M \<longleftrightarrow>
    term_formed a \<and> (\<forall>x\<in>set xs. (element,Pair_Term a x)\<in>M)"
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

lemma relation_equation:
  "(list_site,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>a. t=Pair_Term a (Payload_Term []) \<and> term_formed a) \<or>
    (\<exists>a x y. t=Pair_Term a (Pair_Term x y) \<and> (element_site,Pair_Term a x)\<in>positive_meaning P \<and>
      (list_site,Pair_Term a y)\<in>positive_meaning P)"
proof
  assume holds: "(list_site,t)\<in>positive_meaning P"
  obtain c S where member: "(c,S)\<in>system_clause_family P list_site"
    and rule_instance: "schema_rule_instance S (positive_meaning P) t"
    using holds positive_variable_rule_family[OF call] by blast
  have clause: "((list_site,c),S)\<in>system_clauses P" using member by (simp add: system_clause_member)
  have sf: "schema_formed S" using clause system_formed by (auto simp: schema_system_formed_def)
  have cases: "S=context_list_nil_schema \<or> S=context_list_step_schema element_site list_site"
    using clause by (auto simp: family context_list_clauses_def)
  have ordinary: "schema_material_premises S={}"
    using cases by (auto simp: context_list_nil_schema_def context_list_step_schema_def)
  obtain f where assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and shape: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern f p)\<in>positive_meaning P"
    using rule_instance ordinary_schema_rule_valuation[OF sf ordinary] by blast
  show "(\<exists>a. t=Pair_Term a (Payload_Term []) \<and> term_formed a) \<or>
    (\<exists>a x y. t=Pair_Term a (Pair_Term x y) \<and> (element_site,Pair_Term a x)\<in>positive_meaning P \<and>
      (list_site,Pair_Term a y)\<in>positive_meaning P)"
    using cases
  proof
    assume schema: "S=context_list_nil_schema"
    have "term_formed (f 0)"
      using assignment by (simp add: schema context_list_nil_schema_def schema_variables_def)
    then show ?thesis using shape by (simp add: schema context_list_nil_schema_def)
  next
    assume schema: "S=context_list_step_schema element_site list_site"
    have first: "(element_site,Pair_Term (f 0) (f 1))\<in>positive_meaning P"
      using support schema by (auto simp: context_list_step_schema_def)
    have tail: "(list_site,Pair_Term (f 0) (f 2))\<in>positive_meaning P"
      using support[rule_format, of 1 list_site "Pattern_Pair data_x data_z"] schema
      by (auto simp: context_list_step_schema_def)
    show ?thesis using shape first tail by (simp add: schema context_list_step_schema_def)
  qed
next
  assume "(\<exists>a. t=Pair_Term a (Payload_Term []) \<and> term_formed a) \<or>
    (\<exists>a x y. t=Pair_Term a (Pair_Term x y) \<and> (element_site,Pair_Term a x)\<in>positive_meaning P \<and>
      (list_site,Pair_Term a y)\<in>positive_meaning P)"
  then show "(list_site,t)\<in>positive_meaning P"
  proof
    assume "\<exists>a. t=Pair_Term a (Payload_Term []) \<and> term_formed a"
    then obtain a where t: "t=Pair_Term a (Payload_Term [])" and af: "term_formed a" by blast
    have "(list_site,evaluate_pattern (\<lambda>_. a) (schema_conclusion context_list_nil_schema))\<in>positive_meaning P"
      by (rule rule[where c=0])
        (use af in \<open>auto simp: context_list_clauses_def context_list_nil_schema_def schema_variables_def\<close>)
    then show ?thesis using t by (simp add: context_list_nil_schema_def)
  next
    assume "\<exists>a x y. t=Pair_Term a (Pair_Term x y) \<and> (element_site,Pair_Term a x)\<in>positive_meaning P \<and>
      (list_site,Pair_Term a y)\<in>positive_meaning P"
    then obtain a x y where t: "t=Pair_Term a (Pair_Term x y)"
      and first: "(element_site,Pair_Term a x)\<in>positive_meaning P"
      and tail: "(list_site,Pair_Term a y)\<in>positive_meaning P" by blast
    have formed: "term_formed a" "term_formed x" "term_formed y"
      using element_formed[OF first] schema_call_formed_target[OF positive_meaning_formed[OF tail]] by auto
    let ?f="\<lambda>i::nat. if i=0 then a else if i=1 then x else y"
    have "(list_site,evaluate_pattern ?f (schema_conclusion (context_list_step_schema element_site list_site)))
        \<in>positive_meaning P"
      by (rule rule[where c=1])
        (use formed first tail in \<open>auto simp: context_list_clauses_def context_list_step_schema_def schema_variables_def\<close>)
    then show ?thesis using t by (simp add: context_list_step_schema_def)
  qed
qed

sublocale semantics: context_list_rule_relation "positive_meaning P" element_site list_site
  by unfold_locales (rule relation_equation)

lemmas sound = semantics.sound
lemmas complete = semantics.complete
lemmas exact = semantics.exact
lemmas lists = semantics.lists

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
