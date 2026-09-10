theory Factor_List_Profiles
  imports Factor_Bag_Comparison
begin

section \<open>Complete lists call one fixed element definition\<close>

definition list_profile_clauses :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> (nat,nat,nat) factor_schema) set" where
  "list_profile_clauses element list={(0,data_list_nil_schema),(1,list_step_schema element list)}"

locale list_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and element_site list_site :: nat
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

theorem sound:
  assumes holds: "(list_site,t)\<in>positive_meaning P"
  shows "\<exists>xs. t=data_list_term xs \<and> (\<forall>x\<in>set xs. (element_site,x)\<in>positive_meaning P)"
proof -
  let ?Q="\<lambda>t. \<exists>xs. t=data_list_term xs \<and> (\<forall>x\<in>set xs. (element_site,x)\<in>positive_meaning P)"
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
      then have cases: "S=data_list_nil_schema \<or> S=list_step_schema element_site list_site"
        using clause by (auto simp: family list_profile_clauses_def)
      then show "?Q (evaluate_pattern f (schema_conclusion S))"
      proof
        assume "S=data_list_nil_schema"
        then show ?thesis by (intro exI[of _ "[]"]) (simp add: data_list_nil_schema_def)
      next
        assume schema: "S=list_step_schema element_site list_site"
        have first: "(element_site,f 0)\<in>positive_meaning P"
          using support schema by (auto simp: list_step_schema_def)
        obtain xs where tail: "f 1=data_list_term xs" "\<forall>x\<in>set xs. (element_site,x)\<in>positive_meaning P"
          using support[rule_format, of 1 list_site data_y] schema by (auto simp: list_step_schema_def)
        show ?thesis by (intro exI[of _ "f 0#xs"])
          (use first tail in \<open>simp add: schema list_step_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem complete:
  assumes "\<forall>x\<in>set xs. (element_site,x)\<in>positive_meaning P"
  shows "(list_site,data_list_term xs)\<in>positive_meaning P"
  using assms
proof (induction xs)
  case Nil
  have result: "(list_site,evaluate_pattern (\<lambda>_. Payload_Term []) (schema_conclusion data_list_nil_schema))
    \<in>positive_meaning P"
    by (rule rule[where c=0])
      (auto simp: list_profile_clauses_def data_list_nil_schema_def schema_variables_def)
  show ?case using result by (simp add: data_list_nil_schema_def)
next
  case (Cons x xs)
  have first: "(element_site,x)\<in>positive_meaning P" and tail: "(list_site,data_list_term xs)\<in>positive_meaning P"
    using Cons by auto
  have formed: "term_formed x" "term_formed (data_list_term xs)"
    using element_formed[OF first] schema_call_formed_target[OF positive_meaning_formed[OF tail]] by auto
  let ?f="\<lambda>i::nat. if i=0 then x else data_list_term xs"
  have result: "(list_site,evaluate_pattern ?f (schema_conclusion (list_step_schema element_site list_site)))
    \<in>positive_meaning P"
    by (rule rule[where c=1])
      (use formed first tail in \<open>auto simp: list_profile_clauses_def list_step_schema_def schema_variables_def\<close>)
  show ?case using result by (simp add: list_step_schema_def)
qed

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
