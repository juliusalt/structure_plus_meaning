theory Factor_Separated_Lists
  imports Factor_Presentation_Transport
begin

section \<open>Every element is compared with every later element\<close>

definition separated_list_step_schema ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "separated_list_step_schema element all list=data_rule (Pattern_Pair data_x data_y)
    {(0,element,data_x),(1,all,Pattern_Pair data_x data_y),(2,list,data_y)}"

definition separated_list_clauses ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat\<times>(nat,nat,nat) factor_schema) set" where
  "separated_list_clauses element all list=
    {(0,data_list_nil_schema),(1,separated_list_step_schema element all list)}"

locale separated_list_profile =
  context_list_profile P separate_site all_site
  for P :: "(nat,nat,nat,nat) schema_system" and separate_site all_site :: nat +
  fixes element_site list_site :: nat
  assumes collection_family: "\<And>c S. ((list_site,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>separated_list_clauses element_site all_site list_site"
    and collection_call: "\<And>t. schema_call_formed P list_site t \<longleftrightarrow> term_formed t"
begin

abbreviation apart where
  "apart x y \<equiv> (separate_site,Pair_Term x y)\<in>positive_meaning P"

lemma admitted_formed:
  assumes "(element_site,t)\<in>positive_meaning P"
  shows "term_formed t"
  using schema_call_formed_target[OF positive_meaning_formed[OF assms]] by blast

lemma collection_rule:
  assumes clause: "(c,S)\<in>separated_list_clauses element_site all_site list_site"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning P"
  shows "(list_site,evaluate_pattern f (schema_conclusion S))\<in>positive_meaning P"
proof -
  have member: "((list_site,c),S)\<in>system_clauses P" using clause by (simp add: collection_family)
  have sf: "schema_formed S" using member system_formed by (auto simp: schema_system_formed_def)
  have ordinary: "schema_material_premises S={}"
    using clause by (auto simp: separated_list_clauses_def data_list_nil_schema_def separated_list_step_schema_def)
  have formed: "term_formed (evaluate_pattern f (schema_conclusion S))"
    by (rule evaluate_pattern_formed)
      (use sf assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have head: "schema_call_formed P list_site (evaluate_pattern f (schema_conclusion S))"
    using formed by (simp add: collection_call)
  show ?thesis by (rule ordinary_positive_valuation_step[OF member ordinary assignment head support])
qed

theorem collection_sound:
  assumes holds: "(list_site,t)\<in>positive_meaning P"
  shows "\<exists>xs. t=data_list_term xs \<and>
    (\<forall>x\<in>set xs. (element_site,x)\<in>positive_meaning P) \<and> sorted_wrt apart xs"
proof -
  let ?Q="\<lambda>t. \<exists>xs. t=data_list_term xs \<and>
    (\<forall>x\<in>set xs. (element_site,x)\<in>positive_meaning P) \<and> sorted_wrt apart xs"
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
      then have cases: "S=data_list_nil_schema \<or> S=separated_list_step_schema element_site all_site list_site"
        using clause by (auto simp: collection_family separated_list_clauses_def)
      then show "?Q (evaluate_pattern f (schema_conclusion S))"
      proof
        assume "S=data_list_nil_schema"
        then show ?thesis by (intro exI[of _ "[]"]) (simp add: data_list_nil_schema_def)
      next
        assume schema: "S=separated_list_step_schema element_site all_site list_site"
        have first: "(element_site,f 0)\<in>positive_meaning P"
          and separated: "(all_site,Pair_Term (f 0) (f 1))\<in>positive_meaning P"
          using support schema by (auto simp: separated_list_step_schema_def)
        obtain xs where tail: "f 1=data_list_term xs"
          "\<forall>x\<in>set xs. (element_site,x)\<in>positive_meaning P" "sorted_wrt apart xs"
          using support[rule_format, of 2 list_site data_y] schema
          by (auto simp: separated_list_step_schema_def)
        have different: "\<forall>x\<in>set xs. apart (f 0) x"
        proof -
          have checked: "(all_site,Pair_Term (f 0) (data_list_term xs))\<in>positive_meaning P"
            using separated by (simp only: tail(1))
          show ?thesis using checked lists[of "f 0" xs] by blast
        qed
        show ?thesis by (intro exI[of _ "f 0#xs"])
          (use first tail different in \<open>simp add: schema separated_list_step_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem collection_complete:
  assumes "\<forall>x\<in>set xs. (element_site,x)\<in>positive_meaning P" "sorted_wrt apart xs"
  shows "(list_site,data_list_term xs)\<in>positive_meaning P"
  using assms
proof (induction xs)
  case Nil
  have result: "(list_site,evaluate_pattern (\<lambda>_. Payload_Term []) (schema_conclusion data_list_nil_schema))
      \<in>positive_meaning P"
    by (rule collection_rule[where c=0])
      (auto simp: separated_list_clauses_def data_list_nil_schema_def schema_variables_def)
  show ?case using result by (simp add: data_list_nil_schema_def)
next
  case (Cons x xs)
  have first: "(element_site,x)\<in>positive_meaning P"
    and tail: "(list_site,data_list_term xs)\<in>positive_meaning P"
    using Cons by auto
  have formed: "term_formed x" "term_formed (data_list_term xs)"
    using admitted_formed[OF first] schema_call_formed_target[OF positive_meaning_formed[OF tail]] by auto
  have separated: "(all_site,Pair_Term x (data_list_term xs))\<in>positive_meaning P"
    using Cons.prems(2) formed(1) by (simp add: lists)
  let ?f="\<lambda>i::nat. if i=0 then x else data_list_term xs"
  have result: "(list_site,evaluate_pattern ?f
      (schema_conclusion (separated_list_step_schema element_site all_site list_site)))\<in>positive_meaning P"
    by (rule collection_rule[where c=1])
      (use formed first tail separated in \<open>auto simp: separated_list_clauses_def
        separated_list_step_schema_def schema_variables_def\<close>)
  show ?case using result by (simp add: separated_list_step_schema_def)
qed

theorem collection_exact:
  "(list_site,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>xs. t=data_list_term xs \<and>
      (\<forall>x\<in>set xs. (element_site,x)\<in>positive_meaning P) \<and> sorted_wrt apart xs)"
  using collection_sound collection_complete by blast

corollary collection_lists:
  "(list_site,data_list_term xs)\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>x\<in>set xs. (element_site,x)\<in>positive_meaning P) \<and> sorted_wrt apart xs"
  by (auto simp: collection_exact data_list_term_injective)

section \<open>Subject inequality supplies the exact finite-collection constraint\<close>

lemma presented_separation:
  assumes reading: "list_all2 read xs ps"
    and compare: "\<And>a b p q. read a p \<Longrightarrow> read b q \<Longrightarrow> apart p q \<longleftrightarrow> a\<noteq>b"
  shows "sorted_wrt apart ps \<longleftrightarrow> distinct xs"
  using reading
proof (induction xs arbitrary: ps)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  obtain p qs where parts: "ps=p#qs" "read a p" "list_all2 read xs qs"
    using Cons.prems by (auto simp: list_all2_Cons1)
  have members: "(\<forall>a\<in>set xs. \<exists>p\<in>set qs. read a p) \<and>
    (\<forall>p\<in>set qs. \<exists>a\<in>set xs. read a p)"
    by (rule list_all2_members[OF parts(3)])
  have head: "(\<forall>q\<in>set qs. apart p q) \<longleftrightarrow> a\<notin>set xs"
    using members compare[OF parts(2)] by blast
  show ?case using Cons.IH[OF parts(3)] head by (simp add: parts(1))
qed

theorem collection_presentation_class:
  assumes compare: "presented_relation_contract
    read D (\<lambda>t. (element_site,t)\<in>positive_meaning P)
    read D (\<lambda>t. (element_site,t)\<in>positive_meaning P) (\<noteq>) apart"
  shows "presentation_class (data_collection_presents read)
    (\<lambda>A. finite A \<and> (\<forall>a\<in>A. D a)) (\<lambda>t. (list_site,t)\<in>positive_meaning P)"
proof -
  interpret comparison: presented_relation_contract
    read D "\<lambda>t. (element_site,t)\<in>positive_meaning P"
    read D "\<lambda>t. (element_site,t)\<in>positive_meaning P" "(\<noteq>)" apart
    by (rule compare)
  have element: "presentation_class read D (\<lambda>t. (element_site,t)\<in>positive_meaning P)"
    by (rule comparison.left.presentation_class_axioms)
  have source: "presentation_class (data_collection_presents read)
    (\<lambda>A. finite A \<and> (\<forall>a\<in>A. D a)) (presented_predicate (data_sequence_presents read) distinct)"
    by (rule data_collection_presentation_class[OF element])
  have admission: "presented_predicate (data_sequence_presents read) distinct t \<longleftrightarrow>
    (list_site,t)\<in>positive_meaning P" for t
  proof
    assume "presented_predicate (data_sequence_presents read) distinct t"
    then obtain xs ps where parts: "list_all2 read xs ps" "distinct xs" "t=data_list_term ps"
      by (auto simp: presented_predicate_def data_sequence_presents_def)
    have formed: "\<forall>p\<in>set ps. (element_site,p)\<in>positive_meaning P"
      using presentation_class.list_boundaries[OF element parts(1)] by blast
    have separated: "sorted_wrt apart ps" using presented_separation[OF parts(1) comparison.at] parts(2) by blast
    show "(list_site,t)\<in>positive_meaning P"
      using collection_complete[OF formed separated] parts(3) by simp
  next
    assume "(list_site,t)\<in>positive_meaning P"
    then obtain ps where parts: "t=data_list_term ps"
      "\<forall>p\<in>set ps. (element_site,p)\<in>positive_meaning P" "sorted_wrt apart ps"
      using collection_sound by blast
    obtain xs where reading: "list_all2 read xs ps" using presentation_class.list_admitted[OF element parts(2)] by blast
    have distinct: "distinct xs" using presented_separation[OF reading comparison.at] parts(3) by blast
    show "presented_predicate (data_sequence_presents read) distinct t"
      using parts(1) reading distinct by (auto simp: presented_predicate_def data_sequence_presents_def)
  qed
  have same_admission: "presented_predicate (data_sequence_presents read) distinct =
      (\<lambda>t. (list_site,t)\<in>positive_meaning P)"
    by (rule ext) (rule admission)
  show ?thesis using source by (simp only: same_admission)
qed

end

text \<open>
  The existing context-list clauses check one explicit comparison call against
  every later member. Two further ordinary clauses admit each element and the
  complete tail. Their meaning retains every occurrence and the final list
  boundary, even when the element and comparison definitions participate in
  the same positive recursion.

  The finite-collection class follows from the existing sequence, constraint,
  and covered-image constructions. It consumes the inequality contract
  exported by the element notion. Admission and subject comparison are
  therefore established at that boundary, and the generic collection proof
  derives its own meaning from the contract. Different presentations of one
  subject cannot pass as distinct members.
  No order of a finite set is selected by these clauses.
\<close>

end
