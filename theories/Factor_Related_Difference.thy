theory Factor_Related_Difference
  imports Bag_Difference_Witnesses Factor_Related_Bags Factor_List_Profiles
begin

section \<open>Difference clauses call explicit equality and inequality definitions\<close>

definition related_extra_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "related_extra_schema data list=data_rule (Pattern_Pair (Pattern_Payload []) (Pattern_Pair data_x data_y))
    {(0,data,data_x),(1,list,data_y)}"

definition related_missing_schema :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "related_missing_schema data list all=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,data,data_x),(1,list,data_y),(2,all,Pattern_Pair data_x data_z)}"

definition related_difference_clauses ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (nat\<times>(nat,nat,nat) factor_schema) set" where
  "related_difference_clauses data list all select difference=
    {(0,related_extra_schema data list),(1,related_missing_schema data list all),
      (2,bag_step_schema select difference)}"

locale related_bag_difference =
  related_bags P data_site list_site same_site select_site bag_site
  for P :: "(nat,nat,nat,nat) schema_system" and data_site list_site same_site select_site bag_site :: nat +
  fixes apart_site all_site difference_site :: nat
  assumes apart_data: "\<And>x y. (apart_site,Pair_Term x y)\<in>positive_meaning P \<Longrightarrow>
      term_formed x \<and> self_contained_term x \<and> term_formed y \<and> self_contained_term y"
    and all_family: "\<And>c S. ((all_site,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>context_list_clauses apart_site all_site"
    and all_call: "\<And>t. schema_call_formed P all_site t \<longleftrightarrow> term_formed t"
    and difference_family: "\<And>c S. ((difference_site,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>related_difference_clauses data_site list_site all_site select_site difference_site"
    and difference_call: "\<And>t. schema_call_formed P difference_site t \<longleftrightarrow> term_formed t"
begin

abbreviation apart where "apart x y \<equiv> (apart_site,Pair_Term x y)\<in>positive_meaning P"

sublocale absence: context_list_profile P apart_site all_site
  by (rule context_list_profile.intro[OF system_formed all_family all_call])

lemmas absence_exact = absence.exact
lemmas absence_lists = absence.lists

lemma difference_rule:
  assumes clause: "(c,S)\<in>related_difference_clauses data_site list_site all_site select_site difference_site"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning P"
  shows "(difference_site,evaluate_pattern f (schema_conclusion S))\<in>positive_meaning P"
proof -
  have member: "((difference_site,c),S)\<in>system_clauses P" using clause by (simp add: difference_family)
  have sf: "schema_formed S" using member system_formed unfolding schema_system_formed_def by blast
  have ordinary: "schema_material_premises S={}"
    using clause by (auto simp: related_difference_clauses_def related_extra_schema_def
      related_missing_schema_def bag_step_schema_def)
  have formed: "term_formed (evaluate_pattern f (schema_conclusion S))"
    by (rule evaluate_pattern_formed)
      (use sf assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have head: "schema_call_formed P difference_site (evaluate_pattern f (schema_conclusion S))"
    using formed by (simp add: difference_call)
  show ?thesis by (rule ordinary_positive_valuation_step[OF member ordinary assignment head support])
qed

theorem difference_sound:
  assumes holds: "(difference_site,t)\<in>positive_meaning P"
  shows "\<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
    data_elements xs \<and> data_elements ys \<and> bag_difference_witness related apart xs ys"
proof -
  let ?Q="\<lambda>t. \<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
    data_elements xs \<and> data_elements ys \<and> bag_difference_witness related apart xs ys"
  have invariant: "difference_site=difference_site \<longrightarrow> ?Q t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=difference_site \<longrightarrow> ?Q t"])
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses P"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
      and head: "schema_call_formed P d (evaluate_pattern f (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning P \<and>
        (e=difference_site \<longrightarrow> ?Q (evaluate_pattern f p))"
    show "d=difference_site \<longrightarrow> ?Q (evaluate_pattern f (schema_conclusion S))"
    proof
      assume "d=difference_site"
      then consider (extra) "S=related_extra_schema data_site list_site"
        | (missing) "S=related_missing_schema data_site list_site all_site"
        | (step) "S=bag_step_schema select_site difference_site"
        using clause by (auto simp: difference_family related_difference_clauses_def)
      then show "?Q (evaluate_pattern f (schema_conclusion S))"
      proof cases
        case extra
        have first: "term_formed (f 0)" "self_contained_term (f 0)"
          using support extra by (auto simp: related_extra_schema_def data_meaning)
        obtain ys where tail: "f 1=data_list_term ys" "data_elements ys"
          using support[rule_format, of 1 list_site data_y] extra
          by (auto simp: related_extra_schema_def list_meaning)
        have witness: "bag_difference_witness related apart [] (f 0#ys)"
          by (rule bag_difference_witness.extra)
        show ?thesis by (intro exI[of _ "[]"] exI[of _ "f 0#ys"])
          (use first tail witness in \<open>simp add: extra related_extra_schema_def\<close>)
      next
        case missing
        have first: "term_formed (f 0)" "self_contained_term (f 0)"
          using support missing by (auto simp: related_missing_schema_def data_meaning)
        obtain xs where tail: "f 1=data_list_term xs" "data_elements xs"
          using support[rule_format, of 1 list_site data_y] missing
          by (auto simp: related_missing_schema_def list_meaning)
        have checked: "(all_site,Pair_Term (f 0) (f 2))\<in>positive_meaning P"
          using support missing by (auto simp: related_missing_schema_def)
        obtain ys where other: "f 2=data_list_term ys" "\<forall>y\<in>set ys. apart (f 0) y"
          using absence.sound[OF checked] by auto
        have data: "data_elements ys" using other(2) apart_data by blast
        have witness: "bag_difference_witness related apart (f 0#xs) ys"
          by (rule bag_difference_witness.missing) (rule other(2))
        show ?thesis by (intro exI[of _ "f 0#xs"] exI[of _ ys])
          (use first tail other data witness in \<open>simp add: missing related_missing_schema_def\<close>)
      next
        case step
        have selection: "(select_site,Pair_Term (f 0) (Pair_Term (f 2) (f 3)))\<in>positive_meaning P"
          using support step by (auto simp: bag_step_schema_def)
        obtain y pre post where selected: "f 2=data_list_term (pre@y#post)"
          "f 3=data_list_term (pre@post)" "data_elements (pre@y#post)" "related (f 0) y"
          using selection_sound[OF selection] by auto
        obtain xs zs where tail: "f 1=data_list_term xs" "f 3=data_list_term zs"
          "data_elements xs" "data_elements zs" "bag_difference_witness related apart xs zs"
          using support[rule_format, of 1 difference_site "Pattern_Pair data_y data_w"] step
          by (auto simp: bag_step_schema_def)
        have residual: "zs=pre@post" using selected(2) tail(2) by (simp add: data_list_term_injective)
        have witness: "bag_difference_witness related apart (f 0#xs) (pre@y#post)"
          by (rule bag_difference_witness.matching)
            (rule selected(4), use tail(5) residual in simp)
        have first: "term_formed (f 0) \<and> self_contained_term (f 0)"
          using comparison_data[OF selected(4)] by blast
        show ?thesis by (intro exI[of _ "f 0#xs"] exI[of _ "pre@y#post"])
          (use selected tail witness first in \<open>auto simp: step bag_step_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem difference_complete:
  assumes "data_elements xs" "data_elements ys" "bag_difference_witness related apart xs ys"
  shows "(difference_site,Pair_Term (data_list_term xs) (data_list_term ys))\<in>positive_meaning P"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  obtain y zs where shape: "ys=y#zs" using Nil.prems(3)
    by (cases ys) (auto simp: bag_difference_witness_nil)
  have first: "(data_site,y)\<in>positive_meaning P"
    and tail: "(list_site,data_list_term zs)\<in>positive_meaning P"
    using Nil.prems(2) shape by (auto simp: data_meaning list_meaning data_list_term_injective)
  let ?f="\<lambda>i::nat. if i=0 then y else data_list_term zs"
  have result: "(difference_site,evaluate_pattern ?f
      (schema_conclusion (related_extra_schema data_site list_site)))\<in>positive_meaning P"
    by (rule difference_rule[where c=0])
      (use Nil.prems(2) shape first tail in \<open>auto simp: related_difference_clauses_def related_extra_schema_def
        schema_variables_def data_list_term_formed\<close>)
  show ?case using result by (simp add: shape related_extra_schema_def)
next
  case (Cons x xs)
  consider (missing) "\<forall>y\<in>set ys. apart x y"
    | (matching) y pre post where "ys=pre@y#post" "related x y" "bag_difference_witness related apart xs (pre@post)"
    using Cons.prems(3) by (auto simp: bag_difference_witness_cons)
  then show ?case
  proof cases
    case missing
    have first: "(data_site,x)\<in>positive_meaning P"
      and tail: "(list_site,data_list_term xs)\<in>positive_meaning P"
      using Cons.prems(1) by (auto simp: data_meaning list_meaning data_list_term_injective)
    have checked: "(all_site,Pair_Term x (data_list_term ys))\<in>positive_meaning P"
      by (rule absence.complete) (use Cons.prems(1) missing in auto)
    let ?f="\<lambda>i::nat. if i=0 then x else if i=1 then data_list_term xs else data_list_term ys"
    have result: "(difference_site,evaluate_pattern ?f
        (schema_conclusion (related_missing_schema data_site list_site all_site)))\<in>positive_meaning P"
      by (rule difference_rule[where c=1])
        (use Cons.prems(1,2) first tail checked in \<open>auto simp: related_difference_clauses_def related_missing_schema_def
          schema_variables_def data_list_term_formed\<close>)
    show ?thesis using result by (simp add: related_missing_schema_def)
  next
    case (matching y pre post)
    have data: "data_elements (pre@y#post)" using Cons.prems(2) matching(1) by simp
    have selection: "(select_site,Pair_Term x
        (Pair_Term (data_list_term ys) (data_list_term (pre@post))))\<in>positive_meaning P"
      using selection_complete[OF data matching(2)] by (simp only: matching(1))
    have tail: "(difference_site,Pair_Term (data_list_term xs) (data_list_term (pre@post)))\<in>positive_meaning P"
      by (rule Cons.IH) (use Cons.prems(1) data matching(3) in auto)
    let ?f="\<lambda>i::nat. if i=0 then x else if i=1 then data_list_term xs
      else if i=2 then data_list_term ys else data_list_term (pre@post)"
    have result: "(difference_site,evaluate_pattern ?f
        (schema_conclusion (bag_step_schema select_site difference_site)))\<in>positive_meaning P"
      by (rule difference_rule[where c=2])
        (use Cons.prems(1,2) data selection tail in \<open>auto simp: related_difference_clauses_def bag_step_schema_def
          schema_variables_def data_list_term_formed\<close>)
    show ?thesis using result by (simp add: bag_step_schema_def)
  qed
qed

theorem difference_exact:
  "(difference_site,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
      data_elements xs \<and> data_elements ys \<and> bag_difference_witness related apart xs ys)"
  using difference_sound difference_complete by blast

corollary difference_lists:
  "(difference_site,Pair_Term (data_list_term xs) (data_list_term ys))\<in>positive_meaning P \<longleftrightarrow>
    data_elements xs \<and> data_elements ys \<and> bag_difference_witness related apart xs ys"
  by (auto simp: difference_exact data_list_term_injective)

theorem difference_collections:
  assumes first: "data_collection_presents read A a" and second: "data_collection_presents read B b"
    and equal: "\<And>z w p q. read z p \<Longrightarrow> read w q \<Longrightarrow> related p q \<longleftrightarrow> z=w"
    and unequal: "\<And>z w p q. read z p \<Longrightarrow> read w q \<Longrightarrow> apart p q \<longleftrightarrow> z\<noteq>w"
  shows "(difference_site,Pair_Term a b)\<in>positive_meaning P \<longleftrightarrow> A\<noteq>B"
proof -
  have recovery: "z=w" if "read z p" "read w p" for z w p
    using equal[OF that(1) that(1)] equal[OF that(1,2)] by simp
  have formed: "term_formed p \<and> self_contained_term p" if "read z p" for z p
  proof -
    have same: "related p p" using equal[OF that that] by simp
    show ?thesis using comparison_data[OF same] by blast
  qed
  obtain xs ps where left: "distinct xs" "set xs=A" "list_all2 read xs ps" "a=data_list_term ps"
    using first unfolding data_collection_presents_def by blast
  obtain ys qs where right: "distinct ys" "set ys=B" "list_all2 read ys qs" "b=data_list_term qs"
    using second unfolding data_collection_presents_def by blast
  have data: "data_elements ps" "data_elements qs"
    using list_all2_members[OF left(3)] list_all2_members[OF right(3)] formed by blast+
  have witnesses: "bag_difference_witness related apart ps qs \<longleftrightarrow> mset xs\<noteq>mset ys"
    by (rule bag_difference_witness_readings[OF left(3) right(3) recovery equal unequal])
  have identity: "mset xs=mset ys \<longleftrightarrow> A=B"
    using set_eq_iff_mset_eq_distinct[OF left(1) right(1)] left(2) right(2) by blast
  show ?thesis using data by (simp only: left(4) right(4) difference_lists witnesses identity; blast)
qed

end

text \<open>
  These clauses realize the independent finite witness theorem through two
  actual comparison definitions. Selection removes exactly one positively
  matched occurrence. Absence checks every member through the inequality
  definition, and recursion checks the entire residual list boundary.

  The raw contract is explicit on every term: both operands are complete data
  lists and the positive witness relation holds. An empty absence list checks
  context formation. A caller that presents another notion establishes its
  equality and inequality equations locally; the generic collection theorem
  then identifies this witness relation with inequality of the finite subjects.
  The definitions may belong to one positive recursive group. A failed call
  is never used as a native premise.
\<close>

end
