theory Factor_Related_Bags
  imports Factor_Bag_Comparison Bag_Readings
begin

section \<open>Selection through an actual comparison definition\<close>

definition related_selection_here_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "related_selection_here_schema compare list=data_rule
    (Pattern_Pair data_x (Pattern_Pair (Pattern_Pair data_y data_z) data_z))
    {(0,compare,Pattern_Pair data_x data_y),(1,list,data_z)}"

definition related_selection_clauses ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> (nat,nat,nat) factor_schema) set" where
  "related_selection_clauses data list compare select=
    {(0,related_selection_here_schema compare list),(1,selection_later_schema data select)}"

definition related_bag_clauses :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> (nat,nat,nat) factor_schema) set" where
  "related_bag_clauses select bag={(0,bag_nil_schema),(1,bag_step_schema select bag)}"

locale related_bags =
  fixes P :: "(nat,nat,nat,nat) schema_system"
    and data_site list_site compare_site select_site bag_site :: nat
  assumes system_formed: "schema_system_formed P"
    and selection_family: "\<And>c S. ((select_site,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>related_selection_clauses data_site list_site compare_site select_site"
    and bag_family: "\<And>c S. ((bag_site,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>related_bag_clauses select_site bag_site"
    and selection_call: "\<And>t. schema_call_formed P select_site t \<longleftrightarrow> term_formed t"
    and bag_call: "\<And>t. schema_call_formed P bag_site t \<longleftrightarrow> term_formed t"
    and data_meaning: "\<And>t. (data_site,t)\<in>positive_meaning P \<longleftrightarrow>
      term_formed t \<and> self_contained_term t"
    and list_meaning: "\<And>t. (list_site,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>xs. t=data_list_term xs \<and> data_elements xs)"
    and comparison_data: "\<And>x y. (compare_site,Pair_Term x y)\<in>positive_meaning P \<Longrightarrow>
      term_formed x \<and> self_contained_term x \<and> term_formed y \<and> self_contained_term y"
begin

abbreviation related where
  "related x y \<equiv> (compare_site,Pair_Term x y)\<in>positive_meaning P"

lemma rule:
  assumes clause: "((d,c),S)\<in>system_clauses P"
    and selected: "d\<in>{select_site,bag_site}"
    and ordinary: "schema_material_premises S={}"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning P"
  shows "(d,evaluate_pattern f (schema_conclusion S))\<in>positive_meaning P"
proof -
  have sf: "schema_formed S" using clause system_formed by (auto simp: schema_system_formed_def)
  have tf: "term_formed (evaluate_pattern f (schema_conclusion S))"
    by (rule evaluate_pattern_formed)
      (use sf assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  have call: "schema_call_formed P d (evaluate_pattern f (schema_conclusion S))"
    using selected tf by (auto simp: selection_call bag_call)
  show ?thesis by (rule ordinary_positive_valuation_step[OF clause ordinary assignment call support])
qed

theorem selection_sound:
  assumes holds: "(select_site,t)\<in>positive_meaning P"
  shows "\<exists>x y pre post. t=Pair_Term x
    (Pair_Term (data_list_term (pre@y#post)) (data_list_term (pre@post))) \<and>
    data_elements (pre@y#post) \<and> related x y"
proof -
  let ?Q="\<lambda>t. \<exists>x y pre post. t=Pair_Term x
    (Pair_Term (data_list_term (pre@y#post)) (data_list_term (pre@post))) \<and>
    data_elements (pre@y#post) \<and> related x y"
  have invariant: "select_site=select_site \<longrightarrow> ?Q t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=select_site \<longrightarrow> ?Q t"])
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses P"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
      and call: "schema_call_formed P d (evaluate_pattern f (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning P \<and>
        (e=select_site \<longrightarrow> ?Q (evaluate_pattern f p))"
    show "d=select_site \<longrightarrow> ?Q (evaluate_pattern f (schema_conclusion S))"
    proof
      assume "d=select_site"
      then have cases: "S=related_selection_here_schema compare_site list_site \<or>
        S=selection_later_schema data_site select_site"
        using clause by (auto simp: selection_family related_selection_clauses_def)
      then show "?Q (evaluate_pattern f (schema_conclusion S))"
      proof
        assume schema: "S=related_selection_here_schema compare_site list_site"
        have compared: "related (f 0) (f 1)" and list: "(list_site,f 2)\<in>positive_meaning P"
          using support schema by (auto simp: related_selection_here_schema_def)
        have head: "term_formed (f 1) \<and> self_contained_term (f 1)"
          using comparison_data[OF compared] by blast
        obtain post where tail: "f 2=data_list_term post" "data_elements post"
          using list by (auto simp: list_meaning)
        show ?thesis by (intro exI[of _ "f 0"] exI[of _ "f 1"] exI[of _ "[]"] exI[of _ post])
          (use head tail compared in \<open>simp add: schema related_selection_here_schema_def\<close>)
      next
        assume schema: "S=selection_later_schema data_site select_site"
        have skipped: "term_formed (f 2) \<and> self_contained_term (f 2)"
          using support schema by (auto simp: selection_later_schema_def data_meaning)
        obtain y pre post where tail: "f 1=data_list_term (pre@y#post)"
          "f 3=data_list_term (pre@post)" "data_elements (pre@y#post)" "related (f 0) y"
          using support[rule_format, of 1 select_site "Pattern_Pair data_x (Pattern_Pair data_y data_w)"] schema
          by (auto simp: selection_later_schema_def)
        show ?thesis by (intro exI[of _ "f 0"] exI[of _ y] exI[of _ "f 2#pre"] exI[of _ post])
          (use skipped tail in \<open>simp add: schema selection_later_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem selection_complete:
  assumes "data_elements (pre@y#post)" "related x y"
  shows "(select_site,Pair_Term x
    (Pair_Term (data_list_term (pre@y#post)) (data_list_term (pre@post))))\<in>positive_meaning P"
  using assms
proof (induction pre)
  case Nil
  have head: "term_formed x" using comparison_data[OF Nil.prems(2)] by blast
  have tail: "(list_site,data_list_term post)\<in>positive_meaning P"
    using Nil.prems(1) by (auto simp: list_meaning)
  let ?f="\<lambda>a::nat. if a=0 then x else if a=1 then y else data_list_term post"
  have result: "(select_site,evaluate_pattern ?f
      (schema_conclusion (related_selection_here_schema compare_site list_site)))\<in>positive_meaning P"
    by (rule rule[where c=0])
      (use Nil.prems head tail in \<open>auto simp: selection_family related_selection_clauses_def
        related_selection_here_schema_def schema_variables_def data_list_term_formed\<close>)
  show ?case using result by (simp add: related_selection_here_schema_def)
next
  case (Cons z pre)
  have head: "term_formed x" using comparison_data[OF Cons.prems(2)] by blast
  have skipped: "(data_site,z)\<in>positive_meaning P"
    using Cons.prems(1) by (simp add: data_meaning)
  have tail: "(select_site,Pair_Term x
    (Pair_Term (data_list_term (pre@y#post)) (data_list_term (pre@post))))\<in>positive_meaning P"
    using Cons by auto
  let ?f="\<lambda>a::nat. if a=0 then x else if a=1 then data_list_term (pre@y#post)
    else if a=2 then z else data_list_term (pre@post)"
  have result: "(select_site,evaluate_pattern ?f
      (schema_conclusion (selection_later_schema data_site select_site)))\<in>positive_meaning P"
    by (rule rule[where c=1])
      (use Cons.prems head skipped tail in \<open>auto simp: selection_family related_selection_clauses_def
        selection_later_schema_def schema_variables_def data_list_term_formed\<close>)
  show ?case using result by (simp add: selection_later_schema_def)
qed

theorem selection_exact:
  "(select_site,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>x y pre post. t=Pair_Term x
      (Pair_Term (data_list_term (pre@y#post)) (data_list_term (pre@post))) \<and>
      data_elements (pre@y#post) \<and> related x y)"
  using selection_sound selection_complete by blast

section \<open>Matching every occurrence through that same definition\<close>

theorem comparison_sound:
  assumes holds: "(bag_site,t)\<in>positive_meaning P"
  shows "\<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
    data_elements xs \<and> data_elements ys \<and> rel_mset related (mset xs) (mset ys)"
proof -
  let ?Q="\<lambda>t. \<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
    data_elements xs \<and> data_elements ys \<and> rel_mset related (mset xs) (mset ys)"
  have invariant: "bag_site=bag_site \<longrightarrow> ?Q t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=bag_site \<longrightarrow> ?Q t"])
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses P"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
      and call: "schema_call_formed P d (evaluate_pattern f (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning P \<and>
        (e=bag_site \<longrightarrow> ?Q (evaluate_pattern f p))"
    show "d=bag_site \<longrightarrow> ?Q (evaluate_pattern f (schema_conclusion S))"
    proof
      assume "d=bag_site"
      then have cases: "S=bag_nil_schema \<or> S=bag_step_schema select_site bag_site"
        using clause by (auto simp: bag_family related_bag_clauses_def)
      then show "?Q (evaluate_pattern f (schema_conclusion S))"
      proof
        assume "S=bag_nil_schema"
        then show ?thesis by (intro exI[of _ "[]"] exI[of _ "[]"]) (simp add: bag_nil_schema_def)
      next
        assume schema: "S=bag_step_schema select_site bag_site"
        have selection: "(select_site,Pair_Term (f 0) (Pair_Term (f 2) (f 3)))\<in>positive_meaning P"
          using support schema by (auto simp: bag_step_schema_def)
        obtain y pre post where selected: "f 2=data_list_term (pre@y#post)"
          "f 3=data_list_term (pre@post)" "data_elements (pre@y#post)" "related (f 0) y"
          using selection_sound[OF selection] by auto
        obtain xs zs where compared: "f 1=data_list_term xs" "f 3=data_list_term zs"
          "data_elements xs" "data_elements zs" "rel_mset related (mset xs) (mset zs)"
          using support[rule_format, of 1 bag_site "Pattern_Pair data_y data_w"] schema
          by (auto simp: bag_step_schema_def)
        have residual: "zs=pre@post" using selected(2) compared(2)
          by (simp add: data_list_term_injective)
        have head: "term_formed (f 0) \<and> self_contained_term (f 0)"
          using comparison_data[OF selected(4)] by blast
        have matching: "rel_mset related (mset (f 0#xs)) (mset (pre@y#post))"
          using rel_mset_Plus[OF selected(4) compared(5)] by (simp add: residual)
        show ?thesis by (intro exI[of _ "f 0#xs"] exI[of _ "pre@y#post"])
          (use selected compared head matching in \<open>auto simp: schema bag_step_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem comparison_complete:
  assumes "data_elements xs" "data_elements ys" "rel_mset related (mset xs) (mset ys)"
  shows "(bag_site,Pair_Term (data_list_term xs) (data_list_term ys))\<in>positive_meaning P"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  have empty: "ys=[]" using Nil.prems by simp
  have result: "(bag_site,evaluate_pattern (\<lambda>_. Payload_Term []) (schema_conclusion bag_nil_schema))
    \<in>positive_meaning P"
    by (rule rule[where c=0])
      (auto simp: bag_family related_bag_clauses_def bag_nil_schema_def schema_variables_def)
  show ?case using result empty by (simp add: bag_nil_schema_def)
next
  case (Cons x xs)
  obtain N y where removal: "mset ys=add_mset y N" "related x y" "rel_mset related (mset xs) N"
    using msed_rel_invL[OF Cons.prems(3)[simplified]] by blast
  have inside: "y\<in>set ys"
  proof -
    have "y\<in>#mset ys" using removal(1) by simp
    then show ?thesis by simp
  qed
  obtain pre post where split: "ys=pre@y#post" using split_list[OF inside] by blast
  have residual: "N=mset (pre@post)" using removal(1) by (simp add: split)
  have data: "data_elements (pre@y#post)" using Cons.prems(2) split by simp
  have selection: "(select_site,Pair_Term x
    (Pair_Term (data_list_term ys) (data_list_term (pre@post))))\<in>positive_meaning P"
    using selection_complete[OF data removal(2)] split by simp
  have tail: "(bag_site,Pair_Term (data_list_term xs) (data_list_term (pre@post)))\<in>positive_meaning P"
    by (rule Cons.IH) (use Cons.prems(1) data removal(3) residual in auto)
  let ?f="\<lambda>a::nat. if a=0 then x else if a=1 then data_list_term xs
    else if a=2 then data_list_term ys else data_list_term (pre@post)"
  have result: "(bag_site,evaluate_pattern ?f (schema_conclusion (bag_step_schema select_site bag_site)))
    \<in>positive_meaning P"
    by (rule rule[where c=1])
      (use Cons.prems(1,2) data selection tail in \<open>auto simp: bag_family related_bag_clauses_def
        bag_step_schema_def schema_variables_def data_list_term_formed\<close>)
  show ?case using result by (simp add: bag_step_schema_def)
qed

theorem comparison_exact:
  "(bag_site,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
      data_elements xs \<and> data_elements ys \<and> rel_mset related (mset xs) (mset ys))"
  using comparison_sound comparison_complete by blast

corollary comparison_lists:
  "(bag_site,Pair_Term (data_list_term xs) (data_list_term ys))\<in>positive_meaning P \<longleftrightarrow>
    data_elements xs \<and> data_elements ys \<and> rel_mset related (mset xs) (mset ys)"
  by (auto simp: comparison_exact data_list_term_injective)

section \<open>Member readings preserve sequence multiplicities\<close>

theorem comparison_readings:
  assumes first: "list_all2 read xs ps" and second: "list_all2 read ys qs"
    and compare: "\<And>z w x y. read z x \<Longrightarrow> read w y \<Longrightarrow> related x y \<longleftrightarrow> z=w"
  shows "(bag_site,Pair_Term (data_list_term ps) (data_list_term qs))\<in>positive_meaning P
    \<longleftrightarrow> mset xs=mset ys"
proof -
  have unique: "z=w" if "read z x" "read w x" for z w x
  proof -
    have "related x x" using compare[OF that(1) that(1)] by simp
    then show ?thesis using compare[OF that(1,2)] by blast
  qed
  have formed: "term_formed x \<and> self_contained_term x" if "read z x" for z x
  proof -
    have "related x x" using compare[OF that that] by simp
    then show ?thesis using comparison_data by blast
  qed
  have data: "data_elements ps" "data_elements qs"
    using list_all2_members[OF first] list_all2_members[OF second] formed by blast+
  have matching: "rel_mset related (mset ps) (mset qs) \<longleftrightarrow> mset xs=mset ys"
    by (rule rel_mset_readings[where R=read and C=related, OF first second unique compare])
  show ?thesis using data by (simp only: comparison_lists matching; blast)
qed

section \<open>Complete collection presentations recover equality of their subjects\<close>

theorem comparison_collections:
  assumes left: "data_collection_presents read A a"
    and right: "data_collection_presents read B b"
    and compare: "\<And>z w x y. read z x \<Longrightarrow> read w y \<Longrightarrow> related x y \<longleftrightarrow> z=w"
  shows "(bag_site,Pair_Term a b)\<in>positive_meaning P \<longleftrightarrow> A=B"
proof -
  obtain xs ps where first: "distinct xs" "set xs=A" "list_all2 read xs ps" "a=data_list_term ps"
    using left unfolding data_collection_presents_def by blast
  obtain ys qs where second: "distinct ys" "set ys=B" "list_all2 read ys qs" "b=data_list_term qs"
    using right unfolding data_collection_presents_def by blast
  have identity: "mset xs=mset ys \<longleftrightarrow> A=B"
    using set_eq_iff_mset_eq_distinct[OF first(1) second(1)] first(2) second(2) by blast
  show ?thesis by (simp only: first(4) second(4) comparison_readings[OF first(3) second(3) compare] identity)
qed

end

text \<open>
  The two clause families call explicit definition coordinates in an actual
  formed program. The relation in the exact comparison theorem is the positive
  meaning of that program's comparison call. No external predicate enters the
  operator. The proof permits that definition to participate in the same
  positive dependency cycle, provided the stated data boundary is established.

  Selection compares two entries, removes precisely the selected occurrence,
  and checks every skipped entry and the complete retained tail. Each recursive
  bag step has two distinct premise sockets. Its existential residual is an
  ordinary fully formed argument at both calls. The resulting relation matches
  every occurrence through the fixed comparison definition.

  When that callee compares presentations of one subject exactly, the lifted
  rule compares the recovered multisets and complete finite collections exactly. Every source
  entry remains present once, every child presentation may vary, and every
  enumeration order is admitted. The mathematical decoder used in that proof
  is a local witness; it is absent from the program and its semantic operator.
\<close>

end
