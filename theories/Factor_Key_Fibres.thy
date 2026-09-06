theory Factor_Key_Fibres
  imports Factor_Environment_Admission
begin

section \<open>Every occurrence at a supplied key is retained\<close>

definition key_values :: "'k \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> 'v list" where
  "key_values k xs = map snd (filter (\<lambda>z. fst z=k) xs)"

lemma key_values_simps [simp]:
  "key_values k []=[]"
  "key_values k ((j,v)#xs)=(if j=k then v#key_values k xs else key_values k xs)"
  by (simp_all add: key_values_def)

lemma key_values_set:
  "set (key_values k xs)={v. (k,v)\<in>set xs}"
  by (auto simp: key_values_def intro: rev_image_eqI)

lemma key_values_count:
  "count_list (key_values k xs) v=count_list xs (k,v)"
  by (induction xs) (auto simp: key_values_def split: prod.splits)

lemma key_values_distinct:
  assumes "distinct xs"
  shows "distinct (key_values k xs)"
  using assms by (induction xs) (auto simp: key_values_set split: prod.splits)

lemma key_values_map:
  assumes "inj f"
  shows "key_values (f k) (map (\<lambda>(j,v). (f j,g v)) xs)=map g (key_values k xs)"
  using assms by (induction xs) (auto simp: inj_eq split: prod.splits)

lemma bag_comparison_encoded:
  assumes injective: "inj f" and data: "data_elements (map f xs)"
  shows "(6,Pair_Term (data_list_term (map f xs)) t)\<in>positive_meaning bag_comparison_system
    \<longleftrightarrow> (\<exists>ys. t=data_list_term (map f ys) \<and> mset xs=mset ys)"
proof
  assume holds: "(6,Pair_Term (data_list_term (map f xs)) t)\<in>positive_meaning bag_comparison_system"
  obtain us where presented: "t=data_list_term us" "mset (map f xs)=mset us"
    using holds by (auto simp: bag_comparison_exact data_list_term_injective)
  have range: "\<forall>u\<in>set us. \<exists>y. u=f y"
    using mset_eq_setD[OF presented(2)] by auto
  obtain ys where list: "us=map f ys" using range list_range_witnesses by blast
  have same: "mset xs=mset ys"
    using presented(2) list injective_mapped_multisets[OF injective] by simp
  show "\<exists>ys. t=data_list_term (map f ys) \<and> mset xs=mset ys"
    using presented(1) list same by blast
next
  assume "\<exists>ys. t=data_list_term (map f ys) \<and> mset xs=mset ys"
  then obtain ys where presented: "t=data_list_term (map f ys)" "mset xs=mset ys" by blast
  have sets: "set xs=set ys" by (rule mset_eq_setD[OF presented(2)])
  have formed: "data_elements (map f ys)" using data sets by auto
  show "(6,Pair_Term (data_list_term (map f xs)) t)\<in>positive_meaning bag_comparison_system"
    using data formed presented(2) by (simp add: presented(1) bag_comparison_lists)
qed

abbreviation key_fibre_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "key_fibre_argument k xs ys \<equiv> Pair_Term k (Pair_Term xs ys)"

definition key_fibre_nil_schema :: "(nat,nat,nat) factor_schema" where
  "key_fibre_nil_schema=data_rule
    (Pattern_Pair data_x (Pattern_Pair (Pattern_Payload []) (Pattern_Payload []))) {(0,2,data_x)}"

definition key_fibre_keep_schema :: "(nat,nat,nat) factor_schema" where
  "key_fibre_keep_schema=data_rule
    (Pattern_Pair data_x
      (Pattern_Pair (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
        (Pattern_Pair data_y data_w)))
    {(0,28,Pattern_Pair data_x (Pattern_Pair data_z data_w))}"

definition key_fibre_skip_schema :: "(nat,nat,nat) factor_schema" where
  "key_fibre_skip_schema=data_rule
    (Pattern_Pair data_x
      (Pattern_Pair (Pattern_Pair (Pattern_Pair data_y data_z) data_w) (Pattern_Variable 4)))
    {(0,3,Pattern_Pair data_x data_y),
     (1,28,Pattern_Pair data_x (Pattern_Pair data_w (Pattern_Variable 4)))}"

definition key_fibre_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "key_fibre_clauses={(0,key_fibre_nil_schema),(1,key_fibre_keep_schema),(2,key_fibre_skip_schema)}"

definition key_fibre_system :: "(nat,nat,nat,nat) schema_system" where
  "key_fibre_system=add_view_definition environment_identity_system 28 data_x key_fibre_clauses"

lemmas key_fibre_schema_defs = key_fibre_nil_schema_def key_fibre_keep_schema_def key_fibre_skip_schema_def

lemma key_fibre_system_formed [simp]: "schema_system_formed key_fibre_system"
  unfolding key_fibre_system_def
  by (rule add_recursive_definition_formed[OF environment_identity_system_formed])
    (auto simp: key_fibre_clauses_def key_fibre_schema_defs schema_formed_def
      schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma key_fibre_definitions [simp]:
  "system_definitions key_fibre_system=insert 28 (system_definitions environment_identity_system)"
  by (simp add: key_fibre_system_def)

lemma key_fibre_call:
  "schema_call_formed key_fibre_system d t \<longleftrightarrow>
    d\<in>system_definitions key_fibre_system \<and> term_formed t"
  using added_variable_calls[OF environment_identity_system_formed
    key_fibre_system_formed[unfolded key_fibre_system_def] environment_identity_call]
  by (simp only: key_fibre_system_def[symmetric])

theorem key_fibre_old_meaning:
  assumes "d\<in>system_definitions environment_identity_system"
  shows "(d,t)\<in>positive_meaning key_fibre_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning environment_identity_system"
  using added_definition_preserves_old(2)[OF environment_identity_system_formed
    key_fibre_system_formed[unfolded key_fibre_system_def], of d t] assms
  by (auto simp: key_fibre_system_def)

lemma key_fibre_clause [simp]:
  "((28,c),S)\<in>system_clauses key_fibre_system \<longleftrightarrow> (c,S)\<in>key_fibre_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses environment_identity_system \<Longrightarrow>
    d\<in>system_definitions environment_identity_system" for d c S
    using environment_identity_system_formed unfolding schema_system_formed_def by blast
  have absent: "((28,c),S)\<notin>system_clauses environment_identity_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: key_fibre_system_def)
qed

lemma key_fibre_bag_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6}"
  shows "(d,t)\<in>positive_meaning key_fibre_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning bag_comparison_system"
  using key_fibre_old_meaning[of d t] environment_identity_old_meaning[of d t]
    environment_comparison_old_meaning[of d t] environment_bag_base_meaning[OF assms, of t] assms by auto

lemma key_fibre_data:
  "(2,t)\<in>positive_meaning key_fibre_system \<longleftrightarrow> term_formed t \<and> self_contained_term t"
  using key_fibre_bag_meaning[of 2 t] bag_comparison_recognizes[of t] by auto

lemma key_fibre_inequality:
  "(3,Pair_Term x y)\<in>positive_meaning key_fibre_system \<longleftrightarrow>
    term_formed x \<and> self_contained_term x \<and> term_formed y \<and> self_contained_term y \<and> x\<noteq>y"
  using key_fibre_bag_meaning[of 3 "Pair_Term x y"] bag_comparison_old_meaning[of 3 "Pair_Term x y"]
    data_comparison_exact[of "Pair_Term x y"] by auto

theorem key_fibre_sound:
  assumes holds: "(28,t)\<in>positive_meaning key_fibre_system"
  shows "\<exists>k xs. t=key_fibre_argument k (pair_list_term xs) (data_list_term (key_values k xs)) \<and>
    term_formed k \<and> self_contained_term k \<and> formed_key_rows xs"
proof -
  let ?Q="\<lambda>t. \<exists>k xs. t=key_fibre_argument k (pair_list_term xs) (data_list_term (key_values k xs)) \<and>
    term_formed k \<and> self_contained_term k \<and> formed_key_rows xs"
  have invariant: "(28::nat)=28 \<longrightarrow> ?Q t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=28 \<longrightarrow> ?Q t"])
    fix d c S f
    assume clause: "((d,c),S)\<in>system_clauses key_fibre_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
      and call: "schema_call_formed key_fibre_system d (evaluate_pattern f (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning key_fibre_system \<and>
        (e=28 \<longrightarrow> ?Q (evaluate_pattern f p))"
    show "d=28 \<longrightarrow> ?Q (evaluate_pattern f (schema_conclusion S))"
    proof
      assume "d=28"
      then consider (nil) "S=key_fibre_nil_schema"
        | (keep) "S=key_fibre_keep_schema" | (skip) "S=key_fibre_skip_schema"
        using clause by (auto simp: key_fibre_clauses_def)
      then show "?Q (evaluate_pattern f (schema_conclusion S))"
      proof cases
        case nil
        have key: "term_formed (f 0)" "self_contained_term (f 0)"
          using support nil by (auto simp: key_fibre_nil_schema_def key_fibre_data)
        show ?thesis by (intro exI[of _ "f 0"] exI[of _ "[]"])
          (use key in \<open>simp add: nil key_fibre_nil_schema_def\<close>)
      next
        case keep
        obtain xs where tail: "f 2=pair_list_term xs" "f 3=data_list_term (key_values (f 0) xs)"
          "term_formed (f 0)" "self_contained_term (f 0)" "formed_key_rows xs"
          using support[rule_format, of 0 28 "Pattern_Pair data_x (Pattern_Pair data_z data_w)"] keep
          by (auto simp: key_fibre_keep_schema_def)
        have value_formed: "term_formed (f 1)"
          using assignment keep by (auto simp: key_fibre_keep_schema_def schema_variables_def)
        show ?thesis by (intro exI[of _ "f 0"] exI[of _ "(f 0,f 1)#xs"])
          (use tail value_formed in \<open>auto simp: keep key_fibre_keep_schema_def\<close>)
      next
        case skip
        obtain xs where tail: "f 3=pair_list_term xs" "f 4=data_list_term (key_values (f 0) xs)"
          "term_formed (f 0)" "self_contained_term (f 0)" "formed_key_rows xs"
          using support[rule_format, of 1 28 "Pattern_Pair data_x (Pattern_Pair data_w (Pattern_Variable 4))"] skip
          by (auto simp: key_fibre_skip_schema_def)
        have keys: "term_formed (f 1)" "self_contained_term (f 1)" "f 0\<noteq>f 1"
          using support[rule_format, of 0 3 "Pattern_Pair data_x data_y"] skip
          by (auto simp: key_fibre_skip_schema_def key_fibre_inequality)
        have value_formed: "term_formed (f 2)"
          using assignment skip by (auto simp: key_fibre_skip_schema_def schema_variables_def)
        show ?thesis by (intro exI[of _ "f 0"] exI[of _ "(f 1,f 2)#xs"])
          (use tail keys value_formed in \<open>auto simp: skip key_fibre_skip_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem key_fibre_complete:
  assumes "term_formed k" "self_contained_term k" "formed_key_rows xs"
  shows "(28,key_fibre_argument k (pair_list_term xs) (data_list_term (key_values k xs)))
    \<in>positive_meaning key_fibre_system"
  using assms
proof (induction xs)
  case Nil
  have child: "(2,k)\<in>positive_meaning key_fibre_system"
    using Nil.prems by (simp add: key_fibre_data)
  have result: "(28,evaluate_pattern (\<lambda>_. k) (schema_conclusion key_fibre_nil_schema))
    \<in>positive_meaning key_fibre_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use Nil.prems child in \<open>auto simp: key_fibre_clauses_def key_fibre_nil_schema_def
        schema_variables_def key_fibre_call octets_formed_def\<close>)
  show ?case using result by (simp add: key_fibre_nil_schema_def)
next
  case (Cons z xs)
  obtain j v where row: "z=(j,v)" by (cases z) auto
  have tail: "(28,key_fibre_argument k (pair_list_term xs) (data_list_term (key_values k xs)))
    \<in>positive_meaning key_fibre_system"
    using Cons by auto
  have terms: "term_formed (pair_list_term xs)" "term_formed (data_list_term (key_values k xs))"
    using schema_call_formed_target[OF positive_meaning_formed[OF tail]] by auto
  show ?case
  proof (cases "j=k")
    case True
    let ?f="\<lambda>i::nat. if i=0 then k else if i=1 then v else if i=2 then pair_list_term xs
      else data_list_term (key_values k xs)"
    have result: "(28,evaluate_pattern ?f (schema_conclusion key_fibre_keep_schema))
      \<in>positive_meaning key_fibre_system"
      by (rule ordinary_positive_valuation_step[where c=1])
        (use Cons.prems terms tail in \<open>auto simp: row key_fibre_clauses_def key_fibre_keep_schema_def
          schema_variables_def key_fibre_call\<close>)
    show ?thesis using result True by (simp add: row key_fibre_keep_schema_def)
  next
    case False
    have different: "(3,Pair_Term k j)\<in>positive_meaning key_fibre_system"
      using Cons.prems False by (auto simp: row key_fibre_inequality)
    let ?f="\<lambda>i::nat. if i=0 then k else if i=1 then j else if i=2 then v else if i=3 then pair_list_term xs
      else data_list_term (key_values k xs)"
    have result: "(28,evaluate_pattern ?f (schema_conclusion key_fibre_skip_schema))
      \<in>positive_meaning key_fibre_system"
      by (rule ordinary_positive_valuation_step[where c=2])
        (use Cons.prems terms tail different in \<open>auto simp: row key_fibre_clauses_def key_fibre_skip_schema_def
          schema_variables_def key_fibre_call\<close>)
    show ?thesis using result False by (simp add: row key_fibre_skip_schema_def)
  qed
qed

theorem key_fibre_exact:
  "(28,t)\<in>positive_meaning key_fibre_system \<longleftrightarrow>
    (\<exists>k xs. t=key_fibre_argument k (pair_list_term xs) (data_list_term (key_values k xs)) \<and>
      term_formed k \<and> self_contained_term k \<and> formed_key_rows xs)"
  using key_fibre_sound key_fibre_complete by blast

corollary key_fibre_lists:
  "(28,key_fibre_argument k (pair_list_term xs) t)\<in>positive_meaning key_fibre_system \<longleftrightarrow>
    term_formed k \<and> self_contained_term k \<and> formed_key_rows xs \<and> t=data_list_term (key_values k xs)"
  by (auto simp: key_fibre_exact pair_list_term_injective)

lemma key_fibre_mapped_lists:
  assumes injective: "inj f" and key: "term_formed (f k)" "self_contained_term (f k)"
    and rows: "formed_key_rows (map (\<lambda>(j,v). (f j,g v)) xs)"
  shows "(28,key_fibre_argument (f k)
    (data_list_term (map (\<lambda>z. Pair_Term (f (fst z)) (g (snd z))) xs)) t)
      \<in>positive_meaning key_fibre_system \<longleftrightarrow> t=data_list_term (map g (key_values k xs))"
proof -
  have encoded: "data_list_term (map (\<lambda>z. Pair_Term (f (fst z)) (g (snd z))) xs)=
    pair_list_term (map (\<lambda>(j,v). (f j,g v)) xs)"
    by (simp add: case_prod_unfold comp_def)
  show ?thesis by (simp only: encoded key_fibre_lists key_values_map[OF injective])
    (use key rows in simp)
qed

text \<open>
  The recursive program inspects every key and the final list boundary.
  Repeated occurrences of the requested key force the keep clause; the skip
  clause requires the existing ordinary inequality definition. Its two
  premises retain distinct sockets. No absent-entry test or filter callback
  is added to the consequence operator.

  Keys are formed self-contained data. Values need only be formed terms.
  Every retained occurrence, including repeated equal values, remains in
  the supplied order. No functional-table or distinctness assumption is
  imposed on this collector. The later material profile separately checks
  the whole artifact and compares each collected result as a counted
  collection. All earlier interfaces and meanings remain fixed.
\<close>

end
