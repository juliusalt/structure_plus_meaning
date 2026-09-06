theory Factor_Data_List_Operations
  imports Factor_Target_Projection
begin

section \<open>Concatenation retains every input occurrence\<close>

abbreviation collection_join_argument ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "collection_join_argument x y z \<equiv> Pair_Term x (Pair_Term y z)"

abbreviation collection_join_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "collection_join_pattern x y z \<equiv> Pattern_Pair x (Pattern_Pair y z)"

definition data_append_nil_schema :: "(nat,nat,nat) factor_schema" where
  "data_append_nil_schema=data_rule
    (collection_join_pattern (Pattern_Payload []) data_x data_x) {(0,4,data_x)}"

definition data_append_cons_schema :: "(nat,nat,nat) factor_schema" where
  "data_append_cons_schema=data_rule
    (collection_join_pattern (Pattern_Pair data_x data_y) data_z (Pattern_Pair data_x data_w))
    {(0,2,data_x),(1,46,collection_join_pattern data_y data_z data_w)}"

definition data_append_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "data_append_clauses={(0,data_append_nil_schema),(1,data_append_cons_schema)}"

definition data_append_system :: "(nat,nat,nat,nat) schema_system" where
  "data_append_system=add_view_definition target_projection_system 46 data_x data_append_clauses"

lemma data_append_system_formed [simp]: "schema_system_formed data_append_system"
  unfolding data_append_system_def
  by (rule add_recursive_definition_formed[OF target_projection_system_formed])
    (auto simp: data_append_clauses_def data_append_nil_schema_def data_append_cons_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma data_append_definitions [simp]:
  "system_definitions data_append_system=insert 46 (system_definitions target_projection_system)"
  by (simp add: data_append_system_def)

lemma data_append_call:
  "schema_call_formed data_append_system d t \<longleftrightarrow>
    d\<in>system_definitions data_append_system \<and> term_formed t"
  using added_variable_calls[OF target_projection_system_formed
    data_append_system_formed[unfolded data_append_system_def] target_projection_call]
  by (simp only: data_append_system_def[symmetric])

lemma data_append_old_meaning:
  assumes "d\<in>system_definitions target_projection_system"
  shows "(d,t)\<in>positive_meaning data_append_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning target_projection_system"
  using added_definition_preserves_old(2)[OF target_projection_system_formed
    data_append_system_formed[unfolded data_append_system_def], of d t] assms
  by (auto simp: data_append_system_def)

lemma data_append_clause [simp]:
  "((46,c),S)\<in>system_clauses data_append_system \<longleftrightarrow> (c,S)\<in>data_append_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses target_projection_system \<Longrightarrow>
    d\<in>system_definitions target_projection_system" for d c S
    using target_projection_system_formed unfolding schema_system_formed_def by blast
  have absent: "((46,c),S)\<notin>system_clauses target_projection_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: data_append_system_def)
qed

lemma data_append_bag_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6}"
  shows "(d,t)\<in>positive_meaning data_append_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning bag_comparison_system"
  using data_append_old_meaning[of d t] target_projection_bag_meaning[OF assms, of t] assms by auto

lemma data_append_components:
  "(2,t)\<in>positive_meaning data_append_system \<longleftrightarrow> term_formed t \<and> self_contained_term t"
  "(4,t)\<in>positive_meaning data_append_system \<longleftrightarrow> (\<exists>xs. t=data_list_term xs \<and> data_elements xs)"
  using data_append_bag_meaning[of 2 t] data_append_bag_meaning[of 4 t]
    bag_comparison_recognizes[of t] data_list_exact[of t] by auto

theorem data_append_sound:
  assumes holds: "(46,t)\<in>positive_meaning data_append_system"
  shows "\<exists>xs ys. t=collection_join_argument (data_list_term xs) (data_list_term ys)
    (data_list_term (xs@ys)) \<and> data_elements xs \<and> data_elements ys"
proof -
  let ?Q="\<lambda>t. \<exists>xs ys. t=collection_join_argument (data_list_term xs) (data_list_term ys)
    (data_list_term (xs@ys)) \<and> data_elements xs \<and> data_elements ys"
  have invariant: "(46::nat)=46 \<longrightarrow> ?Q t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=46 \<longrightarrow> ?Q t"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses data_append_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and call: "schema_call_formed data_append_system d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning data_append_system \<and>
        (e=46 \<longrightarrow> ?Q (evaluate_pattern h p))"
    show "d=46 \<longrightarrow> ?Q (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=46"
      then have alternatives: "S=data_append_nil_schema \<or> S=data_append_cons_schema"
        using clause by (auto simp: data_append_clauses_def)
      then show "?Q (evaluate_pattern h (schema_conclusion S))"
      proof
        assume schema: "S=data_append_nil_schema"
        obtain ys where parts: "h 0=data_list_term ys" "data_elements ys"
          using support by (auto simp: schema data_append_nil_schema_def data_append_components)
        show ?thesis by (intro exI[of _ "[]"] exI[of _ ys])
          (use parts in \<open>simp add: schema data_append_nil_schema_def\<close>)
      next
        assume schema: "S=data_append_cons_schema"
        have first: "term_formed (h 0)" "self_contained_term (h 0)"
          using support by (auto simp: schema data_append_cons_schema_def data_append_components)
        obtain xs ys where tail: "h 1=data_list_term xs" "h 2=data_list_term ys"
          "h 3=data_list_term (xs@ys)" "data_elements xs" "data_elements ys"
          using support[rule_format, of 1 46 "collection_join_pattern data_y data_z data_w"]
          by (auto simp: schema data_append_cons_schema_def)
        show ?thesis by (intro exI[of _ "h 0#xs"] exI[of _ ys])
          (use first tail in \<open>simp add: schema data_append_cons_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem data_append_complete:
  assumes "data_elements xs" "data_elements ys"
  shows "(46,collection_join_argument (data_list_term xs) (data_list_term ys)
    (data_list_term (xs@ys)))\<in>positive_meaning data_append_system"
  using assms
proof (induction xs)
  case Nil
  have child: "(4,data_list_term ys)\<in>positive_meaning data_append_system"
    using Nil.prems by (auto simp: data_append_components)
  have result: "(46,evaluate_pattern (\<lambda>_. data_list_term ys) (schema_conclusion data_append_nil_schema))
    \<in>positive_meaning data_append_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use Nil.prems child in \<open>auto simp: data_append_clauses_def data_append_nil_schema_def
        schema_variables_def data_append_call data_list_term_formed octets_formed_def\<close>)
  show ?case using result by (simp add: data_append_nil_schema_def)
next
  case (Cons x xs)
  have first: "(2,x)\<in>positive_meaning data_append_system"
    using Cons.prems by (simp add: data_append_components)
  have tail: "(46,collection_join_argument (data_list_term xs) (data_list_term ys)
    (data_list_term (xs@ys)))\<in>positive_meaning data_append_system"
    using Cons by auto
  let ?h="\<lambda>i::nat. if i=0 then x else if i=1 then data_list_term xs
    else if i=2 then data_list_term ys else data_list_term (xs@ys)"
  have result: "(46,evaluate_pattern ?h (schema_conclusion data_append_cons_schema))
    \<in>positive_meaning data_append_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use Cons.prems first tail in \<open>auto simp: data_append_clauses_def data_append_cons_schema_def
        schema_variables_def data_append_call data_list_term_formed\<close>)
  show ?case using result by (simp add: data_append_cons_schema_def)
qed

theorem data_append_exact:
  "(46,t)\<in>positive_meaning data_append_system \<longleftrightarrow>
    (\<exists>xs ys. t=collection_join_argument (data_list_term xs) (data_list_term ys)
      (data_list_term (xs@ys)) \<and> data_elements xs \<and> data_elements ys)"
  using data_append_sound data_append_complete by blast

corollary data_append_lists:
  "(46,collection_join_argument (data_list_term xs) (data_list_term ys) (data_list_term zs))
    \<in>positive_meaning data_append_system \<longleftrightarrow>
    data_elements xs \<and> data_elements ys \<and> zs=xs@ys"
  by (auto simp: data_append_exact data_list_term_injective)

section \<open>Inclusion explicitly reuses the complete right collection\<close>

definition data_subset_nil_schema :: "(nat,nat,nat) factor_schema" where
  "data_subset_nil_schema=data_rule
    (Pattern_Pair (Pattern_Payload []) data_x) {(0,4,data_x)}"

definition data_subset_cons_schema :: "(nat,nat,nat) factor_schema" where
  "data_subset_cons_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z)
    {(0,5,Pattern_Pair data_x (Pattern_Pair data_z data_w)),(1,47,Pattern_Pair data_y data_z)}"

definition data_subset_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "data_subset_clauses={(0,data_subset_nil_schema),(1,data_subset_cons_schema)}"

definition data_subset_system :: "(nat,nat,nat,nat) schema_system" where
  "data_subset_system=add_view_definition data_append_system 47 data_x data_subset_clauses"

lemma data_subset_system_formed [simp]: "schema_system_formed data_subset_system"
  unfolding data_subset_system_def
  by (rule add_recursive_definition_formed[OF data_append_system_formed])
    (auto simp: data_subset_clauses_def data_subset_nil_schema_def data_subset_cons_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma data_subset_definitions [simp]:
  "system_definitions data_subset_system=insert 47 (system_definitions data_append_system)"
  by (simp add: data_subset_system_def)

lemma data_subset_call:
  "schema_call_formed data_subset_system d t \<longleftrightarrow>
    d\<in>system_definitions data_subset_system \<and> term_formed t"
  using added_variable_calls[OF data_append_system_formed
    data_subset_system_formed[unfolded data_subset_system_def] data_append_call]
  by (simp only: data_subset_system_def[symmetric])

lemma data_subset_old_meaning:
  assumes "d\<in>system_definitions data_append_system"
  shows "(d,t)\<in>positive_meaning data_subset_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning data_append_system"
  using added_definition_preserves_old(2)[OF data_append_system_formed
    data_subset_system_formed[unfolded data_subset_system_def], of d t] assms
  by (auto simp: data_subset_system_def)

lemma data_subset_clause [simp]:
  "((47,c),S)\<in>system_clauses data_subset_system \<longleftrightarrow> (c,S)\<in>data_subset_clauses"
proof -
  have owned: "((d,c),S)\<in>system_clauses data_append_system \<Longrightarrow>
    d\<in>system_definitions data_append_system" for d c S
    using data_append_system_formed unfolding schema_system_formed_def by blast
  have absent: "((47,c),S)\<notin>system_clauses data_append_system" by (auto dest: owned)
  show ?thesis using absent by (simp add: data_subset_system_def)
qed

lemma data_subset_bag_meaning:
  assumes "d\<in>{0,1,2,3,4,5,6}"
  shows "(d,t)\<in>positive_meaning data_subset_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning bag_comparison_system"
  using data_subset_old_meaning[of d t] data_append_bag_meaning[OF assms, of t] assms by auto

lemma data_subset_components:
  "(4,t)\<in>positive_meaning data_subset_system \<longleftrightarrow> (\<exists>xs. t=data_list_term xs \<and> data_elements xs)"
  "(5,t)\<in>positive_meaning data_subset_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(46,t)\<in>positive_meaning data_subset_system \<longleftrightarrow> (46,t)\<in>positive_meaning data_append_system"
  using data_subset_bag_meaning[of 4 t] data_subset_bag_meaning[of 5 t]
    data_subset_old_meaning[of 46 t] data_list_exact[of t] by auto

theorem data_subset_sound:
  assumes holds: "(47,t)\<in>positive_meaning data_subset_system"
  shows "\<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
    data_elements xs \<and> data_elements ys \<and> set xs\<subseteq>set ys"
proof -
  let ?Q="\<lambda>t. \<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
    data_elements xs \<and> data_elements ys \<and> set xs\<subseteq>set ys"
  have invariant: "(47::nat)=47 \<longrightarrow> ?Q t"
  proof (rule positive_valuation_induct[OF holds, where property="\<lambda>d t. d=47 \<longrightarrow> ?Q t"])
    fix d c S h
    assume clause: "((d,c),S)\<in>system_clauses data_subset_system"
      and assignment: "\<forall>a\<in>schema_variables S. term_formed (h a)"
      and call: "schema_call_formed data_subset_system d (evaluate_pattern h (schema_conclusion S))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
        (e,evaluate_pattern h p)\<in>positive_meaning data_subset_system \<and>
        (e=47 \<longrightarrow> ?Q (evaluate_pattern h p))"
    show "d=47 \<longrightarrow> ?Q (evaluate_pattern h (schema_conclusion S))"
    proof
      assume "d=47"
      then have alternatives: "S=data_subset_nil_schema \<or> S=data_subset_cons_schema"
        using clause by (auto simp: data_subset_clauses_def)
      then show "?Q (evaluate_pattern h (schema_conclusion S))"
      proof
        assume schema: "S=data_subset_nil_schema"
        obtain ys where parts: "h 0=data_list_term ys" "data_elements ys"
          using support by (auto simp: schema data_subset_nil_schema_def data_subset_components)
        show ?thesis by (intro exI[of _ "[]"] exI[of _ ys])
          (use parts in \<open>simp add: schema data_subset_nil_schema_def\<close>)
      next
        assume schema: "S=data_subset_cons_schema"
        have selected: "(5,Pair_Term (h 0) (Pair_Term (h 2) (h 3)))\<in>positive_meaning bag_comparison_system"
          using support by (auto simp: schema data_subset_cons_schema_def data_subset_components)
        obtain xs ys where tail: "h 1=data_list_term xs" "h 2=data_list_term ys"
          "data_elements xs" "data_elements ys" "set xs\<subseteq>set ys"
          using support[rule_format, of 1 47 "Pattern_Pair data_y data_z"]
          by (auto simp: schema data_subset_cons_schema_def)
        have member: "h 0\<in>set ys"
          using selected selected_data_member_exact[of "h 0" "h 2"] tail(2)
          by (auto simp: data_list_term_injective)
        show ?thesis by (intro exI[of _ "h 0#xs"] exI[of _ ys])
          (use tail member in \<open>auto simp: schema data_subset_cons_schema_def\<close>)
      qed
    qed
  qed
  show ?thesis using invariant by simp
qed

theorem data_subset_complete:
  assumes "data_elements xs" "data_elements ys" "set xs\<subseteq>set ys"
  shows "(47,Pair_Term (data_list_term xs) (data_list_term ys))\<in>positive_meaning data_subset_system"
  using assms
proof (induction xs)
  case Nil
  have child: "(4,data_list_term ys)\<in>positive_meaning data_subset_system"
    using Nil.prems by (auto simp: data_subset_components)
  have result: "(47,evaluate_pattern (\<lambda>_. data_list_term ys) (schema_conclusion data_subset_nil_schema))
    \<in>positive_meaning data_subset_system"
    by (rule ordinary_positive_valuation_step[where c=0])
      (use Nil.prems child in \<open>auto simp: data_subset_clauses_def data_subset_nil_schema_def
        schema_variables_def data_subset_call data_list_term_formed octets_formed_def\<close>)
  show ?case using result by (simp add: data_subset_nil_schema_def)
next
  case (Cons x xs)
  have membership: "selected_data_member x (data_list_term ys)"
    using Cons.prems by (auto simp: selected_data_member_exact)
  then obtain r where selected: "(5,Pair_Term x (Pair_Term (data_list_term ys) r))
    \<in>positive_meaning data_subset_system"
    by (auto simp: data_subset_components)
  have rf: "term_formed r"
    using schema_call_formed_target[OF positive_meaning_formed[OF selected]] by auto
  have tail: "(47,Pair_Term (data_list_term xs) (data_list_term ys))\<in>positive_meaning data_subset_system"
    using Cons by auto
  let ?h="\<lambda>i::nat. if i=0 then x else if i=1 then data_list_term xs
    else if i=2 then data_list_term ys else r"
  have result: "(47,evaluate_pattern ?h (schema_conclusion data_subset_cons_schema))
    \<in>positive_meaning data_subset_system"
    by (rule ordinary_positive_valuation_step[where c=1])
      (use Cons.prems rf selected tail in \<open>auto simp: data_subset_clauses_def data_subset_cons_schema_def
        schema_variables_def data_subset_call data_list_term_formed\<close>)
  show ?case using result by (simp add: data_subset_cons_schema_def)
qed

theorem data_subset_exact:
  "(47,t)\<in>positive_meaning data_subset_system \<longleftrightarrow>
    (\<exists>xs ys. t=Pair_Term (data_list_term xs) (data_list_term ys) \<and>
      data_elements xs \<and> data_elements ys \<and> set xs\<subseteq>set ys)"
  using data_subset_sound data_subset_complete by blast

corollary data_subset_lists:
  "(47,Pair_Term (data_list_term xs) (data_list_term ys))\<in>positive_meaning data_subset_system \<longleftrightarrow>
    data_elements xs \<and> data_elements ys \<and> set xs\<subseteq>set ys"
  by (auto simp: data_subset_exact data_list_term_injective)

text \<open>
  Concatenation preserves both orders and every repeated occurrence. Inclusion
  checks each left element by an actual selection call, then passes the entire
  right collection to the recursive call. This explicit reuse derives set
  inclusion; it does not change the earlier rule that compares every count.
  Both recursions admit every element and the final empty-payload boundary.
  Their exact contracts cover arbitrary terms, and every prior entry keeps its
  original meaning.
\<close>

end
