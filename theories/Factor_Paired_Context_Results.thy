theory Factor_Paired_Context_Results
  imports Factor_Related_Lists
begin

section \<open>Two actual callees retain the same context and input\<close>

abbreviation paired_context_results_argument where
  "paired_context_results_argument u b x y \<equiv> Pair_Term u (Pair_Term b (Pair_Term x y))"

abbreviation paired_context_results_pattern where
  "paired_context_results_pattern u b x y \<equiv> Pattern_Pair u (Pattern_Pair b (Pattern_Pair x y))"

definition paired_context_results_schema :: "nat\<Rightarrow>nat\<Rightarrow>(nat,nat,nat) factor_schema" where
  "paired_context_results_schema first second=data_rule
    (paired_context_results_pattern data_x data_y data_z data_w)
    {(0,first,context_relation_pattern data_x data_y data_z),
     (1,second,context_relation_pattern data_x data_y data_w)}"

locale paired_context_results_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry first second :: nat
  assumes family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=paired_context_results_schema first second"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
      term_formed (h 2) \<and> term_formed (h 3) \<and>
      t=paired_context_results_argument (h 0) (h 1) (h 2) (h 3) \<and>
      (first,context_relation_argument (h 0) (h 1) (h 2))\<in>positive_meaning P \<and>
      (second,context_relation_argument (h 0) (h 1) (h 3))\<in>positive_meaning P)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family paired_context_results_schema_def schema_variables_def call)

theorem at_arguments:
  "(entry,paired_context_results_argument u b x y)\<in>positive_meaning P \<longleftrightarrow>
    (first,context_relation_argument u b x)\<in>positive_meaning P \<and>
    (second,context_relation_argument u b y)\<in>positive_meaning P"
proof
  assume "(entry,paired_context_results_argument u b x y)\<in>positive_meaning P"
  then show "(first,context_relation_argument u b x)\<in>positive_meaning P \<and>
    (second,context_relation_argument u b y)\<in>positive_meaning P"
    by (simp only: valuation factor_term.inject) blast
next
  assume reads: "(first,context_relation_argument u b x)\<in>positive_meaning P \<and>
    (second,context_relation_argument u b y)\<in>positive_meaning P"
  have terms: "term_formed u" "term_formed b" "term_formed x" "term_formed y"
    using reads positive_meaning_formed[of first "context_relation_argument u b x" P]
      positive_meaning_formed[of second "context_relation_argument u b y" P]
    by (auto dest: schema_call_formed_target)
  let ?h="(\<lambda>_::nat. u)(1:=b,2:=x,3:=y)"
  show "(entry,paired_context_results_argument u b x y)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ ?h]) (use reads terms in auto)
qed

theorem exact:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>u b x y. t=paired_context_results_argument u b x y \<and>
      (first,context_relation_argument u b x)\<in>positive_meaning P \<and>
      (second,context_relation_argument u b y)\<in>positive_meaning P)"
  using valuation at_arguments by blast


theorem related_lists_exact:
  assumes first_list: "\<And>t. (first,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>u rs xs. t=context_relation_argument u (data_list_term rs) (data_list_term xs) \<and>
        term_formed u \<and> list_all2 (R u) rs xs)"
    and second_list: "\<And>t. (second,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>u rs ys. t=context_relation_argument u (data_list_term rs) (data_list_term ys) \<and>
        term_formed u \<and> list_all2 (S u) rs ys)"
  shows "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>u rs xs ys. t=paired_context_results_argument u
      (data_list_term rs) (data_list_term xs) (data_list_term ys) \<and>
      term_formed u \<and> list_all2 (R u) rs xs \<and> list_all2 (S u) rs ys)"
proof
  assume admitted: "(entry,t)\<in>positive_meaning P"
  obtain u b x y where body: "t=paired_context_results_argument u b x y"
    and first_call: "(first,context_relation_argument u b x)\<in>positive_meaning P"
    and second_call: "(second,context_relation_argument u b y)\<in>positive_meaning P"
    using admitted by (simp only: exact) blast
  obtain rs xs where left: "b=data_list_term rs" "x=data_list_term xs"
    "term_formed u" "list_all2 (R u) rs xs"
    using first_call by (auto simp only: first_list factor_term.inject)
  obtain ts ys where right: "b=data_list_term ts" "y=data_list_term ys"
    "list_all2 (S u) ts ys"
    using second_call by (auto simp only: second_list factor_term.inject)
  have same: "ts=rs" using left(1) right(1) by (simp only: data_list_term_injective)
  show "\<exists>u rs xs ys. t=paired_context_results_argument u
      (data_list_term rs) (data_list_term xs) (data_list_term ys) \<and>
      term_formed u \<and> list_all2 (R u) rs xs \<and> list_all2 (S u) rs ys"
    by (rule exI[of _ u], rule exI[of _ rs], rule exI[of _ xs], rule exI[of _ ys])
      (use body left right same in simp)
next
  assume "\<exists>u rs xs ys. t=paired_context_results_argument u
      (data_list_term rs) (data_list_term xs) (data_list_term ys) \<and>
      term_formed u \<and> list_all2 (R u) rs xs \<and> list_all2 (S u) rs ys"
  then obtain u rs xs ys where fields:
    "t=paired_context_results_argument u (data_list_term rs) (data_list_term xs) (data_list_term ys)"
    "term_formed u" "list_all2 (R u) rs xs" "list_all2 (S u) rs ys" by blast
  have first_call: "(first,context_relation_argument u (data_list_term rs) (data_list_term xs))\<in>positive_meaning P"
    by (simp only: first_list; rule exI[of _ u], rule exI[of _ rs], rule exI[of _ xs])
      (use fields(2,3) in simp)
  have second_call: "(second,context_relation_argument u (data_list_term rs) (data_list_term ys))\<in>positive_meaning P"
    by (simp only: second_list; rule exI[of _ u], rule exI[of _ rs], rule exI[of _ ys])
      (use fields(2,4) in simp)
  show "(entry,t)\<in>positive_meaning P"
    using first_call second_call by (simp only: fields(1) at_arguments)
qed

end

text \<open>
  The complete source clause and entry interface are the local prerequisites.
  The callees may coincide or participate in positive cycles. Their actual
  judgments establish every input and output's formation. Neither callee's
  meaning is inferred from its index, and the two premise occurrences remain
  separate even when they invoke the same call.
\<close>

end
