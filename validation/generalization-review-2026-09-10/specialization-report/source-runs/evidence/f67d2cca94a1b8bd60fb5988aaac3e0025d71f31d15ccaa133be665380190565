theory Factor_Observation_Profiles
  imports Factor_Observation_Equations Finite_Investigation
begin

section \<open>The unchanged base gives exact complete data operations\<close>

lemma observation_components:
  "(2,t)\<in>positive_meaning observation_system \<longleftrightarrow> term_formed t \<and> self_contained_term t"
  "(3,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>x y. t=Pair_Term x y \<and> data_elements [x,y] \<and> x\<noteq>y)"
  "(4,t)\<in>positive_meaning observation_system \<longleftrightarrow> (\<exists>xs. t=data_list_term xs \<and> data_elements xs)"
  "(5,t)\<in>positive_meaning observation_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(132,t)\<in>positive_meaning observation_system \<longleftrightarrow> (132,t)\<in>positive_meaning data_absence_system"
  using observation_base_meaning[of 2 t] observation_base_meaning[of 3 t]
    observation_base_meaning[of 4 t] observation_base_meaning[of 5 t] observation_base_meaning[of 132 t]
    data_absence_old_meaning[of 2 t] data_absence_old_meaning[of 3 t]
    data_absence_old_meaning[of 4 t] data_absence_old_meaning[of 5 t]
    bag_comparison_recognizes[of t] data_absence_comparison[of t] data_comparison_exact[of t]
    data_list_exact[of t]
  by auto

lemma observation_member_exact:
  "(303,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>xs x. t=Pair_Term (data_list_term xs) x \<and> data_elements xs \<and>
      term_formed x \<and> self_contained_term x \<and> x\<in>set xs)"
proof -
  have removal: "(\<exists>r. term_formed r \<and> (5,Pair_Term x (Pair_Term p r))\<in>positive_meaning observation_system)
      \<longleftrightarrow> selected_data_member x p" for x p
    using positive_meaning_formed schema_call_formed_target
    by (auto simp: observation_components(4); fastforce)
  have raw: "(303,t)\<in>positive_meaning observation_system \<longleftrightarrow>
      (\<exists>p x. term_formed p \<and> term_formed x \<and> t=Pair_Term p x \<and> selected_data_member x p)"
    using removal by (simp only: observation_member_calls) blast
  show ?thesis
    by (auto simp: raw selected_data_member_exact data_list_term_formed data_list_term_self_contained; blast)
qed

lemma observation_absent_exact:
  "(304,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>xs x. t=Pair_Term (data_list_term xs) x \<and> data_elements xs \<and>
      term_formed x \<and> self_contained_term x \<and> x\<notin>set xs)"
  by (auto simp: observation_absent_calls observation_components data_absence_exact
    data_list_term_formed data_list_term_self_contained; blast)

lemma observation_context_exact:
  "(295,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>xs c. t=Pair_Term (data_list_term xs) c \<and> data_elements xs \<and>
      term_formed c \<and> self_contained_term c)"
  by (auto simp: observation_context_calls observation_components data_list_term_formed data_list_term_self_contained)

lemma observation_keep_exact:
  "(296,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>xs c f w. t=Pair_Term (Pair_Term (data_list_term xs) c) (context_relation_argument f c w) \<and>
      data_elements xs \<and> data_elements [f,c,w] \<and> f\<in>set xs)"
  by (auto simp: observation_keep_calls observation_member_exact observation_components
    data_list_term_formed data_list_term_self_contained)

lemma observation_omit_exact:
  "(297,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>xs c f d w. t=Pair_Term (Pair_Term (data_list_term xs) c) (context_relation_argument f d w) \<and>
      data_elements xs \<and> data_elements [c,f,d,w] \<and> (d\<noteq>c \<or> f\<notin>set xs))"
  by (auto simp: observation_omit_calls observation_absent_exact observation_components
    data_list_term_formed data_list_term_self_contained; blast)

lemma observation_pair_exact:
  "(299,t)\<in>positive_meaning observation_system \<longleftrightarrow>
    (\<exists>p f c w. t=context_relation_argument p (context_relation_argument f c w) (Pair_Term f w) \<and>
      term_formed p \<and> data_elements [f,c,w])"
  by (auto simp: observation_pair_calls observation_components)

section \<open>Every source row is checked before the chosen rows are projected\<close>

abbreviation observation_context_admitted :: "factor_term \<Rightarrow> bool" where
  "observation_context_admitted p \<equiv> \<exists>xs c. p=Pair_Term (data_list_term xs) c \<and>
    data_elements xs \<and> term_formed c \<and> self_contained_term c"

abbreviation observation_row_admitted :: "factor_term \<Rightarrow> bool" where
  "observation_row_admitted row \<equiv> \<exists>f c w. row=context_relation_argument f c w \<and> data_elements [f,c,w]"

abbreviation observation_row_selected :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "observation_row_selected p row \<equiv> \<exists>xs c f w.
    p=Pair_Term (data_list_term xs) c \<and> row=context_relation_argument f c w \<and> f\<in>set xs"

interpretation observation_filter: context_filter_profile observation_system 295 296 297 298
  observation_context_admitted "\<lambda>p row. observation_row_admitted row" observation_row_selected
  by (rule context_filter_profile.intro[OF observation_system_formed])
    (auto simp: observation_clause observation_clause_family_def observation_call observation_context_exact
      observation_keep_exact observation_omit_exact data_list_term_formed data_list_term_self_contained
      data_list_term_injective)

interpretation observation_pairs: related_list_profile observation_system 299 300
  by (rule related_list_profile.intro[OF observation_system_formed])
    (auto simp: observation_clause observation_clause_family_def observation_call)

interpretation observation_difference: context_filter_profile observation_system 4 304 303 305
  "\<lambda>p. \<exists>xs. p=data_list_term xs \<and> data_elements xs"
  "\<lambda>p x. term_formed x \<and> self_contained_term x"
  "\<lambda>p x. \<exists>xs. p=data_list_term xs \<and> x\<notin>set xs"
  by (rule context_filter_profile.intro[OF observation_system_formed])
    (auto simp: observation_clause observation_clause_family_def observation_call observation_components
      observation_member_exact observation_absent_exact data_list_term_formed data_list_term_self_contained
      data_list_term_injective)

section \<open>Ordered witnesses implement the existing finite profiles and losses\<close>

definition observation_profile_list where
  "observation_profile_list F rows c=
    map (\<lambda>(f,d,w). (f,w)) (filter (\<lambda>(f,d,w). f\<in>set F \<and> d=c) rows)"

definition observation_losses_list where
  "observation_losses_list F rows c d=
    filter (\<lambda>x. x\<notin>set (observation_profile_list F rows d)) (observation_profile_list F rows c)"

lemma observation_profile_list_fset:
  "fset_of_list (observation_profile_list F rows c)=
    finite_candidate_profile (fset_of_list F) (fset_of_list rows) c"
  by (rule fset_inject[THEN iffD1])
    (auto simp: observation_profile_list_def finite_candidate_profile_def
      fset_of_list.rep_eq fimage.rep_eq split: prod.splits)

lemma observation_losses_list_fset:
  "fset_of_list (observation_losses_list F rows c d)=
    finite_candidate_losses (fset_of_list F) (fset_of_list rows) c d"
  by (rule fset_inject[THEN iffD1])
    (simp add: observation_losses_list_def finite_candidate_losses_def
      observation_profile_list_fset[symmetric] fset_of_list.rep_eq)

abbreviation observation_row_term :: "(factor_term\<times>factor_term\<times>factor_term) \<Rightarrow> factor_term" where
  "observation_row_term row \<equiv> case row of (f,c,w) \<Rightarrow> context_relation_argument f c w"

abbreviation observation_value_term :: "(factor_term\<times>factor_term) \<Rightarrow> factor_term" where
  "observation_value_term row \<equiv> case row of (f,w) \<Rightarrow> Pair_Term f w"

abbreviation observation_rows_data :: "(factor_term\<times>factor_term\<times>factor_term) list \<Rightarrow> bool" where
  "observation_rows_data rows \<equiv> \<forall>(f,c,w)\<in>set rows. data_elements [f,c,w]"

lemma observation_encoded_filter:
  "(298,context_relation_argument (Pair_Term (data_list_term F) c)
    (data_list_term (map observation_row_term rows)) q)\<in>positive_meaning observation_system \<longleftrightarrow>
    data_elements F \<and> term_formed c \<and> self_contained_term c \<and> observation_rows_data rows \<and>
    q=data_list_term (map observation_row_term (filter (\<lambda>(f,d,w). f\<in>set F \<and> d=c) rows))"
proof -
  have selected: "filter (observation_row_selected (Pair_Term (data_list_term F) c))
      (map observation_row_term rows)=
      map observation_row_term (filter (\<lambda>(f,d,w). f\<in>set F \<and> d=c) rows)"
    by (induction rows) (auto simp: data_list_term_injective split: prod.splits)
  show ?thesis
    by (simp only: observation_filter.at_input selected) (auto simp: data_list_term_injective split: prod.splits)
qed

lemma observation_encoded_pairs:
  assumes "term_formed p"
  shows "(300,context_relation_argument p (data_list_term (map observation_row_term rows)) q)
    \<in>positive_meaning observation_system \<longleftrightarrow>
    observation_rows_data rows \<and> q=data_list_term (map (\<lambda>(f,d,w). Pair_Term f w) rows)"
  by (rule observation_pairs.encoded_partial_input[OF assms])
    (use assms in \<open>auto simp: observation_pair_exact split: prod.splits\<close>)

lemma observation_encoded_profile:
  "(301,context_relation_argument (Pair_Term (data_list_term F) c)
    (data_list_term (map observation_row_term rows)) q)\<in>positive_meaning observation_system \<longleftrightarrow>
    data_elements F \<and> term_formed c \<and> self_contained_term c \<and> observation_rows_data rows \<and>
    q=data_list_term (map observation_value_term (observation_profile_list F rows c))"
proof -
  have row_formed: "term_formed (data_list_term (map observation_row_term xs))"
    if "observation_rows_data xs" for xs
    using that by (auto simp: data_list_term_formed split: prod.splits)
  have output_formed: "term_formed (data_list_term (map (\<lambda>(f,d,w). Pair_Term f w) xs))"
    if "observation_rows_data xs" for xs
    using that by (auto simp: data_list_term_formed split: prod.splits)
  let ?p="Pair_Term (data_list_term F) c"
  let ?input="data_list_term (map observation_row_term rows)"
  have raw: "(301,context_relation_argument ?p ?input q)\<in>positive_meaning observation_system \<longleftrightarrow>
      term_formed ?p \<and> term_formed ?input \<and> term_formed q \<and>
      (\<exists>mid. term_formed mid \<and>
        (298,context_relation_argument ?p ?input mid)\<in>positive_meaning observation_system \<and>
        (300,context_relation_argument ?p mid q)\<in>positive_meaning observation_system)"
    by (auto simp only: observation_profile_calls factor_term.inject)
  have mapped: "map observation_value_term (map (\<lambda>(f,d,w). (f,w)) xs)=
      map (\<lambda>(f,d,w). Pair_Term f w) xs" for xs
    by (induction xs) (auto split: prod.splits)
  show ?thesis
    by (simp only: raw observation_encoded_filter observation_profile_list_def mapped)
      (auto simp: observation_encoded_pairs
        data_list_term_formed row_formed output_formed split: prod.splits)
qed

lemma observation_encoded_difference:
  "(305,context_relation_argument (data_list_term ys) (data_list_term xs) q)
    \<in>positive_meaning observation_system \<longleftrightarrow>
    data_elements ys \<and> data_elements xs \<and> q=data_list_term (filter (\<lambda>x. x\<notin>set ys) xs)"
  by (auto simp: observation_difference.at_input data_list_term_injective)

lemma observation_profile_data:
  assumes "observation_rows_data rows"
  shows "data_elements (map observation_value_term (observation_profile_list F rows c))"
  using assms by (auto simp: observation_profile_list_def split: prod.splits)

lemma observation_encoded_losses:
  "(306,context_relation_argument (Pair_Term (data_list_term F) (Pair_Term c d))
    (data_list_term (map observation_row_term rows)) q)\<in>positive_meaning observation_system \<longleftrightarrow>
    data_elements F \<and> data_elements [c,d] \<and> observation_rows_data rows \<and>
    q=data_list_term (map observation_value_term (observation_losses_list F rows c d))"
proof -
  have difference: "filter (\<lambda>x. x\<notin>set (map observation_value_term ys)) (map observation_value_term xs)=
      map observation_value_term (filter (\<lambda>x. x\<notin>set ys) xs)" for xs ys
    by (induction xs) (auto split: prod.splits)
  have row_formed: "term_formed (data_list_term (map observation_row_term rows))"
    if "observation_rows_data rows"
    using that by (auto simp: data_list_term_formed split: prod.splits)
  let ?a="Pair_Term (data_list_term F) (Pair_Term c d)"
  let ?input="data_list_term (map observation_row_term rows)"
  have raw: "(306,context_relation_argument ?a ?input q)\<in>positive_meaning observation_system \<longleftrightarrow>
      term_formed (data_list_term F) \<and> term_formed c \<and> term_formed d \<and> term_formed ?input \<and> term_formed q \<and>
      (\<exists>l r. term_formed l \<and> term_formed r \<and>
        (301,context_relation_argument (Pair_Term (data_list_term F) c) ?input l)\<in>positive_meaning observation_system \<and>
        (301,context_relation_argument (Pair_Term (data_list_term F) d) ?input r)\<in>positive_meaning observation_system \<and>
        (305,context_relation_argument r l q)\<in>positive_meaning observation_system)"
    apply (simp only: observation_losses_calls factor_term.inject)
    apply (rule iffI)
     apply (elim exE)
     subgoal for v0 v1 v2 v3 v4 v5 v6
       by (elim conjE; hypsubst)
         (intro conjI; (assumption | (rule exI[of _ v5], rule exI[of _ v6], blast)))
    apply (elim conjE exE)
    subgoal for l r
      by (rule exI[of _ "data_list_term F"], rule exI[of _ c], rule exI[of _ d],
        rule exI[of _ ?input], rule exI[of _ q], rule exI[of _ l], rule exI[of _ r]) auto
    done
  have data: "data_elements (map observation_value_term (observation_profile_list F rows c))"
    "data_elements (map observation_value_term (observation_profile_list F rows d))"
    if "observation_rows_data rows"
    by (rule observation_profile_data[OF that])+
  show ?thesis
  proof (cases "data_elements F \<and> data_elements [c,d] \<and> observation_rows_data rows")
    case False
    then show ?thesis by (simp only: raw observation_encoded_profile) auto
  next
    case True
    let ?left="data_list_term (map observation_value_term (observation_profile_list F rows c))"
    let ?right="data_list_term (map observation_value_term (observation_profile_list F rows d))"
    let ?out="data_list_term (map observation_value_term (observation_losses_list F rows c d))"
    have left: "(301,context_relation_argument (Pair_Term (data_list_term F) c) ?input l)
        \<in>positive_meaning observation_system \<longleftrightarrow> l=?left" for l
      using True by (simp only: observation_encoded_profile) auto
    have right: "(301,context_relation_argument (Pair_Term (data_list_term F) d) ?input r)
        \<in>positive_meaning observation_system \<longleftrightarrow> r=?right" for r
      using True by (simp only: observation_encoded_profile) auto
    have rows: "observation_rows_data rows" using True by blast
    have difference_call: "(305,context_relation_argument ?right ?left q)
        \<in>positive_meaning observation_system \<longleftrightarrow> q=?out" for q
      using data[OF rows]
      by (simp only: observation_encoded_difference observation_losses_list_def difference) blast
    have formed: "term_formed (data_list_term F)" "term_formed c" "term_formed d"
      "term_formed ?input" "term_formed ?left" "term_formed ?right" "term_formed ?out"
      using True data[OF rows] row_formed[OF rows]
      by (auto simp: data_list_term_formed observation_losses_list_def)
    show ?thesis using True formed
      apply (auto simp only: raw left right difference_call)
      subgoal
        by (intro exI[of _ ?left] exI[of _ ?right]) (use formed in \<open>simp add: difference_call\<close>)
      done
  qed
qed

text \<open>
  The ordered intermediate retains every selected occurrence in input order.
  Its finite set is exactly the pre-existing candidate profile; the same
  construction followed by explicit absence gives the pre-existing losses.
  Both profiles in a loss computation share the actual facet list and table.

  Each input row must contain complete data, including a row that is omitted.
  The empty table still requires the complete context. These are consequences
  of the actual native calls, not assumptions used to ignore rejected inputs.
  An ordered witness alone does not admit every output presentation of a set.
\<close>

end
