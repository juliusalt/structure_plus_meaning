theory Factor_Data_Product_Equations
  imports Factor_Data_Product_Clauses
begin

section \<open>The component contracts retain their complete data boundaries\<close>

lemma data_product_data_meaning:
  assumes "d\<in>{2,4}"
  shows "(d,t)\<in>positive_meaning data_product_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning data_append_system"
proof -
  have base: "d\<in>system_definitions data_flatten_base_system"
    using data_flatten_base_data_roots assms by blast
  have member: "d\<in>system_definitions data_flatten_system" using base by simp
  have original: "(d,t)\<in>positive_meaning data_flatten_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning data_append_system"
    using data_flatten_group.old_meaning[OF base, of t]
      rooted_system_meaning_at[OF data_append_system_formed base[unfolded data_flatten_base_system_def], of t]
    by (simp only: data_flatten_system_def data_flatten_base_system_def)
  show ?thesis using data_product_base_meaning[of d t] assms
    data_product_flatten_meaning[OF member, of t] original by auto
qed

lemma data_product_components:
  "(2,t)\<in>positive_meaning data_product_system \<longleftrightarrow> data_term_boundary t"
  "(4,t)\<in>positive_meaning data_product_system \<longleftrightarrow> (\<exists>xs. t=data_list_term xs \<and> data_elements xs)"
  "(218,t)\<in>positive_meaning data_product_system \<longleftrightarrow> (218,t)\<in>positive_meaning data_flatten_system"
  "(219,t)\<in>positive_meaning data_product_system \<longleftrightarrow> (219,t)\<in>positive_meaning data_set_comparison_system"
  using data_product_data_meaning[of 2 t] data_product_data_meaning[of 4 t] data_append_components[of t]
    data_product_base_meaning[of 218 t] data_product_base_meaning[of 219 t]
    data_product_flatten_meaning[of 218 t] data_product_set_meaning[of 219 t] by auto

interpretation data_product_pair: paired_terms_profile data_product_system 318 2 2
  by (unfold_locales) (auto simp: data_product_clause data_product_clause_family_def data_product_call)

interpretation data_product_inner: related_list_profile data_product_system 318 319
  by (unfold_locales) (auto simp: data_product_clause data_product_clause_family_def data_product_call)

interpretation data_product_point: admitted_context_profile data_product_system 320 2 319
  by (unfold_locales) (auto simp: data_product_clause data_product_clause_family_def data_product_call)

interpretation data_product_transpose: transposed_context_profile data_product_system 321 320
  by (unfold_locales) (auto simp: data_product_clause data_product_clause_family_def data_product_call)

interpretation data_product_outer: related_list_profile data_product_system 321 322
  by (unfold_locales) (auto simp: data_product_clause data_product_clause_family_def data_product_call)

interpretation data_product_flat: context_result_comparison_profile data_product_system 323 322 218
  by (unfold_locales) (auto simp: data_product_clause data_product_clause_family_def data_product_call)

interpretation data_product_admitted: admitted_context_profile data_product_system 324 4 323
  by (unfold_locales) (auto simp: data_product_clause data_product_clause_family_def data_product_call)

interpretation data_product_comparison: context_result_comparison_profile data_product_system 325 324 219
  by (unfold_locales) (auto simp: data_product_clause data_product_clause_family_def data_product_call)

lemma data_product_point_exact:
  "(320,context_relation_argument a p q)\<in>positive_meaning data_product_system \<longleftrightarrow>
    data_term_boundary a \<and> (\<exists>ys. data_elements ys \<and> p=data_list_term ys \<and>
      q=data_list_term (map (Pair_Term a) ys))"
proof (cases "data_term_boundary a")
  case True
  have formed: "term_formed a" using True by blast
  have element: "data_product_inner.related a x y \<longleftrightarrow> data_term_boundary x \<and> y=Pair_Term a x" for x y
    using True by (simp only: data_product_pair.at_input data_product_components; blast)
  have mapped: "(319,context_relation_argument a p q)\<in>positive_meaning data_product_system \<longleftrightarrow>
      (\<exists>ys. data_elements ys \<and> p=data_list_term ys \<and> q=data_list_term (map (Pair_Term a) ys))"
    by (rule data_product_inner.partial_function_exact[where D=data_term_boundary and f="Pair_Term a", OF formed element])
  show ?thesis by (simp only: data_product_point.at_input data_product_components mapped)
next
  case False
  show ?thesis using False by (simp only: data_product_point.at_input data_product_components; blast)
qed

lemma data_product_point_lists:
  "(321,context_relation_argument (data_list_term ys) a q)\<in>positive_meaning data_product_system \<longleftrightarrow>
    data_term_boundary a \<and> data_elements ys \<and> q=data_list_term (map (Pair_Term a) ys)"
  by (simp only: data_product_transpose.at_input data_product_point_exact data_list_term_injective) auto

lemma data_product_outer_exact:
  assumes data: "data_elements ys"
  shows "(322,context_relation_argument (data_list_term ys) p q)\<in>positive_meaning data_product_system \<longleftrightarrow>
    (\<exists>xs. data_elements xs \<and> p=data_list_term xs \<and>
      q=data_list_term (map (\<lambda>x. data_list_term (map (Pair_Term x) ys)) xs))"
proof -
  have formed: "term_formed (data_list_term ys)" using data by (auto simp: data_list_term_formed)
  have element: "data_product_outer.related (data_list_term ys) x q \<longleftrightarrow>
      data_term_boundary x \<and> q=data_list_term (map (Pair_Term x) ys)" for x q
    using data by (simp only: data_product_point_lists; blast)
  show ?thesis by (rule data_product_outer.partial_function_exact[
    where D=data_term_boundary and f="\<lambda>x. data_list_term (map (Pair_Term x) ys)", OF formed element])
qed

section \<open>The private computation preserves both input orders and repetitions\<close>

abbreviation data_product_list where
  "data_product_list xs ys \<equiv> concat (map (\<lambda>x. map (Pair_Term x) ys) xs)"

lemma data_product_list_data:
  assumes "data_elements xs" "data_elements ys"
  shows "data_elements (data_product_list xs ys)"
  using assms by auto

lemma data_product_flat_lists:
  assumes first: "data_elements xs" and second: "data_elements ys"
  shows "(323,context_relation_argument (data_list_term ys) (data_list_term xs) q)
    \<in>positive_meaning data_product_system \<longleftrightarrow> q=data_list_term (data_product_list xs ys)"
proof -
  have formed: "term_formed (data_list_term ys)" using second by (simp add: data_list_term_formed)
  have element: "(321,context_relation_argument (data_list_term ys) (id x) v)\<in>positive_meaning data_product_system
      \<longleftrightarrow> v=data_list_term (map (Pair_Term x) ys)" if "x\<in>set xs" for x v
    using first second that by (simp only: id_apply data_product_point_lists; blast)
  have contributions: "data_elements (map (Pair_Term x) ys)" if "x\<in>set xs" for x
    using first second that by auto
  have flatten: "(218,Pair_Term (data_list_term (map data_list_term xss)) v)\<in>positive_meaning data_product_system
      \<longleftrightarrow> (\<forall>ys\<in>set xss. data_elements ys) \<and> v=data_list_term (concat xss)" for xss v
    by (simp only: data_product_components data_flatten_at_lists)
  show ?thesis using data_product_outer.flattened_output[where a="data_list_term ys" and h=id
    and xs=xs and g="\<lambda>x. map (Pair_Term x) ys" and flatten_site=218 and q=q,
    OF formed element contributions flatten]
    by (simp add: data_product_flat.at_input)
qed

lemma data_product_ordered_lists:
  "(324,context_relation_argument (data_list_term ys) (data_list_term xs) q)\<in>positive_meaning data_product_system
    \<longleftrightarrow> data_elements xs \<and> data_elements ys \<and> q=data_list_term (data_product_list xs ys)"
proof
  assume run: "(324,context_relation_argument (data_list_term ys) (data_list_term xs) q)\<in>positive_meaning data_product_system"
  have second: "data_elements ys" using run
    by (auto simp only: data_product_admitted.at_input data_product_components data_list_term_injective)
  have first: "data_elements xs" using run
    by (auto simp only: data_product_admitted.at_input data_product_flat.at_input
      data_product_outer_exact[OF second] data_list_term_injective)
  show "data_elements xs \<and> data_elements ys \<and> q=data_list_term (data_product_list xs ys)"
    using run first second by (simp only: data_product_admitted.at_input data_product_flat_lists[OF first second]; blast)
next
  assume "data_elements xs \<and> data_elements ys \<and> q=data_list_term (data_product_list xs ys)"
  then show "(324,context_relation_argument (data_list_term ys) (data_list_term xs) q)\<in>positive_meaning data_product_system"
    by (simp only: data_product_admitted.at_input data_product_components data_list_term_injective)
      (use data_product_flat_lists in blast)
qed

theorem data_product_ordered_exact:
  "(324,t)\<in>positive_meaning data_product_system \<longleftrightarrow>
    (\<exists>xs ys. data_elements xs \<and> data_elements ys \<and>
      t=context_relation_argument (data_list_term ys) (data_list_term xs) (data_list_term (data_product_list xs ys)))"
proof
  assume run: "(324,t)\<in>positive_meaning data_product_system"
  obtain ys p q w where parts: "data_elements ys"
    "t=context_relation_argument (data_list_term ys) p q"
    "(322,context_relation_argument (data_list_term ys) p w)\<in>positive_meaning data_product_system"
    using run by (auto simp only: data_product_admitted.exact data_product_components
      data_product_flat.exact factor_term.inject)
  obtain xs where first: "data_elements xs" "p=data_list_term xs"
    using parts(3) by (simp only: data_product_outer_exact[OF parts(1)]; blast)
  show "\<exists>xs ys. data_elements xs \<and> data_elements ys \<and>
      t=context_relation_argument (data_list_term ys) (data_list_term xs) (data_list_term (data_product_list xs ys))"
    using run parts(1,2) first by (simp only: first(2) parts(2) data_product_ordered_lists; blast)
next
  assume "\<exists>xs ys. data_elements xs \<and> data_elements ys \<and>
      t=context_relation_argument (data_list_term ys) (data_list_term xs) (data_list_term (data_product_list xs ys))"
  then show "(324,t)\<in>positive_meaning data_product_system" by (auto simp only: data_product_ordered_lists)
qed

section \<open>Public results cover exactly the complete Cartesian set\<close>

lemma data_product_list_set:
  "set (data_product_list xs ys)={Pair_Term x y | x y. x\<in>set xs \<and> y\<in>set ys}"
  by auto

lemma data_product_lists:
  "(325,context_relation_argument (data_list_term ys) (data_list_term xs) (data_list_term zs))
    \<in>positive_meaning data_product_system \<longleftrightarrow>
    data_elements xs \<and> data_elements ys \<and> data_elements zs \<and>
      set zs={Pair_Term x y | x y. x\<in>set xs \<and> y\<in>set ys}"
proof -
  let ?w="data_list_term (data_product_list xs ys)"
  have computed: "(325,context_relation_argument (data_list_term ys) (data_list_term xs) (data_list_term zs))
      \<in>positive_meaning data_product_system \<longleftrightarrow>
      data_elements xs \<and> data_elements ys \<and> (219,Pair_Term ?w (data_list_term zs))\<in>positive_meaning data_product_system"
    by (simp only: data_product_comparison.at_input data_product_ordered_lists)
      (simp only: conj_assoc; simp)
  have data: "data_elements (data_product_list xs ys)" if "data_elements xs" "data_elements ys"
    by (rule data_product_list_data[OF that])
  have compared: "(325,context_relation_argument (data_list_term ys) (data_list_term xs) (data_list_term zs))
      \<in>positive_meaning data_product_system \<longleftrightarrow>
      data_elements xs \<and> data_elements ys \<and> data_elements zs \<and> set (data_product_list xs ys)=set zs"
    by (simp only: computed data_product_components data_set_comparison_lists)
      (use data in blast)
  show ?thesis by (simp only: compared data_product_list_set eq_commute)
qed

theorem data_product_exact:
  "(325,t)\<in>positive_meaning data_product_system \<longleftrightarrow>
    (\<exists>xs ys zs. data_elements xs \<and> data_elements ys \<and> data_elements zs \<and>
      t=context_relation_argument (data_list_term ys) (data_list_term xs) (data_list_term zs) \<and>
      set zs={Pair_Term x y | x y. x\<in>set xs \<and> y\<in>set ys})"
proof
  assume run: "(325,t)\<in>positive_meaning data_product_system"
  obtain a p q w where parts: "t=context_relation_argument a p q"
    "(324,context_relation_argument a p w)\<in>positive_meaning data_product_system"
    "(219,Pair_Term w q)\<in>positive_meaning data_product_system"
    using run by (simp only: data_product_comparison.exact) blast
  obtain xs ys where inputs: "data_elements xs" "data_elements ys"
    "a=data_list_term ys" "p=data_list_term xs" "w=data_list_term (data_product_list xs ys)"
    using parts(2) by (auto simp only: data_product_ordered_exact factor_term.inject)
  obtain zs where output_site: "q=data_list_term zs" "data_elements zs"
    "set (data_product_list xs ys)=set zs"
    using parts(3) by (auto simp only: inputs(5) data_product_components data_set_comparison_exact
      factor_term.inject data_list_term_injective)
  have same: "set zs={Pair_Term x y | x y. x\<in>set xs \<and> y\<in>set ys}"
    using sym[OF output_site(3)] by (simp only: data_product_list_set)
  have shape: "t=context_relation_argument (data_list_term ys) (data_list_term xs) (data_list_term zs)"
    using parts(1) by (simp only: inputs(3,4) output_site(1))
  show "\<exists>xs ys zs. data_elements xs \<and> data_elements ys \<and> data_elements zs \<and>
      t=context_relation_argument (data_list_term ys) (data_list_term xs) (data_list_term zs) \<and>
      set zs={Pair_Term x y | x y. x\<in>set xs \<and> y\<in>set ys}"
    by (rule exI[of _ xs], rule exI[of _ ys], rule exI[of _ zs],
      rule conjI[OF inputs(1)], rule conjI[OF inputs(2)], rule conjI[OF output_site(2)],
      rule conjI[OF shape same])

next
  assume "\<exists>xs ys zs. data_elements xs \<and> data_elements ys \<and> data_elements zs \<and>
      t=context_relation_argument (data_list_term ys) (data_list_term xs) (data_list_term zs) \<and>
      set zs={Pair_Term x y | x y. x\<in>set xs \<and> y\<in>set ys}"
  then obtain xs ys zs where parts: "data_elements xs" "data_elements ys" "data_elements zs"
    "t=context_relation_argument (data_list_term ys) (data_list_term xs) (data_list_term zs)"
    "set zs={Pair_Term x y | x y. x\<in>set xs \<and> y\<in>set ys}" by blast
  have admitted: "data_elements xs \<and> data_elements ys \<and> data_elements zs \<and>
      set zs={Pair_Term x y | x y. x\<in>set xs \<and> y\<in>set ys}"
    by (rule conjI[OF parts(1)], rule conjI[OF parts(2)], rule conjI[OF parts(3,5)])
  show "(325,t)\<in>positive_meaning data_product_system"
    unfolding parts(4) by (rule iffD2[OF data_product_lists admitted])
qed

text \<open>
  The inner map holds one first operand fixed. The transposed outer map
  visits every first operand while keeping the second list available.
  Flattening consumes all these contributions. Its private witness retains
  both input orders and every repeated occurrence. The explicit admission
  calls retain the whole data boundary when either list is empty.

  The public comparison admits every presentation of exactly the set of
  constructed pairs. Missing pairs and foreign pairs fail. When the same
  candidate set is supplied in both positions, self pairs and both directions
  of every cross pair remain present, including pairs whose later loss is empty.
\<close>

end
