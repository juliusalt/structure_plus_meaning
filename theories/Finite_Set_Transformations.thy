theory Finite_Set_Transformations
  imports "HOL-Library.FSet"
begin

lemma finite_image_restriction:
  assumes "B |\<subseteq>| fimage f A"
  shows "fimage f (ffilter (\<lambda>x. f x |\<in>| B) A)=B"
  by (rule fset_inject[THEN iffD1])
    (use assms in \<open>auto simp: less_eq_fset.rep_eq fimage.rep_eq\<close>)

lemma finite_difference_empty:
  "A |-| B={||} \<longleftrightarrow> A |\<subseteq>| B"
  by (auto simp: fset_eq_iff less_eq_fset.rep_eq)

lemma finite_differences_empty:
  "A |-| B={||} \<and> B |-| A={||} \<longleftrightarrow> A=B"
  by (auto simp: finite_difference_empty intro: order_antisym)

end
