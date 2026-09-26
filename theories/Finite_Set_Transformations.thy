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

text \<open>
  A filter commutes with an image, reading the image's values; the second components of a set keyed by a function
  and filtered are the set filtered at its keys.
\<close>

lemma fimage_ffilter_value: "ffilter Q (fimage f X) = fimage f (ffilter (\<lambda>x. Q (f x)) X)"
  by (auto simp: fset_eq_iff fimage.rep_eq ffilter.rep_eq)

lemma fimage_snd_keyed: "fimage snd (ffilter F (fimage (\<lambda>g. (f g,g)) C)) = ffilter (\<lambda>g. F (f g,g)) C"
  by (force simp: fset_eq_iff fimage.rep_eq ffilter.rep_eq)

end
