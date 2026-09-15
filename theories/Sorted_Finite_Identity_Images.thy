theory Sorted_Finite_Identity_Images
  imports "HOL-Library.FSet"
begin

theorem sorted_finite_identity_image:
  fixes encode :: "'a::linorder \<Rightarrow> 'b::linorder"
  assumes each: "\<And>x y. encode x=encode y \<longleftrightarrow> x=y"
    and ordered: "\<And>x y. encode x\<le>encode y \<longleftrightarrow> x\<le>y"
  shows "map encode (sorted_list_of_fset values)=sorted_list_of_fset (fimage encode values)"
proof (rule sorted_distinct_set_unique)
  show "sorted (map encode (sorted_list_of_fset values))"
    by (simp add: sorted_map ordered sorted_list_of_fset.rep_eq)
  show "distinct (map encode (sorted_list_of_fset values))"
    by (simp add: distinct_map inj_on_def each sorted_list_of_fset.rep_eq)
  show "sorted (sorted_list_of_fset (fimage encode values))"
    by (simp add: sorted_list_of_fset.rep_eq)
  show "distinct (sorted_list_of_fset (fimage encode values))"
    by (simp add: sorted_list_of_fset.rep_eq)
  show "set (map encode (sorted_list_of_fset values))=
      set (sorted_list_of_fset (fimage encode values))"
    by (simp add: sorted_list_of_fset.rep_eq fimage.rep_eq)
qed

text \<open>An injective presentation that preserves the whole order preserves
  the exact sorted list of a finite collection. This is an ordered equality,
  including the complete enumeration, rather than only set equality.\<close>

end
