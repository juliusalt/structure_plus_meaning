theory Finite_Set_Composition
  imports "HOL-Library.FSet"
begin

section \<open>Exact members of finite compositions\<close>

lemma ffUnion_membership:
  "x |\<in>| ffUnion A \<longleftrightarrow> (\<exists>B. B |\<in>| A \<and> x |\<in>| B)"
  by (auto simp: ffUnion.rep_eq)

lemma finite_union_image_member:
  "x |\<in>| ffUnion (fimage f A) \<longleftrightarrow> (\<exists>a. a |\<in>| A \<and> x |\<in>| f a)"
  by (auto simp: ffUnion.rep_eq fimage.rep_eq)

lemma finite_singleton_when_member:
  "x |\<in>| (if P then {|y|} else {||}) \<longleftrightarrow> P \<and> x=y"
  by (cases P) auto

lemma finite_image_member:
  "y |\<in>| fimage f A \<longleftrightarrow> (\<exists>x. x |\<in>| A \<and> y=f x)"
  by (auto simp: fimage.rep_eq)

lemma finite_first_projection_member:
  "a |\<in>| fimage fst R \<longleftrightarrow> (\<exists>b. (a,b) |\<in>| R)"
  by (simp only: finite_image_member split_paired_Ex fst_conv; blast)

lemma finite_second_projection_member:
  "b |\<in>| fimage snd R \<longleftrightarrow> (\<exists>a. (a,b) |\<in>| R)"
  by (simp only: finite_image_member split_paired_Ex snd_conv; blast)

lemma finite_value_image_domain:
  "fimage fst (fimage (map_prod id f) R)=fimage fst R"
  by (simp add: fimage_fimage comp_def map_prod_def case_prod_unfold)

lemma finite_unless_member:
  "x |\<in>| (if P then {||} else A) \<longleftrightarrow> \<not>P \<and> x |\<in>| A"
  by (cases P) auto

end
