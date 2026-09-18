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

lemma finite_union_image_flatten:
  "ffUnion (fimage f (ffUnion (fimage g A)))=
    ffUnion (fimage (\<lambda>a. ffUnion (fimage f (g a))) A)"
  by (rule fset_inject[THEN iffD1], rule set_eqI)
    (simp only: finite_union_image_member; blast)

lemma finite_singleton_when_member:
  "x |\<in>| (if P then {|y|} else {||}) \<longleftrightarrow> P \<and> x=y"
  by (cases P) auto

lemma finite_optional_value_member:
  "y |\<in>| (case a of None \<Rightarrow> {||} | Some x \<Rightarrow> {|x|}) \<longleftrightarrow> a=Some y"
  by (cases a) auto

lemma finite_image_member:
  "y |\<in>| fimage f A \<longleftrightarrow> (\<exists>x. x |\<in>| A \<and> y=f x)"
  by (auto simp: fimage.rep_eq)

lemma finite_value_image_member:
  "(s,y) |\<in>| fimage (map_prod id f) A \<longleftrightarrow>
    (\<exists>x. (s,x) |\<in>| A \<and> y=f x)"
  by (simp only: finite_image_member split_paired_Ex map_prod_def case_prod_conv id_apply prod.inject; blast)

lemma finite_first_projection_member:
  "a |\<in>| fimage fst R \<longleftrightarrow> (\<exists>b. (a,b) |\<in>| R)"
  by (simp only: finite_image_member split_paired_Ex fst_conv; blast)

lemma finite_second_projection_member:
  "b |\<in>| fimage snd R \<longleftrightarrow> (\<exists>a. (a,b) |\<in>| R)"
  by (simp only: finite_image_member split_paired_Ex snd_conv; blast)

lemma finite_value_image_domain:
  "fimage fst (fimage (map_prod id f) R)=fimage fst R"
  by (simp add: fimage_fimage comp_def map_prod_def case_prod_unfold)

lemma finite_value_image_range:
  "fimage snd (fimage (map_prod id f) R)=fimage f (fimage snd R)"
  by (simp add: fimage_fimage comp_def map_prod_def case_prod_unfold)

lemma fset_image_equality:
  assumes "inj f"
  shows "fimage f S=fimage f T \<longleftrightarrow> S=T"
  by (simp only: fset_inject[symmetric] fimage.rep_eq inj_image_eq_iff[OF assms])

lemma finite_unless_member:
  "x |\<in>| (if P then {||} else A) \<longleftrightarrow> \<not>P \<and> x |\<in>| A"
  by (cases P) auto

section \<open>The product of two finite sets\<close>

context
  includes fset.lifting
begin

lift_definition finite_pairs :: "'a fset \<Rightarrow> 'b fset \<Rightarrow> ('a\<times>'b) fset" is "\<lambda>A B. A\<times>B"
  by simp

end

lemma finite_pairs_member [simp]: "(a,b) |\<in>| finite_pairs A B \<longleftrightarrow> a |\<in>| A \<and> b |\<in>| B"
  by (simp add: finite_pairs.rep_eq)

text \<open>
  The product is listed pair by pair from the listings of its factors, so it is formed in time
  proportional to its size; a union of the images of one factor would compare every new pair
  with every pair already collected.
\<close>

end
