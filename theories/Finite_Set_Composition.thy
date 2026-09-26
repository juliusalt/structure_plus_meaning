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

section \<open>Images, unions and filters read at their members\<close>

text \<open>
  An image, a union of images and a filter of a finite set depend on their function only at the set's members; an
  image fixing every member is the set, and a member of one image is a member of the union.
\<close>

lemma ffUnion_fimage_member: "y |\<in>| G \<Longrightarrow> x |\<in>| f y \<Longrightarrow> x |\<in>| ffUnion (fimage f G)"
  by (force simp: ffUnion.rep_eq fimage.rep_eq)

lemma fimage_fixed:
  assumes "\<And>z. z |\<in>| B \<Longrightarrow> f z = z"
  shows "fimage f B = B"
proof -
  have "f ` fset B = fset B" using assms by (force intro: rev_image_eqI)
  then show ?thesis by (metis fimage.rep_eq fset_inject)
qed

lemma fimage_cong_on: "(\<And>x. x |\<in>| A \<Longrightarrow> f x = g x) \<Longrightarrow> fimage f A = fimage g A"
  by (force simp: fset_eq_iff fimage.rep_eq)

lemma ffUnion_fimage_agree:
  assumes "\<And>x. x |\<in>| A \<Longrightarrow> f x=g x"
  shows "ffUnion (fimage f A)=ffUnion (fimage g A)"
  by (simp only: fimage_cong_on[OF assms])

lemma ffilter_cong_on: "(\<And>x. x |\<in>| X \<Longrightarrow> F x \<longleftrightarrow> G x) \<Longrightarrow> ffilter F X = ffilter G X"
  by (auto simp: fset_eq_iff ffilter.rep_eq)

text \<open>The rows of a finite relation at a key, read over its listed rows, one insertion at a time.\<close>

lemma ffilter_finsert: "ffilter P (finsert a A) = (if P a then finsert a (ffilter P A) else ffilter P A)"
  by transfer auto

end
