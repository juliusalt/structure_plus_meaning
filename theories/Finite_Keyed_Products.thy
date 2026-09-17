theory Finite_Keyed_Products
  imports Bootstrap_Finite_Closure Finite_Set_Composition
begin

definition finite_keyed_product :: "('s\<times>'a) fset\<Rightarrow>('s\<times>'b) fset\<Rightarrow>('s\<times>'a\<times>'b) fset" where
  "finite_keyed_product R S=fimage (\<lambda>((s,a),b). (s,a,b))
    (finite_edge_compose (fimage (\<lambda>(s,a). ((s,a),s)) R) S)"

lemma finite_keyed_product_member:
  "(s,a,b) |\<in>| finite_keyed_product R S \<longleftrightarrow> (s,a) |\<in>| R \<and> (s,b) |\<in>| S"
  by (simp only: finite_keyed_product_def finite_image_member finite_edge_compose_member
    split_paired_Ex case_prod_conv prod.inject; blast)

lemma finite_keyed_product_union:
  "ffUnion (fimage (\<lambda>(s,a). ffUnion
      (fimage (\<lambda>(r,b). if r=s then F s a b else {||}) S)) R)=
    ffUnion (fimage (\<lambda>(s,a,b). F s a b) (finite_keyed_product R S))"
  by (rule fset_inject[THEN iffD1], rule set_eqI)
    (simp only: finite_union_image_member split_paired_Ex case_prod_conv
      finite_keyed_product_member; auto split: if_splits)

lemma finite_keyed_product_union_values:
  "ffUnion (fimage (\<lambda>(s,a). ffUnion
      (fimage (\<lambda>(r,b). if r=s then F s a b else {||}) S)) (fimage (map_prod id f) R))=
    ffUnion (fimage (\<lambda>(s,a,b). F s (f a) b) (finite_keyed_product R S))"
proof -
  have mapped:
    "ffUnion (fimage (\<lambda>(s,a). ffUnion
      (fimage (\<lambda>(r,b). if r=s then F s a b else {||}) S)) (fimage (map_prod id f) R))=
      ffUnion (fimage (\<lambda>(s,a). ffUnion
      (fimage (\<lambda>(r,b). if r=s then F s (f a) b else {||}) S)) R)"
    by (simp only: fimage_fimage comp_def map_prod_def case_prod_unfold id_apply fst_conv snd_conv)
  show ?thesis by (rule trans[OF mapped], rule finite_keyed_product_union)
qed

text \<open>
  The original finite relation composition pairs every value at a common key
  and retains that key. Its exact member equation permits arbitrary complete
  relations; functionality is a separate prerequisite when a use requires it.
\<close>

end
