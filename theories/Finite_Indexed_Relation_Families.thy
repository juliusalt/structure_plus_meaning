theory Finite_Indexed_Relation_Families
  imports Indexed_Relation_Families Finite_Set_Composition
begin

definition finite_indexed_relation_family ::
    "'n fset\<Rightarrow>('n\<Rightarrow>('s\<times>'m) fset)\<Rightarrow>(('n\<times>'s)\<times>'m) fset" where
  "finite_indexed_relation_family N R=ffUnion (fimage (\<lambda>n.
    fimage (\<lambda>(s,m). ((n,s),m)) (R n)) N)"

lemma finite_indexed_relation_family_member:
  "((n,s),m) |\<in>| finite_indexed_relation_family N R \<longleftrightarrow>
    n |\<in>| N \<and> (s,m) |\<in>| R n"
  by (simp only: finite_indexed_relation_family_def finite_union_image_member finite_image_member
    split_paired_Ex case_prod_conv prod.inject; blast)

theorem finite_indexed_relation_family_correct:
  "fset (finite_indexed_relation_family N R)=indexed_relation_family (fset N) (\<lambda>n. fset (R n))"
  by (rule set_eqI) (auto simp: finite_indexed_relation_family_member indexed_relation_family_member)

export_code finite_indexed_relation_family checking SML

end
