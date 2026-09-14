theory Finite_Indexed_Relation_Images
  imports Bootstrap_Finite_Closure Finite_Function_Graphs Finite_Set_Composition
begin

definition finite_indexed_relation_image ::
    "('n\<times>'m) fset\<Rightarrow>(('n\<times>'s)\<times>'n) fset\<Rightarrow>(('m\<times>'s)\<times>'m) fset" where
  "finite_indexed_relation_image M R=fimage (\<lambda>(m,s,k). ((m,s),k))
    (finite_edge_compose (fimage prod.swap M)
      (fimage (\<lambda>((n,s),k). (n,s,k)) (finite_edge_compose R M)))"

lemma finite_indexed_relation_image_member:
  "((m,s),k) |\<in>| finite_indexed_relation_image M R \<longleftrightarrow>
    (\<exists>n q. ((n,s),q) |\<in>| R \<and> (n,m) |\<in>| M \<and> (q,k) |\<in>| M)"
  by (simp only: finite_indexed_relation_image_def finite_image_member
    split_paired_Ex finite_edge_compose_member case_prod_conv
    prod.swap_def fst_conv snd_conv prod.inject; blast)

theorem finite_indexed_relation_image_correct:
  "fset (finite_indexed_relation_image M R)={((m,s),k). \<exists>n q.
    ((n,s),q)\<in>fset R \<and> (n,m)\<in>fset M \<and> (q,k)\<in>fset M}"
  by (rule set_eqI) (auto simp: finite_indexed_relation_image_member; blast)

export_code finite_indexed_relation_image checking SML

text \<open>
  Two actual relation compositions transport both endpoints while preserving
  the middle index. The exact member equation applies to arbitrary supplied
  finite relations, including missing, conflicting and merged mappings.
  Functionality and injectivity remain independent conditions on their uses.
\<close>

end
