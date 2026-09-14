theory RRA_Finite_Environment_Positions
  imports RRA_Finite_Environments RRA_Citation_Closure Finite_Set_Composition
begin

definition finite_environment_positions ::
  "'u finite_artifact_environment \<Rightarrow> ('u\<times>local_address) fset" where
  "finite_environment_positions E = ffUnion (fimage (\<lambda>(u,C).
    fimage (Pair u) (finite_carrier (finite_structure C))) (finite_environment_artifacts E))"

lemma finite_environment_positions_member:
  "d |\<in>| finite_environment_positions E \<longleftrightarrow>
    (\<exists>R. (fst d,R) |\<in>| finite_environment_artifacts E \<and>
      snd d |\<in>| finite_carrier (finite_structure R))"
  by (cases d; simp only: finite_environment_positions_def finite_union_image_member
    finite_image_member split_paired_Ex case_prod_conv prod.inject fst_conv snd_conv; blast)

lemma finite_environment_positions_correct:
  "fset (finite_environment_positions E) = environment_positions (decode_finite_environment E)"
  by (auto simp: finite_environment_positions_def finite_union_image_member finite_image_member
      environment_positions_def artifact_at_def split: prod.splits; force)

end
