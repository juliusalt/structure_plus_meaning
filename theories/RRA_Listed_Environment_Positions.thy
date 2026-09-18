theory RRA_Listed_Environment_Positions
  imports Listed_Set_Unions RRA_Finite_Environment_Positions
begin

section \<open>The positions of an environment are listed once\<close>

text \<open>
  The positions of an environment are the addresses of its artifacts, each paired with its use. They
  are computed once and then read by membership, so they are the listed union of the positions of
  each artifact: every artifact's carrier is listed once, instead of being inserted address by address
  into the positions already collected. Reading whether a site is a position of an environment whose
  artifacts hold a literal target of thousands of addresses had cost the square of that target.
\<close>

lemma finite_environment_positions_listed [code abstract]:
  "fset (finite_environment_positions E)=listed_image_union
    (\<lambda>(u,C). Pair u ` fset (finite_carrier (finite_structure C))) (fset (finite_environment_artifacts E))"
  by (auto simp: finite_environment_positions_def listed_image_union_def ffUnion.rep_eq fimage.rep_eq)

end
