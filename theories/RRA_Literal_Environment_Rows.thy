theory RRA_Literal_Environment_Rows
  imports RRA_Finite_Environment_Construction RRA_Finite_Environments
begin

definition finite_literal_artifact_rows where
  "finite_literal_artifact_rows R literals=(None,R)#map (\<lambda>(k,S). (Some k,S)) literals"

definition finite_literal_binding_rows where
  "finite_literal_binding_rows literals=map (\<lambda>(k,S). ((None,k),Some k)) literals"

theorem finite_literal_rows_environment:
  "finite_enumerated_environment (finite_literal_artifact_rows R literals) (finite_literal_binding_rows literals)=
    finite_literal_environment R (fset_of_list literals)"
  by (simp add: finite_enumerated_environment_def finite_literal_artifact_rows_def
    finite_literal_binding_rows_def finite_literal_environment_def fset_of_list_map fimage_fimage comp_def case_prod_unfold)

text \<open>
  The complete artifact and binding row lists present exactly the original
  literal environment. Duplicates retain their finite-relation meaning;
  formation and unique slot conditions remain separate prerequisites.
\<close>

end
