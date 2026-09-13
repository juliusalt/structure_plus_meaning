theory Factor_Finite_System_Unions
  imports Factor_Finite_System_Fields Factor_System_Unions
begin

definition finite_system_union where
  "finite_system_union P Q=\<lparr>finite_system_interfaces=finite_system_interfaces P |\<union>| finite_system_interfaces Q,
    finite_system_clauses=finite_system_clauses P |\<union>| finite_system_clauses Q\<rparr>"

lemma finite_system_union_correct [simp]:
  "decode_finite_system (finite_system_union P Q)=system_union (decode_finite_system P) (decode_finite_system Q)"
  by (simp add: finite_system_union_def system_union_def decode_finite_system_def map_relation_values_def image_Un)

end
