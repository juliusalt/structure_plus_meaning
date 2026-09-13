theory Factor_Finite_View_Installation
  imports Factor_Finite_System_Fields Factor_View_Definitions
begin

section \<open>Finite definition addition preserves the complete existing system fields\<close>

definition finite_add_view_definition :: "('a,'s,'d,'c) finite_schema_system\<Rightarrow>'d\<Rightarrow>
    'a finite_term_pattern\<Rightarrow>('c\<times>('a,'s,'d) finite_factor_schema) fset\<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system" where
  "finite_add_view_definition P d p C=\<lparr>
    finite_system_interfaces=finsert (d,p) (finite_system_interfaces P),
    finite_system_clauses=finite_system_clauses P |\<union>| fimage (\<lambda>(c,S). ((d,c),S)) C\<rparr>"

lemma finite_add_view_definition_correct [simp]:
  "decode_finite_system (finite_add_view_definition P d p C)=
    add_view_definition (decode_finite_system P) d (decode_finite_pattern p)
      (map_relation_values decode_finite_schema (fset C))"
  by (simp add: finite_add_view_definition_def add_view_definition_def decode_finite_system_def
    map_relation_values_def fimage.rep_eq image_Un image_image case_prod_unfold)

export_code finite_add_view_definition checking SML

end
