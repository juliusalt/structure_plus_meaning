theory Factor_Finite_System_Fields
  imports Factor_Executable_Systems Factor_System_Renaming Factor_Finite_Schema_Renaming Functional_Enumeration_Indexes
begin

section \<open>Executable projections and simultaneous definition relocation\<close>

definition finite_system_interface_option :: "('a,'s,'d,'c) finite_schema_system\<Rightarrow>'d\<Rightarrow>'a finite_term_pattern option" where
  "finite_system_interface_option P d=finite_relation_option (finite_system_interfaces P) d"

definition finite_system_clause_family :: "('a,'s,'d,'c) finite_schema_system\<Rightarrow>'d\<Rightarrow>
    ('c\<times>('a,'s,'d) finite_factor_schema) fset" where
  "finite_system_clause_family P d=fimage (\<lambda>((e,c),S). (c,S))
    (ffilter (\<lambda>r. fst (fst r)=d) (finite_system_clauses P))"

lemma finite_system_interface_option_correct:
  assumes formed: "finite_system_formed P" and member: "d |\<in>| finite_system_definitions P"
  shows "\<exists>p. finite_system_interface_option P d=Some p \<and>
    decode_finite_pattern p=system_interface (decode_finite_system P) d"
proof -
  obtain p where row: "(d,p) |\<in>| finite_system_interfaces P"
    using member by (auto simp: finite_system_definitions_def)
  have functional: "finite_relation_functional (finite_system_interfaces P)"
    using formed by (simp add: finite_system_formed_def)
  have selected: "finite_system_interface_option P d=Some p"
    by (simp only: finite_system_interface_option_def
      functional_option_index.query_search[OF functional UNIV_I, unfolded id_apply]; rule row)
  have source: "schema_system_formed (decode_finite_system P)"
    using formed by (simp only: finite_system_formed_correct)
  have actual: "(d,decode_finite_pattern p)\<in>system_interfaces (decode_finite_system P)"
    using row by (auto simp: map_relation_values_def)
  show ?thesis by (rule exI[of _ p]) (use selected system_interface_unique[OF source actual] in simp)
qed

lemma finite_system_clause_family_correct [simp]:
  "map_relation_values decode_finite_schema (fset (finite_system_clause_family P d))=
    system_clause_family (decode_finite_system P) d"
  by (auto simp: finite_system_clause_family_def system_clause_family_def map_relation_values_def
    fimage.rep_eq ffilter.rep_eq image_iff; force)

definition finite_rename_system :: "('d\<Rightarrow>'e)\<Rightarrow>('a,'s,'d,'c) finite_schema_system\<Rightarrow>
    ('a,'s,'e,'c) finite_schema_system" where
  "finite_rename_system g P=\<lparr>
    finite_system_interfaces=fimage (map_prod g id) (finite_system_interfaces P),
    finite_system_clauses=fimage (map_prod (map_prod g id) (finite_rename_schema id id g)) (finite_system_clauses P)\<rparr>"

lemma finite_rename_system_correct [simp]:
  "decode_finite_system (finite_rename_system g P)=rename_system g (decode_finite_system P)"
  by (simp add: finite_rename_system_def rename_system_def decode_finite_system_def
    map_relation_values_def fimage.rep_eq image_image map_prod_def case_prod_unfold finite_rename_schema_correct)

end
