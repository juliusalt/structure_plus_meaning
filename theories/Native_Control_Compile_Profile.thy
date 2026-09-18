theory Native_Control_Compile_Profile
  imports Native_Control_Source_Profile
begin

definition profile_compile_term where
  "profile_compile_term t=finite_compile_schema (finite_ground_rule t)"

definition profile_pattern_term where
  "profile_pattern_term t=finite_pattern_syntax (\<lambda>a::local_address. []) (finite_exact_term_pattern t)"

definition profile_compiled_forest where
  "profile_compiled_forest Ks=finite_schema_forest Ks"

definition profile_artifact_size :: "finite_exact_artifact \<Rightarrow> nat\<times>nat\<times>nat" where
  "profile_artifact_size R=(fcard (finite_carrier (finite_structure R)),
    fcard (finite_incidence (finite_structure R)),fcard (finite_bindings (finite_data R)))"

export_code profile_terms profile_compile_term profile_pattern_term profile_compiled_forest
  profile_artifact_size integer_of_nat
  in Eval module_name Native_Control_Compile_Profile file_prefix "native_control_compile_profile"

end
