theory Native_Control_Source_Profile
  imports Native_Control_Context_Execution
begin

text \<open>Diagnostic entry points expose the original ground-source suboperations
  on the unchanged seed. These definitions do not register replacement code
  equations, choose a correction, or supply a checked-context judgment.\<close>

definition profile_terms :: "unit \<Rightarrow> finite_factor_term list" where
  "profile_terms ignored=map isabelle_entity_data (snd development_seed_context)"

definition profile_input_formed where
  "profile_input_formed xs=list_all finite_term_formed xs"

definition profile_program_formed :: "local_address option finite_native_system \<Rightarrow> bool" where
  "profile_program_formed Q=finite_system_formed Q"

definition profile_source_reading where
  "profile_source_reading ignored=finite_native_source (finite_guard_source True) None [0]"

definition profile_agreement where
  "profile_agreement Q=finite_system_agrees_on (finite_guard_source_program True) Q
    (finite_system_definitions (finite_guard_source_program True))"

definition profile_context where
  "profile_context Q=finite_source_extension_context (finite_guard_source True) None [0] Q"

definition profile_placement where
  "profile_placement Q=finite_program_coordinates (finite_guard_source True)
    (finite_system_definitions (finite_guard_source_program True)) (finite_system_definitions Q) id"

definition profile_coordinates where
  "profile_coordinates Q=map (profile_placement Q) (sorted_list_of_fset (finite_system_definitions Q))"

definition profile_rename_old where
  "profile_rename_old Q=finite_rename_system (profile_placement Q) (finite_guard_source_program True)"

definition profile_rename_target where
  "profile_rename_target Q=finite_rename_system (profile_placement Q) Q"

definition profile_extension_ready :: "local_address option finite_native_system \<Rightarrow>
    local_address option finite_native_system \<Rightarrow> bool" where
  "profile_extension_ready P Q=finite_native_extension_ready (finite_guard_source True) P Q"

definition profile_compile :: "local_address option finite_native_system \<Rightarrow>
    local_address option finite_native_system \<Rightarrow> _" where
  "profile_compile P Q=finite_compile_definitions Q
    (sorted_list_of_fset (finite_system_definitions Q |-| finite_system_definitions P))"

definition profile_install where
  "profile_install rows=finite_install_code_rows (finite_guard_source True) rows"

definition profile_select where
  "profile_select E Q=finite_select_roots E (sorted_list_of_fset (finite_system_definitions Q))"

export_code profile_terms profile_input_formed finite_ground_program profile_program_formed
  profile_source_reading profile_agreement profile_context profile_coordinates
  profile_rename_old profile_rename_target profile_extension_ready profile_compile
  profile_install profile_select finite_ground_source
  in Eval module_name Native_Control_Source_Profile file_prefix "native_control_source_profile"

end
