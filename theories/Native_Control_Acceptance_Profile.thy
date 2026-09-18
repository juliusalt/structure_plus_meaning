theory Native_Control_Acceptance_Profile
  imports Native_Control_Syntax_Execution
begin

type_synonym profile_acceptance_source = "local_address option definition_site \<times>
  local_address option finite_artifact_environment \<times> local_address option"

definition profile_acceptance_source :: "unit \<Rightarrow> profile_acceptance_source option" where
  "profile_acceptance_source ignored=isabelle_acceptance_source (snd development_seed_context)"

definition profile_acceptance_environment :: "profile_acceptance_source \<Rightarrow> bool" where
  "profile_acceptance_environment source=finite_environment_formed (fst (snd source))"

definition profile_acceptance_roots :: "profile_acceptance_source \<Rightarrow> _" where
  "profile_acceptance_roots source=finite_native_root_family_readings
    (fst (snd source)) (snd (snd source)) []"

definition profile_acceptance_rows :: "profile_acceptance_source \<Rightarrow> _" where
  "profile_acceptance_rows source=finite_native_definition_rows (fst (snd source))"

definition profile_acceptance_read :: "profile_acceptance_source \<Rightarrow> _" where
  "profile_acceptance_read source=finite_native_source (fst (snd source)) (snd (snd source)) []"

definition profile_acceptance_evaluate :: "local_address option finite_native_system \<Rightarrow>
    profile_acceptance_source \<Rightarrow> _" where
  "profile_acceptance_evaluate P source=finite_program_evaluation P (fset_of_list
    (map (\<lambda>e. (fst source,isabelle_entity_data e)) (development_seed_demands development_seed_context)))"

export_code profile_acceptance_source profile_acceptance_environment profile_acceptance_roots
  profile_acceptance_rows profile_acceptance_read profile_acceptance_evaluate
  in Eval module_name Native_Control_Acceptance_Profile file_prefix "native_control_acceptance_profile"

end
