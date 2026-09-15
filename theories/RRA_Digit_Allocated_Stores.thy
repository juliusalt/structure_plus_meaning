theory RRA_Digit_Allocated_Stores
  imports RRA_Encoded_Bounded_Updates
begin

typedef digit_allocated_environment = "{q. encoded_bounded_valid digit_use_path digit_address_path q}"
  morphisms raw_digit_allocated Digit_Allocated_Environment
  using digit_environment.bounded_empty_valid by blast

setup_lifting type_definition_digit_allocated_environment

lift_definition empty_digit_allocated :: digit_allocated_environment
  is "encoded_bounded_rows digit_use_path digit_address_path [] []"
  by (rule digit_environment.bounded_empty_valid)

lift_definition (code_dt) load_digit_allocated ::
  "(local_address option\<times>finite_exact_artifact) list\<Rightarrow>
    ((local_address option\<times>local_address)\<times>local_address option) list\<Rightarrow>digit_allocated_environment option"
  is "encoded_bounded_load digit_use_path digit_address_path"
  by (auto intro: optional_result_invariant digit_environment.bounded_load_valid)

lift_definition (code_dt) digit_allocated_allocate ::
  "digit_allocated_environment\<Rightarrow>finite_exact_artifact\<Rightarrow>digit_allocated_environment option"
  is "encoded_bounded_allocate digit_use_path"
  by (auto intro: optional_result_invariant digit_environment.bounded_allocate_valid)

lift_definition (code_dt) digit_allocated_add_binding ::
  "digit_allocated_environment\<Rightarrow>local_address option\<Rightarrow>local_address\<Rightarrow>
    local_address option\<Rightarrow>digit_allocated_environment option"
  is "encoded_bounded_binding digit_use_path digit_address_path"
  by (auto intro: optional_result_invariant digit_environment.bounded_binding_valid)

lift_definition digit_allocated_next_use :: "digit_allocated_environment\<Rightarrow>local_address option"
  is bounded_environment_next_use .

lift_definition digit_allocated_artifacts ::
  "digit_allocated_environment\<Rightarrow>local_address option\<Rightarrow>finite_exact_artifact fset"
  is "\<lambda>q. encoded_environment_artifacts digit_use_path (snd q)" .

lift_definition digit_allocated_bindings ::
  "digit_allocated_environment\<Rightarrow>local_address option\<Rightarrow>local_address\<Rightarrow>local_address option fset"
  is "\<lambda>q. encoded_environment_bindings digit_use_path digit_address_path (snd q)" .

theorem digit_allocated_valid:
  "encoded_bounded_valid digit_use_path digit_address_path (raw_digit_allocated q)"
  using raw_digit_allocated[of q] by simp

export_code empty_digit_allocated load_digit_allocated digit_allocated_allocate digit_allocated_add_binding
  digit_allocated_next_use digit_allocated_artifacts digit_allocated_bindings checking SML

end
