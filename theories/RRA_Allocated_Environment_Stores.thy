theory RRA_Allocated_Environment_Stores
  imports RRA_Bounded_Environment_Updates
begin

typedef allocated_environment_store = "{q. bounded_environment_valid q}"
  morphisms raw_allocated_environment Allocated_Environment
  using bounded_empty_environment_valid by blast

setup_lifting type_definition_allocated_environment_store

lift_definition empty_allocated_environment :: allocated_environment_store
  is "bounded_environment_rows [] []" by (rule bounded_empty_environment_valid)

lift_definition (code_dt) load_allocated_environment ::
  "(local_address option\<times>finite_exact_artifact) list\<Rightarrow>
    ((local_address option\<times>local_address)\<times>local_address option) list\<Rightarrow>
      allocated_environment_store option"
  is bounded_environment_load
  by (auto intro: optional_result_invariant bounded_environment_load_valid)

lift_definition (code_dt) allocate_environment_artifact ::
  "allocated_environment_store\<Rightarrow>finite_exact_artifact\<Rightarrow>allocated_environment_store option"
  is bounded_environment_allocate
  by (auto intro: optional_result_invariant bounded_environment_allocate_valid)

lift_definition (code_dt) allocated_environment_add_binding ::
  "allocated_environment_store\<Rightarrow>local_address option\<Rightarrow>local_address\<Rightarrow>
    local_address option\<Rightarrow>allocated_environment_store option"
  is bounded_environment_add_binding
  by (auto intro: optional_result_invariant bounded_environment_add_binding_valid)

lift_definition allocated_environment_next_use :: "allocated_environment_store\<Rightarrow>local_address option"
  is bounded_environment_next_use .

lift_definition allocated_environment_artifacts ::
  "allocated_environment_store\<Rightarrow>local_address option\<Rightarrow>finite_exact_artifact fset"
  is "\<lambda>q. indexed_environment_artifacts (snd q)" .

lift_definition allocated_environment_bindings ::
  "allocated_environment_store\<Rightarrow>local_address option\<Rightarrow>local_address\<Rightarrow>local_address option fset"
  is "\<lambda>q. indexed_environment_bindings (snd q)" .

theorem allocated_environment_valid:
  "bounded_environment_valid (raw_allocated_environment q)"
  using raw_allocated_environment[of q] by simp

export_code empty_allocated_environment load_allocated_environment allocate_environment_artifact
  allocated_environment_add_binding allocated_environment_next_use allocated_environment_artifacts
  allocated_environment_bindings checking SML

end
