theory Factor_Finite_Guard_Source_Extensions
  imports Factor_Finite_Mapped_Extensions Factor_Native_Requirement_Source_Models
begin

section \<open>The actual complete source program supplies the executable ordinary model\<close>

definition finite_nat_guard_source_model :: "bool\<Rightarrow>(nat,nat,nat,nat) finite_schema_system" where
  "finite_nat_guard_source_model b=\<lparr>finite_system_interfaces={|(0,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),finite_rename_schema (\<lambda>_. 0) (\<lambda>_. 0) (\<lambda>_. 0)
      (if b then finite_variable_schema else finite_equality_schema))|}\<rparr>"

lemma finite_nat_guard_source_model_correct [simp]:
  "decode_finite_system (finite_nat_guard_source_model b)=nat_guard_source_model b"
  by (simp add: finite_nat_guard_source_model_def nat_guard_source_model_def nat_guard_source_clause_def
    decode_finite_system_def map_relation_values_def finite_rename_schema_correct)

lemma finite_nat_guard_source_model_definitions [simp]:
  "finite_system_definitions (finite_nat_guard_source_model b)={|0|}"
  by (simp add: finite_system_definitions_def finite_nat_guard_source_model_def)

lemma finite_nat_guard_source_formed [simp]: "finite_system_formed (finite_nat_guard_source_model b)"
  by (simp only: finite_system_formed_correct finite_nat_guard_source_model_correct; rule nat_guard_source_model_formed)

lemma finite_guard_source_extension_profile:
  assumes target: "finite_system_formed Q"
    and agreement: "systems_agree_on (decode_finite_system (finite_nat_guard_source_model b)) (decode_finite_system Q)
      (system_definitions (decode_finite_system (finite_nat_guard_source_model b)))"
  shows "finite_mapped_native_extension (finite_guard_source b) (finite_nat_guard_source_model b) Q None [0]
    (decode_finite_system (finite_guard_source_program b)) native_guard_source_coordinate"
  by (rule finite_mapped_native_extension.intro[OF finite_guard_source_package finite_nat_guard_source_formed target agreement])
    (simp_all add: nat_guard_source_model_variant)

end
