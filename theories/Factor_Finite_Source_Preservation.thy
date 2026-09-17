theory Factor_Finite_Source_Preservation
  imports Factor_Finite_Native_Sources RRA_Finite_Environment_Preservation
begin

type_synonym finite_native_entry_result =
  "(local_address option definition_site\<times>local_address option finite_artifact_environment\<times>
    local_address option) option"

definition finite_source_preservation_observation ::
    "local_address option finite_artifact_environment\<Rightarrow>local_address option\<Rightarrow>local_address\<Rightarrow>
      finite_native_entry_result\<Rightarrow>bool" where
  "finite_source_preservation_observation E u r result=(case result of None \<Rightarrow> False
    | Some (d,F,v) \<Rightarrow> finite_environment_formed F \<and> finite_environment_included E F \<and>
      finite_environment_agrees_on E F (finite_environment_uses E) \<and>
      (case finite_native_source E u r of None \<Rightarrow> False
        | Some P \<Rightarrow> finite_native_source F u r=Some P))"

definition finite_source_preservation_condition ::
    "local_address option finite_artifact_environment\<Rightarrow>local_address option\<Rightarrow>local_address\<Rightarrow>
      finite_native_entry_result\<Rightarrow>bool" where
  "finite_source_preservation_condition E u r result=(case result of None \<Rightarrow> False
    | Some (d,F,v) \<Rightarrow> environment_formed (decode_finite_environment F) \<and>
      environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
      (\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
        artifact_at (decode_finite_environment E) w A \<longleftrightarrow> artifact_at (decode_finite_environment F) w A) \<and>
      (\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
        binds_slot (decode_finite_environment E) w k v \<longleftrightarrow> binds_slot (decode_finite_environment F) w k v) \<and>
      (\<exists>P. native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
        native_package_at (decode_finite_environment F) u r (decode_finite_system P)))"

theorem finite_source_preservation_exact:
  "finite_source_preservation_observation E u r result=finite_source_preservation_condition E u r result"
  by (auto simp: finite_source_preservation_observation_def finite_source_preservation_condition_def
    finite_environment_formed_correct finite_environment_included_correct finite_environment_agrees_on_correct
    finite_native_source_correct[symmetric] split: option.splits prod.splits)

end
