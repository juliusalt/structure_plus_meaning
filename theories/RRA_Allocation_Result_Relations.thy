theory RRA_Allocation_Result_Relations
  imports RRA_Allocated_Environment_References Finite_Prepared_Results
begin

definition original_allocation_result ::
  "(nat\<times>local_address option artifact_environment)\<Rightarrow>allocated_environment_update\<Rightarrow>
    (nat\<times>local_address option artifact_environment) option\<Rightarrow>bool" where
  "original_allocation_result state op result=(case state of (n,E) \<Rightarrow>
    let update=allocated_environment_update_at n op in case result of
      None \<Rightarrow> \<not>original_environment_update_ready E update
    | Some (n',F) \<Rightarrow> original_environment_update_ready E update \<and>
        n'=allocated_environment_next_head n op \<and> F=original_environment_update_body E update)"

definition finite_allocation_reference ::
  "(nat\<times>local_address option finite_artifact_environment)\<Rightarrow>
    allocated_environment_update\<Rightarrow>allocated_update_value" where
  "finite_allocation_reference state op=(case state of (n,E) \<Rightarrow>
    let update=allocated_environment_update_at n op in if finite_environment_update_ready E update then
      Some (allocated_environment_next_head n op,finite_environment_update_body E update) else None)"

theorem finite_allocation_reference_exact:
  "result=finite_allocation_reference state op \<longleftrightarrow>
    original_allocation_result (fst state,decode_finite_environment (snd state)) op
      (map_option (\<lambda>(n,E). (n,decode_finite_environment E)) result)"
  by (cases state; cases result)
    (auto simp: finite_allocation_reference_def original_allocation_result_def Let_def
      finite_environment_update_ready_exact finite_environment_update_body_exact[symmetric]
      decode_finite_environment_injective split: prod.splits if_splits)

lemma allocated_reference_instance:
  "allocated_update_reference_option q op=
    finite_allocation_reference (allocated_environment_view (raw_allocated_environment q)) op"
  by (simp add: allocated_update_reference_option_def finite_allocation_reference_def
    allocated_environment_view_def Let_def)

lemma allocated_relation_instance:
  "allocated_update_relation X result=(case X of (input,op) \<Rightarrow>
    \<exists>q. input=Some q \<and> original_allocation_result
      (fst (raw_allocated_environment q),decode_finite_environment
        (indexed_environment_view (snd (raw_allocated_environment q)))) op
      (map_option (\<lambda>(n,E). (n,decode_finite_environment E)) result))"
  by (cases X; cases result)
    (auto simp: allocated_update_relation_def original_allocation_result_def Let_def split: option.splits)

text \<open>
  The original result relation depends on the complete counter and original
  environment, independently of a storage representation. It specifies the
  guarded constructor's whole optional result. Input formation is a separate
  admission premise, carried by each closed store when this relation is used.
\<close>

end
