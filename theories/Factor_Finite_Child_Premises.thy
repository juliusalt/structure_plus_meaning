theory Factor_Finite_Child_Premises
  imports Factor_Finite_Child_Example Factor_Ground_Inference_Premises Factor_Inference_Claim_Compilation
begin

definition finite_child_source_calls :: "octets\<Rightarrow>(nat\<times>factor_term) list" where
  "finite_child_source_calls p=ground_inference_source_calls
    (finite_environment_term (finite_child_extension p)) (Some [2]) [0] (Some []) [] (Some [2]) [1] [7]
    (finite_environment_term (finite_child_sources p)) (Some [2]) [3]
    (finite_environment_term (finite_child_sources p)) (Some [2]) [8]
    (finite_child_report p) finite_child_discharges finite_child_parent_interior finite_child_parent_slots [[3]] []"

theorem finite_child_source_calls_sound:
  "set (finite_child_source_calls [])\<subseteq>positive_meaning inference_specialization_system"
proof -
  have rec: "pattern_record_at (example_child_environment []) (Some [2]) {} [3] [] (set [[3]]) (set [])"
    using empty_binder_pattern_record[OF finite_child_environments_formed(1)
      finite_child_artifact_at finite_child_binder] by simp
  show ?thesis unfolding finite_child_source_calls_def finite_child_report_def
    by (rule ground_inference_source_calls_sound[OF finite_child_presentations(2) finite_child_presentations(1)
      finite_child_presentations(1)])
      (use finite_child_native_parent finite_child_binding rec in \<open>simp_all add: finite_child_report_def
        finite_child_discharges_def finite_child_parent_interior_def finite_literal_node_interior_def
        finite_child_parent_slots_def\<close>)
qed

lemma finite_child_source_calls_data:
  assumes "(d,t)\<in>set (finite_child_source_calls p)"
  shows "self_contained_term t"
  by (rule ground_inference_source_calls_data[OF _ _ _ _
      assms[unfolded finite_child_source_calls_def]])
    (simp_all add: finite_child_report_def finite_child_ordinary_rows_def
      data_list_term_self_contained call_instance_value_def case_prod_unfold)

definition finite_child_inference_known :: "octets\<Rightarrow>(nat\<times>finite_factor_term) list" where
  "finite_child_inference_known p=finite_data_call_values (finite_child_source_calls p)"

lemma decode_finite_child_inference_known:
  "map decode_finite_call_term (finite_child_inference_known p)=finite_child_source_calls p"
  unfolding finite_child_inference_known_def
  by (rule decode_finite_data_call_values[OF finite_child_source_calls_data])

theorem finite_child_inference_known_sound:
  "image decode_finite_call_term (set (finite_child_inference_known []))
    \<subseteq>positive_meaning inference_specialization_system"
  using finite_child_source_calls_sound
  by (simp only: set_map[symmetric] decode_finite_child_inference_known)

theorem inference_claim_child_known_sound:
  "image decode_finite_call_term (set (finite_child_inference_known []))
    \<subseteq>positive_meaning inference_claim_full_system"
  by (rule subset_trans[OF finite_child_inference_known_sound
    whole_agreement_positive_subset[OF inference_specialization_formed inference_claim_full_formed
      inference_claim_full_inference_agreement]])

lemma finite_child_known_entries:
  "map fst (finite_child_inference_known p)=[94,294,126,125,61,61,345,346]"
  by (simp add: finite_child_inference_known_def finite_data_call_values_def finite_child_source_calls_def
    ground_inference_source_calls_def Let_def)

text \<open>
  These are source leaves for the exact one-premise source. Neither the source
  reader nor the final claim reader is an initial known call. The kernel proofs
  justify the finite inputs to conditional native reasoning; native admission
  of mathematical proofs remains a separate boundary.
\<close>

end
