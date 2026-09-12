theory Factor_Finite_Inference_Premises
  imports Factor_Finite_Inference_Example Factor_Ground_Inference_Premises
begin

section \<open>The complete initial calls concern the actual supplied sources\<close>

definition finite_literal_source_calls :: "octets \<Rightarrow> (nat\<times>factor_term) list" where
  "finite_literal_source_calls p=ground_inference_source_calls
    (finite_environment_term (finite_literal_extension p)) None [0] (Some []) [] None [1] [7]
    (finite_environment_term (finite_literal_sources p)) None [3]
    (finite_environment_term (finite_literal_sources p)) None [8]
    (ground_schema_report (Payload_Term p)) [] finite_literal_node_interior [[6]] [[3]] []"

theorem finite_literal_source_calls_sound:
  "set (finite_literal_source_calls [])\<subseteq>positive_meaning inference_specialization_system"
proof -
  have rec: "pattern_record_at (example_literal_environment []) None {} [3] [] (set [[3]]) (set [])"
    using empty_binder_pattern_record[OF finite_literal_environments_formed(1)
      finite_literal_artifact_at finite_literal_binder] by simp
  show ?thesis unfolding finite_literal_source_calls_def ground_schema_report_def
    by (rule ground_inference_source_calls_sound[OF finite_literal_presentations(2)
      finite_literal_presentations(1) finite_literal_presentations(1)])
      (use finite_literal_native_node finite_literal_binding rec in \<open>simp_all add: ground_schema_report_def
        finite_literal_node_interior_def\<close>)
qed

section \<open>Finite execution receives those same data calls\<close>

lemma finite_literal_source_calls_data:
  assumes "(d,t)\<in>set (finite_literal_source_calls p)"
  shows "self_contained_term t"
  by (rule ground_inference_source_calls_data[OF _ _ _ _
      assms[unfolded finite_literal_source_calls_def]])
    (simp_all add: ground_schema_report_def data_list_term_self_contained)

definition finite_literal_inference_known :: "octets \<Rightarrow> (nat\<times>finite_factor_term) list" where
  "finite_literal_inference_known p =
    finite_data_call_values (finite_literal_source_calls p)"

lemma decode_finite_literal_inference_known:
  "map decode_finite_call_term (finite_literal_inference_known p)=finite_literal_source_calls p"
  unfolding finite_literal_inference_known_def
  by (rule decode_finite_data_call_values[OF finite_literal_source_calls_data])

theorem finite_literal_inference_known_sound:
  "image decode_finite_call_term (set (finite_literal_inference_known []))
    \<subseteq>positive_meaning inference_specialization_system"
  using finite_literal_source_calls_sound
  by (simp only: set_map[symmetric] decode_finite_literal_inference_known)

lemma finite_literal_known_entries:
  "map fst (finite_literal_inference_known p)=[94,294,126,125,61,61,345,346]"
  by (simp add: finite_literal_inference_known_def finite_data_call_values_def finite_literal_source_calls_def ground_inference_source_calls_def Let_def)

export_code finite_literal_inference_value finite_literal_inference_known
  Finite_Payload Finite_Pair Finite_Target Finite_Whole nat_of_integer integer_of_nat
  in SML module_name Finite_Literal_Inference_Premises file_prefix finite_literal_inference_premises

text \<open>
  The two reference instantiations coincide for an empty scope, but both
  premise occurrences remain in the supplied list. Every initial call is
  proved in the same program as the compiled construction library. The final
  inference-specialization entry is absent from this initial evidence.
\<close>

end
