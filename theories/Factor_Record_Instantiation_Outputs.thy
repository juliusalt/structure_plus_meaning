theory Factor_Record_Instantiation_Outputs
  imports Factor_Record_Instantiation
begin

section \<open>The admitted source determines its complete encoded output\<close>

theorem record_instantiation_same_output:
  assumes source: "environment_value_presents E e"
    and first: "(61,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) x (data_list_term (map Payload_Term Us))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning record_instantiation_system"
    and second: "(61,pattern_instantiation_argument e (use_data_term u) (data_list_term (map Payload_Term Vs))
      (binding_rows_term xs) (Payload_Term r) y (data_list_term (map Payload_Term Us))
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning record_instantiation_system"
  shows "x=y"
proof -
  obtain ts where left: "x=data_list_term ts"
    using first by (simp only: record_instantiation_at_source[OF source]) blast
  obtain us where right: "y=data_list_term us"
    using second by (simp only: record_instantiation_at_source[OF source]) blast
  have same: "ts=us"
    using record_instantiation_result_unique[OF source first[unfolded left] second[unfolded right]] by blast
  show ?thesis by (simp only: left right same)
qed

text \<open>
  A caller may supply arbitrary output terms. Actual admission supplies their
  complete sequence shape, after which the existing source uniqueness theorem
  compares them. This removes a repeated output-decoding step from clients.
\<close>

end
