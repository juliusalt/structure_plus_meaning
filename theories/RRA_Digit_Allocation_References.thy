theory RRA_Digit_Allocation_References
  imports RRA_Digit_Allocated_Projection RRA_Allocation_Result_Relations
begin

type_synonym digit_allocation_subject = "digit_allocated_environment option\<times>allocated_environment_update"

definition digit_allocation_relation :: "digit_allocation_subject\<Rightarrow>allocated_update_value\<Rightarrow>bool" where
  "digit_allocation_relation X result=(case X of (input,op) \<Rightarrow>
    \<exists>q. input=Some q \<and> original_allocation_result
      (fst (digit_allocated_view q),decode_finite_environment (snd (digit_allocated_view q))) op
      (map_option (\<lambda>(n,E). (n,decode_finite_environment E)) result))"

definition digit_allocation_reference where
  "digit_allocation_reference X=(case X of (input,op) \<Rightarrow>
    finite_prepared_results (\<lambda>q. finite_allocation_reference (digit_allocated_view q) op) input)"

theorem digit_allocation_reference_exact:
  "result |\<in>| digit_allocation_reference X \<longleftrightarrow> digit_allocation_relation X result"
  by (cases X) (simp only: digit_allocation_reference_def digit_allocation_relation_def case_prod_conv
    finite_prepared_results_exact finite_allocation_reference_exact)

theorem digit_allocation_typed_exact:
  "map_option digit_allocated_view (digit_allocated_update q op)=
    finite_allocation_reference (digit_allocated_view q) op"
proof -
  have view_function: "digit_allocated_view=(\<lambda>x. encoded_bounded_view read_digit_use_path read_digit_address_path
    (raw_digit_allocated x))"
    by (rule ext) (rule digit_allocated_view_raw)
  have projected: "map_option digit_allocated_view (digit_allocated_update q op)=
    map_option (encoded_bounded_view read_digit_use_path read_digit_address_path)
      (map_option raw_digit_allocated (digit_allocated_update q op))"
    by (simp only: option.map_comp comp_def view_function)
  show ?thesis by (simp only: projected digit_allocated_update_raw
    digit_environment.bounded_update_view[OF digit_allocated_valid]
    finite_allocation_reference_def digit_allocated_view_raw encoded_bounded_view_def case_prod_conv Let_def)
qed

end
