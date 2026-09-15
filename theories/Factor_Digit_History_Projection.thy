theory Factor_Digit_History_Projection
  imports Factor_Digit_History_States Optional_Result_Views
begin

lemma digit_history_original_components:
  "finite_history_header (digit_history_original_state q)=digit_history_header q"
  "required_history_material (digit_history_original_state q)=snd (digit_allocated_view (digit_history_material q))"
  "required_history_members (digit_history_original_state q)=digit_history_ledger q"
  by (simp_all only: digit_history_original_state_def finite_history_with_components)

lemma digit_history_policy_fields:
  "required_history_policy (digit_history_original_state q)=history_header_policy (digit_history_header q)"
  "required_history_policy_use (digit_history_original_state q)=history_header_policy_use (digit_history_header q)"
  "required_history_entry (digit_history_original_state q)=history_header_entry (digit_history_header q)"
  by (simp_all add: digit_history_original_state_def finite_history_with_def)

definition digit_history_base_view where
  "digit_history_base_view q=(fst (digit_allocated_view (digit_history_material q)),digit_history_original_state q)"

lemma digit_history_base_components:
  "fst (digit_history_base_view q)=fst (digit_allocated_view (digit_history_material q))"
  "snd (digit_history_base_view q)=digit_history_original_state q"
  by (simp_all only: digit_history_base_view_def fst_conv snd_conv)

definition bounded_history_result_view :: "(nat\<times>finite_required_history_state)\<Rightarrow>digit_history_result" where
  "bounded_history_result_view state=(fst state,snd state,fset_of_list (required_history_members (snd state)))"

lemma digit_history_state_view_cache:
  "history_member_index_exact (digit_history_index q) (digit_history_ledger q) \<Longrightarrow>
    digit_history_state_view q=bounded_history_result_view (digit_history_base_view q)"
  by (simp only: digit_history_state_view_def bounded_history_result_view_def digit_history_base_components
    digit_history_original_components history_member_view_exact)

definition bounded_history_load where
  "bounded_history_load (q::finite_required_history_state)=(if finite_environment_formed (required_history_material q)
    then Some (finite_compact_use_head (finite_environment_uses (required_history_material q)) None,q) else None)"

theorem digit_history_load_base_projection:
  "map_option digit_history_base_view (digit_history_load_state q)=bounded_history_load q"
  unfolding bounded_history_load_def
  by (rule optional_single_result_projection)
    (rule digit_history_load_state_domain,
     simp add: digit_history_base_view_def digit_history_load_state_properties)

theorem digit_history_load_state_projection:
  "map_option digit_history_state_view (digit_history_load_state q)=
    map_option bounded_history_result_view (bounded_history_load q)"
  by (rule optional_result_view_projection[OF digit_history_load_base_projection])
    (rule digit_history_state_view_cache; rule digit_history_load_state_properties(2))

theorem load_digit_required_history_projection:
  "map_option digit_history_view (load_digit_required_history q)=
    map_option bounded_history_result_view (bounded_history_load (raw_required_history q))"
proof -
  have "map_option digit_history_state_view
      (map_option raw_digit_required_history (load_digit_required_history q))=
    map_option bounded_history_result_view (bounded_history_load (raw_required_history q))"
    by (simp only: load_digit_required_history_raw digit_history_load_state_projection)
  then show ?thesis by (simp only: option.map_comp comp_def digit_history_view_def[abs_def])
qed

lemma load_digit_required_history_available:
  "load_digit_required_history q\<noteq>None"
proof -
  have formed: "finite_environment_formed (required_history_material (raw_required_history q))"
    using required_history_valid[of q] by (auto simp: finite_required_history_valid_def)
  have available: "digit_history_load_state (raw_required_history q)\<noteq>None"
    by (simp only: digit_history_load_state_domain formed)
  show ?thesis using available
    by (simp only: load_digit_required_history_raw[symmetric] map_option_is_None simp_thms)
qed

text \<open>
  The complete view retains the actual counter, every original history field
  and every decoded cache member. Cache fidelity supplies the relation component
  independently of original history validity. Loading a valid original history
  always succeeds and preserves this whole view, including ledger order.
\<close>

end
