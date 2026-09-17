theory RRA_Digit_Allocated_Grafts
  imports RRA_Encoded_Bounded_Grafts RRA_Digit_Allocated_Projection
begin

lift_definition (code_dt) digit_allocated_graft :: "digit_allocated_environment\<Rightarrow>local_address option\<Rightarrow>
    (local_address option\<times>finite_exact_artifact) list\<Rightarrow>
    ((local_address option\<times>local_address)\<times>local_address option) list\<Rightarrow>digit_allocated_environment option"
  is "encoded_bounded_graft digit_use_path digit_address_path"
  by (auto intro: optional_result_invariant digit_environment.bounded_graft_valid)

lemma digit_allocated_graft_raw:
  "map_option raw_digit_allocated (digit_allocated_graft q u A B)=
    encoded_bounded_graft digit_use_path digit_address_path (raw_digit_allocated q) u A B"
  by transfer (simp add: option.map_id[unfolded id_def])

theorem digit_allocated_graft_view:
  "map_option digit_allocated_view (digit_allocated_graft q u A B)=
    (let n=fst (digit_allocated_view q);E=snd (digit_allocated_view q);
      F=finite_enumerated_environment A B;h=prefix_use_map [n] u in
      if finite_graft_prerequisites h E u F then Some (Suc n,finite_embedded_graft h E F) else None)"
proof -
  have view_function: "digit_allocated_view=(\<lambda>x. encoded_bounded_view read_digit_use_path read_digit_address_path (raw_digit_allocated x))"
    by (rule ext) (rule digit_allocated_view_raw)
  have projected: "map_option digit_allocated_view (digit_allocated_graft q u A B)=
    map_option (encoded_bounded_view read_digit_use_path read_digit_address_path)
      (map_option raw_digit_allocated (digit_allocated_graft q u A B))"
    by (simp only: option.map_comp comp_def view_function)
  show ?thesis by (simp only: projected digit_allocated_graft_raw
    digit_environment.bounded_graft_view[OF digit_allocated_valid]
    digit_allocated_view_raw encoded_bounded_view_def fst_conv snd_conv Let_def)
qed

text \<open>
  The existing closed digit store gains a whole graft operation. Its type
  carries original formation and the actual updated bound. The operation checks
  the imported environment and shared-boundary lookups, inserts every renamed
  imported row into the original index and advances the stored head. Complete
  projection is an observation; the actual graft never executes that whole view.
\<close>

end
