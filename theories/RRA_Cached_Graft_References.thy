theory RRA_Cached_Graft_References
  imports RRA_Digit_Allocated_Grafts Finite_Prepared_Results
begin

type_synonym cached_graft_value = "(nat\<times>local_address option finite_artifact_environment) option"
type_synonym cached_graft_subject = "digit_allocated_environment option\<times>local_address option\<times>
    (local_address option\<times>finite_exact_artifact) list\<times>
    ((local_address option\<times>local_address)\<times>local_address option) list"

definition original_bounded_graft_result :: "(nat\<times>local_address option artifact_environment)\<Rightarrow>
    local_address option\<Rightarrow>local_address option artifact_environment\<Rightarrow>
    (nat\<times>local_address option artifact_environment) option\<Rightarrow>bool" where
  "original_bounded_graft_result state u F result \<longleftrightarrow>
    original_graft_result (prefix_use_map [fst state] u) (snd state) u F (map_option snd result) \<and>
    (case result of None \<Rightarrow> True | Some (n,G) \<Rightarrow> n=Suc (fst state))"

definition finite_bounded_graft_reference :: "(nat\<times>local_address option finite_artifact_environment)\<Rightarrow>
    local_address option\<Rightarrow>local_address option finite_artifact_environment\<Rightarrow>cached_graft_value" where
  "finite_bounded_graft_reference state u F=(let n=fst state;E=snd state;h=prefix_use_map [n] u in
    if finite_graft_prerequisites h E u F then Some (Suc n,finite_embedded_graft h E F) else None)"

lemma bounded_finite_graft_ready_exact:
  assumes bound: "finite_environment_head_bound n E"
  shows "finite_graft_prerequisites (prefix_use_map [n] u) E u F=
    original_graft_ready (prefix_use_map [n] u) (decode_finite_environment E) u (decode_finite_environment F)"
  using bounded_graft_prefix_embedding[OF bound, of u F]
  by (auto simp: finite_graft_prerequisites_def original_graft_ready_def
    finite_environment_formed_correct finite_shared_graft_artifact_exact finite_boundary_bindings_compatible_exact)

theorem finite_bounded_graft_reference_exact:
  assumes bound: "finite_environment_head_bound (fst state) (snd state)"
  shows "result=finite_bounded_graft_reference state u F \<longleftrightarrow>
    original_bounded_graft_result (fst state,decode_finite_environment (snd state)) u (decode_finite_environment F)
      (map_option (\<lambda>(n,G). (n,decode_finite_environment G)) result)"
  by (cases result) (auto simp: finite_bounded_graft_reference_def original_bounded_graft_result_def
    original_graft_result_def Let_def bounded_finite_graft_ready_exact[OF bound]
    finite_embedded_graft_exact[symmetric] split: prod.splits if_splits)

lemma digit_graft_view_bound:
  "finite_environment_head_bound (fst (digit_allocated_view q)) (snd (digit_allocated_view q))"
  using digit_environment.bounded_view_formed_and_bounded(2)[OF digit_allocated_valid, of q]
  by (simp only: digit_allocated_view_raw encoded_bounded_view_def fst_conv snd_conv)

lemma digit_graft_reference_exact:
  "map_option digit_allocated_view (digit_allocated_graft q u A B)=
    finite_bounded_graft_reference (digit_allocated_view q) u (finite_enumerated_environment A B)"
  by (simp only: digit_allocated_graft_view finite_bounded_graft_reference_def Let_def)

definition cached_graft_relation :: "cached_graft_subject\<Rightarrow>cached_graft_value\<Rightarrow>bool" where
  "cached_graft_relation X result=(case X of (input,u,A,B) \<Rightarrow> \<exists>q. input=Some q \<and>
    original_bounded_graft_result (fst (digit_allocated_view q),decode_finite_environment (snd (digit_allocated_view q)))
      u (decode_finite_environment (finite_enumerated_environment A B))
      (map_option (\<lambda>(n,G). (n,decode_finite_environment G)) result))"

definition cached_graft_reference where
  "cached_graft_reference X=(case X of (input,u,A,B) \<Rightarrow>
    finite_prepared_results (\<lambda>q. finite_bounded_graft_reference (digit_allocated_view q)
      u (finite_enumerated_environment A B)) input)"

theorem cached_graft_reference_exact:
  "result |\<in>| cached_graft_reference X \<longleftrightarrow> cached_graft_relation X result"
  by (cases X) (simp only: cached_graft_reference_def cached_graft_relation_def case_prod_conv
    finite_prepared_results_exact finite_bounded_graft_reference_exact[OF digit_graft_view_bound])

end
