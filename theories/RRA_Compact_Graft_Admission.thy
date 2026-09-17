theory RRA_Compact_Graft_Admission
  imports RRA_Finite_Graft_Readiness Optional_Result_Invariants
begin

definition guarded_compact_graft where
  "guarded_compact_graft E u F=(if finite_compact_graft_ready E u F then Some (finite_compact_graft E u F) else None)"

theorem guarded_compact_graft_exact:
  "result=guarded_compact_graft E u F \<longleftrightarrow>
    original_graft_result (finite_compact_use_map (finite_environment_uses E) u)
      (decode_finite_environment E) u (decode_finite_environment F)
      (map_option decode_finite_environment result)"
  by (cases result) (auto simp: guarded_compact_graft_def original_graft_result_def
    finite_compact_graft_ready_exact finite_compact_graft_def finite_embedded_graft_exact[symmetric]
    split: if_splits)

theorem guarded_compact_graft_formed:
  "guarded_compact_graft E u F=Some G \<Longrightarrow> finite_environment_formed G"
  using original_ready_graft_formed
  by (auto simp: guarded_compact_graft_def finite_compact_graft_ready_exact
    finite_environment_formed_correct finite_compact_graft_def finite_embedded_graft_exact split: if_splits)

theorem guarded_compact_graft_complete:
  "guarded_compact_graft E u F=Some G \<Longrightarrow>
    G=finite_merge_environment E
      (finite_rename_environment (finite_compact_use_map (finite_environment_uses E) u) F)"
  by (auto simp: guarded_compact_graft_def finite_compact_graft_def finite_embedded_graft_def split: if_splits)

text \<open>
  The executable admission decision has an exact original readiness contract.
  Success retains every original and renamed relation row. Matching existing
  boundary bindings satisfy compatibility; conflicts refuse the entire graft.
  No conflicting binding is removed to manufacture a formed result.
\<close>

end
