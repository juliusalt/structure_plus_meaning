theory RRA_Allocated_Environment_Projection
  imports RRA_Allocated_Environment_Stores RRA_Environment_Update_Correctness
begin

definition allocated_environment_view where
  "allocated_environment_view q=(fst q,indexed_environment_view (snd q))"

lemma allocated_environment_load_raw:
  "map_option raw_allocated_environment (load_allocated_environment A B)=bounded_environment_load A B"
  by transfer (simp add: option.map_id[unfolded id_def])

lemma allocated_environment_allocate_raw:
  "map_option raw_allocated_environment (allocate_environment_artifact q R)=
    bounded_environment_allocate (raw_allocated_environment q) R"
  by transfer (simp add: option.map_id[unfolded id_def])

lemma allocated_environment_binding_raw:
  "map_option raw_allocated_environment (allocated_environment_add_binding q u k v)=
    bounded_environment_add_binding (raw_allocated_environment q) u k v"
  by transfer (simp add: option.map_id[unfolded id_def])

datatype allocated_environment_update = Allocate_Artifact finite_exact_artifact
  | Add_Allocated_Binding "local_address option" local_address "local_address option"

fun allocated_environment_update_at where
  "allocated_environment_update_at n (Allocate_Artifact R)=Install_Artifact (Some [n]) R"
| "allocated_environment_update_at n (Add_Allocated_Binding u k v)=Install_Binding u k v"

fun allocated_environment_next_head where
  "allocated_environment_next_head n (Allocate_Artifact R)=Suc n"
| "allocated_environment_next_head n (Add_Allocated_Binding u k v)=n"

fun allocated_environment_update_raw where
  "allocated_environment_update_raw q (Allocate_Artifact R)=bounded_environment_allocate q R"
| "allocated_environment_update_raw q (Add_Allocated_Binding u k v)=bounded_environment_add_binding q u k v"

fun allocated_environment_update_typed where
  "allocated_environment_update_typed q (Allocate_Artifact R)=allocate_environment_artifact q R"
| "allocated_environment_update_typed q (Add_Allocated_Binding u k v)=allocated_environment_add_binding q u k v"

lemma allocated_environment_update_projection:
  "map_option raw_allocated_environment (allocated_environment_update_typed q op)=
    allocated_environment_update_raw (raw_allocated_environment q) op"
  by (cases op) (simp_all add: allocated_environment_allocate_raw allocated_environment_binding_raw)

lemma allocated_environment_update_guarded:
  assumes valid: "bounded_environment_valid q"
  shows "allocated_environment_update_raw q op=(if environment_update_guard 1 (snd q)
      (allocated_environment_update_at (fst q) op)
    then Some (allocated_environment_next_head (fst q) op,
      indexed_environment_update (snd q) (allocated_environment_update_at (fst q) op)) else None)"
  using bounded_environment_allocate_indexed[OF valid]
  by (cases op)
    (auto simp: indexed_add_artifact_def indexed_artifact_ready_def bounded_environment_next_use_def
      bounded_environment_add_binding_def indexed_add_binding_def indexed_binding_ready_def)

theorem allocated_environment_update_view:
  assumes valid: "bounded_environment_valid q"
  shows "map_option allocated_environment_view (allocated_environment_update_raw q op)=
    (let n=fst q;E=indexed_environment_view (snd q);update=allocated_environment_update_at n op in
      if finite_environment_update_ready E update then
        Some (allocated_environment_next_head n op,finite_environment_update_body E update) else None)"
  by (simp add: allocated_environment_update_guarded[OF valid] allocated_environment_view_def Let_def
    environment_update_guard_full[OF indexed_environment_view_exact, unfolded One_nat_def]
    indexed_environment_update_view[OF indexed_environment_view_exact])

text \<open>
  Whole-state inspection retains the allocation head and complete original
  environment. The original local guarded constructor determines every field
  after an operation. Projection traverses the store for inspection; the actual
  allocation and binding operations do not use that whole view.
\<close>

end
