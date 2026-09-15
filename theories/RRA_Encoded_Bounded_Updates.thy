theory RRA_Encoded_Bounded_Updates
  imports RRA_Encoded_Bounded_States
begin

definition encoded_bounded_allocate where
  "encoded_bounded_allocate use_code q R=(if finite_exact_formed R then
    Some (Suc (fst q),encoded_insert_artifact use_code (snd q) (bounded_environment_next_use q) R) else None)"

definition encoded_bounded_binding where
  "encoded_bounded_binding use_code slot_code q u k v=map_option (\<lambda>I. (fst q,I))
    (encoded_add_binding use_code slot_code (snd q) u k v)"

context environment_key_codec
begin

lemma bounded_allocate_equivalent:
  assumes equivalent: "encoded_bounded_equivalent use_code slot_code q r"
  shows "rel_option (encoded_bounded_equivalent use_code slot_code)
    (encoded_bounded_allocate use_code q R) (bounded_environment_allocate r R)"
proof -
  have head: "fst q=fst r" and indexes: "environment_indexes_equivalent use_code slot_code (snd q) (snd r)"
    using equivalent by (auto simp: encoded_bounded_equivalent_def)
  have next_item: "bounded_environment_next_use q=bounded_environment_next_use r"
    by (simp add: bounded_environment_next_use_def head)
  have inserted: "environment_indexes_equivalent use_code slot_code
    (encoded_insert_artifact use_code (snd q) (bounded_environment_next_use q) R)
    (indexed_insert_artifact (snd r) (bounded_environment_next_use r) R)"
    by (simp only: next_item; rule artifact_insert_equivalent[OF indexes])
  show ?thesis by (simp add: encoded_bounded_allocate_def bounded_environment_allocate_def
    encoded_bounded_equivalent_def head inserted split: if_splits)
qed

lemma bounded_binding_equivalent:
  assumes equivalent: "encoded_bounded_equivalent use_code slot_code q r"
  shows "rel_option (encoded_bounded_equivalent use_code slot_code)
    (encoded_bounded_binding use_code slot_code q u k v) (bounded_environment_add_binding r u k v)"
proof -
  have head: "fst q=fst r" and indexes: "environment_indexes_equivalent use_code slot_code (snd q) (snd r)"
    using equivalent by (auto simp: encoded_bounded_equivalent_def)
  have guard: "encoded_binding_ready use_code slot_code (snd q) u k v=indexed_binding_ready (snd r) u k v"
    by (rule equivalent_binding_ready[OF indexes])
  have inserted: "environment_indexes_equivalent use_code slot_code
    (encoded_insert_binding use_code slot_code (snd q) u k v) (indexed_insert_binding (snd r) u k v)"
    by (rule binding_insert_equivalent[OF indexes])
  show ?thesis by (simp add: encoded_bounded_binding_def bounded_environment_add_binding_def
    encoded_add_binding_def indexed_add_binding_def guard encoded_bounded_equivalent_def head inserted split: if_splits)
qed

lemma bounded_allocate_valid:
  assumes valid: "encoded_bounded_valid use_code slot_code q" and step: "encoded_bounded_allocate use_code q R=Some following"
  shows "encoded_bounded_valid use_code slot_code following"
proof -
  obtain r where equivalent: "encoded_bounded_equivalent use_code slot_code q r" and old: "bounded_environment_valid r"
    using bounded_valid_original[OF valid] by blast
  obtain next_item where step_old: "bounded_environment_allocate r R=Some next_item"
    and following: "encoded_bounded_equivalent use_code slot_code following next_item"
    using bounded_allocate_equivalent[OF equivalent, of R] step
    by (cases "bounded_environment_allocate r R") auto
  have "bounded_environment_valid next_item" by (rule bounded_environment_allocate_valid[OF old step_old])
  then show ?thesis using equivalent_bounded_valid[OF following] by blast
qed

lemma bounded_binding_valid:
  assumes valid: "encoded_bounded_valid use_code slot_code q" and step: "encoded_bounded_binding use_code slot_code q u k v=Some following"
  shows "encoded_bounded_valid use_code slot_code following"
proof -
  obtain r where equivalent: "encoded_bounded_equivalent use_code slot_code q r" and old: "bounded_environment_valid r"
    using bounded_valid_original[OF valid] by blast
  obtain next_item where step_old: "bounded_environment_add_binding r u k v=Some next_item"
    and following: "encoded_bounded_equivalent use_code slot_code following next_item"
    using bounded_binding_equivalent[OF equivalent, of u k v] step
    by (cases "bounded_environment_add_binding r u k v") auto
  have "bounded_environment_valid next_item" by (rule bounded_environment_add_binding_valid[OF old step_old])
  then show ?thesis using equivalent_bounded_valid[OF following] by blast
qed

end

text \<open>
  Actual encoded allocation and binding operations preserve the original
  optional transitions through complete lookup equivalence. The established
  original bound and formation preservation arguments are reused. Allocation
  checks only the new artifact, inserts at the actual stored head and advances
  it; the original environment is never rebuilt by that operation.
\<close>

end
