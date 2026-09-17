theory RRA_Digit_Allocated_Projection
  imports RRA_Digit_Allocated_Stores
begin

definition encoded_bounded_view where
  "encoded_bounded_view use_decode slot_decode q=(fst q,encoded_environment_view use_decode slot_decode (snd q))"

fun encoded_bounded_update where
  "encoded_bounded_update use_code slot_code q (Allocate_Artifact R)=encoded_bounded_allocate use_code q R"
| "encoded_bounded_update use_code slot_code q (Add_Allocated_Binding u k v)=encoded_bounded_binding use_code slot_code q u k v"

context environment_key_codec
begin

lemma bounded_view_equivalent:
  "encoded_bounded_equivalent use_code slot_code q r \<Longrightarrow>
    encoded_bounded_view use_decode slot_decode q=allocated_environment_view r"
  by (auto simp: encoded_bounded_equivalent_def encoded_bounded_view_def allocated_environment_view_def
    intro: equivalent_environment_view)

lemma bounded_update_equivalent:
  "encoded_bounded_equivalent use_code slot_code q r \<Longrightarrow>
    rel_option (encoded_bounded_equivalent use_code slot_code)
      (encoded_bounded_update use_code slot_code q op) (allocated_environment_update_raw r op)"
  by (cases op) (simp_all add: bounded_allocate_equivalent bounded_binding_equivalent)

theorem bounded_update_view:
  assumes valid: "encoded_bounded_valid use_code slot_code q"
  shows "map_option (encoded_bounded_view use_decode slot_decode) (encoded_bounded_update use_code slot_code q op)=
    (let n=fst q;E=encoded_environment_view use_decode slot_decode (snd q);update=allocated_environment_update_at n op in
      if finite_environment_update_ready E update then
        Some (allocated_environment_next_head n op,finite_environment_update_body E update) else None)"
proof -
  obtain r where equivalent: "encoded_bounded_equivalent use_code slot_code q r" and old: "bounded_environment_valid r"
    using bounded_valid_original[OF valid] by blast
  have related: "rel_option (encoded_bounded_equivalent use_code slot_code)
      (encoded_bounded_update use_code slot_code q op) (allocated_environment_update_raw r op)"
    by (rule bounded_update_equivalent[OF equivalent])
  have mapped: "map_option (encoded_bounded_view use_decode slot_decode) (encoded_bounded_update use_code slot_code q op)=
      map_option allocated_environment_view (allocated_environment_update_raw r op)"
    using related by (cases "encoded_bounded_update use_code slot_code q op"; cases "allocated_environment_update_raw r op")
      (auto dest: bounded_view_equivalent)
  have head: "fst q=fst r"
    and environment: "encoded_environment_view use_decode slot_decode (snd q)=indexed_environment_view (snd r)"
    using bounded_view_equivalent[OF equivalent]
    by (auto simp: encoded_bounded_view_def allocated_environment_view_def)
  show ?thesis by (simp only: mapped allocated_environment_update_view[OF old] head environment)
qed

end

lemma digit_allocated_load_raw:
  "map_option raw_digit_allocated (load_digit_allocated A B)=encoded_bounded_load digit_use_path digit_address_path A B"
  by transfer (simp add: option.map_id[unfolded id_def])

lemma digit_allocated_allocate_raw:
  "map_option raw_digit_allocated (digit_allocated_allocate q R)=encoded_bounded_allocate digit_use_path (raw_digit_allocated q) R"
  by transfer (simp add: option.map_id[unfolded id_def])

lemma digit_allocated_binding_raw:
  "map_option raw_digit_allocated (digit_allocated_add_binding q u k v)=
    encoded_bounded_binding digit_use_path digit_address_path (raw_digit_allocated q) u k v"
  by transfer (simp add: option.map_id[unfolded id_def])

fun digit_allocated_update where
  "digit_allocated_update q (Allocate_Artifact R)=digit_allocated_allocate q R"
| "digit_allocated_update q (Add_Allocated_Binding u k v)=digit_allocated_add_binding q u k v"

lemma digit_allocated_update_raw:
  "map_option raw_digit_allocated (digit_allocated_update q op)=
    encoded_bounded_update digit_use_path digit_address_path (raw_digit_allocated q) op"
  by (cases op) (simp_all add: digit_allocated_allocate_raw digit_allocated_binding_raw)

lift_definition digit_allocated_view :: "digit_allocated_environment\<Rightarrow>nat\<times>local_address option finite_artifact_environment"
  is "encoded_bounded_view read_digit_use_path read_digit_address_path" .

lemma digit_allocated_view_raw:
  "digit_allocated_view q=encoded_bounded_view read_digit_use_path read_digit_address_path (raw_digit_allocated q)"
  by transfer simp

text \<open>
  The complete view preserves the actual counter and every original relation.
  Generic optional-step equivalence transfers the established original
  constructor equation. Raw projection of the digit API preserves every
  absent result; viewing a state is distinct from its local update operation.
\<close>

end
