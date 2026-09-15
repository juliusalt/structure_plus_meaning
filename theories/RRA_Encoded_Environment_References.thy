theory RRA_Encoded_Environment_References
  imports RRA_Digit_Environment_Instance RRA_Environment_Update_Correctness
begin

fun encoded_environment_update where
  "encoded_environment_update use_code slot_code I (Install_Artifact u R)=encoded_insert_artifact use_code I u R"
| "encoded_environment_update use_code slot_code I (Install_Binding u k v)=encoded_insert_binding use_code slot_code I u k v"

fun encoded_environment_update_ready where
  "encoded_environment_update_ready use_code slot_code I (Install_Artifact u R)=encoded_artifact_ready use_code I u R"
| "encoded_environment_update_ready use_code slot_code I (Install_Binding u k v)=encoded_binding_ready use_code slot_code I u k v"

definition encoded_environment_update_option where
  "encoded_environment_update_option use_code slot_code use_decode slot_decode X=(case X of (A,B,op) \<Rightarrow>
    let E=finite_enumerated_environment A B;I=encoded_environment_rows use_code slot_code A B
    in if finite_environment_formed E \<and> encoded_environment_update_ready use_code slot_code I op
      then Some (encoded_environment_view use_decode slot_decode (encoded_environment_update use_code slot_code I op))
      else None)"

definition encoded_environment_update_method where
  "encoded_environment_update_method use_code slot_code use_decode slot_decode X=
    finite_optional_image id {|encoded_environment_update_option use_code slot_code use_decode slot_decode X|}"

context environment_key_codec
begin

lemma update_ready_exact:
  "encoded_environment_represents use_code slot_code I E \<Longrightarrow>
    encoded_environment_update_ready use_code slot_code I op=finite_environment_update_ready E op"
  unfolding finite_environment_update_ready_exact
  by (cases op) (simp_all add: artifact_ready_exact binding_ready_exact)

lemma update_view_exact:
  "encoded_environment_represents use_code slot_code I E \<Longrightarrow>
    encoded_environment_view use_decode slot_decode (encoded_environment_update use_code slot_code I op)=
      finite_environment_update_body E op"
  by (cases op; auto intro: view_representation insert_artifact_exact insert_binding_exact)

theorem update_method_exact:
  "encoded_environment_update_method use_code slot_code use_decode slot_decode X=environment_update_reference X"
  by (cases X)
    (auto simp: encoded_environment_update_method_def encoded_environment_update_option_def
      environment_update_reference_def Let_def update_ready_exact[OF rows_exact] update_view_exact[OF rows_exact]
      finite_optional_image_exact intro!: fset_inject[THEN iffD1] set_eqI)

end

end
