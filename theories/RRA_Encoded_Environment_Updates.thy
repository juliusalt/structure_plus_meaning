theory RRA_Encoded_Environment_Updates
  imports RRA_Encoded_Environment_Views
begin

definition encoded_artifact_ready where
  "encoded_artifact_ready use_code I u R=lookup_artifact_ready (encoded_environment_artifacts use_code I) u R"

definition encoded_binding_ready where
  "encoded_binding_ready use_code slot_code I u k v=lookup_binding_ready
    (encoded_environment_artifacts use_code I) (encoded_environment_bindings use_code slot_code I) u k v"

definition encoded_add_artifact where
  "encoded_add_artifact use_code I u R=(if encoded_artifact_ready use_code I u R
    then Some (encoded_insert_artifact use_code I u R) else None)"

definition encoded_add_binding where
  "encoded_add_binding use_code slot_code I u k v=(if encoded_binding_ready use_code slot_code I u k v
    then Some (encoded_insert_binding use_code slot_code I u k v) else None)"

context environment_key_encoding
begin

lemma artifact_ready_exact:
  "encoded_environment_represents use_code slot_code I E \<Longrightarrow>
    encoded_artifact_ready use_code I u R \<longleftrightarrow>
      exact_formed (decode_finite_object R) \<and> u\<notin>environment_uses (decode_finite_environment E)"
  using lookup_artifact_ready_exact
  by (simp only: encoded_environment_represents_def encoded_artifact_ready_def; blast)

lemma binding_ready_exact:
  "encoded_environment_represents use_code slot_code I E \<Longrightarrow>
    encoded_binding_ready use_code slot_code I u k v \<longleftrightarrow>
      (\<exists>R. artifact_at (decode_finite_environment E) u R \<and> k\<in>rra_carrier (object_structure R)) \<and>
      v\<in>environment_uses (decode_finite_environment E) \<and>
      (\<forall>w. \<not>binds_slot (decode_finite_environment E) u k w)"
  using lookup_binding_ready_exact
  by (simp only: encoded_environment_represents_def encoded_binding_ready_def; blast)

theorem add_artifact_formed:
  assumes represented: "encoded_environment_represents use_code slot_code I E"
    and formed: "finite_environment_formed E" and result: "encoded_add_artifact use_code I u R=Some J"
  shows "finite_environment_formed (finite_add_artifact_use E u R)"
    "encoded_environment_represents use_code slot_code J (finite_add_artifact_use E u R)"
proof -
  have ready: "encoded_artifact_ready use_code I u R" and J: "J=encoded_insert_artifact use_code I u R"
    using result by (auto simp: encoded_add_artifact_def split: if_splits)
  show "finite_environment_formed (finite_add_artifact_use E u R)"
    by (rule lookup_added_artifact_formed[OF represented[unfolded encoded_environment_represents_def] formed
      ready[unfolded encoded_artifact_ready_def]])
  show "encoded_environment_represents use_code slot_code J (finite_add_artifact_use E u R)"
    by (simp only: J; rule insert_artifact_exact[OF represented])
qed

theorem add_binding_formed:
  assumes represented: "encoded_environment_represents use_code slot_code I E"
    and formed: "finite_environment_formed E" and result: "encoded_add_binding use_code slot_code I u k v=Some J"
  shows "finite_environment_formed (finite_add_source_bindings E u {|(k,v)|})"
    "encoded_environment_represents use_code slot_code J (finite_add_source_bindings E u {|(k,v)|})"
proof -
  have ready: "encoded_binding_ready use_code slot_code I u k v"
    and J: "J=encoded_insert_binding use_code slot_code I u k v"
    using result by (auto simp: encoded_add_binding_def split: if_splits)
  show "finite_environment_formed (finite_add_source_bindings E u {|(k,v)|})"
    by (rule lookup_added_binding_formed[OF represented[unfolded encoded_environment_represents_def] formed
      ready[unfolded encoded_binding_ready_def]])
  show "encoded_environment_represents use_code slot_code J (finite_add_source_bindings E u {|(k,v)|})"
    by (simp only: J; rule insert_binding_exact[OF represented])
qed

end

end
