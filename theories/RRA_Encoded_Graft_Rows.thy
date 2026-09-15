theory RRA_Encoded_Graft_Rows
  imports RRA_Encoded_Environment_Merges RRA_Finite_Embedded_Grafts RRA_Digit_Environment_Instance
begin

definition rename_artifact_rows where
  "rename_artifact_rows h A=map (\<lambda>(u,R). (h u,R)) A"

definition rename_binding_rows where
  "rename_binding_rows h B=map (\<lambda>((u,k),v). ((h u,k),h v)) B"

lemma renamed_environment_rows:
  "finite_enumerated_environment (rename_artifact_rows h A) (rename_binding_rows h B)=
    finite_rename_environment h (finite_enumerated_environment A B)"
  by (simp add: finite_enumerated_environment_def finite_rename_environment_def
    rename_artifact_rows_def rename_binding_rows_def fset_of_list_map)

definition encoded_graft_rows where
  "encoded_graft_rows use_code slot_code I h A B=encoded_merge_rows use_code slot_code I
    (rename_artifact_rows h A) (rename_binding_rows h B)"

context environment_key_encoding
begin

theorem graft_rows_exact:
  "encoded_environment_represents use_code slot_code I E \<Longrightarrow>
    encoded_environment_represents use_code slot_code (encoded_graft_rows use_code slot_code I h A B)
      (finite_embedded_graft h E (finite_enumerated_environment A B))"
  by (simp only: encoded_graft_rows_def finite_embedded_graft_def renamed_environment_rows[symmetric];
    rule merge_rows_exact)

end

context environment_key_codec
begin

theorem graft_rows_view:
  "encoded_environment_view use_decode slot_decode (encoded_graft_rows use_code slot_code I h A B)=
    finite_embedded_graft h (encoded_environment_view use_decode slot_decode I) (finite_enumerated_environment A B)"
  by (simp only: encoded_graft_rows_def merge_rows_view renamed_environment_rows finite_embedded_graft_def)

end

export_code encoded_graft_rows digit_use_path digit_address_path checking SML

end
