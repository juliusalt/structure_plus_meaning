theory RRA_Unary_Environment_Instance
  imports RRA_Encoded_Environment_Updates
begin

interpretation unary_environment: environment_key_codec use_binary_path address_binary_path
    decode_use_binary_path decode_address_binary_path
  by (unfold_locales) (auto simp: inj_on_def)

lemma unary_environment_artifacts:
  "encoded_environment_artifacts use_binary_path I=indexed_environment_artifacts I"
  by (simp add: encoded_environment_artifacts_def indexed_environment_artifacts_def indexed_artifacts_at_def fun_eq_iff)

lemma unary_environment_bindings:
  "encoded_environment_bindings use_binary_path address_binary_path I=indexed_environment_bindings I"
  by (simp add: encoded_environment_bindings_def indexed_environment_bindings_def fun_eq_iff)

lemma unary_environment_rows:
  "encoded_environment_rows use_binary_path address_binary_path A B=index_environment_rows A B"
  by (simp add: encoded_environment_rows_def index_environment_rows_def artifact_relation_store_def)

lemma unary_environment_insertions:
  "encoded_insert_artifact use_binary_path I u R=indexed_insert_artifact I u R"
  "encoded_insert_binding use_binary_path address_binary_path I u k v=indexed_insert_binding I u k v"
  by (simp_all add: encoded_insert_artifact_def encoded_insert_binding_def indexed_insert_artifact_def indexed_insert_binding_def)

lemma unary_environment_guards:
  "encoded_artifact_ready use_binary_path I u R=indexed_artifact_ready I u R"
  "encoded_binding_ready use_binary_path address_binary_path I u k v=indexed_binding_ready I u k v"
  by (simp_all add: encoded_artifact_ready_def encoded_binding_ready_def lookup_artifact_ready_def lookup_binding_ready_def
    unary_environment_artifacts unary_environment_bindings indexed_artifact_ready_def indexed_binding_ready_def)

lemma unary_environment_updates:
  "encoded_add_artifact use_binary_path I u R=indexed_add_artifact I u R"
  "encoded_add_binding use_binary_path address_binary_path I u k v=indexed_add_binding I u k v"
  by (simp_all add: encoded_add_artifact_def encoded_add_binding_def indexed_add_artifact_def indexed_add_binding_def
    unary_environment_guards unary_environment_insertions)

lemma unary_environment_view:
  "encoded_environment_view decode_use_binary_path decode_address_binary_path I=indexed_environment_view I"
proof -
  have encoded: "indexed_environment_represents I
    (encoded_environment_view decode_use_binary_path decode_address_binary_path I)"
    using unary_environment.view_exact[of I]
    by (simp only: encoded_environment_represents_def unary_environment_artifacts unary_environment_bindings
      indexed_environment_lookup_contract)
  show ?thesis by (rule indexed_environment_representation_unique[OF encoded indexed_environment_view_exact])
qed

export_code encoded_environment_rows encoded_environment_artifacts encoded_environment_bindings
  encoded_add_artifact encoded_add_binding encoded_environment_view checking SML

text \<open>
  The original concrete implementation instantiates every general operation
  exactly, including its whole view and optional update results. Existing
  accepted source closures remain unchanged. Other codecs must supply their
  own complete key contracts before these general results can be used.
\<close>

end
