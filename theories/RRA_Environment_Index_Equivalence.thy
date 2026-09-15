theory RRA_Environment_Index_Equivalence
  imports RRA_Digit_Environment_Instance
begin

definition environment_indexes_equivalent ::
  "(local_address option\<Rightarrow>bool list)\<Rightarrow>(local_address\<Rightarrow>bool list)\<Rightarrow>
    indexed_artifact_environment\<Rightarrow>indexed_artifact_environment\<Rightarrow>bool" where
  "environment_indexes_equivalent use_code slot_code I J \<longleftrightarrow>
    encoded_environment_artifacts use_code I=indexed_environment_artifacts J \<and>
    encoded_environment_bindings use_code slot_code I=indexed_environment_bindings J"

lemma environment_indexes_same_subject:
  "encoded_environment_represents use_code slot_code I E \<Longrightarrow> indexed_environment_represents J E \<Longrightarrow>
    environment_indexes_equivalent use_code slot_code I J"
  using environment_lookup_transfer
  by (auto simp: encoded_environment_represents_def environment_indexes_equivalent_def)

lemma equivalent_environment_representation:
  "environment_indexes_equivalent use_code slot_code I J \<Longrightarrow>
    encoded_environment_represents use_code slot_code I E=indexed_environment_represents J E"
  by (simp add: environment_indexes_equivalent_def encoded_environment_represents_def indexed_environment_lookup_contract)

lemma equivalent_artifact_ready:
  "environment_indexes_equivalent use_code slot_code I J \<Longrightarrow>
    encoded_artifact_ready use_code I u R=indexed_artifact_ready J u R"
  by (simp add: environment_indexes_equivalent_def encoded_artifact_ready_def lookup_artifact_ready_def indexed_artifact_ready_def)

lemma equivalent_binding_ready:
  "environment_indexes_equivalent use_code slot_code I J \<Longrightarrow>
    encoded_binding_ready use_code slot_code I u k v=indexed_binding_ready J u k v"
  by (simp add: environment_indexes_equivalent_def encoded_binding_ready_def lookup_binding_ready_def indexed_binding_ready_def)

context environment_key_encoding
begin

lemma artifact_insert_equivalent:
  "environment_indexes_equivalent use_code slot_code I J \<Longrightarrow>
    environment_indexes_equivalent use_code slot_code (encoded_insert_artifact use_code I u R) (indexed_insert_artifact J u R)"
  by (auto simp: environment_indexes_equivalent_def fun_eq_iff)

lemma binding_insert_equivalent:
  "environment_indexes_equivalent use_code slot_code I J \<Longrightarrow>
    environment_indexes_equivalent use_code slot_code
      (encoded_insert_binding use_code slot_code I u k v) (indexed_insert_binding J u k v)"
  by (auto simp: environment_indexes_equivalent_def fun_eq_iff)

end

context environment_key_codec
begin

lemma original_index_exists:
  "\<exists>J::indexed_artifact_environment. environment_indexes_equivalent use_code slot_code I J"
proof -
  obtain J::indexed_artifact_environment where original:
    "indexed_environment_represents J (encoded_environment_view use_decode slot_decode I)"
    using finite_environment_index_exists[of "encoded_environment_view use_decode slot_decode I"] by blast
  show ?thesis using environment_indexes_same_subject[OF view_exact original] by blast
qed

lemma equivalent_environment_view:
  assumes equivalent: "environment_indexes_equivalent use_code slot_code I J"
  shows "encoded_environment_view use_decode slot_decode I=indexed_environment_view J"
proof -
  have represented: "indexed_environment_represents J (encoded_environment_view use_decode slot_decode I)"
    using equivalent_environment_representation[OF equivalent, of "encoded_environment_view use_decode slot_decode I"]
      view_exact[of I] by blast
  show ?thesis using indexed_environment_view_representation[OF represented] by simp
qed

end

text \<open>
  Equivalence concerns every original lookup and its complete environment.
  Physical index equality or sharing is not assumed. The reference index is a
  mathematical witness; local update code does not reconstruct or traverse it.
\<close>

end
