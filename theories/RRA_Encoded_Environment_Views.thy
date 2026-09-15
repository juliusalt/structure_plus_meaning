theory RRA_Encoded_Environment_Views
  imports RRA_Encoded_Environments
begin

fun decode_encoded_artifact_row where
  "decode_encoded_artifact_row use_decode (path,R)=map_option (\<lambda>u. (u,R)) (use_decode path)"

fun decode_encoded_binding_row where
  "decode_encoded_binding_row use_decode slot_decode ((outer,inner),v)=(case use_decode outer of
    None \<Rightarrow> None | Some u \<Rightarrow>
      map_option (\<lambda>k. ((u,k),v)) (slot_decode inner))"

definition encoded_environment_view ::
  "(bool list\<Rightarrow>local_address option option)\<Rightarrow>
    (bool list\<Rightarrow>local_address option)\<Rightarrow>
    indexed_artifact_environment\<Rightarrow>local_address option finite_artifact_environment" where
  "encoded_environment_view use_decode slot_decode I=\<lparr>
    finite_environment_artifacts=finite_optional_image (decode_encoded_artifact_row use_decode)
      (relation_store_entries (indexed_artifact_store I)),
    finite_environment_bindings=finite_optional_image (decode_encoded_binding_row use_decode slot_decode)
      (nested_relation_entries (indexed_binding_store I))\<rparr>"

locale environment_key_codec = environment_key_encoding use_code slot_code
  for use_code :: "local_address option\<Rightarrow>bool list"
    and slot_code :: "local_address\<Rightarrow>bool list" +
  fixes use_decode :: "bool list\<Rightarrow>local_address option option"
    and slot_decode :: "bool list\<Rightarrow>local_address option"
  assumes use_decode_exact: "\<And>path u. use_decode path=Some u \<longleftrightarrow> path=use_code u"
    and slot_decode_exact: "\<And>path k. slot_decode path=Some k \<longleftrightarrow> path=slot_code k"
begin

lemma artifact_row_exact:
  "decode_encoded_artifact_row use_decode row=Some (u,R) \<longleftrightarrow> row=(use_code u,R)"
  by (cases row) (auto simp: use_decode_exact)

lemma binding_row_exact:
  "decode_encoded_binding_row use_decode slot_decode row=Some ((u,k),v) \<longleftrightarrow>
    row=((use_code u,slot_code k),v)"
  by (cases row) (auto simp: use_decode_exact slot_decode_exact split: prod.splits option.splits)

theorem view_exact:
  "encoded_environment_represents use_code slot_code I (encoded_environment_view use_decode slot_decode I)"
  by (auto simp: encoded_environment_represents_def environment_lookup_represents_def encoded_environment_view_def
    finite_optional_image_exact artifact_row_exact binding_row_exact
    relation_store_entries_exact nested_relation_entries_exact
    encoded_environment_artifacts_def encoded_environment_bindings_def split: option.splits; force)

theorem view_representation:
  "encoded_environment_represents use_code slot_code I E \<Longrightarrow>
    encoded_environment_view use_decode slot_decode I=E"
  unfolding encoded_environment_represents_def
  by (rule environment_lookup_representation_unique[OF view_exact[unfolded encoded_environment_represents_def]])

end

text \<open>
  A complete codec is required independently for the outer use and inner slot.
  Every original relation row is recovered from actual store entries, while
  undecodable presentation paths contribute no environment facts. The general
  lookup uniqueness result owns whole-view recovery for every such codec.
\<close>

end
