theory RRA_Indexed_Environment_Views
  imports RRA_Formed_Environment_Stores Binary_Store_Entries RRA_Binary_Path_Decoding Finite_Optional_Images
begin

fun decode_indexed_artifact_row where
  "decode_indexed_artifact_row (path,R)=map_option (\<lambda>u. (u,R)) (decode_use_binary_path path)"

fun decode_indexed_binding_row where
  "decode_indexed_binding_row ((outer,inner),v)=(case decode_use_binary_path outer of
    None \<Rightarrow> None | Some u \<Rightarrow>
      map_option (\<lambda>k. ((u,k),v)) (decode_address_binary_path inner))"

lemma decode_indexed_artifact_row_exact:
  "decode_indexed_artifact_row row=Some (u,R) \<longleftrightarrow> row=(use_binary_path u,R)"
  by (cases row) auto

lemma decode_indexed_binding_row_exact:
  "decode_indexed_binding_row row=Some ((u,k),v) \<longleftrightarrow>
    row=((use_binary_path u,address_binary_path k),v)"
  by (cases row) (auto split: prod.splits option.splits)

definition indexed_environment_view :: "indexed_artifact_environment \<Rightarrow> local_address option finite_artifact_environment" where
  "indexed_environment_view I=\<lparr>
    finite_environment_artifacts=finite_optional_image decode_indexed_artifact_row
      (relation_store_entries (indexed_artifact_store I)),
    finite_environment_bindings=finite_optional_image decode_indexed_binding_row
      (nested_relation_entries (indexed_binding_store I))\<rparr>"

theorem indexed_environment_view_exact:
  "indexed_environment_represents I (indexed_environment_view I)"
  by (auto simp: indexed_environment_represents_def indexed_environment_view_def
    finite_optional_image_exact decode_indexed_artifact_row_exact decode_indexed_binding_row_exact
    relation_store_entries_exact nested_relation_entries_exact
    indexed_environment_artifacts_def indexed_artifacts_at_def indexed_environment_bindings_def
    split: option.splits; force)

lemma indexed_environment_representation_unique:
  fixes E F :: "local_address option finite_artifact_environment"
  assumes "indexed_environment_represents I E" "indexed_environment_represents I F"
  shows "E=F"
proof -
  have art: "finite_environment_artifacts E=finite_environment_artifacts F"
    using assms by (auto simp: indexed_environment_represents_def intro!: fset_inject[THEN iffD1] set_eqI)
  have bindings: "finite_environment_bindings E=finite_environment_bindings F"
    using assms by (auto simp: indexed_environment_represents_def intro!: fset_inject[THEN iffD1] set_eqI)
  show ?thesis using art bindings by (cases E; cases F) simp
qed

theorem indexed_environment_view_representation:
  "indexed_environment_represents I E \<Longrightarrow> indexed_environment_view I=E"
  by (rule indexed_environment_representation_unique[OF indexed_environment_view_exact])

corollary environment_store_view_formed:
  "finite_environment_formed (indexed_environment_view (raw_environment_store S))"
  using environment_store_formed[of S] indexed_environment_view_representation by metis

text \<open>
  The view recovers the complete original artifact and binding relations from
  the actual store. Its equation covers every use and slot. Traversing the
  whole store is an observation and export operation; local updates do not
  invoke it. Keys outside the declared encoding are presentation structure
  and receive no environment entries from this decoder.
\<close>

end
