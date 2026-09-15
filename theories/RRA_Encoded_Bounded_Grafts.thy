theory RRA_Encoded_Bounded_Grafts
  imports RRA_Finite_Graft_Bounds RRA_Encoded_Graft_Rows RRA_Digit_Allocated_Projection
begin

definition encoded_bounded_graft where
  "encoded_bounded_graft use_code slot_code q u A B=(let h=prefix_use_map [fst q] u;
    F=finite_enumerated_environment A B in
    if lookup_graft_ready (encoded_environment_artifacts use_code (snd q))
      (encoded_environment_bindings use_code slot_code (snd q)) h u F
    then Some (Suc (fst q),encoded_graft_rows use_code slot_code (snd q) h A B) else None)"

context environment_key_encoding
begin

theorem bounded_graft_valid:
  assumes valid: "encoded_bounded_valid use_code slot_code q" and step: "encoded_bounded_graft use_code slot_code q u A B=Some following"
  shows "encoded_bounded_valid use_code slot_code following"
proof -
  obtain E where formed: "finite_environment_formed E"
    and represented: "encoded_environment_represents use_code slot_code (snd q) E"
    and bound: "finite_environment_head_bound (fst q) E"
    using encoded_bounded_subject[OF valid] by blast
  let ?h="prefix_use_map [fst q] u"
  let ?F="finite_enumerated_environment A B"
  let ?G="finite_embedded_graft ?h E ?F"
  have lookups: "environment_lookup_represents (encoded_environment_artifacts use_code (snd q))
    (encoded_environment_bindings use_code slot_code (snd q)) E"
    using represented by (simp only: encoded_environment_represents_def)
  have ready: "lookup_graft_ready (encoded_environment_artifacts use_code (snd q))
      (encoded_environment_bindings use_code slot_code (snd q)) ?h u ?F"
    and following: "following=(Suc (fst q),encoded_graft_rows use_code slot_code (snd q) ?h A B)"
    using step by (auto simp: encoded_bounded_graft_def Let_def split: if_splits)
  have original_ready: "original_graft_ready ?h (decode_finite_environment E) u (decode_finite_environment ?F)"
  proof -
    have equation: "lookup_graft_ready (encoded_environment_artifacts use_code (snd q))
      (encoded_environment_bindings use_code slot_code (snd q)) ?h u ?F=
      original_graft_ready ?h (decode_finite_environment E) u (decode_finite_environment ?F)"
      by (rule lookup_graft_ready_original[OF lookups formed]; rule bounded_graft_prefix_embedding[OF bound])
    show ?thesis using ready equation by blast
  qed
  have shared: "finite_shared_graft_artifact E u ?F"
    using ready by (simp add: lookup_graft_ready_def lookup_shared_graft_artifact_exact[OF lookups])
  have new_formed: "finite_environment_formed ?G"
    using original_ready_graft_formed[OF original_ready]
    by (simp only: finite_environment_formed_correct finite_embedded_graft_exact)
  have new_representation: "encoded_environment_represents use_code slot_code
    (encoded_graft_rows use_code slot_code (snd q) ?h A B) ?G" by (rule graft_rows_exact[OF represented])
  have new_bound: "finite_environment_head_bound (Suc (fst q)) ?G"
    by (rule finite_graft_head_bound[OF bound shared_graft_source_bound[OF bound shared]])
  have new_lookups: "\<forall>v R. R |\<in>| encoded_environment_artifacts use_code
      (encoded_graft_rows use_code slot_code (snd q) ?h A B) v \<longrightarrow> use_word_head v<Suc (fst q)"
    using new_bound by (simp only: encoded_environment_head_bound[OF new_representation])
  show ?thesis using new_formed new_representation new_lookups
    by (auto simp: following encoded_bounded_valid_def)
qed

end

context environment_key_codec
begin

lemma bounded_view_formed_and_bounded:
  assumes valid: "encoded_bounded_valid use_code slot_code q"
  shows "finite_environment_formed (encoded_environment_view use_decode slot_decode (snd q))"
    "finite_environment_head_bound (fst q) (encoded_environment_view use_decode slot_decode (snd q))"
  using encoded_bounded_subject[OF valid] view_representation by metis+

theorem bounded_graft_view:
  assumes valid: "encoded_bounded_valid use_code slot_code q"
  shows "map_option (encoded_bounded_view use_decode slot_decode) (encoded_bounded_graft use_code slot_code q u A B)=
    (let E=encoded_environment_view use_decode slot_decode (snd q);F=finite_enumerated_environment A B;
      n=fst q;h=prefix_use_map [n] u in if finite_graft_prerequisites h E u F
      then Some (Suc n,finite_embedded_graft h E F) else None)"
  using bounded_view_formed_and_bounded(1)[OF valid]
  by (simp add: encoded_bounded_graft_def encoded_bounded_view_def Let_def
    lookup_graft_ready_finite[OF view_exact[unfolded encoded_environment_represents_def]] graft_rows_view)

end

end
