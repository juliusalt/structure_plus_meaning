theory RRA_Finite_Embedded_Grafts
  imports RRA_General_Environment_Grafts
begin

definition finite_embedded_graft where
  "finite_embedded_graft h E F=finite_merge_environment E (finite_rename_environment h F)"

lemma finite_embedded_graft_exact:
  "decode_finite_environment (finite_embedded_graft h E F)=
    embedded_graft_environment h (decode_finite_environment E) (decode_finite_environment F)"
  by (simp add: finite_embedded_graft_def embedded_graft_environment_def)

definition finite_compact_graft where
  "finite_compact_graft E u F=finite_embedded_graft (finite_compact_use_map (finite_environment_uses E) u) E F"

lemma finite_original_graft_instance:
  "finite_graft_environment E u F=finite_embedded_graft (finite_fresh_use_map (finite_environment_uses E) u) E F"
  by (simp only: finite_graft_environment_def finite_embedded_graft_def)

lemma original_graft_instance:
  "graft_environment E u F=embedded_graft_environment (fresh_use_map (environment_uses E) u) E F"
  by (simp only: graft_environment_def embedded_graft_environment_def)

lemma compact_graft_instance:
  "decode_finite_environment (finite_compact_graft E u F)=embedded_graft_environment
    (compact_use_map (environment_uses (decode_finite_environment E)) u)
      (decode_finite_environment E) (decode_finite_environment F)"
  by (simp add: finite_compact_graft_def finite_embedded_graft_exact finite_compact_use_map_exact
    finite_environment_uses_correct)

theorem compact_graft_formed:
  assumes old: "finite_environment_formed E" and imported: "finite_environment_formed F"
    and source: "artifact_at (decode_finite_environment E) u R"
    and boundary: "artifact_at (decode_finite_environment F) None R"
  shows "finite_environment_formed (finite_compact_graft E u F) \<longleftrightarrow>
    boundary_bindings_compatible (compact_use_map (environment_uses (decode_finite_environment E)) u)
      (decode_finite_environment E) u (decode_finite_environment F)"
proof -
  have ef: "environment_formed (decode_finite_environment E)" using old by (simp only: finite_environment_formed_correct)
  have ff: "environment_formed (decode_finite_environment F)" using imported by (simp only: finite_environment_formed_correct)
  have embedding: "boundary_use_embedding (environment_uses (decode_finite_environment E)) u
      (compact_use_map (environment_uses (decode_finite_environment E)) u)"
    by (rule compact_boundary_embedding; rule environment_uses_finite[OF ef])
  interpret graft: environment_graft "decode_finite_environment E" "decode_finite_environment F" u R
      "compact_use_map (environment_uses (decode_finite_environment E)) u"
    by (unfold_locales) (rule ef, rule ff, rule source, rule boundary, rule embedding)
  show ?thesis by (simp only: finite_environment_formed_correct compact_graft_instance graft.formed_exact)
qed

export_code finite_embedded_graft finite_compact_graft checking SML

end
