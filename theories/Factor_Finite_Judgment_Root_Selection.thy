theory Factor_Finite_Judgment_Root_Selection
  imports Factor_Finite_Judgment_Scope_Readings Factor_Finite_Quotation_Roots Finite_Supported_Images
begin

lemma finite_judgment_value_root_required:
  assumes member: "q |\<in>| finite_judgment_value_readings C r"
  shows "r |\<in>| finite_complete_data_root_candidates C"
proof -
  obtain F pu pr au ar where q: "q=(F,pu,pr,au,ar)" by (cases q) auto
  have quoted: "judgment_value_quoted_at (decode_finite_object C) r (decode_finite_environment F) pu pr au ar"
    using member by (simp only: q finite_judgment_value_readings_exact)
  obtain t where complete: "complete_data_quoted_at (decode_finite_object C) r t"
    using quoted unfolding judgment_value_quoted_at_def by blast
  show ?thesis using finite_complete_data_root_candidates_exact[OF complete] by simp
qed

definition finite_whole_judgment_readings_at_roots where
  "finite_whole_judgment_readings_at_roots C=ffUnion (fimage (finite_judgment_value_readings C)
    (finite_complete_data_root_candidates C))"

theorem finite_whole_judgment_readings_at_roots_exact:
  "finite_whole_judgment_readings_at_roots C=finite_whole_judgment_readings C"
  unfolding finite_whole_judgment_readings_at_roots_def finite_whole_judgment_readings_def
proof (rule finite_union_image_supported)
  fix r assume "r |\<in>| finite_complete_data_root_candidates C"
  then show "r |\<in>| finite_carrier (finite_structure C)"
    by (auto simp: finite_complete_data_root_candidates_def finite_unreferenced_positions_def)
next
  fix r q assume "r |\<in>| finite_carrier (finite_structure C)"
    and member: "q |\<in>| finite_judgment_value_readings C r"
  show "r |\<in>| finite_complete_data_root_candidates C"
    by (rule finite_judgment_value_root_required[OF member])
qed

export_code finite_whole_judgment_readings_at_roots checking SML

text \<open>
  Every successful value reading requires an unreferenced root in the complete
  source. The generic supported-image theorem restricts the search to those
  actual candidates and preserves the entire original result on every input.
  Root coordinates remain arbitrary.
\<close>

end
