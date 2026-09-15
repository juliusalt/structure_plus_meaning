theory Factor_Constructed_Judgment_Sources
  imports Factor_Certified_Cause_Variants Factor_Finite_Known_Judgment_Scopes
begin

lemma data_collection_presents_reverse:
  "data_collection_presents P A (data_list_term (rev ts)) \<longleftrightarrow>
    data_collection_presents P A (data_list_term ts)"
proof -
  have forward: "data_collection_presents P A (data_list_term ts) \<Longrightarrow>
      data_collection_presents P A (data_list_term (rev ts))" for ts
  proof -
    assume original: "data_collection_presents P A (data_list_term ts)"
    obtain xs where rows: "distinct xs" "set xs=A" "list_all2 P xs ts"
      using original by (auto simp: data_collection_presents_def data_list_term_injective)
    have "distinct (rev xs)" "set (rev xs)=A" "list_all2 P (rev xs) (rev ts)"
      using rows by simp_all
    then show "data_collection_presents P A (data_list_term (rev ts))"
      by (simp only: data_collection_presents_def; blast)
  qed
  show ?thesis using forward[of ts] forward[of "rev ts"] by auto
qed

lemma reversed_environment_value_exact:
  "environment_value_presents E (reversed_environment_term F) \<longleftrightarrow>
    finite_environment_formed F \<and> E=decode_finite_environment F"
  using finite_environment_value_exact[of E F]
  by (simp del: rev_map add: reversed_environment_term_def finite_environment_term_def
      environment_value_presents_def data_collection_presents_reverse rev_map[symmetric])

lemma reversed_judgment_value_exact:
  "judgment_value_presents F qu qr bu br (reversed_judgment_term E pu pr au ar) \<longleftrightarrow>
    finite_environment_formed E \<and> F=decode_finite_environment E \<and>
    qu=pu \<and> qr=pr \<and> bu=au \<and> br=ar \<and>
    (pu,pr) |\<in>| finite_environment_positions E \<and>
    (au,ar) |\<in>| finite_environment_positions E"
proof -
  have environment: "environment_value_presents F (reversed_environment_term E)=
      environment_value_presents F (finite_environment_term E)"
    using finite_environment_value_exact[of F E]
    by (simp add: reversed_environment_value_exact)
  have same_judgment: "judgment_value_presents F qu qr bu br (reversed_judgment_term E pu pr au ar)=
      judgment_value_presents F qu qr bu br (finite_judgment_term E pu pr au ar)"
    by (simp add: reversed_judgment_term_def finite_judgment_term_def
        judgment_value_presents_def environment)
  show ?thesis by (simp only: same_judgment finite_judgment_term_exact)
qed

theorem finite_constructed_judgment_scopes:
  assumes built: "finite_data_syntax t=Some C"
    and presented: "judgment_value_presents (decode_finite_environment J) pu pr au ar t"
  shows "finite_whole_judgment_readings C={|(J,pu,pr,au,ar)|}"
proof -
  have formed: "term_formed t" using judgment_value_presents_formed[OF presented] by blast
  have complete: "complete_data_quoted_at (decode_finite_object C) [] t"
    by (rule finite_data_syntax_complete_quotation[OF formed built])
  have quoted: "judgment_value_quoted_at (decode_finite_object C) [] (decode_finite_environment J) pu pr au ar"
    using presented complete by (simp only: judgment_value_quoted_at_def; blast)
  show ?thesis by (rule finite_whole_judgment_readings_singleton[OF quoted])
qed

definition checked_judgment_source where
  "checked_judgment_source reversed E pu pr au ar=(
    if finite_environment_formed E \<and> (pu,pr) |\<in>| finite_environment_positions E \<and>
      (au,ar) |\<in>| finite_environment_positions E then
      map_option (Pair E) (finite_data_syntax (if reversed then reversed_judgment_term E pu pr au ar
        else finite_judgment_term E pu pr au ar)) else None)"

theorem checked_judgment_source_scopes:
  "checked_judgment_source reversed E pu pr au ar=Some (J,C) \<Longrightarrow>
    finite_whole_judgment_readings C={|(J,pu,pr,au,ar)|}"
proof -
  assume result: "checked_judgment_source reversed E pu pr au ar=Some (J,C)"
  have same: "J=E" and formed: "finite_environment_formed E"
    and program: "(pu,pr) |\<in>| finite_environment_positions E"
    and app: "(au,ar) |\<in>| finite_environment_positions E"
    and built: "finite_data_syntax (if reversed then reversed_judgment_term E pu pr au ar
      else finite_judgment_term E pu pr au ar)=Some C"
    using result by (auto simp: checked_judgment_source_def split: if_splits option.splits)
  have presented: "judgment_value_presents (decode_finite_environment J) pu pr au ar
      (if reversed then reversed_judgment_term E pu pr au ar else finite_judgment_term E pu pr au ar)"
    using same formed program app by (simp add: reversed_judgment_value_exact finite_judgment_term_exact)
  show ?thesis by (rule finite_constructed_judgment_scopes[OF built presented])
qed

definition constructed_judgment_sources where
  "constructed_judgment_sources E pu pr au ar=(case finite_native_judgment_quote E pu pr au ar of
    None \<Rightarrow> [] | Some (J,C) \<Rightarrow>
      [Some (J,C),checked_judgment_source False E pu pr au ar,
        checked_judgment_source True J pu pr au ar])"

theorem constructed_judgment_sources_scopes:
  "Some (J,C)\<in>set (constructed_judgment_sources E pu pr au ar) \<Longrightarrow>
    finite_whole_judgment_readings C={|(J,pu,pr,au,ar)|}"
proof -
  assume member: "Some (J,C)\<in>set (constructed_judgment_sources E pu pr au ar)"
  show ?thesis
  proof (cases "finite_native_judgment_quote E pu pr au ar")
    case None
    then show ?thesis using member by (simp add: constructed_judgment_sources_def)
  next
    case (Some entry)
    obtain A D where pair: "entry=(A,D)" by (cases entry) auto
    have quoted: "finite_native_judgment_quote E pu pr au ar=Some (A,D)" using Some pair by simp
    have alternatives: "(J=A \<and> C=D) \<or>
        checked_judgment_source False E pu pr au ar=Some (J,C) \<or>
        checked_judgment_source True A pu pr au ar=Some (J,C)"
      using member by (auto simp: constructed_judgment_sources_def quoted)
    then consider (original) "J=A" "C=D"
      | (whole_source) "checked_judgment_source False E pu pr au ar=Some (J,C)"
      | (reverse_source) "checked_judgment_source True A pu pr au ar=Some (J,C)" by blast
    then show ?thesis
    proof cases
      case original
      then show ?thesis using finite_native_judgment_quote_scopes[OF quoted] by simp
    next
      case whole_source
      show ?thesis by (rule checked_judgment_source_scopes[OF whole_source])
    next
      case reverse_source
      show ?thesis by (rule checked_judgment_source_scopes[OF reverse_source])
    qed
  qed
qed

text \<open>The checked constructors retain the least, complete source, and
  reversed complete presentations. Their actual formation and site guards,
  data construction, and whole-quotation uniqueness establish each complete
  scope. Reversing a finite collection does not reorder or discard occurrences
  inside its represented artifacts or counted-data fields.\<close>

end
