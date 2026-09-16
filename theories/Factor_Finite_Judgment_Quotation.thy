theory Factor_Finite_Judgment_Quotation
  imports Factor_Executable_Judgment_Retention Factor_Executable_Environment_Values_Base Factor_Finite_Data_Syntax Factor_Judgment_Values
begin

definition finite_judgment_term where
  "finite_judgment_term E pu pr au ar=Pair_Term (finite_environment_term E)
    (Pair_Term (site_data_term pu pr) (site_data_term au ar))"

lemma finite_judgment_term_self_contained [simp]:
  "self_contained_term (finite_judgment_term E pu pr au ar)"
  by (simp add: finite_judgment_term_def)

theorem finite_judgment_term_exact:
  "judgment_value_presents F qu qr bu br (finite_judgment_term E pu pr au ar) \<longleftrightarrow>
    finite_environment_formed E \<and> F=decode_finite_environment E \<and>
    qu=pu \<and> qr=pr \<and> bu=au \<and> br=ar \<and>
    (pu,pr) |\<in>| finite_environment_positions E \<and>
    (au,ar) |\<in>| finite_environment_positions E"
proof -
  have environment: "environment_value_presents F (finite_environment_term E) \<longleftrightarrow>
    finite_environment_formed E \<and> F=decode_finite_environment E"
    using finite_environment_value_exact[where E=F and C=E] by simp
  show ?thesis by (auto simp: finite_judgment_term_def judgment_value_presents_def environment
    finite_environment_positions_correct; force)
qed

definition finite_native_judgment_quote where
  "finite_native_judgment_quote E pu pr au ar=(if finite_native_judgment_ready E pu pr au ar then
    let J=finite_native_judgment_environment E pu pr au ar in
      map_option (Pair J) (finite_data_syntax (finite_judgment_term J pu pr au ar)) else None)"

lemma finite_native_judgment_quote_result:
  "finite_native_judgment_quote E pu pr au ar=Some (J,C) \<longleftrightarrow>
    finite_native_judgment_ready E pu pr au ar \<and>
    J=finite_native_judgment_environment E pu pr au ar \<and>
    finite_data_syntax (finite_judgment_term J pu pr au ar)=Some C"
  by (auto simp: finite_native_judgment_quote_def Let_def split: option.splits if_splits)

theorem finite_native_judgment_quote_domain:
  "(\<exists>J C. finite_native_judgment_quote E pu pr au ar=Some (J,C)) \<longleftrightarrow>
    finite_native_judgment_ready E pu pr au ar"
proof -
  have available: "finite_data_syntax (finite_judgment_term J pu pr au ar)\<noteq>None" for J
    by (simp add: finite_data_syntax_domain)
  show ?thesis using available
    by (simp only: finite_native_judgment_quote_result; cases "finite_data_syntax
      (finite_judgment_term (finite_native_judgment_environment E pu pr au ar) pu pr au ar)"; auto)
qed

theorem finite_native_judgment_quote_correct:
  assumes result: "finite_native_judgment_quote E pu pr au ar=Some (J,C)"
  shows "judgment_value_quoted_at (decode_finite_object C) [] (decode_finite_environment J) pu pr au ar"
    "decode_finite_environment J=native_judgment_environment (decode_finite_environment E) pu pr au ar"
    "decode_finite_environment J=native_judgment_environment (decode_finite_environment J) pu pr au ar"
    "environment_included (decode_finite_environment J) (decode_finite_environment E)"
    "native_package_environment (decode_finite_environment J) pu pr=
      native_package_environment (decode_finite_environment E) pu pr"
proof -
  have ready: "finite_native_judgment_ready E pu pr au ar"
    and scoped: "J=finite_native_judgment_environment E pu pr au ar"
    and built: "finite_data_syntax (finite_judgment_term J pu pr au ar)=Some C"
    using result by (simp only: finite_native_judgment_quote_result; blast)+
  obtain P d t I K where package: "native_package_at (decode_finite_environment E) pu pr P"
    and app: "native_application_at (decode_finite_environment E) au ar d t I K"
    using ready by (simp only: finite_native_judgment_ready_correct; blast)
  have actual: "decode_finite_environment J=native_judgment_environment (decode_finite_environment E) pu pr au ar"
    by (simp only: scoped finite_native_judgment_environment_correct)
  have kept_package: "native_package_at (decode_finite_environment J) pu pr P"
    and kept_app: "native_application_at (decode_finite_environment J) au ar d t I K"
    and formed: "environment_formed (decode_finite_environment J)"
    using native_judgment_environment_recovers[OF package app] by (simp_all only: actual)
  have positions: "(pu,pr) |\<in>| finite_environment_positions J"
    "(au,ar) |\<in>| finite_environment_positions J"
    using native_judgment_positions[OF kept_package kept_app]
    by (simp_all only: finite_environment_positions_correct)
  have presented: "judgment_value_presents (decode_finite_environment J) pu pr au ar
    (finite_judgment_term J pu pr au ar)"
    using formed positions by (simp only: finite_judgment_term_exact
      finite_environment_formed_correct; blast)
  have term_formed: "term_formed (finite_judgment_term J pu pr au ar)"
    using judgment_value_presents_formed[OF presented] by blast
  have quote: "complete_data_quoted_at (decode_finite_object C) [] (finite_judgment_term J pu pr au ar)"
    by (rule finite_data_syntax_complete_quotation[OF term_formed built])
  show "judgment_value_quoted_at (decode_finite_object C) [] (decode_finite_environment J) pu pr au ar"
    using presented quote by (simp only: judgment_value_quoted_at_def; blast)
  show "decode_finite_environment J=native_judgment_environment (decode_finite_environment E) pu pr au ar"
    by (rule actual)
  show "decode_finite_environment J=native_judgment_environment (decode_finite_environment J) pu pr au ar"
    using native_judgment_environment_idempotent[OF package app] by (simp only: actual)
  show "environment_included (decode_finite_environment J) (decode_finite_environment E)"
    by (simp only: actual; rule native_judgment_environment_included)
  show "native_package_environment (decode_finite_environment J) pu pr=
    native_package_environment (decode_finite_environment E) pu pr"
    by (simp only: actual; rule native_judgment_program_environment[OF package app])
qed

export_code finite_native_judgment_quote checking SML

text \<open>
  The actual program and call are read before their least environment is
  computed and quoted. The complete environment and both exact sites determine
  the quoted value. Its output recovers the original minimal judgment scope;
  quotation alone does not establish that the call is true.
\<close>

end
