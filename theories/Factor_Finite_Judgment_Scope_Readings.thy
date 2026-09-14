theory Factor_Finite_Judgment_Scope_Readings
  imports Factor_Finite_Judgment_Readings RRA_Finite_Generation_Checking
    RRA_Finite_Generation_Projections Factor_Generation_Scopes
begin

definition finite_whole_judgment_readings where
  "finite_whole_judgment_readings C=ffUnion (fimage (finite_judgment_value_readings C)
    (finite_carrier (finite_structure C)))"

theorem finite_whole_judgment_readings_exact:
  "(F,pu,pr,au,ar) |\<in>| finite_whole_judgment_readings C \<longleftrightarrow>
    (\<exists>r. judgment_value_quoted_at (decode_finite_object C) r (decode_finite_environment F) pu pr au ar)"
proof -
  have root: "r |\<in>| finite_carrier (finite_structure C)"
    if "judgment_value_quoted_at (decode_finite_object C) r (decode_finite_environment F) pu pr au ar" for r
    using judgment_value_quoted_anchor[OF that] by (simp add: anchor_formed_def)
  show ?thesis
    by (simp only: finite_whole_judgment_readings_def finite_union_image_member
      finite_judgment_value_readings_exact; use root in blast)
qed

lemma finite_whole_judgment_readings_complete:
  assumes quoted: "judgment_value_quoted_at (decode_finite_object C) r F pu pr au ar"
  shows "\<exists>Q. (Q,pu,pr,au,ar) |\<in>| finite_whole_judgment_readings C \<and> decode_finite_environment Q=F"
proof -
  have formed: "environment_formed F" using judgment_value_quoted_formed[OF quoted] by blast
  obtain Q where decode: "decode_finite_environment Q=F"
    using finite_environment_representation[OF formed] by blast
  have member: "(Q,pu,pr,au,ar) |\<in>| finite_whole_judgment_readings C"
    using quoted decode by (simp only: finite_whole_judgment_readings_exact; blast)
  show ?thesis using member decode by blast
qed

definition finite_generation_judgment_readings where
  "finite_generation_judgment_readings E gu gr G=(if finite_check_generation G E gu gr then
    (case generation_cause G of Finite_Whole C \<Rightarrow> finite_whole_judgment_readings C | _ \<Rightarrow> {||})
    else {||})"

theorem finite_generation_judgment_readings_exact:
  "(F,pu,pr,au,ar) |\<in>| finite_generation_judgment_readings E gu gr G \<longleftrightarrow>
    generation_judgment_scope_at (decode_finite_environment E) gu gr (decode_finite_generation G)
      (decode_finite_environment F) pu pr au ar"
  by (cases "generation_cause G"; cases "finite_check_generation G E gu gr")
    (simp only: finite_generation_judgment_readings_def if_True if_False finite_exact_target.case
      finite_whole_judgment_readings_exact;
     auto simp: generation_judgment_scope_at_def decode_finite_generation_selectors
       finite_check_generation_exact[symmetric])+

lemma finite_generation_judgment_readings_complete:
  assumes scope: "generation_judgment_scope_at (decode_finite_environment E) gu gr
    (decode_finite_generation G) F pu pr au ar"
  shows "\<exists>Q. (Q,pu,pr,au,ar) |\<in>| finite_generation_judgment_readings E gu gr G \<and>
    decode_finite_environment Q=F"
proof -
  obtain C r where quoted: "judgment_value_quoted_at C r F pu pr au ar"
    using generation_judgment_scope_cause[OF scope] by blast
  have formed: "environment_formed F" using judgment_value_quoted_formed[OF quoted] by blast
  obtain Q where decode: "decode_finite_environment Q=F"
    using finite_environment_representation[OF formed] by blast
  have member: "(Q,pu,pr,au,ar) |\<in>| finite_generation_judgment_readings E gu gr G"
    using scope decode by (simp only: finite_generation_judgment_readings_exact)
  show ?thesis using member decode by blast
qed

export_code finite_whole_judgment_readings finite_generation_judgment_readings checking SML

text \<open>
  Candidate roots are actual carrier positions of the whole recorded cause.
  The reader preserves every complete quotation layout and every admitted value
  presentation. The original generation must be present at its actual site.
  Scope recovery remains independent of leastness, truth and historical permission.
\<close>

end
