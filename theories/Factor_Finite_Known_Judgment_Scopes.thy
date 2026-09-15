theory Factor_Finite_Known_Judgment_Scopes
  imports Factor_Finite_Judgment_Scope_Readings Factor_Finite_Judgment_Quotation
begin

theorem finite_whole_judgment_readings_singleton:
  assumes quoted: "judgment_value_quoted_at (decode_finite_object C) r (decode_finite_environment J) pu pr au ar"
  shows "finite_whole_judgment_readings C={|(J,pu,pr,au,ar)|}"
proof -
  have member: "(J,pu,pr,au,ar) |\<in>| finite_whole_judgment_readings C"
    using quoted by (simp only: finite_whole_judgment_readings_exact; blast)
  have only: "q=(J,pu,pr,au,ar)" if q: "q |\<in>| finite_whole_judgment_readings C" for q
  proof -
    obtain F qu qr bu br where shape: "q=(F,qu,qr,bu,br)" by (cases q) auto
    obtain s where other: "judgment_value_quoted_at (decode_finite_object C) s (decode_finite_environment F) qu qr bu br"
      using q by (simp only: shape finite_whole_judgment_readings_exact; blast)
    have same: "J=F \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br"
      using judgment_value_whole_unique[OF quoted other]
      by (simp only: decode_finite_environment_injective; blast)
    show ?thesis using same by (simp add: shape)
  qed
  show ?thesis
  proof (rule fset_eqI)
    fix q
    show "q |\<in>| finite_whole_judgment_readings C \<longleftrightarrow> q |\<in>| {|(J,pu,pr,au,ar)|}"
    proof
      assume "q |\<in>| finite_whole_judgment_readings C"
      then have "q=(J,pu,pr,au,ar)" by (rule only)
      then show "q |\<in>| {|(J,pu,pr,au,ar)|}" by simp
    next
      assume "q |\<in>| {|(J,pu,pr,au,ar)|}"
      then have "q=(J,pu,pr,au,ar)" by simp
      then show "q |\<in>| finite_whole_judgment_readings C" using member by simp
    qed
  qed
qed

corollary finite_native_judgment_quote_scopes:
  "finite_native_judgment_quote E pu pr au ar=Some (J,C) \<Longrightarrow>
    finite_whole_judgment_readings C={|(J,pu,pr,au,ar)|}"
  by (rule finite_whole_judgment_readings_singleton[OF finite_native_judgment_quote_correct(1)])

theorem finite_generation_judgment_readings_known:
  assumes actual: "finite_check_generation G E gu gr"
    and cause: "generation_cause G=Finite_Whole C"
    and quoted: "judgment_value_quoted_at (decode_finite_object C) r (decode_finite_environment J) pu pr au ar"
  shows "finite_generation_judgment_readings E gu gr G={|(J,pu,pr,au,ar)|}"
  by (simp only: finite_generation_judgment_readings_def actual if_True cause finite_exact_target.case
    finite_whole_judgment_readings_singleton[OF quoted])

text \<open>
  The existing whole-quotation uniqueness and injective finite environment view
  determine the complete finite scope family from an actual quoted judgment.
  The generation equation additionally requires the actual original generation
  reading and its complete cause target. Arbitrary supplied scope values do not
  acquire these premises.
\<close>

end
