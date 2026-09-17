theory Factor_Finite_Policy_Causes
  imports Factor_Finite_Certified_Causes Factor_Policy_Causes Factor_Finite_Application_Value_Selection
begin

definition finite_policy_cause_alignment where
  "finite_policy_cause_alignment K pu pr d R q=(case q of (F,qu,qr,au,ar) \<Rightarrow>
    qu=pu \<and> qr=pr \<and> finite_native_package_environment F qu qr=finite_native_package_environment K pu pr \<and>
    finite_application_value_ready F au ar d (Finite_Target (Finite_Whole R)))"

lemma finite_policy_cause_alignment_exact:
  "finite_policy_cause_alignment K pu pr d R (F,qu,qr,au,ar) \<longleftrightarrow>
    qu=pu \<and> qr=pr \<and>
    native_package_environment (decode_finite_environment F) qu qr=
      native_package_environment (decode_finite_environment K) pu pr \<and>
    (\<exists>I A. native_application_at (decode_finite_environment F) au ar d
      (Target_Term (Whole_Artifact (decode_finite_object R))) I A)"
  by (simp only: finite_policy_cause_alignment_def case_prod_conv
    decode_finite_environment_injective[symmetric] finite_native_package_environment_correct
    finite_application_value_ready_exact decode_finite_term.simps decode_finite_target.simps)

lemma finite_policy_package_available:
  "finite_native_package_readings K pu pr\<noteq>{||} \<longleftrightarrow>
    (\<exists>P. native_package_at (decode_finite_environment K) pu pr P)"
proof
  assume "finite_native_package_readings K pu pr\<noteq>{||}"
  then obtain P where "P |\<in>| finite_native_package_readings K pu pr" by auto
  then show "\<exists>P. native_package_at (decode_finite_environment K) pu pr P"
    by (simp only: finite_native_package_readings_correct; blast)
next
  assume "\<exists>P. native_package_at (decode_finite_environment K) pu pr P"
  then obtain P where package: "native_package_at (decode_finite_environment K) pu pr P" by blast
  show "finite_native_package_readings K pu pr\<noteq>{||}"
    using finite_native_package_readings_complete[OF package] by auto
qed

definition finite_certified_policy_cause where
  "finite_certified_policy_cause K pu pr d E gu gr G H root R=(
    finite_native_package_readings K pu pr\<noteq>{||} \<and>
    finite_certified_base_cause E gu gr G H root R \<and>
    fBex (finite_generation_judgment_readings E gu gr G) (finite_policy_cause_alignment K pu pr d R))"

theorem finite_certified_policy_cause_exact:
  "finite_certified_policy_cause K pu pr d E gu gr G H root R \<longleftrightarrow>
    certified_policy_cause_at (decode_finite_environment K) pu pr d
      (decode_finite_environment E) gu gr (decode_finite_generation G)
      (decode_finite_environment H) root (decode_finite_object R)"
proof -
  have aligned: "fBex (finite_generation_judgment_readings E gu gr G) (finite_policy_cause_alignment K pu pr d R)
    \<longleftrightarrow> (\<exists>F au ar I A. generation_judgment_scope_at (decode_finite_environment E) gu gr
      (decode_finite_generation G) F pu pr au ar \<and>
      native_package_environment F pu pr=native_package_environment (decode_finite_environment K) pu pr \<and>
      native_application_at F au ar d (Target_Term (Whole_Artifact (decode_finite_object R))) I A)"
  proof
    assume "fBex (finite_generation_judgment_readings E gu gr G) (finite_policy_cause_alignment K pu pr d R)"
    then obtain F qu qr au ar where member: "(F,qu,qr,au,ar) |\<in>| finite_generation_judgment_readings E gu gr G"
      and alignment: "finite_policy_cause_alignment K pu pr d R (F,qu,qr,au,ar)"
      by (auto simp: Bex_def split_paired_Ex)
    show "\<exists>F au ar I A. generation_judgment_scope_at (decode_finite_environment E) gu gr
      (decode_finite_generation G) F pu pr au ar \<and>
      native_package_environment F pu pr=native_package_environment (decode_finite_environment K) pu pr \<and>
      native_application_at F au ar d (Target_Term (Whole_Artifact (decode_finite_object R))) I A"
      using member alignment by (simp only: finite_generation_judgment_readings_exact finite_policy_cause_alignment_exact; blast)
  next
    assume "\<exists>F au ar I A. generation_judgment_scope_at (decode_finite_environment E) gu gr
      (decode_finite_generation G) F pu pr au ar \<and>
      native_package_environment F pu pr=native_package_environment (decode_finite_environment K) pu pr \<and>
      native_application_at F au ar d (Target_Term (Whole_Artifact (decode_finite_object R))) I A"
    then obtain F au ar I A where scope: "generation_judgment_scope_at (decode_finite_environment E) gu gr
      (decode_finite_generation G) F pu pr au ar"
      and same: "native_package_environment F pu pr=native_package_environment (decode_finite_environment K) pu pr"
      and app: "native_application_at F au ar d (Target_Term (Whole_Artifact (decode_finite_object R))) I A" by blast
    obtain M where member: "(M,pu,pr,au,ar) |\<in>| finite_generation_judgment_readings E gu gr G"
      and decode: "decode_finite_environment M=F"
      using finite_generation_judgment_readings_complete[OF scope] by blast
    have alignment: "finite_policy_cause_alignment K pu pr d R (M,pu,pr,au,ar)"
      using same app by (simp only: finite_policy_cause_alignment_exact decode; blast)
    show "fBex (finite_generation_judgment_readings E gu gr G) (finite_policy_cause_alignment K pu pr d R)"
      unfolding Bex_def
      by (rule exI[of _ "(M,pu,pr,au,ar)"]) (use member alignment in auto)
  qed
  show ?thesis by (simp only: finite_certified_policy_cause_def certified_policy_cause_at_def
    finite_policy_package_available finite_certified_base_cause_exact aligned)
qed

end
