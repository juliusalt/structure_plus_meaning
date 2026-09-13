theory Factor_Finite_Requirement_Term_Observations
  imports Factor_Finite_Native_Term_Observations Factor_Finite_Requirement_Goals
begin

definition finite_admission_requirements_test where
  "finite_admission_requirements_test gs A t=(finite_term_formed t \<and>
    list_all (\<lambda>g. finite_admission_goal_test A g t) gs)"

theorem finite_native_requirement_terms_exact:
  assumes evaluated: "finite_native_program_evaluation E u r (finite_program_term_demand P T)=Some (P,A)"
    and supported: "finite_admission_requirements_supported gs P"
  shows "fset (ffilter (finite_admission_requirements_test gs A) T)=
    {t\<in>fset T. admission_requirements_hold (positive_meaning (decode_finite_system P)) gs (decode_finite_term t)}"
proof -
  have each: "finite_admission_goal_test A g t \<longleftrightarrow>
      admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)"
    if goal: "g\<in>set gs" and tested: "t\<in>fset T" for g t
  proof -
    have support: "finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
      using supported goal by (simp only: finite_admission_requirements_supported_def list_all_iff; blast)
    show ?thesis using finite_native_goal_terms_exact[OF evaluated support] tested by auto
  qed
  show ?thesis using each by (auto simp: finite_admission_requirements_test_def
    finite_term_formed_correct list_all_iff admission_requirements_hold_def)
qed

definition finite_native_requirement_term_observation where
  "finite_native_requirement_term_observation E u r gs T=finite_native_term_observation
    (finite_admission_requirements_supported gs) (finite_admission_requirements_test gs) E u r T"

theorem finite_native_requirement_term_observation_semantics:
  "finite_native_requirement_term_observation E u r gs T=Some (P,M) \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    (\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P)) \<and>
    (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A) \<and>
    fset M={t\<in>fset T.
      admission_requirements_hold (positive_meaning (decode_finite_system P)) gs (decode_finite_term t)}"
proof -
  have exact: "finite_native_term_observation (finite_admission_requirements_supported gs)
      (finite_admission_requirements_test gs) E u r T=Some (P,M) \<longleftrightarrow>
      native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
      finite_admission_requirements_supported gs P \<and>
      (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A) \<and>
      fset M={t\<in>fset T. admission_requirements_hold (positive_meaning (decode_finite_system P)) gs (decode_finite_term t)}"
    by (rule finite_native_term_observation_semantics; rule finite_native_requirement_terms_exact; assumption)
  show ?thesis by (simp only: finite_native_requirement_term_observation_def exact
    finite_admission_requirements_supported_correct)
qed

export_code finite_native_requirement_term_observation checking SML

end
