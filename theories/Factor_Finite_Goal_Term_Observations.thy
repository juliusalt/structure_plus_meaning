theory Factor_Finite_Goal_Term_Observations
  imports Factor_Finite_Native_Term_Observations
begin

section \<open>Observe one original goal over its complete supplied term family\<close>

definition finite_native_goal_term_observation where
  "finite_native_goal_term_observation E u r g T=finite_native_term_observation
    (\<lambda>P. finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P)
    (\<lambda>A. finite_admission_goal_test A g) E u r T"

lemma finite_native_goal_term_observation_conditions:
  "finite_native_goal_term_observation E u r g T=Some (P,M) \<longleftrightarrow>
    finite_native_source E u r=Some P \<and>
    finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P \<and>
    (\<exists>A. finite_native_program_evaluation E u r (finite_program_term_demand P T)=Some (P,A) \<and>
      M=ffilter (finite_admission_goal_test A g) T)"
  by (simp only: finite_native_goal_term_observation_def finite_native_term_observation_conditions)

theorem finite_native_goal_term_observation_exact:
  assumes result: "finite_native_goal_term_observation E u r g T=Some (P,M)"
  shows "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    "admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P)"
    "fset M={t\<in>fset T.
      admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)}"
proof -
  have source: "finite_native_source E u r=Some P"
    and supported: "finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
    using result by (simp only: finite_native_goal_term_observation_conditions; blast)+
  obtain A where evaluated:
      "finite_native_program_evaluation E u r (finite_program_term_demand P T)=Some (P,A)"
    and mask: "M=ffilter (finite_admission_goal_test A g) T"
    using result by (simp only: finite_native_goal_term_observation_conditions; blast)
  show "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    using source by (simp only: finite_native_source_correct)
  show "admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P)"
    using supported by (simp only: less_eq_fset.rep_eq finite_admission_goal_sites_correct
      finite_system_definitions_correct)
  show "fset M={t\<in>fset T.
      admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)}"
    by (simp only: mask finite_native_goal_terms_exact[OF evaluated supported])
qed

theorem finite_native_goal_term_observation_ready:
  "(\<exists>M. finite_native_goal_term_observation E u r g T=Some (P,M)) \<longleftrightarrow>
    finite_native_source E u r=Some P \<and>
    finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P \<and>
    (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A)"
  by (auto simp: finite_native_goal_term_observation_conditions finite_native_program_evaluation_conditions
    finite_native_source_correct[symmetric])

theorem finite_native_goal_term_observation_semantics:
  "finite_native_goal_term_observation E u r g T=Some (P,M) \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P) \<and>
    (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A) \<and>
    fset M={t\<in>fset T.
      admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)}"
  by (simp only: finite_native_goal_term_observation_def
    finite_native_term_observation_semantics[OF finite_native_goal_terms_exact]
    less_eq_fset.rep_eq finite_admission_goal_sites_correct finite_system_definitions_correct)

end
