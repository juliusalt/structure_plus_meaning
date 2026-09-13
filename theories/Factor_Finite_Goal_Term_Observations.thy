theory Factor_Finite_Goal_Term_Observations
  imports Factor_Finite_Term_Demands
begin

section \<open>Observe one original goal over its complete supplied term family\<close>

definition finite_native_goal_term_observation where
  "finite_native_goal_term_observation E u r g T=(case finite_native_source E u r of None \<Rightarrow> None
    | Some P \<Rightarrow> if finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P
      then map_option (\<lambda>(Q,A). (Q,ffilter (finite_admission_goal_test A g) T))
        (finite_native_program_evaluation E u r (finite_program_term_demand P T)) else None)"

lemma finite_native_goal_term_observation_conditions:
  "finite_native_goal_term_observation E u r g T=Some (P,M) \<longleftrightarrow>
    finite_native_source E u r=Some P \<and>
    finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P \<and>
    (\<exists>A. finite_native_program_evaluation E u r (finite_program_term_demand P T)=Some (P,A) \<and>
      M=ffilter (finite_admission_goal_test A g) T)"
  by (auto simp: finite_native_goal_term_observation_def finite_native_program_evaluation_def
    split: option.splits prod.splits if_splits)

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
  by (auto simp: finite_native_goal_term_observation_conditions finite_native_program_evaluation_def)

theorem finite_native_goal_term_observation_semantics:
  "finite_native_goal_term_observation E u r g T=Some (P,M) \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
    admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P) \<and>
    (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A) \<and>
    fset M={t\<in>fset T.
      admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)}"
proof
  assume result: "finite_native_goal_term_observation E u r g T=Some (P,M)"
  have ready: "\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A"
    using finite_native_goal_term_observation_ready[of E u r g T P] result by blast
  show "native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
      admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P) \<and>
      (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A) \<and>
      fset M={t\<in>fset T.
        admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)}"
    using finite_native_goal_term_observation_exact[OF result] ready by blast
next
  assume facts: "native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
      admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P) \<and>
      (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A) \<and>
      fset M={t\<in>fset T.
        admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)}"
  have ready: "\<exists>N. finite_native_goal_term_observation E u r g T=Some (P,N)"
    using facts by (simp only: finite_native_goal_term_observation_ready finite_native_source_correct
      less_eq_fset.rep_eq finite_admission_goal_sites_correct finite_system_definitions_correct; blast)
  obtain N where observed: "finite_native_goal_term_observation E u r g T=Some (P,N)"
    using ready by blast
  have "N=M" using finite_native_goal_term_observation_exact(3)[OF observed] facts
    by (simp only: fset_inject[symmetric]; blast)
  then show "finite_native_goal_term_observation E u r g T=Some (P,M)"
    using observed by simp
qed

export_code finite_native_goal_term_observation checking SML

end
