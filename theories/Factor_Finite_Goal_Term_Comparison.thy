theory Factor_Finite_Goal_Term_Comparison
  imports Factor_Finite_Goal_Term_Observations Finite_Term_Observation_Comparisons
begin

lemma finite_native_goal_term_observation_total:
  assumes "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    "admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P)"
    "\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A"
  shows "\<exists>M. finite_native_goal_term_observation E u r g T=Some (P,M)"
  using assms by (simp only: finite_native_goal_term_observation_ready finite_native_source_correct
    less_eq_fset.rep_eq finite_admission_goal_sites_correct finite_system_definitions_correct)

definition finite_native_goal_term_comparison where
  "finite_native_goal_term_comparison E u r g F v s h T=finite_term_observation_comparison
    (finite_native_goal_term_observation E u r g T) (finite_native_goal_term_observation F v s h T)"

definition finite_native_goal_term_comparison_holds where
  "finite_native_goal_term_comparison_holds f E u r g F v s h T=(
    case finite_native_goal_term_comparison E u r g F v s h T of None \<Rightarrow> False
    | Some (extra,missing) \<Rightarrow> (if f=0 then extra={||} else missing={||}))"

definition finite_native_goal_term_comparison_condition where
  "finite_native_goal_term_comparison_condition f E u r g F v s h T \<longleftrightarrow>
    (\<exists>P Q. native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
      admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P) \<and>
      (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A) \<and>
      native_package_at (decode_finite_environment F) v s (decode_finite_system Q) \<and>
      admission_goal_sites h\<subseteq>system_definitions (decode_finite_system Q) \<and>
      (\<exists>B. finite_program_evaluation Q (finite_program_term_demand Q T)=Some B) \<and>
      (\<forall>t\<in>fset T. if f=0 then
        admission_goal_holds (positive_meaning (decode_finite_system Q)) h (decode_finite_term t)
          \<longrightarrow> admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)
        else admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)
          \<longrightarrow> admission_goal_holds (positive_meaning (decode_finite_system Q)) h (decode_finite_term t)))"

theorem finite_native_goal_term_comparison_exact:
  "finite_native_goal_term_comparison_holds f E u r g F v s h T=
    finite_native_goal_term_comparison_condition f E u r g F v s h T"
  using finite_term_observation_comparison_exact[OF
    finite_native_goal_term_observation_semantics[unfolded conj_assoc[symmetric]]
    finite_native_goal_term_observation_semantics[unfolded conj_assoc[symmetric]]]
  by (simp only: finite_native_goal_term_comparison_holds_def finite_native_goal_term_comparison_def
    finite_term_observation_comparison_holds_def finite_native_goal_term_comparison_condition_def conj_assoc)

export_code finite_native_goal_term_comparison finite_native_goal_term_comparison_holds checking SML

end
