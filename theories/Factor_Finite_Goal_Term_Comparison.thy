theory Factor_Finite_Goal_Term_Comparison
  imports Factor_Finite_Goal_Term_Observations
begin

lemma finite_native_goal_term_observation_total:
  assumes "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    "admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P)"
    "\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A"
  shows "\<exists>M. finite_native_goal_term_observation E u r g T=Some (P,M)"
  using assms by (simp only: finite_native_goal_term_observation_ready finite_native_source_correct
    less_eq_fset.rep_eq finite_admission_goal_sites_correct finite_system_definitions_correct)

definition finite_native_goal_term_comparison where
  "finite_native_goal_term_comparison E u r g F v s h T=(
    case finite_native_goal_term_observation E u r g T of None \<Rightarrow> None | Some (P,A) \<Rightarrow>
      map_option (\<lambda>(Q,B). (B |-| A,A |-| B)) (finite_native_goal_term_observation F v s h T))"

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
proof
  assume holds: "finite_native_goal_term_comparison_holds f E u r g F v s h T"
  obtain P A Q B where left: "finite_native_goal_term_observation E u r g T=Some (P,A)"
    and right: "finite_native_goal_term_observation F v s h T=Some (Q,B)"
    and residual: "if f=0 then B |-| A={||} else A |-| B={||}"
    using holds by (auto simp: finite_native_goal_term_comparison_holds_def
      finite_native_goal_term_comparison_def split: option.splits prod.splits)
  have available_left: "\<exists>Z. finite_program_evaluation P (finite_program_term_demand P T)=Some Z"
    using finite_native_goal_term_observation_ready[of E u r g T P] left by blast
  have available_right: "\<exists>Z. finite_program_evaluation Q (finite_program_term_demand Q T)=Some Z"
    using finite_native_goal_term_observation_ready[of F v s h T Q] right by blast
  have compared: "\<forall>t\<in>fset T. if f=0 then
      admission_goal_holds (positive_meaning (decode_finite_system Q)) h (decode_finite_term t)
        \<longrightarrow> admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)
      else admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)
        \<longrightarrow> admission_goal_holds (positive_meaning (decode_finite_system Q)) h (decode_finite_term t)"
    using residual finite_native_goal_term_observation_exact(3)[OF left]
      finite_native_goal_term_observation_exact(3)[OF right]
    by (auto simp: fset_eq_iff split: if_splits)
  show "finite_native_goal_term_comparison_condition f E u r g F v s h T"
    unfolding finite_native_goal_term_comparison_condition_def
    by (rule exI[of _ P], rule exI[of _ Q])
      (use finite_native_goal_term_observation_exact(1,2)[OF left]
        finite_native_goal_term_observation_exact(1,2)[OF right]
        available_left available_right compared in blast)
next
  assume condition: "finite_native_goal_term_comparison_condition f E u r g F v s h T"
  obtain P Q where native_left: "native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
    and supported_left: "admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P)"
    and available_left: "\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A"
    and native_right: "native_package_at (decode_finite_environment F) v s (decode_finite_system Q)"
    and supported_right: "admission_goal_sites h\<subseteq>system_definitions (decode_finite_system Q)"
    and available_right: "\<exists>B. finite_program_evaluation Q (finite_program_term_demand Q T)=Some B"
    and compared: "\<forall>t\<in>fset T. if f=0 then
      admission_goal_holds (positive_meaning (decode_finite_system Q)) h (decode_finite_term t)
        \<longrightarrow> admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)
      else admission_goal_holds (positive_meaning (decode_finite_system P)) g (decode_finite_term t)
        \<longrightarrow> admission_goal_holds (positive_meaning (decode_finite_system Q)) h (decode_finite_term t)"
    using condition by (simp only: finite_native_goal_term_comparison_condition_def; blast)
  obtain A where left: "finite_native_goal_term_observation E u r g T=Some (P,A)"
    using finite_native_goal_term_observation_total[OF native_left supported_left available_left] by blast
  obtain B where right: "finite_native_goal_term_observation F v s h T=Some (Q,B)"
    using finite_native_goal_term_observation_total[OF native_right supported_right available_right] by blast
  have residual: "if f=0 then B |-| A={||} else A |-| B={||}"
    using compared finite_native_goal_term_observation_exact(3)[OF left]
      finite_native_goal_term_observation_exact(3)[OF right]
    by (auto simp: fset_eq_iff split: if_splits)
  show "finite_native_goal_term_comparison_holds f E u r g F v s h T"
    by (simp add: finite_native_goal_term_comparison_holds_def finite_native_goal_term_comparison_def
      left right residual)
qed

export_code finite_native_goal_term_comparison finite_native_goal_term_comparison_holds checking SML

end
