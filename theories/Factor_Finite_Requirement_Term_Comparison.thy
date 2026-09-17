theory Factor_Finite_Requirement_Term_Comparison
  imports Factor_Finite_Requirement_Term_Observations Factor_Finite_Goal_Term_Comparison
begin

definition finite_native_requirement_term_comparison where
  "finite_native_requirement_term_comparison E u r gs F v d T=finite_term_observation_comparison
    (finite_native_requirement_term_observation E u r gs T)
    (finite_native_goal_term_observation F v [] (Existing_Admission d) T)"

definition finite_native_requirement_term_comparison_holds where
  "finite_native_requirement_term_comparison_holds f E u r gs F v d T=(
    case finite_native_requirement_term_comparison E u r gs F v d T of None \<Rightarrow> False
    | Some (extra,missing) \<Rightarrow> (if f=0 then extra={||} else missing={||}))"

definition finite_native_requirement_term_comparison_condition where
  "finite_native_requirement_term_comparison_condition f E u r gs F v d T \<longleftrightarrow>
    (\<exists>P Q. native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and>
      (\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P)) \<and>
      (\<exists>A. finite_program_evaluation P (finite_program_term_demand P T)=Some A) \<and>
      native_package_at (decode_finite_environment F) v [] (decode_finite_system Q) \<and>
      d\<in>system_definitions (decode_finite_system Q) \<and>
      (\<exists>B. finite_program_evaluation Q (finite_program_term_demand Q T)=Some B) \<and>
      (\<forall>t\<in>fset T. if f=0 then
        (d,decode_finite_term t)\<in>positive_meaning (decode_finite_system Q) \<longrightarrow>
          admission_requirements_hold (positive_meaning (decode_finite_system P)) gs (decode_finite_term t)
        else admission_requirements_hold (positive_meaning (decode_finite_system P)) gs (decode_finite_term t)
          \<longrightarrow> (d,decode_finite_term t)\<in>positive_meaning (decode_finite_system Q)))"

theorem finite_native_requirement_term_comparison_exact:
  "finite_native_requirement_term_comparison_holds f E u r gs F v d T=
    finite_native_requirement_term_comparison_condition f E u r gs F v d T"
  using finite_term_observation_comparison_exact[OF
    finite_native_requirement_term_observation_semantics[where E=E and u=u and r=r and gs=gs and T=T,
      unfolded conj_assoc[symmetric]]
    finite_native_goal_term_observation_semantics[where E=F and u=v and r="[]" and g="Existing_Admission d" and T=T,
      unfolded conj_assoc[symmetric]], where f=f]
  by (simp add: finite_native_requirement_term_comparison_holds_def finite_native_requirement_term_comparison_def
    finite_term_observation_comparison_holds_def finite_native_requirement_term_comparison_condition_def)

end
