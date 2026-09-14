theory Factor_Native_Derivation_Investigation
  imports Factor_Native_Derivation_Correctness Finite_Assessed_Investigation
begin

definition native_derivation_optional_condition ::
    "nat\<Rightarrow>(native_history_problem\<Rightarrow>native_derivation_result)\<Rightarrow>native_history_problem option\<Rightarrow>bool" where
  "native_derivation_optional_condition f method problem=(case problem of None \<Rightarrow> False
    | Some X \<Rightarrow> native_derivation_condition f method X)"

definition native_derivation_assess where
  "native_derivation_assess m w=map_option (\<lambda>X.
    native_derivation_assessment X (native_derivation_method m X)) (native_history_problem w)"

definition native_derivation_assess_report where
  "native_derivation_assess_report m w=map_option (\<lambda>X. let result=native_derivation_method m X in
    (native_derivation_assessment X result,native_derivation_evidence_review X result)) (native_history_problem w)"

lemma native_derivation_assess_report_projection:
  "map_option fst (native_derivation_assess_report m w)=native_derivation_assess m w"
  by (simp add: native_derivation_assess_report_def native_derivation_assess_def
    option.map_comp comp_def Let_def)

definition native_derivation_optional_inspect where
  "native_derivation_optional_inspect A f=(case A of None \<Rightarrow> False
    | Some B \<Rightarrow> native_derivation_inspect B f)"

definition native_derivation_quality where
  "native_derivation_quality m w f=native_derivation_optional_inspect (native_derivation_assess m w) f"

lemma native_derivation_quality_exact:
  "native_derivation_quality m w f=native_derivation_optional_condition f
    (native_derivation_method m) (native_history_problem w)"
  by (simp add: native_derivation_quality_def native_derivation_assess_def
    native_derivation_optional_inspect_def native_derivation_optional_condition_def
    native_derivation_assessment_exact split: option.splits)

interpretation native_derivation: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14]" "[0,1,2,3,4,5]" ws
    native_derivation_method native_derivation_optional_condition native_history_problem native_derivation_quality
    for ws
  by (unfold_locales) (rule native_derivation_quality_exact)

definition native_derivation_investigation_observations where
  "native_derivation_investigation_observations ws=assessed_subject_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] ws
    native_derivation_assess native_derivation_optional_inspect"

definition native_derivation_investigation_relation where
  "native_derivation_investigation_relation ws=subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] ws native_derivation_quality"

definition native_derivation_calculation where
  "native_derivation_calculation ws=assessed_subject_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] ws
    native_derivation_assess native_derivation_optional_inspect"

lemma native_derivation_investigation_observations_equation:
  "fset_of_list (native_derivation_investigation_observations ws)=fset_of_list
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] ws native_derivation_quality)"
  by (rule fset_inject[THEN iffD1])
    (simp only: fset_of_list.rep_eq native_derivation_investigation_observations_def
      native_derivation_quality_def[abs_def]; rule assessed_subject_observations_equation)

lemma native_derivation_calculation_equation:
  "native_derivation_calculation ws=(native_derivation_investigation_observations ws,native_derivation_investigation_relation ws,
    subject_investigation_selected [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] ws native_derivation_quality,
    subject_investigation_adequate [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] ws native_derivation_quality)"
  by (simp only: native_derivation_calculation_def assessed_subject_investigation_equation
    native_derivation_investigation_observations_def native_derivation_investigation_relation_def native_derivation_quality_def[abs_def])

definition native_derivation_candidates where
  "native_derivation_candidates=fimage (\<lambda>m. (m,native_derivation_method m)) (fset_of_list [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14])"
definition native_derivation_conditions where
  "native_derivation_conditions=fimage (\<lambda>f. (f,native_derivation_optional_condition f)) (fset_of_list [0,1,2,3,4,5])"
definition native_derivation_workloads where
  "native_derivation_workloads ws=fimage (\<lambda>w. (w,native_history_problem w)) (fset_of_list ws)"

lemma native_derivation_subject_maps:
  "finite_observation_subjects_formed native_derivation_candidates native_derivation_conditions (native_derivation_workloads ws)"
  by (simp only: native_derivation_candidates_def native_derivation_conditions_def native_derivation_workloads_def;
    rule native_derivation.maps_formed)

lemma native_derivation_investigation_observations_derived:
  "fset_of_list (native_derivation_investigation_observations ws)=finite_derived_observations
    native_derivation_candidates native_derivation_conditions (native_derivation_workloads ws)
      (\<lambda>condition method problem. condition method problem)"
  by (simp only: native_derivation_investigation_observations_equation native_derivation_candidates_def
    native_derivation_conditions_def native_derivation_workloads_def; rule native_derivation.observations_derived)

theorem native_derivation_observation_at_subject:
  assumes "(m,method) |\<in>| native_derivation_candidates" "(f,condition) |\<in>| native_derivation_conditions"
    "(w,problem) |\<in>| native_derivation_workloads ws"
  shows "(f,m,w)\<in>set (native_derivation_investigation_observations ws) \<longleftrightarrow> condition method problem"
  using finite_derived_observation_at_subject[OF native_derivation_subject_maps assms,
    where P="\<lambda>condition method problem. condition method problem"]
  by (simp only: native_derivation_investigation_observations_derived[symmetric] fset_of_list.rep_eq)

definition native_derivation_comparison where
  "native_derivation_comparison ws method other=finite_subject_comparison
    native_derivation_conditions (native_derivation_workloads ws) method other"

theorem native_derivation_comparison_at_subject:
  assumes "(m,method) |\<in>| native_derivation_candidates" "(n,other) |\<in>| native_derivation_candidates"
  shows "(m,n)\<in>set (native_derivation_investigation_relation ws) \<longleftrightarrow> native_derivation_comparison ws method other"
  by (simp only: native_derivation_investigation_relation_def native_derivation_comparison_def
    native_derivation_conditions_def native_derivation_workloads_def; rule native_derivation.comparison_at_subject)
    (use assms in \<open>simp_all only: native_derivation_candidates_def\<close>)

definition native_derivation_investigation where
  "native_derivation_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] selected
    (native_derivation_investigation_observations ws) (native_derivation_investigation_relation ws)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm native_derivation_investigation_def},
   equation = @{thm native_derivation_investigation_observations_derived},
   formation = @{thm native_derivation_subject_maps},
   observation = @{thm native_derivation_observation_at_subject},
   comparison = @{thm native_derivation_comparison_at_subject}}\<close>

theorem native_derivation_adequacy_at_subject:
  assumes subject: "(m,method) |\<in>| native_derivation_candidates"
  shows "m\<in>set (snd (snd (snd (native_derivation_calculation ws)))) \<longleftrightarrow>
    (\<forall>(f,condition)\<in>fset native_derivation_conditions.
      \<forall>(w,problem)\<in>fset (native_derivation_workloads ws). condition method problem)"
  by (simp only: native_derivation_calculation_equation snd_conv native_derivation_conditions_def
    native_derivation_workloads_def; rule native_derivation.adequacy_at_subject)
    (use subject in \<open>simp only: native_derivation_candidates_def\<close>)

definition native_derivation_investigation_report where
  "native_derivation_investigation_report ws selections=(let result=native_derivation_calculation ws;
    rows=fst result; relation=fst (snd result)
    in (result,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] rows relation) selections))"

lemma native_derivation_report_initial:
  "fst (snd (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5]
    (fst (native_derivation_calculation ws)) (fst (snd (native_derivation_calculation ws))) selected))=
      native_derivation_investigation ws selected"
  by (simp only: investigation_cycle_initial native_derivation_calculation_equation fst_conv snd_conv
    native_derivation_investigation_def)

export_code native_derivation_investigation_report native_derivation_assess checking SML

text \<open>
  Every subject contains its actual native environment and requested calls.
  Candidates return complete recursive certificates or actual structural
  mutations. The observation equation connects each computed assessment to
  its original source, independent checker and all six requirements.
  Adequacy retains every requirement even when a smaller basis distinguishes
  the supplied candidates. Native artifact placement, replay, mathematical
  proof admission, complete development enforcement and genesis remain open.
\<close>

end
