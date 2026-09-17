theory Factor_Native_History_Investigation
  imports Factor_Native_History_Assessment Finite_Assessed_Investigation
begin

definition native_history_optional_condition ::
    "nat\<Rightarrow>(native_history_problem\<Rightarrow>native_history_result)\<Rightarrow>native_history_problem option\<Rightarrow>bool" where
  "native_history_optional_condition f method problem=(case problem of None \<Rightarrow> False
    | Some X \<Rightarrow> native_history_condition f method X)"

definition native_history_assess where
  "native_history_assess m w=map_option (\<lambda>X.
    native_history_assessment X (native_history_method m X)) (native_history_problem w)"

definition native_history_assess_report where
  "native_history_assess_report m w=map_option (\<lambda>X. let result=native_history_method m X in
    (native_history_assessment X result,native_history_evidence_review X result)) (native_history_problem w)"

lemma native_history_assess_report_projection:
  "map_option fst (native_history_assess_report m w)=native_history_assess m w"
  by (simp add: native_history_assess_report_def native_history_assess_def
    option.map_comp comp_def Let_def)

definition native_history_optional_inspect where
  "native_history_optional_inspect A f=(case A of None \<Rightarrow> False
    | Some B \<Rightarrow> native_history_inspect B f)"

definition native_history_quality where
  "native_history_quality m w f=native_history_optional_inspect (native_history_assess m w) f"

lemma native_history_quality_exact:
  "native_history_quality m w f=native_history_optional_condition f
    (native_history_method m) (native_history_problem w)"
  by (simp add: native_history_quality_def native_history_assess_def
    native_history_optional_inspect_def native_history_optional_condition_def
    native_history_assessment_exact split: option.splits)

interpretation native_history: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10]" "[0,1,2,3,4,5]" ws
    native_history_method native_history_optional_condition native_history_problem native_history_quality
    for ws
  by (unfold_locales) (rule native_history_quality_exact)

definition native_history_investigation_observations where
  "native_history_investigation_observations ws=assessed_subject_observations [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] ws
    native_history_assess native_history_optional_inspect"

definition native_history_investigation_relation where
  "native_history_investigation_relation ws=subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] ws native_history_quality"

definition native_history_calculation where
  "native_history_calculation ws=assessed_subject_investigation [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] ws
    native_history_assess native_history_optional_inspect"

lemma native_history_investigation_observations_equation:
  "fset_of_list (native_history_investigation_observations ws)=fset_of_list
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] ws native_history_quality)"
  by (rule fset_inject[THEN iffD1])
    (simp only: fset_of_list.rep_eq native_history_investigation_observations_def
      native_history_quality_def[abs_def]; rule assessed_subject_observations_equation)

lemma native_history_calculation_equation:
  "native_history_calculation ws=(native_history_investigation_observations ws,native_history_investigation_relation ws,
    subject_investigation_selected [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] ws native_history_quality,
    subject_investigation_adequate [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] ws native_history_quality)"
  by (simp only: native_history_calculation_def assessed_subject_investigation_equation
    native_history_investigation_observations_def native_history_investigation_relation_def native_history_quality_def[abs_def])

definition native_history_candidates where
  "native_history_candidates=fimage (\<lambda>m. (m,native_history_method m)) (fset_of_list [0,1,2,3,4,5,6,7,8,9,10])"
definition native_history_conditions where
  "native_history_conditions=fimage (\<lambda>f. (f,native_history_optional_condition f)) (fset_of_list [0,1,2,3,4,5])"
definition native_history_workloads where
  "native_history_workloads ws=fimage (\<lambda>w. (w,native_history_problem w)) (fset_of_list ws)"

lemma native_history_subject_maps:
  "finite_observation_subjects_formed native_history_candidates native_history_conditions (native_history_workloads ws)"
  by (simp only: native_history_candidates_def native_history_conditions_def native_history_workloads_def;
    rule native_history.maps_formed)

lemma native_history_investigation_observations_derived:
  "fset_of_list (native_history_investigation_observations ws)=finite_derived_observations
    native_history_candidates native_history_conditions (native_history_workloads ws)
      (\<lambda>condition method problem. condition method problem)"
  by (simp only: native_history_investigation_observations_equation native_history_candidates_def
    native_history_conditions_def native_history_workloads_def; rule native_history.observations_derived)

theorem native_history_observation_at_subject:
  assumes "(m,method) |\<in>| native_history_candidates" "(f,condition) |\<in>| native_history_conditions"
    "(w,problem) |\<in>| native_history_workloads ws"
  shows "(f,m,w)\<in>set (native_history_investigation_observations ws) \<longleftrightarrow> condition method problem"
  using finite_derived_observation_at_subject[OF native_history_subject_maps assms,
    where P="\<lambda>condition method problem. condition method problem"]
  by (simp only: native_history_investigation_observations_derived[symmetric] fset_of_list.rep_eq)

definition native_history_comparison where
  "native_history_comparison ws method other=finite_subject_comparison
    native_history_conditions (native_history_workloads ws) method other"

theorem native_history_comparison_at_subject:
  assumes "(m,method) |\<in>| native_history_candidates" "(n,other) |\<in>| native_history_candidates"
  shows "(m,n)\<in>set (native_history_investigation_relation ws) \<longleftrightarrow> native_history_comparison ws method other"
  by (simp only: native_history_investigation_relation_def native_history_comparison_def
    native_history_conditions_def native_history_workloads_def; rule native_history.comparison_at_subject)
    (use assms in \<open>simp_all only: native_history_candidates_def\<close>)

definition native_history_investigation where
  "native_history_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] selected
    (native_history_investigation_observations ws) (native_history_investigation_relation ws)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm native_history_investigation_def},
   equation = @{thm native_history_investigation_observations_derived},
   formation = @{thm native_history_subject_maps},
   observation = @{thm native_history_observation_at_subject},
   comparison = @{thm native_history_comparison_at_subject}}\<close>

theorem native_history_adequacy_at_subject:
  assumes subject: "(m,method) |\<in>| native_history_candidates"
  shows "m\<in>set (snd (snd (snd (native_history_calculation ws)))) \<longleftrightarrow>
    (\<forall>(f,condition)\<in>fset native_history_conditions.
      \<forall>(w,problem)\<in>fset (native_history_workloads ws). condition method problem)"
  by (simp only: native_history_calculation_equation snd_conv native_history_conditions_def
    native_history_workloads_def; rule native_history.adequacy_at_subject)
    (use subject in \<open>simp only: native_history_candidates_def\<close>)

definition native_history_investigation_report where
  "native_history_investigation_report ws selections=(let result=native_history_calculation ws;
    rows=fst result; relation=fst (snd result)
    in (result,map (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] rows relation) selections))"

lemma native_history_report_initial:
  "fst (snd (investigation_cycle_report [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5]
    (fst (native_history_calculation ws)) (fst (snd (native_history_calculation ws))) selected))=
      native_history_investigation ws selected"
  by (simp only: investigation_cycle_initial native_history_calculation_equation fst_conv snd_conv
    native_history_investigation_def)

text \<open>
  Each subject contains its actual native environment, package selector and
  requested calls. Each candidate is its complete evidence-producing operation.
  The six independent conditions retain exact requested positive meaning,
  source identity, refusal of unavailable inputs, every progressive preceding
  state, and the complete original clause, binding and premise witnesses.
  The observation equation connects each computed assessment to those subjects.

  Adequacy retains all six conditions. A smaller distinguishing basis does not
  remove any obligation. The finite comparison covers exactly the supplied
  candidates and generated source problems. It does not construct a native
  proof artifact, check native mathematical proofs, establish arbitrary-method
  coverage, enforce the full development cycle, or authorize genesis.
\<close>

end
