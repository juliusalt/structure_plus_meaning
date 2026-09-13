theory Factor_Native_Requirement_Investigation
  imports Factor_Native_Requirement_Assessment Finite_Assessed_Investigation
begin

definition native_requirement_optional_condition where
  "native_requirement_optional_condition f method problem=(case problem of None \<Rightarrow> False
    | Some X \<Rightarrow> native_requirement_condition f method X)"

definition native_requirement_assess where
  "native_requirement_assess m w=map_option (\<lambda>X.
    native_requirement_assessment X (native_requirement_method m X)) (native_requirement_problem w)"

definition native_requirement_optional_inspect where
  "native_requirement_optional_inspect A f=(case A of None \<Rightarrow> False
    | Some B \<Rightarrow> native_admission_inspect B f)"

definition native_requirement_quality where
  "native_requirement_quality m w f=native_requirement_optional_inspect (native_requirement_assess m w) f"

lemma native_requirement_quality_exact:
  "native_requirement_quality m w f=native_requirement_optional_condition f
    (native_requirement_method m) (native_requirement_problem w)"
  by (simp add: native_requirement_quality_def native_requirement_assess_def
    native_requirement_optional_inspect_def native_requirement_optional_condition_def
    native_requirement_assessment_exact split: option.splits)

interpretation native_requirement: finite_subject_investigation "[0,1,2,3,4,5,6,7]" "[0,1,2,3]" ws
    native_requirement_method native_requirement_optional_condition native_requirement_problem native_requirement_quality
    for ws
  by (unfold_locales) (rule native_requirement_quality_exact)

definition native_requirement_investigation_observations where
  "native_requirement_investigation_observations ws=assessed_subject_observations [0,1,2,3,4,5,6,7] [0,1,2,3] ws
    native_requirement_assess native_requirement_optional_inspect"

definition native_requirement_investigation_relation where
  "native_requirement_investigation_relation ws=subject_investigation_relation [0,1,2,3,4,5,6,7] [0,1,2,3] ws native_requirement_quality"

definition native_requirement_calculation where
  "native_requirement_calculation ws=assessed_subject_investigation [0,1,2,3,4,5,6,7] [0,1,2,3] ws
    native_requirement_assess native_requirement_optional_inspect"

lemma native_requirement_investigation_observations_equation:
  "fset_of_list (native_requirement_investigation_observations ws)=fset_of_list
    (subject_investigation_observations [0,1,2,3,4,5,6,7] [0,1,2,3] ws native_requirement_quality)"
  by (rule fset_inject[THEN iffD1])
    (simp only: fset_of_list.rep_eq native_requirement_investigation_observations_def
      native_requirement_quality_def[abs_def]; rule assessed_subject_observations_equation)

lemma native_requirement_calculation_equation:
  "native_requirement_calculation ws=(native_requirement_investigation_observations ws,native_requirement_investigation_relation ws,
    subject_investigation_selected [0,1,2,3,4,5,6,7] [0,1,2,3] ws native_requirement_quality,
    subject_investigation_adequate [0,1,2,3,4,5,6,7] [0,1,2,3] ws native_requirement_quality)"
  by (simp only: native_requirement_calculation_def assessed_subject_investigation_equation
    native_requirement_investigation_observations_def native_requirement_investigation_relation_def native_requirement_quality_def[abs_def])

definition native_requirement_candidates where
  "native_requirement_candidates=fimage (\<lambda>m. (m,native_requirement_method m)) (fset_of_list [0,1,2,3,4,5,6,7])"
definition native_requirement_conditions where
  "native_requirement_conditions=fimage (\<lambda>f. (f,native_requirement_optional_condition f)) (fset_of_list [0,1,2,3])"
definition native_requirement_workloads where
  "native_requirement_workloads ws=fimage (\<lambda>w. (w,native_requirement_problem w)) (fset_of_list ws)"

lemma native_requirement_subject_maps:
  "finite_observation_subjects_formed native_requirement_candidates native_requirement_conditions (native_requirement_workloads ws)"
  by (simp only: native_requirement_candidates_def native_requirement_conditions_def native_requirement_workloads_def;
    rule native_requirement.maps_formed)

lemma native_requirement_investigation_observations_derived:
  "fset_of_list (native_requirement_investigation_observations ws)=finite_derived_observations
    native_requirement_candidates native_requirement_conditions (native_requirement_workloads ws)
      (\<lambda>condition method problem. condition method problem)"
  by (simp only: native_requirement_investigation_observations_equation native_requirement_candidates_def
    native_requirement_conditions_def native_requirement_workloads_def; rule native_requirement.observations_derived)

theorem native_requirement_observation_at_subject:
  assumes "(m,method) |\<in>| native_requirement_candidates" "(f,condition) |\<in>| native_requirement_conditions"
    "(w,problem) |\<in>| native_requirement_workloads ws"
  shows "(f,m,w)\<in>set (native_requirement_investigation_observations ws) \<longleftrightarrow> condition method problem"
  using finite_derived_observation_at_subject[OF native_requirement_subject_maps assms,
    where P="\<lambda>condition method problem. condition method problem"]
  by (simp only: native_requirement_investigation_observations_derived[symmetric] fset_of_list.rep_eq)

definition native_requirement_comparison where
  "native_requirement_comparison ws method other=finite_subject_comparison
    native_requirement_conditions (native_requirement_workloads ws) method other"

theorem native_requirement_comparison_at_subject:
  assumes "(m,method) |\<in>| native_requirement_candidates" "(n,other) |\<in>| native_requirement_candidates"
  shows "(m,n)\<in>set (native_requirement_investigation_relation ws) \<longleftrightarrow> native_requirement_comparison ws method other"
  by (simp only: native_requirement_investigation_relation_def native_requirement_comparison_def
    native_requirement_conditions_def native_requirement_workloads_def; rule native_requirement.comparison_at_subject)
    (use assms in \<open>simp_all only: native_requirement_candidates_def\<close>)

definition native_requirement_investigation where
  "native_requirement_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7] [0,1,2,3] selected
    (native_requirement_investigation_observations ws) (native_requirement_investigation_relation ws)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm native_requirement_investigation_def},
   equation = @{thm native_requirement_investigation_observations_derived},
   formation = @{thm native_requirement_subject_maps},
   observation = @{thm native_requirement_observation_at_subject},
   comparison = @{thm native_requirement_comparison_at_subject}}\<close>

theorem native_requirement_adequacy_at_subject:
  assumes subject: "(m,method) |\<in>| native_requirement_candidates"
  shows "m\<in>set (snd (snd (snd (native_requirement_calculation ws)))) \<longleftrightarrow>
    (\<forall>(f,condition)\<in>fset native_requirement_conditions.
      \<forall>(w,problem)\<in>fset (native_requirement_workloads ws). condition method problem)"
  by (simp only: native_requirement_calculation_equation snd_conv native_requirement_conditions_def
    native_requirement_workloads_def; rule native_requirement.adequacy_at_subject)
    (use subject in \<open>simp only: native_requirement_candidates_def\<close>)

definition native_requirement_investigation_report where
  "native_requirement_investigation_report ws selections=(let result=native_requirement_calculation ws;
    rows=fst result; relation=fst (snd result)
    in (result,map (investigation_cycle_report [0,1,2,3,4,5,6,7] [0,1,2,3] rows relation) selections))"

lemma native_requirement_report_initial:
  "fst (snd (investigation_cycle_report [0,1,2,3,4,5,6,7] [0,1,2,3]
    (fst (native_requirement_calculation ws)) (fst (snd (native_requirement_calculation ws))) selected))=
      native_requirement_investigation ws selected"
  by (simp only: investigation_cycle_initial native_requirement_calculation_equation fst_conv snd_conv
    native_requirement_investigation_def)

export_code native_requirement_investigation_report native_requirement_assess checking SML

text \<open>
  The actual source packages and original requirement families are the problem subjects. Each
  candidate is its complete constructor operation. The independent conditions
  retain original positive meaning, usable term evaluation, complete old
  material and bindings, and refusal when the source or a requested leaf is
  unavailable. No satisfaction table is supplied to the observation operation.

  The finite comparison and adequacy claims cover exactly the supplied problem
  indices and their generated term families. Every required condition remains
  part of adequacy even when a smaller observation basis distinguishes this
  particular candidate family. The constructor's separate universal proof
  establishes its meaning for every supported source goal and every term.
  This investigation does not establish coverage of arbitrary methods or the
  complete development workflow, and it does not authorize a bootstrap handoff.
\<close>

end
