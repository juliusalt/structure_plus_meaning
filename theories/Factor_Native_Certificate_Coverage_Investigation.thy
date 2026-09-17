theory Factor_Native_Certificate_Coverage_Investigation
  imports Factor_Native_Certificate_Coverage Finite_Assessment_Reports
begin

definition certificate_coverage_method :: "nat\<Rightarrow>native_derivation_result list\<Rightarrow>native_derivation_result list" where
  "certificate_coverage_method (m::nat) originals=(if m=0 then originals else [])"

definition certificate_coverage_problem where
  "certificate_coverage_problem (w::nat)=map
    (native_certificate_original \<circ> native_certificate_problem) native_certificate_indices"

definition certificate_coverage_condition :: "nat\<Rightarrow>(native_derivation_result list\<Rightarrow>native_derivation_result list)
    \<Rightarrow>native_derivation_result list\<Rightarrow>bool" where
  "certificate_coverage_condition (f::nat) method originals=(if f=0 then set originals\<subseteq>set (method originals)
    else if f<4 then native_certificate_scope_coverage_condition (f-1) (method originals) else False)"

definition certificate_coverage_assessment where
  "certificate_coverage_assessment originals result=(set originals\<subseteq>set result,
    native_certificate_scope_coverage result)"

definition certificate_coverage_inspect :: "bool\<times>native_certificate_family_coverage_report list\<Rightarrow>nat\<Rightarrow>bool" where
  "certificate_coverage_inspect assessment (f::nat)=(if f=0 then fst assessment
    else if f<4 then native_certificate_scope_coverage_inspect (snd assessment) (f-1) else False)"

theorem certificate_coverage_assessment_exact:
  "certificate_coverage_inspect (certificate_coverage_assessment originals (method originals)) f=
    certificate_coverage_condition f method originals"
  by (simp only: certificate_coverage_inspect_def certificate_coverage_assessment_def fst_conv snd_conv
    certificate_coverage_condition_def native_certificate_scope_coverage_exact)

definition certificate_coverage_assess where
  "certificate_coverage_assess m w=certificate_coverage_assessment (certificate_coverage_problem w) (certificate_coverage_method m (certificate_coverage_problem w))"

definition certificate_coverage_quality where
  "certificate_coverage_quality m w f=certificate_coverage_inspect (certificate_coverage_assess m w) f"

lemma certificate_coverage_quality_exact:
  "certificate_coverage_quality m w f=certificate_coverage_condition f (certificate_coverage_method m) (certificate_coverage_problem w)"
  by (simp only: certificate_coverage_quality_def certificate_coverage_assess_def certificate_coverage_assessment_exact)

interpretation certificate_coverage: finite_subject_investigation "[0,1]" "[0,1,2,3]" ws
    certificate_coverage_method certificate_coverage_condition certificate_coverage_problem certificate_coverage_quality for ws
  by (unfold_locales) (rule certificate_coverage_quality_exact)

definition certificate_coverage_investigation_observations where
  "certificate_coverage_investigation_observations ws=assessed_subject_observations [0,1] [0,1,2,3] ws
    certificate_coverage_assess certificate_coverage_inspect"
definition certificate_coverage_investigation_relation where
  "certificate_coverage_investigation_relation ws=subject_investigation_relation [0,1] [0,1,2,3] ws certificate_coverage_quality"
definition certificate_coverage_calculation where
  "certificate_coverage_calculation ws=assessed_subject_investigation [0,1] [0,1,2,3] ws
    certificate_coverage_assess certificate_coverage_inspect"

lemma certificate_coverage_investigation_observations_equation:
  "fset_of_list (certificate_coverage_investigation_observations ws)=fset_of_list
    (subject_investigation_observations [0,1] [0,1,2,3] ws certificate_coverage_quality)"
  by (rule fset_inject[THEN iffD1])
    (simp only: fset_of_list.rep_eq certificate_coverage_investigation_observations_def certificate_coverage_quality_def[abs_def];
      rule assessed_subject_observations_equation)

lemma certificate_coverage_calculation_equation:
  "certificate_coverage_calculation ws=(certificate_coverage_investigation_observations ws,certificate_coverage_investigation_relation ws,
    subject_investigation_selected [0,1] [0,1,2,3] ws certificate_coverage_quality,
    subject_investigation_adequate [0,1] [0,1,2,3] ws certificate_coverage_quality)"
  by (simp only: certificate_coverage_calculation_def assessed_subject_investigation_equation
    certificate_coverage_investigation_observations_def certificate_coverage_investigation_relation_def certificate_coverage_quality_def[abs_def])

definition certificate_coverage_candidates where
  "certificate_coverage_candidates=fimage (\<lambda>m. (m,certificate_coverage_method m)) (fset_of_list [0,1])"
definition certificate_coverage_conditions where
  "certificate_coverage_conditions=fimage (\<lambda>f. (f,certificate_coverage_condition f)) (fset_of_list [0,1,2,3])"
definition certificate_coverage_workloads where
  "certificate_coverage_workloads ws=fimage (\<lambda>w. (w,certificate_coverage_problem w)) (fset_of_list ws)"

lemma certificate_coverage_subject_maps:
  "finite_observation_subjects_formed certificate_coverage_candidates certificate_coverage_conditions (certificate_coverage_workloads ws)"
  by (simp only: certificate_coverage_candidates_def certificate_coverage_conditions_def certificate_coverage_workloads_def;
    rule certificate_coverage.maps_formed)

lemma certificate_coverage_investigation_observations_derived:
  "fset_of_list (certificate_coverage_investigation_observations ws)=finite_derived_observations certificate_coverage_candidates
    certificate_coverage_conditions (certificate_coverage_workloads ws) (\<lambda>condition method problem. condition method problem)"
  by (simp only: certificate_coverage_investigation_observations_equation certificate_coverage_candidates_def
    certificate_coverage_conditions_def certificate_coverage_workloads_def; rule certificate_coverage.observations_derived)

theorem certificate_coverage_observation_at_subject:
  assumes "(m,method) |\<in>| certificate_coverage_candidates" "(f,condition) |\<in>| certificate_coverage_conditions"
    "(w,problem) |\<in>| certificate_coverage_workloads ws"
  shows "(f,m,w)\<in>set (certificate_coverage_investigation_observations ws) \<longleftrightarrow> condition method problem"
  using finite_derived_observation_at_subject[OF certificate_coverage_subject_maps assms,
    where P="\<lambda>condition method problem. condition method problem"]
  by (simp only: certificate_coverage_investigation_observations_derived[symmetric] fset_of_list.rep_eq)

definition certificate_coverage_comparison where
  "certificate_coverage_comparison ws method other=finite_subject_comparison
    certificate_coverage_conditions (certificate_coverage_workloads ws) method other"

theorem certificate_coverage_comparison_at_subject:
  assumes "(m,method) |\<in>| certificate_coverage_candidates" "(n,other) |\<in>| certificate_coverage_candidates"
  shows "(m,n)\<in>set (certificate_coverage_investigation_relation ws) \<longleftrightarrow> certificate_coverage_comparison ws method other"
  by (simp only: certificate_coverage_investigation_relation_def certificate_coverage_comparison_def
    certificate_coverage_conditions_def certificate_coverage_workloads_def; rule certificate_coverage.comparison_at_subject)
    (use assms in \<open>simp_all only: certificate_coverage_candidates_def\<close>)

definition certificate_coverage_investigation where
  "certificate_coverage_investigation ws selected=investigation_basis [0,1] [0,1,2,3] selected
    (certificate_coverage_investigation_observations ws) (certificate_coverage_investigation_relation ws)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm certificate_coverage_investigation_def},
   equation = @{thm certificate_coverage_investigation_observations_derived},
   formation = @{thm certificate_coverage_subject_maps},
   observation = @{thm certificate_coverage_observation_at_subject},
   comparison = @{thm certificate_coverage_comparison_at_subject}}\<close>

theorem certificate_coverage_adequacy_at_subject:
  assumes subject: "(m,method) |\<in>| certificate_coverage_candidates"
  shows "m\<in>set (snd (snd (snd (certificate_coverage_calculation ws)))) \<longleftrightarrow>
    (\<forall>(f,condition)\<in>fset certificate_coverage_conditions.
      \<forall>(w,problem)\<in>fset (certificate_coverage_workloads ws). condition method problem)"
  by (simp only: certificate_coverage_calculation_equation snd_conv certificate_coverage_conditions_def
    certificate_coverage_workloads_def; rule certificate_coverage.adequacy_at_subject)
    (use subject in \<open>simp only: certificate_coverage_candidates_def\<close>)

definition certificate_coverage_packet where
  "certificate_coverage_packet selections=(let
    Xs=map native_certificate_problem native_certificate_indices;
    originals=map native_certificate_original Xs;
    cells=map (\<lambda>m. let result=certificate_coverage_method m originals in
      (m,result,certificate_coverage_assessment originals result)) [0,1];
    compared=certificate_coverage_calculation [0]
    in (Xs,originals,cells,compared,
      map (investigation_cycle_report [0,1] [0,1,2,3] (fst compared) (fst (snd compared))) selections))"

text \<open>
  This scope comparison consumes the actual complete original source-derived
  certificate families. Retention is checked on those full values. The other
  conditions ask for concrete proof, call and shared-path distinctions inside
  those originals, with every witness retained. Comparison selection alone
  does not establish coverage or permit adoption of the certificate method.
\<close>

end
