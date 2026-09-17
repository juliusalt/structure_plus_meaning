theory Factor_Native_Certificate_Investigation
  imports Factor_Native_Certificate_Correctness Finite_Assessment_Reports
begin

definition native_certificate_assess where
  "native_certificate_assess m w=native_certificate_assessment (native_certificate_problem w) (native_certificate_method m (native_certificate_problem w))"

definition native_certificate_quality where
  "native_certificate_quality m w f=native_certificate_inspect (native_certificate_assess m w) f"

lemma native_certificate_quality_exact:
  "native_certificate_quality m w f=native_certificate_condition f (native_certificate_method m) (native_certificate_problem w)"
  by (simp only: native_certificate_quality_def native_certificate_assess_def native_certificate_assessment_exact)

interpretation native_certificate: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]" "[0,1,2,3,4,5,6]" ws
    native_certificate_method native_certificate_condition native_certificate_problem native_certificate_quality for ws
  by (unfold_locales) (rule native_certificate_quality_exact)

definition native_certificate_investigation_observations where
  "native_certificate_investigation_observations ws=assessed_subject_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2,3,4,5,6] ws
    native_certificate_assess native_certificate_inspect"
definition native_certificate_investigation_relation where
  "native_certificate_investigation_relation ws=subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2,3,4,5,6] ws native_certificate_quality"
definition native_certificate_calculation where
  "native_certificate_calculation ws=assessed_subject_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2,3,4,5,6] ws
    native_certificate_assess native_certificate_inspect"

lemma native_certificate_investigation_observations_equation:
  "fset_of_list (native_certificate_investigation_observations ws)=fset_of_list
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2,3,4,5,6] ws native_certificate_quality)"
  by (rule fset_inject[THEN iffD1])
    (simp only: fset_of_list.rep_eq native_certificate_investigation_observations_def native_certificate_quality_def[abs_def];
      rule assessed_subject_observations_equation)

lemma native_certificate_calculation_equation:
  "native_certificate_calculation ws=(native_certificate_investigation_observations ws,native_certificate_investigation_relation ws,
    subject_investigation_selected [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2,3,4,5,6] ws native_certificate_quality,
    subject_investigation_adequate [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2,3,4,5,6] ws native_certificate_quality)"
  by (simp only: native_certificate_calculation_def assessed_subject_investigation_equation
    native_certificate_investigation_observations_def native_certificate_investigation_relation_def native_certificate_quality_def[abs_def])

definition native_certificate_candidates where
  "native_certificate_candidates=fimage (\<lambda>m. (m,native_certificate_method m)) (fset_of_list [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])"
definition native_certificate_conditions where
  "native_certificate_conditions=fimage (\<lambda>f. (f,native_certificate_condition f)) (fset_of_list [0,1,2,3,4,5,6])"
definition native_certificate_workloads where
  "native_certificate_workloads ws=fimage (\<lambda>w. (w,native_certificate_problem w)) (fset_of_list ws)"

lemma native_certificate_subject_maps:
  "finite_observation_subjects_formed native_certificate_candidates native_certificate_conditions (native_certificate_workloads ws)"
  by (simp only: native_certificate_candidates_def native_certificate_conditions_def native_certificate_workloads_def;
    rule native_certificate.maps_formed)

lemma native_certificate_investigation_observations_derived:
  "fset_of_list (native_certificate_investigation_observations ws)=finite_derived_observations native_certificate_candidates
    native_certificate_conditions (native_certificate_workloads ws) (\<lambda>condition method problem. condition method problem)"
  by (simp only: native_certificate_investigation_observations_equation native_certificate_candidates_def
    native_certificate_conditions_def native_certificate_workloads_def; rule native_certificate.observations_derived)

theorem native_certificate_observation_at_subject:
  assumes "(m,method) |\<in>| native_certificate_candidates" "(f,condition) |\<in>| native_certificate_conditions"
    "(w,problem) |\<in>| native_certificate_workloads ws"
  shows "(f,m,w)\<in>set (native_certificate_investigation_observations ws) \<longleftrightarrow> condition method problem"
  using finite_derived_observation_at_subject[OF native_certificate_subject_maps assms,
    where P="\<lambda>condition method problem. condition method problem"]
  by (simp only: native_certificate_investigation_observations_derived[symmetric] fset_of_list.rep_eq)

definition native_certificate_comparison where
  "native_certificate_comparison ws method other=finite_subject_comparison
    native_certificate_conditions (native_certificate_workloads ws) method other"

theorem native_certificate_comparison_at_subject:
  assumes "(m,method) |\<in>| native_certificate_candidates" "(n,other) |\<in>| native_certificate_candidates"
  shows "(m,n)\<in>set (native_certificate_investigation_relation ws) \<longleftrightarrow> native_certificate_comparison ws method other"
  by (simp only: native_certificate_investigation_relation_def native_certificate_comparison_def
    native_certificate_conditions_def native_certificate_workloads_def; rule native_certificate.comparison_at_subject)
    (use assms in \<open>simp_all only: native_certificate_candidates_def\<close>)

definition native_certificate_investigation where
  "native_certificate_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] [0,1,2,3,4,5,6] selected
    (native_certificate_investigation_observations ws) (native_certificate_investigation_relation ws)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm native_certificate_investigation_def},
   equation = @{thm native_certificate_investigation_observations_derived},
   formation = @{thm native_certificate_subject_maps},
   observation = @{thm native_certificate_observation_at_subject},
   comparison = @{thm native_certificate_comparison_at_subject}}\<close>

theorem native_certificate_adequacy_at_subject:
  assumes subject: "(m,method) |\<in>| native_certificate_candidates"
  shows "m\<in>set (snd (snd (snd (native_certificate_calculation ws)))) \<longleftrightarrow>
    (\<forall>(f,condition)\<in>fset native_certificate_conditions.
      \<forall>(w,problem)\<in>fset (native_certificate_workloads ws). condition method problem)"
  by (simp only: native_certificate_calculation_equation snd_conv native_certificate_conditions_def
    native_certificate_workloads_def; rule native_certificate.adequacy_at_subject)
    (use subject in \<open>simp only: native_certificate_candidates_def\<close>)

definition native_certificate_context where
  "native_certificate_context w=(let X=native_certificate_problem w; original=native_certificate_original X in
    (X,original,native_certificate_base_from original))"

definition native_certificate_cell where
  "native_certificate_cell m C=(case C of (X,original,base) \<Rightarrow>
    let result=native_certificate_apply m base in (result,native_certificate_assessment_from original result))"

lemma native_certificate_cell_at:
  "native_certificate_cell m (native_certificate_context w)=
    (native_certificate_method m (native_certificate_problem w),native_certificate_assess m w)"
  by (simp only: native_certificate_context_def native_certificate_cell_def case_prod_conv Let_def
    native_certificate_method_def native_certificate_base_def native_certificate_assess_def native_certificate_assessment_def)

definition native_certificate_report_table where
  "native_certificate_report_table ws=context_assessment_table native_certificate_methods ws native_certificate_context native_certificate_cell"

lemma native_certificate_report_calculation_exact:
  "context_assessment_investigation native_certificate_methods [0,1,2,3,4,5,6] ws (native_certificate_report_table ws)
    (\<lambda>(result,A). native_certificate_inspect A)=native_certificate_calculation ws"
  by (simp only: native_certificate_report_table_def context_assessment_investigation_exact
    native_certificate_calculation_def native_certificate_methods_def;
    rule assessed_subject_investigation_cong)
    (simp only: native_certificate_cell_at case_prod_conv)

definition native_certificate_report_packet where
  "native_certificate_report_packet ws selections=(let table=native_certificate_report_table ws;
    result=context_assessment_investigation native_certificate_methods [0,1,2,3,4,5,6] ws table
      (\<lambda>(result,A). native_certificate_inspect A)
    in (map (\<lambda>(w,(X,original,base),cells). (w,X,original,cells)) table,result,
      map (investigation_cycle_report native_certificate_methods [0,1,2,3,4,5,6]
        (fst result) (fst (snd result))) selections))"

theorem native_certificate_report_packet_exact:
  "native_certificate_report_packet ws selections=
    (map (\<lambda>w. (w,native_certificate_problem w,native_certificate_original (native_certificate_problem w),map (\<lambda>m.
      (m,native_certificate_method m (native_certificate_problem w),native_certificate_assess m w)) native_certificate_methods)) ws,
      native_certificate_calculation ws,map (investigation_cycle_report native_certificate_methods [0,1,2,3,4,5,6]
        (fst (native_certificate_calculation ws)) (fst (snd (native_certificate_calculation ws)))) selections)"
  apply (simp only: native_certificate_report_packet_def Let_def native_certificate_report_calculation_exact)
  by (simp add: native_certificate_report_table_def context_assessment_table_def
    native_certificate_cell_at native_certificate_context_def native_certificate_cell_def native_certificate_method_def
    native_certificate_assess_def native_certificate_assessment_def native_certificate_base_def Let_def comp_def)

text \<open>
  Each complete original native source and request supplies its actual program,
  answers and certificate family. The shared cells retain that original family,
  every actual candidate graph and its complete row inspections. Their exact
  equation supplies the full original-subject comparison and every revision
  field. Source positioning, native placement, mathematical-proof admission,
  the full physical cost account and genesis remain separate requirements.
\<close>

end
