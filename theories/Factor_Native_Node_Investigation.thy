theory Factor_Native_Node_Investigation
  imports Factor_Native_Node_Assessment Finite_Assessment_Reports
begin

definition native_node_assess where
  "native_node_assess m w=native_node_assessment (native_node_problem w) (native_node_method m (native_node_problem w))"

definition native_node_quality where
  "native_node_quality m w f=native_node_inspect (native_node_assess m w) f"

lemma native_node_quality_exact:
  "native_node_quality m w f=native_node_condition f (native_node_method m) (native_node_problem w)"
  by (simp only: native_node_quality_def native_node_assess_def native_node_assessment_exact)

interpretation native_node: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10]" "[0,1,2,3,4,5]" ws
    native_node_method native_node_condition native_node_problem native_node_quality for ws
  by (unfold_locales) (rule native_node_quality_exact)

definition native_node_investigation_observations where
  "native_node_investigation_observations ws=assessed_subject_observations [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] ws
    native_node_assess native_node_inspect"
definition native_node_investigation_relation where
  "native_node_investigation_relation ws=subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] ws native_node_quality"
definition native_node_calculation where
  "native_node_calculation ws=assessed_subject_investigation [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] ws
    native_node_assess native_node_inspect"

lemma native_node_investigation_observations_equation:
  "fset_of_list (native_node_investigation_observations ws)=fset_of_list
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] ws native_node_quality)"
  by (rule fset_inject[THEN iffD1])
    (simp only: fset_of_list.rep_eq native_node_investigation_observations_def native_node_quality_def[abs_def];
      rule assessed_subject_observations_equation)

lemma native_node_calculation_equation:
  "native_node_calculation ws=(native_node_investigation_observations ws,native_node_investigation_relation ws,
    subject_investigation_selected [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] ws native_node_quality,
    subject_investigation_adequate [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] ws native_node_quality)"
  by (simp only: native_node_calculation_def assessed_subject_investigation_equation
    native_node_investigation_observations_def native_node_investigation_relation_def native_node_quality_def[abs_def])

definition native_node_candidates where
  "native_node_candidates=fimage (\<lambda>m. (m,native_node_method m)) (fset_of_list [0,1,2,3,4,5,6,7,8,9,10])"
definition native_node_conditions where
  "native_node_conditions=fimage (\<lambda>f. (f,native_node_condition f)) (fset_of_list [0,1,2,3,4,5])"
definition native_node_workloads where
  "native_node_workloads ws=fimage (\<lambda>w. (w,native_node_problem w)) (fset_of_list ws)"

lemma native_node_subject_maps:
  "finite_observation_subjects_formed native_node_candidates native_node_conditions (native_node_workloads ws)"
  by (simp only: native_node_candidates_def native_node_conditions_def native_node_workloads_def;
    rule native_node.maps_formed)

lemma native_node_investigation_observations_derived:
  "fset_of_list (native_node_investigation_observations ws)=finite_derived_observations native_node_candidates
    native_node_conditions (native_node_workloads ws) (\<lambda>condition method problem. condition method problem)"
  by (simp only: native_node_investigation_observations_equation native_node_candidates_def
    native_node_conditions_def native_node_workloads_def; rule native_node.observations_derived)

theorem native_node_observation_at_subject:
  assumes "(m,method) |\<in>| native_node_candidates" "(f,condition) |\<in>| native_node_conditions"
    "(w,problem) |\<in>| native_node_workloads ws"
  shows "(f,m,w)\<in>set (native_node_investigation_observations ws) \<longleftrightarrow> condition method problem"
  using finite_derived_observation_at_subject[OF native_node_subject_maps assms,
    where P="\<lambda>condition method problem. condition method problem"]
  by (simp only: native_node_investigation_observations_derived[symmetric] fset_of_list.rep_eq)

definition native_node_comparison where
  "native_node_comparison ws method other=finite_subject_comparison
    native_node_conditions (native_node_workloads ws) method other"

theorem native_node_comparison_at_subject:
  assumes "(m,method) |\<in>| native_node_candidates" "(n,other) |\<in>| native_node_candidates"
  shows "(m,n)\<in>set (native_node_investigation_relation ws) \<longleftrightarrow> native_node_comparison ws method other"
  by (simp only: native_node_investigation_relation_def native_node_comparison_def
    native_node_conditions_def native_node_workloads_def; rule native_node.comparison_at_subject)
    (use assms in \<open>simp_all only: native_node_candidates_def\<close>)

definition native_node_investigation where
  "native_node_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10] [0,1,2,3,4,5] selected
    (native_node_investigation_observations ws) (native_node_investigation_relation ws)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm native_node_investigation_def},
   equation = @{thm native_node_investigation_observations_derived},
   formation = @{thm native_node_subject_maps},
   observation = @{thm native_node_observation_at_subject},
   comparison = @{thm native_node_comparison_at_subject}}\<close>

theorem native_node_adequacy_at_subject:
  assumes subject: "(m,method) |\<in>| native_node_candidates"
  shows "m\<in>set (snd (snd (snd (native_node_calculation ws)))) \<longleftrightarrow>
    (\<forall>(f,condition)\<in>fset native_node_conditions.
      \<forall>(w,problem)\<in>fset (native_node_workloads ws). condition method problem)"
  by (simp only: native_node_calculation_equation snd_conv native_node_conditions_def
    native_node_workloads_def; rule native_node.adequacy_at_subject)
    (use subject in \<open>simp only: native_node_candidates_def\<close>)

definition native_node_cell where
  "native_node_cell m X=(let result=native_node_method m X in (result,native_node_assessment X result))"

definition native_node_report_table where
  "native_node_report_table ws=context_assessment_table native_node_methods ws native_node_problem native_node_cell"

lemma native_node_report_calculation_exact:
  "context_assessment_investigation native_node_methods [0,1,2,3,4,5] ws (native_node_report_table ws)
    (\<lambda>(result,A). native_node_inspect A)=native_node_calculation ws"
  by (simp only: native_node_report_table_def context_assessment_investigation_exact
    native_node_calculation_def native_node_methods_def;
    rule assessed_subject_investigation_cong)
    (simp only: native_node_cell_def native_node_assess_def Let_def case_prod_conv)

definition native_node_report_packet where
  "native_node_report_packet ws selections=(let table=native_node_report_table ws;
    result=context_assessment_investigation native_node_methods [0,1,2,3,4,5] ws table
      (\<lambda>(result,A). native_node_inspect A)
    in (table,result,map (investigation_cycle_report native_node_methods [0,1,2,3,4,5]
      (fst result) (fst (snd result))) selections))"

theorem native_node_report_packet_exact:
  "native_node_report_packet ws selections=
    (map (\<lambda>w. (w,native_node_problem w,map (\<lambda>m.
      (m,native_node_method m (native_node_problem w),native_node_assess m w)) native_node_methods)) ws,
      native_node_calculation ws,map (investigation_cycle_report native_node_methods [0,1,2,3,4,5]
        (fst (native_node_calculation ws)) (fst (snd (native_node_calculation ws)))) selections)"
  apply (simp only: native_node_report_packet_def Let_def native_node_report_calculation_exact)
  by (simp only: native_node_report_table_def context_assessment_table_def native_node_cell_def
    native_node_assess_def Let_def)

text \<open>
  Actual source and metadata subjects supply the constructor inputs. Every cell
  retains its returned environment, exact native readings and independent
  assessments. The shared packet preserves the original complete investigation
  and every repair/revision cycle. The finite comparison has no authority to
  validate an inference or authorize mathematical-proof admission or genesis.
\<close>

end
