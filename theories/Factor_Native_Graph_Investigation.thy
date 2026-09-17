theory Factor_Native_Graph_Investigation
  imports Factor_Native_Graph_Correctness Finite_Assessment_Reports
begin

definition native_graph_assess where
  "native_graph_assess m w=native_graph_assessment (native_graph_problem w) (native_graph_method m (native_graph_problem w))"

definition native_graph_quality where
  "native_graph_quality m w f=native_graph_inspect (native_graph_assess m w) f"

lemma native_graph_quality_exact:
  "native_graph_quality m w f=native_graph_condition f (native_graph_method m) (native_graph_problem w)"
  by (simp only: native_graph_quality_def native_graph_assess_def native_graph_assessment_exact)

interpretation native_graph: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14]" "[0,1,2,3,4,5]" ws
    native_graph_method native_graph_condition native_graph_problem native_graph_quality for ws
  by (unfold_locales) (rule native_graph_quality_exact)

definition native_graph_investigation_observations where
  "native_graph_investigation_observations ws=assessed_subject_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] ws
    native_graph_assess native_graph_inspect"
definition native_graph_investigation_relation where
  "native_graph_investigation_relation ws=subject_investigation_relation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] ws native_graph_quality"
definition native_graph_calculation where
  "native_graph_calculation ws=assessed_subject_investigation [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] ws
    native_graph_assess native_graph_inspect"

lemma native_graph_investigation_observations_equation:
  "fset_of_list (native_graph_investigation_observations ws)=fset_of_list
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] ws native_graph_quality)"
  by (rule fset_inject[THEN iffD1])
    (simp only: fset_of_list.rep_eq native_graph_investigation_observations_def native_graph_quality_def[abs_def];
      rule assessed_subject_observations_equation)

lemma native_graph_calculation_equation:
  "native_graph_calculation ws=(native_graph_investigation_observations ws,native_graph_investigation_relation ws,
    subject_investigation_selected [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] ws native_graph_quality,
    subject_investigation_adequate [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] ws native_graph_quality)"
  by (simp only: native_graph_calculation_def assessed_subject_investigation_equation
    native_graph_investigation_observations_def native_graph_investigation_relation_def native_graph_quality_def[abs_def])

definition native_graph_candidates where
  "native_graph_candidates=fimage (\<lambda>m. (m,native_graph_method m)) (fset_of_list [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14])"
definition native_graph_conditions where
  "native_graph_conditions=fimage (\<lambda>f. (f,native_graph_condition f)) (fset_of_list [0,1,2,3,4,5])"
definition native_graph_workloads where
  "native_graph_workloads ws=fimage (\<lambda>w. (w,native_graph_problem w)) (fset_of_list ws)"

lemma native_graph_subject_maps:
  "finite_observation_subjects_formed native_graph_candidates native_graph_conditions (native_graph_workloads ws)"
  by (simp only: native_graph_candidates_def native_graph_conditions_def native_graph_workloads_def;
    rule native_graph.maps_formed)

lemma native_graph_investigation_observations_derived:
  "fset_of_list (native_graph_investigation_observations ws)=finite_derived_observations native_graph_candidates
    native_graph_conditions (native_graph_workloads ws) (\<lambda>condition method problem. condition method problem)"
  by (simp only: native_graph_investigation_observations_equation native_graph_candidates_def
    native_graph_conditions_def native_graph_workloads_def; rule native_graph.observations_derived)

theorem native_graph_observation_at_subject:
  assumes "(m,method) |\<in>| native_graph_candidates" "(f,condition) |\<in>| native_graph_conditions"
    "(w,problem) |\<in>| native_graph_workloads ws"
  shows "(f,m,w)\<in>set (native_graph_investigation_observations ws) \<longleftrightarrow> condition method problem"
  using finite_derived_observation_at_subject[OF native_graph_subject_maps assms,
    where P="\<lambda>condition method problem. condition method problem"]
  by (simp only: native_graph_investigation_observations_derived[symmetric] fset_of_list.rep_eq)

definition native_graph_comparison where
  "native_graph_comparison ws method other=finite_subject_comparison
    native_graph_conditions (native_graph_workloads ws) method other"

theorem native_graph_comparison_at_subject:
  assumes "(m,method) |\<in>| native_graph_candidates" "(n,other) |\<in>| native_graph_candidates"
  shows "(m,n)\<in>set (native_graph_investigation_relation ws) \<longleftrightarrow> native_graph_comparison ws method other"
  by (simp only: native_graph_investigation_relation_def native_graph_comparison_def
    native_graph_conditions_def native_graph_workloads_def; rule native_graph.comparison_at_subject)
    (use assms in \<open>simp_all only: native_graph_candidates_def\<close>)

definition native_graph_investigation where
  "native_graph_investigation ws selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] [0,1,2,3,4,5] selected
    (native_graph_investigation_observations ws) (native_graph_investigation_relation ws)"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm native_graph_investigation_def},
   equation = @{thm native_graph_investigation_observations_derived},
   formation = @{thm native_graph_subject_maps},
   observation = @{thm native_graph_observation_at_subject},
   comparison = @{thm native_graph_comparison_at_subject}}\<close>

theorem native_graph_adequacy_at_subject:
  assumes subject: "(m,method) |\<in>| native_graph_candidates"
  shows "m\<in>set (snd (snd (snd (native_graph_calculation ws)))) \<longleftrightarrow>
    (\<forall>(f,condition)\<in>fset native_graph_conditions.
      \<forall>(w,problem)\<in>fset (native_graph_workloads ws). condition method problem)"
  by (simp only: native_graph_calculation_equation snd_conv native_graph_conditions_def
    native_graph_workloads_def; rule native_graph.adequacy_at_subject)
    (use subject in \<open>simp only: native_graph_candidates_def\<close>)

definition native_graph_context where
  "native_graph_context w=(native_graph_problem w,native_graph_base (native_graph_problem w))"

definition native_graph_cell where
  "native_graph_cell m C=(case C of (X,base) \<Rightarrow>
    let result=native_graph_apply m X base in (result,native_graph_assessment X result))"

lemma native_graph_cell_at:
  "native_graph_cell m (native_graph_context w)=
    (native_graph_method m (native_graph_problem w),native_graph_assess m w)"
  by (simp only: native_graph_context_def native_graph_cell_def case_prod_conv Let_def
    native_graph_method_def native_graph_assess_def)

definition native_graph_report_table where
  "native_graph_report_table ws=context_assessment_table native_graph_methods ws native_graph_context native_graph_cell"

lemma native_graph_report_calculation_exact:
  "context_assessment_investigation native_graph_methods [0,1,2,3,4,5] ws (native_graph_report_table ws)
    (\<lambda>(result,A). native_graph_inspect A)=native_graph_calculation ws"
  by (simp only: native_graph_report_table_def context_assessment_investigation_exact
    native_graph_calculation_def native_graph_methods_def;
    rule assessed_subject_investigation_cong)
    (simp only: native_graph_cell_at case_prod_conv)

definition native_graph_report_packet where
  "native_graph_report_packet ws selections=(let table=native_graph_report_table ws;
    result=context_assessment_investigation native_graph_methods [0,1,2,3,4,5] ws table
      (\<lambda>(result,A). native_graph_inspect A)
    in (map (\<lambda>(w,(X,base),cells). (w,X,cells)) table,result,
      map (investigation_cycle_report native_graph_methods [0,1,2,3,4,5]
        (fst result) (fst (snd result))) selections))"

theorem native_graph_report_packet_exact:
  "native_graph_report_packet ws selections=
    (map (\<lambda>w. (w,native_graph_problem w,map (\<lambda>m.
      (m,native_graph_method m (native_graph_problem w),native_graph_assess m w)) native_graph_methods)) ws,
      native_graph_calculation ws,map (investigation_cycle_report native_graph_methods [0,1,2,3,4,5]
        (fst (native_graph_calculation ws)) (fst (snd (native_graph_calculation ws)))) selections)"
  apply (simp only: native_graph_report_packet_def Let_def native_graph_report_calculation_exact)
  by (simp add: native_graph_report_table_def context_assessment_table_def
    native_graph_cell_at native_graph_context_def native_graph_cell_def native_graph_method_def
    native_graph_assess_def Let_def comp_def)

text \<open>
  Each actual original source and graph supplies one shared base construction.
  Every candidate cell computes its actual result and complete independent
  assessment. The packet has exactly the original full subjects, observations,
  comparisons and all repair/revision fields. The complete mapping permits
  different placements while preserving every original node and indexed edge.
  Realization and metadata recovery do not establish inference validity,
  native mathematical-proof admission, the full cost account or genesis.
\<close>

end
