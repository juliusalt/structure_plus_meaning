theory Native_Control_Receiving_Review
  imports Native_Control_Constructed_Source_View Optional_View_Refinement Faceted_Native_Questions
begin

section \<open>Actual refused reports and an actual source without a package\<close>

definition absent_development_report :: native_development_report where
  "absent_development_report = \<lparr>development_generation=None,
    development_compiled_conditions=None, development_observed_conditions=None,
    development_scope_review=None, development_comparison=None, development_revision=None\<rparr>"

lemma absent_development_admission [simp]:
  "native_development_admission Q absent_development_report = None"
  by (simp add: native_development_admission_def absent_development_report_def)

lemma absent_native_choice [simp]:
  "keyed_admitted_choice key subjects question absent_development_report = None"
  by (simp add: keyed_admitted_choice_def keyed_admitted_subjects_def split: option.splits)

lemma absent_adapter_install [simp]:
  "admitted_guard_install body absent_development_report target = None"
  by (simp add: admitted_guard_install_def admitted_guard_requests_def judgment_artifact_choice_def)

lemma absent_target_install [simp]:
  "admitted_guard_install body adapter absent_development_report = None"
  by (simp add: admitted_guard_install_def admitted_guard_requests_def guard_representation_choice_def)

lemma absent_body_install [simp]:
  "admitted_guard_install absent_development_report adapter target = None"
  by (simp add: admitted_guard_install_def admitted_guard_requests_def judgment_bridge_install_def
    judgment_bridge_receive_def split: option.splits)

definition receiving_empty_source :: "local_address option finite_artifact_environment" where
  "receiving_empty_source = \<lparr>finite_environment_artifacts={||},finite_environment_bindings={||}\<rparr>"

lemma empty_source_not_available:
  "\<not> installed_guard_source_available receiving_empty_source None"
  by (simp add: installed_guard_source_available_exact native_package_at_def
    native_root_family_at_def decode_finite_environment_def receiving_empty_source_def
    artifact_at_def map_relation_values_def)

definition receiving_construct where
  "receiving_construct reports = (case reports of (body,adapter,target) \<Rightarrow>
    admitted_guard_install body adapter target)"

definition receiving_read where
  "receiving_read rows = map (\<lambda>(i,r). (i,case r of None \<Rightarrow> False
    | Some (d,K,v) \<Rightarrow> installed_guard_source_available K v)) rows"

definition receiving_project where
  "receiving_project rows = map (\<lambda>(i,r). (i,r \<noteq> None)) rows"

lemma receiving_read_option:
  "map_option receiving_read rows = installed_guard_source_checks rows"
  by (cases rows) (simp_all add: receiving_read_def installed_guard_source_checks_def)

lemma receiving_project_option:
  "map_option receiving_project rows = admitted_guard_install_summary rows"
  by (cases rows) (simp_all add: receiving_project_def admitted_guard_install_summary_def)

interpretation receiving: constructed_optional_view receiving_construct receiving_read receiving_project
  "[]" "\<lambda>(K,v). installed_guard_source_available K v"
  "(absent_development_report,absent_development_report,absent_development_report)" "(receiving_empty_source,None)"
proof
  fix reports
  show "map_option receiving_read (receiving_construct reports) =
    map_option receiving_project (receiving_construct reports)"
    by (cases reports rule: prod_cases3) (simp only: receiving_construct_def prod.case
      receiving_read_option receiving_project_option
      admitted_guard_source_checks_exact)
  show "receiving_construct (absent_development_report,absent_development_report,absent_development_report) = None"
    by (simp add: receiving_construct_def)
  show "\<not> (case (receiving_empty_source,None) of (K,v) \<Rightarrow> installed_guard_source_available K v)"
    by (simp add: empty_source_not_available)
qed

section \<open>The complete finite program family is compared under all three original distinctions\<close>

definition receiving_programs where
  "receiving_programs = List.product [Read_Optional,Project_Optional,Force_Optional]
    [Keep_Source_Reader,Always_Available]"

definition receiving_facets where
  "receiving_facets = [Complete_Optional_View,Original_Source_Reader,No_Repeated_Reader]"

lemma receiving_program_scope:
  "set receiving_programs = UNIV"
proof -
  have "(p,q) \<in> set receiving_programs" for p q
    by (cases p; cases q) (simp_all add: receiving_programs_def)
  then show ?thesis by auto
qed

definition receiving_refinement_question where
  "receiving_refinement_question ignored = faceted_native_question receiving_programs
    receiving_facets optional_view_observation"

definition receiving_refinement_choice where
  "receiving_refinement_choice report = keyed_admitted_choice (first_occurrence_key receiving_programs)
    receiving_programs (receiving_refinement_question ()) report"

theorem receiving_refinement_original_conditions:
  assumes chosen: "receiving_refinement_choice report = Some program"
    and facet: "facet \<in> set receiving_facets"
  shows "receiving.requirement program facet"
  using keyed_admitted_choice_condition[OF first_occurrence_key_inj_on chosen[unfolded receiving_refinement_choice_def
    receiving_refinement_question_def] facet]
  by (simp only: receiving.observation_exact)

theorem receiving_refinement_selected_program:
  assumes chosen: "receiving_refinement_choice report = Some program"
  shows "program = (Project_Optional,Keep_Source_Reader)"
proof -
  have all: "\<And>f. f \<in> set receiving_facets \<Longrightarrow> optional_view_observation program f"
    by (rule keyed_admitted_choice_condition[OF first_occurrence_key_inj_on chosen[unfolded receiving_refinement_choice_def
      receiving_refinement_question_def]])
  obtain p q where program: "program=(p,q)" by (cases program) auto
  show ?thesis using all[of Complete_Optional_View] all[of Original_Source_Reader]
    all[of No_Repeated_Reader]
    by (cases p; cases q)
      (simp_all add: program receiving_facets_def optional_view_observation_def)
qed

export_code receiving_refinement_question receiving_refinement_choice receiving_programs receiving_facets
  optional_view_observation absent_development_report judgment_steering_questions
  judgment_bridge_question judgment_artifact_execution_question guard_representation_execution_question
  context_execution_summary native_steered_development judgment_artifact_value
  finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Receiving_Review file_prefix "native_control_receiving_review"

text \<open>The observer is exact for the original all-report installation/view,
  all arbitrary source inputs and the primitive reader dependency. The original
  three questions and reports remain separate admissions. Complete coverage
  concerns the six interpreted programs only. Native repair of omitted facets
  cannot establish broader candidate adequacy, elapsed-time superiority,
  governing policy authority or a certified policy cause. No executable receiving
  refinement is installed by this review theory.\<close>

end
