theory Native_Control_Selected_Root
  imports Native_Control_Prepared_Cause_Review Native_Control_Cause_Continuation
    Admitted_Conditional_Applications Finite_Presented_Reasoning
begin

definition cause_root_apply_prepared where
  "cause_root_apply_prepared prepared report = (case prepared of ((s,R,q,obs),cache) \<Rightarrow>
    map_option (\<lambda>m. conditional_application_run m finite_quoted_guard_schema q obs)
      (cause_root_prepared_choice prepared cause_root_methods cause_root_facets report))"

lemma cause_root_apply_prepared_exact:
  "cause_root_apply_prepared (cause_root_prepare (s,R,q,obs)) report =
    admitted_conditional_applications cause_root_methods cause_root_facets
      finite_quoted_guard_schema q obs report"
proof -
  have observe: "cause_root_observation (s,R,q,obs) =
    conditional_application_observation finite_quoted_guard_schema q obs"
    by (rule ext, rule ext) (simp only: cause_root_observation_def prod.case)
  show ?thesis by (simp only: cause_root_apply_prepared_def cause_root_prepare_def prod.case
    cause_root_prepared_choice_def cause_root_prepared_question_def prepared_faceted_question_exact
    observe admitted_conditional_applications_def)
qed

definition native_cause_root_family where
  "native_cause_root_family reports = (let subject=cause_root_subject ();
    prepared=cause_root_prepare subject in Parallel.map (cause_root_apply_prepared prepared) reports)"

theorem native_cause_root_family_exact:
  assumes subject: "cause_root_subject ()=(s,R,q,obs)"
  shows "native_cause_root_family reports = map
    (admitted_conditional_applications cause_root_methods cause_root_facets
      finite_quoted_guard_schema q obs) reports"
  by (simp only: native_cause_root_family_def Let_def subject Parallel.map_def
    cause_root_apply_prepared_exact[abs_def])

theorem native_cause_root_original_obligations:
  assumes subject: "cause_root_subject ()=(s,R,q,obs)"
    and index: "i<length reports"
    and result: "native_cause_root_family reports!i=Some A"
    and member: "(t,V,H) |\<in>| A"
  shows "A\<noteq>{||}" "t=q"
    "schema_instance (decode_finite_schema finite_quoted_guard_schema)
      (decode_finite_term_bindings V) (decode_finite_term t) (decode_finite_premises H)"
    "schema_material_satisfied (decode_finite_schema finite_quoted_guard_schema)
      (decode_finite_term_bindings V)"
    "fimage fst H={|0,1,2|}"
proof -
  have actual: "admitted_conditional_applications cause_root_methods cause_root_facets
      finite_quoted_guard_schema q obs (reports!i)=Some A"
    using result by (simp only: native_cause_root_family_exact[OF subject] nth_map[OF index])
  have facets: "Requested_Result\<in>set cause_root_facets" "Original_Rule\<in>set cause_root_facets"
    by (simp_all add: cause_root_facets_def)
  show "A\<noteq>{||}" by (rule admitted_conditional_applications_original(1)[OF actual facets])
  show "t=q" by (rule admitted_conditional_applications_original(2)[OF actual facets member])
  have inst: "finite_schema_instance finite_quoted_guard_schema V t H"
    by (rule admitted_conditional_applications_original(3)[OF actual facets member])
  show "schema_instance (decode_finite_schema finite_quoted_guard_schema)
      (decode_finite_term_bindings V) (decode_finite_term t) (decode_finite_premises H)"
    using inst by (simp only: finite_schema_instance_correct)
  show "schema_material_satisfied (decode_finite_schema finite_quoted_guard_schema)
      (decode_finite_term_bindings V)"
    using admitted_conditional_applications_original(4)[OF actual facets member]
    by (simp only: finite_schema_material_satisfied_correct)
  have sockets: "fimage fst (finite_schema_premises finite_quoted_guard_schema)={|0,1,2|}"
    by (rule fset_eqI) (auto simp: finite_quoted_guard_schema_code)
  show "fimage fst H={|0,1,2|}"
    using original_application_preserves_sockets[OF inst]
    by (simp only: sockets)
qed

definition cause_root_results_value where
  "cause_root_results_value = finite_sequence_presentation (finite_option_presentation
    (finite_collection_presentation finite_natural_application_value))"

lemma cause_root_results_value_injective: "inj cause_root_results_value"
  unfolding cause_root_results_value_def
  by (intro finite_sequence_presentation_injective finite_option_presentation_injective
    finite_collection_presentation_injective finite_reasoning_values_injective)

definition cause_root_results_summary :: "finite_natural_application fset option list \<Rightarrow>
    (nat \<times> nat list \<times> nat list) option list" where
  "cause_root_results_summary = map (map_option (\<lambda>A. (fcard A,
    sorted_list_of_fset (fimage (\<lambda>(t,V,H). fcard V) A),
    sorted_list_of_fset (fimage (\<lambda>(t,V,H). fcard H) A))))"

definition cause_root_missing_records where
  "cause_root_missing_records body adapter target = (case cause_root_subject () of (s,R,q,obs) \<Rightarrow>
    admitted_guard_certificate_records body adapter target None R receiving_empty_source (Finite_Whole R) [])"

lemma cause_root_missing_records_exact:
  "cause_root_missing_records body adapter target =
    map_option (map (\<lambda>(i,source). (i,None))) (admitted_guard_install body adapter target)"
  by (simp add: cause_root_missing_records_def admitted_guard_missing_certificate split: prod.splits)

definition cause_root_missing_summary where
  "cause_root_missing_summary rows = map_option (map (\<lambda>(i,cause). (i,cause\<noteq>None))) rows"

definition cause_root_missing_observation where
  "cause_root_missing_observation body adapter target =
    cause_root_missing_summary (cause_root_missing_records body adapter target)"

export_code native_cause_root_family cause_root_results_value cause_root_results_summary
  cause_root_missing_records cause_root_missing_observation
  cause_root_subject cause_root_prepared_family cause_root_prepared_question
  cause_root_prepared_choice cause_root_prepared_profile cause_root_methods cause_root_facets
  cause_root_review_scopes cause_root_observation_controls
  absent_development_report judgment_steering_questions judgment_bridge_question
  judgment_artifact_execution_question guard_representation_execution_question
  context_execution_summary native_steered_development judgment_artifact_value
  finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Selected_Root file_prefix "native_control_selected_root"

text \<open>The original native admission chooses the constructor actually
  executed. Whole outputs preserve all three original premise occurrences;
  their complete presentation is injective. The separate actual installed-guard
  attempt with no certificate retains failures and cannot create a policy cause.
  Natural-coordinate root applications are not installed-coordinate proof trees.
  Source recovery, proof transport and native certificates remain mandatory.\<close>

end
