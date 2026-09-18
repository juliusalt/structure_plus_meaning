theory Native_Control_Cause_Review
  imports Native_Control_Reviewed_Receiving Conditional_Application_Review
begin

section \<open>The actual installed target's original root schema\<close>

lemma quoted_guard_head_missing:
  "finite_schema_head_missing finite_quoted_guard_schema={|1,2,3|}"
  by (rule fset_eqI) (auto simp: finite_schema_head_missing_def finite_schema_variables_def
    finite_quoted_guard_schema_code)

lemma quoted_guard_requested_empty:
  "finite_requested_schema_applications finite_quoted_guard_schema q={||}"
  by (rule requested_application_missing_variable[where a=1])
    (simp_all add: finite_schema_variables_def finite_quoted_guard_schema_code)

type_synonym guard_root_subject = "syntax_judgment_subject \<times> finite_exact_artifact \<times>
  finite_factor_term \<times> ((nat,nat) finite_schema_observation_site \<times> finite_factor_term) fset"

definition cause_root_subject :: "unit \<Rightarrow> guard_root_subject" where
  "cause_root_subject ignored=(let s=(syntax_checked_rooted_context,syntax_proposition Original_Union);
    t=syntax_judgment_data s; R=finite_term_syntax t;
    q=Finite_Target (Finite_Whole R); c=finite_artifact_value R;
    obs={|(Finite_Conclusion_Site,q),
      (Finite_Premise_Site 1 123,Finite_Pair c (Finite_Pair (Finite_Payload []) t))|}
    in (s,R,q,obs))"

definition cause_root_observation :: "guard_root_subject \<Rightarrow> conditional_application_method \<Rightarrow>
    conditional_application_facet \<Rightarrow> bool" where
  "cause_root_observation subject m f=(case subject of (s,R,q,obs) \<Rightarrow>
    conditional_application_observation finite_quoted_guard_schema q obs m f)"

definition cause_root_methods where
  "cause_root_methods=[Requested_Head,Erased_Premises,Observed_Parts]"
definition cause_root_facets where
  "cause_root_facets=[Requested_Result,Original_Rule]"

definition cause_root_question where
  "cause_root_question subject methods facets=faceted_native_question methods facets
    (cause_root_observation subject)"

definition cause_root_choice where
  "cause_root_choice subject methods facets report=native_admitted_choice methods
    (cause_root_question subject methods facets) report"

theorem cause_root_original_requirements:
  assumes chosen: "cause_root_choice (s,R,q,obs) methods facets report=Some m"
    and facet: "f\<in>set facets"
  shows "conditional_application_requirement finite_quoted_guard_schema q obs m f"
  using conditional_application_admitted[OF chosen[unfolded cause_root_choice_def
    cause_root_question_def cause_root_observation_def prod.case] facet] .

definition cause_root_review_scopes where
  "cause_root_review_scopes=[(cause_root_methods,cause_root_facets),
    (rev cause_root_methods,cause_root_facets),
    (cause_root_methods@cause_root_methods,cause_root_facets),
    (cause_root_methods,[Requested_Result]),(cause_root_methods,[Original_Rule]),
    ([Requested_Head,Erased_Premises],cause_root_facets),([],cause_root_facets)]"

definition cause_root_application_summary where
  "cause_root_application_summary subject m=(case subject of (s,R,q,obs) \<Rightarrow>
    let A=conditional_application_run m finite_quoted_guard_schema q obs in
      (fcard A, map (cause_root_observation subject m) cause_root_facets,
       sorted_list_of_fset (fimage (\<lambda>(t,V,H). fcard V) A),
       sorted_list_of_fset (fimage (\<lambda>(t,V,H). fcard H) A)))"

definition cause_root_observation_controls :: "guard_root_subject \<Rightarrow> guard_root_subject list" where
  "cause_root_observation_controls subject=(case subject of (s,R,q,obs) \<Rightarrow>
    [(s,R,q,obs),(s,R,q,ffilter (\<lambda>(site,t). site=Finite_Conclusion_Site) obs),
     (s,R,q,{||})])"

export_code cause_root_subject cause_root_question cause_root_choice cause_root_methods
  cause_root_facets cause_root_review_scopes cause_root_application_summary
  cause_root_observation_controls cause_root_observation
  finite_schema_head_missing finite_quoted_guard_schema
  absent_development_report judgment_steering_questions judgment_bridge_question
  judgment_artifact_execution_question guard_representation_execution_question
  context_execution_summary native_steered_development judgment_artifact_value
  finite_term_shared_word_fold integer_of_nat
  in Eval module_name Native_Control_Cause_Review file_prefix "native_control_cause_review"

text \<open>The subject is the original checked union statement in its exact
  rooted context, quoted as a complete artifact. The schema is exactly the
  original guard constructor's root clause; no accepting row is added. Its
  observations describe actual structural values and do not assert the three
  premise calls. The original reports, source transport, complete source,
  native proofs and governing authority remain separate prerequisites.\<close>

end
