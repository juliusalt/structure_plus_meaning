theory Factor_Development_Subjects
  imports Factor_Development_Comparison
begin

definition development_methods :: "nat list" where "development_methods=[0..<10]"
definition development_facets :: "nat list" where "development_facets=[0..<5]"

definition development_subject_context where
  "development_subject_context qs w=(let Q=qs!w in (Q,construct_native_development Q,development_reference Q))"

definition development_subject_table where
  "development_subject_table qs=context_assessment_table development_methods [0..<length qs]
    (development_subject_context qs) development_producer_cell"

lemma development_subject_cell_exact:
  "development_producer_cell m (development_subject_context qs w)=
    (development_producer m (qs!w),development_producer_assessment (qs!w)
      (construct_native_development (qs!w)) (development_reference (qs!w)) (development_producer m (qs!w)))"
  by (simp only: development_producer_cell_def development_subject_context_def development_producer_def Let_def case_prod_conv)

definition development_table_condition where
  "development_table_condition table nquestions m f=list_all (\<lambda>w.
    case context_assessment_lookup table m w of None \<Rightarrow> False
      | Some (actual,assessment) \<Rightarrow> development_producer_inspect assessment f) [0..<nquestions]"

lemma development_table_condition_exact:
  assumes method: "m\<in>set development_methods"
  shows "development_table_condition (development_subject_table qs) (length qs) m f \<longleftrightarrow>
    (\<forall>Q\<in>set qs. development_producer_condition f (development_producer m) Q)"
  using method by (auto simp: development_table_condition_def development_subject_table_def
    context_assessment_lookup_exact development_subject_cell_exact development_producer_condition_def
    list_all_iff all_set_conv_all_nth)

definition development_subject_quality where
  "development_subject_quality qs m w f=development_producer_condition f (development_producer m) (qs!w)"

interpretation development_subject: finite_subject_investigation "[0,1,2,3,4,5,6,7,8,9]" "[0,1,2,3,4]" "[0..<length qs]"
    development_producer development_producer_condition "nth qs" "development_subject_quality qs" for qs
  by (unfold_locales) (simp only: development_subject_quality_def)

definition development_subject_investigation where
  "development_subject_investigation qs selected=investigation_basis [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] selected
    (subject_investigation_observations [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] [0..<length qs] (development_subject_quality qs))
    (subject_investigation_relation [0,1,2,3,4,5,6,7,8,9] [0,1,2,3,4] [0..<length qs] (development_subject_quality qs))"

setup \<open>Finite_Observation_Contracts.register
  {definition = @{thm development_subject_investigation_def},
   equation = @{thm development_subject.observations_derived},
   formation = @{thm development_subject.maps_formed},
   observation = @{thm development_subject.observation_at_subject},
   comparison = @{thm development_subject.comparison_at_subject}}\<close>

text \<open>The inputs are complete original questions. The implementation computes
  every actual producer and its independent original-goal reference once per
  question. Lookup only consumes this constructed table. Its equation connects
  each inspected cell to that actual producer and original question.\<close>

end
