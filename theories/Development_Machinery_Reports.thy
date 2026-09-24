theory Development_Machinery_Reports
  imports Development_Machinery Development_Loop_Presentations Development_State_Presenter
begin

section \<open>The machinery's reports present its residual record\<close>

text \<open>
  The machinery is a residual record: every problem its constructor poses is residual and generated, so it
  cites nothing, and its problems are presented as their rows keyed by the state's constant keys, their
  contract terms carried in the machinery's names. A report that is not a presentation is the store's
  absence.
\<close>

abbreviation development_machinery_inert :: "isabelle_term \<Rightarrow> finite_factor_term" where
  "development_machinery_inert \<equiv> development_local_term_data (fst development_machinery_context)"

definition development_machinery_problem_data ::
    "development_machinery_problem_report \<Rightarrow> finite_factor_term option" where
  "development_machinery_problem_data=finite_partial_pair
    (development_problems_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None))
    (finite_partial_pair (Some \<circ> isabelle_positions_data)
      (finite_partial_pair
        (development_dependencies_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None))
        (development_problem_assessment_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None))))"

lemma development_machinery_problem_data_presented:
  assumes domain: "development_row_domain state_constant_key (\<lambda>_. None) (\<lambda>_. None) P"
  shows "finite_presented_on development_machinery_problem_data
    (lists P\<times>UNIV\<times>{D. fset D\<subseteq>P\<times>{X. fset X\<subseteq>UNIV\<times>P}}\<times>(lists P\<times>lists P\<times>lists P\<times>lists P\<times>UNIV))"
  unfolding development_machinery_problem_data_def
  by (intro finite_partial_pair_presented development_problems_data_presented finite_presented_total
    isabelle_collections_injective(2) development_dependencies_data_presented
    development_problem_assessment_data_presented domain)

definition development_machinery_problem_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_machinery_problem_value answered=finite_store_option id
    (development_machinery_problem_data (development_machinery_problem_report answered))"

definition development_machinery_loop_data :: "development_machinery_loop_report \<Rightarrow> finite_factor_term option" where
  "development_machinery_loop_data=finite_partial_pair
    (Some \<circ> finite_sequence_presentation (finite_option_presentation finite_development_context_value))
    (finite_partial_pair (Some \<circ> finite_option_presentation finite_development_context_value)
      (finite_partial_option
        (development_problems_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None))))"

lemma development_machinery_loop_data_presented:
  assumes domain: "development_row_domain state_constant_key (\<lambda>_. None) (\<lambda>_. None) P"
  shows "finite_presented_on development_machinery_loop_data (UNIV\<times>UNIV\<times>{x. set_option x\<subseteq>lists P})"
  unfolding development_machinery_loop_data_def
  by (intro finite_partial_pair_presented finite_presented_total finite_sequence_presentation_injective
    finite_option_presentation_injective finite_development_values_injective finite_partial_option_presented
    development_problems_data_presented domain)

definition development_machinery_loop_value :: "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_machinery_loop_value answered=finite_store_option id
    (development_machinery_loop_data (development_machinery_loop_report answered))"

definition development_machinery_verification_data ::
    "development_machinery_verification \<Rightarrow> finite_factor_term option" where
  "development_machinery_verification_data=finite_partial_option (finite_partial_pair
    (development_requests_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None))
    (finite_partial_pair (development_problems_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None))
      (Some \<circ> finite_sequence_presentation (finite_sequence_presentation
        (finite_pair_presentation development_verdict_data finite_boolean_data)))))"

lemma development_machinery_verification_data_presented:
  assumes domain: "development_row_domain state_constant_key (\<lambda>_. None) (\<lambda>_. None) P"
    and requests: "development_request_domain state_constant_key (\<lambda>_. None) (\<lambda>_. None) R"
  shows "finite_presented_on development_machinery_verification_data {x. set_option x\<subseteq>lists R\<times>lists P\<times>UNIV}"
  unfolding development_machinery_verification_data_def
  by (intro finite_partial_option_presented finite_partial_pair_presented development_requests_data_presented
    development_problems_data_presented finite_presented_total finite_sequence_presentation_injective
    finite_pair_presentation_injective development_verdict_data_injective finite_boolean_data_injective domain requests)

definition development_machinery_verification_value ::
    "development_problem fset \<Rightarrow> finite_factor_term" where
  "development_machinery_verification_value answered=finite_store_option id
    (development_machinery_verification_data (development_machinery_verification answered))"

definition development_machinery_native_judgment_value :: "String.literal \<Rightarrow> bool list \<Rightarrow> finite_factor_term" where
  "development_machinery_native_judgment_value n bits=finite_store_option id
    (development_named_native_judgment_data state_constant_key development_machinery_inert (\<lambda>_. None) (\<lambda>_. None)
      (development_named_native_judgment development_definition_verdict development_machinery_state
        (development_machinery_requests development_machinery_unanswered) n bits))"

end
