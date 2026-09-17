theory Finite_Presented_Reasoning
  imports Finite_Presented_Evaluations Factor_Application_Execution Factor_Guided_Investigation
begin

section \<open>Natural coordinate schemas, libraries, applications and reasons\<close>

definition finite_natural_schema_value :: "(nat,nat,nat) finite_factor_schema \<Rightarrow> finite_factor_term" where
  "finite_natural_schema_value=finite_schema_presentation finite_natural_data finite_natural_data finite_natural_data"

definition finite_natural_premise_value :: "nat\<times>nat\<times>finite_factor_term \<Rightarrow> finite_factor_term" where
  "finite_natural_premise_value=finite_pair_presentation finite_natural_data (finite_coordinate_call_value finite_natural_data)"

definition finite_natural_enumeration_value :: "(nat\<times>nat\<times>nat finite_term_pattern) list \<Rightarrow> finite_factor_term" where
  "finite_natural_enumeration_value=finite_sequence_presentation (finite_pair_presentation finite_natural_data
    (finite_pair_presentation finite_natural_data (finite_pattern_presentation finite_natural_data)))"

definition finite_natural_library_value ::
  "(nat\<times>(nat,nat,nat) finite_factor_schema\<times>(nat\<times>nat\<times>nat finite_term_pattern) list) list \<Rightarrow> finite_factor_term" where
  "finite_natural_library_value=finite_sequence_presentation (finite_pair_presentation finite_natural_data
    (finite_pair_presentation finite_natural_schema_value finite_natural_enumeration_value))"

definition finite_natural_application_value :: "finite_natural_application \<Rightarrow> finite_factor_term" where
  "finite_natural_application_value=finite_pair_presentation id (finite_pair_presentation
    (finite_collection_presentation (finite_pair_presentation finite_natural_data id))
    (finite_collection_presentation finite_natural_premise_value))"

definition finite_natural_schema_application_value where
  "finite_natural_schema_application_value=finite_pair_presentation finite_natural_data
    (finite_pair_presentation finite_natural_schema_value finite_natural_application_value)"

definition finite_natural_reason_value where
  "finite_natural_reason_value=finite_pair_presentation (finite_coordinate_call_value finite_natural_data)
    (finite_pair_presentation (finite_collection_presentation finite_natural_premise_value)
      (finite_pair_presentation finite_natural_data (finite_coordinate_call_value finite_natural_data)))"

definition finite_guided_result_value where
  "finite_guided_result_value=finite_pair_presentation finite_boolean_data
    (finite_pair_presentation (finite_collection_presentation finite_natural_schema_application_value)
      (finite_pair_presentation (finite_collection_presentation finite_natural_premise_value)
        (finite_pair_presentation (finite_collection_presentation (finite_coordinate_call_value finite_natural_data))
          (finite_collection_presentation finite_natural_reason_value))))"

definition finite_guided_state_value where
  "finite_guided_state_value=finite_pair_presentation
    (finite_collection_presentation (finite_coordinate_call_value finite_natural_data))
    (finite_pair_presentation (finite_collection_presentation (finite_coordinate_call_value finite_natural_data))
      (finite_collection_presentation finite_natural_schema_application_value))"

definition finite_application_problem_view :: "finite_application_problem \<Rightarrow> _" where
  "finite_application_problem_view P=(application_entry P,application_schema P,application_enumeration P,
    application_frontier P,application_requests P,application_required P)"

lemma finite_application_problem_view_injective [intro]: "inj finite_application_problem_view"
proof (rule injI)
  fix x y :: finite_application_problem
  assume same: "finite_application_problem_view x=finite_application_problem_view y"
  show "x=y" by (rule finite_application_problem.equality; use same in \<open>simp add: finite_application_problem_view_def\<close>)
qed

definition finite_application_problem_value where
  "finite_application_problem_value=finite_viewed_value (finite_pair_presentation finite_natural_data
    (finite_pair_presentation finite_natural_schema_value (finite_pair_presentation finite_natural_enumeration_value
      (finite_pair_presentation (finite_collection_presentation (finite_coordinate_call_value finite_natural_data))
        (finite_pair_presentation (finite_collection_presentation (finite_coordinate_call_value finite_natural_data))
          (finite_collection_presentation finite_natural_application_value))))))
    finite_application_problem_view"

lemma finite_reasoning_values_injective [intro]:
  "inj finite_natural_schema_value" "inj finite_natural_premise_value" "inj finite_natural_enumeration_value"
  "inj finite_natural_library_value" "inj finite_natural_application_value"
  "inj finite_natural_schema_application_value" "inj finite_natural_reason_value"
  "inj finite_guided_result_value" "inj finite_guided_state_value" "inj finite_application_problem_value"
  unfolding finite_natural_schema_value_def finite_natural_premise_value_def finite_natural_enumeration_value_def
    finite_natural_library_value_def finite_natural_application_value_def finite_natural_schema_application_value_def
    finite_natural_reason_value_def finite_guided_result_value_def finite_guided_state_value_def
    finite_application_problem_value_def
  by (intro finite_schema_presentation_injective finite_natural_data_injective finite_pair_presentation_injective
      finite_coordinate_call_value_injective finite_sequence_presentation_injective finite_pattern_presentation_injective
      inj_on_id finite_collection_presentation_injective finite_boolean_data_injective finite_viewed_value_injective
      finite_application_problem_view_injective)+

text \<open>
  Natural coordinate schemas, premise occurrences, enumerations and compiled
  libraries specialize the coordinate presentations. An application keeps its
  conclusion, bindings and premises, and with its entry and schema its complete
  construction. A guided result keeps formation, every application, the
  residual goals, the demand and every reason; a guided state keeps its frontier,
  requests and applications. An application problem is presented through all
  of its record fields.
\<close>

end
