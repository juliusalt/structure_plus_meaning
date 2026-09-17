theory Requirement_Plan_Presentation
  imports Finite_Presented_Evaluations Finite_Term_Words Native_Package_Presentation
    Requirement_Artifact_Execution_Base Factor_Native_Requirement_Cases Factor_Requirement_Source_Boundary
begin

section \<open>Admission plans and requirement requests\<close>

fun finite_admission_instruction_value :: "admission_instruction \<Rightarrow> finite_factor_term" where
  "finite_admission_instruction_value (Pair_Admission_Instruction d a b)=Finite_Pair (Finite_Payload [0])
    (finite_pair_presentation finite_natural_data (finite_pair_presentation finite_natural_data finite_natural_data) (d,a,b))"
| "finite_admission_instruction_value (List_Admission_Instruction d a)=Finite_Pair (Finite_Payload [1])
    (finite_pair_presentation finite_natural_data finite_natural_data (d,a))"

lemma finite_admission_instruction_value_injective [intro]: "inj finite_admission_instruction_value"
proof (rule injI)
  fix x y assume same: "finite_admission_instruction_value x=finite_admission_instruction_value y"
  have pair: "inj (finite_pair_presentation finite_natural_data finite_natural_data)"
    by (intro finite_pair_presentation_injective finite_natural_data_injective)
  have triple: "inj (finite_pair_presentation finite_natural_data (finite_pair_presentation finite_natural_data finite_natural_data))"
    by (intro finite_pair_presentation_injective finite_natural_data_injective)
  show "x=y" using same by (cases x; cases y) (simp_all add: inj_eq[OF pair] inj_eq[OF triple] inj_eq[OF finite_natural_data_injective])
qed

definition finite_admission_plan_value :: "nat list\<times>nat\<times>admission_instruction list \<Rightarrow> finite_factor_term" where
  "finite_admission_plan_value=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation finite_natural_data (finite_sequence_presentation finite_admission_instruction_value))"

definition finite_requirement_request_value where
  "finite_requirement_request_value rest=finite_pair_presentation
    (finite_sequence_presentation (finite_goal_value finite_natural_data)) (finite_pair_presentation finite_natural_data rest)"

lemma finite_admission_plan_values_injective [intro]:
  "inj finite_admission_plan_value" "inj rest \<Longrightarrow> inj (finite_requirement_request_value rest)"
  unfolding finite_admission_plan_value_def finite_requirement_request_value_def
  by (intro finite_pair_presentation_injective finite_index_values_injective finite_natural_data_injective
      finite_sequence_presentation_injective finite_admission_instruction_value_injective finite_goal_value_injective)+

section \<open>Requirement plan and source report rows\<close>

definition finite_keyed_table_value :: "(finite_factor_term\<times>finite_factor_term) list \<Rightarrow> finite_factor_term" where
  "finite_keyed_table_value=finite_sequence_presentation (finite_pair_presentation id id)"

definition finite_checked_requirement_report_value where
  "finite_checked_requirement_report_value=finite_requirement_request_value (finite_pair_presentation finite_admission_plan_value
    (finite_pair_presentation finite_boolean_data (finite_pair_presentation finite_boolean_data
      (finite_pair_presentation finite_boolean_data (finite_option_presentation finite_admission_plan_value)))))"

definition finite_requirement_artifact_report_value where
  "finite_requirement_artifact_report_value=finite_requirement_request_value
    (finite_pair_presentation finite_artifact_value_rows_value (finite_pair_presentation finite_boolean_data
      (finite_pair_presentation (finite_option_presentation finite_admission_plan_value) finite_boolean_data)))"

definition finite_portable_requirement_report_value where
  "finite_portable_requirement_report_value=finite_pair_presentation finite_keyed_table_value
    (finite_pair_presentation finite_keyed_table_value (finite_pair_presentation (finite_sequence_presentation finite_boolean_data)
      (finite_pair_presentation finite_boolean_data
        (finite_option_presentation (finite_pair_presentation finite_admission_plan_value finite_boolean_data)))))"

definition finite_requirement_source_boundary_value where
  "finite_requirement_source_boundary_value=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation (finite_option_presentation finite_admission_plan_value)
      (finite_pair_presentation finite_boolean_data finite_boolean_data))"

definition finite_retained_clause_report_value where
  "finite_retained_clause_report_value=finite_pair_presentation finite_environment_rows_value
    (finite_pair_presentation (finite_schema_presentation Finite_Payload Finite_Payload finite_site_data)
      (finite_pair_presentation finite_environment_rows_value (finite_pair_presentation finite_use_data
        (finite_pair_presentation Finite_Payload (finite_pair_presentation finite_site_data
          (finite_pair_presentation (finite_sequence_presentation (finite_sequence_presentation finite_site_data))
            (finite_sequence_presentation finite_boolean_data)))))))"

definition finite_guard_meaning_value where
  "finite_guard_meaning_value=finite_pair_presentation (finite_sequence_presentation finite_site_data) finite_boolean_data"

definition finite_source_requirement_plan_value where
  "finite_source_requirement_plan_value=finite_pair_presentation (finite_option_presentation finite_admission_plan_value)
    (finite_sequence_presentation finite_boolean_data)"

lemma finite_requirement_report_rows_injective [intro]:
  "inj finite_keyed_table_value" "inj finite_checked_requirement_report_value"
  "inj finite_requirement_artifact_report_value" "inj finite_portable_requirement_report_value"
  "inj finite_requirement_source_boundary_value" "inj finite_retained_clause_report_value"
  "inj finite_guard_meaning_value" "inj finite_source_requirement_plan_value"
  unfolding finite_keyed_table_value_def finite_checked_requirement_report_value_def
    finite_requirement_artifact_report_value_def finite_portable_requirement_report_value_def
    finite_requirement_source_boundary_value_def finite_retained_clause_report_value_def
    finite_guard_meaning_value_def finite_source_requirement_plan_value_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective finite_admission_plan_values_injective
      finite_index_values_injective finite_boolean_data_injective finite_option_presentation_injective
      finite_artifact_value_rows_value_injective inj_on_id finite_environment_rows_value_injective
      finite_schema_presentation_injective finite_payload_injective finite_site_data_injective finite_use_data_injective)+

section \<open>The complete requirement plan and source reports\<close>

definition requirement_plan_counters :: "nat list" where
  "requirement_plan_counters=[353,354,360,1000]"

definition requirement_plan_presented_report where
  "requirement_plan_presented_report counters=(admission_sequence_reports,checked_requirement_source,
    checked_requirement_reports,requirement_artifact_reports,
    map (\<lambda>n. (n,portable_requirement_reports n)) counters)"

definition finite_requirement_plan_packet_value where
  "finite_requirement_plan_packet_value=finite_pair_presentation
    (finite_sequence_presentation (finite_requirement_request_value finite_admission_plan_value))
    (finite_pair_presentation finite_index_sequence_value
      (finite_pair_presentation (finite_sequence_presentation finite_checked_requirement_report_value)
        (finite_pair_presentation (finite_sequence_presentation finite_requirement_artifact_report_value)
          (finite_indexed_rows_value (finite_sequence_presentation finite_portable_requirement_report_value)))))"

definition requirement_plan_report_value where
  "requirement_plan_report_value counters=finite_requirement_plan_packet_value
    (requirement_plan_presented_report counters)"

definition retained_clause_indices :: "nat list" where
  "retained_clause_indices=[0..<15]"

definition requirement_source_presented_report where
  "requirement_source_presented_report ns cases=(
    map (\<lambda>b. (b,requirement_source_boundary_report b)) [False,True],
    map (\<lambda>n. (n,retained_clause_control_report n)) ns,
    map (\<lambda>b. (b,native_guard_source_meaning_report b)) [False,True],
    map (\<lambda>(b,p). ((b,p),source_requirement_plan_report b p)) cases)"

definition finite_requirement_source_packet_value where
  "finite_requirement_source_packet_value=finite_pair_presentation
    (finite_sequence_presentation (finite_pair_presentation finite_boolean_data finite_requirement_source_boundary_value))
    (finite_pair_presentation (finite_indexed_rows_value finite_retained_clause_report_value)
      (finite_pair_presentation (finite_sequence_presentation (finite_pair_presentation finite_boolean_data finite_guard_meaning_value))
        (finite_sequence_presentation (finite_pair_presentation (finite_pair_presentation finite_boolean_data finite_boolean_data)
          finite_source_requirement_plan_value))))"

definition requirement_source_report_value where
  "requirement_source_report_value ns cases=finite_requirement_source_packet_value
    (requirement_source_presented_report ns cases)"

lemma requirement_plan_packet_values_injective:
  "inj finite_requirement_plan_packet_value" "inj finite_requirement_source_packet_value"
  unfolding finite_requirement_plan_packet_value_def finite_requirement_source_packet_value_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective finite_admission_plan_values_injective
      finite_index_values_injective finite_requirement_report_rows_injective finite_indexed_rows_value_injective
      finite_boolean_data_injective)+

theorem requirement_plan_report_words_exact:
  "finite_term_shared_word (requirement_plan_report_value cs)=finite_term_shared_word (requirement_plan_report_value ds)
    \<longleftrightarrow> requirement_plan_presented_report cs=requirement_plan_presented_report ds"
  "finite_term_shared_word (requirement_source_report_value ns xs)=
    finite_term_shared_word (requirement_source_report_value ms ys) \<longleftrightarrow>
    requirement_source_presented_report ns xs=requirement_source_presented_report ms ys"
  by (simp_all add: finite_term_shared_word_injective requirement_plan_report_value_def
      requirement_source_report_value_def inj_eq[OF requirement_plan_packet_values_injective(1)]
      inj_eq[OF requirement_plan_packet_values_injective(2)])

text \<open>
  An admission plan keeps its entries, next definition and every instruction; a
  requirement request keeps its goals and start with its result. The requirement
  plan report keeps every sequence, checked, artifact and portable table request
  with its plans, observations and executions. The requirement source report keeps
  both source boundaries, every retained clause control with both complete
  environment rows, the expected schema, coordinates, recovered domains and
  observations, both guard meanings and every source requirement plan.
\<close>

end
