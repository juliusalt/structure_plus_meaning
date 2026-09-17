theory Finite_Presented_Investigations
  imports Finite_Presented_Coordinates
begin

section \<open>Every family shares the table, comparison and cycle presentations\<close>

definition finite_index_sequence_value :: "nat list \<Rightarrow> finite_factor_term" where
  "finite_index_sequence_value=finite_sequence_presentation finite_natural_data"

definition finite_index_pair_value :: "nat\<times>nat \<Rightarrow> finite_factor_term" where
  "finite_index_pair_value=finite_pair_presentation finite_natural_data finite_natural_data"

definition finite_indexed_pairs_value :: "(nat\<times>(nat\<times>nat) list) \<Rightarrow> finite_factor_term" where
  "finite_indexed_pairs_value=finite_pair_presentation finite_natural_data
    (finite_sequence_presentation finite_index_pair_value)"

definition finite_index_triple_value :: "nat\<times>nat\<times>nat \<Rightarrow> finite_factor_term" where
  "finite_index_triple_value=finite_pair_presentation finite_natural_data finite_index_pair_value"

definition finite_index_quadruple_value :: "nat\<times>nat\<times>nat\<times>nat \<Rightarrow> finite_factor_term" where
  "finite_index_quadruple_value=finite_pair_presentation finite_natural_data finite_index_triple_value"

lemma finite_index_values_injective [intro]:
  "inj finite_index_sequence_value" "inj finite_index_pair_value" "inj finite_indexed_pairs_value"
  "inj finite_index_triple_value" "inj finite_index_quadruple_value"
  unfolding finite_index_sequence_value_def finite_index_pair_value_def finite_indexed_pairs_value_def
    finite_index_triple_value_def finite_index_quadruple_value_def
  by (intro finite_sequence_presentation_injective finite_pair_presentation_injective finite_natural_data_injective)+

definition finite_indexed_rows_value :: "('a \<Rightarrow> finite_factor_term) \<Rightarrow> (nat\<times>'a) list \<Rightarrow> finite_factor_term" where
  "finite_indexed_rows_value f=finite_sequence_presentation (finite_pair_presentation finite_natural_data f)"

lemma finite_indexed_rows_value_injective [intro]: "inj f \<Longrightarrow> inj (finite_indexed_rows_value f)"
  unfolding finite_indexed_rows_value_def
  by (intro finite_sequence_presentation_injective finite_pair_presentation_injective finite_natural_data_injective)

definition finite_assessment_table_value ::
  "('c \<Rightarrow> finite_factor_term) \<Rightarrow> ('a \<Rightarrow> finite_factor_term) \<Rightarrow>
    (nat\<times>'c\<times>(nat\<times>'a) list) list \<Rightarrow> finite_factor_term" where
  "finite_assessment_table_value fc fa=finite_indexed_rows_value (finite_pair_presentation fc (finite_indexed_rows_value fa))"

lemma finite_assessment_table_value_injective [intro]:
  "inj fc \<Longrightarrow> inj fa \<Longrightarrow> inj (finite_assessment_table_value fc fa)"
  unfolding finite_assessment_table_value_def
  by (intro finite_indexed_rows_value_injective finite_pair_presentation_injective)

definition finite_investigation_comparison_value where
  "finite_investigation_comparison_value=finite_pair_presentation
    (finite_sequence_presentation finite_index_triple_value)
    (finite_pair_presentation (finite_sequence_presentation finite_index_pair_value)
      (finite_pair_presentation finite_index_sequence_value finite_index_sequence_value))"

definition finite_investigation_basis_value where
  "finite_investigation_basis_value=finite_pair_presentation finite_boolean_data
    (finite_pair_presentation (finite_sequence_presentation finite_index_pair_value)
      (finite_pair_presentation (finite_sequence_presentation finite_indexed_pairs_value)
        (finite_sequence_presentation (finite_pair_presentation finite_natural_data finite_indexed_pairs_value))))"

definition finite_investigation_repairs_value where
  "finite_investigation_repairs_value=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation (finite_sequence_presentation finite_index_quadruple_value)
      (finite_pair_presentation (finite_sequence_presentation finite_index_quadruple_value)
        (finite_sequence_presentation finite_index_pair_value)))"

definition finite_investigation_revision_value where
  "finite_investigation_revision_value=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation finite_index_sequence_value
      (finite_pair_presentation (finite_sequence_presentation finite_index_quadruple_value)
        (finite_pair_presentation finite_index_sequence_value (finite_sequence_presentation finite_index_pair_value))))"

definition finite_investigation_cycle_value where
  "finite_investigation_cycle_value=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation finite_investigation_basis_value
      (finite_pair_presentation finite_investigation_repairs_value
        (finite_pair_presentation finite_investigation_revision_value finite_investigation_basis_value)))"

lemma finite_investigation_values_injective [intro]:
  "inj finite_investigation_comparison_value" "inj finite_investigation_basis_value"
  "inj finite_investigation_repairs_value" "inj finite_investigation_revision_value"
  "inj finite_investigation_cycle_value"
  unfolding finite_investigation_comparison_value_def finite_investigation_basis_value_def
    finite_investigation_repairs_value_def finite_investigation_revision_value_def
    finite_investigation_cycle_value_def
  by (intro finite_sequence_presentation_injective finite_pair_presentation_injective finite_natural_data_injective
      finite_boolean_data_injective finite_index_values_injective)+

definition finite_investigation_outcome_value where
  "finite_investigation_outcome_value=finite_pair_presentation finite_investigation_comparison_value
    (finite_sequence_presentation finite_investigation_cycle_value)"

lemma finite_investigation_outcome_value_injective [intro]: "inj finite_investigation_outcome_value"
  unfolding finite_investigation_outcome_value_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective
      finite_investigation_values_injective)

definition finite_investigation_packet_value ::
  "('c \<Rightarrow> finite_factor_term) \<Rightarrow> ('a \<Rightarrow> finite_factor_term) \<Rightarrow> _ \<Rightarrow> finite_factor_term" where
  "finite_investigation_packet_value fc fa=finite_pair_presentation (finite_assessment_table_value fc fa)
    finite_investigation_outcome_value"

lemma finite_investigation_packet_value_injective [intro]:
  "inj fc \<Longrightarrow> inj fa \<Longrightarrow> inj (finite_investigation_packet_value fc fa)"
  unfolding finite_investigation_packet_value_def
  by (intro finite_pair_presentation_injective finite_assessment_table_value_injective
      finite_investigation_outcome_value_injective)

section \<open>Subject reports, separately listed assessments and development cycles\<close>

definition finite_subject_report_value ::
  "('x \<Rightarrow> finite_factor_term) \<Rightarrow> ('s \<Rightarrow> finite_factor_term) \<Rightarrow> ('r \<Rightarrow> finite_factor_term) \<Rightarrow>
    ('x\<times>'s\<times>(nat\<times>'r) list) option \<Rightarrow> finite_factor_term" where
  "finite_subject_report_value problem source result=finite_option_presentation
    (finite_pair_presentation problem (finite_pair_presentation source (finite_indexed_rows_value result)))"

lemma finite_subject_report_value_injective [intro]:
  "inj problem \<Longrightarrow> inj source \<Longrightarrow> inj result \<Longrightarrow> inj (finite_subject_report_value problem source result)"
  unfolding finite_subject_report_value_def
  by (intro finite_option_presentation_injective finite_pair_presentation_injective finite_indexed_rows_value_injective)

definition finite_subject_assessment_packet_value ::
  "('s \<Rightarrow> finite_factor_term) \<Rightarrow> ('a \<Rightarrow> finite_factor_term) \<Rightarrow> _ \<Rightarrow> finite_factor_term" where
  "finite_subject_assessment_packet_value subject cell=finite_pair_presentation (finite_indexed_rows_value subject)
    (finite_pair_presentation (finite_indexed_rows_value (finite_indexed_rows_value cell))
      finite_investigation_outcome_value)"

lemma finite_subject_assessment_packet_value_injective [intro]:
  "inj subject \<Longrightarrow> inj cell \<Longrightarrow> inj (finite_subject_assessment_packet_value subject cell)"
  unfolding finite_subject_assessment_packet_value_def
  by (intro finite_pair_presentation_injective finite_indexed_rows_value_injective
      finite_investigation_outcome_value_injective)

definition finite_subject_cycle_packet_value ::
  "('t \<Rightarrow> finite_factor_term) \<Rightarrow> ('c \<Rightarrow> finite_factor_term) \<Rightarrow> _ \<Rightarrow> finite_factor_term" where
  "finite_subject_cycle_packet_value table criticism=finite_pair_presentation table
    (finite_pair_presentation criticism (finite_pair_presentation finite_investigation_comparison_value
      (finite_pair_presentation finite_investigation_cycle_value finite_index_sequence_value)))"

lemma finite_subject_cycle_packet_value_injective [intro]:
  "inj table \<Longrightarrow> inj criticism \<Longrightarrow> inj (finite_subject_cycle_packet_value table criticism)"
  unfolding finite_subject_cycle_packet_value_def
  by (intro finite_pair_presentation_injective finite_investigation_values_injective finite_index_values_injective)

text \<open>
  A context assessment table, its subject comparison and its investigation cycles
  have the same shape in every family; only the context and assessment
  presentations vary. Their indices and truth values keep the natural data
  presentation, and the packet presentation is injective whenever the family's
  context and assessment presentations are. Indexed rows are the common layer
  of tables, subject lists and candidate cells. A subject report retains its
  optional problem, source reading and every candidate result; the subject and
  assessment packet lists those reports and cells separately before the
  outcome. A development cycle keeps its table and criticism with the
  comparison, one revision cycle and the admitted candidate indices. Each
  composite states only the injectivity contracts of its parts.
\<close>

end
