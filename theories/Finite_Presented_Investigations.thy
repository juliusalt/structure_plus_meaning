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

definition finite_assessment_table_value ::
  "('c \<Rightarrow> finite_factor_term) \<Rightarrow> ('a \<Rightarrow> finite_factor_term) \<Rightarrow>
    (nat\<times>'c\<times>(nat\<times>'a) list) list \<Rightarrow> finite_factor_term" where
  "finite_assessment_table_value fc fa=finite_sequence_presentation
    (finite_pair_presentation finite_natural_data (finite_pair_presentation fc
      (finite_sequence_presentation (finite_pair_presentation finite_natural_data fa))))"

lemma finite_assessment_table_value_injective [intro]:
  "inj fc \<Longrightarrow> inj fa \<Longrightarrow> inj (finite_assessment_table_value fc fa)"
  unfolding finite_assessment_table_value_def
  by (intro finite_sequence_presentation_injective finite_pair_presentation_injective finite_natural_data_injective)

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

definition finite_investigation_packet_value ::
  "('c \<Rightarrow> finite_factor_term) \<Rightarrow> ('a \<Rightarrow> finite_factor_term) \<Rightarrow> _ \<Rightarrow> finite_factor_term" where
  "finite_investigation_packet_value fc fa=finite_pair_presentation (finite_assessment_table_value fc fa)
    (finite_pair_presentation finite_investigation_comparison_value
      (finite_sequence_presentation finite_investigation_cycle_value))"

lemma finite_investigation_packet_value_injective [intro]:
  "inj fc \<Longrightarrow> inj fa \<Longrightarrow> inj (finite_investigation_packet_value fc fa)"
  unfolding finite_investigation_packet_value_def
  by (intro finite_pair_presentation_injective finite_assessment_table_value_injective
      finite_sequence_presentation_injective finite_investigation_values_injective)

text \<open>
  A context assessment table, its subject comparison and its investigation cycles
  have the same shape in every family; only the context and assessment
  presentations vary. Their indices and truth values keep the natural data
  presentation, and the packet presentation is injective whenever the family's
  context and assessment presentations are.
\<close>

end
