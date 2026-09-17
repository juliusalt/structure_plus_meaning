theory Finite_Presented_Decision_Families
 imports Finite_Inspected_Values Boolean_Decision_Assessments
begin

section \<open>Decision families present keyed optional subjects, readings and decisions\<close>

definition finite_optional_row_value ::
  "('k \<Rightarrow> finite_factor_term) \<Rightarrow> ('x \<Rightarrow> finite_factor_term) \<Rightarrow> 'k\<times>'x option \<Rightarrow> finite_factor_term" where
  "finite_optional_row_value key payload=finite_pair_presentation key (finite_option_presentation payload)"

lemma finite_optional_row_value_injective [intro]:
  "inj key \<Longrightarrow> inj payload \<Longrightarrow> inj (finite_optional_row_value key payload)"
  unfolding finite_optional_row_value_def
  by (intro finite_pair_presentation_injective finite_option_presentation_injective)

definition finite_prepared_decision_family_value where
  "finite_prepared_decision_family_value key subject report=finite_collection_presentation
    (finite_optional_row_value key (finite_pair_presentation subject report))"

lemma finite_prepared_decision_family_value_injective [intro]:
  "inj key \<Longrightarrow> inj subject \<Longrightarrow> inj report \<Longrightarrow> inj (finite_prepared_decision_family_value key subject report)"
  unfolding finite_prepared_decision_family_value_def
  by (intro finite_collection_presentation_injective finite_optional_row_value_injective
      finite_pair_presentation_injective)

definition finite_decision_row_assessment_value where
  "finite_decision_row_assessment_value key subject report=finite_optional_row_value key
    (finite_pair_presentation subject (finite_pair_presentation report
      (finite_pair_presentation finite_boolean_data finite_boolean_data)))"

lemma finite_decision_row_assessment_value_injective [intro]:
  "inj key \<Longrightarrow> inj subject \<Longrightarrow> inj report \<Longrightarrow> inj (finite_decision_row_assessment_value key subject report)"
  unfolding finite_decision_row_assessment_value_def
  by (intro finite_optional_row_value_injective finite_pair_presentation_injective finite_boolean_data_injective)

definition finite_decision_family_assessment_value where
  "finite_decision_family_assessment_value key subject report=finite_pair_presentation finite_boolean_data
    (finite_collection_presentation (finite_decision_row_assessment_value key subject report))"

lemma finite_decision_family_assessment_value_injective [intro]:
  "inj key \<Longrightarrow> inj subject \<Longrightarrow> inj report \<Longrightarrow> inj (finite_decision_family_assessment_value key subject report)"
  unfolding finite_decision_family_assessment_value_def
  by (intro finite_pair_presentation_injective finite_boolean_data_injective finite_collection_presentation_injective
      finite_decision_row_assessment_value_injective)

definition finite_decision_context_value where
  "finite_decision_context_value seed key subject report=finite_pair_presentation seed
    (finite_pair_presentation finite_natural_data (finite_pair_presentation finite_boolean_data
      (finite_prepared_decision_family_value key subject report)))"

lemma finite_decision_context_value_injective [intro]:
  "inj seed \<Longrightarrow> inj key \<Longrightarrow> inj subject \<Longrightarrow> inj report \<Longrightarrow>
    inj (finite_decision_context_value seed key subject report)"
  unfolding finite_decision_context_value_def
  by (intro finite_pair_presentation_injective finite_natural_data_injective finite_boolean_data_injective
      finite_prepared_decision_family_value_injective)

definition finite_decision_investigation_packet_value where
  "finite_decision_investigation_packet_value seed key subject report=finite_pair_presentation seed
    (finite_investigation_packet_value (finite_decision_context_value seed key subject report)
      (finite_decision_family_assessment_value key subject report))"

lemma finite_decision_investigation_packet_value_injective [intro]:
  "inj seed \<Longrightarrow> inj key \<Longrightarrow> inj subject \<Longrightarrow> inj report \<Longrightarrow>
    inj (finite_decision_investigation_packet_value seed key subject report)"
  unfolding finite_decision_investigation_packet_value_def
  by (intro finite_pair_presentation_injective finite_investigation_packet_value_injective
      finite_decision_context_value_injective finite_decision_family_assessment_value_injective)

section \<open>Previously accepted decision presentations with each row inspection\<close>

definition finite_decision_row_value where
 "finite_decision_row_value key subject report=finite_inspected_value
   (finite_decision_row_assessment_value key subject report) decision_row_inspect [0,1]"

lemma finite_decision_row_value_injective [intro]:
 "inj key \<Longrightarrow> inj subject \<Longrightarrow> inj report \<Longrightarrow>
   inj (finite_decision_row_value key subject report)"
 unfolding finite_decision_row_value_def
 by (intro finite_inspected_value_injective finite_decision_row_assessment_value_injective)

definition finite_decision_family_value where
 "finite_decision_family_value key subject report=finite_pair_presentation finite_boolean_data
   (finite_collection_presentation (finite_decision_row_value key subject report))"

lemma finite_decision_family_value_injective [intro]:
 "inj key \<Longrightarrow> inj subject \<Longrightarrow> inj report \<Longrightarrow>
   inj (finite_decision_family_value key subject report)"
 unfolding finite_decision_family_value_def
 by (intro finite_pair_presentation_injective finite_boolean_data_injective
     finite_collection_presentation_injective finite_decision_row_value_injective)

text \<open>
  A decision row is a key with an optional subject. Preparation pairs each subject
  with its reading; assessment adds the original and chosen decisions. A decision
  family assessment keeps its coverage with every assessed row, and a decision
  context keeps its seed, subject index, coverage and prepared family. The
  decision investigation packet specializes the investigation packet with those
  contexts and assessments. All are parameterized by the key, subject and reading
  presentations and state only their injectivity contracts.

  The last two presentations were accepted earlier and add each row's computed
  inspections to the assessed row. They are expressed through the assessed row
  here, and their words are unchanged. Such derived additions make a word's
  content depend on the chosen presentation; replacing them by the assessed row
  presentations remains open for the families that use them.
\<close>

end
