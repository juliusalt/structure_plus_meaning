theory Native_Package_Presentation
  imports Finite_Presented_Evaluations Finite_Presented_Native_Construction Finite_Term_Words
    Factor_Finite_Native_Extension_Cases Factor_Finite_Native_Controls
    Factor_Source_Observation_Investigation Factor_Finite_Source_Extension_Cases
begin

section \<open>Package observations, extensions and constructor controls\<close>

definition finite_package_observation_value where
  "finite_package_observation_value=finite_pair_presentation finite_boolean_data
    (finite_pair_presentation finite_boolean_data (finite_pair_presentation finite_boolean_data
      (finite_pair_presentation finite_use_data (finite_pair_presentation (finite_collection_presentation finite_native_system_value)
        (finite_pair_presentation finite_natural_data (finite_pair_presentation finite_natural_data
          finite_environment_rows_value))))))"

definition finite_native_extension_report_value where
  "finite_native_extension_report_value=finite_option_presentation
    (finite_pair_presentation finite_site_data finite_package_observation_value)"

definition finite_native_control_report_value where
  "finite_native_control_report_value=finite_pair_presentation finite_natural_system_value
    (finite_pair_presentation finite_boolean_data (finite_pair_presentation finite_boolean_data
      (finite_option_presentation (finite_pair_presentation
        (finite_collection_presentation (finite_pair_presentation finite_natural_data finite_site_data))
        finite_package_observation_value))))"

lemma finite_package_values_injective [intro]:
  "inj finite_package_observation_value" "inj finite_native_extension_report_value"
  "inj finite_native_control_report_value"
  unfolding finite_package_observation_value_def finite_native_extension_report_value_def
    finite_native_control_report_value_def
  by (intro finite_pair_presentation_injective finite_boolean_data_injective finite_use_data_injective
      finite_collection_presentation_injective finite_native_system_value_injective finite_natural_data_injective
      finite_environment_rows_value_injective finite_option_presentation_injective finite_site_data_injective
      finite_natural_system_value_injective)+

definition source_requirement_variants :: "(bool\<times>bool) list" where
  "source_requirement_variants=[(False,False),(False,True),(True,False),(True,True)]"

definition native_control_indices :: "nat list" where
  "native_control_indices=[0..<14]"

definition native_extension_presented_report where
  "native_extension_presented_report cases controls=
    (map (\<lambda>(b,p). ((b,p),finite_native_extension_report b p)) cases,
      map (\<lambda>i. (i,finite_native_control_report i)) controls)"

definition finite_native_extension_packet_value where
  "finite_native_extension_packet_value=finite_pair_presentation
    (finite_sequence_presentation (finite_pair_presentation (finite_pair_presentation finite_boolean_data finite_boolean_data)
      finite_native_extension_report_value))
    (finite_indexed_rows_value finite_native_control_report_value)"

definition native_extension_report_value where
  "native_extension_report_value cases controls=finite_native_extension_packet_value
    (native_extension_presented_report cases controls)"

section \<open>Source observations and source extensions\<close>

definition finite_source_example_report_value where
  "finite_source_example_report_value=finite_pair_presentation (finite_native_source_problem_value finite_native_system_value)
    (finite_pair_presentation (finite_collection_presentation finite_native_system_value)
      (finite_pair_presentation finite_boolean_data (finite_indexed_rows_value finite_boolean_data)))"

definition finite_source_extension_cases_value where
  "finite_source_extension_cases_value=finite_option_presentation (finite_native_source_problem_value
    (finite_pair_presentation finite_native_source_value
      (finite_sequence_presentation (finite_pair_presentation finite_natural_data
        (finite_pair_presentation finite_native_system_value (finite_pair_presentation finite_boolean_data
          (finite_pair_presentation finite_native_source_value
            (finite_option_presentation (finite_pair_presentation finite_native_system_value
              (finite_pair_presentation (finite_collection_presentation (finite_pair_presentation finite_site_data finite_site_data))
                (finite_pair_presentation finite_environment_presentation (finite_pair_presentation finite_use_data
                  (finite_pair_presentation (finite_collection_presentation finite_native_system_value)
                    (finite_collection_presentation finite_native_system_value))))))))))))))"

lemma finite_source_values_injective [intro]:
  "inj finite_source_example_report_value" "inj finite_source_extension_cases_value"
  unfolding finite_source_example_report_value_def finite_source_extension_cases_value_def
  by (intro finite_pair_presentation_injective finite_native_source_problem_value_injective
      finite_native_system_value_injective finite_collection_presentation_injective finite_boolean_data_injective
      finite_indexed_rows_value_injective finite_option_presentation_injective finite_native_source_value_injective
      finite_sequence_presentation_injective finite_natural_data_injective finite_site_data_injective
      finite_environment_presentation_injective finite_use_data_injective)+

definition native_source_example_indices :: "nat list" where
  "native_source_example_indices=[0,1,2,3,4,5,6]"

definition native_source_extension_indices :: "nat list" where
  "native_source_extension_indices=[0..<12]"

definition native_source_presented_report where
  "native_source_presented_report ws selections=(let
      observations=source_investigation_observations; relation=source_investigation_relation
    in (map (\<lambda>c. (c,source_example_report c)) ws,(observations,relation),
      map (investigation_cycle_report [0,1,2,3,4,5,6] [0,1,2,3] observations relation) selections,
      map (\<lambda>i. (i,finite_source_extension_cases i)) native_source_extension_indices))"

definition finite_native_source_packet_value where
  "finite_native_source_packet_value=finite_pair_presentation (finite_indexed_rows_value finite_source_example_report_value)
    (finite_pair_presentation (finite_pair_presentation (finite_sequence_presentation finite_index_triple_value)
        (finite_sequence_presentation finite_index_pair_value))
      (finite_pair_presentation (finite_sequence_presentation finite_investigation_cycle_value)
        (finite_indexed_rows_value finite_source_extension_cases_value)))"

definition native_source_report_value where
  "native_source_report_value ws selections=finite_native_source_packet_value
    (native_source_presented_report ws selections)"

definition native_source_report_selections :: "nat list list" where
  "native_source_report_selections=[[0,1,2],[],[3]]"

lemma native_package_packet_values_injective:
  "inj finite_native_extension_packet_value" "inj finite_native_source_packet_value"
  unfolding finite_native_extension_packet_value_def finite_native_source_packet_value_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective finite_boolean_data_injective
      finite_package_values_injective finite_indexed_rows_value_injective finite_source_values_injective
      finite_index_values_injective finite_investigation_values_injective)+

theorem native_package_report_words_exact:
  "finite_term_shared_word (native_extension_report_value cs is)=
    finite_term_shared_word (native_extension_report_value ds js) \<longleftrightarrow>
    native_extension_presented_report cs is=native_extension_presented_report ds js"
  "finite_term_shared_word (native_source_report_value ws s)=
    finite_term_shared_word (native_source_report_value vs t) \<longleftrightarrow>
    native_source_presented_report ws s=native_source_presented_report vs t"
  by (simp_all add: finite_term_shared_word_injective native_extension_report_value_def native_source_report_value_def
      inj_eq[OF native_package_packet_values_injective(1)] inj_eq[OF native_package_packet_values_injective(2)])

text \<open>
  A package observation keeps formation, both source matches, the selector use,
  every read package, both counts and the complete environment rows. Extension
  reports keep the entry, and constructor controls keep the candidate program,
  formation, agreement, coordinates and observation. Source examples keep each
  source problem, all readings, the match and every observation; source extension
  cases keep every target, admitted source, coordinate, environment and both
  readings. The presented reports keep every case, comparison and revision.
\<close>

end
