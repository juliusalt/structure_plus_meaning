theory Factor_Reader_Library_Coverage
  imports Factor_Library_Coverage Factor_Specialization_Report_Reasoning
    Factor_Binding_Observation_Reasoning Factor_Recursive_Construction_Investigation
begin

definition reader_construction_library ::
  "(nat\<times>(nat,nat,nat) finite_factor_schema\<times>(nat\<times>nat\<times>nat finite_term_pattern) list) list" where
  "reader_construction_library=specialization_report_reasoning_library @
    binding_observation_reasoning_library @ binding_list_construction_library"

lemma reader_construction_library_entries:
  "image fst (set reader_construction_library)={342,345,347}"
  by (auto simp: reader_construction_library_def specialization_report_reasoning_library_def
    binding_observation_reasoning_library_def binding_list_construction_library_def)

definition reader_library_coverage where
  "reader_library_coverage K goals=natural_library_coverage reader_construction_library K goals"

text \<open>
  This adequacy operation selects the existing native clause representations
  itself. It does not accept a manually supplied entry-dependency table.
  Its report is an abstraction of these constructors, with the universal
  obstruction contract from the generic coverage operation. It does not
  turn an unproved source call into known evidence.
\<close>

end
