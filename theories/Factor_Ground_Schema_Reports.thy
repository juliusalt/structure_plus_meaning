theory Factor_Ground_Schema_Reports
  imports Factor_Schema_Observations Factor_Pattern_Determination
begin

section \<open>Complete reports for exact-term recognizers\<close>

definition ground_schema_report :: "factor_term \<Rightarrow> factor_term" where
  "ground_schema_report t = schema_reference_value (Payload_Term []) t
    (Payload_Term []) (Payload_Term []) t (Payload_Term []) (Payload_Term [])"

theorem ground_recognizer_report:
  "schema_reference_presents (recognizer_schema (exact_term_pattern t))
    (ground_schema_report t) \<longleftrightarrow> term_formed t"
  by (simp add: schema_reference_presents_def schema_data_formed_def
    schema_reference_data_def schema_reference_outputs_def schema_reference_record_fields
    ground_schema_report_def recognizer_schema_def schema_formed_def schema_variables_def
    schema_sockets_def schema_dependencies_def rel_dom_def rel_ran_def single_valued_def
    evaluate_schema_premises_def evaluate_schema_materials_def)

text \<open>
  The exact term has no variables, ordinary premises or material premises.
  Both prescribed evaluations recover that same term. The report retains
  every field of the general schema formatter, and its formation condition
  is precisely the formation of the supplied term.
\<close>

end
