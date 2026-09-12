theory Factor_Ground_Schema_Reports
  imports Factor_Schema_Observations Factor_Pattern_Determination
begin

section \<open>One complete ground report retains ordinary and material rows\<close>

abbreviation ground_schema_rows_report where
  "ground_schema_rows_report t qs cs \<equiv> schema_reference_value (Payload_Term []) t
    (call_instance_rows_term qs) (binding_rows_term cs) t (call_instance_rows_term qs) (binding_rows_term cs)"

theorem ground_schema_reference_rows:
  assumes ground: "schema_variables S={}"
  shows "schema_reference_presents S (ground_schema_rows_report t qs cs) \<longleftrightarrow>
    schema_data_formed S \<and> distinct qs \<and> distinct cs \<and>
      schema_instance S {} t (set qs) \<and> set cs=material_instance_relation {} (schema_material_premises S)"
proof
  assume admitted: "schema_reference_presents S (ground_schema_rows_report t qs cs)"
  obtain Vs u rs ds v ws es where raw:
    "schema_data_formed S" "distinct Vs" "set Vs=schema_variables S"
    "distinct rs" "distinct ds" "distinct ws" "distinct es"
    "schema_instance S (image (\<lambda>a. (a,Payload_Term a)) (set Vs)) u (set rs)"
    "set ds=material_instance_relation (image (\<lambda>a. (a,Payload_Term a)) (set Vs)) (schema_material_premises S)"
    "schema_instance S (image (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) (set Vs)) v (set ws)"
    "set es=material_instance_relation (image (\<lambda>a. (a,Target_Term (Whole_Artifact empty_artifact))) (set Vs)) (schema_material_premises S)"
    "ground_schema_rows_report t qs cs=schema_reference_value (data_list_term (map Payload_Term Vs)) u
      (call_instance_rows_term rs) (binding_rows_term ds) v (call_instance_rows_term ws) (binding_rows_term es)"
    using schema_reference_presents_fields[THEN iffD1, OF admitted] by blast
  have empty_scope: "Vs=[]" using raw(3) ground by auto
  have encoded: "t=u \<and> call_instance_rows_term qs=call_instance_rows_term rs \<and>
      binding_rows_term cs=binding_rows_term ds \<and> t=v \<and>
      call_instance_rows_term qs=call_instance_rows_term ws \<and> binding_rows_term cs=binding_rows_term es"
    using raw(12) by (auto simp only: factor_term.inject)
  have shape: "t=u" "qs=rs" "cs=ds" "t=v" "qs=ws" "cs=es"
    using encoded by (auto simp only: binding_rows_term_injective call_instance_rows_map_injective)
  show "schema_data_formed S \<and> distinct qs \<and> distinct cs \<and>
      schema_instance S {} t (set qs) \<and> set cs=material_instance_relation {} (schema_material_premises S)"
    using raw(1,4,5,8,9) shape by (auto simp: empty_scope)
next
  assume fields: "schema_data_formed S \<and> distinct qs \<and> distinct cs \<and>
    schema_instance S {} t (set qs) \<and> set cs=material_instance_relation {} (schema_material_premises S)"
  show "schema_reference_presents S (ground_schema_rows_report t qs cs)"
    unfolding schema_reference_presents_fields
    by (rule conjI, use fields in blast, rule exI[of _ "[]"], rule exI[of _ t],
      rule exI[of _ qs], rule exI[of _ cs], rule exI[of _ t], rule exI[of _ qs], rule exI[of _ cs])
      (use fields ground in simp)
qed

definition ground_schema_report :: "factor_term \<Rightarrow> factor_term" where
  "ground_schema_report t = schema_reference_value (Payload_Term []) t
    (Payload_Term []) (Payload_Term []) t (Payload_Term []) (Payload_Term [])"

theorem ground_recognizer_report:
  "schema_reference_presents (recognizer_schema (exact_term_pattern t))
    (ground_schema_report t) \<longleftrightarrow> term_formed t"
proof -
  have ground: "schema_variables (recognizer_schema (exact_term_pattern t))={}" by simp
  show ?thesis
    using ground_schema_reference_rows[OF ground, where t=t and qs="[]" and cs="[]"]
    by (simp add: ground_schema_report_def schema_data_formed_def recognizer_schema_def schema_formed_def schema_variables_def
        schema_sockets_def schema_dependencies_def rel_dom_def rel_ran_def single_valued_def
        schema_instance_def schema_premise_instance_def term_bindings_formed_def
        call_instance_relation_def material_instance_relation_def)
qed

text \<open>
  An empty complete binder makes both prescribed evaluations the same
  instance. The general equation keeps the full ordinary and material rows,
  their distinct enumerations and schema-data formation. The exact-term
  recognizer consumes that equation with both row families empty.
\<close>

end
