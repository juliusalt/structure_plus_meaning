theory Finite_Portable_Table_Guard
  imports Factor_Portable_Table_Guard Finite_Keyed_Table_Comparison
begin

definition finite_portable_table_comparison where
  "finite_portable_table_comparison xs ys \<longleftrightarrow>
    finite_keyed_table_comparison xs ys \<and>
    (\<forall>(k,v)\<in>set xs. finite_data_projection v=Some v) \<and>
    (\<forall>(k,v)\<in>set ys. finite_data_projection v=Some v)"

theorem finite_portable_table_comparison_subject:
  "finite_portable_table_comparison xs ys \<longleftrightarrow>
    portable_table_comparison (decoded_keyed_rows xs) (decoded_keyed_rows ys)"
  by (simp only: finite_portable_table_comparison_def portable_table_comparison_def
    finite_keyed_table_comparison_def finite_keyed_rows_formed_correct decoded_keyed_rows_keys
    decoded_keyed_rows_set)
    (auto simp: case_prod_unfold)

theorem finite_portable_table_comparison_correct:
  "finite_portable_table_comparison xs ys \<longleftrightarrow>
    (360,Pair_Term (pair_list_term (decoded_keyed_rows xs)) (pair_list_term (decoded_keyed_rows ys)))
      \<in>positive_meaning portable_table_system"
  by (simp only: finite_portable_table_comparison_subject portable_table_gate_on_rows)

definition finite_portable_guard_schema where
  "finite_portable_guard_schema=finite_schema_of (requirement_guard_schema portable_table_requirements)"

lemmas finite_portable_guard_schema_code [code]=finite_portable_guard_schema_def
  [unfolded requirement_guard_schema_def portable_table_requirements_def
    finite_schema_of_def map_relation_values_def, simplified]

lemma decode_finite_portable_guard_schema:
  "decode_finite_schema finite_portable_guard_schema=requirement_guard_schema portable_table_requirements"
  unfolding finite_portable_guard_schema_def
  by (rule decode_finite_schema_of, rule requirement_guard_formed)
    (auto simp: portable_table_requirements_def single_valued_def)

definition portable_table_guard_library where
  "portable_table_guard_library=finite_compiled_library [(360,finite_portable_guard_schema)]"

lemma portable_table_guard_library_clause:
  assumes "(d,S,ps)\<in>set portable_table_guard_library"
  shows "d=360 \<and> decode_finite_schema S=requirement_guard_schema portable_table_requirements \<and>
    (\<exists>c. ((d,c),decode_finite_schema S)\<in>system_clauses portable_table_system)"
  using assms portable_table_installation.guarded_clauses
  by (auto simp: portable_table_guard_library_def finite_compiled_library_member
    decode_finite_portable_guard_schema portable_table_system_def)

export_code finite_portable_table_comparison portable_table_guard_library checking SML

end
