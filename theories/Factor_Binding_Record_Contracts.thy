theory Factor_Binding_Record_Contracts
  imports Factor_Binding_Record_Clauses Factor_Record_Instantiation_Outputs
begin

section \<open>The supplied rows are exactly the observations of the actual record\<close>

theorem binding_record_on_record:
  assumes source: "environment_value_presents E e"
    and raw: "pattern_record_at E v (set Bs) r (substitution_row_patterns As s) (set Is) (set Ks)"
    and variables: "\<forall>b\<in>set Bs. octets_formed b"
    and complete: "set Bs=(\<Union>a\<in>set As. pattern_variables (s a))"
    and orders: "distinct Bs" "distinct Is" "distinct Ks"
  shows "(348,binding_record_argument e (use_data_term v) (Payload_Term r)
      (data_list_term (map Payload_Term Bs)) (use_data_term u) bs
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
      \<in>positive_meaning binding_record_system \<longleftrightarrow>
    term_formed (use_data_term u) \<and>
      bs=positioned_binding_rows_term (map (\<lambda>a. ((u,a),pattern_claim_observation (s a))) As)"
proof -
  let ?B="data_list_term (map Payload_Term Bs)"
  let ?I="data_list_term (map Payload_Term Is)"
  let ?K="data_list_term (map Payload_Term Ks)"
  let ?xb="map (\<lambda>b. (b,Payload_Term b)) Bs"
  let ?yb="map (\<lambda>b. (b,Target_Term (Whole_Artifact empty_artifact))) Bs"
  let ?xs="binding_rows_term (map (\<lambda>a. (a,evaluate_pattern Payload_Term (s a))) As)"
  let ?ys="binding_rows_term (map (\<lambda>a. (a,evaluate_pattern
    (\<lambda>_. Target_Term (Whole_Artifact empty_artifact)) (s a))) As)"
  have replacements: "\<forall>a\<in>set As. octets_formed a \<and> pattern_formed (s a)"
    using pattern_record_formed[OF raw] by (auto simp: substitution_row_patterns_def)
  have replacement_variables: "\<forall>a\<in>set As. \<forall>b\<in>pattern_variables (s a). octets_formed b"
    using variables complete by blast
  have table_orders: "distinct ?xb" "distinct ?yb"
    using orders(1) by (auto simp: distinct_map inj_on_def)
  have tables: "set ?xb=image (\<lambda>b. (b,Payload_Term b)) (set Bs)"
    "set ?yb=image (\<lambda>b. (b,Target_Term (Whole_Artifact empty_artifact))) (set Bs)"
    by simp_all
  have instances:
    "(61,pattern_instantiation_argument e (use_data_term v) ?B (binding_rows_term ?xb)
      (Payload_Term r) ?xs ?B ?I ?K)\<in>positive_meaning record_instantiation_system"
    "(61,pattern_instantiation_argument e (use_data_term v) ?B (binding_rows_term ?yb)
      (Payload_Term r) ?ys ?B ?I ?K)\<in>positive_meaning record_instantiation_system"
    using substitution_record_two_instances[OF source replacements variables complete
      orders(1) table_orders orders(2,3) tables, where u=v and r=r] raw by blast+
  have markers: "(125,reference_bindings_value ?B (binding_rows_term ?xb) (binding_rows_term ?yb))
    \<in>positive_meaning reference_bindings_system"
    using variables by (simp only: reference_bindings_at_list)
  show ?thesis
  proof
    assume admitted: "(348,binding_record_argument e (use_data_term v) (Payload_Term r)
      ?B (use_data_term u) bs ?I ?K)\<in>positive_meaning binding_record_system"
    obtain xb yb xs ys where reads:
      "(125,reference_bindings_value ?B xb yb)\<in>positive_meaning reference_bindings_system"
      "(61,pattern_instantiation_argument e (use_data_term v) ?B xb (Payload_Term r) xs ?B ?I ?K)
        \<in>positive_meaning record_instantiation_system"
      "(61,pattern_instantiation_argument e (use_data_term v) ?B yb (Payload_Term r) ys ?B ?I ?K)
        \<in>positive_meaning record_instantiation_system"
      "(347,binding_observation_argument (use_data_term u) bs xs ys)\<in>positive_meaning binding_observation_program"
      using admitted by (simp only: binding_record_at_arguments binding_record_calls_def) blast
    have marker_values: "xb=binding_rows_term ?xb" "yb=binding_rows_term ?yb"
      using reads(1) by (auto simp only: reference_bindings_at_list)
    have first_output: "xs=?xs"
      by (rule record_instantiation_same_output[OF source _ instances(1)])
        (use reads(2) in \<open>simp only: marker_values\<close>)
    have second_output: "ys=?ys"
      by (rule record_instantiation_same_output[OF source _ instances(2)])
        (use reads(3) in \<open>simp only: marker_values\<close>)
    have owner_formed: "term_formed (use_data_term u)"
      using schema_call_formed_target[OF positive_meaning_formed[OF reads(4)]] by simp
    have rows: "bs=positioned_binding_rows_term (map (\<lambda>a. ((u,a),pattern_claim_observation (s a))) As)"
      using reads(4) by (simp only: first_output second_output
        binding_observation_at_pattern_rows[OF owner_formed replacements replacement_variables])
    show "term_formed (use_data_term u) \<and>
      bs=positioned_binding_rows_term (map (\<lambda>a. ((u,a),pattern_claim_observation (s a))) As)"
      using owner_formed rows by blast
  next
    assume fields: "term_formed (use_data_term u) \<and>
      bs=positioned_binding_rows_term (map (\<lambda>a. ((u,a),pattern_claim_observation (s a))) As)"
    have observations: "(347,binding_observation_argument (use_data_term u) bs ?xs ?ys)
      \<in>positive_meaning binding_observation_program"
      using binding_observation_pattern_rows[OF conjunct1[OF fields] replacements replacement_variables]
        fields by simp
    show "(348,binding_record_argument e (use_data_term v) (Payload_Term r)
      ?B (use_data_term u) bs ?I ?K)\<in>positive_meaning binding_record_system"
      by (simp only: binding_record_at_arguments binding_record_calls_def;
        rule exI[of _ "binding_rows_term ?xb"], rule exI[of _ "binding_rows_term ?yb"],
        rule exI[of _ ?xs], rule exI[of _ ?ys])
        (use markers instances observations in blast)
  qed
qed

text \<open>
  The record contributes actual patterns and their complete variable boundary.
  The supplied rows cannot choose a different pattern observation, discard a
  private variable, change an unreturned field, or exchange record sources
  between probes. Repeated source keys retain their record occurrences here;
  the node's binding-table reader separately imposes its functional boundary.
\<close>

end
