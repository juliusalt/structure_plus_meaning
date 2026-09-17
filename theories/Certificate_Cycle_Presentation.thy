theory Certificate_Cycle_Presentation
  imports Native_Certificate_Presentation Factor_Native_Certificate_Development
    Factor_Native_Certificate_Input_Development Factor_Native_Certificate_Scope_Repair
    Factor_Native_Certificate_Coverage_Investigation
begin

section \<open>Certificate coverage specializes conflicts over instantiated nodes\<close>

definition finite_conflict_value ::
  "('w \<Rightarrow> finite_factor_term) \<Rightarrow> ('s \<Rightarrow> finite_factor_term) \<Rightarrow> 'w\<times>'s\<times>'s \<Rightarrow> finite_factor_term" where
  "finite_conflict_value witness side=finite_pair_presentation witness (finite_pair_presentation side side)"

lemma finite_conflict_value_injective [intro]:
  "inj witness \<Longrightarrow> inj side \<Longrightarrow> inj (finite_conflict_value witness side)"
  unfolding finite_conflict_value_def
  by (intro finite_pair_presentation_injective)

definition finite_certificate_coverage_value :: "native_certificate_coverage_report \<Rightarrow> finite_factor_term" where
  "finite_certificate_coverage_value=finite_pair_presentation finite_certificate_paths_value
    (finite_pair_presentation (finite_collection_presentation
        (finite_conflict_value finite_native_schema_proof_value finite_instantiated_node_value))
      (finite_pair_presentation (finite_collection_presentation
          (finite_conflict_value finite_call_value finite_instantiated_node_value))
        (finite_collection_presentation
          (finite_conflict_value finite_instantiated_node_value finite_certificate_path_node_value))))"

definition finite_certificate_family_coverage_value ::
  "native_certificate_family_coverage_report \<Rightarrow> finite_factor_term" where
  "finite_certificate_family_coverage_value=finite_option_presentation (finite_collection_presentation
    (finite_pair_presentation finite_instantiated_node_value finite_certificate_coverage_value))"

definition finite_certificate_scope_coverage_value ::
  "native_certificate_family_coverage_report list \<Rightarrow> finite_factor_term" where
  "finite_certificate_scope_coverage_value=finite_sequence_presentation finite_certificate_family_coverage_value"

lemma finite_certificate_coverage_values_injective [intro]:
  "inj finite_certificate_coverage_value" "inj finite_certificate_family_coverage_value"
  "inj finite_certificate_scope_coverage_value"
proof -
  show coverage: "inj finite_certificate_coverage_value"
    unfolding finite_certificate_coverage_value_def
    by (intro finite_pair_presentation_injective finite_collection_presentation_injective finite_conflict_value_injective
        finite_certificate_paths_value_injective finite_native_schema_proof_value_injective
        finite_instantiated_node_value_injective finite_call_value_injective finite_certificate_path_node_value_injective)
  show family: "inj finite_certificate_family_coverage_value"
    unfolding finite_certificate_family_coverage_value_def
    by (intro finite_option_presentation_injective finite_collection_presentation_injective
        finite_pair_presentation_injective finite_instantiated_node_value_injective coverage)
  show "inj finite_certificate_scope_coverage_value"
    unfolding finite_certificate_scope_coverage_value_def
    by (intro finite_sequence_presentation_injective family)
qed

section \<open>Certificate inputs are queries or supplied certificate families\<close>

fun finite_certificate_input_value :: "native_certificate_input \<Rightarrow> finite_factor_term" where
  "finite_certificate_input_value (Native_Certificate_Query X)=Finite_Pair (Finite_Payload [0])
    (finite_option_presentation finite_native_history_subject_value X)"
| "finite_certificate_input_value (Native_Certificate_Supplied E u r A T)=Finite_Pair (Finite_Payload [1])
    (Finite_Pair (finite_native_history_subject_value (E,u,r,A))
      (finite_collection_presentation finite_history_certificate_value T))"

lemma finite_certificate_input_value_injective [intro]: "inj finite_certificate_input_value"
proof (rule injI)
  fix x y assume same: "finite_certificate_input_value x=finite_certificate_input_value y"
  have query: "inj (finite_option_presentation finite_native_history_subject_value)"
    by (intro finite_option_presentation_injective finite_native_history_subject_value_injective)
  have certificates: "inj (finite_collection_presentation finite_history_certificate_value)"
    by (intro finite_collection_presentation_injective finite_history_certificate_value_injective)
  show "x=y"
    using same by (cases x; cases y)
      (simp_all add: inj_eq[OF query] inj_eq[OF certificates] inj_eq[OF finite_native_history_subject_value_injective])
qed

section \<open>Development cycles specialize subject cycle packets over certificate tables\<close>

definition finite_certificate_development_packet_value where
  "finite_certificate_development_packet_value problem=finite_subject_cycle_packet_value
    (finite_certificate_table_value problem) (finite_indexed_rows_value finite_certificate_family_coverage_value)"

lemma finite_certificate_development_packet_value_injective [intro]:
  "inj problem \<Longrightarrow> inj (finite_certificate_development_packet_value problem)"
  unfolding finite_certificate_development_packet_value_def
  by (intro finite_subject_cycle_packet_value_injective finite_certificate_table_value_injective
      finite_indexed_rows_value_injective finite_certificate_coverage_values_injective)

definition native_certificate_development_presented_report where
  "native_certificate_development_presented_report ws selected=(let packet=native_certificate_development_packet ws selected
    in (native_certificate_indices,ws,packet,
      assessment_truth_rows (\<lambda>(result,A). native_certificate_inspect A) [0..<7]
        (map (\<lambda>(w,X,original,cells). (w,(X,original),cells)) (fst packet))))"

definition native_certificate_development_report_value where
  "native_certificate_development_report_value ws selected=finite_scoped_report_value
    (finite_certificate_development_packet_value (finite_option_presentation finite_native_history_subject_value))
    (native_certificate_development_presented_report ws selected)"

definition native_certificate_development_report_selections :: "nat list" where
  "native_certificate_development_report_selections=[0..<7]"

definition native_certificate_input_presented_report where
  "native_certificate_input_presented_report ws selected=(let packet=native_certificate_input_packet ws selected
    in (native_certificate_input_indices,ws,packet,
      assessment_truth_rows (\<lambda>(result,A). native_certificate_inspect A) [0..<7]
        (map (\<lambda>(w,X,original,cells). (w,(X,original),cells)) (fst packet))))"

definition native_certificate_input_report_value where
  "native_certificate_input_report_value ws selected=finite_scoped_report_value
    (finite_certificate_development_packet_value finite_certificate_input_value)
    (native_certificate_input_presented_report ws selected)"

definition native_certificate_input_report_selections :: "nat list" where
  "native_certificate_input_report_selections=[0..<7]"

section \<open>Coverage and scope repair investigations keep their complete original inputs\<close>

definition finite_certificate_coverage_packet_value where
  "finite_certificate_coverage_packet_value=finite_pair_presentation
    (finite_sequence_presentation (finite_option_presentation finite_native_history_subject_value))
    (finite_pair_presentation (finite_sequence_presentation finite_native_derivation_result_value)
      (finite_pair_presentation (finite_indexed_rows_value (finite_pair_presentation
          (finite_sequence_presentation finite_native_derivation_result_value)
          (finite_pair_presentation finite_boolean_data finite_certificate_scope_coverage_value)))
        finite_investigation_outcome_value))"

definition certificate_coverage_presented_report where
  "certificate_coverage_presented_report (ws::nat list) selections=(let packet=certificate_coverage_packet selections
    in ([0::nat],ws,packet,assessment_truth_rows (\<lambda>(result,A). certificate_coverage_inspect A) [0,1,2,3]
      (map (\<lambda>w. (w,(),fst (snd (snd packet)))) ws)))"

definition certificate_coverage_report_value where
  "certificate_coverage_report_value ws selections=finite_scoped_report_value finite_certificate_coverage_packet_value
    (certificate_coverage_presented_report ws selections)"

definition certificate_coverage_report_scope :: "nat list" where
  "certificate_coverage_report_scope=[0]"

definition certificate_coverage_report_selections :: "nat list list" where
  "certificate_coverage_report_selections=[[],[0],[0,1,2,3]]"

definition finite_certificate_scope_repair_packet_value where
  "finite_certificate_scope_repair_packet_value=finite_investigation_packet_value
    (finite_sequence_presentation finite_certificate_input_value)
    (finite_pair_presentation (finite_sequence_presentation finite_certificate_input_value)
      (finite_pair_presentation finite_boolean_data
        (finite_pair_presentation (finite_sequence_presentation finite_native_derivation_result_value)
          finite_certificate_scope_coverage_value)))"

definition certificate_scope_repair_presented_report where
  "certificate_scope_repair_presented_report (ws::nat list) selections=(let packet=certificate_scope_repair_packet selections
    in ([0::nat],ws,packet,assessment_truth_rows (\<lambda>(xs,A). certificate_scope_repair_inspect A) [0,1,2,3] (fst packet)))"

definition certificate_scope_repair_report_value where
  "certificate_scope_repair_report_value ws selections=finite_scoped_report_value
    finite_certificate_scope_repair_packet_value (certificate_scope_repair_presented_report ws selections)"

definition certificate_scope_repair_report_scope :: "nat list" where
  "certificate_scope_repair_report_scope=[0]"

definition certificate_scope_repair_report_selections :: "nat list list" where
  "certificate_scope_repair_report_selections=[[],[0],[0,1,2,3]]"

lemma certificate_cycle_report_values_injective:
  "inj (finite_scoped_report_value
    (finite_certificate_development_packet_value (finite_option_presentation finite_native_history_subject_value)))"
  "inj (finite_scoped_report_value (finite_certificate_development_packet_value finite_certificate_input_value))"
  "inj (finite_scoped_report_value finite_certificate_coverage_packet_value)"
  "inj (finite_scoped_report_value finite_certificate_scope_repair_packet_value)"
  unfolding finite_certificate_coverage_packet_value_def finite_certificate_scope_repair_packet_value_def
  by (intro finite_scoped_report_value_injective finite_certificate_development_packet_value_injective
      finite_option_presentation_injective finite_native_history_subject_value_injective
      finite_certificate_input_value_injective finite_pair_presentation_injective finite_sequence_presentation_injective
      finite_native_derivation_result_value_injective finite_indexed_rows_value_injective finite_boolean_data_injective
      finite_certificate_coverage_values_injective finite_investigation_outcome_value_injective
      finite_investigation_packet_value_injective)+

theorem certificate_cycle_report_words_exact:
  "finite_term_shared_word (native_certificate_development_report_value ws s)=
    finite_term_shared_word (native_certificate_development_report_value vs t) \<longleftrightarrow>
    native_certificate_development_presented_report ws s=native_certificate_development_presented_report vs t"
  "finite_term_shared_word (native_certificate_input_report_value ws s)=
    finite_term_shared_word (native_certificate_input_report_value vs t) \<longleftrightarrow>
    native_certificate_input_presented_report ws s=native_certificate_input_presented_report vs t"
  "finite_term_shared_word (certificate_coverage_report_value ws ss)=
    finite_term_shared_word (certificate_coverage_report_value vs ts) \<longleftrightarrow>
    certificate_coverage_presented_report ws ss=certificate_coverage_presented_report vs ts"
  "finite_term_shared_word (certificate_scope_repair_report_value ws ss)=
    finite_term_shared_word (certificate_scope_repair_report_value vs ts) \<longleftrightarrow>
    certificate_scope_repair_presented_report ws ss=certificate_scope_repair_presented_report vs ts"
  by (simp_all add: finite_term_shared_word_injective native_certificate_development_report_value_def
      native_certificate_input_report_value_def certificate_coverage_report_value_def
      certificate_scope_repair_report_value_def inj_eq[OF certificate_cycle_report_values_injective(1)]
      inj_eq[OF certificate_cycle_report_values_injective(2)] inj_eq[OF certificate_cycle_report_values_injective(3)]
      inj_eq[OF certificate_cycle_report_values_injective(4)])

text \<open>
  A conflict keeps its witness with both distinct sides. Coverage keeps every path
  with the proof, call and sharing conflicts over complete instantiated nodes; a
  family and a scope keep their coverage of every certificate. Inputs keep their
  queries or supplied families. A development packet specializes the subject
  cycle packet with a certificate table over its problem presentation and the
  scope criticism. Coverage and scope repair keep every original input, output,
  assessment, comparison and revision. Each presented report keeps its scopes,
  packet and every actual inspection; supplied certificate checks and criticism
  acceptance are determined by the presented packet and are not added to it.
\<close>

end
