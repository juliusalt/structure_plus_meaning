theory Factor_Source_Contracts
  imports Factor_Source_Lookup
begin

section \<open>Generic reader composition returns every artifact presentation\<close>

interpretation source_value_reading: presented_function_contract
  source_query_presents source_query_domain "\<lambda>p. \<exists>q. (243,Pair_Term p q)\<in>positive_meaning source_system"
  artifact_value_presents exact_formed "\<lambda>q. (11,q)\<in>positive_meaning artifact_admission_system" source_query_value
  "\<lambda>p q. (244,Pair_Term p q)\<in>positive_meaning source_system"
  using source_value_composition.function_contract[OF source_lookup_reading.presented_function_contract_axioms
    artifact_literal_reading.presented_function_contract_axioms]
  by simp

theorem source_value_exact:
  "(244,t)\<in>positive_meaning source_system \<longleftrightarrow>
    (\<exists>z p q. t=Pair_Term p q \<and> source_query_presents z p \<and>
      artifact_value_presents (source_query_value z) q)"
proof -
  have pair: "(244,Pair_Term p q)\<in>positive_meaning source_system \<longleftrightarrow>
      (\<exists>z. source_query_presents z p \<and> artifact_value_presents (source_query_value z) q)" for p q
    by (simp only: source_value_reading.exact presented_relation_def; blast)
  have shape: "(244,t)\<in>positive_meaning source_system \<Longrightarrow> \<exists>p q. t=Pair_Term p q"
    by (simp only: source_value_composition.exact; blast)
  show ?thesis using pair shape by blast
qed

theorem source_value_at_context:
  assumes "context": "source_context_presents (xs,B) c"
    and source: "construction_source_at xs B j R"
  shows "(244,Pair_Term (Pair_Term c (construction_source_term j)) q)\<in>positive_meaning source_system
    \<longleftrightarrow> artifact_value_presents R q"
proof -
  have query: "source_query_presents ((xs,B),j) (Pair_Term c (construction_source_term j))"
    using "context" source by (simp only: source_query_at; blast)
  have sf: "construction_sources_formed xs B" using source_contexts.subject_boundary[OF "context"] by simp
  show ?thesis using source_value_reading.output[OF query, of q] construction_source_value_at(1)[OF sf source]
    by simp
qed

theorem source_lookup_presentation_invariance:
  assumes first: "source_context_presents (xs,B) p" and second: "source_context_presents (xs,B) q"
  shows "(243,Pair_Term (Pair_Term p j) v)\<in>positive_meaning source_system \<longleftrightarrow>
      (243,Pair_Term (Pair_Term q j) v)\<in>positive_meaning source_system"
    "(244,Pair_Term (Pair_Term p j) v)\<in>positive_meaning source_system \<longleftrightarrow>
      (244,Pair_Term (Pair_Term q j) v)\<in>positive_meaning source_system"
  by (simp_all only: source_lookup_at_context[OF first] source_lookup_at_context[OF second]
    source_value_composition.at_pair)

section \<open>Missing sources and invalid unused material remain rejected\<close>

lemma source_operations_require_context:
  assumes "d\<in>{243,244}" "(d,Pair_Term (Pair_Term c j) q)\<in>positive_meaning source_system"
  shows "(242,c)\<in>positive_meaning source_system"
  using assms by (auto simp: source_value_composition.at_pair source_lookup_calls)

theorem source_invalid_context_rejected:
  assumes base: "finite_table_presents Payload_Term (\<lambda>R q. q=Target_Term (Whole_Artifact R)) B b"
    and invalid: "\<not>source_context_domain (xs,B)" and entry: "d\<in>{243,244}"
  shows "(d,Pair_Term (Pair_Term (Pair_Term (artifact_list_term xs) b) j) q)\<notin>positive_meaning source_system"
  using source_operations_require_context[OF entry] invalid source_context_at_fields[OF base, of xs] by blast

theorem source_missing_rejected:
  assumes "context": "source_context_presents (xs,B) c"
    and absent: "\<not>(\<exists>R. construction_source_at xs B j R)"
  shows "(243,Pair_Term (Pair_Term c (construction_source_term j)) q)\<notin>positive_meaning source_system"
    "(244,Pair_Term (Pair_Term c (construction_source_term j)) q)\<notin>positive_meaning source_system"
  using absent by (auto simp: source_value_composition.at_pair source_lookup_at_context[OF "context"]
    construction_source_term_exact)

corollary source_end_position_rejected:
  assumes "source_context_presents (xs,B) c" "length xs\<le>n"
  shows "(243,Pair_Term (Pair_Term c (natural_term n)) q)\<notin>positive_meaning source_system"
    "(244,Pair_Term (Pair_Term c (natural_term n)) q)\<notin>positive_meaning source_system"
  using source_missing_rejected[OF assms(1), of "Inl n" q] assms(2) by auto

theorem source_unused_duplicate_rejected:
  "\<exists>p b. (28,key_fibre_argument (Payload_Term []) p
      (data_list_term [Target_Term (Whole_Artifact empty_artifact)]))\<in>positive_meaning key_fibre_system \<and>
    (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)\<in>positive_meaning term_sequence_system \<and>
    (242,Pair_Term (artifact_list_term []) b)\<notin>positive_meaning source_system \<and>
    (243,Pair_Term (Pair_Term (Pair_Term (artifact_list_term []) b) (Payload_Term [])) (Target_Term (Whole_Artifact empty_artifact)))\<notin>positive_meaning source_system"
proof -
  let ?R="Target_Term (Whole_Artifact empty_artifact)"
  let ?pairs="[(Payload_Term [],?R),(Payload_Term [0],?R),(Payload_Term [0],?R)]"
  let ?rows="map (\<lambda>(k,v). Pair_Term k v) ?pairs"
  let ?p="data_list_term ?rows"
  let ?b="enumeration_term ?rows"
  have fibre: "(28,key_fibre_argument (Payload_Term []) ?p (data_list_term [?R]))\<in>positive_meaning key_fibre_system"
    by (simp only: key_fibre_lists) (simp add: octets_formed_def)
  have change: "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) ?p ?b)
      \<in>positive_meaning term_sequence_system"
  proof (simp only: term_sequence_enumeration_exact; rule conjI)
    show "term_formed ?p" by (simp add: data_list_term_formed octets_formed_def)
    show "enumeration_retermination ?p ?b"
      unfolding enumeration_retermination_def by (rule exI[of _ ?rows]) simp
  qed
  have unique: "p=?p" if "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p ?b)
      \<in>positive_meaning source_system" for p
  proof -
    have read: "enumeration_retermination p ?b"
      using that by (simp only: source_component_meanings(5) term_sequence_enumeration_exact; blast)
    have expected: "enumeration_retermination ?p ?b"
      using change by (simp only: term_sequence_enumeration_exact; blast)
    show ?thesis by (rule presentation_class.recovery[OF enumeration_retermination_class read expected])
  qed
  have keys: "(21,?p)\<notin>positive_meaning keyed_list_system"
    by (simp only: keyed_list_exact pair_list_term_injective) simp
  have "context": "(242,Pair_Term (artifact_list_term []) ?b)\<notin>positive_meaning source_system"
    using unique keys by (auto simp: source_context_calls source_base_table.exact source_component_meanings(3))
  have query: "(243,Pair_Term (Pair_Term (Pair_Term (artifact_list_term []) ?b) (Payload_Term [])) ?R)
      \<notin>positive_meaning source_system"
    using source_operations_require_context[of 243 "Pair_Term (artifact_list_term []) ?b" "Payload_Term []" ?R] "context" by blast
  show ?thesis by (rule exI[of _ ?p], rule exI[of _ ?b]) (use fibre change "context" query in blast)
qed

section \<open>Repeated positions and the two existing source roles remain distinct\<close>

theorem source_repeated_input_positions:
  assumes "exact_formed R" "exact_formed S"
  defines "c\<equiv>Pair_Term (artifact_list_term [R,S,R]) (enumeration_term [])"
  shows "source_query_presents (([R,S,R],{}),Inl 0) (Pair_Term c (natural_term 0))"
    "source_query_presents (([R,S,R],{}),Inl 2) (Pair_Term c (natural_term 2))"
    "(243,Pair_Term (Pair_Term c (natural_term 0)) (Target_Term (Whole_Artifact R)))\<in>positive_meaning source_system"
    "(243,Pair_Term (Pair_Term c (natural_term 2)) (Target_Term (Whole_Artifact R)))\<in>positive_meaning source_system"
    "Pair_Term c (natural_term 0)\<noteq>Pair_Term c (natural_term 2)"
proof -
  have base: "finite_table_presents Payload_Term (\<lambda>T p. p=Target_Term (Whole_Artifact T)) {} (enumeration_term [])"
    by (simp add: finite_table_presents_def finite_collection_presents_def single_valued_def)
  have "context": "source_context_presents ([R,S,R],{}) c"
    using assms(1,2) base by (simp add: source_base_fields c_def)
  show "source_query_presents (([R,S,R],{}),Inl 0) (Pair_Term c (natural_term 0))"
    "source_query_presents (([R,S,R],{}),Inl 2) (Pair_Term c (natural_term 2))"
    using "context" by (simp_all add: source_query_at)
  show "(243,Pair_Term (Pair_Term c (natural_term 0)) (Target_Term (Whole_Artifact R)))\<in>positive_meaning source_system"
    using source_lookup_at_context[OF "context", of "natural_term 0" "Target_Term (Whole_Artifact R)"]
    by (auto intro!: exI[of _ "Inl 0"])
  show "(243,Pair_Term (Pair_Term c (natural_term 2)) (Target_Term (Whole_Artifact R)))\<in>positive_meaning source_system"
    using source_lookup_at_context[OF "context", of "natural_term 2" "Target_Term (Whole_Artifact R)"]
    by (auto intro!: exI[of _ "Inl 2"])
  show "Pair_Term c (natural_term 0)\<noteq>Pair_Term c (natural_term 2)"
    by (simp only: factor_term.inject natural_term_exact; simp)
qed

theorem source_input_zero_and_empty_key:
  assumes "exact_formed R" "exact_formed S"
  defines "c\<equiv>Pair_Term (artifact_list_term [R])
    (enumeration_term [Pair_Term (Payload_Term []) (Target_Term (Whole_Artifact S))])"
  shows "(243,Pair_Term (Pair_Term c (natural_term 0)) (Target_Term (Whole_Artifact R)))\<in>positive_meaning source_system"
    "(243,Pair_Term (Pair_Term c (Payload_Term [])) (Target_Term (Whole_Artifact S)))\<in>positive_meaning source_system"
    "natural_term 0\<noteq>Payload_Term []"
proof -
  have base: "finite_table_presents Payload_Term (\<lambda>T p. p=Target_Term (Whole_Artifact T)) {([],S)}
      (enumeration_term [Pair_Term (Payload_Term []) (Target_Term (Whole_Artifact S))])"
    unfolding finite_table_presents_def finite_collection_presents_def
    by (rule conjI, simp add: single_valued_def, rule exI[of _ "[([],S)]"],
        rule exI[of _ "[Pair_Term (Payload_Term []) (Target_Term (Whole_Artifact S))]"])
      (simp add: table_entry_presents_def)
  have bases: "source_base_presents {([],S)}
      (enumeration_term [Pair_Term (Payload_Term []) (Target_Term (Whole_Artifact S))])"
    by (simp only: source_base_fields) (use assms(2) base in \<open>simp add: octets_formed_def\<close>)
  have "context": "source_context_presents ([R],{([],S)}) c"
    using assms(1) bases by (simp add: c_def)
  show "(243,Pair_Term (Pair_Term c (natural_term 0)) (Target_Term (Whole_Artifact R)))\<in>positive_meaning source_system"
    using source_lookup_at_context[OF "context", of "natural_term 0" "Target_Term (Whole_Artifact R)"]
    by (auto intro!: exI[of _ "Inl 0"])
  show "(243,Pair_Term (Pair_Term c (Payload_Term [])) (Target_Term (Whole_Artifact S)))\<in>positive_meaning source_system"
    using source_lookup_at_context[OF "context", of "Payload_Term []" "Target_Term (Whole_Artifact S)"]
    by (auto intro!: exI[of _ "Inr []"])
  show "natural_term 0\<noteq>Payload_Term []" by simp
qed

section \<open>One fixed native program precedes every future operand\<close>

abbreviation source_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "source_operation_result d t \<equiv>
    if d=237 then (\<exists>R. artifact_literal_presents R t)
    else if d=242 then (\<exists>C. source_context_presents C t)
    else if d=243 then (\<exists>z p q. t=Pair_Term p q \<and> source_query_presents z p \<and>
      artifact_literal_presents (source_query_value z) q)
    else (\<exists>z p q. t=Pair_Term p q \<and> source_query_presents z p \<and>
      artifact_value_presents (source_query_value z) q)"

lemma source_operations_exact:
  assumes "d\<in>{237,242,243,244}"
  shows "(d,t)\<in>positive_meaning source_system \<longleftrightarrow> source_operation_result d t"
  using assms by (auto simp: source_literal_exact source_context_exact source_lookup_exact source_value_exact; blast)

theorem native_source_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {237::nat,242,243,244} \<and>
    (\<forall>d\<in>{237,242,243,244}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> source_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{237,242,243,244}\<subseteq>system_definitions source_system" by auto
  have calls: "schema_call_formed source_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{237,242,243,244}" for d t using source_system_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF source_system_formed selected calls source_operations_exact])
qed

text \<open>
  The literal lookup and artifact-data projection share their intermediate
  class. The general composition profile therefore supplies the complete
  function contract, including every compatible artifact enumeration. Changing
  base-table order preserves lookup truth, while different input occurrences
  remain distinct even when their artifact values agree.

  The eight-definition group has eleven ordinary clauses over the least
  closure of six external callees. Four public sites are fixed before future
  operands and retain the exact native program environment, artifacts, and
  bindings. Source availability is now native. Complete construction admission,
  its separate global permission condition, recorded construction causes, and
  native mathematical-proof presentation remain further obligations.
\<close>

end
