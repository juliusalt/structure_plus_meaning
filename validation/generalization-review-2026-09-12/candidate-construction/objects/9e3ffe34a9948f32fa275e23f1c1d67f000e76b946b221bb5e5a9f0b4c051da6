theory Factor_Generation_Source_Contracts
  imports Factor_Generation_Predecessor_Admission
begin

section \<open>The source notion owns the contracts used by later clients\<close>

theorem generation_source_native_presentation_class:
  "presentation_class generation_source_presents
    (\<lambda>z. generation_at_context (fst z) (snd z))
    (\<lambda>t. (152,t)\<in>positive_meaning generation_source_system)"
  using generation_source_presentation_class by (simp only: generation_source_exact)

theorem generation_core_report_native_presentation_class:
  "presentation_class generation_report_presents
    (\<lambda>z. generation_at_context (fst z) (snd z))
    (\<lambda>t. (151,t)\<in>positive_meaning generation_source_system)"
  using generation_report_presentation_class by (simp only: generation_core_report_exact)

theorem generation_predecessor_report_native_presentation_class:
  "presentation_class generation_predecessor_report_presents
    (\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and>
      snd z=generation_predecessor_rows (fst (fst (fst z))) (fst (snd (fst (fst z)))) (snd (snd (fst (fst z)))))
    (\<lambda>t. (155,t)\<in>positive_meaning generation_source_system)"
  using generation_predecessor_report_presentation_class by (simp only: generation_predecessor_report_exact)

interpretation generation_source_native_presentations: presentation_class generation_source_presents
  "\<lambda>z. generation_at_context (fst z) (snd z)" "\<lambda>t. (152,t)\<in>positive_meaning generation_source_system"
  by (rule generation_source_native_presentation_class)

interpretation generation_core_report_contract: presented_relation_contract
  source_root_presents site_context_formed "\<lambda>t. \<exists>z. source_root_presents z t"
  generation_value_presents generation_formed "\<lambda>t. (139,t)\<in>positive_meaning generation_value_system"
  generation_at_context "\<lambda>p q. (151,Pair_Term p q)\<in>positive_meaning generation_source_system"
  by (unfold_locales)
    (use source_root_presentation_class generation_native_presentation_class
      generation_core_report_exact generation_report_relation in \<open>auto simp: presentation_class_def\<close>)

theorem generation_core_source_native_class:
  "presentation_class generation_core_source_presents generation_formed
    (\<lambda>t. (152,t)\<in>positive_meaning generation_source_system)"
  using generation_core_source_presentation_class by (simp only: generation_source_exact)

theorem generation_source_conversion_exact:
  "(151,Pair_Term p q)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    presentation_transport generation_core_source_presents generation_value_presents p q"
  by (auto simp: generation_core_report_exact generation_report_presents_def
    generation_core_source_presents_def generation_source_presents_def
    factor_pair_presents_def presentation_transport_def)

interpretation generation_source_conversion: presented_function_contract
  generation_core_source_presents generation_formed "\<lambda>t. (152,t)\<in>positive_meaning generation_source_system"
  generation_value_presents generation_formed "\<lambda>t. (139,t)\<in>positive_meaning generation_value_system"
  id "\<lambda>p q. (151,Pair_Term p q)\<in>positive_meaning generation_source_system"
proof -
  have operation: "(\<lambda>p q. (151,Pair_Term p q)\<in>positive_meaning generation_source_system)=
      presentation_transport generation_core_source_presents generation_value_presents"
    by (intro ext; rule generation_source_conversion_exact)
  show "presented_function_contract generation_core_source_presents generation_formed
      (\<lambda>t. (152,t)\<in>positive_meaning generation_source_system)
      generation_value_presents generation_formed (\<lambda>t. (139,t)\<in>positive_meaning generation_value_system)
      id (\<lambda>p q. (151,Pair_Term p q)\<in>positive_meaning generation_source_system)"
    by (simp only: operation; rule presentation_identity_function[OF generation_core_source_native_class
      generation_native_presentation_class])
qed

lemma generation_predecessor_function_formed:
  assumes "generation_at_context (fst z) (snd z)"
  shows "finite (generation_predecessor_rows (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z)))) \<and>
    (\<forall>row\<in>generation_predecessor_rows (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z))).
      generation_predecessor_row_formed row)"
  using generation_predecessor_rows_complete(1)[OF assms] generation_predecessor_rows_formed by blast

interpretation generation_predecessor_function: presented_function_contract
  generation_source_presents "\<lambda>z. generation_at_context (fst z) (snd z)"
    "\<lambda>t. (152,t)\<in>positive_meaning generation_source_system"
  "data_collection_presents generation_predecessor_row_presents"
    "\<lambda>L. finite L \<and> (\<forall>row\<in>L. generation_predecessor_row_formed row)"
    "presented_predicate (data_sequence_presents generation_predecessor_row_presents) distinct"
  "\<lambda>z. generation_predecessor_rows (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z)))"
  "\<lambda>p q. (155,Pair_Term p q)\<in>positive_meaning generation_source_system"
  using generation_source_native_presentation_class generation_predecessor_collections.presentation_class_axioms
    generation_predecessor_function_formed
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def
    generation_predecessor_report_exact generation_predecessor_report_relation; blast)

corollary generation_core_report_invariance:
  assumes "source_root_presents z p" "generation_value_presents G q"
    "source_root_presents z p'" "generation_value_presents G q'"
  shows "(151,Pair_Term p q)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (151,Pair_Term p' q')\<in>positive_meaning generation_source_system"
  by (rule generation_core_report_contract.invariance[OF assms])

corollary generation_predecessor_report_invariance:
  assumes "generation_source_presents z p" "data_collection_presents generation_predecessor_row_presents L q"
    "generation_source_presents z p'" "data_collection_presents generation_predecessor_row_presents L q'"
  shows "(155,Pair_Term p q)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    (155,Pair_Term p' q')\<in>positive_meaning generation_source_system"
  by (rule generation_predecessor_function.invariance[OF assms])

corollary generation_predecessor_report_at_values:
  assumes "generation_source_presents ((E,(u,r)),G) p"
    "data_collection_presents generation_predecessor_row_presents L q"
  shows "(155,Pair_Term p q)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    L=generation_predecessor_rows E u r"
  using generation_predecessor_function.at[OF assms] by simp

corollary generation_predecessor_unrelated_rows_rejected:
  assumes "generation_source_presents ((E,(u,r)),G) p"
    "data_collection_presents generation_predecessor_row_presents L q" "L\<noteq>generation_predecessor_rows E u r"
  shows "(155,Pair_Term p q)\<notin>positive_meaning generation_source_system"
  using generation_predecessor_report_at_values[OF assms(1,2)] assms(3) by blast

corollary generation_predecessor_empty_report:
  assumes source: "environment_value_presents E e" and native: "generation_at E u r G"
  shows "(155,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (data_list_term []))
      \<in>positive_meaning generation_source_system \<longleftrightarrow>
    fset (generation_predecessors G)={}"
proof -
  have empty: "generation_predecessor_rows E u r={} \<longleftrightarrow> fset (generation_predecessors G)={}"
    using generation_predecessor_rows_complete(3)[OF native] by (auto simp: bij_betw_def)
  have collection: "data_collection_presents generation_predecessor_row_presents L (data_list_term []) \<longleftrightarrow> L={}"
    for L
    by (simp only: data_collection_presents_def data_list_term_injective; auto)
  show ?thesis by (simp only: generation_predecessor_report_on_source[OF source native] collection empty)
qed

corollary generation_predecessor_repeated_row_rejected:
  assumes source: "generation_source_presents z p"
    and rows: "generation_predecessor_row_presents row q" "generation_predecessor_row_presents row q'"
  shows "(155,Pair_Term p (data_list_term [q,q']))\<notin>positive_meaning generation_source_system"
proof
  assume "(155,Pair_Term p (data_list_term [q,q']))\<in>positive_meaning generation_source_system"
  then have admitted: "data_collection_presents generation_predecessor_row_presents
      (generation_predecessor_rows (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z)))) (data_list_term [q,q'])"
    by (simp only: generation_predecessor_function.output[OF source])
  obtain xs where distinct: "distinct xs" and "values": "list_all2 generation_predecessor_row_presents xs [q,q']"
    using admitted by (simp only: data_collection_presents_def data_list_term_injective) blast
  have repeated: "list_all2 generation_predecessor_row_presents [row,row] [q,q']"
    using rows by simp
  have same: "xs=[row,row]"
    by (rule presentation_class.list_recovery[OF generation_predecessor_row_presentation_class "values" repeated])
  show False using distinct by (simp add: same)
qed

section \<open>Total source and report witnesses cover every formed core\<close>

theorem generation_source_native_total:
  assumes formed: "generation_formed G"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>u p q rows.
    generation_at E u [] G \<and> generation_source_presents ((E,(u,[])),G) p \<and>
    generation_value_presents G q \<and>
    data_collection_presents generation_predecessor_row_presents (generation_predecessor_rows E u []) rows \<and>
    (152,p)\<in>positive_meaning generation_source_system \<and>
    (151,Pair_Term p q)\<in>positive_meaning generation_source_system \<and>
    (155,Pair_Term p rows)\<in>positive_meaning generation_source_system"
proof -
  obtain E :: "local_address option artifact_environment" and u where native: "generation_at E u [] G"
    using generation_presentation_total[OF formed] by blast
  obtain p where source: "generation_source_presents ((E,(u,[])),G) p"
    using generation_source_presentation_total[OF native] by blast
  obtain q where "value": "generation_value_presents G q" using generation_value_presents_total[OF formed] by blast
  have admitted: "(152,p)\<in>positive_meaning generation_source_system" using source by (auto simp: generation_source_exact)
  have core: "(151,Pair_Term p q)\<in>positive_meaning generation_source_system"
    using source "value" by (auto simp: generation_source_conversion_exact generation_core_source_presents_def
      presentation_transport_def)
  obtain rows where report: "(155,Pair_Term p rows)\<in>positive_meaning generation_source_system"
    using generation_predecessor_function.total[OF admitted] by blast
  have complete: "data_collection_presents generation_predecessor_row_presents (generation_predecessor_rows E u []) rows"
    using report by (simp only: generation_predecessor_function.output[OF source] fst_conv snd_conv)
  show ?thesis using native source "value" complete admitted core report by blast
qed

corollary generation_source_base_native_total:
  assumes "target_formed l" "target_formed p" "target_formed c"
  shows "\<exists>source. generation_core_source_presents (Generation l {||} p c) source \<and>
    (152,source)\<in>positive_meaning generation_source_system"
proof -
  have formed: "generation_formed (Generation l {||} p c)" by (rule generation_formed.formed[OF assms]) simp
  show ?thesis using generation_source_native_total[OF formed]
    by (auto simp: generation_core_source_presents_def)
qed

corollary generation_source_successor_native_total:
  assumes "generation_formed G" "target_formed l" "target_formed p" "target_formed c"
  shows "\<exists>source. generation_core_source_presents (Generation l {|G|} p c) source \<and>
    (152,source)\<in>positive_meaning generation_source_system"
proof -
  have formed: "generation_formed (Generation l {|G|} p c)"
    by (rule generation_formed.formed[OF assms(2-4)]) (use assms(1) in simp)
  show ?thesis using generation_source_native_total[OF formed]
    by (auto simp: generation_core_source_presents_def)
qed

section \<open>The least retained source preserves every reading and report\<close>

theorem generation_native_retention_presentation_class:
  "presentation_class generation_retention_presents
    (\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and>
      snd z=generation_source_environment (fst (fst (fst z))) (fst (snd (fst (fst z)))) (snd (snd (fst (fst z)))))
    (\<lambda>t. (152,t)\<in>positive_meaning generation_source_system)"
  using generation_retention_presentation_class by (simp only: generation_source_exact)

corollary generation_core_report_retention:
  assumes source: "environment_value_presents E e"
    and retained: "environment_value_presents (generation_source_environment E u r) f"
    and "value": "generation_value_presents G q"
  shows "(151,Pair_Term (generation_source_term f (use_data_term u) (Payload_Term r)) q)
      \<in>positive_meaning generation_source_system \<longleftrightarrow>
    (151,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) q)
      \<in>positive_meaning generation_source_system"
proof -
  have formed: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  show ?thesis by (simp only: generation_core_report_on_values[OF retained "value"]
    generation_core_report_on_values[OF source "value"] generation_source_environment_reading[OF formed])
qed

corollary generation_source_admission_retention:
  assumes source: "environment_value_presents E e"
    and retained: "environment_value_presents (generation_source_environment E u r) f"
  shows "(152,generation_source_term f (use_data_term u) (Payload_Term r))\<in>positive_meaning generation_source_system
    \<longleftrightarrow> (152,generation_source_term e (use_data_term u) (Payload_Term r))
      \<in>positive_meaning generation_source_system"
proof -
  have formed: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  show ?thesis by (simp only: generation_source_at_source[OF retained] generation_source_at_source[OF source]
    generation_source_environment_reading[OF formed])
qed

corollary generation_predecessor_admission_retention:
  assumes source: "environment_value_presents E e" and native: "generation_at E u r G"
    and retained: "environment_value_presents (generation_source_environment E u r) f"
  shows "(155,Pair_Term (generation_source_term f (use_data_term u) (Payload_Term r)) rows)
      \<in>positive_meaning generation_source_system \<longleftrightarrow>
    (155,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) rows)
      \<in>positive_meaning generation_source_system"
proof -
  have reread: "generation_at (generation_source_environment E u r) u r G"
    by (rule generation_source_environment_properties(2)[OF native])
  have site: "(u,r)\<in>generation_read_sites E {(u,r)}" using generation_read_sites_roots[of "{(u,r)}" E] by blast
  have same: "generation_predecessor_rows (generation_source_environment E u r) u r=generation_predecessor_rows E u r"
    using generation_source_environment_properties(7)[OF native] site by blast
  show ?thesis by (simp only: generation_predecessor_report_on_source[OF retained reread]
    generation_predecessor_report_on_source[OF source native] same)
qed

theorem generation_native_retention_least:
  assumes source: "environment_value_presents E e" and retained: "environment_value_presents F f"
    and included: "environment_included F E"
    and admitted: "(152,generation_source_term f (use_data_term u) (Payload_Term r))\<in>positive_meaning generation_source_system"
  shows "environment_included (generation_source_environment E u r) F"
proof -
  have formed: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  obtain H where native: "generation_at F u r H" using admitted by (simp only: generation_source_at_source[OF retained]) blast
  show ?thesis by (rule generation_source_environment_least[OF formed native included])
qed

section \<open>One fixed native program supplies all nine operations\<close>

abbreviation generation_child_value_lists_result :: "factor_term \<Rightarrow> bool" where
  "generation_child_value_lists_result t \<equiv> \<exists>a xs ys.
    t=context_relation_argument a (data_list_term xs) (data_list_term ys) \<and> term_formed a \<and>
    list_all2 (\<lambda>x y. generation_child_value_result (context_relation_argument a x y)) xs ys"

abbreviation generation_child_row_lists_result :: "factor_term \<Rightarrow> bool" where
  "generation_child_row_lists_result t \<equiv> \<exists>a xs ys.
    t=context_relation_argument a (data_list_term xs) (data_list_term ys) \<and> term_formed a \<and>
    list_all2 (\<lambda>x y. generation_child_row_result (context_relation_argument a x y)) xs ys"

theorem generation_source_list_operations_exact:
  "(150,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> generation_child_value_lists_result t"
  "(154,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> generation_child_row_lists_result t"
  by (simp_all add: generation_child_values.exact generation_child_rows.exact
    generation_child_value_exact generation_child_row_exact)

abbreviation generation_source_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_source_operation_result d t \<equiv>
    if d=147 then generation_syntax_result t
    else if d=148 then generation_fields_result t
    else if d=149 then generation_child_value_result t
    else if d=150 then generation_child_value_lists_result t
    else if d=151 then (\<exists>z. generation_report_presents z t)
    else if d=152 then (\<exists>z. generation_source_presents z t)
    else if d=153 then generation_child_row_result t
    else if d=154 then generation_child_row_lists_result t
    else (\<exists>z. generation_predecessor_report_presents z t)"

theorem generation_source_operations_exact:
  assumes "d\<in>{147,148,149,150,151,152,153,154,155}"
  shows "(d,t)\<in>positive_meaning generation_source_system \<longleftrightarrow> generation_source_operation_result d t"
  using assms by (auto simp: generation_syntax_exact generation_fields_exact generation_child_value_exact
    generation_source_list_operations_exact generation_core_report_exact generation_source_exact
    generation_child_row_exact generation_predecessor_report_exact; blast)

theorem native_generation_source_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {147::nat,148,149,150,151,152,153,154,155} \<and>
    (\<forall>d\<in>{147,148,149,150,151,152,153,154,155}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> generation_source_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{147,148,149,150,151,152,153,154,155}\<subseteq>system_definitions generation_source_system" by auto
  have calls: "schema_call_formed generation_source_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{147,148,149,150,151,152,153,154,155}" for d t
    using generation_source_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF generation_source_system_formed selected calls
    generation_source_operations_exact])
qed

text \<open>
  The exported contracts admit exactly the existing source, core-report, and
  predecessor-report classes. The source-to-value operation is the general
  semantic correspondence between two presentations of the same complete
  core. The predecessor operation is a total function on admitted actual
  sources, with every output presentation available. Later clients use those
  locally established contracts and the general adaptation and composition
  laws.

  Every formed finite core has an actual admitted source and both reports.
  Base and nonempty predecessor cases follow from that total result. Native
  admission also admits the existing determined retention class: the source
  determines its least required environment without storing it again.
  Replacing the supplied environment by that restriction preserves admission,
  every expected-core reading, and all complete-row tests. The leastness
  theorem ranges over every included environment that still passes admission.

  Factor_Generation_Scope_Contracts supplies the separate recorded-cause and
  payload-scope reports. Factor_Generation_Retention_Contracts supplies claims
  of the least retained environment through the source's existing determined
  class. Cause validity, higher protocol relations, and native checking of
  mathematical presentation contracts and proofs remain separate work.

  The compiled program and its nine distinct operation sites are fixed before
  future operands. Its full original scope, artifacts, and outgoing bindings
  are preserved. Empty helper lists require only formed context; whole source
  and report entries supply their actual environment and parent checks.
\<close>

end
