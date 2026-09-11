theory Factor_Judgment_Retention_Contracts
  imports Factor_Judgment_Dependency_Contracts Factor_Native_Equality Factor_Compiled_Applications
begin

section \<open>The judgment boundary owns closed admission and its retention function\<close>

theorem judgment_closed_source_native_class:
  "presentation_class judgment_closed_source_presents
    (\<lambda>z. judgment_source_readable z \<and> judgment_required_environment z=fst z)
    (\<lambda>p. (183,p)\<in>positive_meaning judgment_retention_system)"
  using judgment_closed_source_presentation_class by (simp only: judgment_closed_source_exact)

theorem judgment_retention_report_native_class:
  "presentation_class judgment_retention_report_presents
    (\<lambda>z. judgment_source_readable (fst z) \<and> snd z=judgment_required_environment (fst z))
    (\<lambda>p. (184,p)\<in>positive_meaning judgment_retention_system)"
  using judgment_retention_report_presentation_class by (simp only: judgment_retention_report_exact)

interpretation judgment_retention_function: presented_function_contract
  judgment_source_presents judgment_source_readable "\<lambda>p. (178,p)\<in>positive_meaning judgment_retention_system"
  environment_value_presents environment_formed "\<lambda>p. (26,p)\<in>positive_meaning environment_admission_system"
  judgment_required_environment "\<lambda>p q. (184,Pair_Term p q)\<in>positive_meaning judgment_retention_system"
  using judgment_source_native_class environment_presentations.presentation_class_axioms judgment_required_environment_formed
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def
    judgment_retention_report_exact judgment_retention_report_relation; blast)

corollary judgment_retention_report_output:
  assumes source: "judgment_source_presents z p"
  shows "(184,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    environment_value_presents (judgment_required_environment z) q"
  by (rule judgment_retention_function.output[OF source])

corollary judgment_retention_report_invariance:
  assumes "judgment_source_presents z p" "environment_value_presents F q"
    "judgment_source_presents z p'" "environment_value_presents F q'"
  shows "(184,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (184,Pair_Term p' q')\<in>positive_meaning judgment_retention_system"
  by (rule judgment_retention_function.invariance[OF assms])

corollary judgment_retention_wrong_environment_rejected:
  assumes source: "judgment_source_presents z p" and claim: "environment_value_presents F f"
    and wrong: "F\<noteq>judgment_required_environment z"
  shows "(184,Pair_Term p f)\<notin>positive_meaning judgment_retention_system"
  using judgment_retention_function.at[OF source claim] wrong by simp

corollary judgment_retention_wrong_use_domain_rejected:
  assumes source: "judgment_source_presents z p" and claim: "environment_value_presents F f"
    and wrong: "environment_uses F\<noteq>judgment_required_uses z"
  shows "(184,Pair_Term p f)\<notin>positive_meaning judgment_retention_system"
proof -
  have readable: "judgment_source_readable z" using source by (simp add: judgment_source_presents_def)
  have different: "F\<noteq>judgment_required_environment z"
    using wrong judgment_required_environment_domains(1)[OF readable] by blast
  show ?thesis by (rule judgment_retention_wrong_environment_rejected[OF source claim different])
qed

corollary judgment_retention_wrong_slot_domain_rejected:
  assumes source: "judgment_source_presents z p" and claim: "environment_value_presents F f"
    and wrong: "rel_dom (environment_bindings F)\<noteq>judgment_required_slots z"
  shows "(184,Pair_Term p f)\<notin>positive_meaning judgment_retention_system"
proof -
  have readable: "judgment_source_readable z" using source by (simp add: judgment_source_presents_def)
  have different: "F\<noteq>judgment_required_environment z"
    using wrong judgment_required_environment_domains(2)[OF readable] by blast
  show ?thesis by (rule judgment_retention_wrong_environment_rejected[OF source claim different])
qed

corollary judgment_nonminimal_source_rejected:
  assumes source: "judgment_source_presents z p" and larger: "judgment_required_environment z\<noteq>fst z"
  shows "(183,p)\<notin>positive_meaning judgment_retention_system"
  by (simp only: judgment_closed_source_at_presentation[OF source]; rule larger)

corollary judgment_unused_binding_rejected:
  assumes source: "judgment_source_presents z p" and stored: "a\<in>rel_dom (environment_bindings (fst z))"
    and unused: "a\<notin>judgment_required_slots z"
  shows "(183,p)\<notin>positive_meaning judgment_retention_system"
proof -
  have readable: "judgment_source_readable z" using source by (simp add: judgment_source_presents_def)
  have larger: "judgment_required_environment z\<noteq>fst z"
  proof
    assume same: "judgment_required_environment z=fst z"
    have domain: "rel_dom (environment_bindings (fst z))=judgment_required_slots z"
      using judgment_required_environment_domains(2)[OF readable] by (simp only: same)
    show False using stored unused by (simp only: domain)
  qed
  show ?thesis by (rule judgment_nonminimal_source_rejected[OF source larger])
qed

corollary judgment_unused_artifact_rejected:
  assumes source: "judgment_source_presents z p" and stored: "u\<in>environment_uses (fst z)"
    and unused: "u\<notin>judgment_required_uses z"
  shows "(183,p)\<notin>positive_meaning judgment_retention_system"
proof -
  have readable: "judgment_source_readable z" using source by (simp add: judgment_source_presents_def)
  have larger: "judgment_required_environment z\<noteq>fst z"
  proof
    assume same: "judgment_required_environment z=fst z"
    have domain: "environment_uses (fst z)=judgment_required_uses z"
      using judgment_required_environment_domains(1)[OF readable] by (simp only: same)
    show False using stored unused by (simp only: domain)
  qed
  show ?thesis by (rule judgment_nonminimal_source_rejected[OF source larger])
qed

section \<open>Every accepted report recovers the actual material and both readings\<close>

theorem judgment_native_retention_material:
  assumes source: "judgment_source_presents (E,((pu,pr),(au,ar))) p"
    and expected: "environment_value_presents F f"
    and report: "(184,Pair_Term p f)\<in>positive_meaning judgment_retention_system"
  shows "F=native_judgment_environment E pu pr au ar"
    and "environment_included F E"
    and "artifact_at F u R \<longleftrightarrow>
      u\<in>judgment_required_uses (E,((pu,pr),(au,ar))) \<and> artifact_at E u R"
    and "binds_slot F u k v \<longleftrightarrow> (u,k)\<in>native_judgment_demands E pu pr au ar \<and> binds_slot E u k v"
    and "environment_closed F {pu,au} (native_judgment_demands F pu pr au ar)"
    and "native_package_at F pu pr Q \<longleftrightarrow> native_package_at E pu pr Q"
    and "native_application_at F au ar d t I K \<longleftrightarrow> native_application_at E au ar d t I K"
    and "native_application_formed F pu pr au ar \<longleftrightarrow> native_application_formed E pu pr au ar"
    and "native_positive_holds F pu pr au ar \<longleftrightarrow> native_positive_holds E pu pr au ar"
    and "native_package_environment F pu pr=native_package_environment E pu pr"
proof -
  show same: "F=native_judgment_environment E pu pr au ar"
    using report judgment_retention_function.at[OF source expected] by simp
  obtain A c x J L where package: "native_package_at E pu pr A" and app: "native_application_at E au ar c x J L"
    using source by (auto simp: judgment_source_presentation_fields)
  have formed: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have kept: "native_package_at F pu pr A" "native_application_at F au ar c x J L"
    using native_judgment_environment_recovers(1,2)[OF package app] by (simp_all only: same)
  show included: "environment_included F E" by (simp only: same; rule native_judgment_environment_included)
  show "artifact_at F u R \<longleftrightarrow>
      u\<in>judgment_required_uses (E,((pu,pr),(au,ar))) \<and> artifact_at E u R"
    by (simp add: same native_judgment_environment_def)
  show "binds_slot F u k v \<longleftrightarrow> (u,k)\<in>native_judgment_demands E pu pr au ar \<and> binds_slot E u k v"
    by (simp add: same native_judgment_environment_def)
  show "environment_closed F {pu,au} (native_judgment_demands F pu pr au ar)"
    by (simp only: same; rule native_judgment_environment_closed[OF package app])
  have retained_package: "native_package_at F pu pr Q" if "native_package_at E pu pr Q"
    using native_judgment_environment_recovers(1)[OF that app] by (simp only: same)
  show "native_package_at F pu pr Q \<longleftrightarrow> native_package_at E pu pr Q"
    using retained_package native_package_included[OF _ included formed] by blast
  have retained_app: "native_application_at F au ar d t I K" if "native_application_at E au ar d t I K"
    using native_judgment_environment_recovers(2)[OF package that] by (simp only: same)
  show "native_application_at F au ar d t I K \<longleftrightarrow> native_application_at E au ar d t I K"
    using retained_app native_application_included[OF _ included formed] by blast
  show "native_application_formed F pu pr au ar \<longleftrightarrow> native_application_formed E pu pr au ar"
    by (simp only: native_application_formed_with_reads[OF kept] native_application_formed_with_reads[OF package app])
  show "native_positive_holds F pu pr au ar \<longleftrightarrow> native_positive_holds E pu pr au ar"
    by (simp only: same; rule native_judgment_environment_truth[OF package app])
  show "native_package_environment F pu pr=native_package_environment E pu pr"
    by (simp only: same; rule native_judgment_program_environment[OF package app])
qed

theorem judgment_retention_preserves_reports:
  assumes source: "judgment_source_presents z p"
    and retained: "judgment_source_presents (judgment_required_environment z,snd z) p'"
  shows "(184,Pair_Term p q)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (184,Pair_Term p' q)\<in>positive_meaning judgment_retention_system"
proof -
  have readable: "judgment_source_readable z" using source by (simp add: judgment_source_presents_def)
  show ?thesis by (simp only: judgment_retention_function.output[OF source] judgment_retention_function.output[OF retained]
    judgment_retained_context(2)[OF readable])
qed

theorem judgment_retention_claim_supplies_closed_source:
  assumes source: "judgment_source_presents (E,((pu,pr),(au,ar))) p"
    and report: "(184,Pair_Term p f)\<in>positive_meaning judgment_retention_system"
  shows "judgment_closed_source_presents (native_judgment_environment E pu pr au ar,((pu,pr),(au,ar)))
      (judgment_context_term f (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar))"
    and "(183,judgment_context_term f (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar))
      \<in>positive_meaning judgment_retention_system"
proof -
  have readable: "judgment_source_readable (E,((pu,pr),(au,ar)))"
    using source by (simp add: judgment_source_presents_def)
  have expected: "environment_value_presents (native_judgment_environment E pu pr au ar) f"
    using report by (simp only: judgment_retention_report_output[OF source] fst_conv snd_conv)
  have retained: "judgment_source_readable (native_judgment_environment E pu pr au ar,((pu,pr),(au,ar)))"
    and fixed: "native_judgment_environment (native_judgment_environment E pu pr au ar) pu pr au ar=
      native_judgment_environment E pu pr au ar"
    using judgment_retained_context(1,2)[OF readable] by simp_all
  have present: "judgment_source_presents (native_judgment_environment E pu pr au ar,((pu,pr),(au,ar)))
      (judgment_context_term f (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar))"
    using retained expected by (simp only: judgment_source_presentation_fields fst_conv snd_conv) blast
  show closed: "judgment_closed_source_presents (native_judgment_environment E pu pr au ar,((pu,pr),(au,ar)))
      (judgment_context_term f (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar))"
    using present fixed by (simp add: judgment_closed_source_presents_def)
  show "(183,judgment_context_term f (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar))
      \<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_closed_source_exact) (use closed in blast)
qed

section \<open>Every readable source has closed material and complete quotations\<close>

theorem judgment_retention_native_total:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "\<exists>F p q f. F=native_judgment_environment E pu pr au ar \<and>
    judgment_source_presents (E,((pu,pr),(au,ar))) p \<and>
    judgment_source_presents (F,((pu,pr),(au,ar))) q \<and> environment_value_presents F f \<and>
    (178,p)\<in>positive_meaning judgment_retention_system \<and> (183,q)\<in>positive_meaning judgment_retention_system \<and>
    (184,Pair_Term p f)\<in>positive_meaning judgment_retention_system \<and>
    (184,Pair_Term q f)\<in>positive_meaning judgment_retention_system \<and>
    complete_data_quoted_at (term_syntax q) [] q \<and>
    complete_data_quoted_at (term_syntax (Pair_Term q f)) [] (Pair_Term q f)"
proof -
  let ?z="(E,((pu,pr),(au,ar)))"
  let ?F="native_judgment_environment E pu pr au ar"
  have readable: "judgment_source_readable ?z"
    by (rule exI[of _ P], rule exI[of _ d], rule exI[of _ t], rule exI[of _ I], rule exI[of _ K])
      (use package app in simp)
  have retained: "judgment_source_readable (?F,((pu,pr),(au,ar)))"
    and fixed: "native_judgment_environment ?F pu pr au ar=?F"
    using judgment_retained_context(1,2)[OF readable] by simp_all
  obtain p where source: "judgment_source_presents ?z p" using judgment_sources.total[OF readable] by blast
  obtain q where target: "judgment_source_presents (?F,((pu,pr),(au,ar))) q" using judgment_sources.total[OF retained] by blast
  have formed: "environment_formed ?F" by (rule native_judgment_environment_recovers(3)[OF package app])
  obtain f where expected: "environment_value_presents ?F f" using environment_value_presents_total[OF formed] by blast
  have admission: "(178,p)\<in>positive_meaning judgment_retention_system" by (simp only: judgment_source_exact) (use source in blast)
  have closed: "(183,q)\<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_closed_source_at_presentation[OF target] fst_conv snd_conv; rule fixed)
  have report: "(184,Pair_Term p f)\<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_retention_report_output[OF source] fst_conv snd_conv; rule expected)
  have copied: "(184,Pair_Term q f)\<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_retention_report_output[OF target] fst_conv snd_conv fixed; rule expected)
  have data: "term_formed q" "self_contained_term q" "term_formed f" "self_contained_term f"
    using judgment_source_presents_formed[OF target] environment_value_presents_formed[OF expected] by blast+
  have quote: "complete_data_quoted_at (term_syntax q) [] q"
    by (rule complete_data_quotation_total[OF data(1,2)])
  have full: "complete_data_quoted_at (term_syntax (Pair_Term q f)) [] (Pair_Term q f)"
    by (rule complete_data_quotation_total) (use data in simp_all)
  show ?thesis using source target expected admission closed report copied quote full by blast
qed

theorem judgment_native_retention_does_not_establish_truth:
  "\<exists>E pu pr au ar p f. judgment_source_presents (E,((pu,pr),(au,ar))) p \<and> environment_value_presents E f \<and>
    (183,p)\<in>positive_meaning judgment_retention_system \<and>
    (184,Pair_Term p f)\<in>positive_meaning judgment_retention_system \<and>
    native_application_formed E pu pr au ar \<and> \<not>native_positive_holds E pu pr au ar \<and>
    (115,p)\<notin>positive_meaning native_positive_admission_system"
proof -
  let ?E="equality_query_environment (Payload_Term [])"
  have operand: "term_formed (Payload_Term [])" by (simp add: octets_formed_def)
  have call: "native_application_formed ?E None [0] (Some []) []"
    by (rule native_equality_future_application_formed[OF operand])
  have false: "\<not>native_positive_holds ?E None [0] (Some []) []"
    by (simp only: native_equality_future_truth[OF operand]) simp
  obtain P d t I K where reads: "native_package_at ?E None [0] P" "native_application_at ?E (Some []) [] d t I K"
    using call by (auto simp: native_application_formed_def)
  obtain F p q f where source: "judgment_source_presents (?E,((None,[0]),(Some [],[]))) p"
    and retained: "judgment_source_presents (F,((None,[0]),(Some [],[]))) q"
    and expected: "environment_value_presents F f"
    and closed: "(183,q)\<in>positive_meaning judgment_retention_system"
    and report: "(184,Pair_Term p f)\<in>positive_meaning judgment_retention_system"
    and copied: "(184,Pair_Term q f)\<in>positive_meaning judgment_retention_system"
    using judgment_retention_native_total[OF reads] by blast
  have formed: "native_application_formed F None [0] (Some []) []"
    using judgment_native_retention_material(8)[OF source expected report] call by blast
  have untrue: "\<not>native_positive_holds F None [0] (Some []) []"
    using judgment_native_retention_material(9)[OF source expected report] false by blast
  have coordinates: "judgment_value_presents F None [0] (Some []) [] q"
    using retained by (simp add: judgment_source_presents_def)
  have rejected: "(115,q)\<notin>positive_meaning native_positive_admission_system"
    by (simp only: native_positive_admission_on_values[OF coordinates]; rule untrue)
  show ?thesis using retained expected closed copied formed untrue rejected by blast
qed

section \<open>One fixed native program supplies all seven operations\<close>

abbreviation judgment_retention_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "judgment_retention_operation_result d t \<equiv>
    if d=178 then (\<exists>z. judgment_source_presents z t)
    else if d=179 then judgment_demanded_slot_result t
    else if d=180 then judgment_required_use_result t
    else if d=181 then judgment_use_list_result t
    else if d=182 then judgment_slot_list_result t
    else if d=183 then (\<exists>z. judgment_closed_source_presents z t)
    else (\<exists>z. judgment_retention_report_presents z t)"

theorem judgment_retention_operations_exact:
  assumes "d\<in>{178,179,180,181,182,183,184}"
  shows "(d,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> judgment_retention_operation_result d t"
  using assms by (auto simp: judgment_source_exact judgment_demanded_slot_exact judgment_required_use_exact
    judgment_coverage_lists_exact judgment_closed_source_exact judgment_retention_report_exact; blast)

theorem native_judgment_retention_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {178::nat,179,180,181,182,183,184} \<and>
    (\<forall>d\<in>{178,179,180,181,182,183,184}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> judgment_retention_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{178,179,180,181,182,183,184}\<subseteq>system_definitions judgment_retention_system" by auto
  have calls: "schema_call_formed judgment_retention_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{178,179,180,181,182,183,184}" for d t
    using judgment_retention_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF judgment_retention_system_formed selected calls
    judgment_retention_operations_exact])
qed

text \<open>
  Source admission, dependency queries, closed admission, and the retention
  report have complete local contracts. The report returns every presentation
  of the exact least environment. Wrong material, wrong use or slot domains,
  and nonminimal supplied scopes are rejected.

  The retained material preserves every artifact value and binding target
  at its actual use, both full readings and their metadata, call formation,
  truth, and the independently determined program scope. Reports are
  idempotent. Closed-source admission can become true after restriction.
  Every readable source has closed material and complete quotations, and
  an actual formed false call also has accepted retention.

  One fixed native compilation supplies all seven entries before future
  operands while preserving its original scope, artifacts, and bindings.
  Recorded cause validation consumes this boundary separately. Mathematical
  presentation contracts and their native proof presentations remain open.
\<close>

end
