theory Factor_Generation_Retention_Contracts
  imports Factor_Generation_Dependency_Contracts Factor_Generation_Scope_Contracts
begin

section \<open>The generation notion owns closed admission and its retention function\<close>

theorem generation_closed_source_native_class:
  "presentation_class generation_closed_source_presents
    (\<lambda>z. generation_at_context (fst z) (snd z) \<and>
      generation_environment_closed (fst (fst z)) {snd (fst z)})
    (\<lambda>t. (176,t)\<in>positive_meaning generation_retention_system)"
  using generation_closed_source_presentation_class by (simp only: generation_closed_source_exact)

theorem generation_retention_report_native_class:
  "presentation_class generation_retention_report_presents
    (\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and>
      snd z=generation_required_environment (fst z))
    (\<lambda>t. (177,t)\<in>positive_meaning generation_retention_system)"
  using generation_retention_report_presentation_class by (simp only: generation_retention_report_exact)

interpretation generation_retention_function: presented_function_contract
  generation_source_presents "\<lambda>z. generation_at_context (fst z) (snd z)"
    "\<lambda>t. (152,t)\<in>positive_meaning generation_source_system"
  environment_value_presents environment_formed "\<lambda>t. (26,t)\<in>positive_meaning environment_admission_system"
  generation_required_environment "\<lambda>p q. (177,Pair_Term p q)\<in>positive_meaning generation_retention_system"
  using generation_source_native_presentation_class environment_presentations.presentation_class_axioms
    generation_required_environment_formed
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def
    generation_retention_report_exact generation_retention_report_relation; blast)

corollary generation_retention_report_output:
  assumes "generation_source_presents ((E,(u,r)),G) p"
  shows "(177,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    environment_value_presents (generation_source_environment E u r) q"
  using generation_retention_function.output[OF assms, of q] by simp

corollary generation_retention_report_invariance:
  assumes "generation_source_presents z p" "environment_value_presents F q"
    "generation_source_presents z p'" "environment_value_presents F q'"
  shows "(177,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (177,Pair_Term p' q')\<in>positive_meaning generation_retention_system"
  by (rule generation_retention_function.invariance[OF assms])

corollary generation_retention_wrong_environment_rejected:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and claim: "environment_value_presents F f" and wrong: "F\<noteq>generation_source_environment E u r"
  shows "(177,Pair_Term p f)\<notin>positive_meaning generation_retention_system"
  using generation_retention_function.at[OF source claim] wrong by simp

corollary generation_retention_wrong_use_domain_rejected:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and claim: "environment_value_presents F f"
    and wrong: "environment_uses F\<noteq>requested_uses E (generation_requests E {(u,r)})"
  shows "(177,Pair_Term p f)\<notin>positive_meaning generation_retention_system"
proof -
  have native: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have different: "F\<noteq>generation_source_environment E u r"
    using wrong generation_source_environment_domains(1)[OF native] by blast
  show ?thesis by (rule generation_retention_wrong_environment_rejected[OF source claim different])
qed

corollary generation_retention_wrong_slot_domain_rejected:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and claim: "environment_value_presents F f"
    and wrong: "rel_dom (environment_bindings F)\<noteq>requested_slots E (generation_requests E {(u,r)})"
  shows "(177,Pair_Term p f)\<notin>positive_meaning generation_retention_system"
proof -
  have native: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have different: "F\<noteq>generation_source_environment E u r"
    using wrong generation_source_environment_domains(2)[OF native] by blast
  show ?thesis by (rule generation_retention_wrong_environment_rejected[OF source claim different])
qed

corollary generation_nonminimal_source_rejected:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and larger: "generation_source_environment E u r\<noteq>E"
  shows "(176,p)\<notin>positive_meaning generation_retention_system"
proof -
  have native: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  obtain e where encoded: "environment_value_presents E e" and shape: "p=generation_source_term e (use_data_term u) (Payload_Term r)"
    using source by (auto simp: generation_source_presentation_fields)
  show ?thesis using larger
    by (simp only: shape generation_closed_source_at_source[OF encoded] generation_source_closed_iff_fixed[OF native]; simp)
qed

section \<open>The accepted claim retains every actual item and recursive reading\<close>

theorem generation_native_retention_material:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and report: "(177,Pair_Term p f)\<in>positive_meaning generation_retention_system"
  shows "environment_value_presents (generation_source_environment E u r) f"
    and "generation_at (generation_source_environment E u r) u r G"
    and "generation_environment_closed (generation_source_environment E u r) {(u,r)}"
    and "\<forall>v A. artifact_at (generation_source_environment E u r) v A \<longleftrightarrow>
      v\<in>requested_uses E (generation_requests E {(u,r)}) \<and> artifact_at E v A"
    and "\<forall>v k w. binds_slot (generation_source_environment E u r) v k w \<longleftrightarrow>
      (v,k)\<in>requested_slots E (generation_requests E {(u,r)}) \<and> binds_slot E v k w"
    and "\<forall>v a. (v,a)\<in>generation_read_sites E {(u,r)} \<longrightarrow>
      generation_predecessor_rows (generation_source_environment E u r) v a=generation_predecessor_rows E v a"
proof -
  have presented: "generation_retention_presents (((E,(u,r)),G),generation_source_environment E u r) p"
    using source by (simp add: generation_retention_presents_def)
  have native: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  show "environment_value_presents (generation_source_environment E u r) f"
    using report by (simp only: generation_retention_report_output[OF source])
  show "generation_at (generation_source_environment E u r) u r G"
    and "generation_environment_closed (generation_source_environment E u r) {(u,r)}"
    and "\<forall>v A. artifact_at (generation_source_environment E u r) v A \<longleftrightarrow>
      v\<in>requested_uses E (generation_requests E {(u,r)}) \<and> artifact_at E v A"
    and "\<forall>v k w. binds_slot (generation_source_environment E u r) v k w \<longleftrightarrow>
      (v,k)\<in>requested_slots E (generation_requests E {(u,r)}) \<and> binds_slot E v k w"
    using generation_presented_retention(1,2,4,5)[OF presented] by blast+
  show "\<forall>v a. (v,a)\<in>generation_read_sites E {(u,r)} \<longrightarrow>
      generation_predecessor_rows (generation_source_environment E u r) v a=generation_predecessor_rows E v a"
    by (rule generation_source_environment_properties(7)[OF native])
qed

theorem generation_retention_preserves_reports:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and retained: "generation_source_presents ((generation_source_environment E u r,(u,r)),G) p'"
  shows "\<forall>q.
    ((151,Pair_Term p q)\<in>positive_meaning generation_source_system \<longleftrightarrow>
      (151,Pair_Term p' q)\<in>positive_meaning generation_source_system) \<and>
    ((155,Pair_Term p q)\<in>positive_meaning generation_source_system \<longleftrightarrow>
      (155,Pair_Term p' q)\<in>positive_meaning generation_source_system) \<and>
    ((162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
      (162,Pair_Term p' q)\<in>positive_meaning generation_scope_system) \<and>
    ((167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
      (167,Pair_Term p' q)\<in>positive_meaning generation_scope_system) \<and>
    ((177,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
      (177,Pair_Term p' q)\<in>positive_meaning generation_retention_system)"
proof -
  let ?F="generation_source_environment E u r"
  have native: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have site: "(u,r)\<in>generation_read_sites E {(u,r)}" using generation_read_sites_roots[of "{(u,r)}" E] by blast
  have rows: "generation_predecessor_rows ?F u r=generation_predecessor_rows E u r"
    using generation_source_environment_properties(7)[OF native] site by blast
  have fixed: "generation_source_environment ?F u r=?F" by (rule generation_source_environment_properties(6)[OF native])
  have original_core: "generation_core_source_presents G p" and retained_core: "generation_core_source_presents G p'"
    using source retained by (auto simp: generation_core_source_presents_def)
  have cores: "(151,Pair_Term p q)\<in>positive_meaning generation_source_system \<longleftrightarrow>
      (151,Pair_Term p' q)\<in>positive_meaning generation_source_system" for q
    by (simp only: generation_source_conversion.output[OF original_core] generation_source_conversion.output[OF retained_core])
  have predecessors: "(155,Pair_Term p q)\<in>positive_meaning generation_source_system \<longleftrightarrow>
      (155,Pair_Term p' q)\<in>positive_meaning generation_source_system" for q
    by (simp only: generation_predecessor_function.output[OF source] generation_predecessor_function.output[OF retained]
      fst_conv snd_conv rows)
  obtain p0 where middle: "generation_source_presents ((?F,(u,r)),G) p0"
    and scopes: "\<forall>q.
      ((162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
        (162,Pair_Term p0 q)\<in>positive_meaning generation_scope_system) \<and>
      ((167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
        (167,Pair_Term p0 q)\<in>positive_meaning generation_scope_system)"
    using generation_scope_native_retention[OF source] by blast
  have scope_values: "((162,Pair_Term p0 q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
       (162,Pair_Term p' q)\<in>positive_meaning generation_scope_system) \<and>
      ((167,Pair_Term p0 q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
       (167,Pair_Term p' q)\<in>positive_meaning generation_scope_system)" for q
    by (simp only: generation_recorded_scope_relation.at_source[OF middle]
      generation_recorded_scope_relation.at_source[OF retained]
      generation_payload_scope_relation.at_source[OF middle] generation_payload_scope_relation.at_source[OF retained]; simp)
  have reports: "(177,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
      (177,Pair_Term p' q)\<in>positive_meaning generation_retention_system" for q
    by (simp only: generation_retention_report_output[OF source] generation_retention_report_output[OF retained] fixed)
  show ?thesis using cores predecessors scopes scope_values reports by blast
qed

corollary generation_retention_preserves_source_admissions:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and retained: "generation_source_presents ((generation_source_environment E u r,(u,r)),G) p'"
  shows "((152,p)\<in>positive_meaning generation_source_system \<longleftrightarrow>
      (152,p')\<in>positive_meaning generation_source_system) \<and>
    ((163,p)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
      (163,p')\<in>positive_meaning generation_scope_system) \<and>
    ((168,p)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
      (168,p')\<in>positive_meaning generation_scope_system)"
  using source retained generation_retention_preserves_reports[OF source retained]
  by (simp only: generation_source_exact generation_recorded_projection.exact generation_payload_projection.exact; blast)

corollary generation_retention_claim_supplies_closed_source:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and report: "(177,Pair_Term p f)\<in>positive_meaning generation_retention_system"
  shows "generation_source_presents ((generation_source_environment E u r,(u,r)),G)
      (generation_source_term f (use_data_term u) (Payload_Term r)) \<and>
    (176,generation_source_term f (use_data_term u) (Payload_Term r))\<in>positive_meaning generation_retention_system"
proof -
  have encoded: "environment_value_presents (generation_source_environment E u r) f"
    and native: "generation_at (generation_source_environment E u r) u r G"
    and closed: "generation_environment_closed (generation_source_environment E u r) {(u,r)}"
    using generation_native_retention_material(1-3)[OF source report] by blast+
  have presented: "generation_source_presents ((generation_source_environment E u r,(u,r)),G)
      (generation_source_term f (use_data_term u) (Payload_Term r))"
    using encoded native by (auto simp: generation_source_presentation_fields)
  show ?thesis using presented closed by (simp only: generation_closed_source_at_source[OF encoded]; blast)
qed

section \<open>Every formed core has native retained material, independently of cause validity\<close>

theorem generation_retention_native_total:
  assumes formed: "generation_formed G"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>u p f.
    generation_at E u [] G \<and> generation_source_environment E u []=E \<and>
    generation_source_presents ((E,(u,[])),G) p \<and> environment_value_presents E f \<and>
    (176,p)\<in>positive_meaning generation_retention_system \<and>
    (177,Pair_Term p f)\<in>positive_meaning generation_retention_system \<and>
    complete_data_quoted_at (term_syntax (Pair_Term p f)) [] (Pair_Term p f)"
proof -
  obtain A :: "local_address option artifact_environment" and u where native: "generation_at A u [] G"
    using generation_presentation_total[OF formed] by blast
  let ?E="generation_source_environment A u []"
  have ef: "environment_formed ?E" and read: "generation_at ?E u [] G"
    and closed: "generation_environment_closed ?E {(u,[])}" and fixed: "generation_source_environment ?E u []=?E"
    using generation_source_environment_properties(1-3,6)[OF native] by blast+
  obtain p where source: "generation_source_presents ((?E,(u,[])),G) p"
    using generation_source_presentation_total[OF read] by blast
  obtain f where encoded: "environment_value_presents ?E f" using environment_value_presents_total[OF ef] by blast
  have report: "(177,Pair_Term p f)\<in>positive_meaning generation_retention_system"
    by (simp only: generation_retention_report_output[OF source] fixed; rule encoded)
  have admission: "(176,p)\<in>positive_meaning generation_retention_system"
    using source closed by (auto simp: generation_closed_source_exact generation_closed_source_presents_def)
  have presentation: "generation_retention_report_presents (((?E,(u,[])),G),?E) (Pair_Term p f)"
    using source encoded fixed by (simp add: generation_retention_report_presents_def)
  have data: "term_formed (Pair_Term p f) \<and> self_contained_term (Pair_Term p f)"
    by (rule generation_retention_report_formed[OF presentation])
  have quote: "complete_data_quoted_at (term_syntax (Pair_Term p f)) [] (Pair_Term p f)"
    by (rule complete_data_quotation_total) (use data in blast)+
  show ?thesis using read fixed source encoded admission report quote by blast
qed

theorem generation_native_retention_does_not_validate_cause:
  "\<exists>E u G p f. generation_source_presents ((E,(u,[])),G) p \<and> environment_value_presents E f \<and>
    (176,p)\<in>positive_meaning generation_retention_system \<and>
    (177,Pair_Term p f)\<in>positive_meaning generation_retention_system \<and> \<not>generation_cause_valid_at E u [] G"
proof -
  obtain E u G p where source: "generation_source_presents ((E,(u,[])),G) p"
    and fixed: "generation_source_environment E u []=E" and invalid: "\<not>generation_cause_valid_at E u [] G"
    using generation_recorded_native_scope_does_not_validate_cause by blast
  have native: "generation_at E u [] G" using source by (simp add: generation_source_presents_def)
  have formed: "environment_formed E" by (rule generation_at_environment_formed[OF native])
  obtain f where encoded: "environment_value_presents E f" using environment_value_presents_total[OF formed] by blast
  have closed: "generation_environment_closed E {(u,[])}"
    using fixed by (simp only: generation_source_closed_iff_fixed[OF native])
  have admission: "(176,p)\<in>positive_meaning generation_retention_system"
    using source closed by (auto simp: generation_closed_source_exact generation_closed_source_presents_def)
  have report: "(177,Pair_Term p f)\<in>positive_meaning generation_retention_system"
    by (simp only: generation_retention_report_output[OF source] fixed; rule encoded)
  show ?thesis using source encoded admission report invalid by blast
qed

section \<open>One fixed native program supplies all nine entries\<close>

abbreviation generation_retention_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_retention_operation_result d t \<equiv>
    if d=169 then generation_read_site_result t
    else if d=170 then generation_citation_root_result t
    else if d=171 then generation_request_result t
    else if d=172 then generation_demanded_slot_result t
    else if d=173 then generation_required_use_result t
    else if d=174 then generation_use_list_result t
    else if d=175 then generation_slot_list_result t
    else if d=176 then (\<exists>z. generation_closed_source_presents z t)
    else (\<exists>z. generation_retention_report_presents z t)"

theorem generation_retention_operations_exact:
  assumes "d\<in>{169,170,171,172,173,174,175,176,177}"
  shows "(d,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> generation_retention_operation_result d t"
  using assms by (auto simp: generation_read_site_exact generation_citation_root_exact generation_request_exact
    generation_demanded_slot_exact generation_required_use_exact generation_coverage_lists_exact
    generation_closed_source_exact generation_retention_report_exact; blast)

theorem native_generation_retention_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {169::nat,170,171,172,173,174,175,176,177} \<and>
    (\<forall>d\<in>{169,170,171,172,173,174,175,176,177}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> generation_retention_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{169,170,171,172,173,174,175,176,177}\<subseteq>system_definitions generation_retention_system" by auto
  have calls: "schema_call_formed generation_retention_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{169,170,171,172,173,174,175,176,177}" for d t
    using generation_retention_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF generation_retention_system_formed selected calls
    generation_retention_operations_exact])
qed

text \<open>
  The total function returns precisely every presentation of the required
  environment. Incorrect uses, omitted or extra binding slots, and every
  other different environment are rejected. All table values and aliases
  remain part of exact environment identity.

  Accepted claims recover the complete retained material and a closed source
  using the submitted environment presentation. Every core, predecessor,
  recorded-scope, payload-scope, and retention report survives restriction.
  Every formed core has admitted closed material and a complete report
  quotation. Actual invalid causes also have accepted retention reports.

  The fixed native program precedes all future operands and preserves its
  original scope, artifacts, and bindings. Its mathematical exactness and
  presentation proofs retain their separate native proof-presentation
  obligation. Cause validity, authority, and higher protocol readers remain
  independent implementation work.
\<close>

end
