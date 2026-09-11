theory Factor_Base_Admission_Contracts
  imports Factor_Base_Admission
begin

section \<open>The base declaration owns its relation and determined-output contracts\<close>

theorem base_admission_source_native_class:
  "presentation_class base_admission_source_presents (\<lambda>z. base_admission_context (fst z) (snd z))
    (\<lambda>p. (186,p)\<in>positive_meaning base_cause_system)"
  using base_admission_source_presentation_class by (simp only: base_admission_source_exact)

theorem base_admission_report_native_class:
  "presentation_class base_admission_report_presents (\<lambda>z. base_admission_context (fst z) (snd z))
    (\<lambda>p. (185,p)\<in>positive_meaning base_cause_system)"
  using base_admission_report_presentation_class by (simp only: base_admission_report_exact)

lemma base_admission_report_presented:
  "(185,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
    presented_relation judgment_context_presents artifact_value_presents base_admission_context p q"
proof -
  have linked: "presented_relation judgment_source_presents artifact_value_presents base_admission_context p q
      \<longleftrightarrow> presented_relation judgment_context_presents artifact_value_presents base_admission_context p q"
  proof
    assume "presented_relation judgment_source_presents artifact_value_presents base_admission_context p q"
    then obtain z R where source: "judgment_source_presents z p" and expected: "artifact_value_presents R q"
      and admitted: "base_admission_context z R" by (simp only: presented_relation_def; blast)
    have context_value: "judgment_context_presents z p"
      using source by (simp only: judgment_source_presents_def; blast)
    show "presented_relation judgment_context_presents artifact_value_presents base_admission_context p q"
      unfolding presented_relation_def by (rule exI[of _ z], rule exI[of _ R])
        (use context_value expected admitted in blast)
  next
    assume "presented_relation judgment_context_presents artifact_value_presents base_admission_context p q"
    then obtain z R where context_value: "judgment_context_presents z p" and expected: "artifact_value_presents R q"
      and admitted: "base_admission_context z R" by (simp only: presented_relation_def; blast)
    have source: "judgment_source_presents z p"
      using base_admission_context_source[OF admitted] context_value by (simp only: judgment_source_presents_def)
    show "presented_relation judgment_source_presents artifact_value_presents base_admission_context p q"
      unfolding presented_relation_def by (rule exI[of _ z], rule exI[of _ R])
        (use source expected admitted in blast)
  qed
  show ?thesis by (simp only: base_admission_report_exact base_admission_report_relation linked)
qed

interpretation base_admission_relation: presented_relation_contract
  judgment_context_presents judgment_context_formed "\<lambda>p. \<exists>z. judgment_context_presents z p"
  artifact_value_presents exact_formed "\<lambda>q. (11,q)\<in>positive_meaning artifact_admission_system"
  base_admission_context "\<lambda>p q. (185,Pair_Term p q)\<in>positive_meaning base_cause_system"
  using judgment_context_presentation_class artifact_presentations.presentation_class_axioms
  by (simp only: presented_relation_contract_def presented_relation_contract_axioms_def base_admission_report_presented; blast)

lemma base_admission_function_exact:
  "(185,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
    presented_relation base_admission_source_presents artifact_value_presents (\<lambda>z R. R=snd z) p q"
  by (auto simp: base_admission_report_exact base_admission_report_presents_def base_admission_source_presents_def
    factor_pair_presents_def presented_relation_def; metis fst_conv snd_conv)

interpretation base_admission_reading: presented_function_contract
  base_admission_source_presents "\<lambda>z. base_admission_context (fst z) (snd z)"
    "\<lambda>p. (186,p)\<in>positive_meaning base_cause_system"
  artifact_value_presents exact_formed "\<lambda>q. (11,q)\<in>positive_meaning artifact_admission_system"
  snd "\<lambda>p q. (185,Pair_Term p q)\<in>positive_meaning base_cause_system"
  using base_admission_source_native_class artifact_presentations.presentation_class_axioms base_admission_context_formed
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def base_admission_function_exact; blast)

corollary base_admission_native_invariance:
  assumes "judgment_context_presents z p" "artifact_value_presents R q"
    "judgment_context_presents z p'" "artifact_value_presents R q'"
  shows "(185,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
    (185,Pair_Term p' q')\<in>positive_meaning base_cause_system"
  by (rule base_admission_relation.invariance[OF assms])

corollary base_admission_wrong_payload_rejected:
  assumes source: "base_admission_source_presents (z,R) p" and expected: "artifact_value_presents S q"
    and different: "R\<noteq>S"
  shows "(185,Pair_Term p q)\<notin>positive_meaning base_cause_system"
  using artifact_value_presents_unique[OF _ expected] different
  by (simp only: base_admission_reading.output[OF source] snd_conv; blast)

corollary base_admission_false_declaration_rejected:
  assumes source: "judgment_context_presents (E,((pu,pr),(au,ar))) p"
    and false: "\<not>native_positive_holds E pu pr au ar"
  shows "(185,Pair_Term p q)\<notin>positive_meaning base_cause_system"
    and "(186,p)\<notin>positive_meaning base_cause_system"
proof -
  have absent: "\<not>base_admission_judgment_at E pu pr au ar R" for R
  proof
    assume admitted: "base_admission_judgment_at E pu pr au ar R"
    have truth: "native_positive_holds E pu pr au ar" by (rule base_admission_truth[OF admitted])
    show False using false truth by blast
  qed
  have reports: "(185,Pair_Term p v)\<notin>positive_meaning base_cause_system" for v
    by (simp only: base_admission_relation.at_source[OF source] fst_conv snd_conv)
      (use absent in blast)
  show "(185,Pair_Term p q)\<notin>positive_meaning base_cause_system" by (rule reports)
  show "(186,p)\<notin>positive_meaning base_cause_system"
    by (simp only: base_admission_projection.exact) (use reports in blast)
qed

theorem base_admission_native_retention:
  assumes source: "judgment_source_presents z p"
    and retained: "judgment_source_presents (judgment_required_environment z,snd z) p'"
  shows "(185,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
      (185,Pair_Term p' q)\<in>positive_meaning base_cause_system"
    and "(186,p)\<in>positive_meaning base_cause_system \<longleftrightarrow> (186,p')\<in>positive_meaning base_cause_system"
proof -
  have readable: "judgment_source_readable z" by (rule judgment_sources.subject_boundary[OF source])
  have reports: "(185,Pair_Term p v)\<in>positive_meaning base_cause_system \<longleftrightarrow>
      (185,Pair_Term p' v)\<in>positive_meaning base_cause_system" for v
    by (simp only: base_admission_report_at_source[OF source] base_admission_report_at_source[OF retained]
      base_admission_context_retained[OF readable])
  show "(185,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
      (185,Pair_Term p' q)\<in>positive_meaning base_cause_system" by (rule reports)
  show "(186,p)\<in>positive_meaning base_cause_system \<longleftrightarrow> (186,p')\<in>positive_meaning base_cause_system"
    by (simp only: base_admission_projection.exact reports)
qed

text \<open>
  The relation contract covers every complete judgment context, including
  unreadable or false contexts. A positive declaration supplies the narrower
  readable source domain. Its determined-output contract accepts exactly all
  complete presentations of the declared artifact. Generic adaptation and
  composition are inherited from these locally owned contracts.
\<close>

end
