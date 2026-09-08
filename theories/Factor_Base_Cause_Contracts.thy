theory Factor_Base_Cause_Contracts
  imports Factor_Recorded_Base_Admission
begin

section \<open>Recorded causes own exact relation and determined-output contracts\<close>

theorem recorded_base_source_native_class:
  "presentation_class recorded_base_source_presents (\<lambda>z. recorded_base_context (fst z) (snd z))
    (\<lambda>p. (188,p)\<in>positive_meaning base_cause_system)"
  using recorded_base_source_presentation_class by (simp only: recorded_base_source_exact)

theorem recorded_base_report_native_class:
  "presentation_class recorded_base_report_presents (\<lambda>z. recorded_base_context (fst z) (snd z))
    (\<lambda>p. (187,p)\<in>positive_meaning base_cause_system)"
  using recorded_base_report_presentation_class by (simp only: recorded_base_report_exact)

interpretation recorded_base_relation: presented_relation_contract
  generation_source_presents "\<lambda>z. generation_at_context (fst z) (snd z)"
    "\<lambda>p. (152,p)\<in>positive_meaning generation_source_system"
  artifact_value_presents exact_formed "\<lambda>q. (11,q)\<in>positive_meaning artifact_admission_system"
  recorded_base_context "\<lambda>p q. (187,Pair_Term p q)\<in>positive_meaning base_cause_system"
  using generation_source_native_presentation_class artifact_presentations.presentation_class_axioms
  by (simp only: presented_relation_contract_def presented_relation_contract_axioms_def
    recorded_base_report_exact recorded_base_report_relation; blast)

lemma recorded_base_function_exact:
  "(187,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
    presented_relation recorded_base_source_presents artifact_value_presents (\<lambda>z R. R=snd z) p q"
  by (auto simp: recorded_base_report_exact recorded_base_report_presents_def recorded_base_source_presents_def
    factor_pair_presents_def presented_relation_def; metis fst_conv snd_conv)

interpretation recorded_base_reading: presented_function_contract
  recorded_base_source_presents "\<lambda>z. recorded_base_context (fst z) (snd z)"
    "\<lambda>p. (188,p)\<in>positive_meaning base_cause_system"
  artifact_value_presents exact_formed "\<lambda>q. (11,q)\<in>positive_meaning artifact_admission_system"
  snd "\<lambda>p q. (187,Pair_Term p q)\<in>positive_meaning base_cause_system"
  using recorded_base_source_native_class artifact_presentations.presentation_class_axioms recorded_base_context_formed
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def recorded_base_function_exact; blast)

corollary recorded_base_native_invariance:
  assumes "generation_source_presents z p" "artifact_value_presents R q"
    "generation_source_presents z p'" "artifact_value_presents R q'"
  shows "(187,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
    (187,Pair_Term p' q')\<in>positive_meaning base_cause_system"
  by (rule recorded_base_relation.invariance[OF assms])

corollary recorded_base_wrong_payload_rejected:
  assumes source: "generation_source_presents z p" and expected: "artifact_value_presents R q"
    and different: "generation_payload (snd z)\<noteq>Whole_Artifact R"
  shows "(187,Pair_Term p q)\<notin>positive_meaning base_cause_system"
  using different by (simp only: recorded_base_relation.at[OF source expected] recorded_base_context_join; blast)

corollary recorded_base_nonminimal_rejected:
  assumes source: "generation_source_presents z p" and scope: "generation_recorded_scope z j"
    and nonminimal: "judgment_required_environment j\<noteq>fst j"
  shows "(187,Pair_Term p q)\<notin>positive_meaning base_cause_system"
    and "(188,p)\<notin>positive_meaning base_cause_system"
proof -
  have reports: "(187,Pair_Term p v)\<notin>positive_meaning base_cause_system" for v
    by (simp only: recorded_base_relation.at_source[OF source] recorded_base_context_at_scope[OF scope])
      (use nonminimal in blast)
  show "(187,Pair_Term p q)\<notin>positive_meaning base_cause_system" by (rule reports)
  show "(188,p)\<notin>positive_meaning base_cause_system"
    by (simp only: recorded_base_projection.exact) (use reports in blast)
qed

corollary recorded_base_false_declaration_rejected:
  assumes source: "generation_source_presents z p"
    and scope: "generation_recorded_scope z (F,((pu,pr),(au,ar)))"
    and false: "\<not>native_positive_holds F pu pr au ar"
  shows "(187,Pair_Term p q)\<notin>positive_meaning base_cause_system"
    and "(188,p)\<notin>positive_meaning base_cause_system"
proof -
  have absent: "\<not>base_admission_judgment_at F pu pr au ar R" for R
  proof
    assume admitted: "base_admission_judgment_at F pu pr au ar R"
    have truth: "native_positive_holds F pu pr au ar" by (rule base_admission_truth[OF admitted])
    show False using false truth by blast
  qed
  have reports: "(187,Pair_Term p v)\<notin>positive_meaning base_cause_system" for v
    by (simp only: recorded_base_relation.at_source[OF source] recorded_base_context_at_scope[OF scope]
      fst_conv snd_conv; use absent in blast)
  show "(187,Pair_Term p q)\<notin>positive_meaning base_cause_system" by (rule reports)
  show "(188,p)\<notin>positive_meaning base_cause_system"
    by (simp only: recorded_base_projection.exact) (use reports in blast)
qed

section \<open>Exact cause and payload fields preserve every report\<close>

theorem recorded_base_native_outer_invariance:
  assumes first: "generation_source_presents z p" and second: "generation_source_presents w p'"
    and cause: "generation_cause (snd z)=generation_cause (snd w)"
    and payload: "generation_payload (snd z)=generation_payload (snd w)"
  shows "(187,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
      (187,Pair_Term p' q)\<in>positive_meaning base_cause_system"
    and "(188,p)\<in>positive_meaning base_cause_system \<longleftrightarrow> (188,p')\<in>positive_meaning base_cause_system"
proof -
  have actual: "generation_at_context (fst z) (snd z)" "generation_at_context (fst w) (snd w)"
    by (rule generation_sources.subject_boundary[OF first], rule generation_sources.subject_boundary[OF second])
  have reports: "(187,Pair_Term p v)\<in>positive_meaning base_cause_system \<longleftrightarrow>
      (187,Pair_Term p' v)\<in>positive_meaning base_cause_system" for v
    by (simp only: recorded_base_relation.at_source[OF first] recorded_base_relation.at_source[OF second]
      recorded_base_context_outer_invariance[OF actual cause payload])
  show "(187,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
      (187,Pair_Term p' q)\<in>positive_meaning base_cause_system" by (rule reports)
  show "(188,p)\<in>positive_meaning base_cause_system \<longleftrightarrow> (188,p')\<in>positive_meaning base_cause_system"
    by (simp only: recorded_base_projection.exact reports)
qed

theorem recorded_base_native_retention:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
  shows "\<exists>p'. generation_source_presents ((generation_source_environment E u r,(u,r)),G) p' \<and>
    generation_source_environment (generation_source_environment E u r) u r=generation_source_environment E u r \<and>
    (\<forall>q. (187,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
      (187,Pair_Term p' q)\<in>positive_meaning base_cause_system) \<and>
    ((188,p)\<in>positive_meaning base_cause_system \<longleftrightarrow> (188,p')\<in>positive_meaning base_cause_system)"
proof -
  have actual: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have retained: "generation_at (generation_source_environment E u r) u r G"
    by (rule generation_source_environment_properties(2)[OF actual])
  obtain p' where second: "generation_source_presents ((generation_source_environment E u r,(u,r)),G) p'"
    using generation_source_presentation_total[OF retained] by blast
  have reports: "(187,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
      (187,Pair_Term p' q)\<in>positive_meaning base_cause_system" for q
    by (rule recorded_base_native_outer_invariance(1)[OF source second]) simp_all
  have admission: "(188,p)\<in>positive_meaning base_cause_system \<longleftrightarrow> (188,p')\<in>positive_meaning base_cause_system"
    by (rule recorded_base_native_outer_invariance(2)[OF source second]) simp_all
  show ?thesis using second generation_source_environment_properties(6)[OF actual] reports admission by blast
qed

theorem recorded_base_native_material:
  assumes source: "generation_source_presents ((E,(u,r)),G) p" and expected: "artifact_value_presents R q"
    and accepted: "(187,Pair_Term p q)\<in>positive_meaning base_cause_system"
  shows "\<exists>F pu pr au ar P d I K C cr v cu.
    generation_payload G=Whole_Artifact R \<and> generation_cause G=Whole_Artifact C \<and>
    artifact_at E cu C \<and> complete_data_quoted_at C cr v \<and> judgment_value_presents F pu pr au ar v \<and>
    generation_judgment_scope_at E u r G F pu pr au ar \<and>
    F=native_judgment_environment F pu pr au ar \<and>
    environment_closed F {pu,au} (native_judgment_demands F pu pr au ar) \<and>
    native_package_at F pu pr P \<and> native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K \<and>
    (d,Target_Term (Whole_Artifact R))\<in>positive_meaning P \<and> native_application_formed F pu pr au ar"
proof -
  have valid: "recorded_base_cause_at E u r G R"
    using accepted by (simp only: recorded_base_relation.at[OF source expected] fst_conv snd_conv)
  obtain F pu pr au ar where scope: "generation_judgment_scope_at E u r G F pu pr au ar"
    and fixed: "F=native_judgment_environment F pu pr au ar" and payload: "generation_payload G=Whole_Artifact R"
    and base: "base_admission_judgment_at F pu pr au ar R"
    using valid unfolding recorded_base_cause_at_def by blast
  obtain P d I K where package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    and truth: "(d,Target_Term (Whole_Artifact R))\<in>positive_meaning P"
    using base unfolding base_admission_judgment_at_def by blast
  have formed: "native_application_formed F pu pr au ar"
    by (rule native_positive_holds_formed[OF base_admission_truth[OF base]])
  have closed: "environment_closed F {pu,au} (native_judgment_demands F pu pr au ar)"
    by (rule recorded_base_scope_closed[OF scope valid])
  have presented: "generation_recorded_scope_presents (((E,(u,r)),G),(F,((pu,pr),(au,ar)))) p"
    using source scope by (simp add: generation_recorded_scope_presents_def generation_recorded_scope_def)
  obtain C cr v cu where material: "generation_cause G=Whole_Artifact C" "artifact_at E cu C"
    "complete_data_quoted_at C cr v" "judgment_value_presents F pu pr au ar v"
    using generation_recorded_scope_material[OF presented] by blast
  show ?thesis using payload material scope fixed closed package app truth formed by blast
qed

section \<open>Every valid declaration has actual native source and report material\<close>

theorem recorded_base_native_total:
  assumes valid: "recorded_base_context z R"
  shows "\<exists>p. generation_source_presents z p \<and> recorded_base_source_presents (z,R) p \<and>
    (188,p)\<in>positive_meaning base_cause_system \<and>
    complete_data_quoted_at (term_syntax p) [] p \<and>
    (\<forall>q. artifact_value_presents R q \<longrightarrow>
      (187,Pair_Term p q)\<in>positive_meaning base_cause_system \<and>
      recorded_base_report_presents (z,R) (Pair_Term p q) \<and>
      complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q))"
proof -
  obtain p where source: "generation_source_presents z p"
    using generation_sources.total[OF recorded_base_context_source[OF valid]] by blast
  have presented: "recorded_base_source_presents (z,R) p"
    using source valid by (simp add: recorded_base_source_presents_def)
  have native: "(188,p)\<in>positive_meaning base_cause_system"
    by (simp only: recorded_base_source_exact) (use presented in blast)
  have formed: "term_formed p" "self_contained_term p" using generation_source_presents_formed[OF source] by blast+
  have quote: "complete_data_quoted_at (term_syntax p) [] p" by (rule complete_data_quotation_total[OF formed])
  have every: "(187,Pair_Term p q)\<in>positive_meaning base_cause_system \<and>
      recorded_base_report_presents (z,R) (Pair_Term p q) \<and>
      complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q)"
    if expected: "artifact_value_presents R q" for q
  proof -
    have read: "(187,Pair_Term p q)\<in>positive_meaning base_cause_system"
      by (simp only: recorded_base_relation.at[OF source expected]; rule valid)
    have report: "recorded_base_report_presents (z,R) (Pair_Term p q)"
      using source valid expected by (auto simp: recorded_base_report_presents_def factor_pair_presents_def)
    have shape: "term_formed (Pair_Term p q)" "self_contained_term (Pair_Term p q)"
      using recorded_base_report_formed[OF report] by blast+
    have quoted: "complete_data_quoted_at (term_syntax (Pair_Term p q)) [] (Pair_Term p q)"
      by (rule complete_data_quotation_total[OF shape])
    show ?thesis using read report quoted by blast
  qed
  show ?thesis using source presented native quote every by blast
qed

theorem base_cause_native_generation_total:
  fixes E :: "local_address option artifact_environment"
  assumes admitted: "base_admission_judgment_at E pu pr au ar R" and locus: "target_formed l"
    and predecessors: "\<forall>H\<in>fset P. generation_formed H"
  shows "\<exists>F C A u p.
    judgment_value_quoted_at C [] F pu pr au ar \<and> F=native_judgment_environment F pu pr au ar \<and>
    native_package_environment F pu pr=native_package_environment E pu pr \<and>
    generation_at A u [] (Generation l P (Whole_Artifact R) (Whole_Artifact C)) \<and>
    generation_environment_closed A {(u,[])} \<and>
    recorded_base_source_presents (((A,(u,[])),Generation l P (Whole_Artifact R) (Whole_Artifact C)),R) p \<and>
    (188,p)\<in>positive_meaning base_cause_system \<and>
    (\<forall>q. artifact_value_presents R q \<longrightarrow> (187,Pair_Term p q)\<in>positive_meaning base_cause_system)"
proof -
  obtain F C and A :: "local_address option artifact_environment" and u where
    quote: "judgment_value_quoted_at C [] F pu pr au ar"
    and fixed: "F=native_judgment_environment F pu pr au ar"
    and program: "native_package_environment F pu pr=native_package_environment E pu pr"
    and gen: "generation_at A u [] (Generation l P (Whole_Artifact R) (Whole_Artifact C))"
    and closed: "generation_environment_closed A {(u,[])}"
    and valid: "recorded_base_cause_at A u [] (Generation l P (Whole_Artifact R) (Whole_Artifact C)) R"
    using base_admission_generation_total[OF admitted locus predecessors] by blast
  let ?z="((A,(u,[])),Generation l P (Whole_Artifact R) (Whole_Artifact C))"
  have base: "recorded_base_context ?z R" using valid by simp
  obtain p where presented: "recorded_base_source_presents (?z,R) p"
    and native: "(188,p)\<in>positive_meaning base_cause_system"
    and reports: "\<forall>q. artifact_value_presents R q \<longrightarrow> (187,Pair_Term p q)\<in>positive_meaning base_cause_system"
    using recorded_base_native_total[OF base] by blast
  show ?thesis using quote fixed program gen closed presented native reports by blast
qed

theorem every_payload_has_native_base_material:
  assumes formed: "exact_formed R" and locus: "target_formed l"
  shows "\<exists>C E u p.
    generation_at E u [] (Generation l {||} (Whole_Artifact R) (Whole_Artifact C)) \<and>
    generation_environment_closed E {(u,[])} \<and>
    recorded_base_source_presents (((E,(u,[])),Generation l {||} (Whole_Artifact R) (Whole_Artifact C)),R) p \<and>
    (188,p)\<in>positive_meaning base_cause_system \<and>
    (\<forall>q. artifact_value_presents R q \<longrightarrow> (187,Pair_Term p q)\<in>positive_meaning base_cause_system)"
proof -
  obtain C and E :: "local_address option artifact_environment" and u where
    gen: "generation_at E u [] (Generation l {||} (Whole_Artifact R) (Whole_Artifact C))"
    and closed: "generation_environment_closed E {(u,[])}"
    and valid: "recorded_base_cause_at E u [] (Generation l {||} (Whole_Artifact R) (Whole_Artifact C)) R"
    using every_formed_payload_has_a_certified_base_generation[OF formed locus] by blast
  let ?z="((E,(u,[])),Generation l {||} (Whole_Artifact R) (Whole_Artifact C))"
  have base: "recorded_base_context ?z R" using valid by simp
  obtain p where presented: "recorded_base_source_presents (?z,R) p"
    and native: "(188,p)\<in>positive_meaning base_cause_system"
    and reports: "\<forall>q. artifact_value_presents R q \<longrightarrow> (187,Pair_Term p q)\<in>positive_meaning base_cause_system"
    using recorded_base_native_total[OF base] by blast
  show ?thesis using gen closed presented native reports by blast
qed

theorem native_recorded_base_rejects_a_formed_false_scope:
  "\<exists>F pu pr au ar E u G p q.
    native_application_formed F pu pr au ar \<and> \<not>native_positive_holds F pu pr au ar \<and>
    generation_source_environment E u []=E \<and> generation_source_presents ((E,(u,[])),G) p \<and>
    judgment_context_presents (F,((pu,pr),(au,ar))) q \<and>
    (162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<and>
    (163,p)\<in>positive_meaning generation_scope_system \<and>
    (188,p)\<notin>positive_meaning base_cause_system \<and>
    (\<forall>v. (185,Pair_Term q v)\<notin>positive_meaning base_cause_system \<and>
      (187,Pair_Term p v)\<notin>positive_meaning base_cause_system)"
proof -
  obtain F pu pr au ar E u G p q where formed: "native_application_formed F pu pr au ar"
    and false: "\<not>native_positive_holds F pu pr au ar" and retained: "generation_source_environment E u []=E"
    and source: "generation_source_presents ((E,(u,[])),G) p"
    and expected: "judgment_context_presents (F,((pu,pr),(au,ar))) q"
    and report: "(162,Pair_Term p q)\<in>positive_meaning generation_scope_system"
    and admitted: "(163,p)\<in>positive_meaning generation_scope_system"
    using generation_recorded_native_scope_does_not_validate_cause by blast
  have scope: "generation_recorded_scope ((E,(u,[])),G) (F,((pu,pr),(au,ar)))"
    using report by (simp only: generation_recorded_scope_relation.at[OF source expected])
  have rejected: "(188,p)\<notin>positive_meaning base_cause_system"
    by (rule recorded_base_false_declaration_rejected(2)[OF source scope false])
  have reports: "(185,Pair_Term q v)\<notin>positive_meaning base_cause_system \<and>
      (187,Pair_Term p v)\<notin>positive_meaning base_cause_system" for v
    using base_admission_false_declaration_rejected(1)[OF expected false]
      recorded_base_false_declaration_rejected(1)[OF source scope false] by blast
  show ?thesis using formed false retained source expected report admitted rejected reports by blast
qed

section \<open>One fixed native program precedes all future operands\<close>

abbreviation base_cause_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "base_cause_operation_result d t \<equiv>
    if d=185 then (\<exists>z. base_admission_report_presents z t)
    else if d=186 then (\<exists>z. base_admission_source_presents z t)
    else if d=187 then (\<exists>z. recorded_base_report_presents z t)
    else (\<exists>z. recorded_base_source_presents z t)"

theorem base_cause_operations_exact:
  assumes "d\<in>{185,186,187,188}"
  shows "(d,t)\<in>positive_meaning base_cause_system \<longleftrightarrow> base_cause_operation_result d t"
proof -
  consider (base_report) "d=185" | (base_source) "d=186" | (recorded_report) "d=187" | (recorded_source) "d=188"
    using assms by auto
  then show ?thesis
  proof cases
    case base_report
    show ?thesis by (simp add: base_report base_admission_report_exact)
  next
    case base_source
    show ?thesis by (simp add: base_source base_admission_source_exact)
  next
    case recorded_report
    show ?thesis by (simp add: recorded_report recorded_base_report_exact)
  next
    case recorded_source
    show ?thesis by (simp add: recorded_source recorded_base_source_exact)
  qed
qed

theorem native_base_cause_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {185::nat,186,187,188} \<and>
    (\<forall>d\<in>{185,186,187,188}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> base_cause_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{185,186,187,188}\<subseteq>system_definitions base_cause_system" by auto
  have calls: "schema_call_formed base_cause_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{185,186,187,188}" for d t using base_cause_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF base_cause_system_formed selected calls base_cause_operations_exact])
qed

text \<open>
  Every compatible report is interpreted by the same locally owned contracts.
  Exact payload identity, the whole actual cause, least judgment retention,
  application formation, and positive truth are preserved. False declarations,
  nonminimal recorded scopes, and mismatched payloads are rejected.

  Every admitted declaration and every formed predecessor family has an actual
  closed generation with native source and report material. An explicit finite
  base policy supplies inhabited examples for every formed payload and locus.
  A formed false declaration has readable scope material but fails validation.

  One fixed closed program precedes all future formed operands and preserves
  its original scope, artifacts, and bindings. Construction permission, adoption,
  certification, and the higher transition protocol retain their separate
  judgments; these four entries implement precisely base admission and recorded
  base cause.
\<close>

end
