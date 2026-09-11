theory Factor_Generation_Scope_Contracts
  imports Factor_Generation_Scope_Admission Factor_Program_Generation_Causes
begin

section \<open>The linked notions own their native presentation contracts\<close>

theorem generation_recorded_scope_native_class:
  "presentation_class generation_recorded_scope_presents
    (\<lambda>z. generation_recorded_scope (fst z) (snd z))
    (\<lambda>t. (163,t)\<in>positive_meaning generation_scope_system)"
  using generation_recorded_scope_presentation_class by (simp only: generation_recorded_source_exact)

theorem generation_recorded_report_native_class:
  "presentation_class generation_scope_report_presents
    (\<lambda>z. generation_recorded_scope (fst z) (snd z))
    (\<lambda>t. (162,t)\<in>positive_meaning generation_scope_system)"
  using generation_scope_report_presentation_class by (simp only: generation_recorded_report_exact)

theorem generation_payload_scope_native_class:
  "presentation_class generation_payload_scope_presents
    (\<lambda>z. generation_payload_scope (fst z) (snd z))
    (\<lambda>t. (168,t)\<in>positive_meaning generation_scope_system)"
  using generation_payload_scope_presentation_class by (simp only: generation_payload_source_exact)

theorem generation_payload_report_native_class:
  "presentation_class generation_payload_report_presents
    (\<lambda>z. generation_payload_scope (fst z) (snd z))
    (\<lambda>t. (167,t)\<in>positive_meaning generation_scope_system)"
  using generation_payload_report_presentation_class by (simp only: generation_payload_report_exact)

interpretation generation_recorded_scope_relation: presented_relation_contract
  generation_source_presents "\<lambda>z. generation_at_context (fst z) (snd z)"
    "\<lambda>t. (152,t)\<in>positive_meaning generation_source_system"
  judgment_context_presents judgment_context_formed "\<lambda>t. (157,t)\<in>positive_meaning context_admission_system"
  generation_recorded_scope "\<lambda>p q. (162,Pair_Term p q)\<in>positive_meaning generation_scope_system"
  using generation_source_native_presentation_class judgment_context_native_class
  by (simp only: presented_relation_contract_def presented_relation_contract_axioms_def
    generation_recorded_report_exact generation_scope_report_relation; blast)

interpretation generation_payload_scope_relation: presented_relation_contract
  generation_source_presents "\<lambda>z. generation_at_context (fst z) (snd z)"
    "\<lambda>t. (152,t)\<in>positive_meaning generation_source_system"
  program_scope_value_presents program_scope_subject
    "\<lambda>t. (122,t)\<in>positive_meaning package_retention_admission_system"
  generation_payload_scope "\<lambda>p q. (167,Pair_Term p q)\<in>positive_meaning generation_scope_system"
  using generation_source_native_presentation_class program_scope_value_presentation_class
  by (simp only: presented_relation_contract_def presented_relation_contract_axioms_def
    generation_payload_report_exact generation_payload_report_relation; blast)

lemma generation_recorded_scope_function_exact:
  "(162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    presented_relation generation_recorded_scope_presents judgment_context_presents (\<lambda>z j. j=snd z) p q"
  by (auto simp: generation_recorded_report_exact generation_scope_report_presents_def
    generation_recorded_scope_presents_def factor_pair_presents_def presented_relation_def;
    metis fst_conv snd_conv)

lemma generation_payload_scope_function_exact:
  "(167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    presented_relation generation_payload_scope_presents program_scope_value_presents (\<lambda>z k. k=snd z) p q"
  by (auto simp: generation_payload_report_exact generation_payload_report_presents_def
    generation_payload_scope_presents_def factor_pair_presents_def presented_relation_def;
    metis fst_conv snd_conv)

interpretation generation_recorded_scope_reading: presented_function_contract
  generation_recorded_scope_presents "\<lambda>z. generation_recorded_scope (fst z) (snd z)"
    "\<lambda>t. (163,t)\<in>positive_meaning generation_scope_system"
  judgment_context_presents judgment_context_formed "\<lambda>t. (157,t)\<in>positive_meaning context_admission_system"
  snd "\<lambda>p q. (162,Pair_Term p q)\<in>positive_meaning generation_scope_system"
  using generation_recorded_scope_native_class judgment_context_native_class generation_recorded_scope_formed
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def generation_recorded_scope_function_exact; blast)

interpretation generation_payload_scope_reading: presented_function_contract
  generation_payload_scope_presents "\<lambda>z. generation_payload_scope (fst z) (snd z)"
    "\<lambda>t. (168,t)\<in>positive_meaning generation_scope_system"
  program_scope_value_presents program_scope_subject
    "\<lambda>t. (122,t)\<in>positive_meaning package_retention_admission_system"
  snd "\<lambda>p q. (167,Pair_Term p q)\<in>positive_meaning generation_scope_system"
  using generation_payload_scope_native_class program_scope_value_presentation_class generation_payload_scope_subject
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def generation_payload_scope_function_exact; blast)

corollary generation_recorded_report_invariance:
  assumes "generation_source_presents z p" "judgment_context_presents j q"
    "generation_source_presents z p'" "judgment_context_presents j q'"
  shows "(162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (162,Pair_Term p' q')\<in>positive_meaning generation_scope_system"
  by (rule generation_recorded_scope_relation.invariance[OF assms])

corollary generation_payload_report_invariance:
  assumes "generation_source_presents z p" "program_scope_value_presents k q"
    "generation_source_presents z p'" "program_scope_value_presents k q'"
  shows "(167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (167,Pair_Term p' q')\<in>positive_meaning generation_scope_system"
  by (rule generation_payload_scope_relation.invariance[OF assms])

corollary generation_recorded_wrong_scope_rejected:
  assumes source: "generation_recorded_scope_presents (z,j) p"
    and expected: "judgment_context_presents k q" and different: "k\<noteq>j"
  shows "(162,Pair_Term p q)\<notin>positive_meaning generation_scope_system"
proof
  assume read: "(162,Pair_Term p q)\<in>positive_meaning generation_scope_system"
  have actual: "judgment_context_presents j q"
    using read by (simp only: generation_recorded_scope_reading.output[OF source] snd_conv)
  have "j=k" by (rule judgments.recovery[OF actual expected])
  then show False using different by simp
qed

corollary generation_payload_wrong_scope_rejected:
  assumes source: "generation_payload_scope_presents (z,k) p"
    and expected: "program_scope_value_presents h q" and different: "h\<noteq>k"
  shows "(167,Pair_Term p q)\<notin>positive_meaning generation_scope_system"
proof
  assume read: "(167,Pair_Term p q)\<in>positive_meaning generation_scope_system"
  have actual: "program_scope_value_presents k q"
    using read by (simp only: generation_payload_scope_reading.output[OF source] snd_conv)
  have "k=h" by (rule presentation_class.recovery[OF program_scope_value_presentation_class actual expected])
  then show False using different by simp
qed

section \<open>Actual core fields preserve scope across outer presentations\<close>

corollary generation_recorded_native_outer_invariance:
  assumes first: "generation_source_presents ((E,(u,r)),G) p"
    and second: "generation_source_presents ((F,(v,a)),H) p'"
    and cause: "generation_cause G=generation_cause H"
    and expected: "judgment_context_presents j q"
  shows "(162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (162,Pair_Term p' q)\<in>positive_meaning generation_scope_system"
  by (simp only: generation_recorded_report_exact generation_scope_report_exact_body[OF first expected]
    generation_scope_report_exact_body[OF second expected] cause)

corollary generation_payload_native_outer_invariance:
  assumes first: "generation_source_presents ((E,(u,r)),G) p"
    and second: "generation_source_presents ((F,(v,a)),H) p'"
    and payload: "generation_payload G=generation_payload H"
    and expected: "program_scope_value_presents k q"
  shows "(167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (167,Pair_Term p' q)\<in>positive_meaning generation_scope_system"
  by (simp only: generation_payload_report_exact generation_payload_report_outer_invariance[OF assms])

theorem generation_scope_native_retention:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
  shows "\<exists>p'. generation_source_presents ((generation_source_environment E u r,(u,r)),G) p' \<and>
    generation_source_environment (generation_source_environment E u r) u r=generation_source_environment E u r \<and>
    (\<forall>q. ((162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
       (162,Pair_Term p' q)\<in>positive_meaning generation_scope_system) \<and>
      ((167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
       (167,Pair_Term p' q)\<in>positive_meaning generation_scope_system)) \<and>
    ((163,p)\<in>positive_meaning generation_scope_system \<longleftrightarrow> (163,p')\<in>positive_meaning generation_scope_system) \<and>
    ((168,p)\<in>positive_meaning generation_scope_system \<longleftrightarrow> (168,p')\<in>positive_meaning generation_scope_system)"
proof -
  let ?R="generation_source_environment E u r"
  have actual: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have retained: "generation_at ?R u r G" by (rule generation_source_environment_properties(2)[OF actual])
  obtain p' where second: "generation_source_presents ((?R,(u,r)),G) p'"
    using generation_source_presentation_total[OF retained] by blast
  have recorded: "generation_recorded_scope ((E,(u,r)),G) j \<longleftrightarrow>
      generation_recorded_scope ((?R,(u,r)),G) j" for j
    using actual retained by (simp add: generation_recorded_scope_def generation_judgment_scope_at_def)
  have carried: "generation_payload_scope ((E,(u,r)),G) k \<longleftrightarrow>
      generation_payload_scope ((?R,(u,r)),G) k" for k
    using actual retained by (simp add: generation_payload_scope_def)
  have reports: "((162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
       (162,Pair_Term p' q)\<in>positive_meaning generation_scope_system) \<and>
      ((167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
       (167,Pair_Term p' q)\<in>positive_meaning generation_scope_system)" for q
    by (simp only: generation_recorded_report_at_source[OF source] generation_recorded_report_at_source[OF second]
      generation_payload_report_at_source[OF source] generation_payload_report_at_source[OF second] recorded carried)
  have sources: "((163,p)\<in>positive_meaning generation_scope_system \<longleftrightarrow> (163,p')\<in>positive_meaning generation_scope_system) \<and>
      ((168,p)\<in>positive_meaning generation_scope_system \<longleftrightarrow> (168,p')\<in>positive_meaning generation_scope_system)"
    by (simp only: generation_recorded_projection.exact generation_payload_projection.exact)
      (use reports in blast)
  show ?thesis using second generation_source_environment_properties(6)[OF actual] reports sources by blast
qed

theorem generation_recorded_native_material:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and expected: "judgment_context_presents (F,((pu,pr),(au,ar))) q"
    and read: "(162,Pair_Term p q)\<in>positive_meaning generation_scope_system"
  shows "\<exists>C cr v R lr M payr cause_r cite I cu.
    generation_cause G=Whole_Artifact C \<and> artifact_at E cu C \<and>
    complete_data_quoted_at C cr v \<and> judgment_value_presents F pu pr au ar v \<and>
    term_quoted_at E cu cr v (rra_carrier (object_structure C)) {} \<and>
    artifact_at E u R \<and> generation_syntax_at R r lr M payr cause_r \<and>
    citation_at R cause_r cite I \<and> interpret_citation E u cite (Whole_Artifact C) \<and>
    ((cite=Local_Whole \<and> cu=u) \<or> (\<exists>k. cite=External_Whole k \<and> binds_slot E u k cu))"
proof -
  have scope: "generation_recorded_scope ((E,(u,r)),G) (F,((pu,pr),(au,ar)))"
    using read by (simp only: generation_recorded_scope_relation.at[OF source expected])
  have presented: "generation_recorded_scope_presents (((E,(u,r)),G),(F,((pu,pr),(au,ar)))) p"
    using source scope by (simp add: generation_recorded_scope_presents_def)
  show ?thesis by (rule generation_recorded_scope_material[OF presented])
qed

theorem generation_payload_native_material:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and expected: "program_scope_value_presents ((F,(pu,pr)),P) q"
    and read: "(167,Pair_Term p q)\<in>positive_meaning generation_scope_system"
  shows "\<exists>C cr v R lr M payr cause_r cite I cu.
    generation_payload G=Whole_Artifact C \<and> artifact_at E cu C \<and>
    complete_data_quoted_at C cr v \<and> program_scope_value_presents ((F,(pu,pr)),P) v \<and>
    term_quoted_at E cu cr v (rra_carrier (object_structure C)) {} \<and>
    artifact_at E u R \<and> generation_syntax_at R r lr M payr cause_r \<and>
    citation_at R payr cite I \<and> interpret_citation E u cite (Whole_Artifact C) \<and>
    ((cite=Local_Whole \<and> cu=u) \<or> (\<exists>k. cite=External_Whole k \<and> binds_slot E u k cu))"
proof -
  have scope: "generation_payload_scope ((E,(u,r)),G) ((F,(pu,pr)),P)"
    using read by (simp only: generation_payload_scope_relation.at[OF source expected])
  have presented: "generation_payload_scope_presents (((E,(u,r)),G),((F,(pu,pr)),P)) p"
    using source scope by (simp add: generation_payload_scope_presents_def)
  show ?thesis by (rule generation_payload_scope_material[OF presented])
qed

section \<open>Total native coverage retains the independence of the two scopes\<close>

theorem generation_recorded_scope_native_total:
  assumes context_formed: "judgment_context_formed j" and locus: "target_formed l"
    and payload: "target_formed pay" and predecessors: "\<forall>H\<in>fset V. generation_formed H"
  shows "\<exists>E u C p. generation_at E u [] (Generation l V pay (Whole_Artifact C)) \<and>
    generation_source_environment E u []=E \<and>
    generation_recorded_scope_presents (((E,(u,[])),Generation l V pay (Whole_Artifact C)),j) p \<and>
    (163,p)\<in>positive_meaning generation_scope_system \<and>
    (\<forall>q. (162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow> judgment_context_presents j q)"
proof -
  obtain E u C where actual: "generation_at E u [] (Generation l V pay (Whole_Artifact C))"
    and retained: "generation_source_environment E u []=E"
    and scope: "generation_recorded_scope ((E,(u,[])),Generation l V pay (Whole_Artifact C)) j"
    using generation_recorded_scope_total[OF assms] by blast
  obtain p where source: "generation_source_presents ((E,(u,[])),Generation l V pay (Whole_Artifact C)) p"
    using generation_source_presentation_total[OF actual] by blast
  have presented: "generation_recorded_scope_presents (((E,(u,[])),Generation l V pay (Whole_Artifact C)),j) p"
    using source scope by (simp add: generation_recorded_scope_presents_def)
  have admitted: "(163,p)\<in>positive_meaning generation_scope_system"
    by (rule generation_recorded_scope_reading.left.presentation_boundary[OF presented])
  have reports: "(162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow> judgment_context_presents j q" for q
    by (simp only: generation_recorded_scope_reading.output[OF presented] snd_conv)
  show ?thesis using actual retained presented admitted reports by blast
qed

theorem generation_payload_scope_native_total:
  assumes scope_formed: "program_scope_subject k" and locus: "target_formed l"
    and cause: "target_formed cause" and predecessors: "\<forall>H\<in>fset V. generation_formed H"
  shows "\<exists>E u C p. generation_at E u [] (Generation l V (Whole_Artifact C) cause) \<and>
    generation_source_environment E u []=E \<and>
    generation_payload_scope_presents (((E,(u,[])),Generation l V (Whole_Artifact C) cause),k) p \<and>
    (168,p)\<in>positive_meaning generation_scope_system \<and>
    (\<forall>q. (167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow> program_scope_value_presents k q)"
proof -
  obtain E u C where actual: "generation_at E u [] (Generation l V (Whole_Artifact C) cause)"
    and retained: "generation_source_environment E u []=E"
    and scope: "generation_payload_scope ((E,(u,[])),Generation l V (Whole_Artifact C) cause) k"
    using generation_payload_scope_total[OF assms] by blast
  obtain p where source: "generation_source_presents ((E,(u,[])),Generation l V (Whole_Artifact C) cause) p"
    using generation_source_presentation_total[OF actual] by blast
  have presented: "generation_payload_scope_presents (((E,(u,[])),Generation l V (Whole_Artifact C) cause),k) p"
    using source scope by (simp add: generation_payload_scope_presents_def)
  have admitted: "(168,p)\<in>positive_meaning generation_scope_system"
    by (rule generation_payload_scope_reading.left.presentation_boundary[OF presented])
  have reports: "(167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow> program_scope_value_presents k q" for q
    by (simp only: generation_payload_scope_reading.output[OF presented] snd_conv)
  show ?thesis using actual retained presented admitted reports by blast
qed

theorem generation_native_scopes_independent:
  assumes "judgment": "judgment_context_formed j" and program: "program_scope_subject k"
    and locus: "target_formed l" and predecessors: "\<forall>H\<in>fset V. generation_formed H"
  shows "\<exists>E u C D p. generation_at E u [] (Generation l V (Whole_Artifact C) (Whole_Artifact D)) \<and>
    generation_source_environment E u []=E \<and>
    generation_recorded_scope_presents (((E,(u,[])),Generation l V (Whole_Artifact C) (Whole_Artifact D)),j) p \<and>
    generation_payload_scope_presents (((E,(u,[])),Generation l V (Whole_Artifact C) (Whole_Artifact D)),k) p \<and>
    (163,p)\<in>positive_meaning generation_scope_system \<and> (168,p)\<in>positive_meaning generation_scope_system \<and>
    (\<forall>q. (162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow> judgment_context_presents j q) \<and>
    (\<forall>q. (167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow> program_scope_value_presents k q)"
proof -
  obtain F pu pr P where coordinates: "k=((F,(pu,pr)),P)" by (cases k; auto)
  have closed: "closed_native_package_at F pu pr P" using program coordinates by simp
  have package: "native_package_at F pu pr P" using closed by (simp add: closed_native_package_at_def)
  obtain C where cf: "exact_formed C" and quote: "program_scope_quoted_at C [] F pu pr P"
    using program_scope_quoted_total[OF package] native_package_closed_environment_fixed[OF closed] by auto
  have payload: "target_formed (Whole_Artifact C)" using cf by simp
  obtain E u D p where actual: "generation_at E u [] (Generation l V (Whole_Artifact C) (Whole_Artifact D))"
    and retained: "generation_source_environment E u []=E"
    and recorded: "generation_recorded_scope_presents (((E,(u,[])),Generation l V (Whole_Artifact C) (Whole_Artifact D)),j) p"
    and admitted: "(163,p)\<in>positive_meaning generation_scope_system"
    and reports: "\<forall>q. (162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow> judgment_context_presents j q"
    using generation_recorded_scope_native_total[OF "judgment" locus payload predecessors] by blast
  let ?G="Generation l V (Whole_Artifact C) (Whole_Artifact D)"
  have carried: "generation_payload_scope ((E,(u,[])),?G) k"
    using actual generation_at_formed[OF actual] quote
    by (auto simp: coordinates generation_payload_scope_def generation_program_scope_def)
  have source: "generation_source_presents ((E,(u,[])),?G) p"
    using recorded by (simp add: generation_recorded_scope_presents_def)
  have presented: "generation_payload_scope_presents (((E,(u,[])),?G),k) p"
    using source carried by (simp add: generation_payload_scope_presents_def)
  have second_admitted: "(168,p)\<in>positive_meaning generation_scope_system"
    by (rule generation_payload_scope_reading.left.presentation_boundary[OF presented])
  have second_reports: "\<forall>q. (167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow> program_scope_value_presents k q"
    by (intro allI; simp only: generation_payload_scope_reading.output[OF presented] snd_conv)
  show ?thesis using actual retained recorded presented admitted reports second_admitted second_reports by blast
qed

section \<open>Native scope recovery remains separate from cause validity\<close>

theorem generation_recorded_native_scope_does_not_validate_cause:
  "\<exists>F pu pr au ar E u G p q.
    native_application_formed F pu pr au ar \<and> \<not>native_positive_holds F pu pr au ar \<and>
    generation_source_environment E u []=E \<and> generation_source_presents ((E,(u,[])),G) p \<and>
    judgment_context_presents (F,((pu,pr),(au,ar))) q \<and>
    (162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<and>
    (163,p)\<in>positive_meaning generation_scope_system \<and> \<not>generation_cause_valid_at E u [] G"
proof -
  obtain F pu pr au ar E u G p q where formed: "native_application_formed F pu pr au ar"
    and false: "\<not>native_positive_holds F pu pr au ar" and retained: "generation_source_environment E u []=E"
    and source: "generation_source_presents ((E,(u,[])),G) p"
    and expected: "judgment_context_presents (F,((pu,pr),(au,ar))) q"
    and report: "generation_scope_report_presents (((E,(u,[])),G),(F,((pu,pr),(au,ar)))) (Pair_Term p q)"
    and invalid: "\<not>generation_cause_valid_at E u [] G"
    using generation_scope_presentations_do_not_validate_causes by blast
  have native: "(162,Pair_Term p q)\<in>positive_meaning generation_scope_system"
    using report by (simp only: generation_recorded_report_exact) blast
  have admission: "(163,p)\<in>positive_meaning generation_scope_system"
    by (simp only: generation_recorded_projection.exact) (use native in blast)
  show ?thesis using formed false retained source expected native admission invalid by blast
qed

theorem generation_payload_native_scope_does_not_validate_cause:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E pu pr P" and locus: "target_formed l"
  shows "\<exists>A u G p q. generation_at A u [] G \<and> generation_source_environment A u []=A \<and>
    generation_source_presents ((A,(u,[])),G) p \<and>
    program_scope_value_presents ((native_package_environment E pu pr,(pu,pr)),P) q \<and>
    (167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<and>
    (168,p)\<in>positive_meaning generation_scope_system \<and> \<not>generation_cause_valid_at A u [] G"
proof -
  obtain A :: "local_address option artifact_environment" and u G
    where actual: "generation_at A u [] G" and retained: "generation_environment_closed A {(u,[])}"
    and scope: "generation_program_scope G (native_package_environment E pu pr) pu pr P"
    and invalid: "\<not>generation_cause_valid_at A u [] G"
    using program_payload_does_not_validate_cause[OF assms] by blast
  have linked: "generation_payload_scope ((A,(u,[])),G) ((native_package_environment E pu pr,(pu,pr)),P)"
    using actual scope by (simp add: generation_payload_scope_def)
  obtain p q where source: "generation_source_presents ((A,(u,[])),G) p"
    and expected: "program_scope_value_presents ((native_package_environment E pu pr,(pu,pr)),P) q"
    using generation_payload_report_total[OF linked] by blast
  have native: "(167,Pair_Term p q)\<in>positive_meaning generation_scope_system"
    by (simp only: generation_payload_scope_relation.at[OF source expected]) (rule linked)
  have admission: "(168,p)\<in>positive_meaning generation_scope_system"
    by (simp only: generation_payload_projection.exact) (use native in blast)
  show ?thesis using actual generation_source_environment_fixed[OF retained] source expected native admission invalid by blast
qed

section \<open>Four fixed ordinary entries serve every future formed operand\<close>

abbreviation generation_scope_operation_result :: "nat \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_scope_operation_result d t \<equiv>
    if d=162 then (\<exists>z. generation_scope_report_presents z t)
    else if d=163 then (\<exists>z. generation_recorded_scope_presents z t)
    else if d=167 then (\<exists>z. generation_payload_report_presents z t)
    else (\<exists>z. generation_payload_scope_presents z t)"

theorem generation_scope_operations_exact:
  assumes "d\<in>{162,163,167,168}"
  shows "(d,t)\<in>positive_meaning generation_scope_system \<longleftrightarrow> generation_scope_operation_result d t"
  using assms by (auto simp: generation_recorded_report_exact generation_recorded_source_exact
    generation_payload_report_exact generation_payload_source_exact; blast)

theorem native_generation_scope_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and>
    inj_on g {162::nat,163,167,168} \<and>
    (\<forall>d\<in>{162,163,167,168}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> generation_scope_operation_result d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  have selected: "{162,163,167,168}\<subseteq>system_definitions generation_scope_system" by auto
  have calls: "schema_call_formed generation_scope_system d t \<longleftrightarrow> term_formed t"
    if "d\<in>{162,163,167,168}" for d t
    using generation_scope_call[of d t] selected that by blast
  show ?thesis by (rule compiled_exact_operations[OF generation_scope_system_formed selected calls generation_scope_operations_exact])
qed

text \<open>
  The two linked notions now own source classes, report classes, relation
  contracts, and total functions recovering their uniquely determined scopes.
  Clients obtain invariance, compatible outputs, and rejection of another
  scope through those contracts. They need not reconstruct quotation or the
  native clause meanings. Retention preserves every report at the least
  generation source environment, and the material contracts keep each actual
  citation, artifact use, and complete quoted body.

  Every formed judgment context and every closed program scope can be carried
  independently by one actual generation. Neither source class requires the
  other. A false native call still has a readable recorded scope, and every
  actual program can be carried with an invalid cause. Cause validity,
  authority, adoption, and amendment remain separate relations.

  One fixed closed native program implements all four operations before any
  future operand is supplied. The complete stored program, its scope, artifacts,
  and bindings persist in each future application environment. No semantic
  primitive, negative premise, nominal identifier, or size bound was added.
\<close>

end
