theory Factor_Construction_Cause_Contracts
  imports Factor_Construction_Cause_Admission Factor_Construction_Cause_Material Factor_Compiled_Applications
begin

definition construction_cause_result where
  "construction_cause_result C k (d::nat) t \<longleftrightarrow>
    (if d=265 then (\<exists>z. construction_profile_report_presents C k z t)
     else if d=266 then (\<exists>z. construction_profile_source_presents C k z t)
     else if d=267 then (\<exists>z. recorded_construction_report_presents C k z t)
     else if d=268 then (\<exists>z. recorded_construction_source_presents C k z t)
     else False)"

context construction_permission_admission
begin

section \<open>Four native entries admit exactly the complete presentation classes\<close>

theorem construction_profile_report_native_exact:
  "(265,t)\<in>positive_meaning (construction_cause_system c (definition_site_value k)) \<longleftrightarrow>
    (\<exists>z. construction_profile_report_presents C k z t)"
  by (auto simp: checker.construction_profile_native_join construction_profile_reading_exact presented_relation_def
    construction_profile_report_presents_def factor_pair_presents_def; metis fst_conv snd_conv)

theorem construction_profile_source_native_exact:
  "(266,p)\<in>positive_meaning (construction_cause_system c (definition_site_value k)) \<longleftrightarrow>
    (\<exists>z. construction_profile_source_presents C k z p)"
proof -
  have total: "\<exists>q. construction_account_presents a q" if "construction_profile_context C k z a" for z a
    using construction_accounts.total[OF conjunct2[OF construction_profile_context_boundary[OF that]]] by blast
  show ?thesis by (simp only: checker.construction_profile_native_source construction_profile_reading_exact)
    (use total in \<open>auto simp: presented_relation_def construction_profile_source_presents_def; metis fst_conv snd_conv\<close>)
qed

theorem construction_profile_report_native_class:
  "presentation_class (construction_profile_report_presents C k) (\<lambda>z. construction_profile_context C k (fst z) (snd z))
    (\<lambda>p. (265,p)\<in>positive_meaning (construction_cause_system c (definition_site_value k)))"
  using construction_profile_report_class by (simp only: construction_profile_report_native_exact)

theorem construction_profile_source_native_class:
  "presentation_class (construction_profile_source_presents C k) (\<lambda>z. construction_profile_context C k (fst z) (snd z))
    (\<lambda>p. (266,p)\<in>positive_meaning (construction_cause_system c (definition_site_value k)))"
  using construction_profile_source_class by (simp only: construction_profile_source_native_exact)

interpretation native_construction_relation: presented_relation_contract
  judgment_context_presents "judgment_context_formed" "\<lambda>p. \<exists>z. judgment_context_presents z p"
  construction_account_presents construction_account_domain "\<lambda>q. \<exists>a. construction_account_presents a q"
  "construction_profile_context C k" "\<lambda>p q. (265,Pair_Term p q)\<in>positive_meaning (construction_cause_system c (definition_site_value k))"
  using judgment_context_presentation_class construction_account_presentation_class construction_profile_reading_exact
  by (simp only: presented_relation_contract_def presented_relation_contract_axioms_def checker.construction_profile_native_at; blast)

interpretation native_construction_reading: presented_function_contract
  "construction_profile_source_presents C k" "\<lambda>z. construction_profile_context C k (fst z) (snd z)"
    "\<lambda>p. (266,p)\<in>positive_meaning (construction_cause_system c (definition_site_value k))"
  construction_account_presents construction_account_domain "\<lambda>q. \<exists>a. construction_account_presents a q"
  snd "\<lambda>p q. (265,Pair_Term p q)\<in>positive_meaning (construction_cause_system c (definition_site_value k))"
  using construction_profile_source_native_class construction_account_presentation_class construction_profile_context_boundary
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def checker.construction_profile_native_at
    construction_profile_function_exact; blast)

theorem recorded_construction_report_native_exact:
  "(267,t)\<in>positive_meaning (construction_cause_system c (definition_site_value k)) \<longleftrightarrow>
    (\<exists>z. recorded_construction_report_presents C k z t)"
  by (auto simp: checker.recorded_construction_native_join recorded_construction_reading_exact presented_relation_def
    recorded_construction_report_presents_def factor_pair_presents_def; metis fst_conv snd_conv)

theorem recorded_construction_source_native_exact:
  "(268,p)\<in>positive_meaning (construction_cause_system c (definition_site_value k)) \<longleftrightarrow>
    (\<exists>z. recorded_construction_source_presents C k z p)"
proof -
  have total: "\<exists>q. construction_account_presents a q" if "recorded_construction_profile C k z a" for z a
    using construction_accounts.total[OF conjunct2[OF recorded_construction_profile_boundary[OF that]]] by blast
  show ?thesis by (simp only: checker.recorded_construction_native_source recorded_construction_reading_exact)
    (use total in \<open>auto simp: presented_relation_def recorded_construction_source_presents_def; metis fst_conv snd_conv\<close>)
qed

theorem recorded_construction_report_native_class:
  "presentation_class (recorded_construction_report_presents C k) (\<lambda>z. recorded_construction_profile C k (fst z) (snd z))
    (\<lambda>p. (267,p)\<in>positive_meaning (construction_cause_system c (definition_site_value k)))"
  using recorded_construction_report_class by (simp only: recorded_construction_report_native_exact)

theorem recorded_construction_source_native_class:
  "presentation_class (recorded_construction_source_presents C k) (\<lambda>z. recorded_construction_profile C k (fst z) (snd z))
    (\<lambda>p. (268,p)\<in>positive_meaning (construction_cause_system c (definition_site_value k)))"
  using recorded_construction_source_class by (simp only: recorded_construction_source_native_exact)

interpretation native_recorded_relation: presented_relation_contract
  generation_source_presents "\<lambda>z. generation_at_context (fst z) (snd z)" "\<lambda>p. \<exists>z. generation_source_presents z p"
  construction_account_presents construction_account_domain "\<lambda>q. \<exists>a. construction_account_presents a q"
  "recorded_construction_profile C k" "\<lambda>p q. (267,Pair_Term p q)\<in>positive_meaning (construction_cause_system c (definition_site_value k))"
  using generation_source_presentation_class construction_account_presentation_class recorded_construction_reading_exact
  by (simp only: presented_relation_contract_def presented_relation_contract_axioms_def checker.recorded_construction_native_at; blast)

interpretation native_recorded_reading: presented_function_contract
  "recorded_construction_source_presents C k" "\<lambda>z. recorded_construction_profile C k (fst z) (snd z)"
    "\<lambda>p. (268,p)\<in>positive_meaning (construction_cause_system c (definition_site_value k))"
  construction_account_presents construction_account_domain "\<lambda>q. \<exists>a. construction_account_presents a q"
  snd "\<lambda>p q. (267,Pair_Term p q)\<in>positive_meaning (construction_cause_system c (definition_site_value k))"
  using recorded_construction_source_native_class construction_account_presentation_class recorded_construction_profile_boundary
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def checker.recorded_construction_native_at
    recorded_construction_function_exact; blast)

section \<open>The native recorded reader retains the original scope and payload conditions\<close>

theorem native_recorded_outer_invariance:
  assumes first: "generation_source_presents z p" and second: "generation_source_presents w v"
    and cause: "generation_cause (snd z)=generation_cause (snd w)"
    and payload: "generation_payload (snd z)=generation_payload (snd w)"
  shows "(267,Pair_Term p q)\<in>positive_meaning (construction_cause_system c (definition_site_value k)) \<longleftrightarrow>
    (267,Pair_Term v q)\<in>positive_meaning (construction_cause_system c (definition_site_value k))"
    and "(268,p)\<in>positive_meaning (construction_cause_system c (definition_site_value k)) \<longleftrightarrow>
    (268,v)\<in>positive_meaning (construction_cause_system c (definition_site_value k))"
  by (simp only: checker.recorded_construction_native_at checker.recorded_construction_native_source
    recorded_reading_outer_invariance[OF assms])+

theorem native_recorded_retention:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
  shows "\<exists>v. generation_source_presents ((generation_source_environment E u r,(u,r)),G) v \<and>
    (\<forall>q. (267,Pair_Term p q)\<in>positive_meaning (construction_cause_system c (definition_site_value k)) \<longleftrightarrow>
      (267,Pair_Term v q)\<in>positive_meaning (construction_cause_system c (definition_site_value k))) \<and>
    ((268,p)\<in>positive_meaning (construction_cause_system c (definition_site_value k)) \<longleftrightarrow>
      (268,v)\<in>positive_meaning (construction_cause_system c (definition_site_value k)))"
  using recorded_reading_retention[OF source]
  by (simp only: checker.recorded_construction_native_at checker.recorded_construction_native_source; blast)

corollary native_recorded_wrong_payload:
  assumes "generation_source_presents z p" "construction_account_presents a q"
    "generation_payload (snd z)\<noteq>Whole_Artifact (construction_account_output a)"
  shows "(267,Pair_Term p q)\<notin>positive_meaning (construction_cause_system c (definition_site_value k))"
  by (simp only: checker.recorded_construction_native_at; rule recorded_reading_wrong_payload[OF assms])

corollary native_recorded_nonminimal_scope:
  assumes "generation_source_presents z p" "generation_recorded_scope z j"
    "judgment_required_environment j\<noteq>fst j"
  shows "(267,Pair_Term p q)\<notin>positive_meaning (construction_cause_system c (definition_site_value k))"
    and "(268,p)\<notin>positive_meaning (construction_cause_system c (definition_site_value k))"
  using recorded_reading_nonminimal_scope[OF assms]
  by (simp only: checker.recorded_construction_native_at checker.recorded_construction_native_source; blast)+

section \<open>One closed program provides every future formed call at all four entries\<close>

lemma construction_cause_native_result:
  assumes "d\<in>{265,266,267,268}"
  shows "(d,t)\<in>positive_meaning (construction_cause_system c (definition_site_value k)) \<longleftrightarrow>
    construction_cause_result C k d t"
  using assms by (auto simp: construction_cause_result_def construction_profile_report_native_exact
    construction_profile_source_native_exact recorded_construction_report_native_exact recorded_construction_source_native_exact)

theorem construction_cause_native_operations:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and> inj_on g {265,266,267,268} \<and>
    (\<forall>d\<in>{265,266,267,268}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> construction_cause_result C k d t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>s w. binds_slot F v s w \<longleftrightarrow> binds_slot E v s w)))"
  by (rule compiled_exact_operations[where D="{265,266,267,268}" and J="construction_cause_result C k",
      OF checker.construction_cause_system_formed _ _ construction_cause_native_result])
    (auto simp: checker.construction_cause_call)

theorem native_profile_recording_total:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and profile: "native_related_test_package C k E pu pr d"
    and account: "construction_account_presents a t" and truth: "(d,t)\<in>positive_meaning P"
    and locus: "target_formed l" and predecessors: "\<forall>H\<in>fset V. generation_formed H"
  shows "\<exists>F D A u. F=native_judgment_environment E pu pr au ar \<and>
    native_package_at F pu pr P \<and> native_application_at F au ar d t I K \<and>
    F=native_judgment_environment F pu pr au ar \<and> judgment_value_quoted_at D [] F pu pr au ar \<and>
    generation_at A u [] (Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) \<and>
    generation_source_environment A u []=A \<and>
    recorded_construction_profile C k ((A,(u,[])),Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) a \<and>
    (\<forall>p q. generation_source_presents ((A,(u,[])),Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) p \<longrightarrow>
      construction_account_presents a q \<longrightarrow> (267,Pair_Term p q)\<in>positive_meaning (construction_cause_system c (definition_site_value k)))"
  using profile_recording_total[OF assms]
  by (simp only: checker.recorded_construction_native_at)

end

context construction_permission_completion
begin

theorem all_accounts_have_native_profiled_recordings:
  "\<exists>E pu P d. closed_native_package_at E pu [] P \<and> native_related_test_package C k E pu [] d \<and>
    (\<forall>a l V. construction_account_domain a \<longrightarrow> target_formed l \<longrightarrow>
      (\<forall>H\<in>fset V. generation_formed H) \<longrightarrow>
      (\<exists>A u D. generation_at A u [] (Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) \<and>
        generation_source_environment A u []=A \<and>
        recorded_construction_profile C k ((A,(u,[])),Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) a \<and>
        (\<forall>p q. generation_source_presents ((A,(u,[])),Generation l V (Whole_Artifact (construction_account_output a)) (Whole_Artifact D)) p \<longrightarrow>
          construction_account_presents a q \<longrightarrow> (267,Pair_Term p q)\<in>positive_meaning (construction_cause_system c (definition_site_value k)))))"
  using all_accounts_have_profiled_recordings
  by (simp only: checker.recorded_construction_native_at)

end

text \<open>
  The four native presentation classes and both relation and determined-output
  contracts follow from the actual complete clause families. Every compatible
  account presentation is admitted. Outer source retention, wrong-payload
  rejection, and the least quoted judgment scope retain their original force.

  One finite closed native program supports every future formed argument at
  all four distinct compiled entries. It preserves its canonical scope and
  every existing artifact and binding. Actual recordings retain the original
  profiled program and application; every complete account has such a recording.

  The sufficient whole-definition permission profile remains an explicit
  restriction of the original construction judgment. This program does not
  decide arbitrary programs' global invariance or provide native checking of
  the mathematical proofs of these contracts.
\<close>

end
