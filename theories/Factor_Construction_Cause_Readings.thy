theory Factor_Construction_Cause_Readings
  imports Factor_Construction_Cause_Presentations Factor_Generation_Scope_Contracts
    Factor_Judgment_Retention_Contracts
begin

section \<open>The independent join names only actual ordinary reader calls\<close>

definition construction_profile_reading where
  "construction_profile_reading c k p q \<longleftrightarrow> (\<exists>e pu pr au ar d t i s.
    p=judgment_context_term e pu pr au ar \<and>
    (115,p)\<in>positive_meaning native_positive_admission_system \<and>
    (58,application_reading_argument e au ar d t i s)\<in>positive_meaning application_reading_system \<and>
    (264,related_test_admission_argument e pu pr d)\<in>positive_meaning (related_test_admission_system c k) \<and>
    (261,Pair_Term t q)\<in>positive_meaning construction_comparison_system)"

definition recorded_construction_reading where
  "recorded_construction_reading c k p q \<longleftrightarrow> (\<exists>x b s orig out l ps pay cause j.
    q=enumeration_term [x,b,s,orig,out] \<and>
    (151,Pair_Term p (generation_fields_term l ps (Pair_Term pay (Payload_Term [])) cause))
      \<in>positive_meaning generation_source_system \<and>
    (162,Pair_Term p j)\<in>positive_meaning generation_scope_system \<and>
    (183,j)\<in>positive_meaning judgment_retention_system \<and>
    construction_profile_reading c k j q \<and>
    (10,Pair_Term out pay)\<in>positive_meaning artifact_projection_system)"

context construction_permission_admission
begin

lemma profile_context_at_reads:
  assumes package: "native_package_at F pu pr P" and app: "native_application_at F au ar d t I K"
  shows "construction_profile_context C k (F,((pu,pr),(au,ar))) a \<longleftrightarrow>
    native_related_test_package C k F pu pr d \<and> construction_account_presents a t \<and>
    (d,t)\<in>positive_meaning P"
  using profile_permission(1)[OF package]
  by (simp only: construction_profile_context_def construction_context_profile_at_reads[OF app]
    fst_conv snd_conv construction_judgment_at_account[OF package app]; blast)

theorem construction_profile_reading_sound:
  assumes read: "construction_profile_reading c (definition_site_value k) p q"
  shows "\<exists>j a. judgment_context_presents j p \<and> construction_profile_context C k j a \<and>
    construction_account_presents a q"
proof -
  obtain e pu pr au ar site t i s where fields: "p=judgment_context_term e pu pr au ar"
    and positive: "(115,p)\<in>positive_meaning native_positive_admission_system"
    and application: "(58,application_reading_argument e au ar site t i s)\<in>positive_meaning application_reading_system"
    and checked: "(264,related_test_admission_argument e pu pr site)\<in>positive_meaning
      (related_test_admission_system c (definition_site_value k))"
    and compared: "(261,Pair_Term t q)\<in>positive_meaning construction_comparison_system"
    using read by (auto simp: construction_profile_reading_def)
  obtain F u r v a where context_value: "judgment_value_presents F u r v a p"
    and truth: "native_positive_holds F u r v a"
    using native_positive_admission_sound[OF positive] by blast
  obtain f where source: "environment_value_presents F f"
    and shape: "p=judgment_context_term f (use_data_term u) (Payload_Term r) (use_data_term v) (Payload_Term a)"
    using context_value by (auto simp: judgment_value_presents_def site_data_term_def)
  have coordinates: "e=f" "pu=use_data_term u" "pr=Payload_Term r"
    "au=use_data_term v" "ar=Payload_Term a" using fields shape by simp_all
  obtain P d z I K where package: "native_package_at F u r P" and app: "native_application_at F v a d z I K"
    and holds: "(d,z)\<in>positive_meaning P" using truth by (auto simp: native_positive_holds_def)
  obtain du dr Is Ks where site: "site=site_data_term du dr"
    and other: "native_application_at F v a (du,dr) t (set Is) (set Ks)"
    using application by (auto simp: coordinates application_reading_at_source[OF source]
      inj_eq[OF use_data_term_injective])
  have same: "(du,dr)=d" "t=z" using native_application_unique[OF other app] by blast+
  have encoded: "site=definition_site_value d"
    using site by (simp only: same(1)[symmetric] fst_conv snd_conv)
  have checked_at: "(264,related_test_admission_argument f (use_data_term u) (Payload_Term r) (definition_site_value d))
      \<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
    using checked by (simp only: coordinates encoded)
  have profile: "native_related_test_package C k F u r d"
    using checked_at by (simp only: checker.on_values[OF reference_value refl source])
  obtain account where input: "construction_account_presents account z" and "output": "construction_account_presents account q"
    using compared by (auto simp: same construction_comparison_exact presentation_transport_def)
  have relation: "construction_profile_context C k (F,((u,r),(v,a))) account"
    by (simp only: profile_context_at_reads[OF package app]) (use profile input holds in blast)
  show ?thesis by (rule exI[of _ "(F,((u,r),(v,a)))"], rule exI[of _ account])
    (use context_value relation "output" in simp)
qed

theorem construction_profile_reading_complete:
  assumes context_value: "judgment_context_presents j p" and relation: "construction_profile_context C k j a"
    and "output": "construction_account_presents a q"
  shows "construction_profile_reading c (definition_site_value k) p q"
proof -
  obtain F pu pr au ar where j: "j=(F,((pu,pr),(au,ar)))" by (cases j; auto split: prod.splits)
  obtain P d t I K where package: "native_package_at F pu pr P" and app: "native_application_at F au ar d t I K"
    using relation by (auto simp: j construction_profile_context_def construction_judgment_at_def)
  have profile: "native_related_test_package C k F pu pr d" and input: "construction_account_presents a t"
    and holds: "(d,t)\<in>positive_meaning P"
    using relation by (simp only: j profile_context_at_reads[OF package app]; blast)+
  obtain e where source: "environment_value_presents F e"
    and shape: "p=judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)"
    using context_value by (auto simp: j judgment_value_presents_def site_data_term_def)
  have truth: "native_positive_holds F pu pr au ar"
    by (simp only: native_positive_holds_with_reads[OF package app]; rule holds)
  have positive: "(115,p)\<in>positive_meaning native_positive_admission_system"
    by (rule native_positive_admission_complete[OF _ truth])
      (use context_value in \<open>simp only: j fst_conv snd_conv\<close>)
  obtain i s where application: "(58,application_reading_argument e (use_data_term au) (Payload_Term ar)
      (definition_site_value d) t i s)\<in>positive_meaning application_reading_system"
    using application_reading_value[OF source app] by blast
  have checked: "(264,related_test_admission_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d))
      \<in>positive_meaning (related_test_admission_system c (definition_site_value k))"
    by (simp only: checker.on_values[OF reference_value refl source]; rule profile)
  have compared: "(261,Pair_Term t q)\<in>positive_meaning construction_comparison_system"
    by (simp only: construction_comparison_on_accounts[OF input "output"]; rule refl)
  show ?thesis unfolding construction_profile_reading_def
    using shape positive application checked compared by blast
qed

theorem construction_profile_reading_exact:
  "construction_profile_reading c (definition_site_value k) p q \<longleftrightarrow>
    presented_relation judgment_context_presents construction_account_presents (construction_profile_context C k) p q"
  using construction_profile_reading_sound construction_profile_reading_complete
  by (simp only: presented_relation_def; blast)

interpretation construction_relation: presented_relation_contract
  judgment_context_presents judgment_context_formed "\<lambda>p. \<exists>j. judgment_context_presents j p"
  construction_account_presents construction_account_domain "\<lambda>q. \<exists>a. construction_account_presents a q"
  "construction_profile_context C k" "construction_profile_reading c (definition_site_value k)"
  using judgment_context_presentation_class construction_account_presentation_class construction_profile_reading_exact
  by (simp only: presented_relation_contract_def presented_relation_contract_axioms_def; blast)

lemma recorded_construction_payload_reading:
  assumes source: "generation_source_presents z p" and account: "construction_account_presents a q"
  shows "(\<exists>x b s orig out l ps pay cause. q=enumeration_term [x,b,s,orig,out] \<and>
    (151,Pair_Term p (generation_fields_term l ps (Pair_Term pay (Payload_Term [])) cause))
      \<in>positive_meaning generation_source_system \<and>
    (10,Pair_Term out pay)\<in>positive_meaning artifact_projection_system) \<longleftrightarrow>
    generation_payload (snd z)=Whole_Artifact (construction_account_output a)"
proof -
  have formed: "generation_formed (snd z)"
    by (rule generation_at_formed[OF generation_sources.subject_boundary[OF source]])
  obtain b s orig where fields: "q=enumeration_term [artifact_list_term (fst (fst a)),b,s,orig,
      Target_Term (Whole_Artifact (construction_account_output a))]"
    using construction_account_fields[OF account] by blast
  have output_formed: "exact_formed (construction_account_output a)"
    using account source_construction_finite(7) by (auto simp: construction_account_presents_def)
  obtain pay where "output": "artifact_value_presents (construction_account_output a) pay"
    using artifact_value_presents_total[OF output_formed] by blast
  have payload: "(\<exists>l ps cause. (151,Pair_Term p (generation_fields_term l ps (Pair_Term v (Payload_Term [])) cause))
      \<in>positive_meaning generation_source_system) \<longleftrightarrow>
      (\<exists>A. generation_payload (snd z)=Whole_Artifact A \<and> artifact_value_presents A v)" for v
    by (simp only: generation_scope_source_value[OF source] generation_value_payload_artifact[OF formed])
  show ?thesis
  proof
    assume "\<exists>x b s orig out l ps pay cause. q=enumeration_term [x,b,s,orig,out] \<and>
      (151,Pair_Term p (generation_fields_term l ps (Pair_Term pay (Payload_Term [])) cause))
        \<in>positive_meaning generation_source_system \<and>
      (10,Pair_Term out pay)\<in>positive_meaning artifact_projection_system"
    then obtain x b' s' orig' out l ps v cause where shape: "q=enumeration_term [x,b',s',orig',out]"
      and generation: "(151,Pair_Term p (generation_fields_term l ps (Pair_Term v (Payload_Term [])) cause))
        \<in>positive_meaning generation_source_system"
      and projection: "(10,Pair_Term out v)\<in>positive_meaning artifact_projection_system" by blast
    have last: "out=Target_Term (Whole_Artifact (construction_account_output a))"
      using shape fields by (auto simp: enumeration_term_injective)
    have expected: "artifact_value_presents (construction_account_output a) v"
      using projection by (simp only: last artifact_projection_at_source)
    have reported: "\<exists>l ps cause. (151,Pair_Term p
        (generation_fields_term l ps (Pair_Term v (Payload_Term [])) cause))
      \<in>positive_meaning generation_source_system" using generation by blast
    obtain R where actual: "generation_payload (snd z)=Whole_Artifact R"
      and presented: "artifact_value_presents R v" using reported by (simp only: payload; blast)
    have same: "R=construction_account_output a" by (rule artifact_value_presents_unique[OF presented expected])
    show "generation_payload (snd z)=Whole_Artifact (construction_account_output a)"
      using actual same by simp
  next
    assume actual: "generation_payload (snd z)=Whole_Artifact (construction_account_output a)"
    have reported: "\<exists>l ps cause. (151,Pair_Term p
        (generation_fields_term l ps (Pair_Term pay (Payload_Term [])) cause))
      \<in>positive_meaning generation_source_system"
      by (simp only: payload; rule exI[of _ "construction_account_output a"], rule conjI[OF actual "output"])
    obtain l ps cause where generation: "(151,Pair_Term p
        (generation_fields_term l ps (Pair_Term pay (Payload_Term [])) cause))
      \<in>positive_meaning generation_source_system" using reported by blast
    have projection: "(10,Pair_Term (Target_Term (Whole_Artifact (construction_account_output a))) pay)
      \<in>positive_meaning artifact_projection_system"
      using "output" by (simp only: artifact_projection_at_source)
    show "\<exists>x b s orig out l ps pay cause. q=enumeration_term [x,b,s,orig,out] \<and>
      (151,Pair_Term p (generation_fields_term l ps (Pair_Term pay (Payload_Term [])) cause))
        \<in>positive_meaning generation_source_system \<and>
      (10,Pair_Term out pay)\<in>positive_meaning artifact_projection_system"
      using fields generation projection by blast
  qed
qed

theorem recorded_construction_reading_at_source:
  assumes source: "generation_source_presents z p"
  shows "recorded_construction_reading c (definition_site_value k) p q \<longleftrightarrow>
    (\<exists>a. recorded_construction_profile C k z a \<and> construction_account_presents a q)"
proof -
  have declared: "(\<exists>v. (162,Pair_Term p v)\<in>positive_meaning generation_scope_system \<and>
      (183,v)\<in>positive_meaning judgment_retention_system \<and>
      construction_profile_reading c (definition_site_value k) v q) \<longleftrightarrow>
    (\<exists>j a. generation_recorded_scope z j \<and> judgment_required_environment j=fst j \<and>
      construction_profile_context C k j a \<and> construction_account_presents a q)"
  proof
    assume "\<exists>v. (162,Pair_Term p v)\<in>positive_meaning generation_scope_system \<and>
      (183,v)\<in>positive_meaning judgment_retention_system \<and>
      construction_profile_reading c (definition_site_value k) v q"
    then obtain v j where scope: "generation_recorded_scope z j" and presented: "judgment_context_presents j v"
      and closed: "(183,v)\<in>positive_meaning judgment_retention_system"
      and reading: "construction_profile_reading c (definition_site_value k) v q"
      by (simp only: generation_recorded_scope_relation.at_source[OF source]; blast)
    obtain a where relation: "construction_profile_context C k j a" and "output": "construction_account_presents a q"
      using reading by (simp only: construction_relation.at_source[OF presented]; blast)
    have readable: "judgment_source_presents j v"
      using presented construction_profile_context_boundary[OF relation] by (simp add: judgment_source_presents_def)
    have fixed: "judgment_required_environment j=fst j"
      using closed by (simp only: judgment_closed_source_at_presentation[OF readable])
    show "\<exists>j a. generation_recorded_scope z j \<and> judgment_required_environment j=fst j \<and>
      construction_profile_context C k j a \<and> construction_account_presents a q"
      using scope fixed relation "output" by blast
  next
    assume "\<exists>j a. generation_recorded_scope z j \<and> judgment_required_environment j=fst j \<and>
      construction_profile_context C k j a \<and> construction_account_presents a q"
    then obtain j a where scope: "generation_recorded_scope z j" and fixed: "judgment_required_environment j=fst j"
      and relation: "construction_profile_context C k j a" and "output": "construction_account_presents a q" by blast
    obtain v where presented: "judgment_context_presents j v"
      using judgments.total[OF generation_recorded_scope_formed[OF scope]] by blast
    have readable: "judgment_source_presents j v"
      using presented construction_profile_context_boundary[OF relation] by (simp add: judgment_source_presents_def)
    have read: "(162,Pair_Term p v)\<in>positive_meaning generation_scope_system"
      by (simp only: generation_recorded_scope_relation.at[OF source presented]; rule scope)
    have closed: "(183,v)\<in>positive_meaning judgment_retention_system"
      by (simp only: judgment_closed_source_at_presentation[OF readable]; rule fixed)
    have reading: "construction_profile_reading c (definition_site_value k) v q"
      by (rule construction_profile_reading_complete[OF presented relation "output"])
    show "\<exists>v. (162,Pair_Term p v)\<in>positive_meaning generation_scope_system \<and>
      (183,v)\<in>positive_meaning judgment_retention_system \<and>
      construction_profile_reading c (definition_site_value k) v q" using read closed reading by blast
  qed
  let ?payload="\<exists>x b s orig out l ps pay cause. q=enumeration_term [x,b,s,orig,out] \<and>
    (151,Pair_Term p (generation_fields_term l ps (Pair_Term pay (Payload_Term [])) cause))
      \<in>positive_meaning generation_source_system \<and>
    (10,Pair_Term out pay)\<in>positive_meaning artifact_projection_system"
  let ?scope="\<exists>v. (162,Pair_Term p v)\<in>positive_meaning generation_scope_system \<and>
    (183,v)\<in>positive_meaning judgment_retention_system \<and>
    construction_profile_reading c (definition_site_value k) v q"
  have parts: "recorded_construction_reading c (definition_site_value k) p q \<longleftrightarrow>
      ?payload \<and> ?scope"
    unfolding recorded_construction_reading_def by blast
  show ?thesis
  proof
    assume read: "recorded_construction_reading c (definition_site_value k) p q"
    have payload_read: "?payload" and scope_read: "?scope" using read by (simp only: parts; blast)+
    obtain j a where scope: "generation_recorded_scope z j" and fixed: "judgment_required_environment j=fst j"
      and relation: "construction_profile_context C k j a" and "output": "construction_account_presents a q"
      using scope_read by (simp only: declared; blast)
    have payload: "generation_payload (snd z)=Whole_Artifact (construction_account_output a)"
      using payload_read by (simp only: recorded_construction_payload_reading[OF source "output"])
    have recorded: "recorded_construction_profile C k z a"
      by (simp only: recorded_construction_profile_join; rule exI[of _ j])
        (use scope fixed payload relation in blast)
    show "\<exists>a. recorded_construction_profile C k z a \<and> construction_account_presents a q"
      by (rule exI[of _ a], rule conjI[OF recorded "output"])
  next
    assume "\<exists>a. recorded_construction_profile C k z a \<and> construction_account_presents a q"
    then obtain a where recorded: "recorded_construction_profile C k z a"
      and "output": "construction_account_presents a q" by blast
    obtain j where scope: "generation_recorded_scope z j" and fixed: "judgment_required_environment j=fst j"
      and payload: "generation_payload (snd z)=Whole_Artifact (construction_account_output a)"
      and relation: "construction_profile_context C k j a"
      using recorded by (simp only: recorded_construction_profile_join; blast)
    have payload_read: "?payload" using payload
      by (simp only: recorded_construction_payload_reading[OF source "output"])
    have scope_read: "?scope" by (simp only: declared; rule exI[of _ j], rule exI[of _ a])
      (use scope fixed relation "output" in blast)
    show "recorded_construction_reading c (definition_site_value k) p q"
      by (simp only: parts; rule conjI[OF payload_read scope_read])
  qed
qed

theorem recorded_construction_reading_exact:
  "recorded_construction_reading c (definition_site_value k) p q \<longleftrightarrow>
    presented_relation generation_source_presents construction_account_presents (recorded_construction_profile C k) p q"
proof
  assume read: "recorded_construction_reading c (definition_site_value k) p q"
  obtain v where "(151,Pair_Term p v)\<in>positive_meaning generation_source_system"
    using read by (auto simp: recorded_construction_reading_def)
  then obtain z where source: "generation_source_presents z p"
    by (auto simp: generation_core_report_exact generation_report_presents_def
      factor_pair_presents_def generation_source_presents_def)
  show "presented_relation generation_source_presents construction_account_presents (recorded_construction_profile C k) p q"
    using read source by (simp only: recorded_construction_reading_at_source[OF source] presented_relation_def; blast)
next
  assume "presented_relation generation_source_presents construction_account_presents (recorded_construction_profile C k) p q"
  then obtain z a where source: "generation_source_presents z p" and relation: "recorded_construction_profile C k z a"
    and "output": "construction_account_presents a q" by (auto simp: presented_relation_def)
  show "recorded_construction_reading c (definition_site_value k) p q"
    by (simp only: recorded_construction_reading_at_source[OF source]) (use relation "output" in blast)
qed

interpretation recorded_relation: presented_relation_contract
  generation_source_presents "\<lambda>z. generation_at_context (fst z) (snd z)" "\<lambda>p. \<exists>z. generation_source_presents z p"
  construction_account_presents construction_account_domain "\<lambda>q. \<exists>a. construction_account_presents a q"
  "recorded_construction_profile C k" "recorded_construction_reading c (definition_site_value k)"
  using generation_source_presentation_class construction_account_presentation_class recorded_construction_reading_exact
  by (simp only: presented_relation_contract_def presented_relation_contract_axioms_def; blast)

lemma construction_profile_function_exact:
  "construction_profile_reading c (definition_site_value k) p q \<longleftrightarrow>
    presented_relation (construction_profile_source_presents C k) construction_account_presents (\<lambda>z a. a=snd z) p q"
  by (auto simp: construction_profile_reading_exact presented_relation_def construction_profile_source_presents_def;
    metis fst_conv snd_conv)

interpretation construction_reading: presented_function_contract
  "construction_profile_source_presents C k" "\<lambda>z. construction_profile_context C k (fst z) (snd z)"
    "\<lambda>p. \<exists>z. construction_profile_source_presents C k z p"
  construction_account_presents construction_account_domain "\<lambda>q. \<exists>a. construction_account_presents a q"
  snd "construction_profile_reading c (definition_site_value k)"
  using construction_profile_source_class construction_account_presentation_class construction_profile_context_boundary
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def construction_profile_function_exact; blast)

lemma recorded_construction_function_exact:
  "recorded_construction_reading c (definition_site_value k) p q \<longleftrightarrow>
    presented_relation (recorded_construction_source_presents C k) construction_account_presents (\<lambda>z a. a=snd z) p q"
  by (auto simp: recorded_construction_reading_exact presented_relation_def recorded_construction_source_presents_def;
    metis fst_conv snd_conv)

interpretation recorded_reading: presented_function_contract
  "recorded_construction_source_presents C k" "\<lambda>z. recorded_construction_profile C k (fst z) (snd z)"
    "\<lambda>p. \<exists>z. recorded_construction_source_presents C k z p"
  construction_account_presents construction_account_domain "\<lambda>q. \<exists>a. construction_account_presents a q"
  snd "recorded_construction_reading c (definition_site_value k)"
  using recorded_construction_source_class construction_account_presentation_class recorded_construction_profile_boundary
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def recorded_construction_function_exact; blast)

theorem recorded_reading_outer_invariance:
  assumes first: "generation_source_presents z p" and second: "generation_source_presents w v"
    and cause: "generation_cause (snd z)=generation_cause (snd w)"
    and payload: "generation_payload (snd z)=generation_payload (snd w)"
  shows "recorded_construction_reading c (definition_site_value k) p q \<longleftrightarrow>
    recorded_construction_reading c (definition_site_value k) v q"
  by (simp only: recorded_relation.at_source[OF first] recorded_relation.at_source[OF second]
    recorded_construction_profile_outer_invariance[OF generation_sources.subject_boundary[OF first]
      generation_sources.subject_boundary[OF second] cause payload])

theorem recorded_reading_retention:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
  shows "\<exists>v. generation_source_presents ((generation_source_environment E u r,(u,r)),G) v \<and>
    (\<forall>q. recorded_construction_reading c (definition_site_value k) p q \<longleftrightarrow>
      recorded_construction_reading c (definition_site_value k) v q)"
proof -
  have actual: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  obtain v where retained: "generation_source_presents ((generation_source_environment E u r,(u,r)),G) v"
    using generation_source_presentation_total[OF generation_source_environment_properties(2)[OF actual]] by blast
  have same: "recorded_construction_reading c (definition_site_value k) p q \<longleftrightarrow>
      recorded_construction_reading c (definition_site_value k) v q" for q
    by (rule recorded_reading_outer_invariance[OF source retained]) simp_all
  show ?thesis using retained same by blast
qed

corollary recorded_reading_wrong_payload:
  assumes "generation_source_presents z p" "construction_account_presents a q"
    "generation_payload (snd z)\<noteq>Whole_Artifact (construction_account_output a)"
  shows "\<not>recorded_construction_reading c (definition_site_value k) p q"
  using assms(3) by (simp only: recorded_relation.at[OF assms(1,2)] recorded_construction_profile_join; blast)

corollary recorded_reading_nonminimal_scope:
  assumes "generation_source_presents z p" "generation_recorded_scope z j"
    "judgment_required_environment j\<noteq>fst j"
  shows "\<not>recorded_construction_reading c (definition_site_value k) p q"
  using assms(3) by (simp only: recorded_relation.at_source[OF assms(1)]
    recorded_construction_profile_at_scope[OF assms(2)]; blast)

end

text \<open>
  These are exact joins of existing ordinary reader meanings, established
  before installing the combined clauses in one native program. Every input
  to the join is exposed in the two formulas. The actual application binds
  the program entry, positive truth, and complete account; the comparison
  permits all presentations of that same account. A recorded cause additionally
  binds the exact payload and least quoted judgment environment.

  The independent reference discharges the original global permission
  condition. The resulting relation is a sufficient profile of the original
  judgment, with complete source and output contracts. It neither replaces
  a recorded program nor decides every program's invariance.
  Factor_Construction_Cause_Components establishes the whole shared-definition
  union, including the counted-difference boundaries. The ordinary clauses and
  native contracts are provided in Factor_Construction_Cause_Clauses and
  Factor_Construction_Cause_Contracts.
\<close>

end
