theory Factor_Recorded_Base_Admission
  imports Factor_Base_Admission_Contracts
begin

section \<open>The generation payload and complete recorded declaration are linked\<close>

lemma recorded_base_report_valuation:
  "(187,t)\<in>positive_meaning base_cause_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (h 1) \<and>
      (151,Pair_Term (h 0) (generation_fields_term (h 2) (h 3) (Pair_Term (h 1) (Payload_Term [])) (h 4)))
        \<in>positive_meaning generation_source_system \<and>
      (162,Pair_Term (h 0) (h 5))\<in>positive_meaning generation_scope_system \<and>
      (183,h 5)\<in>positive_meaning judgment_retention_system \<and>
      (185,Pair_Term (h 5) (h 1))\<in>positive_meaning base_cause_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: recorded_base_report_schema_def schema_variables_def base_cause_call base_cause_components)

lemma recorded_base_report_calls:
  "(187,t)\<in>positive_meaning base_cause_system \<longleftrightarrow>
    (\<exists>p q a b c j. t=Pair_Term p q \<and>
      (151,Pair_Term p (generation_fields_term a b (Pair_Term q (Payload_Term [])) c))\<in>positive_meaning generation_source_system \<and>
      (162,Pair_Term p j)\<in>positive_meaning generation_scope_system \<and>
      (183,j)\<in>positive_meaning judgment_retention_system \<and>
      (185,Pair_Term j q)\<in>positive_meaning base_cause_system)"
proof
  assume "(187,t)\<in>positive_meaning base_cause_system"
  then show "\<exists>p q a b c j. t=Pair_Term p q \<and>
      (151,Pair_Term p (generation_fields_term a b (Pair_Term q (Payload_Term [])) c))\<in>positive_meaning generation_source_system \<and>
      (162,Pair_Term p j)\<in>positive_meaning generation_scope_system \<and>
      (183,j)\<in>positive_meaning judgment_retention_system \<and>
      (185,Pair_Term j q)\<in>positive_meaning base_cause_system"
    by (simp only: recorded_base_report_valuation; blast)
next
  assume "\<exists>p q a b c j. t=Pair_Term p q \<and>
      (151,Pair_Term p (generation_fields_term a b (Pair_Term q (Payload_Term [])) c))\<in>positive_meaning generation_source_system \<and>
      (162,Pair_Term p j)\<in>positive_meaning generation_scope_system \<and>
      (183,j)\<in>positive_meaning judgment_retention_system \<and>
      (185,Pair_Term j q)\<in>positive_meaning base_cause_system"
  then obtain p q a b c j where shape: "t=Pair_Term p q"
    and calls: "(151,Pair_Term p (generation_fields_term a b (Pair_Term q (Payload_Term [])) c))\<in>positive_meaning generation_source_system"
    "(162,Pair_Term p j)\<in>positive_meaning generation_scope_system"
    "(183,j)\<in>positive_meaning judgment_retention_system"
    "(185,Pair_Term j q)\<in>positive_meaning base_cause_system" by blast
  have formed: "term_formed p" "term_formed q" "term_formed a" "term_formed b" "term_formed c" "term_formed j"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]] by auto
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then q else if i=2 then a else if i=3 then b else if i=4 then c else j"
  show "(187,t)\<in>positive_meaning base_cause_system"
    by (simp only: recorded_base_report_valuation; rule exI[of _ ?h]) (use shape calls formed in auto)
qed

lemma recorded_base_checked_judgment:
  assumes context_value: "judgment_context_presents j p"
  shows "((183,p)\<in>positive_meaning judgment_retention_system \<and>
      (185,Pair_Term p q)\<in>positive_meaning base_cause_system) \<longleftrightarrow>
    judgment_required_environment j=fst j \<and> (\<exists>R. base_admission_context j R \<and> artifact_value_presents R q)"
proof
  assume calls: "(183,p)\<in>positive_meaning judgment_retention_system \<and>
    (185,Pair_Term p q)\<in>positive_meaning base_cause_system"
  obtain R where admitted: "base_admission_context j R" and expected: "artifact_value_presents R q"
    using calls by (simp only: base_admission_relation.at_source[OF context_value]; blast)
  have source: "judgment_source_presents j p"
    using base_admission_context_source[OF admitted] context_value by (simp only: judgment_source_presents_def)
  have fixed: "judgment_required_environment j=fst j"
    using calls by (simp only: judgment_closed_source_at_presentation[OF source]; blast)
  show "judgment_required_environment j=fst j \<and> (\<exists>R. base_admission_context j R \<and> artifact_value_presents R q)"
    using fixed admitted expected by blast
next
  assume "judgment_required_environment j=fst j \<and> (\<exists>R. base_admission_context j R \<and> artifact_value_presents R q)"
  then obtain R where fixed: "judgment_required_environment j=fst j"
    and admitted: "base_admission_context j R" and expected: "artifact_value_presents R q" by blast
  have source: "judgment_source_presents j p"
    using base_admission_context_source[OF admitted] context_value by (simp only: judgment_source_presents_def)
  have closed: "(183,p)\<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_closed_source_at_presentation[OF source]; rule fixed)
  have base: "(185,Pair_Term p q)\<in>positive_meaning base_cause_system"
    by (simp only: base_admission_relation.at_source[OF context_value]) (use admitted expected in blast)
  show "(183,p)\<in>positive_meaning judgment_retention_system \<and>
      (185,Pair_Term p q)\<in>positive_meaning base_cause_system" using closed base by blast
qed

theorem recorded_base_report_at_source:
  assumes source: "generation_source_presents z p"
  shows "(187,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
    (\<exists>R. recorded_base_context z R \<and> artifact_value_presents R q)"
proof -
  have actual: "generation_at_context (fst z) (snd z)" by (rule generation_sources.subject_boundary[OF source])
  have formed: "generation_formed (snd z)" by (rule generation_at_formed[OF actual])
  have payload: "(\<exists>a b c. (151,Pair_Term p (generation_fields_term a b (Pair_Term q (Payload_Term [])) c))
      \<in>positive_meaning generation_source_system) \<longleftrightarrow>
      (\<exists>R. generation_payload (snd z)=Whole_Artifact R \<and> artifact_value_presents R q)"
    by (simp only: generation_scope_source_value[OF source] generation_value_payload_artifact[OF formed])
  have declared: "(\<exists>v. (162,Pair_Term p v)\<in>positive_meaning generation_scope_system \<and>
      (183,v)\<in>positive_meaning judgment_retention_system \<and>
      (185,Pair_Term v q)\<in>positive_meaning base_cause_system) \<longleftrightarrow>
      (\<exists>j R. generation_recorded_scope z j \<and> judgment_required_environment j=fst j \<and>
        base_admission_context j R \<and> artifact_value_presents R q)"
  proof
    assume "\<exists>v. (162,Pair_Term p v)\<in>positive_meaning generation_scope_system \<and>
      (183,v)\<in>positive_meaning judgment_retention_system \<and>
      (185,Pair_Term v q)\<in>positive_meaning base_cause_system"
    then obtain v j where scope: "generation_recorded_scope z j" and context_value: "judgment_context_presents j v"
      and checks: "(183,v)\<in>positive_meaning judgment_retention_system \<and>
        (185,Pair_Term v q)\<in>positive_meaning base_cause_system"
      by (simp only: generation_recorded_scope_relation.at_source[OF source]; blast)
    show "\<exists>j R. generation_recorded_scope z j \<and> judgment_required_environment j=fst j \<and>
        base_admission_context j R \<and> artifact_value_presents R q"
      using scope checks by (simp only: recorded_base_checked_judgment[OF context_value]; blast)
  next
    assume "\<exists>j R. generation_recorded_scope z j \<and> judgment_required_environment j=fst j \<and>
      base_admission_context j R \<and> artifact_value_presents R q"
    then obtain j R where scope: "generation_recorded_scope z j" and fixed: "judgment_required_environment j=fst j"
      and base: "base_admission_context j R" and expected: "artifact_value_presents R q" by blast
    obtain v where context_value: "judgment_context_presents j v"
      using judgments.total[OF generation_recorded_scope_formed[OF scope]] by blast
    have read: "(162,Pair_Term p v)\<in>positive_meaning generation_scope_system"
      by (simp only: generation_recorded_scope_relation.at[OF source context_value]; rule scope)
    have checks: "(183,v)\<in>positive_meaning judgment_retention_system \<and>
        (185,Pair_Term v q)\<in>positive_meaning base_cause_system"
      by (simp only: recorded_base_checked_judgment[OF context_value]) (use fixed base expected in blast)
    show "\<exists>v. (162,Pair_Term p v)\<in>positive_meaning generation_scope_system \<and>
        (183,v)\<in>positive_meaning judgment_retention_system \<and>
        (185,Pair_Term v q)\<in>positive_meaning base_cause_system" using read checks by blast
  qed
  have raw: "(187,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
      (\<exists>a b c. (151,Pair_Term p (generation_fields_term a b (Pair_Term q (Payload_Term [])) c))\<in>positive_meaning generation_source_system) \<and>
      (\<exists>v. (162,Pair_Term p v)\<in>positive_meaning generation_scope_system \<and>
        (183,v)\<in>positive_meaning judgment_retention_system \<and>
        (185,Pair_Term v q)\<in>positive_meaning base_cause_system)"
    by (simp only: recorded_base_report_calls factor_term.inject; blast)
  show ?thesis by (simp only: raw payload declared recorded_base_context_join)
    (use artifact_value_presents_unique in blast)
qed

theorem recorded_base_report_exact:
  "(187,t)\<in>positive_meaning base_cause_system \<longleftrightarrow> (\<exists>z. recorded_base_report_presents z t)"
proof
  assume holds: "(187,t)\<in>positive_meaning base_cause_system"
  obtain p q a b c where shape: "t=Pair_Term p q"
    and reading: "(151,Pair_Term p (generation_fields_term a b (Pair_Term q (Payload_Term [])) c))\<in>positive_meaning generation_source_system"
    using holds by (simp only: recorded_base_report_calls; blast)
  obtain z where source: "generation_source_presents z p" using generation_scope_source_recovery[OF reading] by blast
  obtain R where admitted: "recorded_base_context z R" and expected: "artifact_value_presents R q"
    using holds by (simp only: shape recorded_base_report_at_source[OF source]; blast)
  show "\<exists>z. recorded_base_report_presents z t" by (rule exI[of _ "(z,R)"])
    (use source admitted expected shape in \<open>auto simp: recorded_base_report_presents_def factor_pair_presents_def\<close>)
next
  assume "\<exists>z. recorded_base_report_presents z t"
  then obtain z R p q where source: "generation_source_presents z p" and expected: "artifact_value_presents R q"
    and admitted: "recorded_base_context z R" and shape: "t=Pair_Term p q"
    by (auto simp: recorded_base_report_presents_def factor_pair_presents_def)
  show "(187,t)\<in>positive_meaning base_cause_system"
    by (simp only: shape recorded_base_report_at_source[OF source]) (use admitted expected in blast)
qed

interpretation recorded_base_projection: reader_projection_profile base_cause_system 188 187 0 1 0 0
  by (unfold_locales) (auto simp: base_cause_call)

theorem recorded_base_source_exact:
  "(188,p)\<in>positive_meaning base_cause_system \<longleftrightarrow> (\<exists>z. recorded_base_source_presents z p)"
proof -
  have total: "\<exists>q. artifact_value_presents R q" if "recorded_base_context z R" for z R
    using artifact_value_presents_total[OF recorded_base_context_formed[OF that]] by blast
  show ?thesis by (simp only: recorded_base_projection.exact recorded_base_report_exact)
    (use total in \<open>auto simp: recorded_base_report_presents_def recorded_base_source_presents_def
      factor_pair_presents_def; metis fst_conv snd_conv\<close>)
qed

text \<open>
  Generation reading supplies the actual payload field. The scope contract
  supplies the context in the actual whole cause artifact. The same context
  must satisfy least retention and the base declaration contract, whose exact
  artifact must equal the actual payload. Arbitrary compatible presentations
  remain permitted, and the all-term theorem excludes extra input shapes.
\<close>

end
