theory Factor_Construction_Cause_Admission
  imports Factor_Construction_Cause_Clauses Factor_Construction_Cause_Readings
begin

context related_test_admission
begin

section \<open>The complete ordinary clauses realize both independently specified joins\<close>

lemma construction_profile_native_valuation:
  "(265,z)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9}. term_formed (h i)) \<and>
      z=Pair_Term (judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4)) (h 5) \<and>
      (115,judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4))\<in>positive_meaning native_positive_admission_system \<and>
      (58,application_reading_argument (h 0) (h 3) (h 4) (h 6) (h 7) (h 8) (h 9))\<in>positive_meaning application_reading_system \<and>
      (264,related_test_admission_argument (h 0) (h 1) (h 2) (h 6))\<in>positive_meaning (related_test_admission_system c k) \<and>
      (261,Pair_Term (h 7) (h 5))\<in>positive_meaning construction_comparison_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: construction_profile_report_schema_def schema_variables_def construction_cause_call construction_cause_components)

theorem construction_profile_native_join:
  "(265,z)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow>
    (\<exists>p q. z=Pair_Term p q \<and> construction_profile_reading c k p q)"
proof
  assume "(265,z)\<in>positive_meaning (construction_cause_system c k)"
  then show "\<exists>p q. z=Pair_Term p q \<and> construction_profile_reading c k p q"
    by (simp only: construction_profile_native_valuation construction_profile_reading_def; blast)
next
  assume "\<exists>p q. z=Pair_Term p q \<and> construction_profile_reading c k p q"
  then obtain e pu pr au ar q d t i s where shape: "z=Pair_Term (judgment_context_term e pu pr au ar) q"
    and calls: "(115,judgment_context_term e pu pr au ar)\<in>positive_meaning native_positive_admission_system"
    "(58,application_reading_argument e au ar d t i s)\<in>positive_meaning application_reading_system"
    "(264,related_test_admission_argument e pu pr d)\<in>positive_meaning (related_test_admission_system c k)"
    "(261,Pair_Term t q)\<in>positive_meaning construction_comparison_system"
    by (auto simp: construction_profile_reading_def)
  have fields: "term_formed e" "term_formed pu" "term_formed pr" "term_formed au" "term_formed ar"
    "term_formed q" "term_formed d" "term_formed t" "term_formed i" "term_formed s"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(4)]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then pu else if n=2 then pr else if n=3 then au
    else if n=4 then ar else if n=5 then q else if n=6 then d else if n=7 then t else if n=8 then i else s"
  show "(265,z)\<in>positive_meaning (construction_cause_system c k)"
    by (simp only: construction_profile_native_valuation; rule exI[of _ ?h]) (use shape calls fields in auto)
qed

lemma construction_profile_native_at:
  "(265,Pair_Term p q)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow>
    construction_profile_reading c k p q"
  by (simp only: construction_profile_native_join factor_term.inject; blast)

lemma recorded_construction_native_valuation:
  "(267,z)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9,10}. term_formed (h i)) \<and>
      z=Pair_Term (h 0) (enumeration_term [h 1,h 2,h 3,h 4,h 5]) \<and>
      (151,Pair_Term (h 0) (generation_fields_term (h 6) (h 7) (Pair_Term (h 8) (Payload_Term [])) (h 9)))
        \<in>positive_meaning generation_source_system \<and>
      (162,Pair_Term (h 0) (h 10))\<in>positive_meaning generation_scope_system \<and>
      (183,h 10)\<in>positive_meaning judgment_retention_system \<and>
      (265,Pair_Term (h 10) (enumeration_term [h 1,h 2,h 3,h 4,h 5]))\<in>positive_meaning (construction_cause_system c k) \<and>
      (10,Pair_Term (h 5) (h 8))\<in>positive_meaning artifact_projection_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: recorded_construction_report_schema_def schema_variables_def construction_cause_call
      construction_cause_components)

theorem recorded_construction_native_join:
  "(267,z)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow>
    (\<exists>p q. z=Pair_Term p q \<and> recorded_construction_reading c k p q)"
proof
  assume "(267,z)\<in>positive_meaning (construction_cause_system c k)"
  then show "\<exists>p q. z=Pair_Term p q \<and> recorded_construction_reading c k p q"
    by (simp only: recorded_construction_native_valuation construction_profile_native_at recorded_construction_reading_def; blast)
next
  assume "\<exists>p q. z=Pair_Term p q \<and> recorded_construction_reading c k p q"
  then obtain p x b s orig out l ps pay cause j where shape: "z=Pair_Term p (enumeration_term [x,b,s,orig,out])"
    and calls: "(151,Pair_Term p (generation_fields_term l ps (Pair_Term pay (Payload_Term [])) cause))
      \<in>positive_meaning generation_source_system"
    "(162,Pair_Term p j)\<in>positive_meaning generation_scope_system"
    "(183,j)\<in>positive_meaning judgment_retention_system"
    "construction_profile_reading c k j (enumeration_term [x,b,s,orig,out])"
    "(10,Pair_Term out pay)\<in>positive_meaning artifact_projection_system"
    by (auto simp: recorded_construction_reading_def)
  have profile: "(265,Pair_Term j (enumeration_term [x,b,s,orig,out]))\<in>positive_meaning (construction_cause_system c k)"
    by (simp only: construction_profile_native_at; rule calls(4))
  have fields: "term_formed p" "term_formed x" "term_formed b" "term_formed s" "term_formed orig"
    "term_formed out" "term_formed l" "term_formed ps" "term_formed pay" "term_formed cause" "term_formed j"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF profile]] by (auto simp: enumeration_term_formed)
  let ?h="\<lambda>n::nat. if n=0 then p else if n=1 then x else if n=2 then b else if n=3 then s
    else if n=4 then orig else if n=5 then out else if n=6 then l else if n=7 then ps
    else if n=8 then pay else if n=9 then cause else j"
  show "(267,z)\<in>positive_meaning (construction_cause_system c k)"
    by (simp only: recorded_construction_native_valuation; rule exI[of _ ?h]) (use shape calls profile fields in auto)
qed

lemma recorded_construction_native_at:
  "(267,Pair_Term p q)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow>
    recorded_construction_reading c k p q"
  by (simp only: recorded_construction_native_join factor_term.inject; blast)

interpretation construction_profile_projection: reader_projection_profile "construction_cause_system c k" 266 265 0 1 0 0
  by (unfold_locales) (auto simp: construction_cause_call)

lemma construction_profile_native_source:
  "(266,p)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow>
    (\<exists>q. construction_profile_reading c k p q)"
  by (simp only: construction_profile_projection.exact construction_profile_native_at)

interpretation recorded_construction_projection: reader_projection_profile "construction_cause_system c k" 268 267 0 1 0 0
  by (unfold_locales) (auto simp: construction_cause_call)

lemma recorded_construction_native_source:
  "(268,p)\<in>positive_meaning (construction_cause_system c k) \<longleftrightarrow>
    (\<exists>q. recorded_construction_reading c k p q)"
  by (simp only: recorded_construction_projection.exact recorded_construction_native_at)

end

text \<open>
  Each admission equation is derived from all valuations of its actual
  singleton clause family. Every variable's formation follows from successful
  ordinary callees. This includes the generation's auxiliary fields and every
  account field. Both directions then identify the already specified reader
  joins, on all terms, before any presentation class or compilation is used.
\<close>

end
