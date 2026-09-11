theory Factor_Base_Admission
  imports Factor_Base_Cause_Clauses
begin

section \<open>The native clause reads truth and the actual whole-artifact literal\<close>

lemma base_admission_report_valuation:
  "(185,z)\<in>positive_meaning base_cause_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8,9}. term_formed (h i)) \<and>
      z=Pair_Term (judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4)) (h 5) \<and>
      (115,judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4))\<in>positive_meaning native_positive_admission_system \<and>
      (58,application_reading_argument (h 0) (h 3) (h 4) (h 6) (h 7) (h 8) (h 9))\<in>positive_meaning application_reading_system \<and>
      (10,Pair_Term (h 7) (h 5))\<in>positive_meaning artifact_projection_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: base_admission_report_schema_def schema_variables_def base_cause_call base_cause_components)

lemma base_admission_report_calls:
  "(185,z)\<in>positive_meaning base_cause_system \<longleftrightarrow>
    (\<exists>e pu pr au ar q d t i k. z=Pair_Term (judgment_context_term e pu pr au ar) q \<and>
      (115,judgment_context_term e pu pr au ar)\<in>positive_meaning native_positive_admission_system \<and>
      (58,application_reading_argument e au ar d t i k)\<in>positive_meaning application_reading_system \<and>
      (10,Pair_Term t q)\<in>positive_meaning artifact_projection_system)"
proof
  assume "(185,z)\<in>positive_meaning base_cause_system"
  then show "\<exists>e pu pr au ar q d t i k. z=Pair_Term (judgment_context_term e pu pr au ar) q \<and>
      (115,judgment_context_term e pu pr au ar)\<in>positive_meaning native_positive_admission_system \<and>
      (58,application_reading_argument e au ar d t i k)\<in>positive_meaning application_reading_system \<and>
      (10,Pair_Term t q)\<in>positive_meaning artifact_projection_system"
    by (simp only: base_admission_report_valuation; blast)
next
  assume "\<exists>e pu pr au ar q d t i k. z=Pair_Term (judgment_context_term e pu pr au ar) q \<and>
      (115,judgment_context_term e pu pr au ar)\<in>positive_meaning native_positive_admission_system \<and>
      (58,application_reading_argument e au ar d t i k)\<in>positive_meaning application_reading_system \<and>
      (10,Pair_Term t q)\<in>positive_meaning artifact_projection_system"
  then obtain e pu pr au ar q d t i k where shape: "z=Pair_Term (judgment_context_term e pu pr au ar) q"
    and calls: "(115,judgment_context_term e pu pr au ar)\<in>positive_meaning native_positive_admission_system"
    "(58,application_reading_argument e au ar d t i k)\<in>positive_meaning application_reading_system"
    "(10,Pair_Term t q)\<in>positive_meaning artifact_projection_system" by blast
  have formed: "term_formed e" "term_formed pu" "term_formed pr" "term_formed au" "term_formed ar"
    "term_formed q" "term_formed d" "term_formed t" "term_formed i" "term_formed k"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(3)]] by auto
  let ?h="\<lambda>n::nat. if n=0 then e else if n=1 then pu else if n=2 then pr else if n=3 then au
    else if n=4 then ar else if n=5 then q else if n=6 then d else if n=7 then t else if n=8 then i else k"
  show "(185,z)\<in>positive_meaning base_cause_system"
    by (simp only: base_admission_report_valuation; rule exI[of _ ?h]) (use shape calls formed in auto)
qed

lemma base_admission_actual_operand:
  assumes source: "environment_value_presents E e" and app: "native_application_at E au ar d t I K"
  shows "(\<exists>a i k. (58,application_reading_argument e (use_data_term au) (Payload_Term ar) a v i k)
      \<in>positive_meaning application_reading_system) \<longleftrightarrow> v=t"
proof
  assume "\<exists>a i k. (58,application_reading_argument e (use_data_term au) (Payload_Term ar) a v i k)
    \<in>positive_meaning application_reading_system"
  then obtain du da Is Ks where actual: "native_application_at E au ar (du,da) v (set Is) (set Ks)"
    by (simp only: application_reading_at_source[OF source] inj_eq[OF use_data_term_injective] factor_term.inject; blast)
  show "v=t" using native_application_unique[OF actual app] by blast
next
  assume "v=t"
  then show "\<exists>a i k. (58,application_reading_argument e (use_data_term au) (Payload_Term ar) a v i k)
      \<in>positive_meaning application_reading_system"
    using application_reading_value[OF source app] by blast
qed

lemma base_admission_report_with_reads:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and app: "native_application_at E au ar d t I K"
  shows "(185,Pair_Term
      (judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)) q)
      \<in>positive_meaning base_cause_system \<longleftrightarrow>
    (\<exists>R. base_admission_judgment_at E pu pr au ar R \<and> artifact_value_presents R q)"
proof -
  let ?p="judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)"
  have sites: "(pu,pr)\<in>environment_positions E" "(au,ar)\<in>environment_positions E"
    by (rule native_judgment_positions[OF package app])+
  have present: "judgment_value_presents E pu pr au ar ?p"
    using source sites by (auto simp: judgment_value_presents_def site_data_term_def)
  have raw: "(185,Pair_Term ?p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
      (115,?p)\<in>positive_meaning native_positive_admission_system \<and>
      (\<exists>v. (\<exists>a i k. (58,application_reading_argument e (use_data_term au) (Payload_Term ar) a v i k)
        \<in>positive_meaning application_reading_system) \<and>
        (10,Pair_Term v q)\<in>positive_meaning artifact_projection_system)"
    by (simp only: base_admission_report_calls factor_term.inject; blast)
  show ?thesis by (simp only: raw native_positive_admission_on_values[OF present]
    native_positive_holds_with_reads[OF package app] base_admission_actual_operand[OF source app]
    base_admission_with_reads[OF package app] artifact_projection_exact factor_term.inject) blast
qed

theorem base_admission_report_at_source:
  assumes source: "judgment_source_presents z p"
  shows "(185,Pair_Term p q)\<in>positive_meaning base_cause_system \<longleftrightarrow>
    (\<exists>R. base_admission_context z R \<and> artifact_value_presents R q)"
proof -
  obtain E pu pr au ar where coordinates: "z=(E,((pu,pr),(au,ar)))" by (cases z; auto)
  obtain e P d t I K where encoded: "environment_value_presents E e"
    and shape: "p=judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)"
    and package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    using source by (simp only: coordinates judgment_source_presentation_fields; blast)
  show ?thesis by (simp only: shape base_admission_report_with_reads[OF encoded package app] coordinates fst_conv snd_conv)
qed

lemma base_admission_positive_source:
  assumes "(115,p)\<in>positive_meaning native_positive_admission_system"
  shows "\<exists>z. judgment_source_presents z p"
proof -
  obtain E pu pr au ar where present: "judgment_value_presents E pu pr au ar p"
    and positive: "native_positive_holds E pu pr au ar"
    using assms by (simp only: native_positive_admission_exact; blast)
  have readable: "judgment_source_readable (E,((pu,pr),(au,ar)))"
    using positive by (simp only: native_positive_holds_def fst_conv snd_conv; blast)
  show ?thesis by (rule exI[of _ "(E,((pu,pr),(au,ar)))"])
    (use present readable in \<open>simp only: judgment_source_presents_def fst_conv snd_conv\<close>)
qed

theorem base_admission_report_exact:
  "(185,t)\<in>positive_meaning base_cause_system \<longleftrightarrow> (\<exists>z. base_admission_report_presents z t)"
proof
  assume holds: "(185,t)\<in>positive_meaning base_cause_system"
  obtain p q where shape: "t=Pair_Term p q"
    and positive: "(115,p)\<in>positive_meaning native_positive_admission_system"
    using holds by (simp only: base_admission_report_calls; blast)
  obtain z where source: "judgment_source_presents z p" using base_admission_positive_source[OF positive] by blast
  obtain R where admitted: "base_admission_context z R" and expected: "artifact_value_presents R q"
    using holds by (simp only: shape base_admission_report_at_source[OF source]; blast)
  show "\<exists>z. base_admission_report_presents z t" by (rule exI[of _ "(z,R)"])
    (use source admitted expected shape in \<open>auto simp: base_admission_report_presents_def factor_pair_presents_def\<close>)
next
  assume "\<exists>z. base_admission_report_presents z t"
  then obtain z R p q where source: "judgment_source_presents z p" and expected: "artifact_value_presents R q"
    and admitted: "base_admission_context z R" and shape: "t=Pair_Term p q"
    by (auto simp: base_admission_report_presents_def factor_pair_presents_def)
  show "(185,t)\<in>positive_meaning base_cause_system"
    by (simp only: shape base_admission_report_at_source[OF source]) (use admitted expected in blast)
qed

interpretation base_admission_projection: reader_projection_profile base_cause_system 186 185 0 1 0 0
  by (unfold_locales) (auto simp: base_cause_call)

theorem base_admission_source_exact:
  "(186,p)\<in>positive_meaning base_cause_system \<longleftrightarrow> (\<exists>z. base_admission_source_presents z p)"
proof -
  have total: "\<exists>q. artifact_value_presents R q" if "base_admission_context z R" for z R
    using artifact_value_presents_total[OF base_admission_context_formed[OF that]] by blast
  show ?thesis by (simp only: base_admission_projection.exact base_admission_report_exact)
    (use total in \<open>auto simp: base_admission_report_presents_def base_admission_source_presents_def
      factor_pair_presents_def; metis fst_conv snd_conv\<close>)
qed

text \<open>
  The supplied complete context fixes the actual package and application.
  Positive admission supplies their independently defined truth; literal
  projection recovers exactly the whole artifact in that application.
  The all-term result is precisely the source and report presentation class.
  Neither a false call nor a different operand shape acquires base force.
\<close>

end
