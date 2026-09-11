theory Factor_Generation_Scope_Admission
  imports Factor_Generation_Scope_Clauses Factor_Generation_Scope_Presentations
    Factor_Generation_Program_Presentations
begin

section \<open>Ordinary valuations preserve every actual premise\<close>

lemma generation_recorded_report_valuation:
  "(162,z)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>a\<in>{0,1,2,3,4,5}. term_formed (h a)) \<and>
      z=Pair_Term (h 0) (h 1) \<and>
      (151,Pair_Term (h 0) (generation_fields_term (h 2) (h 3) (h 4) (Pair_Term (h 5) (Payload_Term []))))
        \<in>positive_meaning generation_scope_system \<and>
      (160,Pair_Term (h 5) (h 1))\<in>positive_meaning generation_scope_system)"
proof -
  have family: "((162,c),S)\<in>system_clauses generation_scope_system \<longleftrightarrow>
      c=0 \<and> S=generation_recorded_scope_report_schema" for c S by auto
  have ordinary: "schema_material_premises generation_recorded_scope_report_schema={}"
    by (simp add: generation_recorded_scope_report_schema_def)
  have accepts: "schema_call_formed generation_scope_system 162
      (evaluate_pattern h (schema_conclusion generation_recorded_scope_report_schema))"
    if "\<forall>a\<in>schema_variables generation_recorded_scope_report_schema. term_formed (h a)" for h
    using that by (auto simp: generation_scope_call generation_recorded_scope_report_schema_def schema_variables_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF family ordinary])
     apply (fact accepts)
    apply (rule ex_cong1)
    apply (simp add: generation_recorded_scope_report_schema_def schema_variables_def
      conj_ac all_conj_distrib imp_conjL)
    done
qed

lemma generation_payload_report_valuation:
  "(167,z)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>a\<in>{0,1,2,3,4,5}. term_formed (h a)) \<and>
      z=Pair_Term (h 0) (h 1) \<and>
      (151,Pair_Term (h 0) (generation_fields_term (h 2) (h 3) (Pair_Term (h 4) (Payload_Term [])) (h 5)))
        \<in>positive_meaning generation_scope_system \<and>
      (165,Pair_Term (h 4) (h 1))\<in>positive_meaning generation_scope_system)"
proof -
  have family: "((167,c),S)\<in>system_clauses generation_scope_system \<longleftrightarrow>
      c=0 \<and> S=generation_payload_scope_report_schema" for c S by auto
  have ordinary: "schema_material_premises generation_payload_scope_report_schema={}"
    by (simp add: generation_payload_scope_report_schema_def)
  have accepts: "schema_call_formed generation_scope_system 167
      (evaluate_pattern h (schema_conclusion generation_payload_scope_report_schema))"
    if "\<forall>a\<in>schema_variables generation_payload_scope_report_schema. term_formed (h a)" for h
    using that by (auto simp: generation_scope_call generation_payload_scope_report_schema_def schema_variables_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF family ordinary])
     apply (fact accepts)
    apply (rule ex_cong1)
    apply (simp add: generation_payload_scope_report_schema_def schema_variables_def
      conj_ac all_conj_distrib imp_conjL)
    done
qed

lemma generation_recorded_report_calls:
  "(162,z)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (\<exists>p q a b c d. z=Pair_Term p q \<and>
      (151,Pair_Term p (generation_fields_term a b c (Pair_Term d (Payload_Term []))))
        \<in>positive_meaning generation_source_system \<and>
      (160,Pair_Term d q)\<in>positive_meaning judgment_scope_reading_system)"
proof
  assume "(162,z)\<in>positive_meaning generation_scope_system"
  then show "\<exists>p q a b c d. z=Pair_Term p q \<and>
      (151,Pair_Term p (generation_fields_term a b c (Pair_Term d (Payload_Term []))))
        \<in>positive_meaning generation_source_system \<and>
      (160,Pair_Term d q)\<in>positive_meaning judgment_scope_reading_system"
    by (simp only: generation_recorded_report_valuation generation_scope_components) blast
next
  assume "\<exists>p q a b c d. z=Pair_Term p q \<and>
      (151,Pair_Term p (generation_fields_term a b c (Pair_Term d (Payload_Term []))))
        \<in>positive_meaning generation_source_system \<and>
      (160,Pair_Term d q)\<in>positive_meaning judgment_scope_reading_system"
  then obtain p q a b c d where shape: "z=Pair_Term p q"
    and source: "(151,Pair_Term p (generation_fields_term a b c (Pair_Term d (Payload_Term []))))
      \<in>positive_meaning generation_source_system"
    and scope: "(160,Pair_Term d q)\<in>positive_meaning judgment_scope_reading_system" by blast
  have formed: "term_formed p" "term_formed q" "term_formed a" "term_formed b" "term_formed c" "term_formed d"
    using schema_call_formed_target[OF positive_meaning_formed[OF source]]
      schema_call_formed_target[OF positive_meaning_formed[OF scope]] by auto
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then q else if i=2 then a else if i=3 then b else if i=4 then c else d"
  show "(162,z)\<in>positive_meaning generation_scope_system"
    by (simp only: generation_recorded_report_valuation generation_scope_components; rule exI[of _ ?h])
      (use shape source scope formed in auto)
qed

lemma generation_payload_report_calls:
  "(167,z)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (\<exists>p q a b c d. z=Pair_Term p q \<and>
      (151,Pair_Term p (generation_fields_term a b (Pair_Term c (Payload_Term [])) d))
        \<in>positive_meaning generation_source_system \<and>
      (165,Pair_Term c q)\<in>positive_meaning program_scope_reports_system)"
proof
  assume "(167,z)\<in>positive_meaning generation_scope_system"
  then show "\<exists>p q a b c d. z=Pair_Term p q \<and>
      (151,Pair_Term p (generation_fields_term a b (Pair_Term c (Payload_Term [])) d))
        \<in>positive_meaning generation_source_system \<and>
      (165,Pair_Term c q)\<in>positive_meaning program_scope_reports_system"
    by (simp only: generation_payload_report_valuation generation_scope_components) blast
next
  assume "\<exists>p q a b c d. z=Pair_Term p q \<and>
      (151,Pair_Term p (generation_fields_term a b (Pair_Term c (Payload_Term [])) d))
        \<in>positive_meaning generation_source_system \<and>
      (165,Pair_Term c q)\<in>positive_meaning program_scope_reports_system"
  then obtain p q a b c d where shape: "z=Pair_Term p q"
    and source: "(151,Pair_Term p (generation_fields_term a b (Pair_Term c (Payload_Term [])) d))
      \<in>positive_meaning generation_source_system"
    and scope: "(165,Pair_Term c q)\<in>positive_meaning program_scope_reports_system" by blast
  have formed: "term_formed p" "term_formed q" "term_formed a" "term_formed b" "term_formed c" "term_formed d"
    using schema_call_formed_target[OF positive_meaning_formed[OF source]]
      schema_call_formed_target[OF positive_meaning_formed[OF scope]] by auto
  let ?h="\<lambda>i::nat. if i=0 then p else if i=1 then q else if i=2 then a else if i=3 then b else if i=4 then c else d"
  show "(167,z)\<in>positive_meaning generation_scope_system"
    by (simp only: generation_payload_report_valuation generation_scope_components; rule exI[of _ ?h])
      (use shape source scope formed in auto)
qed

section \<open>The generation owner's value contract determines its selected artifact\<close>

lemma generation_scope_value_fields:
  "generation_value_presents G (generation_fields_term a b c d) \<longleftrightarrow>
    target_value_presents (generation_locus G) a \<and>
    data_collection_presents generation_value_presents (fset (generation_predecessors G)) b \<and>
    target_value_presents (generation_payload G) c \<and> target_value_presents (generation_cause G) d"
  by (cases G) (auto simp: generation_value_presents_cases)

lemma generation_value_cause_artifact:
  assumes formed: "generation_formed G"
  shows "(\<exists>a b c. generation_value_presents G
      (generation_fields_term a b c (Pair_Term d (Payload_Term [])))) \<longleftrightarrow>
    (\<exists>C. generation_cause G=Whole_Artifact C \<and> artifact_value_presents C d)"
proof
  assume "\<exists>a b c. generation_value_presents G (generation_fields_term a b c (Pair_Term d (Payload_Term [])))"
  then have present: "target_value_presents (generation_cause G) (Pair_Term d (Payload_Term []))"
    by (simp only: generation_scope_value_fields) blast
  show "\<exists>C. generation_cause G=Whole_Artifact C \<and> artifact_value_presents C d"
    using present by (cases "generation_cause G") (auto simp: target_value_whole target_value_occurrence)
next
  assume "\<exists>C. generation_cause G=Whole_Artifact C \<and> artifact_value_presents C d"
  then have present: "target_value_presents (generation_cause G) (Pair_Term d (Payload_Term []))"
    by (auto simp: target_value_whole)
  obtain a b c e where old: "generation_value_presents G (generation_fields_term a b c e)"
    using generation_value_presents_total[OF formed] by (cases G) (auto simp: generation_value_presents_cases)
  show "\<exists>a b c. generation_value_presents G (generation_fields_term a b c (Pair_Term d (Payload_Term [])))"
    using old present by (simp only: generation_scope_value_fields) blast
qed

lemma generation_value_payload_artifact:
  assumes formed: "generation_formed G"
  shows "(\<exists>a b d. generation_value_presents G
      (generation_fields_term a b (Pair_Term c (Payload_Term [])) d)) \<longleftrightarrow>
    (\<exists>C. generation_payload G=Whole_Artifact C \<and> artifact_value_presents C c)"
proof
  assume "\<exists>a b d. generation_value_presents G (generation_fields_term a b (Pair_Term c (Payload_Term [])) d)"
  then have present: "target_value_presents (generation_payload G) (Pair_Term c (Payload_Term []))"
    by (simp only: generation_scope_value_fields) blast
  show "\<exists>C. generation_payload G=Whole_Artifact C \<and> artifact_value_presents C c"
    using present by (cases "generation_payload G") (auto simp: target_value_whole target_value_occurrence)
next
  assume "\<exists>C. generation_payload G=Whole_Artifact C \<and> artifact_value_presents C c"
  then have present: "target_value_presents (generation_payload G) (Pair_Term c (Payload_Term []))"
    by (auto simp: target_value_whole)
  obtain a b e d where old: "generation_value_presents G (generation_fields_term a b e d)"
    using generation_value_presents_total[OF formed] by (cases G) (auto simp: generation_value_presents_cases)
  show "\<exists>a b d. generation_value_presents G (generation_fields_term a b (Pair_Term c (Payload_Term [])) d)"
    using old present by (simp only: generation_scope_value_fields) blast
qed

lemma generation_scope_source_value:
  assumes source: "generation_source_presents z p"
  shows "(151,Pair_Term p q)\<in>positive_meaning generation_source_system \<longleftrightarrow>
    generation_value_presents (snd z) q"
proof -
  have core: "generation_core_source_presents (snd z) p"
    unfolding generation_core_source_presents_def
    by (rule exI[of _ z]) (use source in simp)
  show ?thesis by (simp only: generation_source_conversion.output[OF core] id_apply)
qed

lemma generation_scope_source_recovery:
  assumes "(151,Pair_Term p q)\<in>positive_meaning generation_source_system"
  shows "\<exists>z. generation_source_presents z p \<and> generation_value_presents (snd z) q"
  using assms by (auto simp: generation_source_conversion_exact presentation_transport_def generation_core_source_presents_def)

lemma generation_recorded_scope_artifact:
  assumes actual: "generation_at_context (fst z) (snd z)"
  shows "generation_recorded_scope z j \<longleftrightarrow>
    (\<exists>C c. generation_cause (snd z)=Whole_Artifact C \<and> artifact_value_presents C c \<and>
      judgment_artifact_presents j c)"
proof
  assume "generation_recorded_scope z j"
  then obtain C r where cause: "generation_cause (snd z)=Whole_Artifact C"
    and quote: "judgment_quotation_presents j (C,r)"
    by (auto simp: generation_recorded_scope_def generation_judgment_scope_at_def)
  have cf: "exact_formed C" using judgment_value_quoted_formed[OF quote] by simp
  obtain c where material: "artifact_value_presents C c" using artifact_value_presents_total[OF cf] by blast
  have read: "judgment_artifact_presents j c"
    by (simp only: judgment_artifact_at_source[OF material]) (use quote in blast)
  show "\<exists>C c. generation_cause (snd z)=Whole_Artifact C \<and> artifact_value_presents C c \<and>
      judgment_artifact_presents j c" using cause material read by blast
next
  assume "\<exists>C c. generation_cause (snd z)=Whole_Artifact C \<and> artifact_value_presents C c \<and>
      judgment_artifact_presents j c"
  then obtain C c where cause: "generation_cause (snd z)=Whole_Artifact C"
    and material: "artifact_value_presents C c" and read: "judgment_artifact_presents j c" by blast
  obtain r where quote: "judgment_quotation_presents j (C,r)"
    using read by (simp only: judgment_artifact_at_source[OF material]) blast
  show "generation_recorded_scope z j" using actual cause quote
    by (auto simp: generation_recorded_scope_def generation_judgment_scope_at_def)
qed

lemma generation_payload_scope_artifact:
  assumes actual: "generation_at_context (fst z) (snd z)"
  shows "generation_payload_scope z k \<longleftrightarrow>
    (\<exists>C c. generation_payload (snd z)=Whole_Artifact C \<and> artifact_value_presents C c \<and>
      program_artifact_presents k c)"
proof -
  obtain E u r P where coordinates: "k=((E,(u,r)),P)" by (cases k; auto)
  have formed: "generation_formed (snd z)" by (rule generation_at_formed[OF actual])
  show ?thesis
  proof
    assume "generation_payload_scope z k"
    then obtain C q where payload: "generation_payload (snd z)=Whole_Artifact C"
      and quote: "program_scope_quoted_at C q E u r P"
      by (auto simp: generation_payload_scope_def generation_program_scope_def coordinates)
    have cf: "exact_formed C" using program_scope_quoted_formed[OF quote] by blast
    obtain c where material: "artifact_value_presents C c" using artifact_value_presents_total[OF cf] by blast
    have read: "program_artifact_presents k c"
      by (simp only: coordinates program_artifact_at_source[OF material]) (use quote in blast)
    show "\<exists>C c. generation_payload (snd z)=Whole_Artifact C \<and> artifact_value_presents C c \<and>
        program_artifact_presents k c" using payload material read by blast
  next
    assume "\<exists>C c. generation_payload (snd z)=Whole_Artifact C \<and> artifact_value_presents C c \<and>
        program_artifact_presents k c"
    then obtain C c where payload: "generation_payload (snd z)=Whole_Artifact C"
      and material: "artifact_value_presents C c" and read: "program_artifact_presents k c" by blast
    obtain q where quote: "program_scope_quoted_at C q E u r P"
      using read by (simp only: coordinates program_artifact_at_source[OF material]) blast
    show "generation_payload_scope z k" using actual formed payload quote
      by (auto simp: coordinates generation_payload_scope_def generation_program_scope_def)
  qed
qed

section \<open>Every report is exactly the independently specified linked class\<close>

theorem generation_recorded_report_at_source:
  assumes source: "generation_source_presents z p"
  shows "(162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (\<exists>j. generation_recorded_scope z j \<and> judgment_context_presents j q)"
proof -
  have actual: "generation_at_context (fst z) (snd z)" by (rule generation_sources.subject_boundary[OF source])
  have formed: "generation_formed (snd z)" by (rule generation_at_formed[OF actual])
  have raw: "(162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
      (\<exists>d. (\<exists>a b c. generation_value_presents (snd z)
        (generation_fields_term a b c (Pair_Term d (Payload_Term [])))) \<and>
        (160,Pair_Term d q)\<in>positive_meaning judgment_scope_reading_system)"
  proof -
    have pairs: "(162,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
        (\<exists>a b c d. (151,Pair_Term p (generation_fields_term a b c (Pair_Term d (Payload_Term []))))\<in>positive_meaning generation_source_system \<and>
          (160,Pair_Term d q)\<in>positive_meaning judgment_scope_reading_system)"
      by (auto simp: generation_recorded_report_calls)
    show ?thesis by (simp only: pairs generation_scope_source_value[OF source]; blast)
  qed
  show ?thesis by (simp only: raw generation_value_cause_artifact[OF formed]
    judgment_scope_report_transport presentation_transport_def generation_recorded_scope_artifact[OF actual]) blast
qed

theorem generation_payload_report_at_source:
  assumes source: "generation_source_presents z p"
  shows "(167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (\<exists>k. generation_payload_scope z k \<and> program_scope_value_presents k q)"
proof -
  have actual: "generation_at_context (fst z) (snd z)" by (rule generation_sources.subject_boundary[OF source])
  have formed: "generation_formed (snd z)" by (rule generation_at_formed[OF actual])
  have raw: "(167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
      (\<exists>c. (\<exists>a b d. generation_value_presents (snd z)
        (generation_fields_term a b (Pair_Term c (Payload_Term [])) d)) \<and>
        (165,Pair_Term c q)\<in>positive_meaning program_scope_reports_system)"
  proof -
    have pairs: "(167,Pair_Term p q)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
        (\<exists>a b c d. (151,Pair_Term p (generation_fields_term a b (Pair_Term c (Payload_Term [])) d))\<in>positive_meaning generation_source_system \<and>
          (165,Pair_Term c q)\<in>positive_meaning program_scope_reports_system)"
      by (auto simp: generation_payload_report_calls)
    show ?thesis by (simp only: pairs generation_scope_source_value[OF source]; blast)
  qed
  show ?thesis by (simp only: raw generation_value_payload_artifact[OF formed]
    program_scope_report_transport presentation_transport_def generation_payload_scope_artifact[OF actual]) blast
qed

theorem generation_recorded_report_exact:
  "(162,t)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (\<exists>z. generation_scope_report_presents z t)"
proof
  assume native: "(162,t)\<in>positive_meaning generation_scope_system"
  obtain p q a b c d where shape: "t=Pair_Term p q"
    and read: "(151,Pair_Term p (generation_fields_term a b c (Pair_Term d (Payload_Term []))))
      \<in>positive_meaning generation_source_system"
    using native by (simp only: generation_recorded_report_calls) blast
  obtain z where source: "generation_source_presents z p" using generation_scope_source_recovery[OF read] by blast
  obtain j where scope: "generation_recorded_scope z j" and expected: "judgment_context_presents j q"
    using native shape by (simp only: generation_recorded_report_at_source[OF source]) blast
  show "\<exists>z. generation_scope_report_presents z t"
    by (rule exI[of _ "(z,j)"])
      (use scope source expected shape in \<open>simp add: generation_scope_report_presents_def\<close>)
next
  assume "\<exists>z. generation_scope_report_presents z t"
  then obtain z j p q where shape: "t=Pair_Term p q" and source: "generation_source_presents z p"
    and expected: "judgment_context_presents j q" and scope: "generation_recorded_scope z j"
    by (auto simp: generation_scope_report_presents_def factor_pair_presents_def)
  show "(162,t)\<in>positive_meaning generation_scope_system"
    by (simp only: shape generation_recorded_report_at_source[OF source]) (use scope expected in blast)
qed

theorem generation_payload_report_exact:
  "(167,t)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (\<exists>z. generation_payload_report_presents z t)"
proof
  assume native: "(167,t)\<in>positive_meaning generation_scope_system"
  obtain p q a b c d where shape: "t=Pair_Term p q"
    and read: "(151,Pair_Term p (generation_fields_term a b (Pair_Term c (Payload_Term [])) d))
      \<in>positive_meaning generation_source_system"
    using native by (simp only: generation_payload_report_calls) blast
  obtain z where source: "generation_source_presents z p" using generation_scope_source_recovery[OF read] by blast
  obtain k where scope: "generation_payload_scope z k" and expected: "program_scope_value_presents k q"
    using native shape by (simp only: generation_payload_report_at_source[OF source]) blast
  show "\<exists>z. generation_payload_report_presents z t"
    by (rule exI[of _ "(z,k)"])
      (use scope source expected shape in \<open>simp add: generation_payload_report_presents_def\<close>)
next
  assume "\<exists>z. generation_payload_report_presents z t"
  then obtain z k p q where shape: "t=Pair_Term p q" and source: "generation_source_presents z p"
    and expected: "program_scope_value_presents k q" and scope: "generation_payload_scope z k"
    by (auto simp: generation_payload_report_presents_def factor_pair_presents_def)
  show "(167,t)\<in>positive_meaning generation_scope_system"
    by (simp only: shape generation_payload_report_at_source[OF source]) (use scope expected in blast)
qed

interpretation generation_recorded_projection: reader_projection_profile generation_scope_system 163 162 0 1 0 0
  by (unfold_locales) (auto simp: generation_scope_call)

interpretation generation_payload_projection: reader_projection_profile generation_scope_system 168 167 0 1 0 0
  by (unfold_locales) (auto simp: generation_scope_call)

theorem generation_recorded_source_exact:
  "(163,p)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (\<exists>z. generation_recorded_scope_presents z p)"
proof -
  have complete: "(\<exists>q z. generation_scope_report_presents z (Pair_Term p q)) \<longleftrightarrow>
      (\<exists>z. generation_recorded_scope_presents z p)"
    using judgments.total generation_recorded_scope_formed
    by (auto simp: generation_scope_report_presents_def generation_recorded_scope_presents_def
      factor_pair_presents_def; metis fst_conv snd_conv)
  show ?thesis by (simp only: generation_recorded_projection.exact generation_recorded_report_exact complete)
qed

theorem generation_payload_source_exact:
  "(168,p)\<in>positive_meaning generation_scope_system \<longleftrightarrow>
    (\<exists>z. generation_payload_scope_presents z p)"
proof -
  have complete: "(\<exists>q z. generation_payload_report_presents z (Pair_Term p q)) \<longleftrightarrow>
      (\<exists>z. generation_payload_scope_presents z p)"
    using program_scope_identity.left.total generation_payload_scope_subject
    by (auto simp: generation_payload_report_presents_def generation_payload_scope_presents_def
      factor_pair_presents_def; metis fst_conv snd_conv)
  show ?thesis by (simp only: generation_payload_projection.exact generation_payload_report_exact complete)
qed

text \<open>
  The complete source conversion supplies the actual core through its owned
  function contract. Its existing field presentations then determine the
  selected whole artifact. Each local scope reader supplies canonical
  correspondence from that artifact to every compatible expected context.

  The resulting all-term theorems are exactly the previously specified
  recorded-scope classes and the independently linked payload-scope classes.
  Source-only admission is their ordinary projection. The proofs retain all
  actual source, quotation, and field constraints while imposing no cause
  validity or report equality with the stored body.
\<close>

end
