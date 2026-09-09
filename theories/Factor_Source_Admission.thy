theory Factor_Source_Admission
  imports Factor_Source_Presentations Factor_Source_Clauses
begin

section \<open>Existing material projection admits exactly whole-artifact literals\<close>

theorem source_literal_exact:
  "(237,p)\<in>positive_meaning source_system \<longleftrightarrow> (\<exists>R. artifact_literal_presents R p)"
  using artifact_presentations.total artifact_presentations.subject_boundary
  by (auto simp: source_literal.exact source_component_meanings(2) artifact_projection_exact; blast)

lemma artifact_literal_native_class:
  "presentation_class artifact_literal_presents exact_formed (\<lambda>p. (237,p)\<in>positive_meaning source_system)"
  using artifact_literal_presentation_class by (simp only: source_literal_exact)

lemma artifact_literal_data_presented:
  "(10,Pair_Term p q)\<in>positive_meaning source_system \<longleftrightarrow>
    presented_relation artifact_literal_presents artifact_value_presents (\<lambda>R S. S=id R) p q"
  using artifact_presentations.subject_boundary
  by (auto simp: source_component_meanings(2) artifact_projection_exact presented_relation_def)

interpretation artifact_literal_reading: presented_function_contract
  artifact_literal_presents exact_formed "\<lambda>p. (237,p)\<in>positive_meaning source_system"
  artifact_value_presents exact_formed "\<lambda>q. (11,q)\<in>positive_meaning artifact_admission_system" id
  "\<lambda>p q. (10,Pair_Term p q)\<in>positive_meaning source_system"
  using artifact_literal_native_class artifact_presentations.presentation_class_axioms artifact_literal_data_presented
  by (simp only: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def; simp)

section \<open>The list and table profiles lift those local element boundaries\<close>

lemma source_input_data_native_class:
  "presentation_class (data_sequence_presents artifact_literal_presents)
    (\<lambda>xs. \<forall>R\<in>set xs. exact_formed R) (\<lambda>p. (238,p)\<in>positive_meaning source_system)"
  by (rule source_input_list.presentation_class[OF artifact_literal_native_class])

lemma source_input_list_exact:
  "(238,p)\<in>positive_meaning source_system \<longleftrightarrow>
    (\<exists>xs. data_sequence_presents artifact_literal_presents xs p)"
  by (rule presentation_class.admissible_iff[OF source_input_data_native_class])

lemma source_base_row_valuation:
  "(239,t)\<in>positive_meaning source_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
      t=Pair_Term (h 0) (h 1) \<and>
      (1,data_list_term [h 0])\<in>positive_meaning source_system \<and>
      (237,h 1)\<in>positive_meaning source_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: source_system_clause source_clause_family_def source_base_row_schema_def schema_variables_def source_system_call)

lemma source_base_row_calls:
  "(239,t)\<in>positive_meaning source_system \<longleftrightarrow>
    (\<exists>k v. t=Pair_Term k v \<and> (1,data_list_term [k])\<in>positive_meaning source_system \<and>
      (237,v)\<in>positive_meaning source_system)"
proof
  assume "(239,t)\<in>positive_meaning source_system"
  then show "\<exists>k v. t=Pair_Term k v \<and> (1,data_list_term [k])\<in>positive_meaning source_system \<and>
      (237,v)\<in>positive_meaning source_system" by (simp only: source_base_row_valuation; blast)
next
  assume "\<exists>k v. t=Pair_Term k v \<and> (1,data_list_term [k])\<in>positive_meaning source_system \<and>
      (237,v)\<in>positive_meaning source_system"
  then obtain k v where shape: "t=Pair_Term k v"
    and support: "(1,data_list_term [k])\<in>positive_meaning source_system" "(237,v)\<in>positive_meaning source_system"
    by blast
  have formed: "term_formed k" "term_formed v"
    using schema_call_formed_target[OF positive_meaning_formed[OF support(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF support(2)]] by auto
  show "(239,t)\<in>positive_meaning source_system"
    by (simp only: source_base_row_valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then k else v"])
      (use shape support formed in auto)
qed

lemma source_base_row_exact:
  "(239,t)\<in>positive_meaning source_system \<longleftrightarrow>
    (\<exists>z. factor_pair_presents payload_value_presents artifact_literal_presents z t)"
  by (simp only: source_base_row_calls source_component_meanings(1) payload_value_recognition source_literal_exact)
    (auto simp: factor_pair_presents_def; metis fst_conv snd_conv)

lemma source_base_row_native_class:
  "presentation_class (factor_pair_presents payload_value_presents artifact_literal_presents)
    (\<lambda>z. octets_formed (fst z) \<and> exact_formed (snd z))
    (\<lambda>t. (239,t)\<in>positive_meaning source_system)"
proof -
  have pairs: "presentation_class (factor_pair_presents payload_value_presents artifact_literal_presents)
      (\<lambda>z. octets_formed (fst z) \<and> exact_formed (snd z))
      (\<lambda>t. \<exists>k v. (\<exists>b. payload_value_presents b k) \<and>
        (\<exists>R. artifact_literal_presents R v) \<and> t=Pair_Term k v)"
    by (rule factor_pair_class[OF payload_value_presentation_class artifact_literal_presentation_class])
  show ?thesis using pairs presentation_class.admissible_iff[OF pairs]
    by (simp only: source_base_row_exact presentation_class_def; blast)
qed

lemma source_base_rows_exact:
  "(240,t)\<in>positive_meaning source_system \<longleftrightarrow>
    (\<exists>xs. data_sequence_presents (factor_pair_presents payload_value_presents artifact_literal_presents) xs t)"
  by (rule presentation_class.admissible_iff[OF source_base_rows.presentation_class[OF source_base_row_native_class]])

lemma source_base_table_exact:
  "(241,t)\<in>positive_meaning source_system \<longleftrightarrow>
    (\<exists>B. data_table_presents payload_value_presents artifact_literal_presents B t)"
proof -
  have shape: "\<exists>v. p=Pair_Term (Payload_Term (fst z)) v"
    if "factor_pair_presents payload_value_presents artifact_literal_presents z p" for z p
    using that by (auto simp: factor_pair_presents_def)
  have boundary: "term_formed p \<and> self_contained_term (Payload_Term (fst z))"
    if "factor_pair_presents payload_value_presents artifact_literal_presents z p" for z p
    using that by (auto simp: factor_pair_presents_def)
  show ?thesis using source_base_table.presented_formed[OF payload_term_injective shape boundary
      source_component_meanings(3) source_base_rows_exact, of t]
    by (simp only: data_table_presents_def)
qed

lemma source_base_data_native_class:
  "presentation_class (data_table_presents payload_value_presents artifact_literal_presents)
    (finite_table_domain octets_formed exact_formed) (\<lambda>p. (241,p)\<in>positive_meaning source_system)"
  using data_table_presentation_class[OF payload_value_presentation_class artifact_literal_presentation_class]
  by (simp only: source_base_table_exact)

section \<open>Retermination preserves every actual complete source enumeration\<close>

lemma source_inputs_native_change:
  "source_inputs_presents xs q \<longleftrightarrow>
    (\<exists>p. data_sequence_presents artifact_literal_presents xs p \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p q)\<in>positive_meaning term_sequence_system)"
  by (auto simp: source_inputs_composition[symmetric] composed_presentation_def
    term_sequence_enumeration_exact source_input_data_sequence data_list_term_formed)

lemma source_base_native_change:
  "source_base_presents B q \<longleftrightarrow>
    (\<exists>p. data_table_presents payload_value_presents artifact_literal_presents B p \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p q)\<in>positive_meaning term_sequence_system)"
proof -
  have formed: "term_formed p" if "data_table_presents payload_value_presents artifact_literal_presents B p" for p
    by (rule data_table_presents_formed[OF that]) auto
  show ?thesis using formed by (auto simp: composed_presentation_def term_sequence_enumeration_exact)
qed

lemma source_inputs_native_at:
  assumes "\<forall>R\<in>set xs. exact_formed R"
  shows "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p (artifact_list_term xs))
      \<in>positive_meaning term_sequence_system \<longleftrightarrow>
    p=data_list_term (map (Target_Term \<circ> Whole_Artifact) xs)"
  using assms by (auto simp: term_sequence_enumeration_exact enumeration_retermination_def
    artifact_list_term_def enumeration_term_injective data_list_term_formed)

lemma source_base_at_change:
  assumes base: "source_base_presents B b"
    and change: "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p b)
      \<in>positive_meaning term_sequence_system"
  shows "data_table_presents payload_value_presents artifact_literal_presents B p"
proof -
  obtain q where table: "data_table_presents payload_value_presents artifact_literal_presents B q"
    and previous: "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) q b)
      \<in>positive_meaning term_sequence_system"
    using base by (simp only: source_base_native_change; blast)
  have first: "enumeration_retermination q b"
    using previous by (simp only: term_sequence_enumeration_exact; blast)
  have second: "enumeration_retermination p b"
    using change by (simp only: term_sequence_enumeration_exact; blast)
  have "q=p" by (rule presentation_class.recovery[OF enumeration_retermination_class first second])
  then show ?thesis using table by simp
qed

lemma source_context_valuation:
  "(242,t)\<in>positive_meaning source_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (h 1) \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (h 2) (h 0))\<in>positive_meaning source_system \<and>
      (238,h 2)\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (h 3) (h 1))\<in>positive_meaning source_system \<and>
      (241,h 3)\<in>positive_meaning source_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: source_system_clause source_clause_family_def source_context_schema_def schema_variables_def source_system_call)

lemma source_context_calls:
  "(242,t)\<in>positive_meaning source_system \<longleftrightarrow>
    (\<exists>x b p q. t=Pair_Term x b \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p x)\<in>positive_meaning source_system \<and>
      (238,p)\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) q b)\<in>positive_meaning source_system \<and>
      (241,q)\<in>positive_meaning source_system)"
proof
  assume "(242,t)\<in>positive_meaning source_system"
  then show "\<exists>x b p q. t=Pair_Term x b \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p x)\<in>positive_meaning source_system \<and>
      (238,p)\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) q b)\<in>positive_meaning source_system \<and>
      (241,q)\<in>positive_meaning source_system" by (simp only: source_context_valuation; blast)
next
  assume "\<exists>x b p q. t=Pair_Term x b \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p x)\<in>positive_meaning source_system \<and>
      (238,p)\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) q b)\<in>positive_meaning source_system \<and>
      (241,q)\<in>positive_meaning source_system"
  then obtain x b p q where shape: "t=Pair_Term x b" and support:
    "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p x)\<in>positive_meaning source_system"
    "(238,p)\<in>positive_meaning source_system"
    "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) q b)\<in>positive_meaning source_system"
    "(241,q)\<in>positive_meaning source_system" by blast
  have formed: "term_formed x" "term_formed b" "term_formed p" "term_formed q"
    using schema_call_formed_target[OF positive_meaning_formed[OF support(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF support(3)]] by auto
  let ?h="\<lambda>i::nat. if i=0 then x else if i=1 then b else if i=2 then p else q"
  show "(242,t)\<in>positive_meaning source_system"
    by (simp only: source_context_valuation; rule exI[of _ ?h]) (use shape support formed in auto)
qed

theorem source_context_exact:
  "(242,t)\<in>positive_meaning source_system \<longleftrightarrow> (\<exists>C. source_context_presents C t)"
proof
  assume accepted: "(242,t)\<in>positive_meaning source_system"
  obtain x b p q where shape: "t=Pair_Term x b"
    and input_change: "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p x)\<in>positive_meaning term_sequence_system"
    and input_list: "(238,p)\<in>positive_meaning source_system"
    and base_change: "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) q b)\<in>positive_meaning term_sequence_system"
    and base_table: "(241,q)\<in>positive_meaning source_system"
    using accepted by (simp only: source_context_calls source_component_meanings(5); blast)
  obtain xs where input: "data_sequence_presents artifact_literal_presents xs p"
    using input_list by (simp only: source_input_list_exact; blast)
  obtain B where base: "data_table_presents payload_value_presents artifact_literal_presents B q"
    using base_table by (simp only: source_base_table_exact; blast)
  have inputs: "source_inputs_presents xs x"
    by (simp only: source_inputs_native_change; rule exI[of _ p]) (use input input_change in blast)
  have bases: "source_base_presents B b"
    by (simp only: source_base_native_change; rule exI[of _ q]) (use base base_change in blast)
  show "\<exists>C. source_context_presents C t"
    by (rule exI[of _ "(xs,B)"]) (use inputs bases shape in auto)
next
  assume "\<exists>C. source_context_presents C t"
  then obtain C x b where shape: "t=Pair_Term x b"
    and inputs: "source_inputs_presents (fst C) x" and bases: "source_base_presents (snd C) b"
    by (auto simp: factor_pair_presents_def)
  obtain p where input: "data_sequence_presents artifact_literal_presents (fst C) p"
    and input_change: "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) p x)\<in>positive_meaning source_system"
    using inputs by (simp only: source_inputs_native_change source_component_meanings(5); blast)
  obtain q where base: "data_table_presents payload_value_presents artifact_literal_presents (snd C) q"
    and base_change: "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) q b)\<in>positive_meaning source_system"
    using bases by (simp only: source_base_native_change source_component_meanings(5); blast)
  have input_list: "(238,p)\<in>positive_meaning source_system"
    using input by (simp only: source_input_list_exact; blast)
  have base_table: "(241,q)\<in>positive_meaning source_system"
    using base by (simp only: source_base_table_exact; blast)
  show "(242,t)\<in>positive_meaning source_system"
    by (simp only: source_context_calls; rule exI[of _ x], rule exI[of _ b], rule exI[of _ p], rule exI[of _ q])
      (use shape input_change input_list base_change base_table in blast)
qed

lemma source_context_native_class:
  "presentation_class source_context_presents source_context_domain (\<lambda>p. (242,p)\<in>positive_meaning source_system)"
  using source_context_presentation_class by (simp only: source_context_exact)

theorem source_context_at_fields:
  assumes base: "finite_table_presents Payload_Term (\<lambda>R q. q=Target_Term (Whole_Artifact R)) B b"
  shows "(242,Pair_Term (artifact_list_term xs) b)\<in>positive_meaning source_system \<longleftrightarrow>
    source_context_domain (xs,B)"
proof
  assume "(242,Pair_Term (artifact_list_term xs) b)\<in>positive_meaning source_system"
  then obtain C where "context": "source_context_presents C (Pair_Term (artifact_list_term xs) b)"
    by (simp only: source_context_exact; blast)
  obtain ys Q where shape: "C=(ys,Q)" by (cases C) auto
  have domain: "source_context_domain (ys,Q)"
    by (rule source_contexts.subject_boundary[OF "context"[unfolded shape]])
  have rows: "finite_table_presents Payload_Term (\<lambda>R q. q=Target_Term (Whole_Artifact R)) Q b"
    and inputs: "artifact_list_term ys=artifact_list_term xs"
    using "context" by (auto simp: shape factor_pair_presents_def source_base_fields)
  have same: "Q=B" by (rule finite_table_presents_unique[OF rows base payload_term_injective]) simp
  show "source_context_domain (xs,B)" using domain same inputs by (simp add: artifact_list_term_exact)
next
  assume domain: "source_context_domain (xs,B)"
  have "context": "source_context_presents (xs,B) (Pair_Term (artifact_list_term xs) b)"
    using domain base by (simp only: source_context_fields; blast)
  show "(242,Pair_Term (artifact_list_term xs) b)\<in>positive_meaning source_system"
    using "context" by (simp only: source_context_exact; blast)
qed

text \<open>
  Literal admission projects the existing complete material reader. The
  element, list, row, and table contracts then supply complete source admission.
  All values must be whole-artifact literals, every key must be a formed
  payload, and the entire base relation must be functional. No unused row or
  input occurrence is exempt from these boundaries.

  The original input and table terms remain the public source presentation.
  Their data-list witnesses differ only at the existing terminator. The
  proofs preserve every supplied row order and repeated input occurrence.
\<close>

end
