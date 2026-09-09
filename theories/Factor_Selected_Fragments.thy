theory Factor_Selected_Fragments
  imports Factor_Construction_Admission_Clauses
begin

section \<open>Complete address sets cross the existing terminator boundary\<close>

lemma selected_set_retermination:
  "composed_presentation payload_set_presents enumeration_retermination A p \<longleftrightarrow>
    (\<forall>a\<in>A. octets_formed a) \<and> finite_set_presents Payload_Term A p"
  by (auto simp: composed_presentation_def payload_set_enumerations enumeration_retermination_def
    data_list_term_injective finite_set_presents_iff; blast)

lemma selected_set_native_retermination:
  "(\<exists>u. payload_set_presents A u \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u p)
        \<in>positive_meaning term_sequence_system) \<longleftrightarrow>
    (\<forall>a\<in>A. octets_formed a) \<and> finite_set_presents Payload_Term A p"
  using payload_set_formed by (auto simp: term_sequence_enumeration_exact
    selected_set_retermination[symmetric] composed_presentation_def)

lemma selected_set_comparison_reverse:
  assumes selected: "payload_set_presents A q"
  shows "(6,Pair_Term p q)\<in>positive_meaning bag_comparison_system \<longleftrightarrow> payload_set_presents A p"
proof -
  have symmetric: "(6,Pair_Term p q)\<in>positive_meaning bag_comparison_system \<longleftrightarrow>
      (6,Pair_Term q p)\<in>positive_meaning bag_comparison_system"
  proof -
    have swap: "(6,Pair_Term v u)\<in>positive_meaning bag_comparison_system"
      if "(6,Pair_Term u v)\<in>positive_meaning bag_comparison_system" for u v
    proof -
      note support=that
      obtain xs ys where shape: "Pair_Term u v=Pair_Term (data_list_term xs) (data_list_term ys)"
        and lists: "data_elements xs" "data_elements ys" "mset xs=mset ys"
        using bag_comparison_sound[OF support] by blast
      have parts: "u=data_list_term xs" "v=data_list_term ys" using shape by simp_all
      show ?thesis
        by (simp only: bag_comparison_exact; rule exI[of _ ys], rule exI[of _ xs])
          (use parts lists in auto)
    qed
    show ?thesis using swap by blast
  qed
  show ?thesis by (simp only: symmetric payload_set_comparison[OF selected])
qed

section \<open>The ordinary selection clause consumes four established relations\<close>

lemma selected_fragment_valuation:
  "(245,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (h 0) (Pair_Term (h 1) (h 2))) (Pair_Term (h 3) (h 4)) \<and>
      (244,Pair_Term (Pair_Term (h 0) (h 1)) (h 3))\<in>positive_meaning construction_admission_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (h 5) (h 2))
        \<in>positive_meaning construction_admission_system \<and>
      (6,Pair_Term (h 5) (h 4))\<in>positive_meaning construction_admission_system \<and>
      (205,Pair_Term (h 3) (h 4))\<in>positive_meaning construction_admission_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: construction_admission_clause construction_admission_clause_family_def
      selected_fragment_schema_def schema_variables_def construction_admission_call)

lemma selected_fragment_calls:
  "(245,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (\<exists>c j a r b u. t=Pair_Term (Pair_Term c (Pair_Term j a)) (Pair_Term r b) \<and>
      (244,Pair_Term (Pair_Term c j) r)\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u a)
        \<in>positive_meaning term_sequence_system \<and>
      (6,Pair_Term u b)\<in>positive_meaning bag_comparison_system \<and>
      (205,Pair_Term r b)\<in>positive_meaning fragment_system)"
proof
  assume "(245,t)\<in>positive_meaning construction_admission_system"
  then show "\<exists>c j a r b u. t=Pair_Term (Pair_Term c (Pair_Term j a)) (Pair_Term r b) \<and>
      (244,Pair_Term (Pair_Term c j) r)\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u a)
        \<in>positive_meaning term_sequence_system \<and>
      (6,Pair_Term u b)\<in>positive_meaning bag_comparison_system \<and>
      (205,Pair_Term r b)\<in>positive_meaning fragment_system"
    by (simp only: selected_fragment_valuation construction_admission_components; blast)
next
  assume "\<exists>c j a r b u. t=Pair_Term (Pair_Term c (Pair_Term j a)) (Pair_Term r b) \<and>
      (244,Pair_Term (Pair_Term c j) r)\<in>positive_meaning source_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u a)
        \<in>positive_meaning term_sequence_system \<and>
      (6,Pair_Term u b)\<in>positive_meaning bag_comparison_system \<and>
      (205,Pair_Term r b)\<in>positive_meaning fragment_system"
  then obtain c j a r b u where shape: "t=Pair_Term (Pair_Term c (Pair_Term j a)) (Pair_Term r b)"
    and calls: "(244,Pair_Term (Pair_Term c j) r)\<in>positive_meaning source_system"
      "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u a)\<in>positive_meaning term_sequence_system"
      "(6,Pair_Term u b)\<in>positive_meaning bag_comparison_system"
      "(205,Pair_Term r b)\<in>positive_meaning fragment_system" by blast
  have formed: "term_formed c" "term_formed j" "term_formed a" "term_formed r" "term_formed b" "term_formed u"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(4)]] by auto
  let ?h="\<lambda>i::nat. if i=0 then c else if i=1 then j else if i=2 then a else if i=3 then r else if i=4 then b else u"
  show "(245,t)\<in>positive_meaning construction_admission_system"
    by (simp only: selected_fragment_valuation; rule exI[of _ ?h])
      (use shape calls formed in \<open>auto simp: construction_admission_components\<close>)
qed

lemma selected_fragment_at_context:
  assumes "context": "source_context_presents C c"
  shows "(245,Pair_Term (Pair_Term c p) q)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (\<exists>z. selection_presents C z p \<and>
      fragment_value_presents (construction_fragment (fst C) (snd C) (fst z) (snd z)) q)"
proof
  assume accepted: "(245,Pair_Term (Pair_Term c p) q)\<in>positive_meaning construction_admission_system"
  obtain j a r b u where shape: "p=Pair_Term j a" "q=Pair_Term r b"
    and calls: "(244,Pair_Term (Pair_Term c j) r)\<in>positive_meaning source_system"
      "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u a)\<in>positive_meaning term_sequence_system"
      "(6,Pair_Term u b)\<in>positive_meaning bag_comparison_system"
      "(205,Pair_Term r b)\<in>positive_meaning fragment_system"
    using accepted by (auto simp only: selected_fragment_calls factor_term.inject)
  obtain z where source: "source_query_presents z (Pair_Term c j)"
    and artifact: "artifact_value_presents (source_query_value z) r"
    using calls(1) by (auto simp only: source_value_exact factor_term.inject)
  obtain C' k where query: "z=(C',k)" by (cases z) auto
  have other: "source_context_presents C' c"
    and actual: "\<exists>R. construction_source_at (fst C') (snd C') k R"
    and index: "j=construction_source_term k"
    using source by (auto simp: query source_query_presents_def)
  have same: "C'=C" using source_contexts.recovery[OF other "context"] .
  obtain G where fragment: "fragment_value_presents G (Pair_Term r b)"
    using calls(4) by (simp only: fragment_admission_exact; blast)
  have gf: "fragment_formed G" and gr: "artifact_value_presents (fragment_source G) r"
    and gs: "payload_set_presents (fragment_selection G) b"
    using fragment by (simp only: fragment_value_fields; blast)+
  have "value": "fragment_source G=construction_source_value (fst C) (snd C) k"
    using artifact_presentations.recovery[OF gr artifact] by (simp add: query same)
  have set: "payload_set_presents (fragment_selection G) u"
    using calls(3) by (simp only: selected_set_comparison_reverse[OF gs])
  have old: "finite_set_presents Payload_Term (fragment_selection G) a"
    using set calls(2) selected_set_native_retermination[of "fragment_selection G" a] by blast
  have valid: "selection_valid C (k,fragment_selection G)"
    using gf actual "value" same by (auto simp: source_selection_valid_def fragment_formed_def)
  have selected: "selection_presents C (k,fragment_selection G) p"
    using valid old index shape(1) by (auto simp: construction_selection_presents_def)
  have material: "construction_fragment (fst C) (snd C) k (fragment_selection G)=G"
    using "value" by (cases G) (simp add: construction_fragment_def)
  show "\<exists>z. selection_presents C z p \<and>
      fragment_value_presents (construction_fragment (fst C) (snd C) (fst z) (snd z)) q"
    by (rule exI[of _ "(k,fragment_selection G)"])
      (use selected fragment material in \<open>simp add: shape\<close>)
next
  assume "\<exists>z. selection_presents C z p \<and>
    fragment_value_presents (construction_fragment (fst C) (snd C) (fst z) (snd z)) q"
  then obtain z where selected: "selection_presents C z p"
    and fragment: "fragment_value_presents (construction_fragment (fst C) (snd C) (fst z) (snd z)) q" by blast
  obtain k A where "value": "z=(k,A)" by (cases z) auto
  obtain a where old: "finite_set_presents Payload_Term A a"
    and input: "p=Pair_Term (construction_source_term k) a"
    using selected by (auto simp: "value" construction_selection_presents_def)
  obtain r b where artifact: "artifact_value_presents (construction_source_value (fst C) (snd C) k) r"
    and selection: "payload_set_presents A b" and "output": "q=Pair_Term r b"
    using fragment by (auto simp: "value" fragment_value_presents_def factor_pair_presents_def construction_fragment_def)
  have coordinates: "\<forall>a\<in>A. octets_formed a" using payload_set_formed[OF selection] by blast
  obtain u where set: "payload_set_presents A u"
    and change: "(233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) u a)
      \<in>positive_meaning term_sequence_system"
    using selected_set_native_retermination[of A a] coordinates old by blast
  have query: "source_query_presents (C,k) (Pair_Term c (construction_source_term k))"
    using selected "context" source_contexts.subject_boundary[OF "context"]
    by (auto simp: "value" source_query_presents_def source_selection_valid_def)
  have source: "(244,Pair_Term (Pair_Term c (construction_source_term k)) r)\<in>positive_meaning source_system"
    using source_value_reading.output[OF query, of r] artifact by simp
  have compared: "(6,Pair_Term u b)\<in>positive_meaning bag_comparison_system"
    using selection by (simp only: payload_set_comparison[OF set])
  have admitted: "(205,Pair_Term r b)\<in>positive_meaning fragment_system"
    using fragment by (simp only: "output" fragment_admission_exact; blast)
  show "(245,Pair_Term (Pair_Term c p) q)\<in>positive_meaning construction_admission_system"
    unfolding selected_fragment_calls
    by (rule exI[of _ c], rule exI[of _ "construction_source_term k"], rule exI[of _ a],
        rule exI[of _ r], rule exI[of _ b], rule exI[of _ u])
      (use source change compared admitted in \<open>simp add: input "output"\<close>)
qed

theorem selected_fragment_exact:
  "(245,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (\<exists>z p q. t=Pair_Term p q \<and> selection_query_presents z p \<and>
      fragment_value_presents (selection_query_fragment z) q)"
proof
  assume accepted: "(245,t)\<in>positive_meaning construction_admission_system"
  obtain c j a r b where shape: "t=Pair_Term (Pair_Term c (Pair_Term j a)) (Pair_Term r b)"
    and source: "(244,Pair_Term (Pair_Term c j) r)\<in>positive_meaning source_system"
    using accepted by (simp only: selected_fragment_calls; blast)
  obtain C where "context": "source_context_presents C c"
    using source by (auto simp: source_value_exact source_query_presents_def factor_pair_presents_def)
  obtain z where selected: "selection_presents C z (Pair_Term j a)"
    and result: "fragment_value_presents (construction_fragment (fst C) (snd C) (fst z) (snd z)) (Pair_Term r b)"
    using accepted by (simp only: shape selected_fragment_at_context[OF "context"]; blast)
  show "\<exists>z p q. t=Pair_Term p q \<and> selection_query_presents z p \<and>
      fragment_value_presents (selection_query_fragment z) q"
    by (rule exI[of _ "(C,z)"], rule exI[of _ "Pair_Term c (Pair_Term j a)"], rule exI[of _ "Pair_Term r b"])
      (use "context" selected result shape in \<open>simp add: selection_query_at\<close>)
next
  assume "\<exists>z p q. t=Pair_Term p q \<and> selection_query_presents z p \<and>
    fragment_value_presents (selection_query_fragment z) q"
  then obtain z p q where input: "selection_query_presents z p"
    and result: "fragment_value_presents (selection_query_fragment z) q"
    and shape: "t=Pair_Term p q" by blast
  have pair: "factor_pair_presents source_context_presents construction_selection_presents z p"
    and domain: "selection_query_domain z" using input by (simp only: selection_query_presents_def; blast)+
  obtain c s where "context": "source_context_presents (fst z) c"
    and raw: "construction_selection_presents (snd z) s" and inner: "p=Pair_Term c s"
    using factor_pair_presents_def[THEN iffD1, OF pair] by blast
  have selected: "selection_presents (fst z) (snd z) s" using domain raw by blast
  show "(245,t)\<in>positive_meaning construction_admission_system"
    by (simp only: shape inner selected_fragment_at_context[OF "context"])
      (use selected result in blast)
qed

interpretation selected_fragment_reading: presented_function_contract
  selection_query_presents selection_query_domain "\<lambda>p. \<exists>z. selection_query_presents z p"
  fragment_value_presents fragment_formed "\<lambda>q. (205,q)\<in>positive_meaning fragment_system"
  selection_query_fragment "\<lambda>p q. (245,Pair_Term p q)\<in>positive_meaning construction_admission_system"
  using selection_query_presentation_class fragment_value_native_class selection_query_fragment_formed
  by (simp add: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def selected_fragment_exact presented_relation_def)

section \<open>Material is obtained by composing the owned fragment projection\<close>

lemma selected_material_step:
  "presented_function_contract fragment_value_presents fragment_formed
    (\<lambda>p. (205,p)\<in>positive_meaning fragment_system)
    artifact_value_presents exact_formed (\<lambda>q. (11,q)\<in>positive_meaning artifact_admission_system)
    fragment_material (\<lambda>p q. (206,Pair_Term p q)\<in>positive_meaning construction_admission_system)"
  using fragment_material_reading.presented_function_contract_axioms
  by (simp only: construction_admission_components(6))

interpretation selected_material_reading: presented_function_contract
  selection_query_presents selection_query_domain "\<lambda>p. \<exists>z. selection_query_presents z p"
  artifact_value_presents exact_formed "\<lambda>q. (11,q)\<in>positive_meaning artifact_admission_system"
  "\<lambda>z. selection_material (fst z) (snd z)"
  "\<lambda>p q. (246,Pair_Term p q)\<in>positive_meaning construction_admission_system"
  using selected_material_composition.function_contract[OF selected_fragment_reading.presented_function_contract_axioms
    selected_material_step] by (simp only: comp_def)

theorem selected_material_exact:
  "(246,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (\<exists>z p q. t=Pair_Term p q \<and> selection_query_presents z p \<and>
      artifact_value_presents (selection_material (fst z) (snd z)) q)"
proof -
  have pair: "(246,Pair_Term p q)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
      (\<exists>z. selection_query_presents z p \<and> artifact_value_presents (selection_material (fst z) (snd z)) q)" for p q
    by (simp only: selected_material_reading.exact presented_relation_def; blast)
  have shape: "(246,t)\<in>positive_meaning construction_admission_system \<Longrightarrow> \<exists>p q. t=Pair_Term p q"
    by (simp only: selected_material_composition.exact; blast)
  show ?thesis using pair shape by blast
qed

lemma selected_material_at_context:
  assumes "context": "source_context_presents C c"
  shows "(246,Pair_Term (Pair_Term c p) q)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (\<exists>z. selection_presents C z p \<and> artifact_value_presents (selection_material C z) q)"
  by (simp only: selected_material_reading.exact presented_relation_def selection_query_at_fixed_context[OF "context"])
    (auto; metis fst_conv snd_conv)

theorem selected_material_context_contract:
  assumes "context": "source_context_presents C c"
  shows "presented_function_contract (selection_presents C) (selection_valid C)
    (\<lambda>p. \<exists>z. selection_presents C z p)
    artifact_value_presents exact_formed (\<lambda>q. (11,q)\<in>positive_meaning artifact_admission_system)
    (selection_material C) (\<lambda>p q. (246,Pair_Term (Pair_Term c p) q)\<in>positive_meaning construction_admission_system)"
  using selection_presentation_class[of C] artifact_presentations.presentation_class_axioms
    selection_material_formed[OF source_contexts.subject_boundary[OF "context"]]
  by (simp add: presented_function_contract_def presented_function_contract_axioms_def
    presented_relation_contract_def presented_relation_contract_axioms_def
    selected_material_at_context[OF "context"] presented_relation_def)

text \<open>
  The supplied source is recovered before the selected fragment is admitted.
  Retermination retains the actual input set order, while complete set
  comparison admits every compatible output order. Fragment admission checks
  that all selected atoms occur in that exact source. These four contracts
  establish the complete fragment result without an output-order convention.

  Material then follows by the general two-reader composition theorem. The
  fixed-context contract is available to the independent keyed-row and
  sequence constructions; neither consumer reopens source lookup or fragment
  restriction. The source context remains present even for an empty selection.
\<close>

end
