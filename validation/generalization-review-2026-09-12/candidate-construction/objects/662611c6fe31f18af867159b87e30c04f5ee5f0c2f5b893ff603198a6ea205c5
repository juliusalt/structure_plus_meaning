theory Factor_Selection_Tables
  imports Factor_Selected_Fragments
begin

section \<open>The native row preserves the actual slot\<close>

lemma selected_piece_row_valuation:
  "(247,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
      t=context_relation_argument (h 0) (Pair_Term (h 1) (h 2)) (Pair_Term (h 1) (h 3)) \<and>
      (1,data_list_term [h 1])\<in>positive_meaning construction_admission_system \<and>
      (246,Pair_Term (Pair_Term (h 0) (h 2)) (h 3))\<in>positive_meaning construction_admission_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: construction_admission_clause construction_admission_clause_family_def
      selected_piece_row_schema_def schema_variables_def construction_admission_call)

lemma selected_piece_row_calls:
  "(247,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (\<exists>c k p q. t=context_relation_argument c (Pair_Term k p) (Pair_Term k q) \<and>
      (\<exists>a. payload_value_presents a k) \<and>
      (246,Pair_Term (Pair_Term c p) q)\<in>positive_meaning construction_admission_system)"
proof
  assume "(247,t)\<in>positive_meaning construction_admission_system"
  then show "\<exists>c k p q. t=context_relation_argument c (Pair_Term k p) (Pair_Term k q) \<and>
      (\<exists>a. payload_value_presents a k) \<and>
      (246,Pair_Term (Pair_Term c p) q)\<in>positive_meaning construction_admission_system"
    by (simp only: selected_piece_row_valuation construction_admission_components(1) payload_recognition_exact; blast)
next
  assume "\<exists>c k p q. t=context_relation_argument c (Pair_Term k p) (Pair_Term k q) \<and>
      (\<exists>a. payload_value_presents a k) \<and>
      (246,Pair_Term (Pair_Term c p) q)\<in>positive_meaning construction_admission_system"
  then obtain c k p q where shape: "t=context_relation_argument c (Pair_Term k p) (Pair_Term k q)"
    and key: "\<exists>a. payload_value_presents a k"
    and run: "(246,Pair_Term (Pair_Term c p) q)\<in>positive_meaning construction_admission_system" by blast
  have formed: "term_formed c" "term_formed k" "term_formed p" "term_formed q"
    using key schema_call_formed_target[OF positive_meaning_formed[OF run]] by auto
  have key_call: "(1,data_list_term [k])\<in>positive_meaning construction_admission_system"
    using key by (simp only: construction_admission_components(1) payload_recognition_exact)
  let ?h="\<lambda>i::nat. if i=0 then c else if i=1 then k else if i=2 then p else q"
  show "(247,t)\<in>positive_meaning construction_admission_system"
    by (simp only: selected_piece_row_valuation; rule exI[of _ ?h])
      (use shape key_call run formed in auto)
qed

lemma selected_piece_row_contract:
  assumes "context": "source_context_presents C c"
  shows "presented_function_contract (factor_pair_presents payload_value_presents (selection_presents C))
    (\<lambda>z. octets_formed (fst z) \<and> selection_valid C (snd z))
    (\<lambda>p. \<exists>k v. p=Pair_Term k v \<and> (\<exists>a. payload_value_presents a k) \<and> (\<exists>z. selection_presents C z v))
    (factor_pair_presents payload_value_presents artifact_value_presents)
    (\<lambda>z. octets_formed (fst z) \<and> exact_formed (snd z))
    (\<lambda>q. \<exists>k v. q=Pair_Term k v \<and> (\<exists>a. payload_value_presents a k) \<and>
      (11,v)\<in>positive_meaning artifact_admission_system)
    (map_prod id (selection_material C)) (selected_piece_rows.related c)"
proof -
  have copy: "presented_function_contract payload_value_presents octets_formed
      (\<lambda>p. \<exists>a. payload_value_presents a p)
      payload_value_presents octets_formed (\<lambda>p. \<exists>a. payload_value_presents a p)
      id (\<lambda>p q. (\<exists>a. payload_value_presents a p) \<and> q=p)"
    by (simp only: literal_copy_contract_iff[OF payload_value_presentation_class]) auto
  have operation: "(\<lambda>p q. \<exists>x y z w. p=Pair_Term x y \<and> q=Pair_Term z w \<and>
      ((\<exists>a. payload_value_presents a x) \<and> z=x) \<and>
      (246,Pair_Term (Pair_Term c y) w)\<in>positive_meaning construction_admission_system)=
      selected_piece_rows.related c"
    by (intro ext) (auto simp only: selected_piece_row_calls factor_term.inject; blast)
  show ?thesis using factor_pair_function_contract[OF copy selected_material_context_contract[OF "context"]]
    by (simp only: operation)
qed

section \<open>Sequence lifting and a commuting image establish table mapping\<close>

lemma selected_piece_data_witness:
  assumes "context": "source_context_presents C c"
  shows "presented_function_witness
    (data_table_presents payload_value_presents (selection_presents C)) (selection_table_domain C)
    (\<lambda>p. \<exists>Q. data_table_presents payload_value_presents (selection_presents C) Q p)
    (data_table_presents payload_value_presents artifact_value_presents)
    (finite_table_domain octets_formed exact_formed)
    (\<lambda>q. \<exists>Q. data_table_presents payload_value_presents artifact_value_presents Q q)
    (\<lambda>Q. map_prod id (selection_material C) ` Q)
    (\<lambda>p q. (21,p)\<in>positive_meaning keyed_list_system \<and>
      (248,context_relation_argument c p q)\<in>positive_meaning construction_admission_system)"
proof (rule table_value_mapping_witness[OF payload_value_presentation_class selection_presentation_class
    artifact_presentations.presentation_class_axioms])
  show "presented_function_contract
      (data_sequence_presents (factor_pair_presents payload_value_presents (selection_presents C)))
      (\<lambda>xs. \<forall>z\<in>set xs. octets_formed (fst z) \<and> selection_valid C (snd z))
      (\<lambda>p. \<exists>ps. (\<forall>x\<in>set ps. \<exists>k v. x=Pair_Term k v \<and>
        (\<exists>a. payload_value_presents a k) \<and> (\<exists>z. selection_presents C z v)) \<and> p=data_list_term ps)
      (data_sequence_presents (factor_pair_presents payload_value_presents artifact_value_presents))
      (\<lambda>ys. \<forall>z\<in>set ys. octets_formed (fst z) \<and> exact_formed (snd z))
      (\<lambda>q. \<exists>qs. (\<forall>y\<in>set qs. \<exists>k v. y=Pair_Term k v \<and>
        (\<exists>a. payload_value_presents a k) \<and> (11,v)\<in>positive_meaning artifact_admission_system) \<and> q=data_list_term qs)
      (map (map_prod id (selection_material C)))
      (\<lambda>p q. (248,context_relation_argument c p q)\<in>positive_meaning construction_admission_system)"
    by (rule selected_piece_rows.presented_mapping_contract[OF source_context_formed[OF "context"]
      selected_piece_row_contract[OF "context"]])
next
  fix xs p assume read: "data_sequence_presents
      (factor_pair_presents payload_value_presents (selection_presents C)) xs p"
  show "(21,p)\<in>positive_meaning keyed_list_system \<longleftrightarrow> distinct xs \<and> single_valued (set xs)"
    by (rule encoded_table_sequence_keys[OF read, where encode=Payload_Term])
      (use selection_presents_formed[OF source_contexts.subject_boundary[OF "context"]]
        in \<open>auto simp: inj_def factor_pair_presents_def\<close>)
qed

lemma selected_piece_reterminated_witness:
  assumes "context": "source_context_presents C c"
  shows "presented_function_witness (selection_table_presents C) (selection_table_domain C)
    (\<lambda>p. \<exists>Q. selection_table_presents C Q p)
    (data_table_presents payload_value_presents artifact_value_presents)
    (finite_table_domain octets_formed exact_formed)
    (\<lambda>q. \<exists>Q. data_table_presents payload_value_presents artifact_value_presents Q q)
    (\<lambda>Q. map_prod id (selection_material C) ` Q)
    (\<lambda>p q. \<exists>u. enumeration_retermination u p \<and>
      (21,u)\<in>positive_meaning keyed_list_system \<and>
      (248,context_relation_argument c u q)\<in>positive_meaning construction_admission_system)"
proof -
  have changed: "presented_function_witness (selection_table_presents C) (selection_table_domain C)
      (\<lambda>p. (\<exists>ts. p=enumeration_term ts) \<and>
        (\<exists>u. (\<exists>Q. data_table_presents payload_value_presents (selection_presents C) Q u) \<and>
          enumeration_retermination u p))
      (data_table_presents payload_value_presents artifact_value_presents)
      (finite_table_domain octets_formed exact_formed)
      (\<lambda>q. \<exists>Q. data_table_presents payload_value_presents artifact_value_presents Q q)
      (\<lambda>Q. map_prod id (selection_material C) ` Q)
      (\<lambda>p q. \<exists>u. enumeration_retermination u p \<and>
        (21,u)\<in>positive_meaning keyed_list_system \<and>
        (248,context_relation_argument c u q)\<in>positive_meaning construction_admission_system)"
    by (rule presented_function_witness.input_presentation[OF selected_piece_data_witness[OF "context"]
        enumeration_retermination_class])
      (auto simp: data_table_presents_def data_collection_presents_def)
  have admission: "((\<exists>ts. p=enumeration_term ts) \<and>
      (\<exists>u. (\<exists>Q. data_table_presents payload_value_presents (selection_presents C) Q u) \<and>
        enumeration_retermination u p)) \<longleftrightarrow> (\<exists>Q. selection_table_presents C Q p)" for p
    by (auto simp: composed_presentation_def enumeration_retermination_def; blast)
  show ?thesis using changed by (simp only: admission)
qed

section \<open>The whole table clause retains context admission on the empty case\<close>

lemma selected_piece_table_valuation:
  "(249,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (h 0) (h 1)) (h 3) \<and>
      (242,h 0)\<in>positive_meaning construction_admission_system \<and>
      (233,collection_join_argument (Target_Term (Whole_Artifact empty_artifact)) (h 2) (h 1))
        \<in>positive_meaning construction_admission_system \<and>
      (21,h 2)\<in>positive_meaning construction_admission_system \<and>
      (248,context_relation_argument (h 0) (h 2) (h 3))\<in>positive_meaning construction_admission_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: construction_admission_clause construction_admission_clause_family_def
      selected_piece_table_schema_def schema_variables_def construction_admission_call)

lemma selected_piece_table_calls:
  "(249,t)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
    (\<exists>c p u q. t=Pair_Term (Pair_Term c p) q \<and>
      (242,c)\<in>positive_meaning source_system \<and> enumeration_retermination u p \<and>
      (21,u)\<in>positive_meaning keyed_list_system \<and>
      (248,context_relation_argument c u q)\<in>positive_meaning construction_admission_system)"
proof
  assume "(249,t)\<in>positive_meaning construction_admission_system"
  then show "\<exists>c p u q. t=Pair_Term (Pair_Term c p) q \<and>
      (242,c)\<in>positive_meaning source_system \<and> enumeration_retermination u p \<and>
      (21,u)\<in>positive_meaning keyed_list_system \<and>
      (248,context_relation_argument c u q)\<in>positive_meaning construction_admission_system"
    by (simp only: selected_piece_table_valuation construction_admission_components term_sequence_enumeration_exact; blast)
next
  assume "\<exists>c p u q. t=Pair_Term (Pair_Term c p) q \<and>
      (242,c)\<in>positive_meaning source_system \<and> enumeration_retermination u p \<and>
      (21,u)\<in>positive_meaning keyed_list_system \<and>
      (248,context_relation_argument c u q)\<in>positive_meaning construction_admission_system"
  then obtain c p u q where shape: "t=Pair_Term (Pair_Term c p) q"
    and calls: "(242,c)\<in>positive_meaning source_system" "enumeration_retermination u p"
      "(21,u)\<in>positive_meaning keyed_list_system"
      "(248,context_relation_argument c u q)\<in>positive_meaning construction_admission_system" by blast
  have formed: "term_formed c" "term_formed u" "term_formed q"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(4)]] by auto
  have old: "term_formed p" using calls(2) formed(2)
    by (auto simp: enumeration_retermination_def data_list_term_formed enumeration_term_formed)
  let ?h="\<lambda>i::nat. if i=0 then c else if i=1 then p else if i=2 then u else q"
  show "(249,t)\<in>positive_meaning construction_admission_system"
    by (simp only: selected_piece_table_valuation; rule exI[of _ ?h])
      (use shape calls formed old in \<open>auto simp: construction_admission_components term_sequence_enumeration_exact\<close>)
qed

lemma selected_piece_context_witness:
  assumes "context": "source_context_presents C c"
  shows "presented_function_witness (selection_table_presents C) (selection_table_domain C)
    (\<lambda>p. \<exists>Q. selection_table_presents C Q p)
    (data_table_presents payload_value_presents artifact_value_presents)
    (finite_table_domain octets_formed exact_formed)
    (\<lambda>q. \<exists>Q. data_table_presents payload_value_presents artifact_value_presents Q q)
    (\<lambda>Q. map_prod id (selection_material C) ` Q)
    (\<lambda>p q. (249,Pair_Term (Pair_Term c p) q)\<in>positive_meaning construction_admission_system)"
proof -
  have admitted: "(242,c)\<in>positive_meaning source_system"
    using "context" by (simp only: source_context_exact; blast)
  have operation: "(249,Pair_Term (Pair_Term c p) q)\<in>positive_meaning construction_admission_system \<longleftrightarrow>
      (\<exists>u. enumeration_retermination u p \<and> (21,u)\<in>positive_meaning keyed_list_system \<and>
        (248,context_relation_argument c u q)\<in>positive_meaning construction_admission_system)" for p q
    using admitted by (auto simp only: selected_piece_table_calls factor_term.inject)
  show ?thesis using selected_piece_reterminated_witness[OF "context"] by (simp only: operation)
qed

interpretation selected_piece_tables: presented_function_witness
  selection_context_presents selection_context_domain "\<lambda>p. \<exists>z. selection_context_presents z p"
  "data_table_presents payload_value_presents artifact_value_presents"
  "finite_table_domain octets_formed exact_formed"
  "\<lambda>q. \<exists>Q. data_table_presents payload_value_presents artifact_value_presents Q q"
  selection_context_value "\<lambda>p q. (249,Pair_Term p q)\<in>positive_meaning construction_admission_system"
proof (rule presented_function_witness.intro[OF selection_context_presentation_class
    data_table_presentation_class[OF payload_value_presentation_class artifact_presentations.presentation_class_axioms]];
    unfold_locales)
  fix p q assume run: "(249,Pair_Term p q)\<in>positive_meaning construction_admission_system"
  obtain c s where shape: "p=Pair_Term c s" and admitted: "(242,c)\<in>positive_meaning source_system"
    using run by (auto simp only: selected_piece_table_calls factor_term.inject)
  obtain C where "context": "source_context_presents C c" using admitted by (simp only: source_context_exact; blast)
  have "\<exists>Q. selection_table_presents C Q s"
    using presented_function_witness.input_boundary[OF selected_piece_context_witness[OF "context"]] run shape by blast
  then obtain Q where table: "selection_table_presents C Q s" by blast
  show "\<exists>z. selection_context_presents z p"
    by (rule exI[of _ "(C,Q)"]) (use "context" table in \<open>simp only: shape selection_context_at\<close>)
next
  fix z p q assume read: "selection_context_presents z p"
    and run: "(249,Pair_Term p q)\<in>positive_meaning construction_admission_system"
  obtain C Q c s where shape: "z=(C,Q)" "p=Pair_Term c s"
    and "context": "source_context_presents C c" and table: "selection_table_presents C Q s"
    using read by (cases z) (auto simp: selection_context_presents_def factor_pair_presents_def selection_table_fields)
  show "data_table_presents payload_value_presents artifact_value_presents (selection_context_value z) q"
    using presented_function_witness.sound[OF selected_piece_context_witness[OF "context"] table] run
    by (simp add: shape)
next
  fix p assume "\<exists>z. selection_context_presents z p"
  then obtain C Q c s where shape: "p=Pair_Term c s"
    and "context": "source_context_presents C c" and table: "selection_table_presents C Q s"
    by (auto simp: selection_context_presents_def factor_pair_presents_def selection_table_fields)
  have "\<exists>q. (249,Pair_Term (Pair_Term c s) q)\<in>positive_meaning construction_admission_system"
    by (rule presented_function_witness.total[OF selected_piece_context_witness[OF "context"]]) (use table in blast)
  then show "\<exists>q. (249,Pair_Term p q)\<in>positive_meaning construction_admission_system" by (simp only: shape)
qed

theorem selected_piece_table_input_exact:
  "(\<exists>q. (249,Pair_Term p q)\<in>positive_meaning construction_admission_system) \<longleftrightarrow>
    (\<exists>z. selection_context_presents z p)"
  by (rule selected_piece_tables.input_exact)

text \<open>
  The slot uses its literal identity contract and the material uses the owned
  selection contract. Product and sequence lifting discharge the complete row
  and traversal meanings. The general table theorem then restricts by actual
  key uniqueness and takes the commuting set image. Retermination changes
  only the input's existing terminator.

  Every admitted whole context and selection table has a returned complete
  piece table. Every returned table denotes the same derived piece graph.
  Distinct slots remain distinct even when their material is equal. The
  source and target classes include all allowed row orders; the native
  traversal's more specific output ordering is internal to this witness.
\<close>

end
