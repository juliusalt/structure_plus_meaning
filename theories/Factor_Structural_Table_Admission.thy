theory Factor_Structural_Table_Admission
  imports Factor_Structural_Table_Clauses
begin

abbreviation piece_entry_presents where
  "piece_entry_presents \<equiv> factor_pair_presents payload_value_presents artifact_value_presents"

abbreviation origin_entry_presents where
  "origin_entry_presents \<equiv>
    factor_pair_presents (factor_pair_presents payload_value_presents payload_value_presents) payload_value_presents"

section \<open>Each row owns every component of its reading\<close>

lemma structural_piece_row_valuation:
  "(211,t)\<in>positive_meaning structural_table_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1}. term_formed (h i)) \<and>
      t=Pair_Term (h 0) (h 1) \<and> (1,data_list_term [h 0])\<in>positive_meaning structural_table_system \<and>
        (11,h 1)\<in>positive_meaning structural_table_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: structural_table_clause structural_table_clause_family_def structural_table_schema_defs
      schema_variables_def structural_table_call)

lemma structural_piece_row_calls:
  "(211,t)\<in>positive_meaning structural_table_system \<longleftrightarrow>
    (\<exists>x y. t=Pair_Term (x) (y) \<and> (1,data_list_term [x])\<in>positive_meaning structural_table_system \<and>
        (11,y)\<in>positive_meaning structural_table_system)"
proof
  assume "(211,t)\<in>positive_meaning structural_table_system"
  then show "\<exists>x y. t=Pair_Term (x) (y) \<and> (1,data_list_term [x])\<in>positive_meaning structural_table_system \<and>
        (11,y)\<in>positive_meaning structural_table_system"
    by (simp only: structural_piece_row_valuation; blast)
next
  assume "\<exists>x y. t=Pair_Term (x) (y) \<and> (1,data_list_term [x])\<in>positive_meaning structural_table_system \<and>
        (11,y)\<in>positive_meaning structural_table_system"
  then obtain x y where shape: "t=Pair_Term (x) (y)" and supported: "(1,data_list_term [x])\<in>positive_meaning structural_table_system \<and>
        (11,y)\<in>positive_meaning structural_table_system" by blast
  have formed: "term_formed x" "term_formed y"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then x else y"
  show "(211,t)\<in>positive_meaning structural_table_system"
    by (simp only: structural_piece_row_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

theorem structural_piece_row_exact:
  "(211,t)\<in>positive_meaning structural_table_system \<longleftrightarrow>
    (\<exists>z. piece_entry_presents z t)"
  by (simp only: structural_piece_row_calls structural_table_components;
    auto simp: factor_pair_presents_def; metis fst_conv snd_conv)

lemma structural_origin_row_valuation:
  "(214,t)\<in>positive_meaning structural_table_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2}. term_formed (h i)) \<and>
      t=Pair_Term (Pair_Term (h 0) (h 1)) (h 2) \<and> (1,data_list_term [h 0])\<in>positive_meaning structural_table_system \<and>
        (1,data_list_term [h 1])\<in>positive_meaning structural_table_system \<and>
        (1,data_list_term [h 2])\<in>positive_meaning structural_table_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: structural_table_clause structural_table_clause_family_def structural_table_schema_defs
      schema_variables_def structural_table_call)

lemma structural_origin_row_calls:
  "(214,t)\<in>positive_meaning structural_table_system \<longleftrightarrow>
    (\<exists>x y z. t=Pair_Term (Pair_Term (x) (y)) (z) \<and> (1,data_list_term [x])\<in>positive_meaning structural_table_system \<and>
        (1,data_list_term [y])\<in>positive_meaning structural_table_system \<and>
        (1,data_list_term [z])\<in>positive_meaning structural_table_system)"
proof
  assume "(214,t)\<in>positive_meaning structural_table_system"
  then show "\<exists>x y z. t=Pair_Term (Pair_Term (x) (y)) (z) \<and> (1,data_list_term [x])\<in>positive_meaning structural_table_system \<and>
        (1,data_list_term [y])\<in>positive_meaning structural_table_system \<and>
        (1,data_list_term [z])\<in>positive_meaning structural_table_system"
    by (simp only: structural_origin_row_valuation; blast)
next
  assume "\<exists>x y z. t=Pair_Term (Pair_Term (x) (y)) (z) \<and> (1,data_list_term [x])\<in>positive_meaning structural_table_system \<and>
        (1,data_list_term [y])\<in>positive_meaning structural_table_system \<and>
        (1,data_list_term [z])\<in>positive_meaning structural_table_system"
  then obtain x y z where shape: "t=Pair_Term (Pair_Term (x) (y)) (z)" and supported: "(1,data_list_term [x])\<in>positive_meaning structural_table_system \<and>
        (1,data_list_term [y])\<in>positive_meaning structural_table_system \<and>
        (1,data_list_term [z])\<in>positive_meaning structural_table_system" by blast
  have formed: "term_formed x" "term_formed y" "term_formed z"
    using supported positive_meaning_formed schema_call_formed_target by fastforce+
  let ?h="\<lambda>i::nat. if i=0 then x else if i=1 then y else z"
  show "(214,t)\<in>positive_meaning structural_table_system"
    by (simp only: structural_origin_row_valuation; rule exI[of _ ?h])
      (use shape supported formed in auto)
qed

theorem structural_origin_row_exact:
  "(214,t)\<in>positive_meaning structural_table_system \<longleftrightarrow>
    (\<exists>z. origin_entry_presents z t)"
  by (simp only: structural_origin_row_calls structural_table_components;
    auto simp: factor_pair_presents_def; metis fst_conv snd_conv)

lemma piece_entry_native_class:
  "presentation_class piece_entry_presents (\<lambda>z. octets_formed (fst z) \<and> exact_formed (snd z))
    (\<lambda>t. (211,t)\<in>positive_meaning structural_table_system)"
proof -
  have pairs: "presentation_class piece_entry_presents (\<lambda>z. octets_formed (fst z) \<and> exact_formed (snd z))
      (\<lambda>t. \<exists>p q. (\<exists>a. payload_value_presents a p) \<and>
        (11,q)\<in>positive_meaning artifact_admission_system \<and> t=Pair_Term p q)"
    by (rule factor_pair_class[OF payload_value_presentation_class artifact_presentations.presentation_class_axioms])
  have admission: "(\<exists>p q. (\<exists>a. payload_value_presents a p) \<and>
      (11,q)\<in>positive_meaning artifact_admission_system \<and> t=Pair_Term p q)
      \<longleftrightarrow> (211,t)\<in>positive_meaning structural_table_system" for t
    using presentation_class.admissible_iff[OF pairs, of t] by (simp only: structural_piece_row_exact)
  show ?thesis using pairs by (simp only: presentation_class_def admission)
qed

lemma origin_entry_native_class:
  "presentation_class origin_entry_presents
    (\<lambda>z. (octets_formed (fst (fst z)) \<and> octets_formed (snd (fst z))) \<and> octets_formed (snd z))
    (\<lambda>t. (214,t)\<in>positive_meaning structural_table_system)"
proof -
  have pairs: "presentation_class (factor_pair_presents attachment_value_presents payload_value_presents)
      (\<lambda>z. (octets_formed (fst (fst z)) \<and> octets_formed (snd (fst z))) \<and> octets_formed (snd z))
      (\<lambda>t. \<exists>p q. (\<exists>a. attachment_value_presents a p) \<and>
        (\<exists>b. payload_value_presents b q) \<and> t=Pair_Term p q)"
    by (rule factor_pair_class[OF attachment_value_presentation_class payload_value_presentation_class])
  have same: "factor_pair_presents attachment_value_presents payload_value_presents=origin_entry_presents"
    by (intro ext) (simp only: factor_pair_presents_def attachment_value_components)
  have admission: "(\<exists>p q. (\<exists>a. attachment_value_presents a p) \<and>
      (\<exists>b. payload_value_presents b q) \<and> t=Pair_Term p q)
      \<longleftrightarrow> (214,t)\<in>positive_meaning structural_table_system" for t
    using presentation_class.admissible_iff[OF pairs, of t] by (simp only: same structural_origin_row_exact)
  show ?thesis using pairs by (simp only: same presentation_class_def admission)
qed

lemma piece_entry_data:
  assumes "piece_entry_presents z t"
  shows "term_formed t \<and> self_contained_term t"
  using assms artifact_value_presents_formed by (auto simp: factor_pair_presents_def)

lemma origin_entry_data:
  assumes "origin_entry_presents z t"
  shows "term_formed t \<and> self_contained_term t"
  using assms by (auto simp: factor_pair_presents_def)

section \<open>Complete recursive row lists compose with the existing key check\<close>

interpretation structural_piece_rows: list_profile structural_table_system 211 212
  by (rule list_profile.intro)
    (auto simp: structural_table_clause structural_table_clause_family_def structural_table_call)

interpretation structural_origin_rows: list_profile structural_table_system 214 215
  by (rule list_profile.intro)
    (auto simp: structural_table_clause structural_table_clause_family_def structural_table_call)

lemma structural_piece_sequence:
  "(212,t)\<in>positive_meaning structural_table_system \<longleftrightarrow>
    (\<exists>xs. data_sequence_presents piece_entry_presents xs t)"
  using presentation_class.admissible_iff[OF structural_piece_rows.presentation_class[OF piece_entry_native_class], of t] by blast

lemma structural_origin_sequence:
  "(215,t)\<in>positive_meaning structural_table_system \<longleftrightarrow>
    (\<exists>xs. data_sequence_presents origin_entry_presents xs t)"
  using presentation_class.admissible_iff[OF structural_origin_rows.presentation_class[OF origin_entry_native_class], of t] by blast

interpretation structural_piece_tables: table_admission_profile structural_table_system 213 21 212
  by (rule table_admission_profile.intro)
    (auto simp: structural_table_clause structural_table_clause_family_def structural_table_call)

interpretation structural_origin_tables: table_admission_profile structural_table_system 216 21 215
  by (rule table_admission_profile.intro)
    (auto simp: structural_table_clause structural_table_clause_family_def structural_table_call)

theorem structural_piece_table_exact:
  "(213,t)\<in>positive_meaning structural_table_system \<longleftrightarrow>
    (\<exists>P. piece_family_presents payload_value_presents P t)"
proof -
  have injective: "inj Payload_Term" by (rule injI) simp
  have tables: "(213,t)\<in>positive_meaning structural_table_system \<longleftrightarrow>
      (\<exists>Q. single_valued Q \<and> data_collection_presents piece_entry_presents Q t)"
    by (rule structural_piece_tables.presented[OF injective _ piece_entry_data
      structural_table_components(3) structural_piece_sequence])
      (auto simp: factor_pair_presents_def)
  have coverage: "(\<exists>Q. single_valued Q \<and> data_collection_presents piece_entry_presents Q t)
      \<longleftrightarrow> (\<exists>P. piece_family_presents payload_value_presents P t)"
  proof
    assume "\<exists>Q. single_valued Q \<and> data_collection_presents piece_entry_presents Q t"
    then obtain Q where parts: "single_valued Q" "data_collection_presents piece_entry_presents Q t" by blast
    show "\<exists>P. piece_family_presents payload_value_presents P t"
      by (rule exI[of _ "\<lparr>piece_graph=Q\<rparr>"])
        (use parts in \<open>simp add: piece_family_presents_def data_table_presents_def\<close>)
  next
    assume "\<exists>P. piece_family_presents payload_value_presents P t"
    then show "\<exists>Q. single_valued Q \<and> data_collection_presents piece_entry_presents Q t"
      by (auto simp: piece_family_presents_def data_table_presents_def)
  qed
  show ?thesis by (simp only: tables coverage)
qed

theorem structural_origin_table_exact:
  "(216,t)\<in>positive_meaning structural_table_system \<longleftrightarrow>
    (\<exists>q. origin_table_presents payload_value_presents q t)"
proof -
  have injective: "inj address_pair_data" by (rule injI) (auto simp: address_pair_data_def)
  have tables: "(216,t)\<in>positive_meaning structural_table_system \<longleftrightarrow>
      (\<exists>Q. single_valued Q \<and> data_collection_presents origin_entry_presents Q t)"
    by (rule structural_origin_tables.presented[OF injective _ origin_entry_data
      structural_table_components(3) structural_origin_sequence])
      (auto simp: factor_pair_presents_def address_pair_data_def)
  show ?thesis by (simp only: tables data_table_presents_def)
qed

theorem piece_family_native_class:
  "presentation_class (piece_family_presents payload_value_presents) (piece_family_domain octets_formed)
    (\<lambda>t. (213,t)\<in>positive_meaning structural_table_system)"
  using piece_family_presentation_class[OF payload_value_presentation_class]
  by (simp only: structural_piece_table_exact)

theorem origin_table_native_class:
  "presentation_class (origin_table_presents payload_value_presents) (origin_table_domain octets_formed)
    (\<lambda>t. (216,t)\<in>positive_meaning structural_table_system)"
  using origin_table_presentation_class[OF payload_value_presentation_class]
  by (simp only: structural_origin_table_exact)

interpretation native_piece_families: presentation_class
  "piece_family_presents payload_value_presents" "piece_family_domain octets_formed"
  "\<lambda>t. (213,t)\<in>positive_meaning structural_table_system"
  by (rule piece_family_native_class)

interpretation native_origin_tables: presentation_class
  "origin_table_presents payload_value_presents" "origin_table_domain octets_formed"
  "\<lambda>t. (216,t)\<in>positive_meaning structural_table_system"
  by (rule origin_table_native_class)

text \<open>
  Both admissions are exact on all terms, including malformed shapes. Each
  piece value may use any complete artifact presentation. Native uniqueness
  observes only the independently encoded key; values do not become identities
  of their rows. Origin rows retain their piece slot, local source address,
  and destination address in separate product positions.
\<close>

end
