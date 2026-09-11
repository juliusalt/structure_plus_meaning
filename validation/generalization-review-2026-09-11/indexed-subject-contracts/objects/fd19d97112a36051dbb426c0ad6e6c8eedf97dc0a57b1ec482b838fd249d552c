theory Factor_Table_Boundaries
  imports Factor_Table_Presentations Factor_Finite_Set_Presentations
begin

section \<open>Element boundaries lift through the complete table\<close>

lemma data_table_presents_constrain:
  "data_table_presents (\<lambda>k p. D k \<and> K k p) (\<lambda>v q. E v \<and> V v q) Q t \<longleftrightarrow>
    (\<forall>z\<in>Q. D (fst z) \<and> E (snd z)) \<and> data_table_presents K V Q t"
proof -
  have row: "factor_pair_presents (\<lambda>k p. D k \<and> K k p) (\<lambda>v q. E v \<and> V v q)=
      (\<lambda>z t. (D (fst z) \<and> E (snd z)) \<and> factor_pair_presents K V z t)"
    by (intro ext) (auto simp: factor_pair_presents_def)
  show ?thesis by (simp only: data_table_presents_def row data_collection_presents_constrain; blast)
qed

lemma data_table_presents_formed:
  assumes table: "data_table_presents K V Q t"
    and keys: "\<And>k p. K k p \<Longrightarrow> term_formed p"
    and "values": "\<And>v q. V v q \<Longrightarrow> term_formed q"
  shows "term_formed t"
  by (rule data_collection_presents_formed[OF conjunct2[OF table[unfolded data_table_presents_def]]])
    (use keys "values" in \<open>auto simp: factor_pair_presents_def\<close>)

lemma data_table_literal_boundaries:
  "data_table_presents (\<lambda>k p. D k \<and> p=f k) (\<lambda>v q. E v \<and> q=g v) Q t \<longleftrightarrow>
    (\<forall>z\<in>Q. D (fst z) \<and> E (snd z)) \<and>
    data_table_presents (\<lambda>k p. p=f k) (\<lambda>v q. q=g v) Q t"
  by (rule data_table_presents_constrain)

section \<open>The existing enumeration terminator transports relational tables\<close>

theorem reterminated_table_presentation_class:
  assumes keys: "presentation_class K D A" and "values": "presentation_class V E B"
  shows "presentation_class
    (composed_presentation (data_table_presents K V) enumeration_retermination)
    (finite_table_domain D E)
    (\<lambda>q. \<exists>Q. composed_presentation (data_table_presents K V) enumeration_retermination Q q)"
proof -
  have source: "presentation_class (data_table_presents K V) (finite_table_domain D E)
      (\<lambda>p. \<exists>Q. data_table_presents K V Q p)"
    by (rule data_table_presentation_class[OF keys "values"])
  have composed: "presentation_class
      (composed_presentation (data_table_presents K V) enumeration_retermination)
      (finite_table_domain D E)
      (\<lambda>q. (\<exists>ts. q=enumeration_term ts) \<and>
        (\<exists>p. (\<exists>Q. data_table_presents K V Q p) \<and> enumeration_retermination p q))"
    by (rule presentation_class_compose_on[OF source enumeration_retermination_class])
      (auto simp: data_table_presents_def data_collection_presents_def)
  show ?thesis using composed presentation_class.admissible_iff[OF composed]
    by (simp only: presentation_class_def; blast)
qed

lemma reterminated_literal_table_boundaries:
  "composed_presentation
      (data_table_presents (\<lambda>k p. D k \<and> p=f k) (\<lambda>v q. E v \<and> q=g v))
      enumeration_retermination Q t \<longleftrightarrow>
    (\<forall>z\<in>Q. D (fst z) \<and> E (snd z)) \<and>
      finite_table_presents f (\<lambda>v q. q=g v) Q t"
  by (auto simp: composed_presentation_def data_table_literal_boundaries finite_table_retermination)

text \<open>
  Restricting keys and values restricts every actual row of the same complete
  table. The table retains its keys, functionality, and all allowed row orders.
  Term formation needs formed component terms; it does not require that values
  be self-contained. Retermination transports relational component classes as
  well as literal encodings and preserves the actual supplied enumeration.
\<close>

end
