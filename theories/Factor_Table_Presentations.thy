theory Factor_Table_Presentations
  imports Factor_Presentation_Transport
begin

section \<open>A finite table is a complete functional relation\<close>

abbreviation finite_table_domain ::
  "('k\<Rightarrow>bool) \<Rightarrow> ('v\<Rightarrow>bool) \<Rightarrow> ('k\<times>'v) set \<Rightarrow> bool" where
  "finite_table_domain D E Q \<equiv>
    finite Q \<and> single_valued Q \<and> (\<forall>z\<in>Q. D (fst z) \<and> E (snd z))"

definition data_table_presents ::
  "('k\<Rightarrow>factor_term\<Rightarrow>bool) \<Rightarrow> ('v\<Rightarrow>factor_term\<Rightarrow>bool) \<Rightarrow>
    ('k\<times>'v) set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "data_table_presents K V Q t \<longleftrightarrow>
    single_valued Q \<and> data_collection_presents (factor_pair_presents K V) Q t"

theorem data_table_presentation_class:
  assumes keys: "presentation_class K D A" and value_readings: "presentation_class V E B"
  shows "presentation_class (data_table_presents K V) (finite_table_domain D E)
    (\<lambda>t. \<exists>Q. data_table_presents K V Q t)"
proof -
  have pairs: "presentation_class (factor_pair_presents K V)
      (\<lambda>z. D (fst z) \<and> E (snd z))
      (\<lambda>t. \<exists>p q. A p \<and> B q \<and> t=Pair_Term p q)"
    by (rule factor_pair_class[OF keys value_readings])
  have collections: "presentation_class (data_collection_presents (factor_pair_presents K V))
      (\<lambda>Q. finite Q \<and> (\<forall>z\<in>Q. D (fst z) \<and> E (snd z)))
      (presented_predicate (data_sequence_presents (factor_pair_presents K V)) distinct)"
    by (rule data_collection_presentation_class[OF pairs])
  have constrained: "presentation_class
      (\<lambda>Q t. finite_table_domain D E Q \<and> data_collection_presents (factor_pair_presents K V) Q t)
      (finite_table_domain D E)
      (\<lambda>t. \<exists>Q. finite_table_domain D E Q \<and> data_collection_presents (factor_pair_presents K V) Q t)"
    by (rule presentation_class_subdomain[OF collections]) blast
  have reading: "(finite_table_domain D E Q \<and> data_collection_presents (factor_pair_presents K V) Q t)
      \<longleftrightarrow> data_table_presents K V Q t" for Q t
    using presentation_class.subject_boundary[OF collections, of Q t]
    by (auto simp: data_table_presents_def)
  show ?thesis using constrained by (simp only: presentation_class_def reading)
qed

lemma data_table_elements:
  assumes table: "data_table_presents K V Q t"
    and keys: "\<And>k p. K k p \<Longrightarrow> term_formed p \<and> self_contained_term p"
    and value_readings: "\<And>v q. V v q \<Longrightarrow> term_formed q \<and> self_contained_term q"
  shows "term_formed t \<and> self_contained_term t"
proof -
  have rows: "data_collection_presents (factor_pair_presents K V) Q t"
    using table by (simp add: data_table_presents_def)
  have each: "factor_pair_presents K V z p \<Longrightarrow> term_formed p \<and> self_contained_term p" for z p
    using keys value_readings by (auto simp: factor_pair_presents_def)
  obtain ts where list: "t=data_list_term ts" "data_elements ts"
    using data_collection_presents_elements[OF rows, of "\<lambda>p. term_formed p \<and> self_contained_term p"] each by blast
  show ?thesis using list by (simp add: data_list_term_formed data_list_term_self_contained)
qed

lemma data_table_empty:
  "data_table_presents K V {} t \<longleftrightarrow> t=data_list_term []"
  by (auto simp: data_table_presents_def data_collection_presents_def single_valued_def)

lemma data_table_at_list:
  "data_table_presents K V Q (data_list_term ts) \<longleftrightarrow>
    (\<exists>xs. distinct xs \<and> set xs=Q \<and> single_valued Q \<and>
      list_all2 (factor_pair_presents K V) xs ts)"
  by (auto simp: data_table_presents_def data_collection_presents_def data_list_term_injective)

section \<open>The earlier enumeration form changes only the complete list terminator\<close>

definition enumeration_retermination :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "enumeration_retermination p q \<longleftrightarrow>
    (\<exists>ts. p=data_list_term ts \<and> q=enumeration_term ts)"

lemma enumeration_retermination_class:
  "presentation_class enumeration_retermination
    (\<lambda>p. \<exists>ts. p=data_list_term ts) (\<lambda>q. \<exists>ts. q=enumeration_term ts)"
  by (unfold_locales)
    (auto simp: enumeration_retermination_def enumeration_term_injective; blast)+

lemma finite_collection_retermination:
  "finite_collection_presents R Q q \<longleftrightarrow>
    composed_presentation (data_collection_presents R) enumeration_retermination Q q"
  by (auto simp: finite_collection_presents_def data_collection_presents_def
    composed_presentation_def enumeration_retermination_def data_list_term_injective; blast)

theorem finite_collection_presentation_class:
  assumes elements: "presentation_class R D A"
  shows "presentation_class (finite_collection_presents R)
    (\<lambda>Q. finite Q \<and> (\<forall>x\<in>Q. D x)) (\<lambda>t. \<exists>Q. finite_collection_presents R Q t)"
proof -
  have collections: "presentation_class (data_collection_presents R)
      (\<lambda>Q. finite Q \<and> (\<forall>x\<in>Q. D x))
      (presented_predicate (data_sequence_presents R) distinct)"
    by (rule data_collection_presentation_class[OF elements])
  have changed: "presentation_class
      (composed_presentation (data_collection_presents R) enumeration_retermination)
      (\<lambda>Q. finite Q \<and> (\<forall>x\<in>Q. D x))
      (\<lambda>q. (\<exists>ts. q=enumeration_term ts) \<and>
        (\<exists>p. presented_predicate (data_sequence_presents R) distinct p \<and> enumeration_retermination p q))"
    by (rule presentation_class_compose_on[OF collections enumeration_retermination_class])
      (auto simp: presented_predicate_def data_sequence_presents_def)
  have reading: "composed_presentation (data_collection_presents R) enumeration_retermination=finite_collection_presents R"
    by (intro ext) (simp only: finite_collection_retermination)
  show ?thesis
    using changed presentation_class.admissible_iff[OF changed]
    by (simp only: reading presentation_class_def; blast)
qed

theorem finite_table_presentation_class:
  assumes keys: "inj K" and value_readings: "presentation_class V E B"
  shows "presentation_class (finite_table_presents K V) (finite_table_domain (\<lambda>_. True) E)
    (\<lambda>t. \<exists>Q. finite_table_presents K V Q t)"
proof -
  have key_class: "presentation_class (\<lambda>k t. t=K k) (\<lambda>_. True) (\<lambda>t. \<exists>k. t=K k)"
    using injective_presentation_class[where f=K and D="\<lambda>_. True"] keys by simp
  have pairs: "presentation_class (factor_pair_presents (\<lambda>k t. t=K k) V)
      (\<lambda>z. E (snd z))
      (\<lambda>t. \<exists>p q. (\<exists>k. p=K k) \<and> B q \<and> t=Pair_Term p q)"
    using factor_pair_class[OF key_class value_readings] by simp
  have row: "factor_pair_presents (\<lambda>k t. t=K k) V=table_entry_presents K V"
    by (intro ext) (auto simp: factor_pair_presents_def table_entry_presents_def)
  have collections: "presentation_class (finite_collection_presents (table_entry_presents K V))
      (\<lambda>Q. finite Q \<and> (\<forall>z\<in>Q. E (snd z)))
      (\<lambda>t. \<exists>Q. finite_collection_presents (table_entry_presents K V) Q t)"
    by (rule finite_collection_presentation_class) (use pairs in \<open>simp only: row\<close>)
  have constrained: "presentation_class
      (\<lambda>Q t. finite_table_domain (\<lambda>_. True) E Q \<and> finite_collection_presents (table_entry_presents K V) Q t)
      (finite_table_domain (\<lambda>_. True) E)
      (\<lambda>t. \<exists>Q. finite_table_domain (\<lambda>_. True) E Q \<and> finite_collection_presents (table_entry_presents K V) Q t)"
    by (rule presentation_class_subdomain[OF collections]) blast
  have reading: "(finite_table_domain (\<lambda>_. True) E Q \<and> finite_collection_presents (table_entry_presents K V) Q t)
      \<longleftrightarrow> finite_table_presents K V Q t" for Q t
    using presentation_class.subject_boundary[OF collections, of Q t]
    by (auto simp: finite_table_presents_def)
  show ?thesis using constrained by (simp only: presentation_class_def reading)
qed

theorem table_enumeration_change:
  assumes keys: "inj K" and value_readings: "presentation_class V E B"
  shows "presentation_change (finite_table_presents K V) (finite_table_domain (\<lambda>_. True) E)
    (\<lambda>t. \<exists>Q. finite_table_presents K V Q t)
    (data_table_presents (\<lambda>k p. p=K k) V)
    (\<lambda>t. \<exists>Q. data_table_presents (\<lambda>k p. p=K k) V Q t)"
proof -
  have key_class: "presentation_class (\<lambda>k p. p=K k) (\<lambda>_. True) (\<lambda>p. \<exists>k. p=K k)"
    using injective_presentation_class[where f=K and D="\<lambda>_. True"] keys by simp
  show ?thesis by (rule presentation_change.intro[OF finite_table_presentation_class[OF keys value_readings]
    data_table_presentation_class[OF key_class value_readings]])
qed

text \<open>
  A table retains every key and its associated value. Distinct keys may carry
  equal values. Products supply the row roles; complete collections retain one
  occurrence of each row; functionality is a restriction on the recovered
  relation. Relational key and value classes may each have many presentations.

  The earlier enumeration form retains its existing subjects and every order.
  Its empty-list target and the data form's empty payload are accounted for by
  an exact change of the complete list terminator. The generic correspondence
  between table classes also permits different orders and component forms.
  No literal equality of their terms, native admission of arbitrary readers,
  or permission invariance follows from this mathematical correspondence.
\<close>

end
