theory Factor_Structural_Collections
  imports Factor_Collection_Comparisons Factor_Bag_Difference
begin

section \<open>Finite sets of exact opaque addresses\<close>

abbreviation payload_value_presents :: "octets \<Rightarrow> factor_term \<Rightarrow> bool" where
  "payload_value_presents a t \<equiv> octets_formed a \<and> t=Payload_Term a"

abbreviation payload_set_presents :: "octets set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "payload_set_presents \<equiv> data_collection_presents payload_value_presents"

lemma payload_value_presentation_class:
  "presentation_class payload_value_presents octets_formed (\<lambda>t. \<exists>a. payload_value_presents a t)"
  by (rule injective_presentation_class) (auto simp: inj_on_def)

lemma payload_set_enumerations:
  "payload_set_presents A p \<longleftrightarrow>
    (\<exists>xs. distinct xs \<and> set xs=A \<and> (\<forall>a\<in>A. octets_formed a) \<and>
      p=data_list_term (map Payload_Term xs))"
  by (simp only: data_collection_presents_constrain data_collection_presents_function; blast)

lemma payload_set_formed:
  assumes "payload_set_presents A p"
  shows "finite A \<and> (\<forall>a\<in>A. octets_formed a) \<and> term_formed p \<and> self_contained_term p"
  using assms by (auto simp: payload_set_enumerations data_list_term_formed data_list_term_self_contained)

lemma payload_set_unique:
  assumes "payload_set_presents A p" "payload_set_presents B p"
  shows "A=B"
  by (rule data_collection_presents_unique[OF assms]) auto

lemma payload_set_admission:
  "(1,p)\<in>positive_meaning distinct_payloads_system \<longleftrightarrow> (\<exists>A. payload_set_presents A p)"
  by (simp only: distinct_payloads_positive_exact payload_set_enumerations; auto)

theorem payload_set_presentation_class:
  "presentation_class payload_set_presents (\<lambda>A. finite A \<and> (\<forall>a\<in>A. octets_formed a))
    (\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system)"
proof -
  have raw: "presentation_class payload_set_presents (\<lambda>A. finite A \<and> (\<forall>a\<in>A. octets_formed a))
      (presented_predicate (data_sequence_presents payload_value_presents) distinct)"
    by (rule data_collection_presentation_class[OF payload_value_presentation_class])
  have admission: "presented_predicate (data_sequence_presents payload_value_presents) distinct p \<longleftrightarrow>
      (1,p)\<in>positive_meaning distinct_payloads_system" for p
    using presentation_class.admissible_iff[OF raw, of p] by (simp only: payload_set_admission)
  show ?thesis using raw by (simp only: presentation_class_def admission)
qed

interpretation payload_sets: presentation_class payload_set_presents
  "\<lambda>A. finite A \<and> (\<forall>a\<in>A. octets_formed a)"
  "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  by (rule payload_set_presentation_class)

lemma payload_set_comparison:
  assumes "payload_set_presents A p"
  shows "(6,Pair_Term p q)\<in>positive_meaning bag_comparison_system \<longleftrightarrow> payload_set_presents A q"
proof -
  have injective: "inj Payload_Term" by (rule injI) simp
  show ?thesis by (rule encoded_collection_comparison[OF injective assms])
    (use payload_set_formed[OF assms] in auto)
qed

lemma payload_value_recognition:
  "(1,data_list_term [x])\<in>positive_meaning distinct_payloads_system \<longleftrightarrow>
    (\<exists>a. payload_value_presents a x)"
  by (rule payload_recognition_exact)

lemma payload_set_selection:
  assumes source: "payload_set_presents A p"
  shows "selected_data_member x p \<longleftrightarrow> (\<exists>a. payload_value_presents a x \<and> a\<in>A)"
proof -
  obtain xs where fields: "set xs=A" "\<forall>a\<in>A. octets_formed a"
    "p=data_list_term (map Payload_Term xs)"
    using source by (auto simp: payload_set_enumerations)
  show ?thesis using fields
    by (auto simp: selected_data_member_exact data_list_term_injective)
qed

lemma payload_set_absence:
  assumes source: "payload_set_presents A p" and element: "payload_value_presents a x"
  shows "(132,Pair_Term x p)\<in>positive_meaning data_absence_system \<longleftrightarrow> a\<notin>A"
proof -
  obtain xs where fields: "set xs=A" "\<forall>a\<in>A. octets_formed a"
    "p=data_list_term (map Payload_Term xs)"
    using source by (auto simp: payload_set_enumerations)
  have formed: "term_formed x" "self_contained_term x" using element by auto
  show ?thesis using data_absence_lists[OF formed, of "map Payload_Term xs"] fields element by auto
qed

section \<open>Attachment coordinates preserve their exact atom and opaque value\<close>

abbreviation attachment_value_presents ::
  "(local_address\<times>octets) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "attachment_value_presents z t \<equiv> octets_formed (fst z) \<and> octets_formed (snd z) \<and> t=address_pair_data z"

lemma attachment_value_components:
  "attachment_value_presents z t \<longleftrightarrow> factor_pair_presents payload_value_presents payload_value_presents z t"
  by (auto simp: factor_pair_presents_def address_pair_data_def)

lemma attachment_value_presentation_class:
  "presentation_class attachment_value_presents (\<lambda>z. octets_formed (fst z) \<and> octets_formed (snd z))
    (\<lambda>t. \<exists>z. attachment_value_presents z t)"
proof -
  have pair: "presentation_class (factor_pair_presents payload_value_presents payload_value_presents)
      (\<lambda>z. octets_formed (fst z) \<and> octets_formed (snd z))
      (\<lambda>t. \<exists>p q. (\<exists>a. payload_value_presents a p) \<and>
        (\<exists>b. payload_value_presents b q) \<and> t=Pair_Term p q)"
    by (rule factor_pair_class[OF payload_value_presentation_class payload_value_presentation_class])
  have admission: "(\<exists>p q. (\<exists>a. payload_value_presents a p) \<and>
      (\<exists>b. payload_value_presents b q) \<and> t=Pair_Term p q) \<longleftrightarrow>
      (\<exists>z. attachment_value_presents z t)" for t
    using presentation_class.admissible_iff[OF pair, of t] by (simp only: attachment_value_components)
  show ?thesis using pair by (simp only: presentation_class_def attachment_value_components admission)
qed

section \<open>Incidence triples keep all three exact coordinates\<close>

abbreviation incidence_coordinates_formed :: "(local_address\<times>local_address\<times>local_address) \<Rightarrow> bool" where
  "incidence_coordinates_formed z \<equiv> octets_formed (fst z) \<and>
    octets_formed (fst (snd z)) \<and> octets_formed (snd (snd z))"

abbreviation incidence_value_presents ::
  "(local_address\<times>local_address\<times>local_address) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "incidence_value_presents z t \<equiv> incidence_coordinates_formed z \<and> t=incidence_data z"

abbreviation incidence_set_presents ::
  "(local_address\<times>local_address\<times>local_address) set \<Rightarrow> factor_term \<Rightarrow> bool" where
  "incidence_set_presents \<equiv> data_collection_presents incidence_value_presents"

lemma incidence_value_components:
  "incidence_value_presents z t \<longleftrightarrow> factor_pair_presents payload_value_presents attachment_value_presents z t"
  by (auto simp: factor_pair_presents_def incidence_data_def address_pair_data_def)

lemma incidence_value_presentation_class:
  "presentation_class incidence_value_presents incidence_coordinates_formed
    (\<lambda>t. \<exists>z. incidence_value_presents z t)"
proof -
  have pair: "presentation_class (factor_pair_presents payload_value_presents attachment_value_presents)
      incidence_coordinates_formed
      (\<lambda>t. \<exists>p q. (\<exists>a. payload_value_presents a p) \<and>
        (\<exists>z. attachment_value_presents z q) \<and> t=Pair_Term p q)"
    by (rule factor_pair_class[OF payload_value_presentation_class attachment_value_presentation_class])
  have admission: "(\<exists>p q. (\<exists>a. payload_value_presents a p) \<and>
      (\<exists>z. attachment_value_presents z q) \<and> t=Pair_Term p q) \<longleftrightarrow>
      (\<exists>z. incidence_value_presents z t)" for t
    using presentation_class.admissible_iff[OF pair, of t] by (simp only: incidence_value_components)
  show ?thesis using pair by (simp only: presentation_class_def incidence_value_components admission)
qed

theorem incidence_set_presentation_class:
  "presentation_class incidence_set_presents
    (\<lambda>A. finite A \<and> (\<forall>z\<in>A. incidence_coordinates_formed z))
    (presented_predicate (data_sequence_presents incidence_value_presents) distinct)"
  by (rule data_collection_presentation_class[OF incidence_value_presentation_class])

lemma incidence_set_enumerations:
  "incidence_set_presents A p \<longleftrightarrow>
    (\<exists>xs. distinct xs \<and> set xs=A \<and> (\<forall>z\<in>A. incidence_coordinates_formed z) \<and>
      p=data_list_term (map incidence_data xs))"
  by (simp only: data_collection_presents_constrain data_collection_presents_function; blast)

lemma incidence_set_formed:
  assumes "incidence_set_presents A p"
  shows "finite A \<and> (\<forall>z\<in>A. incidence_coordinates_formed z) \<and> term_formed p \<and> self_contained_term p"
proof -
  obtain xs where fields: "set xs=A" "\<forall>z\<in>A. incidence_coordinates_formed z"
    "p=data_list_term (map incidence_data xs)"
    using assms by (simp only: incidence_set_enumerations; blast)
  show ?thesis using fields by (auto simp: data_list_term_formed data_list_term_self_contained
    incidence_data_def address_pair_data_def)
qed

lemma incidence_set_comparison:
  assumes "incidence_set_presents A p"
  shows "(6,Pair_Term p q)\<in>positive_meaning bag_comparison_system \<longleftrightarrow> incidence_set_presents A q"
  by (rule encoded_collection_comparison[OF incidence_data_injective assms])
    (use incidence_set_formed[OF assms] in \<open>auto simp: incidence_data_def address_pair_data_def\<close>)

text \<open>
  Both classes use the general complete-collection construction over their
  independently formed elements. Every finite set and every complete order is
  admitted. Triple positions remain distinct, while equal addresses may occupy
  several positions. The set condition excludes duplicate triples, not repeated
  coordinates inside a triple.
\<close>

end
