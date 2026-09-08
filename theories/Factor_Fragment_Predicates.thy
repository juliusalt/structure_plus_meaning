theory Factor_Fragment_Predicates
  imports Factor_Fragment_Equations Presentation_Contracts
begin

section \<open>Payload membership is exact at every complete selection\<close>

lemma fragment_payload_recognition:
  "(1,data_list_term [x])\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a. payload_value_presents a x)"
  by (simp only: fragment_components(1) payload_set_admission[symmetric] payload_value_recognition)

lemma fragment_payload_inside_at_selection:
  assumes source: "payload_set_presents A p"
  shows "(189,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a. payload_value_presents a x \<and> a\<in>A)"
proof -
  have raw: "(189,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (\<exists>B. payload_set_presents B p) \<and> selected_data_member x p"
    by (simp only: fragment_payload_inside_calls factor_term.inject fragment_components(1,2); blast)
  show ?thesis using source by (simp only: raw payload_set_selection[OF source]; blast)
qed

lemma fragment_payload_outside_at_selection:
  assumes source: "payload_set_presents A p"
  shows "(190,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a. payload_value_presents a x \<and> a\<notin>A)"
proof -
  have raw: "(190,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (1,p)\<in>positive_meaning fragment_system \<and>
      (1,data_list_term [x])\<in>positive_meaning fragment_system \<and>
      (132,Pair_Term x p)\<in>positive_meaning fragment_system"
    using fragment_payload_outside_calls[of "Pair_Term p x"]
    by (simp only: factor_term.inject; blast)
  have admitted: "(1,p)\<in>positive_meaning fragment_system"
    by (simp only: fragment_components(1); use source in blast)
  show ?thesis
    by (simp only: raw admitted simp_thms fragment_payload_recognition fragment_components(6);
      use payload_set_absence[OF source] in blast)
qed

section \<open>Each compound relation preserves all coordinate positions\<close>

lemma fragment_attachment_inside_at_selection:
  assumes source: "payload_set_presents A p"
  shows "(191,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a. attachment_value_presents a x \<and> fst a\<in>A)"
proof -
  have raw: "(191,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (\<exists>a b. x=Pair_Term a b \<and>
        (189,Pair_Term p a)\<in>positive_meaning fragment_system \<and> (1,data_list_term [b])\<in>positive_meaning fragment_system)"
    using fragment_attachment_inside_calls[of "Pair_Term p x"] by (simp only: factor_term.inject; blast)
  show ?thesis
    by (simp only: raw fragment_payload_inside_at_selection[OF source]
      fragment_payload_outside_at_selection[OF source] fragment_payload_recognition)
      (auto simp: incidence_data_def address_pair_data_def split_paired_Ex; blast)
qed

lemma fragment_attachment_outside_at_selection:
  assumes source: "payload_set_presents A p"
  shows "(192,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a. attachment_value_presents a x \<and> fst a\<notin>A)"
proof -
  have raw: "(192,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (\<exists>a b. x=Pair_Term a b \<and>
        (190,Pair_Term p a)\<in>positive_meaning fragment_system \<and> (1,data_list_term [b])\<in>positive_meaning fragment_system)"
    using fragment_attachment_outside_calls[of "Pair_Term p x"] by (simp only: factor_term.inject; blast)
  show ?thesis
    by (simp only: raw fragment_payload_inside_at_selection[OF source]
      fragment_payload_outside_at_selection[OF source] fragment_payload_recognition)
      (auto simp: incidence_data_def address_pair_data_def split_paired_Ex; blast)
qed

lemma fragment_incidence_inside_at_selection:
  assumes source: "payload_set_presents A p"
  shows "(193,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a. incidence_value_presents a x \<and> incidence_inside A a)"
proof -
  have raw: "(193,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (\<exists>a b c. x=Pair_Term a (Pair_Term b c) \<and>
        (189,Pair_Term p a)\<in>positive_meaning fragment_system \<and>
        (189,Pair_Term p b)\<in>positive_meaning fragment_system \<and>
        (189,Pair_Term p c)\<in>positive_meaning fragment_system)"
    using fragment_incidence_inside_calls[of "Pair_Term p x"] by (simp only: factor_term.inject; blast)
  show ?thesis
    by (simp only: raw fragment_payload_inside_at_selection[OF source]
      fragment_payload_outside_at_selection[OF source] fragment_payload_recognition)
      (auto simp: incidence_data_def address_pair_data_def split_paired_Ex; blast)
qed

lemma fragment_incidence_not_inside_at_selection:
  assumes source: "payload_set_presents A p"
  shows "(194,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a. incidence_value_presents a x \<and> \<not>incidence_inside A a)"
proof -
  have raw: "(194,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (\<exists>a b c. x=Pair_Term a (Pair_Term b c) \<and>
        (((190,Pair_Term p a)\<in>positive_meaning fragment_system \<and> (1,data_list_term [b])\<in>positive_meaning fragment_system \<and> (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
        ((190,Pair_Term p b)\<in>positive_meaning fragment_system \<and> (1,data_list_term [a])\<in>positive_meaning fragment_system \<and> (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
        ((190,Pair_Term p c)\<in>positive_meaning fragment_system \<and> (1,data_list_term [a])\<in>positive_meaning fragment_system \<and> (1,data_list_term [b])\<in>positive_meaning fragment_system)))"
    using fragment_incidence_not_inside_calls[of "Pair_Term p x"] by (simp only: factor_term.inject; blast)
  show ?thesis
    by (simp only: raw fragment_payload_inside_at_selection[OF source]
      fragment_payload_outside_at_selection[OF source] fragment_payload_recognition)
      (auto simp: incidence_data_def address_pair_data_def split_paired_Ex; blast)
qed

lemma fragment_incidence_outside_at_selection:
  assumes source: "payload_set_presents A p"
  shows "(195,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a. incidence_value_presents a x \<and> incidence_inside (-A) a)"
proof -
  have raw: "(195,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (\<exists>a b c. x=Pair_Term a (Pair_Term b c) \<and>
        (190,Pair_Term p a)\<in>positive_meaning fragment_system \<and>
        (190,Pair_Term p b)\<in>positive_meaning fragment_system \<and>
        (190,Pair_Term p c)\<in>positive_meaning fragment_system)"
    using fragment_incidence_outside_calls[of "Pair_Term p x"] by (simp only: factor_term.inject; blast)
  show ?thesis
    by (simp only: raw fragment_payload_inside_at_selection[OF source]
      fragment_payload_outside_at_selection[OF source] fragment_payload_recognition)
      (auto simp: incidence_data_def address_pair_data_def split_paired_Ex; blast)
qed

lemma fragment_incidence_not_outside_at_selection:
  assumes source: "payload_set_presents A p"
  shows "(196,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>a. incidence_value_presents a x \<and> \<not>incidence_inside (-A) a)"
proof -
  have raw: "(196,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (\<exists>a b c. x=Pair_Term a (Pair_Term b c) \<and>
        (((189,Pair_Term p a)\<in>positive_meaning fragment_system \<and> (1,data_list_term [b])\<in>positive_meaning fragment_system \<and> (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
        ((189,Pair_Term p b)\<in>positive_meaning fragment_system \<and> (1,data_list_term [a])\<in>positive_meaning fragment_system \<and> (1,data_list_term [c])\<in>positive_meaning fragment_system) \<or>
        ((189,Pair_Term p c)\<in>positive_meaning fragment_system \<and> (1,data_list_term [a])\<in>positive_meaning fragment_system \<and> (1,data_list_term [b])\<in>positive_meaning fragment_system)))"
    using fragment_incidence_not_outside_calls[of "Pair_Term p x"] by (simp only: factor_term.inject; blast)
  show ?thesis
    by (simp only: raw fragment_payload_inside_at_selection[OF source]
      fragment_payload_outside_at_selection[OF source] fragment_payload_recognition)
      (auto simp: incidence_data_def address_pair_data_def split_paired_Ex; blast)
qed

section \<open>The complete relation contract also covers malformed arguments\<close>

lemma fragment_predicate_source:
  assumes "d\<in>{189,190,191,192,193,194,195,196}" "(d,t)\<in>positive_meaning fragment_system"
  shows "\<exists>A p x. payload_set_presents A p \<and> t=Pair_Term p x"
  using assms by (auto simp only: insert_iff empty_iff factor_term.inject
    fragment_payload_inside_calls fragment_payload_outside_calls
    fragment_attachment_inside_calls fragment_attachment_outside_calls
    fragment_incidence_inside_calls fragment_incidence_outside_calls
    fragment_incidence_not_inside_calls fragment_incidence_not_outside_calls fragment_components(1); blast)

lemma fragment_predicate_exact_from_source:
  assumes entry: "d\<in>{189,190,191,192,193,194,195,196}"
    and meaning: "\<And>A p x. payload_set_presents A p \<Longrightarrow>
      (d,Pair_Term p x)\<in>positive_meaning fragment_system \<longleftrightarrow> (\<exists>a. S a x \<and> L A a)"
  shows "(d,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p x. t=Pair_Term p x \<and> presented_relation payload_set_presents S L p x)"
proof
  assume holds: "(d,t)\<in>positive_meaning fragment_system"
  obtain A p x where source: "payload_set_presents A p" and shape: "t=Pair_Term p x"
    using fragment_predicate_source[OF entry holds] by blast
  obtain a where element: "S a x" and related: "L A a"
    using holds by (simp only: shape meaning[OF source]; blast)
  show "\<exists>p x. t=Pair_Term p x \<and> presented_relation payload_set_presents S L p x"
    using source shape element related by (auto simp: presented_relation_def)
next
  assume "\<exists>p x. t=Pair_Term p x \<and> presented_relation payload_set_presents S L p x"
  then obtain p x A a where shape: "t=Pair_Term p x"
    and source: "payload_set_presents A p" and element: "S a x" and related: "L A a"
    by (auto simp: presented_relation_def)
  show "(d,t)\<in>positive_meaning fragment_system"
    by (simp only: shape meaning[OF source]) (use element related in blast)
qed

theorem fragment_payload_inside_exact:
  "(189,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p x. t=Pair_Term p x \<and>
      presented_relation payload_set_presents payload_value_presents (\<lambda>A a. a\<in>A) p x)"
  by (rule fragment_predicate_exact_from_source[OF _ fragment_payload_inside_at_selection]) simp

interpretation fragment_payload_inside_relation: presented_relation_contract
  payload_set_presents "\<lambda>A. finite A \<and> (\<forall>a\<in>A. octets_formed a)"
    "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  payload_value_presents "octets_formed" "\<lambda>x. \<exists>a. payload_value_presents a x"
  "\<lambda>A a. a\<in>A" "\<lambda>p x. (189,Pair_Term p x)\<in>positive_meaning fragment_system"
  by (rule presented_relation_contract.intro[OF payload_set_presentation_class payload_value_presentation_class])
    (simp only: presented_relation_contract_axioms_def fragment_payload_inside_exact factor_term.inject; blast)

theorem fragment_payload_outside_exact:
  "(190,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p x. t=Pair_Term p x \<and>
      presented_relation payload_set_presents payload_value_presents (\<lambda>A a. a\<notin>A) p x)"
  by (rule fragment_predicate_exact_from_source[OF _ fragment_payload_outside_at_selection]) simp

interpretation fragment_payload_outside_relation: presented_relation_contract
  payload_set_presents "\<lambda>A. finite A \<and> (\<forall>a\<in>A. octets_formed a)"
    "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  payload_value_presents "octets_formed" "\<lambda>x. \<exists>a. payload_value_presents a x"
  "\<lambda>A a. a\<notin>A" "\<lambda>p x. (190,Pair_Term p x)\<in>positive_meaning fragment_system"
  by (rule presented_relation_contract.intro[OF payload_set_presentation_class payload_value_presentation_class])
    (simp only: presented_relation_contract_axioms_def fragment_payload_outside_exact factor_term.inject; blast)

theorem fragment_attachment_inside_exact:
  "(191,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p x. t=Pair_Term p x \<and>
      presented_relation payload_set_presents attachment_value_presents (\<lambda>A z. fst z\<in>A) p x)"
  by (rule fragment_predicate_exact_from_source[OF _ fragment_attachment_inside_at_selection]) simp

interpretation fragment_attachment_inside_relation: presented_relation_contract
  payload_set_presents "\<lambda>A. finite A \<and> (\<forall>a\<in>A. octets_formed a)"
    "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  attachment_value_presents "\<lambda>z. octets_formed (fst z) \<and> octets_formed (snd z)" "\<lambda>x. \<exists>a. attachment_value_presents a x"
  "\<lambda>A z. fst z\<in>A" "\<lambda>p x. (191,Pair_Term p x)\<in>positive_meaning fragment_system"
  by (rule presented_relation_contract.intro[OF payload_set_presentation_class attachment_value_presentation_class])
    (simp only: presented_relation_contract_axioms_def fragment_attachment_inside_exact factor_term.inject; blast)

theorem fragment_attachment_outside_exact:
  "(192,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p x. t=Pair_Term p x \<and>
      presented_relation payload_set_presents attachment_value_presents (\<lambda>A z. fst z\<notin>A) p x)"
  by (rule fragment_predicate_exact_from_source[OF _ fragment_attachment_outside_at_selection]) simp

interpretation fragment_attachment_outside_relation: presented_relation_contract
  payload_set_presents "\<lambda>A. finite A \<and> (\<forall>a\<in>A. octets_formed a)"
    "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  attachment_value_presents "\<lambda>z. octets_formed (fst z) \<and> octets_formed (snd z)" "\<lambda>x. \<exists>a. attachment_value_presents a x"
  "\<lambda>A z. fst z\<notin>A" "\<lambda>p x. (192,Pair_Term p x)\<in>positive_meaning fragment_system"
  by (rule presented_relation_contract.intro[OF payload_set_presentation_class attachment_value_presentation_class])
    (simp only: presented_relation_contract_axioms_def fragment_attachment_outside_exact factor_term.inject; blast)

theorem fragment_incidence_inside_exact:
  "(193,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p x. t=Pair_Term p x \<and>
      presented_relation payload_set_presents incidence_value_presents (incidence_inside) p x)"
  by (rule fragment_predicate_exact_from_source[OF _ fragment_incidence_inside_at_selection]) simp

interpretation fragment_incidence_inside_relation: presented_relation_contract
  payload_set_presents "\<lambda>A. finite A \<and> (\<forall>a\<in>A. octets_formed a)"
    "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  incidence_value_presents "incidence_coordinates_formed" "\<lambda>x. \<exists>a. incidence_value_presents a x"
  "incidence_inside" "\<lambda>p x. (193,Pair_Term p x)\<in>positive_meaning fragment_system"
  by (rule presented_relation_contract.intro[OF payload_set_presentation_class incidence_value_presentation_class])
    (simp only: presented_relation_contract_axioms_def fragment_incidence_inside_exact factor_term.inject; blast)

theorem fragment_incidence_not_inside_exact:
  "(194,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p x. t=Pair_Term p x \<and>
      presented_relation payload_set_presents incidence_value_presents (\<lambda>A z. \<not>incidence_inside A z) p x)"
  by (rule fragment_predicate_exact_from_source[OF _ fragment_incidence_not_inside_at_selection]) simp

interpretation fragment_incidence_not_inside_relation: presented_relation_contract
  payload_set_presents "\<lambda>A. finite A \<and> (\<forall>a\<in>A. octets_formed a)"
    "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  incidence_value_presents "incidence_coordinates_formed" "\<lambda>x. \<exists>a. incidence_value_presents a x"
  "\<lambda>A z. \<not>incidence_inside A z" "\<lambda>p x. (194,Pair_Term p x)\<in>positive_meaning fragment_system"
  by (rule presented_relation_contract.intro[OF payload_set_presentation_class incidence_value_presentation_class])
    (simp only: presented_relation_contract_axioms_def fragment_incidence_not_inside_exact factor_term.inject; blast)

theorem fragment_incidence_outside_exact:
  "(195,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p x. t=Pair_Term p x \<and>
      presented_relation payload_set_presents incidence_value_presents (\<lambda>A z. incidence_inside (-A) z) p x)"
  by (rule fragment_predicate_exact_from_source[OF _ fragment_incidence_outside_at_selection]) simp

interpretation fragment_incidence_outside_relation: presented_relation_contract
  payload_set_presents "\<lambda>A. finite A \<and> (\<forall>a\<in>A. octets_formed a)"
    "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  incidence_value_presents "incidence_coordinates_formed" "\<lambda>x. \<exists>a. incidence_value_presents a x"
  "\<lambda>A z. incidence_inside (-A) z" "\<lambda>p x. (195,Pair_Term p x)\<in>positive_meaning fragment_system"
  by (rule presented_relation_contract.intro[OF payload_set_presentation_class incidence_value_presentation_class])
    (simp only: presented_relation_contract_axioms_def fragment_incidence_outside_exact factor_term.inject; blast)

theorem fragment_incidence_not_outside_exact:
  "(196,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>p x. t=Pair_Term p x \<and>
      presented_relation payload_set_presents incidence_value_presents (\<lambda>A z. \<not>incidence_inside (-A) z) p x)"
  by (rule fragment_predicate_exact_from_source[OF _ fragment_incidence_not_outside_at_selection]) simp

interpretation fragment_incidence_not_outside_relation: presented_relation_contract
  payload_set_presents "\<lambda>A. finite A \<and> (\<forall>a\<in>A. octets_formed a)"
    "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  incidence_value_presents "incidence_coordinates_formed" "\<lambda>x. \<exists>a. incidence_value_presents a x"
  "\<lambda>A z. \<not>incidence_inside (-A) z" "\<lambda>p x. (196,Pair_Term p x)\<in>positive_meaning fragment_system"
  by (rule presented_relation_contract.intro[OF payload_set_presentation_class incidence_value_presentation_class])
    (simp only: presented_relation_contract_axioms_def fragment_incidence_not_outside_exact factor_term.inject; blast)

text \<open>
  The eight local contracts present membership, attachment membership, and
  the two independent incidence conditions together with their complements.
  Their subject domains are the complete finite selection and complete
  element domains. Equal addresses at different triple positions are valid.

  The native complementary clauses supply explicit positive evidence and
  retain element admission. Generic presentation transport, specialization,
  and composition are available from these owned contracts; later filtering
  and assembly uses need not enlarge their semantic boundary.
\<close>

end
