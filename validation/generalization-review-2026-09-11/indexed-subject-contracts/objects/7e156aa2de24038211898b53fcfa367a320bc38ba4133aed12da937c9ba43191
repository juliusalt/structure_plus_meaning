theory Factor_Fragment_Filters
  imports Factor_Fragment_Predicates
begin

section \<open>The actual complementary contracts instantiate the generic filter\<close>

lemma fragment_filter_profile:
  assumes member: "d\<in>system_definitions fragment_group_system"
    and family: "fragment_clause_family d=context_filter_clauses 1 keep omission_site d"
    and elements: "presentation_class S E B"
    and element_formed: "\<And>a x. S a x \<Longrightarrow> term_formed x \<and> self_contained_term x"
    and selected: "\<And>t. (keep,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (\<exists>p x. t=Pair_Term p x \<and> presented_relation payload_set_presents S L p x)"
    and omitted: "\<And>t. (omission_site,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (\<exists>p x. t=Pair_Term p x \<and> presented_relation payload_set_presents S (\<lambda>A a. \<not>L A a) p x)"
  shows "context_filter_profile fragment_system 1 keep omission_site d
    (\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system)
    (\<lambda>p x. B x) (presented_relation payload_set_presents S L)"
proof (rule presented_context_filter_profile[OF payload_set_presentation_class elements _ element_formed
    fragment_system_formed _ _ _ selected omitted])
  show "payload_set_presents A p \<Longrightarrow> term_formed p \<and> self_contained_term p" for A p
    using payload_set_formed by blast
  show "((d,c),T)\<in>system_clauses fragment_system \<longleftrightarrow>
      (c,T)\<in>context_filter_clauses 1 keep omission_site d" for c T
    by (simp only: fragment_clause[OF member] family)
  show "schema_call_formed fragment_system d t \<longleftrightarrow> term_formed t" for t
    using member by (auto simp: fragment_call)
  show "(1,p)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (1,p)\<in>positive_meaning distinct_payloads_system" for p
    by (simp only: fragment_components(1) payload_set_admission)
qed

interpretation fragment_selected_payloads: context_filter_profile fragment_system 1 189 190 197
  "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  "\<lambda>p x. \<exists>a. payload_value_presents a x"
  "presented_relation payload_set_presents payload_value_presents (\<lambda>A a. a\<in>A)"
  by (rule fragment_filter_profile[OF _ _ payload_value_presentation_class])
    (auto simp: fragment_clause_family_def fragment_payload_inside_exact fragment_payload_outside_exact
      incidence_data_def address_pair_data_def)

interpretation fragment_omitted_payloads: context_filter_profile fragment_system 1 190 189 198
  "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  "\<lambda>p x. \<exists>a. payload_value_presents a x"
  "presented_relation payload_set_presents payload_value_presents (\<lambda>A a. a\<notin>A)"
  by (rule fragment_filter_profile[OF _ _ payload_value_presentation_class])
    (auto simp: fragment_clause_family_def fragment_payload_outside_exact fragment_payload_inside_exact
      incidence_data_def address_pair_data_def)

interpretation fragment_selected_attachments: context_filter_profile fragment_system 1 191 192 199
  "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  "\<lambda>p x. \<exists>a. attachment_value_presents a x"
  "presented_relation payload_set_presents attachment_value_presents (\<lambda>A a. fst a\<in>A)"
  by (rule fragment_filter_profile[OF _ _ attachment_value_presentation_class])
    (auto simp: fragment_clause_family_def fragment_attachment_inside_exact fragment_attachment_outside_exact
      incidence_data_def address_pair_data_def)

interpretation fragment_omitted_attachments: context_filter_profile fragment_system 1 192 191 200
  "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  "\<lambda>p x. \<exists>a. attachment_value_presents a x"
  "presented_relation payload_set_presents attachment_value_presents (\<lambda>A a. fst a\<notin>A)"
  by (rule fragment_filter_profile[OF _ _ attachment_value_presentation_class])
    (auto simp: fragment_clause_family_def fragment_attachment_outside_exact fragment_attachment_inside_exact
      incidence_data_def address_pair_data_def)

interpretation fragment_internal_incidence: context_filter_profile fragment_system 1 193 194 201
  "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  "\<lambda>p x. \<exists>a. incidence_value_presents a x"
  "presented_relation payload_set_presents incidence_value_presents (incidence_inside)"
  by (rule fragment_filter_profile[OF _ _ incidence_value_presentation_class])
    (auto simp: fragment_clause_family_def fragment_incidence_inside_exact fragment_incidence_not_inside_exact
      incidence_data_def address_pair_data_def)

interpretation fragment_external_incidence: context_filter_profile fragment_system 1 195 196 202
  "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  "\<lambda>p x. \<exists>a. incidence_value_presents a x"
  "presented_relation payload_set_presents incidence_value_presents (\<lambda>A z. incidence_inside (-A) z)"
  by (rule fragment_filter_profile[OF _ _ incidence_value_presentation_class])
    (auto simp: fragment_clause_family_def fragment_incidence_outside_exact fragment_incidence_not_outside_exact
      incidence_data_def address_pair_data_def)

interpretation fragment_noninternal_incidence: context_filter_profile fragment_system 1 194 193 203
  "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  "\<lambda>p x. \<exists>a. incidence_value_presents a x"
  "presented_relation payload_set_presents incidence_value_presents (\<lambda>A z. \<not>incidence_inside A z)"
  by (rule fragment_filter_profile[OF _ _ incidence_value_presentation_class])
    (auto simp: fragment_clause_family_def fragment_incidence_not_inside_exact fragment_incidence_inside_exact
      incidence_data_def address_pair_data_def conj_commute conj_left_commute conj_assoc)

interpretation fragment_touching_incidence: context_filter_profile fragment_system 1 196 195 204
  "\<lambda>p. (1,p)\<in>positive_meaning distinct_payloads_system"
  "\<lambda>p x. \<exists>a. incidence_value_presents a x"
  "presented_relation payload_set_presents incidence_value_presents (\<lambda>A z. \<not>incidence_inside (-A) z)"
  by (rule fragment_filter_profile[OF _ _ incidence_value_presentation_class])
    (auto simp: fragment_clause_family_def fragment_incidence_not_outside_exact fragment_incidence_outside_exact
      incidence_data_def address_pair_data_def)

section \<open>Encoded lists retain exactly their selected occurrences\<close>

theorem fragment_selected_payloads_at_selection:
  assumes source: "payload_set_presents A p" and elements: "\<forall>a\<in>set xs. (octets_formed) a"
  shows "(197,Pair_Term p (Pair_Term (data_list_term (map Payload_Term xs)) q))\<in>positive_meaning fragment_system
    \<longleftrightarrow> q=data_list_term (map Payload_Term (filter (\<lambda>a. a\<in>A) xs))"
proof (rule fragment_selected_payloads.encoded_input)
  show "(1,p)\<in>positive_meaning distinct_payloads_system"
    using source by (simp only: payload_set_admission; blast)
  show "\<exists>b. payload_value_presents b (Payload_Term a)" if "a\<in>set xs" for a
    using elements that by auto
  show "presented_relation payload_set_presents payload_value_presents (\<lambda>A a. a\<in>A) p (Payload_Term a) \<longleftrightarrow> a\<in>A"
    if "a\<in>set xs" for a
    by (rule presented_relation_at[OF payload_set_presentation_class payload_value_presentation_class source])
      (use elements that in auto)
qed

theorem fragment_omitted_payloads_at_selection:
  assumes source: "payload_set_presents A p" and elements: "\<forall>a\<in>set xs. (octets_formed) a"
  shows "(198,Pair_Term p (Pair_Term (data_list_term (map Payload_Term xs)) q))\<in>positive_meaning fragment_system
    \<longleftrightarrow> q=data_list_term (map Payload_Term (filter (\<lambda>a. a\<notin>A) xs))"
proof (rule fragment_omitted_payloads.encoded_input)
  show "(1,p)\<in>positive_meaning distinct_payloads_system"
    using source by (simp only: payload_set_admission; blast)
  show "\<exists>b. payload_value_presents b (Payload_Term a)" if "a\<in>set xs" for a
    using elements that by auto
  show "presented_relation payload_set_presents payload_value_presents (\<lambda>A a. a\<notin>A) p (Payload_Term a) \<longleftrightarrow> a\<notin>A"
    if "a\<in>set xs" for a
    by (rule presented_relation_at[OF payload_set_presentation_class payload_value_presentation_class source])
      (use elements that in auto)
qed

theorem fragment_selected_attachments_at_selection:
  assumes source: "payload_set_presents A p" and elements: "\<forall>a\<in>set xs. (\<lambda>z. octets_formed (fst z) \<and> octets_formed (snd z)) a"
  shows "(199,Pair_Term p (Pair_Term (data_list_term (map address_pair_data xs)) q))\<in>positive_meaning fragment_system
    \<longleftrightarrow> q=data_list_term (map address_pair_data (filter (\<lambda>a. fst a\<in>A) xs))"
proof (rule fragment_selected_attachments.encoded_input)
  show "(1,p)\<in>positive_meaning distinct_payloads_system"
    using source by (simp only: payload_set_admission; blast)
  show "\<exists>b. attachment_value_presents b (address_pair_data a)" if "a\<in>set xs" for a
    by (rule exI[of _ a]) (use elements that in auto)
  show "presented_relation payload_set_presents attachment_value_presents (\<lambda>A a. fst a\<in>A) p (address_pair_data a) \<longleftrightarrow> fst a\<in>A"
    if "a\<in>set xs" for a
    by (rule presented_relation_at[OF payload_set_presentation_class attachment_value_presentation_class source])
      (use elements that in auto)
qed

theorem fragment_omitted_attachments_at_selection:
  assumes source: "payload_set_presents A p" and elements: "\<forall>a\<in>set xs. (\<lambda>z. octets_formed (fst z) \<and> octets_formed (snd z)) a"
  shows "(200,Pair_Term p (Pair_Term (data_list_term (map address_pair_data xs)) q))\<in>positive_meaning fragment_system
    \<longleftrightarrow> q=data_list_term (map address_pair_data (filter (\<lambda>a. fst a\<notin>A) xs))"
proof (rule fragment_omitted_attachments.encoded_input)
  show "(1,p)\<in>positive_meaning distinct_payloads_system"
    using source by (simp only: payload_set_admission; blast)
  show "\<exists>b. attachment_value_presents b (address_pair_data a)" if "a\<in>set xs" for a
    by (rule exI[of _ a]) (use elements that in auto)
  show "presented_relation payload_set_presents attachment_value_presents (\<lambda>A a. fst a\<notin>A) p (address_pair_data a) \<longleftrightarrow> fst a\<notin>A"
    if "a\<in>set xs" for a
    by (rule presented_relation_at[OF payload_set_presentation_class attachment_value_presentation_class source])
      (use elements that in auto)
qed

theorem fragment_internal_incidence_at_selection:
  assumes source: "payload_set_presents A p" and elements: "\<forall>a\<in>set xs. (incidence_coordinates_formed) a"
  shows "(201,Pair_Term p (Pair_Term (data_list_term (map incidence_data xs)) q))\<in>positive_meaning fragment_system
    \<longleftrightarrow> q=data_list_term (map incidence_data (filter (\<lambda>a. incidence_inside A a) xs))"
proof (rule fragment_internal_incidence.encoded_input)
  show "(1,p)\<in>positive_meaning distinct_payloads_system"
    using source by (simp only: payload_set_admission; blast)
  show "\<exists>b. incidence_value_presents b (incidence_data a)" if "a\<in>set xs" for a
    by (rule exI[of _ a]) (use elements that in auto)
  show "presented_relation payload_set_presents incidence_value_presents (incidence_inside) p (incidence_data a) \<longleftrightarrow> incidence_inside A a"
    if "a\<in>set xs" for a
    by (rule presented_relation_at[OF payload_set_presentation_class incidence_value_presentation_class source])
      (use elements that in auto)
qed

theorem fragment_external_incidence_at_selection:
  assumes source: "payload_set_presents A p" and elements: "\<forall>a\<in>set xs. (incidence_coordinates_formed) a"
  shows "(202,Pair_Term p (Pair_Term (data_list_term (map incidence_data xs)) q))\<in>positive_meaning fragment_system
    \<longleftrightarrow> q=data_list_term (map incidence_data (filter (\<lambda>a. incidence_inside (-A) a) xs))"
proof (rule fragment_external_incidence.encoded_input)
  show "(1,p)\<in>positive_meaning distinct_payloads_system"
    using source by (simp only: payload_set_admission; blast)
  show "\<exists>b. incidence_value_presents b (incidence_data a)" if "a\<in>set xs" for a
    by (rule exI[of _ a]) (use elements that in auto)
  show "presented_relation payload_set_presents incidence_value_presents (\<lambda>A z. incidence_inside (-A) z) p (incidence_data a) \<longleftrightarrow> incidence_inside (-A) a"
    if "a\<in>set xs" for a
    by (rule presented_relation_at[OF payload_set_presentation_class incidence_value_presentation_class source])
      (use elements that in auto)
qed

theorem fragment_noninternal_incidence_at_selection:
  assumes source: "payload_set_presents A p" and elements: "\<forall>a\<in>set xs. (incidence_coordinates_formed) a"
  shows "(203,Pair_Term p (Pair_Term (data_list_term (map incidence_data xs)) q))\<in>positive_meaning fragment_system
    \<longleftrightarrow> q=data_list_term (map incidence_data (filter (\<lambda>a. \<not>incidence_inside A a) xs))"
proof (rule fragment_noninternal_incidence.encoded_input)
  show "(1,p)\<in>positive_meaning distinct_payloads_system"
    using source by (simp only: payload_set_admission; blast)
  show "\<exists>b. incidence_value_presents b (incidence_data a)" if "a\<in>set xs" for a
    by (rule exI[of _ a]) (use elements that in auto)
  show "presented_relation payload_set_presents incidence_value_presents (\<lambda>A z. \<not>incidence_inside A z) p (incidence_data a) \<longleftrightarrow> \<not>incidence_inside A a"
    if "a\<in>set xs" for a
    by (rule presented_relation_at[OF payload_set_presentation_class incidence_value_presentation_class source])
      (use elements that in auto)
qed

theorem fragment_touching_incidence_at_selection:
  assumes source: "payload_set_presents A p" and elements: "\<forall>a\<in>set xs. (incidence_coordinates_formed) a"
  shows "(204,Pair_Term p (Pair_Term (data_list_term (map incidence_data xs)) q))\<in>positive_meaning fragment_system
    \<longleftrightarrow> q=data_list_term (map incidence_data (filter (\<lambda>a. \<not>incidence_inside (-A) a) xs))"
proof (rule fragment_touching_incidence.encoded_input)
  show "(1,p)\<in>positive_meaning distinct_payloads_system"
    using source by (simp only: payload_set_admission; blast)
  show "\<exists>b. incidence_value_presents b (incidence_data a)" if "a\<in>set xs" for a
    by (rule exI[of _ a]) (use elements that in auto)
  show "presented_relation payload_set_presents incidence_value_presents (\<lambda>A z. \<not>incidence_inside (-A) z) p (incidence_data a) \<longleftrightarrow> \<not>incidence_inside (-A) a"
    if "a\<in>set xs" for a
    by (rule presented_relation_at[OF payload_set_presentation_class incidence_value_presentation_class source])
      (use elements that in auto)
qed

text \<open>
  The same three recursive clauses serve all eight instances. Their local
  premises are the complete relation contracts, including both presentation
  domains for complement. Every list order and every repeated retained
  attachment occurrence is preserved by the list operation.

  These list equations describe actual intermediate terms. The complete
  output classes of fragment projections are obtained by composing with the
  owned artifact and finite-collection comparisons, which admit every output
  enumeration of the resulting subject.
\<close>

end
