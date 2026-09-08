theory Factor_Fragment_Projections
  imports Factor_Fragment_Admission
begin

section \<open>All projections use the same complete source enumeration\<close>

locale fragment_enumeration_context =
  fixes G :: exact_fragment and A E B F and c
  assumes formed: "fragment_formed G"
    and source: "artifact_enumeration (fragment_source G) A E B F"
    and selection: "payload_set_presents (fragment_selection G) c"
begin

abbreviation source_value where
  "source_value \<equiv> Pair_Term (artifact_data_term A E B F) c"

lemmas coordinates = artifact_enumeration_coordinates[OF source]

lemma admitted: "(205,source_value)\<in>positive_meaning fragment_system"
  by (simp only: fragment_admission_at_enumeration[OF source selection]) (rule formed)

lemma material:
  "(206,Pair_Term source_value q)\<in>positive_meaning fragment_system \<longleftrightarrow>
    artifact_value_presents (fragment_material G) q"
proof -
  let ?e="data_list_term (map incidence_data (filter (incidence_inside (fragment_selection G)) E))"
  let ?b="data_list_term (map address_pair_data (filter (\<lambda>z. fst z\<in>fragment_selection G) B))"
  let ?f="data_list_term (map address_pair_data (filter (\<lambda>z. fst z\<in>fragment_selection G) F))"
  let ?r="artifact_fields_term c ?e ?b ?f"
  have filters:
    "(201,Pair_Term c (Pair_Term (data_list_term (map incidence_data E)) u))\<in>positive_meaning fragment_system \<longleftrightarrow> u=?e"
    "(199,Pair_Term c (Pair_Term (data_list_term (map address_pair_data B)) u))\<in>positive_meaning fragment_system \<longleftrightarrow> u=?b"
    "(199,Pair_Term c (Pair_Term (data_list_term (map address_pair_data F)) u))\<in>positive_meaning fragment_system \<longleftrightarrow> u=?f" for u
    by (rule fragment_internal_incidence_at_selection[OF selection coordinates(2)],
      rule fragment_selected_attachments_at_selection[OF selection coordinates(3)],
      rule fragment_selected_attachments_at_selection[OF selection coordinates(4)])
  have raw: "(206,Pair_Term source_value q)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (11,q)\<in>positive_meaning fragment_system \<and>
      (7,Pair_Term ?r q)\<in>positive_meaning fragment_system"
    using admitted by (auto simp: fragment_material_calls artifact_data_term_def filters)
  have expected: "artifact_value_presents (fragment_material G) ?r"
    by (rule fragment_material_value_at_selection[OF formed source selection])
  show ?thesis by (simp only: raw fragment_components(4,5) artifact_admission_exact[symmetric]
    artifact_comparison_admitted_output[OF expected])
qed

lemma remainder:
  "(207,Pair_Term source_value q)\<in>positive_meaning fragment_system \<longleftrightarrow>
    artifact_value_presents (fragment_remainder G) q"
proof -
  let ?a="filter (\<lambda>a. a\<notin>fragment_selection G) A"
  let ?e="filter (incidence_inside (-fragment_selection G)) E"
  let ?b="filter (\<lambda>z. fst z\<notin>fragment_selection G) B"
  let ?f="filter (\<lambda>z. fst z\<notin>fragment_selection G) F"
  let ?r="artifact_data_term ?a ?e ?b ?f"
  have filters:
    "(198,Pair_Term c (Pair_Term (data_list_term (map Payload_Term A)) u))\<in>positive_meaning fragment_system
      \<longleftrightarrow> u=data_list_term (map Payload_Term ?a)"
    "(202,Pair_Term c (Pair_Term (data_list_term (map incidence_data E)) u))\<in>positive_meaning fragment_system
      \<longleftrightarrow> u=data_list_term (map incidence_data ?e)"
    "(200,Pair_Term c (Pair_Term (data_list_term (map address_pair_data B)) u))\<in>positive_meaning fragment_system
      \<longleftrightarrow> u=data_list_term (map address_pair_data ?b)"
    "(200,Pair_Term c (Pair_Term (data_list_term (map address_pair_data F)) u))\<in>positive_meaning fragment_system
      \<longleftrightarrow> u=data_list_term (map address_pair_data ?f)" for u
    by (rule fragment_omitted_payloads_at_selection[OF selection coordinates(1)],
      rule fragment_external_incidence_at_selection[OF selection coordinates(2)],
      rule fragment_omitted_attachments_at_selection[OF selection coordinates(3)],
      rule fragment_omitted_attachments_at_selection[OF selection coordinates(4)])
  have raw: "(207,Pair_Term source_value q)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (11,q)\<in>positive_meaning fragment_system \<and>
      (7,Pair_Term ?r q)\<in>positive_meaning fragment_system"
    using admitted by (auto simp: fragment_remainder_calls artifact_data_term_def filters)
  have expected: "artifact_value_presents (fragment_remainder G) ?r"
    using fragment_remainder_enumeration[OF source] by (auto simp: artifact_value_presents_def)
  show ?thesis by (simp only: raw fragment_components(4,5) artifact_admission_exact[symmetric]
    artifact_comparison_admitted_output[OF expected])
qed

lemma omission:
  "(208,Pair_Term source_value q)\<in>positive_meaning fragment_system \<longleftrightarrow>
    payload_set_presents (fragment_omission G) q"
proof -
  let ?r="data_list_term (map Payload_Term (filter (\<lambda>a. a\<notin>fragment_selection G) A))"
  have filtered: "(198,Pair_Term c (Pair_Term (data_list_term (map Payload_Term A)) u))\<in>positive_meaning fragment_system
      \<longleftrightarrow> u=?r" for u
    by (rule fragment_omitted_payloads_at_selection[OF selection coordinates(1)])
  have raw: "(208,Pair_Term source_value q)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (6,Pair_Term ?r q)\<in>positive_meaning fragment_system"
    using admitted by (auto simp: fragment_omission_calls artifact_data_term_def filtered)
  show ?thesis by (simp only: raw fragment_components(3)
    payload_set_comparison[OF fragment_omission_enumeration[OF source]])
qed

lemma boundary:
  "(209,Pair_Term source_value q)\<in>positive_meaning fragment_system \<longleftrightarrow>
    incidence_set_presents (fragment_boundary G) q"
proof -
  let ?first="filter (\<lambda>z. \<not>incidence_inside (fragment_selection G) z) E"
  let ?last="filter (\<lambda>z. \<not>incidence_inside (-fragment_selection G) z) ?first"
  let ?r="data_list_term (map incidence_data ?last)"
  have first: "(203,Pair_Term c (Pair_Term (data_list_term (map incidence_data E)) u))\<in>positive_meaning fragment_system
      \<longleftrightarrow> u=data_list_term (map incidence_data ?first)" for u
    by (rule fragment_noninternal_incidence_at_selection[OF selection coordinates(2)])
  have remaining: "\<forall>z\<in>set ?first. incidence_coordinates_formed z" using coordinates(2) by auto
  have last: "(204,Pair_Term c (Pair_Term (data_list_term (map incidence_data ?first)) u))\<in>positive_meaning fragment_system
      \<longleftrightarrow> u=?r" for u
    by (rule fragment_touching_incidence_at_selection[OF selection remaining])
  have calls: "(209,Pair_Term source_value q)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (205,source_value)\<in>positive_meaning fragment_system \<and>
      (\<exists>u w. (203,Pair_Term c (Pair_Term (data_list_term (map incidence_data E)) u))
          \<in>positive_meaning fragment_system \<and>
        (204,Pair_Term c (Pair_Term u w))\<in>positive_meaning fragment_system \<and>
        (6,Pair_Term w q)\<in>positive_meaning fragment_system)"
    using fragment_boundary_calls[of "Pair_Term source_value q"]
    by (simp only: artifact_data_term_def factor_term.inject; blast)
  have raw: "(209,Pair_Term source_value q)\<in>positive_meaning fragment_system \<longleftrightarrow>
      (6,Pair_Term ?r q)\<in>positive_meaning fragment_system"
  proof
    assume accepted: "(209,Pair_Term source_value q)\<in>positive_meaning fragment_system"
    obtain u w where first_call: "(203,Pair_Term c (Pair_Term (data_list_term (map incidence_data E)) u))
        \<in>positive_meaning fragment_system"
      and last_call: "(204,Pair_Term c (Pair_Term u w))\<in>positive_meaning fragment_system"
      and comparison: "(6,Pair_Term w q)\<in>positive_meaning fragment_system"
      using accepted calls by blast
    have first_value: "u=data_list_term (map incidence_data ?first)" using first_call first[of u] by blast
    have last_value: "w=?r" using last_call last[of w] by (simp only: first_value; blast)
    show "(6,Pair_Term ?r q)\<in>positive_meaning fragment_system"
      using comparison by (simp only: last_value)
  next
    assume comparison: "(6,Pair_Term ?r q)\<in>positive_meaning fragment_system"
    have first_call: "(203,Pair_Term c (Pair_Term (data_list_term (map incidence_data E))
        (data_list_term (map incidence_data ?first))))\<in>positive_meaning fragment_system"
      using first[of "data_list_term (map incidence_data ?first)"] by simp
    have last_call: "(204,Pair_Term c (Pair_Term (data_list_term (map incidence_data ?first)) ?r))
        \<in>positive_meaning fragment_system"
      using last[of ?r] by simp
    show "(209,Pair_Term source_value q)\<in>positive_meaning fragment_system"
      using calls admitted first_call last_call comparison by blast
  qed
  have expected: "incidence_set_presents (fragment_boundary G) ?r"
    using fragment_boundary_enumeration[OF source] by (simp add: filter_filter conj_commute)
  show ?thesis by (simp only: raw fragment_components(3) incidence_set_comparison[OF expected])
qed

end

section \<open>Every compatible source and every compatible output are covered\<close>

theorem fragment_projections_at_source:
  assumes source: "fragment_value_presents G p"
  shows "(206,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow>
      artifact_value_presents (fragment_material G) q"
    "(207,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow>
      artifact_value_presents (fragment_remainder G) q"
    "(208,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow>
      payload_set_presents (fragment_omission G) q"
    "(209,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow>
      incidence_set_presents (fragment_boundary G) q"
proof -
  obtain A E B F c where formed: "fragment_formed G" and enumeration: "artifact_enumeration (fragment_source G) A E B F"
    and selection: "payload_set_presents (fragment_selection G) c" and shape: "p=Pair_Term (artifact_data_term A E B F) c"
    using source by (simp only: fragment_value_enumerations; blast)
  interpret source: fragment_enumeration_context G A E B F c
    by (rule fragment_enumeration_context.intro[OF formed enumeration selection])
  show "(206,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow> artifact_value_presents (fragment_material G) q"
    "(207,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow> artifact_value_presents (fragment_remainder G) q"
    "(208,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow> payload_set_presents (fragment_omission G) q"
    "(209,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow> incidence_set_presents (fragment_boundary G) q"
    by (simp_all only: shape source.material source.remainder source.omission source.boundary)
qed

lemma fragment_projection_source:
  assumes "d\<in>{206,207,208,209}" "(d,t)\<in>positive_meaning fragment_system"
  shows "\<exists>G p q. t=Pair_Term p q \<and> fragment_value_presents G p"
  using assms by (auto simp: fragment_material_calls fragment_remainder_calls fragment_omission_calls
    fragment_boundary_calls fragment_admission_exact; blast)

lemma fragment_projection_exact_from_source:
  assumes entry: "d\<in>{206,207,208,209}"
    and meaning: "\<And>G p q. fragment_value_presents G p \<Longrightarrow>
      (d,Pair_Term p q)\<in>positive_meaning fragment_system \<longleftrightarrow> S (f G) q"
  shows "(d,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>G p q. t=Pair_Term p q \<and> fragment_value_presents G p \<and> S (f G) q)"
proof
  assume holds: "(d,t)\<in>positive_meaning fragment_system"
  obtain G p q where shape: "t=Pair_Term p q" and source: "fragment_value_presents G p"
    using fragment_projection_source[OF entry holds] by blast
  have output_presentation: "S (f G) q" using holds by (simp only: shape meaning[OF source])
  show "\<exists>G p q. t=Pair_Term p q \<and> fragment_value_presents G p \<and> S (f G) q"
    using shape source output_presentation by blast
next
  assume "\<exists>G p q. t=Pair_Term p q \<and> fragment_value_presents G p \<and> S (f G) q"
  then obtain G p q where shape: "t=Pair_Term p q" and source: "fragment_value_presents G p"
    and output_presentation: "S (f G) q" by blast
  show "(d,t)\<in>positive_meaning fragment_system"
    by (simp only: shape meaning[OF source]) (rule output_presentation)
qed

theorem fragment_material_exact:
  "(206,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>G p q. t=Pair_Term p q \<and> fragment_value_presents G p \<and> artifact_value_presents (fragment_material G) q)"
  by (rule fragment_projection_exact_from_source[where S=artifact_value_presents and f=fragment_material,
    OF _ fragment_projections_at_source(1)]) simp

theorem fragment_remainder_exact:
  "(207,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>G p q. t=Pair_Term p q \<and> fragment_value_presents G p \<and> artifact_value_presents (fragment_remainder G) q)"
  by (rule fragment_projection_exact_from_source[where S=artifact_value_presents and f=fragment_remainder,
    OF _ fragment_projections_at_source(2)]) simp

theorem fragment_omission_exact:
  "(208,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>G p q. t=Pair_Term p q \<and> fragment_value_presents G p \<and> payload_set_presents (fragment_omission G) q)"
  by (rule fragment_projection_exact_from_source[where S=payload_set_presents and f=fragment_omission,
    OF _ fragment_projections_at_source(3)]) simp

theorem fragment_boundary_exact:
  "(209,t)\<in>positive_meaning fragment_system \<longleftrightarrow>
    (\<exists>G p q. t=Pair_Term p q \<and> fragment_value_presents G p \<and> incidence_set_presents (fragment_boundary G) q)"
  by (rule fragment_projection_exact_from_source[where S=incidence_set_presents and f=fragment_boundary,
    OF _ fragment_projections_at_source(4)]) simp

text \<open>
  The source fixes selection, omission, all internal rows, and crossing rows.
  The selected and omitted attachment lists preserve their full original
  multiplicities. The output comparisons admit every complete presentation
  of each derived artifact or finite set, regardless of the source order.
\<close>

end
