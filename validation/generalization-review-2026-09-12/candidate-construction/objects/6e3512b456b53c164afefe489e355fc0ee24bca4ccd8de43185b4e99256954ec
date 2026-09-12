theory Factor_Judgment_Retention_Admission
  imports Factor_Judgment_Dependency_Reading
begin

section \<open>Generic list profiles cover both complete environment tables\<close>

interpretation judgment_use_lists: context_list_profile judgment_retention_system 180 181
  by (unfold_locales) (auto simp: judgment_retention_call)

interpretation judgment_slot_lists: context_list_profile judgment_retention_system 179 182
  by (unfold_locales) (auto simp: judgment_retention_call)

abbreviation judgment_use_list_result :: "factor_term \<Rightarrow> bool" where
  "judgment_use_list_result t \<equiv> \<exists>c xs. t=Pair_Term c (data_list_term xs) \<and> term_formed c \<and>
    (\<forall>x\<in>set xs. judgment_required_use_result (Pair_Term c x))"

abbreviation judgment_slot_list_result :: "factor_term \<Rightarrow> bool" where
  "judgment_slot_list_result t \<equiv> \<exists>c xs. t=Pair_Term c (data_list_term xs) \<and> term_formed c \<and>
    (\<forall>x\<in>set xs. judgment_demanded_slot_result (Pair_Term c x))"

theorem judgment_coverage_lists_exact:
  "(181,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> judgment_use_list_result t"
  "(182,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> judgment_slot_list_result t"
  by (simp_all only: judgment_use_lists.exact judgment_slot_lists.exact judgment_required_use_exact judgment_demanded_slot_exact)

lemma judgment_use_lists_at_presentation:
  assumes source: "judgment_source_presents z p"
  shows "(181,Pair_Term p (data_list_term xs))\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<forall>x\<in>set xs. \<exists>v. x=use_data_term v \<and> v\<in>judgment_required_uses z)"
  using judgment_source_presents_formed[OF source]
  by (simp only: judgment_use_lists.lists judgment_required_use_at_presentation[OF source]; blast)

lemma judgment_slot_lists_at_presentation:
  assumes source: "judgment_source_presents z p"
  shows "(182,Pair_Term p (data_list_term xs))\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<forall>x\<in>set xs. \<exists>a. site_coordinate_presents a x \<and> a\<in>judgment_required_slots z)"
  using judgment_source_presents_formed[OF source]
  by (simp only: judgment_slot_lists.lists judgment_demanded_slot_at_presentation[OF source]; blast)

theorem judgment_stored_coverage:
  assumes source: "environment_value_presents E (Pair_Term a b)"
    and package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and artifact_keys: "(51,Pair_Term a us)\<in>positive_meaning row_keys_system"
    and binding_keys: "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
  shows "((181,Pair_Term
      (judgment_context_term (Pair_Term a b) (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)) us)
      \<in>positive_meaning judgment_retention_system \<and>
    (182,Pair_Term
      (judgment_context_term (Pair_Term a b) (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)) ks)
      \<in>positive_meaning judgment_retention_system) \<longleftrightarrow>
    native_judgment_environment E pu pr au ar=E"
proof -
  have readable: "\<exists>P d v J L. native_package_at E pu pr P \<and> native_application_at E au ar d v J L"
    by (rule exI[of _ P], rule exI[of _ d], rule exI[of _ t], rule exI[of _ I], rule exI[of _ K])
      (use package app in blast)
  have presented: "judgment_source_presents (E,((pu,pr),(au,ar)))
      (judgment_context_term (Pair_Term a b) (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar))"
    by (simp only: judgment_source_presentation_fields) (use readable source in blast)
  obtain xs where uses: "us=data_list_term xs" "set xs=image use_data_term (environment_uses E)"
    using environment_artifact_keys[OF source artifact_keys] by blast
  obtain ys where slots: "ks=data_list_term ys" "set ys=image definition_site_value (rel_dom (environment_bindings E))"
    using environment_binding_keys[OF source binding_keys] by blast
  show ?thesis
    by (simp only: uses(1) slots(1) judgment_use_lists_at_presentation[OF presented]
      judgment_slot_lists_at_presentation[OF presented] native_judgment_fixed_coverage
      uses(2) slots(2) fst_conv snd_conv)
      (auto simp: site_data_term_def inj_eq[OF use_data_term_injective] subset_iff)
qed

section \<open>Closed admission checks readability and the whole stored boundary\<close>

lemma judgment_closed_source_valuation:
  "(183,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7}. term_formed (h i)) \<and>
      t=judgment_context_term (Pair_Term (h 0) (h 1)) (h 2) (h 3) (h 4) (h 5) \<and>
      (178,t)\<in>positive_meaning judgment_retention_system \<and>
      (51,Pair_Term (h 0) (h 6))\<in>positive_meaning row_keys_system \<and>
      (51,Pair_Term (h 1) (h 7))\<in>positive_meaning row_keys_system \<and>
      (181,Pair_Term t (h 6))\<in>positive_meaning judgment_retention_system \<and>
      (182,Pair_Term t (h 7))\<in>positive_meaning judgment_retention_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: judgment_closed_source_schema_def schema_variables_def judgment_retention_call judgment_retention_components)

lemma judgment_closed_source_fields:
  "(183,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>a b pu pr au ar us ks. t=judgment_context_term (Pair_Term a b) pu pr au ar \<and>
      (178,t)\<in>positive_meaning judgment_retention_system \<and>
      (51,Pair_Term a us)\<in>positive_meaning row_keys_system \<and>
      (51,Pair_Term b ks)\<in>positive_meaning row_keys_system \<and>
      (181,Pair_Term t us)\<in>positive_meaning judgment_retention_system \<and>
      (182,Pair_Term t ks)\<in>positive_meaning judgment_retention_system)"
proof
  assume "(183,t)\<in>positive_meaning judgment_retention_system"
  then show "\<exists>a b pu pr au ar us ks. t=judgment_context_term (Pair_Term a b) pu pr au ar \<and>
    (178,t)\<in>positive_meaning judgment_retention_system \<and>
    (51,Pair_Term a us)\<in>positive_meaning row_keys_system \<and>
    (51,Pair_Term b ks)\<in>positive_meaning row_keys_system \<and>
    (181,Pair_Term t us)\<in>positive_meaning judgment_retention_system \<and>
    (182,Pair_Term t ks)\<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_closed_source_valuation) blast
next
  assume "\<exists>a b pu pr au ar us ks. t=judgment_context_term (Pair_Term a b) pu pr au ar \<and>
    (178,t)\<in>positive_meaning judgment_retention_system \<and>
    (51,Pair_Term a us)\<in>positive_meaning row_keys_system \<and>
    (51,Pair_Term b ks)\<in>positive_meaning row_keys_system \<and>
    (181,Pair_Term t us)\<in>positive_meaning judgment_retention_system \<and>
    (182,Pair_Term t ks)\<in>positive_meaning judgment_retention_system"
  then obtain a b pu pr au ar us ks where shape: "t=judgment_context_term (Pair_Term a b) pu pr au ar"
    and calls: "(178,t)\<in>positive_meaning judgment_retention_system"
    "(51,Pair_Term a us)\<in>positive_meaning row_keys_system" "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
    "(181,Pair_Term t us)\<in>positive_meaning judgment_retention_system"
    "(182,Pair_Term t ks)\<in>positive_meaning judgment_retention_system" by blast
  have formed: "term_formed a" "term_formed b" "term_formed pu" "term_formed pr"
    "term_formed au" "term_formed ar" "term_formed us" "term_formed ks"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(3)]] shape by auto
  let ?h="\<lambda>i::nat. if i=0 then a else if i=1 then b else if i=2 then pu else if i=3 then pr
    else if i=4 then au else if i=5 then ar else if i=6 then us else ks"
  show "(183,t)\<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_closed_source_valuation; rule exI[of _ ?h]) (use shape calls formed in auto)
qed

theorem judgment_closed_source_on_values:
  assumes source: "environment_value_presents E e"
  shows "(183,judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar))
      \<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K) \<and>
    native_judgment_environment E pu pr au ar=E"
proof
  let ?p="judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)"
  assume holds: "(183,?p)\<in>positive_meaning judgment_retention_system"
  obtain a b us ks where shape: "e=Pair_Term a b"
    and calls: "(178,?p)\<in>positive_meaning judgment_retention_system"
    "(51,Pair_Term a us)\<in>positive_meaning row_keys_system" "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
    "(181,Pair_Term ?p us)\<in>positive_meaning judgment_retention_system"
    "(182,Pair_Term ?p ks)\<in>positive_meaning judgment_retention_system"
    using holds by (auto simp: judgment_closed_source_fields)
  obtain P d t I K where reads: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    using calls(1) by (simp only: judgment_source_on_values[OF source]) blast
  have encoded: "environment_value_presents E (Pair_Term a b)" using source shape by simp
  have fixed: "native_judgment_environment E pu pr au ar=E"
    using judgment_stored_coverage[OF encoded reads calls(2,3)] calls(4,5) shape by blast
  show "(\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K) \<and>
    native_judgment_environment E pu pr au ar=E" using reads fixed by blast
next
  let ?p="judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)"
  assume "(\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K) \<and>
    native_judgment_environment E pu pr au ar=E"
  then obtain P d t I K where reads: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    and fixed: "native_judgment_environment E pu pr au ar=E" by blast
  obtain a b where shape: "e=Pair_Term a b" using source by (auto simp: environment_value_presents_def)
  have encoded: "environment_value_presents E (Pair_Term a b)" using source shape by simp
  obtain us ks where keys: "(51,Pair_Term a us)\<in>positive_meaning row_keys_system"
    "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system" using environment_keys_total[OF encoded] by blast
  have coverage: "(181,Pair_Term ?p us)\<in>positive_meaning judgment_retention_system \<and>
      (182,Pair_Term ?p ks)\<in>positive_meaning judgment_retention_system"
    using judgment_stored_coverage[OF encoded reads keys] fixed shape by blast
  have admitted: "(178,?p)\<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_source_on_values[OF source]) (use reads in blast)
  show "(183,?p)\<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_closed_source_fields) (use shape keys coverage admitted in blast)
qed

theorem judgment_closed_source_at_presentation:
  assumes source: "judgment_source_presents z p"
  shows "(183,p)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> judgment_required_environment z=fst z"
proof -
  obtain E pu pr au ar where coordinates: "z=(E,((pu,pr),(au,ar)))" by (cases z; auto)
  obtain e P d t I K where presented: "environment_value_presents E e"
    and shape: "p=judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)"
    and reads: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    using source by (simp only: coordinates judgment_source_presentation_fields) blast
  show ?thesis by (simp only: shape judgment_closed_source_on_values[OF presented] coordinates fst_conv snd_conv)
    (use reads in blast)
qed

theorem judgment_closed_source_exact:
  "(183,p)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> (\<exists>z. judgment_closed_source_presents z p)"
proof
  assume holds: "(183,p)\<in>positive_meaning judgment_retention_system"
  obtain z where source: "judgment_source_presents z p"
    using holds by (simp only: judgment_closed_source_fields judgment_source_exact) blast
  have fixed: "judgment_required_environment z=fst z"
    using holds by (simp only: judgment_closed_source_at_presentation[OF source])
  show "\<exists>z. judgment_closed_source_presents z p"
    by (rule exI[of _ z]) (use source fixed in \<open>simp only: judgment_closed_source_presents_def\<close>)
next
  assume "\<exists>z. judgment_closed_source_presents z p"
  then show "(183,p)\<in>positive_meaning judgment_retention_system"
    using judgment_closed_source_at_presentation by (auto simp: judgment_closed_source_presents_def)
qed

section \<open>Inclusion and closed reading determine the claimed environment\<close>

lemma judgment_retention_report_valuation:
  "(184,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
      t=Pair_Term (judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4)) (h 5) \<and>
      (183,judgment_context_term (h 5) (h 1) (h 2) (h 3) (h 4))\<in>positive_meaning judgment_retention_system \<and>
      (113,Pair_Term (h 5) (h 0))\<in>positive_meaning environment_inclusion_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: judgment_retention_report_schema_def schema_variables_def judgment_retention_call judgment_retention_components)

lemma judgment_retention_report_fields:
  "(184,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>e pu pr au ar f. t=Pair_Term (judgment_context_term e pu pr au ar) f \<and>
      (183,judgment_context_term f pu pr au ar)\<in>positive_meaning judgment_retention_system \<and>
      (113,Pair_Term f e)\<in>positive_meaning environment_inclusion_system)"
proof
  assume "(184,t)\<in>positive_meaning judgment_retention_system"
  then show "\<exists>e pu pr au ar f. t=Pair_Term (judgment_context_term e pu pr au ar) f \<and>
    (183,judgment_context_term f pu pr au ar)\<in>positive_meaning judgment_retention_system \<and>
    (113,Pair_Term f e)\<in>positive_meaning environment_inclusion_system"
    by (simp only: judgment_retention_report_valuation) blast
next
  assume "\<exists>e pu pr au ar f. t=Pair_Term (judgment_context_term e pu pr au ar) f \<and>
    (183,judgment_context_term f pu pr au ar)\<in>positive_meaning judgment_retention_system \<and>
    (113,Pair_Term f e)\<in>positive_meaning environment_inclusion_system"
  then obtain e pu pr au ar f where shape: "t=Pair_Term (judgment_context_term e pu pr au ar) f"
    and closed: "(183,judgment_context_term f pu pr au ar)\<in>positive_meaning judgment_retention_system"
    and included: "(113,Pair_Term f e)\<in>positive_meaning environment_inclusion_system" by blast
  have formed: "term_formed e" "term_formed pu" "term_formed pr" "term_formed au" "term_formed ar" "term_formed f"
    using schema_call_formed_target[OF positive_meaning_formed[OF closed]]
      schema_call_formed_target[OF positive_meaning_formed[OF included]] by auto
  let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then pu else if i=2 then pr else if i=3 then au else if i=4 then ar else f"
  show "(184,t)\<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_retention_report_valuation; rule exI[of _ ?h]) (use shape closed included formed in auto)
qed

theorem judgment_retention_report_on_values:
  assumes source: "environment_value_presents E e" and expected: "environment_value_presents F f"
  shows "(184,Pair_Term
      (judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)) f)
      \<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K) \<and>
    F=native_judgment_environment E pu pr au ar"
proof -
  have formed: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have fields: "(184,Pair_Term (judgment_context_term e pu pr au ar) f)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (183,judgment_context_term f pu pr au ar)\<in>positive_meaning judgment_retention_system \<and>
      (113,Pair_Term f e)\<in>positive_meaning environment_inclusion_system" for pu pr au ar
    by (simp only: judgment_retention_report_fields factor_term.inject) blast
  show ?thesis
    by (simp only: fields judgment_closed_source_on_values[OF expected] environment_inclusion_contract.at[OF expected source])
      (use native_judgment_retention_claim_iff[OF formed, of pu pr au ar F] in blast)
qed

theorem judgment_retention_report_exact:
  "(184,t)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> (\<exists>z. judgment_retention_report_presents z t)"
proof
  assume holds: "(184,t)\<in>positive_meaning judgment_retention_system"
  obtain e x y a b f where shape: "t=Pair_Term (judgment_context_term e x y a b) f"
    and closed: "(183,judgment_context_term f x y a b)\<in>positive_meaning judgment_retention_system"
    and inclusion: "(113,Pair_Term f e)\<in>positive_meaning environment_inclusion_system"
    using holds by (simp only: judgment_retention_report_fields) blast
  obtain F E where encoded_environments: "environment_value_presents F f" "environment_value_presents E e"
    and included: "environment_included F E"
    using inclusion by (simp only: environment_inclusion_contract.exact presented_relation_def) blast
  obtain z where present: "judgment_source_presents z (judgment_context_term f x y a b)"
    using closed by (simp only: judgment_closed_source_fields judgment_source_exact) blast
  obtain H pu pr au ar where coordinates: "z=(H,((pu,pr),(au,ar)))" by (cases z; auto)
  obtain h where native_source: "environment_value_presents H h"
    and coordinates: "f=h" "x=use_data_term pu" "y=Payload_Term pr" "a=use_data_term au" "b=Payload_Term ar"
    using present by (simp only: coordinates judgment_source_presentation_fields factor_term.inject) blast
  have actual: "(184,Pair_Term
      (judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)) f)
      \<in>positive_meaning judgment_retention_system"
    using holds by (simp only: shape coordinates)
  have reading: "(\<exists>P d v I K. native_package_at E pu pr P \<and> native_application_at E au ar d v I K) \<and>
      F=native_judgment_environment E pu pr au ar"
    using actual by (simp only: judgment_retention_report_on_values[OF encoded_environments(2,1)])
  have source: "judgment_source_presents (E,((pu,pr),(au,ar))) (judgment_context_term e x y a b)"
    using encoded_environments(2) reading by (simp only: coordinates judgment_source_presentation_fields) blast
  show "\<exists>z. judgment_retention_report_presents z t"
    by (rule exI[of _ "((E,((pu,pr),(au,ar))),F)"])
      (use shape source encoded_environments(1) reading in \<open>auto simp: judgment_retention_report_presents_def factor_pair_presents_def\<close>)
next
  assume "\<exists>z. judgment_retention_report_presents z t"
  then obtain z F p f where source: "judgment_source_presents z p" and expected: "environment_value_presents F f"
    and shape: "t=Pair_Term p f" and result: "F=judgment_required_environment z"
    by (auto simp: judgment_retention_report_presents_def factor_pair_presents_def)
  obtain E pu pr au ar where coordinates: "z=(E,((pu,pr),(au,ar)))" by (cases z; auto)
  obtain e P d v I K where presented: "environment_value_presents E e"
    and fields: "p=judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)"
    and reads: "native_package_at E pu pr P" "native_application_at E au ar d v I K"
    using source by (simp only: coordinates judgment_source_presentation_fields) blast
  have readable: "\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K"
    by (rule exI[of _ P], rule exI[of _ d], rule exI[of _ v], rule exI[of _ I], rule exI[of _ K])
      (use reads in blast)
  have same: "F=native_judgment_environment E pu pr au ar" using result by (simp only: coordinates fst_conv snd_conv)
  show "(184,t)\<in>positive_meaning judgment_retention_system"
    by (simp only: shape fields judgment_retention_report_on_values[OF presented expected])
      (use readable same in blast)
qed

text \<open>
  List admission is the existing complete sequence contract. Its empty case
  requires a formed context term; closed-source admission separately requires
  an actual readable source and both complete environment key lists.

  A report uses the same program and call coordinates in its claimed
  environment and checks complete inclusion. Readability of the original
  source and exact equality with its least environment follow by locality.
  No proof graph or stored dependency certificate is supplied or inferred.
\<close>

end
