theory Factor_Generation_Retention_Admission
  imports Factor_Generation_Requests
begin

section \<open>Complete list profiles check every stored environment key\<close>

interpretation generation_use_lists: context_list_profile generation_retention_system 173 174
  by (unfold_locales) (auto simp: generation_retention_call)

interpretation generation_slot_lists: context_list_profile generation_retention_system 172 175
  by (unfold_locales) (auto simp: generation_retention_call)

abbreviation generation_use_list_result :: "factor_term \<Rightarrow> bool" where
  "generation_use_list_result t \<equiv> \<exists>c xs. t=Pair_Term c (data_list_term xs) \<and> term_formed c \<and>
    (\<forall>x\<in>set xs. generation_required_use_result (Pair_Term c x))"

abbreviation generation_slot_list_result :: "factor_term \<Rightarrow> bool" where
  "generation_slot_list_result t \<equiv> \<exists>c xs. t=Pair_Term c (data_list_term xs) \<and> term_formed c \<and>
    (\<forall>x\<in>set xs. generation_demanded_slot_result (Pair_Term c x))"

theorem generation_coverage_lists_exact:
  "(174,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> generation_use_list_result t"
  "(175,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> generation_slot_list_result t"
  by (simp_all only: generation_use_lists.exact generation_slot_lists.exact
    generation_required_use_exact generation_demanded_slot_exact)

lemma generation_source_argument_formed:
  assumes source: "environment_value_presents E e" and native: "generation_at E u r G"
  shows "term_formed (generation_source_term e (use_data_term u) (Payload_Term r))"
proof -
  have presented: "generation_source_presents ((E,(u,r)),G) (generation_source_term e (use_data_term u) (Payload_Term r))"
    using source native by (auto simp: generation_source_presentation_fields)
  show ?thesis using generation_source_presents_formed[OF presented] by blast
qed

lemma generation_use_lists_on_read:
  assumes source: "environment_value_presents E e" and native: "generation_at E u r G"
  shows "(174,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (data_list_term xs))
      \<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<forall>x\<in>set xs. \<exists>v. x=use_data_term v \<and> v\<in>requested_uses E (generation_requests E {(u,r)}))"
proof -
  have each: "(173,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) x)
      \<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>v. x=use_data_term v \<and> v\<in>requested_uses E (generation_requests E {(u,r)}))" for x
    by (simp only: generation_required_use_at_source[OF source]) (use native in blast)
  show ?thesis by (simp only: generation_use_lists.lists generation_source_argument_formed[OF source native] each; simp)
qed

lemma generation_slot_lists_on_read:
  assumes source: "environment_value_presents E e" and native: "generation_at E u r G"
  shows "(175,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) (data_list_term xs))
      \<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<forall>x\<in>set xs. \<exists>v k. x=site_data_term v k \<and>
      (v,k)\<in>requested_slots E (generation_requests E {(u,r)}))"
proof -
  have each: "(172,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) x)
      \<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>v k. x=site_data_term v k \<and> (v,k)\<in>requested_slots E (generation_requests E {(u,r)}))" for x
    by (simp only: generation_demanded_slot_at_source[OF source]) (use native in blast)
  show ?thesis by (simp only: generation_slot_lists.lists generation_source_argument_formed[OF source native] each; simp)
qed

theorem generation_stored_coverage:
  assumes source: "environment_value_presents E (Pair_Term a b)" and native: "generation_at E u r G"
    and artifact_keys: "(51,Pair_Term a us)\<in>positive_meaning row_keys_system"
    and binding_keys: "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
  shows "((174,Pair_Term (generation_source_term (Pair_Term a b) (use_data_term u) (Payload_Term r)) us)
      \<in>positive_meaning generation_retention_system \<and>
    (175,Pair_Term (generation_source_term (Pair_Term a b) (use_data_term u) (Payload_Term r)) ks)
      \<in>positive_meaning generation_retention_system) \<longleftrightarrow> generation_environment_closed E {(u,r)}"
proof -
  obtain xs where uses: "us=data_list_term xs" "set xs=image use_data_term (environment_uses E)"
    using environment_artifact_keys[OF source artifact_keys] by blast
  obtain ys where slots: "ks=data_list_term ys" "set ys=image definition_site_value (rel_dom (environment_bindings E))"
    using environment_binding_keys[OF source binding_keys] by blast
  show ?thesis
    by (simp only: uses(1) slots(1) generation_use_lists_on_read[OF source native]
      generation_slot_lists_on_read[OF source native] generation_source_closed_coverage[OF native] uses(2) slots(2))
      (auto simp: site_data_term_def inj_eq[OF use_data_term_injective] subset_iff)
qed

section \<open>Closed source admission owns the complete environment boundary\<close>

lemma generation_closed_source_valuation:
  "(176,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5}. term_formed (h i)) \<and>
      t=generation_source_term (Pair_Term (h 0) (h 1)) (h 2) (h 3) \<and>
      (152,generation_source_term (Pair_Term (h 0) (h 1)) (h 2) (h 3))\<in>positive_meaning generation_source_system \<and>
      (51,Pair_Term (h 0) (h 4))\<in>positive_meaning row_keys_system \<and>
      (51,Pair_Term (h 1) (h 5))\<in>positive_meaning row_keys_system \<and>
      (174,Pair_Term t (h 4))\<in>positive_meaning generation_retention_system \<and>
      (175,Pair_Term t (h 5))\<in>positive_meaning generation_retention_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: generation_closed_source_schema_def schema_variables_def generation_retention_call generation_retention_components)

lemma generation_closed_source_fields:
  "(176,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>a b u r us ks. t=generation_source_term (Pair_Term a b) u r \<and>
      (152,t)\<in>positive_meaning generation_source_system \<and>
      (51,Pair_Term a us)\<in>positive_meaning row_keys_system \<and>
      (51,Pair_Term b ks)\<in>positive_meaning row_keys_system \<and>
      (174,Pair_Term t us)\<in>positive_meaning generation_retention_system \<and>
      (175,Pair_Term t ks)\<in>positive_meaning generation_retention_system)"
proof
  assume "(176,t)\<in>positive_meaning generation_retention_system"
  then show "\<exists>a b u r us ks. t=generation_source_term (Pair_Term a b) u r \<and>
      (152,t)\<in>positive_meaning generation_source_system \<and>
      (51,Pair_Term a us)\<in>positive_meaning row_keys_system \<and>
      (51,Pair_Term b ks)\<in>positive_meaning row_keys_system \<and>
      (174,Pair_Term t us)\<in>positive_meaning generation_retention_system \<and>
      (175,Pair_Term t ks)\<in>positive_meaning generation_retention_system"
    by (simp only: generation_closed_source_valuation) blast
next
  assume "\<exists>a b u r us ks. t=generation_source_term (Pair_Term a b) u r \<and>
      (152,t)\<in>positive_meaning generation_source_system \<and>
      (51,Pair_Term a us)\<in>positive_meaning row_keys_system \<and>
      (51,Pair_Term b ks)\<in>positive_meaning row_keys_system \<and>
      (174,Pair_Term t us)\<in>positive_meaning generation_retention_system \<and>
      (175,Pair_Term t ks)\<in>positive_meaning generation_retention_system"
  then obtain a b u r us ks where shape: "t=generation_source_term (Pair_Term a b) u r"
    and calls: "(152,t)\<in>positive_meaning generation_source_system"
      "(51,Pair_Term a us)\<in>positive_meaning row_keys_system" "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
      "(174,Pair_Term t us)\<in>positive_meaning generation_retention_system"
      "(175,Pair_Term t ks)\<in>positive_meaning generation_retention_system" by blast
  have formed: "term_formed a" "term_formed b" "term_formed u" "term_formed r" "term_formed us" "term_formed ks"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(3)]] shape by auto
  let ?h="\<lambda>i::nat. if i=0 then a else if i=1 then b else if i=2 then u else if i=3 then r else if i=4 then us else ks"
  show "(176,t)\<in>positive_meaning generation_retention_system"
    by (simp only: generation_closed_source_valuation, rule exI[of _ ?h]) (use shape calls formed in auto)
qed

theorem generation_closed_source_at_source:
  assumes source: "environment_value_presents E e"
  shows "(176,generation_source_term e (use_data_term u) (Payload_Term r))\<in>positive_meaning generation_retention_system
    \<longleftrightarrow> generation_environment_closed E {(u,r)}"
proof
  assume holds: "(176,generation_source_term e (use_data_term u) (Payload_Term r))\<in>positive_meaning generation_retention_system"
  obtain a b us ks where shape: "e=Pair_Term a b"
    and calls: "(152,generation_source_term e (use_data_term u) (Payload_Term r))\<in>positive_meaning generation_source_system"
      "(51,Pair_Term a us)\<in>positive_meaning row_keys_system" "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system"
      "(174,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) us)\<in>positive_meaning generation_retention_system"
      "(175,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) ks)\<in>positive_meaning generation_retention_system"
    using holds by (auto simp: generation_closed_source_fields)
  obtain G where native: "generation_at E u r G" using calls(1) by (simp only: generation_source_at_source[OF source]) blast
  have encoded: "environment_value_presents E (Pair_Term a b)" using source shape by simp
  show "generation_environment_closed E {(u,r)}"
    using calls(4,5) generation_stored_coverage[OF encoded native calls(2,3)] shape by blast
next
  assume closed: "generation_environment_closed E {(u,r)}"
  obtain G where native: "generation_at E u r G" using closed by (auto simp: generation_environment_closed_def)
  obtain a b where shape: "e=Pair_Term a b" using source by (auto simp: environment_value_presents_def)
  have encoded: "environment_value_presents E (Pair_Term a b)" using source shape by simp
  obtain us ks where keys: "(51,Pair_Term a us)\<in>positive_meaning row_keys_system"
    "(51,Pair_Term b ks)\<in>positive_meaning row_keys_system" using environment_keys_total[OF encoded] by blast
  have coverage: "(174,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) us)\<in>positive_meaning generation_retention_system \<and>
      (175,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) ks)\<in>positive_meaning generation_retention_system"
    using generation_stored_coverage[OF encoded native keys] closed shape by blast
  have admitted: "(152,generation_source_term e (use_data_term u) (Payload_Term r))\<in>positive_meaning generation_source_system"
    using native by (simp only: generation_source_at_source[OF source]) blast
  show "(176,generation_source_term e (use_data_term u) (Payload_Term r))\<in>positive_meaning generation_retention_system"
    using shape keys coverage admitted by (simp only: generation_closed_source_fields) blast
qed

theorem generation_closed_source_exact:
  "(176,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> (\<exists>z. generation_closed_source_presents z t)"
proof
  assume holds: "(176,t)\<in>positive_meaning generation_retention_system"
  obtain E e u r G where source: "environment_value_presents E e" "generation_at E u r G"
    and shape: "t=generation_source_term e (use_data_term u) (Payload_Term r)"
    using holds by (auto simp: generation_closed_source_fields generation_source_exact generation_source_presentation_fields)
  have closed: "generation_environment_closed E {(u,r)}"
    using holds by (simp only: shape generation_closed_source_at_source[OF source(1)])
  show "\<exists>z. generation_closed_source_presents z t"
    by (rule exI[of _ "((E,(u,r)),G)"])
      (use source shape closed in \<open>auto simp: generation_closed_source_presents_def generation_source_presentation_fields\<close>)
next
  assume "\<exists>z. generation_closed_source_presents z t"
  then obtain E e u r G where source: "environment_value_presents E e"
    and shape: "t=generation_source_term e (use_data_term u) (Payload_Term r)"
    and closed: "generation_environment_closed E {(u,r)}"
    by (auto simp: generation_closed_source_presents_def generation_source_presentation_fields)
  show "(176,t)\<in>positive_meaning generation_retention_system"
    by (simp only: shape generation_closed_source_at_source[OF source]; rule closed)
qed

section \<open>A retained-environment report is the exact least-environment relation\<close>

lemma generation_retention_report_valuation:
  "(177,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3}. term_formed (h i)) \<and>
      t=Pair_Term (generation_source_term (h 0) (h 1) (h 2)) (h 3) \<and>
      (176,generation_source_term (h 3) (h 1) (h 2))\<in>positive_meaning generation_retention_system \<and>
      (113,Pair_Term (h 3) (h 0))\<in>positive_meaning environment_inclusion_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: generation_retention_report_schema_def schema_variables_def generation_retention_call generation_retention_components)

lemma generation_retention_report_fields:
  "(177,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>e u r f. t=Pair_Term (generation_source_term e u r) f \<and>
      (176,generation_source_term f u r)\<in>positive_meaning generation_retention_system \<and>
      (113,Pair_Term f e)\<in>positive_meaning environment_inclusion_system)"
proof
  assume "(177,t)\<in>positive_meaning generation_retention_system"
  then show "\<exists>e u r f. t=Pair_Term (generation_source_term e u r) f \<and>
      (176,generation_source_term f u r)\<in>positive_meaning generation_retention_system \<and>
      (113,Pair_Term f e)\<in>positive_meaning environment_inclusion_system"
    by (simp only: generation_retention_report_valuation) blast
next
  assume "\<exists>e u r f. t=Pair_Term (generation_source_term e u r) f \<and>
      (176,generation_source_term f u r)\<in>positive_meaning generation_retention_system \<and>
      (113,Pair_Term f e)\<in>positive_meaning environment_inclusion_system"
  then obtain e u r f where shape: "t=Pair_Term (generation_source_term e u r) f"
    and calls: "(176,generation_source_term f u r)\<in>positive_meaning generation_retention_system"
      "(113,Pair_Term f e)\<in>positive_meaning environment_inclusion_system" by blast
  have formed: "term_formed e" "term_formed u" "term_formed r" "term_formed f"
    using schema_call_formed_target[OF positive_meaning_formed[OF calls(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF calls(2)]] by auto
  let ?h="\<lambda>i::nat. if i=0 then e else if i=1 then u else if i=2 then r else f"
  show "(177,t)\<in>positive_meaning generation_retention_system"
    by (simp only: generation_retention_report_valuation, rule exI[of _ ?h]) (use shape calls formed in auto)
qed

theorem generation_retention_report_on_values:
  assumes source: "environment_value_presents E e" and claim: "environment_value_presents F f"
  shows "(177,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) f)
      \<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>G. generation_at E u r G \<and> F=generation_source_environment E u r)"
proof -
  have formed: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have fields: "(177,Pair_Term (generation_source_term e (use_data_term u) (Payload_Term r)) f)
      \<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (176,generation_source_term f (use_data_term u) (Payload_Term r))\<in>positive_meaning generation_retention_system \<and>
    (113,Pair_Term f e)\<in>positive_meaning environment_inclusion_system"
    by (simp only: generation_retention_report_fields factor_term.inject; blast)
  show ?thesis by (simp only: fields generation_closed_source_at_source[OF claim]
    environment_inclusion_contract.at[OF claim source] generation_retention_claim_iff[OF formed])
qed

theorem generation_retention_report_exact:
  "(177,t)\<in>positive_meaning generation_retention_system \<longleftrightarrow> (\<exists>z. generation_retention_report_presents z t)"
proof
  assume holds: "(177,t)\<in>positive_meaning generation_retention_system"
  obtain e u r f where shape: "t=Pair_Term (generation_source_term e u r) f"
    and calls: "(176,generation_source_term f u r)\<in>positive_meaning generation_retention_system"
      "(113,Pair_Term f e)\<in>positive_meaning environment_inclusion_system"
    using holds by (simp only: generation_retention_report_fields) blast
  obtain F E where presentations: "environment_value_presents F f" "environment_value_presents E e"
    using calls(2) by (simp only: environment_inclusion_contract.exact presented_relation_def) blast
  obtain v a where coordinate: "u=use_data_term v" "r=Payload_Term a"
    using calls(1) by (auto simp: generation_closed_source_exact generation_closed_source_presents_def
      generation_source_presentation_fields)
  obtain G where source: "generation_at E v a G" and retained: "F=generation_source_environment E v a"
    using holds by (simp only: shape coordinate generation_retention_report_on_values[OF presentations(2,1)]) blast
  have original: "generation_source_presents ((E,(v,a)),G) (generation_source_term e u r)"
    using source presentations(2) coordinate by (auto simp: generation_source_presentation_fields)
  show "\<exists>z. generation_retention_report_presents z t"
    by (rule exI[of _ "(((E,(v,a)),G),F)"])
      (use original presentations(1) retained shape in \<open>auto simp: generation_retention_report_presents_def factor_pair_presents_def\<close>)
next
  assume "\<exists>z. generation_retention_report_presents z t"
  then obtain E u r G F p f e where shape: "t=Pair_Term p f" "p=generation_source_term e (use_data_term u) (Payload_Term r)"
    and presentations: "environment_value_presents E e" "environment_value_presents F f"
    and source: "generation_at E u r G" and retained: "F=generation_source_environment E u r"
    by (auto simp: generation_retention_report_presents_def factor_pair_presents_def generation_source_presentation_fields)
  show "(177,t)\<in>positive_meaning generation_retention_system"
    by (simp only: shape generation_retention_report_on_values[OF presentations]) (use source retained in blast)
qed

text \<open>
  Both complete key lists come from the submitted environment's actual tables.
  Their checks are equivalent to the independently defined closed reading.
  A successful report checks that closed reading in its claimed environment
  and actual inclusion in the original environment. The original source
  reading and exact leastness then follow; they are not duplicate premises.

  The all-term equations admit exactly the independent closed-source and
  linked report classes. They retain arbitrary complete environment orders
  and child-artifact presentations and reject every other input shape.
\<close>

end
