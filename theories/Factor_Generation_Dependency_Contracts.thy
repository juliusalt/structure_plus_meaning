theory Factor_Generation_Dependency_Contracts
  imports Factor_Generation_Retention_Admission
begin

section \<open>Dependency notions own their exact native relation contracts\<close>

theorem generation_read_site_presented:
  "(169,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    presented_relation generation_source_presents site_coordinate_presents (\<lambda>z d. d\<in>generation_read_sites (fst (fst z)) {snd (fst z)}) p q"
  by (auto simp: generation_read_site_exact presented_relation_def generation_source_presentation_fields;
    metis fst_conv snd_conv)

interpretation generation_read_site_contract: presented_relation_contract
  generation_source_presents "\<lambda>z. generation_at_context (fst z) (snd z)"
    "\<lambda>t. (152,t)\<in>positive_meaning generation_source_system"
  site_coordinate_presents "\<lambda>_. True" "\<lambda>t. \<exists>d. site_coordinate_presents d t"
  "\<lambda>z d. d\<in>generation_read_sites (fst (fst z)) {snd (fst z)}"
  "\<lambda>p q. (169,Pair_Term p q)\<in>positive_meaning generation_retention_system"
  by (unfold_locales)
    (use generation_source_native_presentation_class site_coordinate_presentation generation_read_site_presented
      in \<open>auto simp: presentation_class_def\<close>)

corollary generation_read_site_at_presentation:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
  shows "(169,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>d. q=definition_site_value d \<and> d\<in>generation_read_sites E {(u,r)})"
  using generation_read_site_contract.at_source[OF source, of q] by simp

theorem generation_request_presented:
  "(171,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    presented_relation generation_source_presents site_coordinate_presents (\<lambda>z d. d\<in>generation_requests (fst (fst z)) {snd (fst z)}) p q"
  by (auto simp: generation_request_exact presented_relation_def generation_source_presentation_fields;
    metis fst_conv snd_conv)

interpretation generation_request_contract: presented_relation_contract
  generation_source_presents "\<lambda>z. generation_at_context (fst z) (snd z)"
    "\<lambda>t. (152,t)\<in>positive_meaning generation_source_system"
  site_coordinate_presents "\<lambda>_. True" "\<lambda>t. \<exists>d. site_coordinate_presents d t"
  "\<lambda>z d. d\<in>generation_requests (fst (fst z)) {snd (fst z)}"
  "\<lambda>p q. (171,Pair_Term p q)\<in>positive_meaning generation_retention_system"
  by (unfold_locales)
    (use generation_source_native_presentation_class site_coordinate_presentation generation_request_presented
      in \<open>auto simp: presentation_class_def\<close>)

corollary generation_request_at_presentation:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
  shows "(171,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>d. q=definition_site_value d \<and> d\<in>generation_requests E {(u,r)})"
  using generation_request_contract.at_source[OF source, of q] by simp

theorem generation_demanded_slot_presented:
  "(172,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    presented_relation generation_source_presents site_coordinate_presents (\<lambda>z d. d\<in>requested_slots (fst (fst z)) (generation_requests (fst (fst z)) {snd (fst z)})) p q"
  by (auto simp: generation_demanded_slot_exact presented_relation_def generation_source_presentation_fields;
    metis fst_conv snd_conv)

interpretation generation_demanded_slot_contract: presented_relation_contract
  generation_source_presents "\<lambda>z. generation_at_context (fst z) (snd z)"
    "\<lambda>t. (152,t)\<in>positive_meaning generation_source_system"
  site_coordinate_presents "\<lambda>_. True" "\<lambda>t. \<exists>d. site_coordinate_presents d t"
  "\<lambda>z d. d\<in>requested_slots (fst (fst z)) (generation_requests (fst (fst z)) {snd (fst z)})"
  "\<lambda>p q. (172,Pair_Term p q)\<in>positive_meaning generation_retention_system"
  by (unfold_locales)
    (use generation_source_native_presentation_class site_coordinate_presentation generation_demanded_slot_presented
      in \<open>auto simp: presentation_class_def\<close>)

corollary generation_demanded_slot_at_presentation:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
  shows "(172,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>d. q=definition_site_value d \<and> d\<in>requested_slots E (generation_requests E {(u,r)}))"
  using generation_demanded_slot_contract.at_source[OF source, of q] by simp

theorem generation_required_use_presented:
  "(173,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    presented_relation generation_source_presents (\<lambda>u t. t=use_data_term u) (\<lambda>z d. d\<in>requested_uses (fst (fst z)) (generation_requests (fst (fst z)) {snd (fst z)})) p q"
  by (auto simp: generation_required_use_exact presented_relation_def generation_source_presentation_fields;
    metis fst_conv snd_conv)

interpretation generation_required_use_contract: presented_relation_contract
  generation_source_presents "\<lambda>z. generation_at_context (fst z) (snd z)"
    "\<lambda>t. (152,t)\<in>positive_meaning generation_source_system"
  "\<lambda>u t. t=use_data_term u" "\<lambda>_. True" "\<lambda>t. \<exists>u. t=use_data_term u"
  "\<lambda>z d. d\<in>requested_uses (fst (fst z)) (generation_requests (fst (fst z)) {snd (fst z)})"
  "\<lambda>p q. (173,Pair_Term p q)\<in>positive_meaning generation_retention_system"
  by (unfold_locales)
    (use generation_source_native_presentation_class use_coordinate_presentation generation_required_use_presented
      in \<open>auto simp: presentation_class_def\<close>)

corollary generation_required_use_at_presentation:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
  shows "(173,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
    (\<exists>d. q=use_data_term d \<and> d\<in>requested_uses E (generation_requests E {(u,r)}))"
  using generation_required_use_contract.at_source[OF source, of q] by simp

theorem generation_dependency_source_boundary:
  assumes entry: "d\<in>{169,171,172,173}"
    and holds: "(d,Pair_Term p q)\<in>positive_meaning generation_retention_system"
  shows "(152,p)\<in>positive_meaning generation_source_system"
  using entry holds generation_read_site_contract.boundaries generation_request_contract.boundaries
    generation_demanded_slot_contract.boundaries generation_required_use_contract.boundaries by auto

theorem generation_native_read_site_has_core:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and read: "(169,Pair_Term p (site_data_term v a))\<in>positive_meaning generation_retention_system"
  shows "\<exists>H. generation_at E v a H"
proof -
  have native: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have roots: "\<forall>w b. (w,b)\<in>{(u,r)} \<longrightarrow> (\<exists>H. generation_at E w b H)" using native by auto
  have site: "(v,a)\<in>generation_read_sites E {(u,r)}"
    using read by (simp add: generation_read_site_contract.at[OF source, where b="(v,a)"])
  show ?thesis by (rule generation_read_sites_have_cores[OF roots site])
qed

theorem generation_native_request_is_interpretable:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and read: "(171,Pair_Term p (site_data_term v a))\<in>positive_meaning generation_retention_system"
  shows "\<exists>x. anchored_at E v a x"
proof -
  have native: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have formed: "environment_formed E" by (rule generation_at_environment_formed[OF native])
  have roots: "\<forall>w b. (w,b)\<in>{(u,r)} \<longrightarrow> (\<exists>H. generation_at E w b H)" using native by auto
  have requests: "citation_requests_formed E (generation_requests E {(u,r)})"
    by (rule generation_requests_formed[OF formed roots])
  have request: "(v,a)\<in>generation_requests E {(u,r)}"
    using read by (simp add: generation_request_contract.at[OF source, where b="(v,a)"])
  show ?thesis using requests request by (simp add: citation_requests_formed_def)
qed

theorem generation_native_demand_has_binding:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and read: "(172,Pair_Term p (site_data_term v k))\<in>positive_meaning generation_retention_system"
  shows "\<exists>w. binds_slot E v k w"
proof -
  have native: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have formed: "environment_formed E" by (rule generation_at_environment_formed[OF native])
  have roots: "\<forall>w b. (w,b)\<in>{(u,r)} \<longrightarrow> (\<exists>H. generation_at E w b H)" using native by auto
  have requests: "citation_requests_formed E (generation_requests E {(u,r)})"
    by (rule generation_requests_formed[OF formed roots])
  have demand: "(v,k)\<in>requested_slots E (generation_requests E {(u,r)})"
    using read by (simp add: generation_demanded_slot_contract.at[OF source, where b="(v,k)"])
  show ?thesis by (rule requested_slot_exists[OF requests demand])
qed

theorem generation_native_required_use_exists:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and read: "(173,Pair_Term p (use_data_term v))\<in>positive_meaning generation_retention_system"
  shows "v\<in>environment_uses E"
proof -
  have native: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have formed: "environment_formed E" by (rule generation_at_environment_formed[OF native])
  have roots: "\<forall>w b. (w,b)\<in>{(u,r)} \<longrightarrow> (\<exists>H. generation_at E w b H)" using native by auto
  have requests: "citation_requests_formed E (generation_requests E {(u,r)})"
    by (rule generation_requests_formed[OF formed roots])
  have needed: "v\<in>requested_uses E (generation_requests E {(u,r)})"
    using read by (simp only: generation_required_use_contract.at[OF source refl] fst_conv snd_conv)
  show ?thesis using requested_uses_subset[OF requests] needed by blast
qed

theorem generation_dependency_queries_retained:
  assumes source: "generation_source_presents ((E,(u,r)),G) p"
    and retained: "generation_source_presents ((generation_source_environment E u r,(u,r)),G) p'"
  shows "\<forall>q.
    ((169,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
      (169,Pair_Term p' q)\<in>positive_meaning generation_retention_system) \<and>
    ((171,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
      (171,Pair_Term p' q)\<in>positive_meaning generation_retention_system) \<and>
    ((172,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
      (172,Pair_Term p' q)\<in>positive_meaning generation_retention_system) \<and>
    ((173,Pair_Term p q)\<in>positive_meaning generation_retention_system \<longleftrightarrow>
      (173,Pair_Term p' q)\<in>positive_meaning generation_retention_system)"
proof -
  let ?F="generation_source_environment E u r"
  have native: "generation_at E u r G" using source by (simp add: generation_source_presents_def)
  have sites: "generation_read_sites ?F {(u,r)}=generation_read_sites E {(u,r)}"
    and requests: "generation_requests ?F {(u,r)}=generation_requests E {(u,r)}"
    by (rule generation_source_environment_properties(4,5)[OF native])+
  have slots: "requested_slots ?F (generation_requests ?F {(u,r)})=requested_slots E (generation_requests E {(u,r)})"
  proof -
    have "requested_slots ?F (generation_requests ?F {(u,r)})=requested_slots ?F (generation_requests E {(u,r)})"
      by (simp only: requests)
    also have "...=requested_slots E (generation_requests E {(u,r)})"
      by (simp only: generation_source_environment_def requested_slots_after_restriction)
    finally show ?thesis .
  qed
  have uses: "requested_uses ?F (generation_requests ?F {(u,r)})=requested_uses E (generation_requests E {(u,r)})"
  proof -
    have "requested_uses ?F (generation_requests ?F {(u,r)})=requested_uses ?F (generation_requests E {(u,r)})"
      by (simp only: requests)
    also have "...=requested_uses E (generation_requests E {(u,r)})"
      by (simp only: generation_source_environment_def requested_uses_after_restriction)
    finally show ?thesis .
  qed
  show ?thesis
    by (simp only: generation_read_site_at_presentation[OF source] generation_read_site_at_presentation[OF retained]
      generation_request_at_presentation[OF source] generation_request_at_presentation[OF retained]
      generation_demanded_slot_at_presentation[OF source] generation_demanded_slot_at_presentation[OF retained]
      generation_required_use_at_presentation[OF source] generation_required_use_at_presentation[OF retained]
      sites slots uses; simp only: requests; simp)
qed

text \<open>
  The source, request, slot, and use relations are fixed independently of
  their native readers. Each reader exports an exact relation contract over
  the same source class. Generic known-source exactness exposes every possible
  output; transport, specialization, and composition remain general laws.

  Read sites recover actual child cores. Requests recover actual interpreted
  citations, demanded slots have actual bindings, and required uses belong
  to the source environment. Least retention preserves every query, including
  arbitrary malformed queries rejected by the complete relation boundary.
\<close>

end
