theory Factor_Generation_Retention_Presentations
  imports Factor_Generation_Presentations
begin

section \<open>Every stored use and binding belongs to the required environment\<close>

lemma generation_source_presentation_fields:
  "generation_source_presents ((E,(u,r)),G) p \<longleftrightarrow>
    generation_at E u r G \<and> (\<exists>e. environment_value_presents E e \<and>
      p=Pair_Term (Pair_Term e (use_data_term u)) (Payload_Term r))"
  using generation_context_formed[of E u r G]
  by (auto simp: generation_source_presents_def source_root_presents_fields)

lemma generation_source_closed_iff_fixed:
  assumes source: "generation_at E u r G"
  shows "generation_environment_closed E {(u,r)} \<longleftrightarrow> generation_source_environment E u r=E"
  using generation_source_environment_fixed generation_source_environment_properties(3)[OF source] by metis

theorem generation_source_closed_coverage:
  assumes source: "generation_at E u r G"
  shows "generation_environment_closed E {(u,r)} \<longleftrightarrow>
    environment_uses E\<subseteq>requested_uses E (generation_requests E {(u,r)}) \<and>
    rel_dom (environment_bindings E)\<subseteq>requested_slots E (generation_requests E {(u,r)})"
proof -
  let ?Q="generation_requests E {(u,r)}"
  have formed: "environment_formed E" by (rule generation_at_environment_formed[OF source])
  have roots: "\<forall>v a. (v,a)\<in>{(u,r)} \<longrightarrow> (\<exists>H. generation_at E v a H)"
    using source by auto
  have requests: "citation_requests_formed E ?Q" by (rule generation_requests_formed[OF formed roots])
  have fixed: "request_environment E ?Q=E \<longleftrightarrow>
      environment_uses E\<subseteq>requested_uses E ?Q \<and>
      rel_dom (environment_bindings E)\<subseteq>requested_slots E ?Q"
  proof
    assume same: "request_environment E ?Q=E"
    have uses: "environment_uses E=requested_uses E ?Q"
      using request_environment_uses[OF requests] by (simp only: same)
    have slots: "rel_dom (environment_bindings E)=requested_slots E ?Q"
      using request_environment_domain[OF requests] by (simp only: same)
    show "environment_uses E\<subseteq>requested_uses E ?Q \<and>
        rel_dom (environment_bindings E)\<subseteq>requested_slots E ?Q"
      by (simp only: uses slots subset_refl simp_thms)
  next
    assume coverage: "environment_uses E\<subseteq>requested_uses E ?Q \<and>
      rel_dom (environment_bindings E)\<subseteq>requested_slots E ?Q"
    show "request_environment E ?Q=E"
      by (rule request_environment_fixed_coverage) (use coverage in blast)+
  qed
  show ?thesis by (simp only: generation_source_closed_iff_fixed[OF source] generation_source_environment_def fixed)
qed

theorem generation_retention_claim_iff:
  assumes formed: "environment_formed E"
  shows "(\<exists>G. generation_at E u r G \<and> F=generation_source_environment E u r) \<longleftrightarrow>
    generation_environment_closed F {(u,r)} \<and> environment_included F E"
proof
  assume "\<exists>G. generation_at E u r G \<and> F=generation_source_environment E u r"
  then obtain G where source: "generation_at E u r G" and same: "F=generation_source_environment E u r" by blast
  have closed: "generation_environment_closed F {(u,r)}"
    using generation_source_environment_properties(3)[OF source] same by simp
  have included: "environment_included F E"
    by (simp only: same generation_source_environment_def) (rule request_environment_included)
  show "generation_environment_closed F {(u,r)} \<and> environment_included F E" using closed included by blast
next
  assume parts: "generation_environment_closed F {(u,r)} \<and> environment_included F E"
  obtain G where retained: "generation_at F u r G"
    using parts by (auto simp: generation_environment_closed_def)
  have ff: "environment_formed F" by (rule generation_at_environment_formed[OF retained])
  have included: "environment_included F E" using parts by blast
  have source: "generation_at E u r G" by (rule generation_at_included[OF retained included formed])
  have lower: "environment_included (generation_source_environment E u r) F"
    by (rule generation_source_environment_least[OF formed retained included])
  have read: "generation_at (generation_source_environment E u r) u r G"
    by (rule generation_source_environment_properties(2)[OF source])
  have fixed: "generation_source_environment F u r=F"
    by (rule generation_source_environment_fixed) (use parts in blast)
  have upper: "environment_included F (generation_source_environment E u r)"
    using generation_source_environment_least[OF ff read lower] by (simp only: fixed)
  have same: "F=generation_source_environment E u r"
    by (rule environment_included_antisym[OF upper lower])
  show "\<exists>G. generation_at E u r G \<and> F=generation_source_environment E u r" using source same by blast
qed

lemma generation_source_environment_domains:
  assumes source: "generation_at E u r G"
  shows "environment_uses (generation_source_environment E u r)=requested_uses E (generation_requests E {(u,r)})"
    and "rel_dom (environment_bindings (generation_source_environment E u r))=requested_slots E (generation_requests E {(u,r)})"
proof -
  have formed: "environment_formed E" by (rule generation_at_environment_formed[OF source])
  have roots: "\<forall>v a. (v,a)\<in>{(u,r)} \<longrightarrow> (\<exists>H. generation_at E v a H)" using source by auto
  have requests: "citation_requests_formed E (generation_requests E {(u,r)})"
    by (rule generation_requests_formed[OF formed roots])
  show "environment_uses (generation_source_environment E u r)=requested_uses E (generation_requests E {(u,r)})"
    unfolding generation_source_environment_def by (rule request_environment_uses[OF requests])
  show "rel_dom (environment_bindings (generation_source_environment E u r))=requested_slots E (generation_requests E {(u,r)})"
    unfolding generation_source_environment_def by (rule request_environment_domain[OF requests])
qed

lemma generation_request_source_uses:
  assumes source: "generation_at E u r G"
  shows "fst ` generation_requests E {(u,r)}=fst ` generation_read_sites E {(u,r)}"
proof
  show "fst ` generation_requests E {(u,r)}\<subseteq>fst ` generation_read_sites E {(u,r)}"
    by (auto simp: generation_requests_def intro: rev_image_eqI)
  show "fst ` generation_read_sites E {(u,r)}\<subseteq>fst ` generation_requests E {(u,r)}"
  proof
    fix v assume member: "v\<in>fst ` generation_read_sites E {(u,r)}"
    obtain a where site: "(v,a)\<in>generation_read_sites E {(u,r)}" using member by auto
    have roots: "\<forall>w b. (w,b)\<in>{(u,r)} \<longrightarrow> (\<exists>H. generation_at E w b H)"
      using source by auto
    obtain H where child: "generation_at E v a H" using generation_read_sites_have_cores[OF roots site] by blast
    show "v\<in>fst ` generation_requests E {(u,r)}" by (rule generation_site_has_request[OF child site])
  qed
qed

section \<open>Closed sources restrict the existing complete source class\<close>

definition generation_closed_source_presents :: "generation_source \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_closed_source_presents z t \<longleftrightarrow> generation_source_presents z t \<and>
    generation_environment_closed (fst (fst z)) {snd (fst z)}"

theorem generation_closed_source_presentation_class:
  "presentation_class generation_closed_source_presents
    (\<lambda>z. generation_at_context (fst z) (snd z) \<and>
      generation_environment_closed (fst (fst z)) {snd (fst z)})
    (\<lambda>t. \<exists>z. generation_closed_source_presents z t)"
proof -
  let ?D="\<lambda>z::generation_source. generation_at_context (fst z) (snd z) \<and>
    generation_environment_closed (fst (fst z)) {snd (fst z)}"
  have restricted: "presentation_class (\<lambda>z t. ?D z \<and> generation_source_presents z t) ?D
      (\<lambda>t. \<exists>z. ?D z \<and> generation_source_presents z t)"
    by (rule presentation_class_subdomain[OF generation_source_presentation_class]) blast
  have reading: "(?D z \<and> generation_source_presents z t) \<longleftrightarrow>
      generation_closed_source_presents z t" for z t
    using generation_sources.subject_boundary by (auto simp: generation_closed_source_presents_def)
  show ?thesis using restricted by (simp only: reading)
qed

lemma generation_closed_source_formed:
  assumes "generation_closed_source_presents z t"
  shows "term_formed t \<and> self_contained_term t"
proof -
  have source: "generation_source_presents z t"
    using assms by (simp add: generation_closed_source_presents_def)
  show ?thesis by (rule generation_source_presents_formed[OF source])
qed

theorem generation_closed_source_quotation_class:
  "presentation_class
    (composed_presentation generation_closed_source_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. generation_at_context (fst z) (snd z) \<and>
      generation_environment_closed (fst (fst z)) {snd (fst z)})
    (\<lambda>p. \<exists>t. (\<exists>z. generation_closed_source_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF generation_closed_source_presentation_class])
    (use generation_closed_source_formed in blast)

section \<open>A report presents the environment determined by its actual source\<close>

abbreviation generation_required_environment :: "generation_source \<Rightarrow> local_address option artifact_environment" where
  "generation_required_environment z \<equiv>
    generation_source_environment (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z)))"

definition generation_retention_report_presents ::
  "(generation_source\<times>local_address option artifact_environment) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "generation_retention_report_presents z t \<longleftrightarrow>
    snd z=generation_required_environment (fst z) \<and>
    factor_pair_presents generation_source_presents environment_value_presents z t"

lemma generation_required_environment_formed:
  assumes "generation_at_context (fst z) (snd z)"
  shows "environment_formed (generation_required_environment z)"
  by (rule generation_source_environment_properties(1)[OF assms])

theorem generation_retention_report_presentation_class:
  "presentation_class generation_retention_report_presents
    (\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and>
      snd z=generation_required_environment (fst z))
    (\<lambda>t. \<exists>z. generation_retention_report_presents z t)"
proof -
  let ?R="factor_pair_presents generation_source_presents environment_value_presents"
  let ?D="\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and>
    snd z=generation_required_environment (fst z)"
  let ?A="\<lambda>t. \<exists>p q. (\<exists>z. generation_source_presents z p) \<and>
    (26,q)\<in>positive_meaning environment_admission_system \<and> t=Pair_Term p q"
  have raw: "presentation_class ?R
      (\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and> environment_formed (snd z)) ?A"
    by (rule factor_pair_class[OF generation_source_presentation_class environment_presentations.presentation_class_axioms])
  have restricted: "presentation_class (\<lambda>z t. ?D z \<and> ?R z t) ?D (\<lambda>t. \<exists>z. ?D z \<and> ?R z t)"
  proof (rule presentation_class_subdomain[OF raw])
    fix z assume domain: "?D z"
    have native: "generation_at_context (fst (fst z)) (snd (fst z))" using domain by blast
    have formed: "environment_formed (generation_required_environment (fst z))"
      by (rule generation_required_environment_formed[OF native])
    show "generation_at_context (fst (fst z)) (snd (fst z)) \<and> environment_formed (snd z)"
      using domain formed by simp
  qed
  have reading: "(?D z \<and> ?R z t) \<longleftrightarrow> generation_retention_report_presents z t" for z t
    using generation_sources.subject_boundary
    by (auto simp: generation_retention_report_presents_def factor_pair_presents_def)
  show ?thesis using restricted by (simp only: reading)
qed

theorem generation_retention_report_relation:
  "(\<exists>z. generation_retention_report_presents z (Pair_Term p q)) \<longleftrightarrow>
    presented_relation generation_source_presents environment_value_presents
      (\<lambda>z F. F=generation_required_environment z) p q"
  by (auto simp: generation_retention_report_presents_def factor_pair_presents_def presented_relation_def;
    metis fst_conv snd_conv)

lemma generation_retention_report_source:
  "generation_retention_report_presents z (Pair_Term p q) \<longleftrightarrow>
    generation_retention_presents z p \<and> environment_value_presents (snd z) q"
  by (auto simp: generation_retention_report_presents_def generation_retention_presents_def factor_pair_presents_def)

lemma generation_retention_report_formed:
  assumes "generation_retention_report_presents z t"
  shows "term_formed t \<and> self_contained_term t"
proof -
  obtain p q where source: "generation_source_presents (fst z) p"
    and environment: "environment_value_presents (snd z) q"
    and shape: "t=Pair_Term p q"
    using assms by (auto simp: generation_retention_report_presents_def factor_pair_presents_def)
  have left: "term_formed p \<and> self_contained_term p"
    by (rule generation_source_presents_formed[OF source])
  have right: "term_formed q \<and> self_contained_term q"
    using environment_value_presents_formed[OF environment] by blast
  show ?thesis using left right by (simp only: shape) simp
qed

theorem generation_retention_report_quotation_class:
  "presentation_class
    (composed_presentation generation_retention_report_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. generation_at_context (fst (fst z)) (snd (fst z)) \<and>
      snd z=generation_required_environment (fst z))
    (\<lambda>p. \<exists>t. (\<exists>z. generation_retention_report_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF generation_retention_report_presentation_class])
    (use generation_retention_report_formed in blast)

text \<open>
  The complete generation source already determines its required environment.
  A report adds a presentation of that same environment and retains their
  intrinsic relation. All environment presentations remain available. Closed
  sources form a subdomain of the original source class.

  A claimed environment can be characterized using its own closed reading
  and inclusion in the supplied source. These two facts recover the original
  source reading and equality with its least restriction. Every artifact use
  and every binding slot is accounted for separately. A needed whole artifact
  does not by itself justify any outgoing binding of that artifact.
\<close>

end
