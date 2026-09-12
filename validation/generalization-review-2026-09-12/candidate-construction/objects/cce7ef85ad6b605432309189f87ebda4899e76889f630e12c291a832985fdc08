theory Factor_Proof_Evidence
  imports Factor_Proof_Metadata RRA_Evidence
begin

section \<open>The exact-target evidence view is derived from the same links\<close>

lemma site_citation_exact_target:
  assumes cite: "site_citation_at E u r d I K" and art: "artifact_at E (fst d) R"
  shows "anchored_at E u r (Occurrence_Anchor (R,snd d))"
proof -
  have ef: "environment_formed E" using cite by (simp add: site_citation_at_def)
  have location: "located_at E u r (fst d) (snd d)" by (rule site_citation_located[OF cite])
  show ?thesis by (rule located_at_target[OF ef location art])
qed

lemma native_site_link_evidence:
  assumes link: "native_site_link_at E u r d e I K"
    and left: "artifact_at E (fst d) R" and right: "artifact_at E (fst e) S"
  shows "link_at E u r (Occurrence_Anchor (R,snd d)) (Occurrence_Anchor (S,snd e))"
proof -
  obtain T ps a b J A L B where parts: "artifact_at E u T" "record_at T r ps [a,b]"
    "site_citation_at E u a d J A" "site_citation_at E u b e L B"
    using link by (auto simp: native_site_link_at_def)
  have first: "anchored_at E u a (Occurrence_Anchor (R,snd d))"
    by (rule site_citation_exact_target[OF parts(3) left])
  have second: "anchored_at E u b (Occurrence_Anchor (S,snd e))"
    by (rule site_citation_exact_target[OF parts(4) right])
  show ?thesis by (rule link_atI[OF parts(1,2) first second])
qed

lemma native_site_link_evidence_exists:
  assumes link: "native_site_link_at E u r d e I K"
  shows "\<exists>R S. artifact_at E (fst d) R \<and> artifact_at E (fst e) S \<and>
    link_at E u r (Occurrence_Anchor (R,snd d)) (Occurrence_Anchor (S,snd e))"
proof -
  obtain a b J A L B where citations: "site_citation_at E u a d J A" "site_citation_at E u b e L B"
    using link by (auto simp: native_site_link_at_def)
  obtain R where left: "artifact_at E (fst d) R"
    using located_at_has_artifact[OF site_citation_located[OF citations(1)]] by blast
  obtain S where right: "artifact_at E (fst e) S"
    using located_at_has_artifact[OF site_citation_located[OF citations(2)]] by blast
  show ?thesis using left right native_site_link_evidence[OF link left right] by blast
qed

theorem native_discharge_table_is_evidence:
  assumes table: "native_discharge_table_at E u r Q I K"
  shows "\<exists>L. envelope_at E u r L"
proof -
  obtain R M where ef: "environment_formed E" and art: "artifact_at E u R" and family: "family_at R r M"
    using table by (auto simp: native_table_at_def)
  have links: "\<And>s a. (s,a) \<in> M \<Longrightarrow> \<exists>A B. link_at E u a A B"
  proof -
    fix s a assume member: "(s,a) \<in> M"
    obtain q J A where row: "native_site_link_at E u a (fst q) (snd q) J A"
      using native_table_raw_row[OF table art family member] by blast
    show "\<exists>A B. link_at E u a A B" using native_site_link_evidence_exists[OF row] by blast
  qed
  let ?L = "{(s,(A,B)) |s a A B. (s,a) \<in> M \<and> link_at E u a A B}"
  have evidence: "envelope_at E u r ?L"
    apply (rule envelope_atI[OF ef art family])
     apply (rule links, assumption)
    by blast
  show ?thesis using evidence by blast
qed

corollary native_discharge_evidence_complete_domain:
  assumes table: "native_discharge_table_at E u r Q I K" and art: "artifact_at E u R" and family: "family_at R r M"
  shows "\<exists>L. envelope_at E u r L \<and> rel_dom L=rel_dom M"
proof -
  obtain L where evidence: "envelope_at E u r L" using native_discharge_table_is_evidence[OF table] by blast
  show ?thesis using evidence envelope_complete_socket_domain[OF evidence art family] by blast
qed

text \<open>
  Every native premise-link table is already an RRA evidence envelope, with
  the same complete family of link occurrences. Its exact-target projection
  is derived from the actual citation interpretations. No extra certificate
  links are inserted. The Factor reader continues to preserve target uses;
  the envelope's exact artifact anchors alone do not recover that scope.
  Evidence formation here has no derivation-validity premise.
\<close>

end
