theory Factor_Proof_Copy
  imports Factor_Native_References Factor_Cloned_Transport
begin

section \<open>Copying proof references preserves their actual endpoints\<close>

context native_syntax_copy
begin

lemma copy_term:
  assumes quote: "term_quoted_at E u r t I K"
  shows "term_quoted_at F w (f r) t (f ` I) (f ` K)"
proof -
  have bound: "I \<union> K \<subseteq> rra_carrier (object_structure R)"
    by (rule term_quoted_carrier[OF quote source])
  have ri: "object_reads_agree (push_object f R) S (f ` I)"
    by (rule restricted_reads) (use bound in blast)
  have sk: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w (f k)"
    by (rule restricted_literals) (use bound in blast)
  show ?thesis
    by (rule term_quotation_transport[OF quote source addressing ri sk target_formed target])
qed

lemma copy_site_citation:
  assumes read: "site_citation_at E u r d I K"
  shows "site_citation_at F w (f r) (g d) (f ` I) (f ` K)"
proof -
  obtain T c where parts: "artifact_at E u T" "citation_at T r c I"
    "citation_location E u c (fst d) (snd d)" "K=citation_slots c"
    using read by (auto simp: site_citation_at_def)
  have same: "T=R" by (rule environment_artifact_unique[OF source_formed parts(1) source])
  have cite: "citation_at R r c I" using parts(2) same by simp
  have copied: "citation_at S (f r) (map_citation_positions f c) (f ` I)"
    by (rule copy_citation[OF cite])
  have loc: "citation_location F w (map_citation_positions f c) (fst (g d)) (snd (g d))"
    using locations[OF cite parts(3)] by simp
  show ?thesis unfolding site_citation_at_def
    by (rule conjI[OF target_formed], rule exI[of _ S],
        rule exI[of _ "map_citation_positions f c"])
       (use target copied loc parts(4) in \<open>simp add: citation_slots_push\<close>)
qed

lemma copy_application:
  assumes app: "native_application_at E u r d t I K"
  shows "native_application_at F w (f r) (g d) t (f ` I) (f ` K)"
proof -
  obtain T ps c a cite C J A where parts:
    "artifact_at E u T" "record_at T r ps [c,a]" "citation_at T c cite C"
    "citation_location E u cite (fst d) (snd d)" "term_quoted_at E u a t J A"
    "insert r (set ps) \<inter> (C \<union> J) = {}" "C \<inter> J = {}"
    "I=insert r (set ps \<union> C \<union> J)" "K=citation_slots cite \<union> A" "I \<inter> K = {}"
    using app by (auto simp: native_application_at_def)
  have same: "T=R" by (rule environment_artifact_unique[OF source_formed parts(1) source])
  have rec: "record_at R r ps [c,a]" and citation: "citation_at R c cite C"
    using parts(2,3) same by simp_all
  have copied_rec: "record_at S (f r) (map f ps) [f c,f a]"
    using copy_record[OF rec] by simp
  have copied_cite: "citation_at S (f c) (map_citation_positions f cite) (f ` C)"
    by (rule copy_citation[OF citation])
  have loc: "citation_location F w (map_citation_positions f cite) (fst (g d)) (snd (g d))"
    using locations[OF citation parts(4)] by simp
  have body: "term_quoted_at F w (f a) t (f ` J) (f ` A)"
    by (rule copy_term[OF parts(5)])
  have top: "insert (f r) (set (map f ps)) \<inter> (f ` C \<union> f ` J) = {}"
    using image_Int[OF injective, of "insert r (set ps)" "C \<union> J"] parts(6)
    by (simp add: image_Un)
  have children: "f ` C \<inter> f ` J = {}"
    using image_Int[OF injective, of C J] parts(7) by simp
  have boundary: "f ` I \<inter> f ` K = {}"
    using image_Int[OF injective, of I K] parts(10) by simp
  show ?thesis unfolding native_application_at_def
    apply (rule conjI[OF target_formed])
    apply (rule exI[of _ S], rule exI[of _ "map f ps"], rule exI[of _ "f c"],
        rule exI[of _ "f a"], rule exI[of _ "map_citation_positions f cite"],
        rule exI[of _ "f ` C"], rule exI[of _ "f ` J"], rule exI[of _ "f ` A"])
    using target copied_rec copied_cite loc body top children boundary parts(8,9)
    by (simp add: image_Un citation_slots_push)
qed

lemma copy_site_link:
  assumes read: "native_site_link_at E u r d e I K"
  shows "native_site_link_at F w (f r) (g d) (g e) (f ` I) (f ` K)"
proof -
  obtain T ps a b J A L B where parts:
    "artifact_at E u T" "record_at T r ps [a,b]"
    "site_citation_at E u a d J A" "site_citation_at E u b e L B"
    "insert r (set ps) \<inter> (J \<union> L) = {}" "J \<inter> L = {}"
    "I=insert r (set ps \<union> J \<union> L)" "K=A \<union> B" "I \<inter> K = {}"
    using read by (auto simp: native_site_link_at_def)
  have same: "T=R" by (rule environment_artifact_unique[OF source_formed parts(1) source])
  have rec: "record_at R r ps [a,b]" using parts(2) same by simp
  have copied_rec: "record_at S (f r) (map f ps) [f a,f b]"
    using copy_record[OF rec] by simp
  have left: "site_citation_at F w (f a) (g d) (f ` J) (f ` A)"
    by (rule copy_site_citation[OF parts(3)])
  have right: "site_citation_at F w (f b) (g e) (f ` L) (f ` B)"
    by (rule copy_site_citation[OF parts(4)])
  have top: "insert (f r) (set (map f ps)) \<inter> (f ` J \<union> f ` L) = {}"
    using image_Int[OF injective, of "insert r (set ps)" "J \<union> L"] parts(5)
    by (simp add: image_Un)
  have children: "f ` J \<inter> f ` L = {}"
    using image_Int[OF injective, of J L] parts(6) by simp
  have boundary: "f ` I \<inter> f ` K = {}"
    using image_Int[OF injective, of I K] parts(9) by simp
  show ?thesis unfolding native_site_link_at_def
    apply (rule conjI[OF target_formed])
    apply (rule exI[of _ S], rule exI[of _ "map f ps"], rule exI[of _ "f a"],
        rule exI[of _ "f b"], rule exI[of _ "f ` J"], rule exI[of _ "f ` A"],
        rule exI[of _ "f ` L"], rule exI[of _ "f ` B"])
    using target copied_rec left right top children boundary parts(7,8)
    by (simp add: image_Un)
qed

end

text \<open>
  Physical positions are copied by f; the endpoints recovered from actual
  citations are transported by g. Term values remain fixed. A site link may
  have equal endpoints, but its two citation interiors remain disjoint under
  the injective structural copy. No proof validity assumption enters these
  syntax transport results.
\<close>

end
