theory Factor_Quotation
  imports Factor_Terms RRA_Citation_Closure RRA_Read_Transport
begin

section \<open>Citation leaves and ordered pairs are structurally distinct\<close>

lemma citation_pair_record_disjoint:
  assumes cite: "citation_at R r c I" and rec: "record_at R r ps [x,y]"
  shows False
proof -
  have raw: "raw_record_at (object_structure R) r ps [x,y]"
    using rec by (simp add: record_at_def)
  have ports: "rel_dom (headed_incidence (object_structure R) r) = set ps"
    by (rule raw_record_port_set[OF raw])
  have distinct: "distinct ps" and separate: "r \<notin> set ps" and len: "length ps = 2"
    using record_at_preserves_socket_occurrences[OF rec] by auto
  have count: "card (rel_dom (headed_incidence (object_structure R) r)) = 2"
    using ports len distinct by (simp add: distinct_card)
  have outside: "r \<notin> rel_dom (headed_incidence (object_structure R) r)"
    using ports separate by simp
  have citation: "raw_citation_at R r c I" using cite by (simp add: citation_at_def)
  show False using count outside
    by (cases rule: raw_citation_at.cases[OF citation]) (auto simp: rel_dom_def)
qed

lemma payload_leaf_citation_disjoint:
  assumes "payload_leaf_at R r v" "citation_at R r c I"
  shows False
  using assms
  by (auto simp: payload_leaf_at_def citation_at_def; blast dest: payload_at_nonempty)

lemma payload_leaf_record_disjoint:
  assumes leaf: "payload_leaf_at R r v" and rec: "record_at R r ps xs"
  shows False
proof -
  have data: "restrict_basis (insert r (set ps)) (object_data R) = empty_basis"
    using rec by (simp add: record_at_def)
  have root: "restrict_basis {r} (object_data R) = empty_basis"
    by (rule empty_restriction_mono[OF data]) simp
  show False using leaf root by (auto simp: payload_leaf_at_def; blast dest: payload_at_nonempty)
qed

lemma environment_payload_octets:
  assumes "environment_formed E" "artifact_at E u R" "payload_leaf_at R r v"
  shows "octets_formed v"
proof -
  have "exact_formed R" using assms(1,2) unfolding environment_formed_def by blast
  then show ?thesis using assms(3) by (rule payload_leaf_octets)
qed

section \<open>Term quotation as a structural reader\<close>

inductive term_quoted_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> factor_term \<Rightarrow>
   local_address set \<Rightarrow> local_address set \<Rightarrow> bool"
  for E where
  target:
    "environment_formed E \<Longrightarrow> artifact_at E u R \<Longrightarrow>
     citation_at R r c I \<Longrightarrow> citation_slots c \<noteq> {} \<Longrightarrow>
     interpret_citation E u c t \<Longrightarrow>
     term_quoted_at E u r (Target_Term t) I (citation_slots c)"
| pair:
    "environment_formed E \<Longrightarrow> artifact_at E u R \<Longrightarrow>
     record_at R r ps [l,q] \<Longrightarrow>
     term_quoted_at E u l x L A \<Longrightarrow> term_quoted_at E u q y Q B \<Longrightarrow>
     insert r (set ps) \<inter> (L \<union> Q) = {} \<Longrightarrow> L \<inter> Q = {} \<Longrightarrow>
     insert r (set ps \<union> L \<union> Q) \<inter> (A \<union> B) = {} \<Longrightarrow>
     term_quoted_at E u r (Pair_Term x y) (insert r (set ps \<union> L \<union> Q)) (A \<union> B)"
| payload:
    "environment_formed E \<Longrightarrow> artifact_at E u R \<Longrightarrow>
     payload_leaf_at R r v \<Longrightarrow>
     term_quoted_at E u r (Payload_Term v) {r} {}"

lemma term_quoted_environment_formed:
  assumes "term_quoted_at E u r t I K"
  shows "environment_formed E"
  using assms by (cases rule: term_quoted_at.cases) auto

lemma term_quoted_formed:
  assumes "term_quoted_at E u r t I K"
  shows "term_formed t"
  using assms by (induction rule: term_quoted_at.induct)
    (auto dest: citation_interpretation_formed intro: environment_payload_octets)

lemma term_quoted_root_interior:
  assumes "term_quoted_at E u r t I K"
  shows "r \<in> I"
  using assms by (cases rule: term_quoted_at.cases)
    (auto simp: citation_at_def dest: raw_citation_interior(2))

lemma term_quoted_finite:
  assumes "term_quoted_at E u r t I K"
  shows "finite I \<and> finite K"
  using assms
proof (induction rule: term_quoted_at.induct)
  case (target u R r c I t)
  have fin: "finite I" using target.hyps(3) raw_citation_interior(1) by (auto simp: citation_at_def)
  have slots: "finite (citation_slots c)" by (cases c) simp_all
  show ?case using fin slots by simp
next
  case (pair u R r ps l q x L A y Q B)
  then show ?case by simp
next
  case (payload u R r v)
  show ?case by simp
qed

lemma term_quoted_with_citation:
  assumes ef: "environment_formed E" and art: "artifact_at E u R" and cite: "citation_at R r c C"
    and quote: "term_quoted_at E u r t I K"
  shows "\<exists>z. t = Target_Term z \<and> I = C \<and> K = citation_slots c \<and>
    interpret_citation E u c z \<and> citation_slots c \<noteq> {}"
proof -
  have same_artifact: "\<And>S. artifact_at E u S \<Longrightarrow> S = R"
    by (rule environment_artifact_unique[OF ef _ art])
  have same_citation: "\<And>d D. citation_at R r d D \<Longrightarrow> d = c \<and> D = C"
    using citation_at_unique[OF _ cite] by blast
  have no_pair: "\<And>ps l q. record_at R r ps [l,q] \<Longrightarrow> False"
    by (rule citation_pair_record_disjoint[OF cite])
  have no_payload: "\<And>v. payload_leaf_at R r v \<Longrightarrow> False"
    by (rule payload_leaf_citation_disjoint[OF _ cite])
  show ?thesis using quote
    by (cases rule: term_quoted_at.cases)
       (auto dest!: same_artifact same_citation no_pair no_payload)
qed

lemma term_quoted_with_pair_record:
  assumes ef: "environment_formed E" and art: "artifact_at E u R" and rec: "record_at R r ps [l,q]"
    and quote: "term_quoted_at E u r t I K"
  shows "\<exists>x y L A Q B. t = Pair_Term x y \<and>
    term_quoted_at E u l x L A \<and> term_quoted_at E u q y Q B \<and>
    I = insert r (set ps \<union> L \<union> Q) \<and> K = A \<union> B \<and>
    insert r (set ps) \<inter> (L \<union> Q) = {} \<and> L \<inter> Q = {} \<and> I \<inter> K = {}"
proof -
  have same_artifact: "\<And>S. artifact_at E u S \<Longrightarrow> S = R"
    by (rule environment_artifact_unique[OF ef _ art])
  have same_record: "\<And>qs a b. record_at R r qs [a,b] \<Longrightarrow> qs = ps \<and> a = l \<and> b = q"
    using record_at_unique[OF _ rec] by auto
  have no_citation: "\<And>c C. citation_at R r c C \<Longrightarrow> False"
    by (rule citation_pair_record_disjoint[OF _ rec])
  have no_payload: "\<And>v. payload_leaf_at R r v \<Longrightarrow> False"
    by (rule payload_leaf_record_disjoint[OF _ rec])
  show ?thesis using quote
    by (cases rule: term_quoted_at.cases)
       (auto dest!: same_artifact same_record no_citation no_payload)
qed

lemma term_quoted_with_payload:
  assumes ef: "environment_formed E" and art: "artifact_at E u R" and leaf: "payload_leaf_at R r v"
    and quote: "term_quoted_at E u r t I K"
  shows "t = Payload_Term v \<and> I = {r} \<and> K = {}"
proof -
  have same_artifact: "\<And>S. artifact_at E u S \<Longrightarrow> S = R"
    by (rule environment_artifact_unique[OF ef _ art])
  have same_payload: "\<And>w. payload_leaf_at R r w \<Longrightarrow> w = v"
    by (rule payload_leaf_unique[OF _ leaf])
  have no_citation: "\<And>c C. citation_at R r c C \<Longrightarrow> False"
    by (rule payload_leaf_citation_disjoint[OF leaf])
  have no_record: "\<And>ps xs. record_at R r ps xs \<Longrightarrow> False"
    by (rule payload_leaf_record_disjoint[OF leaf])
  show ?thesis using quote by (cases rule: term_quoted_at.cases)
    (auto dest!: same_artifact same_payload no_citation no_record)
qed

lemma payload_quotation_has_leaf:
  assumes quote: "term_quoted_at E u r (Payload_Term v) I K" and art: "artifact_at E u R"
  shows "payload_leaf_at R r v \<and> I = {r} \<and> K = {}"
proof -
  have ef: "environment_formed E" by (rule term_quoted_environment_formed[OF quote])
  have same: "\<And>S. artifact_at E u S \<Longrightarrow> S = R"
    by (rule environment_artifact_unique[OF ef _ art])
  show ?thesis using quote by (cases rule: term_quoted_at.cases) (auto dest!: same)
qed

theorem term_quoted_unique:
  assumes first: "term_quoted_at E u r t I K" and second: "term_quoted_at E u r s J W"
  shows "t = s \<and> I = J \<and> K = W"
  using first second
proof (induction arbitrary: s J W rule: term_quoted_at.induct)
  case (target u R r c I t)
  obtain z where eq: "s = Target_Term z" "J = I" "W = citation_slots c"
    and interpreted: "interpret_citation E u c z"
    using term_quoted_with_citation[OF target.hyps(1-3) target.prems] by blast
  have same: "t = z" by (rule citation_interpretation_functional[OF target.hyps(1,5) interpreted])
  show ?case using eq same by simp
next
  case (pair u R r ps l q x L A y Q B)
  obtain x' y' L' A' Q' B' where eq: "s = Pair_Term x' y'"
    "J = insert r (set ps \<union> L' \<union> Q')" "W = A' \<union> B'"
    and left: "term_quoted_at E u l x' L' A'" and right: "term_quoted_at E u q y' Q' B'"
    using term_quoted_with_pair_record[OF pair.hyps(1-3) pair.prems] by auto
  have first: "x = x' \<and> L = L' \<and> A = A'" by (rule pair.IH(1)[OF left])
  have second: "y = y' \<and> Q = Q' \<and> B = B'" by (rule pair.IH(2)[OF right])
  show ?case using eq first second by simp
next
  case (payload u R r v)
  show ?case using term_quoted_with_payload[OF payload.hyps payload.prems] by auto
qed

lemma term_quoted_bad_projection_rejected:
  assumes "term_quoted_at E u r t I K" "t \<noteq> s \<or> I \<noteq> J \<or> K \<noteq> W"
  shows "\<not> term_quoted_at E u r s J W"
  using term_quoted_unique[OF assms(1)] assms(2) by blast

lemma term_quoted_carrier:
  assumes quote: "term_quoted_at E u r t I K" and art: "artifact_at E u R"
  shows "I \<union> K \<subseteq> rra_carrier (object_structure R)"
  using quote art
proof (induction arbitrary: R rule: term_quoted_at.induct)
  case (target u S r c I t)
  have same: "S = R" by (rule environment_artifact_unique[OF target.hyps(1,2) target.prems])
  show ?case using citation_interior_in_carrier[OF target.hyps(3)]
    citation_slots_in_carrier[OF target.hyps(3)] same by blast
next
  case (pair u S r ps l q x L A y Q B)
  have same: "S = R" by (rule environment_artifact_unique[OF pair.hyps(1,2) pair.prems])
  have record_part: "insert r (set ps) \<subseteq> rra_carrier (object_structure R)"
    using record_interior_in_carrier[OF pair.hyps(3)] same by simp
  have left: "L \<union> A \<subseteq> rra_carrier (object_structure R)" by (rule pair.IH(1)[OF pair.prems])
  have right: "Q \<union> B \<subseteq> rra_carrier (object_structure R)" by (rule pair.IH(2)[OF pair.prems])
  show ?case using record_part left right by blast
next
  case (payload u S r v)
  have same: "S = R" by (rule environment_artifact_unique[OF payload.hyps(1,2) payload.prems])
  show ?case using payload_leaf_carrier[OF payload.hyps(3)] same by simp
qed

lemma term_quoted_slots_outside:
  assumes "term_quoted_at E u r t I K"
  shows "I \<inter> K = {}"
  using assms by (cases rule: term_quoted_at.cases) (auto dest: citation_slots_outside_interior)

lemma term_quoted_has_artifact:
  assumes "term_quoted_at E u r t I K"
  shows "\<exists>R. artifact_at E u R \<and> exact_formed R \<and> r \<in> rra_carrier (object_structure R)"
proof -
  have ef: "environment_formed E" by (rule term_quoted_environment_formed[OF assms])
  obtain R where art: "artifact_at E u R" using assms by (cases rule: term_quoted_at.cases) auto
  have formed: "exact_formed R" using ef art unfolding environment_formed_def by blast
  have carrier: "r \<in> rra_carrier (object_structure R)"
    using term_quoted_root_interior[OF assms] term_quoted_carrier[OF assms art] by blast
  show ?thesis using art formed carrier by blast
qed

lemma term_quoted_addresses_formed:
  assumes quote: "term_quoted_at E u r t I K"
  shows "\<forall>a\<in>I\<union>K. octets_formed a"
proof -
  obtain R where actual: "artifact_at E u R" and formed: "exact_formed R"
    using term_quoted_has_artifact[OF quote] by blast
  have inside: "I\<union>K\<subseteq>rra_carrier (object_structure R)"
    by (rule term_quoted_carrier[OF quote actual])
  show ?thesis using formed inside by (auto simp: exact_formed_def)
qed

lemma injective_images_disjoint:
  assumes "inj_on f U" "A \<subseteq> U" "B \<subseteq> U" "A \<inter> B = {}"
  shows "f ` A \<inter> f ` B = {}"
  using inj_on_image_Int[OF assms(1-3)] assms(4) by simp

theorem term_quotation_transport:
  assumes quote: "term_quoted_at E u r t I K"
    and source: "artifact_at E u R"
    and addressing: "finite_addressing (rra_carrier (object_structure R)) f"
    and reads: "object_reads_agree (push_object f R) S (f ` I)"
    and slots: "\<forall>k\<in>K. external_slot_values E u k = external_slot_values F w (f k)"
    and ff: "environment_formed F" and destination: "artifact_at F w S"
  shows "term_quoted_at F w (f r) t (f ` I) (f ` K)"
  using quote source addressing reads slots
proof (induction arbitrary: R rule: term_quoted_at.induct)
  case (target u T r c I t)
  have same: "T = R"
    by (rule environment_artifact_unique[OF target.hyps(1,2) target.prems(1)])
  have cite: "citation_at R r c I" using target.hyps(3) same by simp
  have copied: "citation_at (push_object f R) (f r) (map_citation_positions f c) (f ` I)"
    by (rule citation_at_push[OF cite target.prems(2)])
  have formed: "exact_formed S" using ff destination unfolding environment_formed_def by blast
  have recovered: "citation_at S (f r) (map_citation_positions f c) (f ` I)"
    by (rule citation_at_read_transport[OF copied formed target.prems(3)])
  have external: "citation_slots (map_citation_positions f c) \<noteq> {}"
    using target.hyps(4) by (simp add: citation_slots_push)
  have interpreted: "interpret_citation F w (map_citation_positions f c) t"
    using external_citation_slot_transport[OF target.hyps(4) target.prems(4), of t]
      target.hyps(5) by simp
  have "term_quoted_at F w (f r) (Target_Term t) (f ` I)
    (citation_slots (map_citation_positions f c))"
    by (rule term_quoted_at.target[OF ff destination recovered external interpreted])
  then show ?case by (simp add: citation_slots_push)
next
  case (pair u T r ps l q x L A y Q B)
  let ?U = "rra_carrier (object_structure R)"
  let ?J = "insert r (set ps \<union> L \<union> Q)"
  have same: "T = R"
    by (rule environment_artifact_unique[OF pair.hyps(1,2) pair.prems(1)])
  have rec: "record_at R r ps [l,q]" using pair.hyps(3) same by simp
  have injective: "inj_on f ?U" using pair.prems(2) by (simp add: finite_addressing_def)
  have copied: "record_at (push_object f R) (f r) (map f ps) [f l,f q]"
    using record_at_push[OF rec injective] by simp
  have formed: "object_formed S"
    using ff destination by (auto simp: environment_formed_def exact_formed_def)
  have recovered: "record_at S (f r) (map f ps) [f l,f q]"
    by (rule record_at_read_transport[OF copied formed pair.prems(3)]) auto
  have left_reads: "object_reads_agree (push_object f R) S (f ` L)"
    by (rule object_reads_agree_mono[OF pair.prems(3)]) blast
  have right_reads: "object_reads_agree (push_object f R) S (f ` Q)"
    by (rule object_reads_agree_mono[OF pair.prems(3)]) blast
  have left_slots: "\<forall>k\<in>A. external_slot_values E u k = external_slot_values F w (f k)"
    using pair.prems(4) by blast
  have right_slots: "\<forall>k\<in>B. external_slot_values E u k = external_slot_values F w (f k)"
    using pair.prems(4) by blast
  have left: "term_quoted_at F w (f l) x (f ` L) (f ` A)"
    by (rule pair.IH(1)[OF pair.prems(1,2) left_reads left_slots])
  have right: "term_quoted_at F w (f q) y (f ` Q) (f ` B)"
    by (rule pair.IH(2)[OF pair.prems(1,2) right_reads right_slots])
  have record_carrier: "insert r (set ps) \<subseteq> ?U"
    by (rule record_interior_in_carrier[OF rec])
  have left_carrier: "L \<union> A \<subseteq> ?U"
    by (rule term_quoted_carrier[OF pair.hyps(4) pair.prems(1)])
  have right_carrier: "Q \<union> B \<subseteq> ?U"
    by (rule term_quoted_carrier[OF pair.hyps(5) pair.prems(1)])
  have record_children: "f ` (insert r (set ps)) \<inter> f ` (L \<union> Q) = {}"
    by (rule injective_images_disjoint[OF injective record_carrier _ pair.hyps(6)])
       (use left_carrier right_carrier in blast)
  have children: "f ` L \<inter> f ` Q = {}"
    by (rule injective_images_disjoint[OF injective _ _ pair.hyps(7)])
       (use left_carrier right_carrier in blast)+
  have boundary: "f ` ?J \<inter> f ` (A \<union> B) = {}"
    by (rule injective_images_disjoint[OF injective _ _ pair.hyps(8)])
       (use record_carrier left_carrier right_carrier in blast)+
  have "term_quoted_at F w (f r) (Pair_Term x y)
    (insert (f r) (set (map f ps) \<union> f ` L \<union> f ` Q)) (f ` A \<union> f ` B)"
    by (rule term_quoted_at.pair[OF ff destination recovered left right])
       (use record_children children boundary in \<open>simp_all add: image_Un\<close>)
  then show ?case by (simp add: image_Un)
next
  case (payload u T r v)
  have same: "T = R" by (rule environment_artifact_unique[OF payload.hyps(1,2) payload.prems(1)])
  have leaf: "payload_leaf_at R r v" using payload.hyps(3) same by simp
  have injective: "inj_on f (rra_carrier (object_structure R))"
    using payload.prems(2) by (simp add: finite_addressing_def)
  have copied: "payload_leaf_at (push_object f R) (f r) v"
    by (rule payload_leaf_push[OF leaf injective])
  have formed: "object_formed S"
    using ff destination by (auto simp: environment_formed_def exact_formed_def)
  have recovered: "payload_leaf_at S (f r) v"
    by (rule payload_leaf_read_transport[OF copied formed payload.prems(3)]) simp
  have "term_quoted_at F w (f r) (Payload_Term v) {f r} {}"
    by (rule term_quoted_at.payload[OF ff destination recovered])
  then show ?case by simp
qed

text \<open>
  A target leaf is an external citation to its exact target. An opaque payload
  leaf has one functional attachment and no headed incidence. A pair is an ordered
  two-field record with two disjoint quotation interiors. The external slot
  occurrences remain outside that interior. These are semantic operands and
  structural equations; no constructor name is attached as data.

  This is an admitted term quotation class. The encoding theory constructs
  complete finite witnesses for every formed term. Exactness applies to the
  represented term and its linked citation and binding boundary. Transport
  preserves its term when the injected syntax observations and external slot values
  agree; opaque target addresses are not renamed with quotation positions.
\<close>

end
