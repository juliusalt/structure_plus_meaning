theory Factor_Placeholder_Fill
  imports Factor_Bounded_Generation_Scopes Factor_Positive_Parametricity
begin

section \<open>The placeholder and its fill\<close>

text \<open>
  The placeholder is the empty artifact, decided by artifact identity. Its fill by a payload R fills every
  use holding it (never a chosen subset) and keeps every binding: it is @{const payload_fill} at those uses.
  The fill changes an artifact by @{text placeholder_artifact}, which replaces the empty artifact by R and
  keeps every other, and a target by @{text placeholder_target}, which sends the whole empty artifact to the
  whole of R and fixes every other target; its leaf map @{text placeholder_leaf} maps target leaves so and
  fixes every payload. R may be any formed artifact: equal to one E holds at another use, where the maps are
  not injective, or the empty artifact itself, where the fill is E and the maps are identities.
\<close>

definition placeholder_fill :: "'u artifact_environment \<Rightarrow> exact_artifact \<Rightarrow> 'u artifact_environment" where
  "placeholder_fill E R=payload_fill E {u. artifact_at E u empty_artifact} R"

definition placeholder_artifact :: "exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> exact_artifact" where
  "placeholder_artifact R S=(if S=empty_artifact then R else S)"

fun placeholder_target :: "exact_artifact \<Rightarrow> exact_target \<Rightarrow> exact_target" where
  "placeholder_target R (Whole_Artifact S)=Whole_Artifact (placeholder_artifact R S)"
| "placeholder_target R (Occurrence_Anchor a)=Occurrence_Anchor a"

fun placeholder_leaf :: "exact_artifact \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "placeholder_leaf R (Target_Term t)=Target_Term (placeholder_target R t)"
| "placeholder_leaf R (Payload_Term v)=Payload_Term v"
| "placeholder_leaf R (Pair_Term x y)=Pair_Term x y"

lemma placeholder_target_eq:
  "placeholder_target R t=(if t=Whole_Artifact empty_artifact then Whole_Artifact R else t)"
  by (cases t) (simp_all add: placeholder_artifact_def)

lemma placeholder_artifact_kept:
  assumes "r\<in>rra_carrier (object_structure S)"
  shows "placeholder_artifact R S=S"
  using assms by (auto simp: placeholder_artifact_def empty_artifact_def)

lemma placeholder_artifact_anchor:
  assumes "anchor_formed (S,a)"
  shows "placeholder_artifact R S=S"
  using assms by (intro placeholder_artifact_kept[of a]) (simp add: anchor_formed_def)

lemma placeholder_artifact_citation:
  assumes "citation_at S r c I"
  shows "placeholder_artifact R S=S"
  using assms by (intro placeholder_artifact_kept[of r]) (simp add: citation_at_def)

lemma placeholder_artifact_empty [simp]: "placeholder_artifact empty_artifact S=S"
  by (simp add: placeholder_artifact_def)

lemma placeholder_target_empty [simp]: "placeholder_target empty_artifact t=t"
  by (cases t) simp_all

lemma placeholder_leaves_empty [simp]: "map_term_leaves (placeholder_leaf empty_artifact) t=t"
  by (induction t) simp_all

lemma placeholder_artifact_formed:
  assumes "exact_formed R" "exact_formed S"
  shows "exact_formed (placeholder_artifact R S)"
  using assms by (simp add: placeholder_artifact_def)

lemma placeholder_target_formed:
  assumes "exact_formed R" "target_formed t"
  shows "target_formed (placeholder_target R t)"
  using assms by (cases t) (simp_all add: placeholder_artifact_def)

lemma placeholder_leaf_formed:
  assumes "exact_formed R"
  shows "leaf_map_formed (placeholder_leaf R)"
  using assms by (simp add: leaf_map_formed_def placeholder_target_formed)

lemma placeholder_fill_empty:
  assumes formed: "environment_formed E"
  shows "placeholder_fill E empty_artifact=E"
  unfolding placeholder_fill_def
proof (rule payload_fill_same)
  fix u S assume "u\<in>{u. artifact_at E u empty_artifact}" "artifact_at E u S"
  then show "S=empty_artifact" using environment_artifact_unique[OF formed] by blast
qed

lemma placeholder_fill_formed:
  assumes "environment_formed E" "exact_formed R"
  shows "environment_formed (placeholder_fill E R)"
  unfolding placeholder_fill_def by (rule payload_fill_formed_exact) (use assms in auto)

section \<open>The primitives at the fill\<close>

lemma binds_slot_placeholder_fill [simp]:
  "binds_slot (placeholder_fill E R) u k v \<longleftrightarrow> binds_slot E u k v"
  by (simp add: placeholder_fill_def)

lemma environment_uses_placeholder_fill [simp]:
  "environment_uses (placeholder_fill E R)=environment_uses E"
  by (simp add: placeholder_fill_def)

lemma artifact_at_placeholder_fill:
  assumes formed: "environment_formed E"
  shows "artifact_at (placeholder_fill E R) u S \<longleftrightarrow> (\<exists>T. artifact_at E u T \<and> S=placeholder_artifact R T)"
proof -
  have each: "(if artifact_at E u empty_artifact then R else T)=placeholder_artifact R T"
    if held: "artifact_at E u T" for T
  proof (cases "T=empty_artifact")
    case True
    then show ?thesis using held by (simp add: placeholder_artifact_def)
  next
    case False
    have "\<not>artifact_at E u empty_artifact"
      using environment_artifact_unique[OF formed held] False by blast
    then show ?thesis using False by (simp add: placeholder_artifact_def)
  qed
  show ?thesis
    unfolding placeholder_fill_def artifact_at_payload_fill mem_Collect_eq by (metis each)
qed

lemma artifact_at_placeholder_fill_carried:
  assumes "environment_formed E" "artifact_at E u S"
  shows "artifact_at (placeholder_fill E R) u (placeholder_artifact R S)"
  using assms by (auto simp: artifact_at_placeholder_fill)

lemma artifact_at_placeholder_fill_kept:
  assumes formed: "environment_formed E" and kept: "\<not>artifact_at E u empty_artifact"
  shows "artifact_at (placeholder_fill E R) u S \<longleftrightarrow> artifact_at E u S"
proof
  assume "artifact_at (placeholder_fill E R) u S"
  then obtain T where "artifact_at E u T" "S=placeholder_artifact R T"
    by (auto simp: artifact_at_placeholder_fill[OF formed])
  then show "artifact_at E u S" using kept by (auto simp: placeholder_artifact_def)
next
  assume held: "artifact_at E u S"
  then have "S\<noteq>empty_artifact" using kept by blast
  then show "artifact_at (placeholder_fill E R) u S"
    using artifact_at_placeholder_fill_carried[OF formed held, of R] by (simp add: placeholder_artifact_def)
qed

lemma artifact_at_placeholder_fill_placeholder:
  assumes "environment_formed E" "artifact_at E u empty_artifact"
  shows "artifact_at (placeholder_fill E R) u R"
  using artifact_at_placeholder_fill_carried[OF assms, of R] by (simp add: placeholder_artifact_def)

lemma external_slot_values_placeholder_fill:
  assumes formed: "environment_formed E"
  shows "external_slot_values (placeholder_fill E R) u k=placeholder_artifact R ` external_slot_values E u k"
  unfolding external_slot_values_def artifact_at_placeholder_fill[OF formed] binds_slot_placeholder_fill
  by blast

section \<open>Citations, anchors and locations at the fill\<close>

text \<open>
  Each reader reads E's reading carried to the fill, with its target mapped by @{const placeholder_target};
  where E reads, the reader's own uniqueness at the fill closes the reading. Where E does not read, the fill
  may: an occurrence citation of a slot bound to a use holding the empty artifact reads an occurrence of R.
\<close>

lemma interpret_citation_placeholder_fill:
  assumes formed: "environment_formed E" and R_formed: "exact_formed R"
    and read: "interpret_citation E u c t"
  shows "interpret_citation (placeholder_fill E R) u c (placeholder_target R t)"
proof (cases c)
  case (Local a)
  then obtain S where S: "artifact_at E u S" "anchor_formed (S,a)" "t=Occurrence_Anchor (S,a)"
    using read by auto
  have "artifact_at (placeholder_fill E R) u S"
    using artifact_at_placeholder_fill_carried[OF formed S(1), of R] placeholder_artifact_anchor[OF S(2)] by simp
  then show ?thesis using S Local by auto
next
  case (External k a)
  then obtain v S where S: "binds_slot E u k v" "artifact_at E v S" "anchor_formed (S,a)"
      "t=Occurrence_Anchor (S,a)"
    using read by auto
  have "artifact_at (placeholder_fill E R) v S"
    using artifact_at_placeholder_fill_carried[OF formed S(2), of R] placeholder_artifact_anchor[OF S(3)] by simp
  then show ?thesis using S External by auto
next
  case Local_Whole
  then obtain S where S: "artifact_at E u S" "exact_formed S" "t=Whole_Artifact S"
    using read by auto
  have "artifact_at (placeholder_fill E R) u (placeholder_artifact R S)"
    by (rule artifact_at_placeholder_fill_carried[OF formed S(1)])
  moreover have "exact_formed (placeholder_artifact R S)" by (rule placeholder_artifact_formed[OF R_formed S(2)])
  ultimately show ?thesis using S Local_Whole by auto
next
  case (External_Whole k)
  then obtain v S where S: "binds_slot E u k v" "artifact_at E v S" "exact_formed S" "t=Whole_Artifact S"
    using read by auto
  have "artifact_at (placeholder_fill E R) v (placeholder_artifact R S)"
    by (rule artifact_at_placeholder_fill_carried[OF formed S(2)])
  moreover have "exact_formed (placeholder_artifact R S)" by (rule placeholder_artifact_formed[OF R_formed S(3)])
  ultimately show ?thesis using S External_Whole by auto
qed

corollary interpret_citation_placeholder_fill_exact:
  assumes formed: "environment_formed E" and R_formed: "exact_formed R"
    and read: "interpret_citation E u c t"
  shows "interpret_citation (placeholder_fill E R) u c s \<longleftrightarrow> s=placeholder_target R t"
  using citation_interpretation_functional[OF placeholder_fill_formed[OF formed R_formed]]
    interpret_citation_placeholder_fill[OF formed R_formed read] by blast

lemma citation_location_placeholder_fill:
  assumes formed: "environment_formed E" and located: "citation_location E u c v b"
  shows "citation_location (placeholder_fill E R) u c v b"
proof (cases c)
  case (Local a)
  then obtain S where S: "v=u" "b=a" "artifact_at E u S" "anchor_formed (S,a)"
    using located by auto
  have "artifact_at (placeholder_fill E R) u S"
    using artifact_at_placeholder_fill_carried[OF formed S(3), of R] placeholder_artifact_anchor[OF S(4)] by simp
  then show ?thesis using S Local by auto
next
  case (External k a)
  then obtain S where S: "binds_slot E u k v" "b=a" "artifact_at E v S" "anchor_formed (S,a)"
    using located by auto
  have "artifact_at (placeholder_fill E R) v S"
    using artifact_at_placeholder_fill_carried[OF formed S(3), of R] placeholder_artifact_anchor[OF S(4)] by simp
  then show ?thesis using S External by auto
next
  case Local_Whole
  then show ?thesis using located by simp
next
  case (External_Whole k)
  then show ?thesis using located by simp
qed

corollary citation_location_placeholder_fill_exact:
  assumes formed: "environment_formed E" and R_formed: "exact_formed R"
    and located: "citation_location E u c v b"
  shows "citation_location (placeholder_fill E R) u c w a \<longleftrightarrow> w=v \<and> a=b"
  using citation_location_unique[OF placeholder_fill_formed[OF formed R_formed]]
    citation_location_placeholder_fill[OF formed located] by blast

lemma anchored_at_placeholder_fill:
  assumes formed: "environment_formed E" and R_formed: "exact_formed R" and read: "anchored_at E u r t"
  shows "anchored_at (placeholder_fill E R) u r (placeholder_target R t)"
proof -
  obtain S c I where S: "artifact_at E u S" "citation_at S r c I" "interpret_citation E u c t"
    using read unfolding anchored_at_def by blast
  have "artifact_at (placeholder_fill E R) u S"
    using artifact_at_placeholder_fill_carried[OF formed S(1), of R] placeholder_artifact_citation[OF S(2)] by simp
  then show ?thesis unfolding anchored_at_def
    using S(2) interpret_citation_placeholder_fill[OF formed R_formed S(3)] by blast
qed

corollary anchored_at_placeholder_fill_exact:
  assumes formed: "environment_formed E" and R_formed: "exact_formed R" and read: "anchored_at E u r t"
  shows "anchored_at (placeholder_fill E R) u r s \<longleftrightarrow> s=placeholder_target R t"
  using anchored_at_unique[OF placeholder_fill_formed[OF formed R_formed]]
    anchored_at_placeholder_fill[OF formed R_formed read] by blast

lemma located_at_placeholder_fill:
  assumes formed: "environment_formed E" and read: "located_at E u r v a"
  shows "located_at (placeholder_fill E R) u r v a"
proof -
  obtain S c I where S: "artifact_at E u S" "citation_at S r c I" "citation_location E u c v a"
    using read unfolding located_at_def by blast
  have "artifact_at (placeholder_fill E R) u S"
    using artifact_at_placeholder_fill_carried[OF formed S(1), of R] placeholder_artifact_citation[OF S(2)] by simp
  then show ?thesis unfolding located_at_def
    using S(2) citation_location_placeholder_fill[OF formed S(3)] by blast
qed

corollary located_at_placeholder_fill_exact:
  assumes formed: "environment_formed E" and R_formed: "exact_formed R" and read: "located_at E u r v a"
  shows "located_at (placeholder_fill E R) u r w b \<longleftrightarrow> w=v \<and> b=a"
  using located_at_unique[OF placeholder_fill_formed[OF formed R_formed]]
    located_at_placeholder_fill[OF formed read] by blast

section \<open>Term quotation at the fill\<close>

text \<open>
  A quotation's use holds an artifact whose carrier holds the quotation's root, so it does not hold the
  empty artifact: its reading at the fill is E's, its term mapped by the placeholder's leaf map.
\<close>

lemma term_quoted_not_placeholder:
  assumes quote: "term_quoted_at E u r t I K"
  shows "\<not>artifact_at E u empty_artifact"
proof
  assume "artifact_at E u empty_artifact"
  from term_quoted_carrier[OF quote this] term_quoted_root_interior[OF quote] show False
    by (auto simp: empty_artifact_def)
qed

theorem term_quoted_placeholder_fill:
  assumes R_formed: "exact_formed R" and quote: "term_quoted_at E u r t I K"
  shows "term_quoted_at (placeholder_fill E R) u r (map_term_leaves (placeholder_leaf R) t) I K"
  using quote
proof (induction rule: term_quoted_at.induct)
  case (target u S r c I t)
  have art: "artifact_at (placeholder_fill E R) u S"
    using artifact_at_placeholder_fill_carried[OF target.hyps(1,2), of R]
      placeholder_artifact_citation[OF target.hyps(3)] by simp
  have interp: "interpret_citation (placeholder_fill E R) u c (placeholder_target R t)"
    by (rule interpret_citation_placeholder_fill[OF target.hyps(1) R_formed target.hyps(5)])
  show ?case
    using term_quoted_at.target[OF placeholder_fill_formed[OF target.hyps(1) R_formed] art target.hyps(3,4) interp]
    by simp
next
  case (pair u S r ps l q x L A y Q B)
  have kept: "placeholder_artifact R S=S"
    using pair.hyps(3) by (intro placeholder_artifact_kept[of r]) (simp add: record_at_def)
  have art: "artifact_at (placeholder_fill E R) u S"
    using artifact_at_placeholder_fill_carried[OF pair.hyps(1,2), of R] kept by simp
  show ?case
    using term_quoted_at.pair[OF placeholder_fill_formed[OF pair.hyps(1) R_formed] art pair.hyps(3)
        pair.IH pair.hyps(6-8)]
    by simp
next
  case (payload u S r v)
  have kept: "placeholder_artifact R S=S"
    using payload_leaf_carrier[OF payload.hyps(3)] by (rule placeholder_artifact_kept)
  have art: "artifact_at (placeholder_fill E R) u S"
    using artifact_at_placeholder_fill_carried[OF payload.hyps(1,2), of R] kept by simp
  show ?case
    using term_quoted_at.payload[OF placeholder_fill_formed[OF payload.hyps(1) R_formed] art payload.hyps(3)]
    by simp
qed

corollary term_quoted_placeholder_fill_exact:
  assumes R_formed: "exact_formed R" and quote: "term_quoted_at E u r t I K"
  shows "term_quoted_at (placeholder_fill E R) u r s J W \<longleftrightarrow>
    s=map_term_leaves (placeholder_leaf R) t \<and> J=I \<and> W=K"
  using term_quoted_placeholder_fill[OF assms]
  by (auto dest: term_quoted_unique[OF term_quoted_placeholder_fill[OF assms]])

end
