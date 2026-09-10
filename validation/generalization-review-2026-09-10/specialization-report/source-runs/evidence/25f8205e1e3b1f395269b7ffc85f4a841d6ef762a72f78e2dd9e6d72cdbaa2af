theory RRA_Environment
  imports RRA_Exact
begin

section \<open>Finite environments scoped by use occurrences\<close>

record 'u artifact_environment =
  environment_artifacts :: "('u \<times> exact_artifact) set"
  environment_bindings :: "(('u \<times> local_address) \<times> 'u) set"

definition environment_uses :: "'u artifact_environment \<Rightarrow> 'u set" where
  "environment_uses E = rel_dom (environment_artifacts E)"

definition artifact_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "artifact_at E u R \<longleftrightarrow> (u,R) \<in> environment_artifacts E"

definition binds_slot ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> bool" where
  "binds_slot E u k v \<longleftrightarrow> ((u,k),v) \<in> environment_bindings E"

definition environment_formed :: "'u artifact_environment \<Rightarrow> bool" where
  "environment_formed E \<longleftrightarrow>
    finite (environment_artifacts E) \<and> single_valued (environment_artifacts E) \<and>
    (\<forall>u R. artifact_at E u R \<longrightarrow> exact_formed R) \<and>
    finite (environment_bindings E) \<and> single_valued (environment_bindings E) \<and>
    (\<forall>u k v. binds_slot E u k v \<longrightarrow>
      (\<exists>R. artifact_at E u R \<and> k \<in> rra_carrier (object_structure R)) \<and>
      v \<in> environment_uses E)"

lemma environment_artifact_unique:
  assumes "environment_formed E" "artifact_at E u R" "artifact_at E u S"
  shows "R = S"
  using assms by (auto simp: environment_formed_def artifact_at_def single_valued_def)

lemma environment_binding_unique:
  assumes "environment_formed E" "binds_slot E u k v" "binds_slot E u k w"
  shows "v = w"
  using assms by (auto simp: environment_formed_def binds_slot_def single_valued_def)

lemma environment_uses_finite:
  assumes "environment_formed E"
  shows "finite (environment_uses E)"
proof -
  have "environment_uses E = fst ` environment_artifacts E"
    by (auto simp: environment_uses_def rel_dom_def intro: rev_image_eqI)
  with assms show ?thesis by (simp add: environment_formed_def)
qed

lemma environment_binding_uses:
  assumes formed: "environment_formed E" and binding: "binds_slot E u k v"
  shows "u\<in>environment_uses E" and "v\<in>environment_uses E"
proof -
  obtain R where source: "artifact_at E u R"
    using formed binding unfolding environment_formed_def by blast
  show "u\<in>environment_uses E" using source
    by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
  show "v\<in>environment_uses E"
    using formed binding unfolding environment_formed_def by blast
qed

text \<open>
  A use occurrence identifies one placement in the supplied finite package.
  Equal artifact values may have distinct use occurrences and distinct outgoing
  bindings. The pair of source use and local slot scopes a binding. There is no
  global token namespace and no rule identifying uses because their values agree.
\<close>

section \<open>Citation interpretation\<close>

datatype citation =
    Local local_address
  | External local_address local_address
  | Local_Whole
  | External_Whole local_address

text \<open>
  This datatype is a recovered mathematical projection. The structural syntax
  theory supplies its incidence patterns; these constructor names are not data
  attached to an artifact.
\<close>

fun interpret_citation ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> citation \<Rightarrow> exact_target \<Rightarrow> bool" where
  "interpret_citation E u (Local a) t \<longleftrightarrow>
    (\<exists>R. artifact_at E u R \<and> anchor_formed (R,a) \<and> t = Occurrence_Anchor (R,a))"
| "interpret_citation E u (External k a) t \<longleftrightarrow>
    (\<exists>v R. binds_slot E u k v \<and> artifact_at E v R \<and>
      anchor_formed (R,a) \<and> t = Occurrence_Anchor (R,a))"
| "interpret_citation E u Local_Whole t \<longleftrightarrow>
    (\<exists>R. artifact_at E u R \<and> exact_formed R \<and> t = Whole_Artifact R)"
| "interpret_citation E u (External_Whole k) t \<longleftrightarrow>
    (\<exists>v R. binds_slot E u k v \<and> artifact_at E v R \<and>
      exact_formed R \<and> t = Whole_Artifact R)"

lemma citation_interpretation_functional:
  assumes "environment_formed E" "interpret_citation E u c x" "interpret_citation E u c y"
  shows "x = y"
  using assms
  by (cases c) (auto dest: environment_artifact_unique environment_binding_unique)

lemma citation_interpretation_formed:
  assumes "interpret_citation E u c t"
  shows "target_formed t"
  using assms by (cases c) auto

lemma citation_interpretation_artifact:
  assumes "interpret_citation E u c t"
  shows "\<exists>v. artifact_at E v (target_artifact t)"
  using assms by (cases c) auto

fun citation_location ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> citation \<Rightarrow> 'u \<Rightarrow>
   local_address \<Rightarrow> bool" where
  "citation_location E u (Local a) v b \<longleftrightarrow>
    v = u \<and> b = a \<and> (\<exists>R. artifact_at E u R \<and> anchor_formed (R,a))"
| "citation_location E u (External k a) v b \<longleftrightarrow>
    binds_slot E u k v \<and> b = a \<and> (\<exists>R. artifact_at E v R \<and> anchor_formed (R,a))"
| "citation_location E u Local_Whole v b \<longleftrightarrow> False"
| "citation_location E u (External_Whole k) v b \<longleftrightarrow> False"

lemma citation_location_unique:
  assumes "environment_formed E" "citation_location E u c v a"
    "citation_location E u c w b"
  shows "v = w \<and> a = b"
  using assms by (cases c) (auto dest: environment_binding_unique)

lemma citation_location_has_artifact:
  assumes "citation_location E u c v a"
  shows "\<exists>R. artifact_at E v R \<and> anchor_formed (R,a)"
  using assms by (cases c) auto

lemma citation_location_target:
  assumes formed: "environment_formed E"
    and loc: "citation_location E u c v a" and art: "artifact_at E v R"
  shows "interpret_citation E u c (Occurrence_Anchor (R,a))"
  using assms by (cases c) (auto dest: environment_artifact_unique)

lemma citation_occurrence_location:
  assumes "interpret_citation E u c (Occurrence_Anchor (C,a))"
  shows "\<exists>v. citation_location E u c v a \<and> artifact_at E v C"
  using assms by (cases c) auto

lemma local_citation_is_exact_anchor:
  assumes formed: "environment_formed E" and source: "artifact_at E u R"
  shows "interpret_citation E u (Local a) t \<longleftrightarrow>
    anchor_formed (R,a) \<and> t = Occurrence_Anchor (R,a)"
  using assms by (auto dest: environment_artifact_unique)

lemma local_whole_is_exact_value:
  assumes formed: "environment_formed E" and source: "artifact_at E u R"
  shows "interpret_citation E u Local_Whole t \<longleftrightarrow> t = Whole_Artifact R"
  using assms
  by (auto simp: environment_formed_def artifact_at_def single_valued_def)

lemma external_citation_is_exact_anchor:
  assumes "environment_formed E" "binds_slot E u k v" "artifact_at E v R"
  shows "interpret_citation E u (External k a) t \<longleftrightarrow>
    anchor_formed (R,a) \<and> t = Occurrence_Anchor (R,a)"
  using assms by (auto dest: environment_artifact_unique environment_binding_unique)

lemma external_whole_is_exact_value:
  assumes "environment_formed E" "binds_slot E u k v" "artifact_at E v R"
  shows "interpret_citation E u (External_Whole k) t \<longleftrightarrow> t = Whole_Artifact R"
  using assms
  by (auto simp: environment_formed_def artifact_at_def binds_slot_def single_valued_def; blast)

lemma citation_alias_invariance:
  assumes formed: "environment_formed E"
    and left: "binds_slot E u k v" "artifact_at E v R"
    and right: "binds_slot E u l w" "artifact_at E w R"
  shows "interpret_citation E u (External k a) t = interpret_citation E u (External l a) t"
    and "interpret_citation E u (External_Whole k) t = interpret_citation E u (External_Whole l) t"
  using external_citation_is_exact_anchor[OF formed left]
    external_citation_is_exact_anchor[OF formed right]
    external_whole_is_exact_value[OF formed left]
    external_whole_is_exact_value[OF formed right] by auto

section \<open>Agreement on an explicit dependency boundary\<close>

definition environment_agrees_on ::
  "'u artifact_environment \<Rightarrow> 'u artifact_environment \<Rightarrow> 'u set \<Rightarrow> bool" where
  "environment_agrees_on E F U \<longleftrightarrow>
    (\<forall>u\<in>U. (\<forall>R. artifact_at E u R = artifact_at F u R) \<and>
      (\<forall>k v. binds_slot E u k v = binds_slot F u k v))"

definition environment_edge_closed :: "'u artifact_environment \<Rightarrow> 'u set \<Rightarrow> bool" where
  "environment_edge_closed E U \<longleftrightarrow>
    (\<forall>u\<in>U. \<forall>k v. binds_slot E u k v \<longrightarrow> v \<in> U)"

lemma citation_environment_locality:
  assumes "environment_agrees_on E F U" "environment_edge_closed E U" "u \<in> U"
  shows "interpret_citation E u c t = interpret_citation F u c t"
  using assms
  by (cases c; auto simp: environment_agrees_on_def environment_edge_closed_def; metis)

lemma citation_location_locality:
  assumes "environment_agrees_on E F U" "environment_edge_closed E U" "u \<in> U"
  shows "citation_location E u c v a = citation_location F u c v a"
  using assms
  by (cases c; auto simp: environment_agrees_on_def environment_edge_closed_def; metis)

lemma citation_location_stays_in_boundary:
  assumes "environment_edge_closed E U" "u \<in> U" "citation_location E u c v a"
  shows "v \<in> U"
  using assms by (cases c) (auto simp: environment_edge_closed_def)

lemma environment_agreement_symmetric:
  "environment_agrees_on E F U \<longleftrightarrow> environment_agrees_on F E U"
  by (auto simp: environment_agrees_on_def)

lemma environment_agreement_preserves_closure:
  assumes "environment_agrees_on E F U" "environment_edge_closed E U"
  shows "environment_edge_closed F U"
  using assms by (auto simp: environment_agrees_on_def environment_edge_closed_def)

section \<open>Recursive closure without an ambient registry\<close>

definition environment_edges :: "'u artifact_environment \<Rightarrow> ('u \<times> 'u) set" where
  "environment_edges E = {(u,v). \<exists>k. binds_slot E u k v}"

definition environment_reachable :: "'u artifact_environment \<Rightarrow> 'u set \<Rightarrow> 'u set" where
  "environment_reachable E roots = {v. \<exists>u\<in>roots. (u,v) \<in> (environment_edges E)\<^sup>*}"

definition environment_closed ::
  "'u artifact_environment \<Rightarrow> 'u set \<Rightarrow> ('u \<times> local_address) set \<Rightarrow> bool" where
  "environment_closed E roots demands \<longleftrightarrow>
    environment_formed E \<and> roots \<subseteq> environment_uses E \<and>
    environment_uses E = environment_reachable E roots \<and>
    rel_dom (environment_bindings E) = demands"

text \<open>
  Closure is relative to a complete, explicitly supplied dependency boundary.
  Every demanded source-use/slot pair has one binding, and every retained use is
  reachable from the roots. A recognizer must establish that this boundary is
  exactly the one its structure demands before this relation can establish its
  semantic closure. An arbitrary certificate cannot choose that boundary.
\<close>

lemma environment_edge_endpoints:
  assumes "environment_formed E" "(u,v) \<in> environment_edges E"
  shows "u \<in> environment_uses E" "v \<in> environment_uses E"
proof -
  show "u \<in> environment_uses E"
    using assms
    by (auto simp: environment_formed_def environment_edges_def environment_uses_def
      artifact_at_def rel_dom_def; blast)
  show "v \<in> environment_uses E"
    using assms by (auto simp: environment_formed_def environment_edges_def)
qed

lemma environment_roots_reachable:
  "roots \<subseteq> environment_reachable E roots"
  by (auto simp: environment_reachable_def)

lemma environment_reachable_edge_closed:
  "environment_edge_closed E (environment_reachable E roots)"
  by (auto simp: environment_edge_closed_def environment_reachable_def environment_edges_def
    intro: rtrancl_into_rtrancl)

lemma environment_reachable_least:
  assumes roots: "roots \<subseteq> U" and closed: "environment_edge_closed E U"
  shows "environment_reachable E roots \<subseteq> U"
proof -
  have path: "\<And>x y. (x,y) \<in> (environment_edges E)\<^sup>* \<Longrightarrow> x \<in> U \<Longrightarrow> y \<in> U"
  proof -
    fix x y assume edge: "(x,y) \<in> (environment_edges E)\<^sup>*"
    show "x \<in> U \<Longrightarrow> y \<in> U"
      using edge
      by (induction rule: rtrancl_induct)
         (use closed in \<open>auto simp: environment_edge_closed_def environment_edges_def\<close>)
  qed
  show ?thesis using roots path by (auto simp: environment_reachable_def)
qed

lemma environment_reachable_in_uses:
  assumes "environment_formed E" "roots \<subseteq> environment_uses E"
  shows "environment_reachable E roots \<subseteq> environment_uses E"
proof -
  have closed: "environment_edge_closed E (environment_uses E)"
    using assms(1)
    by (auto simp: environment_edge_closed_def environment_formed_def)
  show ?thesis by (rule environment_reachable_least[OF assms(2) closed])
qed

lemma environment_reachable_finite:
  assumes "environment_formed E" "roots \<subseteq> environment_uses E"
  shows "finite (environment_reachable E roots)"
  by (rule finite_subset[OF environment_reachable_in_uses[OF assms]
    environment_uses_finite[OF assms(1)]])

lemma environment_closed_demands:
  assumes "environment_closed E roots demands"
  shows "finite demands"
    and "\<forall>u k. (u,k) \<in> demands \<longleftrightarrow> (\<exists>!v. binds_slot E u k v)"
proof -
  have fin: "finite (environment_bindings E)"
    using assms by (simp add: environment_closed_def environment_formed_def)
  have "demands = fst ` environment_bindings E"
    using assms by (auto simp: environment_closed_def rel_dom_def intro: rev_image_eqI)
  with fin show "finite demands" by simp
  show "\<forall>u k. (u,k) \<in> demands \<longleftrightarrow> (\<exists>!v. binds_slot E u k v)"
    using assms
    by (auto simp: environment_closed_def rel_dom_def binds_slot_def environment_formed_def single_valued_def)
qed

definition restrict_environment ::
  "'u artifact_environment \<Rightarrow> 'u set \<Rightarrow> 'u artifact_environment" where
  "restrict_environment E U =
    \<lparr>environment_artifacts = {(u,R) \<in> environment_artifacts E. u \<in> U},
     environment_bindings = {((u,k),v) \<in> environment_bindings E. u \<in> U}\<rparr>"

lemma artifact_at_restriction [simp]:
  "artifact_at (restrict_environment E U) u R \<longleftrightarrow> u \<in> U \<and> artifact_at E u R"
  by (auto simp: artifact_at_def restrict_environment_def)

lemma binds_slot_restriction [simp]:
  "binds_slot (restrict_environment E U) u k v \<longleftrightarrow> u \<in> U \<and> binds_slot E u k v"
  by (auto simp: binds_slot_def restrict_environment_def)

lemma environment_restriction_uses:
  "environment_uses (restrict_environment E U) = environment_uses E \<inter> U"
  by (auto simp: environment_uses_def rel_dom_def restrict_environment_def)

lemma environment_restriction_formed:
  assumes "environment_formed E" "environment_edge_closed E U"
  shows "environment_formed (restrict_environment E U)"
proof -
  have af: "finite (environment_artifacts (restrict_environment E U))"
    and bf: "finite (environment_bindings (restrict_environment E U))"
    using assms(1)
    by (auto simp: restrict_environment_def environment_formed_def
      intro: finite_subset[of _ "environment_artifacts E"] finite_subset[of _ "environment_bindings E"])
  show ?thesis using assms af bf
    by (auto simp: environment_formed_def environment_edge_closed_def
      environment_restriction_uses single_valued_def restrict_environment_def
      artifact_at_def binds_slot_def environment_uses_def rel_dom_def; blast)
qed

lemma environment_restriction_agrees:
  "environment_agrees_on E (restrict_environment E U) U"
  by (simp add: environment_agrees_on_def)

lemma environment_restriction_interpretation:
  assumes "environment_edge_closed E U" "u \<in> U"
  shows "interpret_citation (restrict_environment E U) u c t = interpret_citation E u c t"
  using citation_environment_locality[OF environment_restriction_agrees assms] by simp

lemma environment_restriction_reachable:
  assumes roots: "roots \<subseteq> U" and closed: "environment_edge_closed E U"
  shows "environment_reachable (restrict_environment E U) roots = environment_reachable E roots"
proof
  have sub: "environment_edges (restrict_environment E U) \<subseteq> environment_edges E"
    by (auto simp: environment_edges_def)
  show "environment_reachable (restrict_environment E U) roots \<subseteq> environment_reachable E roots"
    using rtrancl_mono[OF sub] by (auto simp: environment_reachable_def)
  have path: "\<And>r v. (r,v) \<in> (environment_edges E)\<^sup>* \<Longrightarrow>
    r \<in> roots \<Longrightarrow> (r,v) \<in> (environment_edges (restrict_environment E U))\<^sup>*"
  proof -
    fix r v
    assume rv: "(r,v) \<in> (environment_edges E)\<^sup>*" and rt: "r \<in> roots"
    from rv show "(r,v) \<in> (environment_edges (restrict_environment E U))\<^sup>*"
    proof (induction rule: rtrancl_induct)
      case base show ?case by simp
    next
      case (step y z)
      have yu: "y \<in> U"
        using step.hyps(1) rt environment_reachable_least[OF roots closed]
        by (auto simp: environment_reachable_def)
      have yz: "(y,z) \<in> environment_edges (restrict_environment E U)"
        using step.hyps(2) yu by (auto simp: environment_edges_def)
      show ?case by (rule rtrancl_into_rtrancl[OF step.IH yz])
    qed
  qed
  show "environment_reachable E roots \<subseteq> environment_reachable (restrict_environment E U) roots"
    using path by (auto simp: environment_reachable_def)
qed

lemma environment_closure_can_be_restricted:
  assumes formed: "environment_formed E" and roots: "roots \<subseteq> environment_uses E"
  defines "U \<equiv> environment_reachable E roots"
  shows "environment_closed (restrict_environment E U) roots
    (rel_dom (environment_bindings (restrict_environment E U)))"
proof -
  have closed: "environment_edge_closed E U"
    unfolding U_def by (rule environment_reachable_edge_closed)
  have rsub: "roots \<subseteq> U"
    unfolding U_def by (rule environment_roots_reachable)
  have usub: "U \<subseteq> environment_uses E"
    unfolding U_def by (rule environment_reachable_in_uses[OF formed roots])
  have ef: "environment_formed (restrict_environment E U)"
    by (rule environment_restriction_formed[OF formed closed])
  have reach: "environment_reachable (restrict_environment E U) roots = U"
    using environment_restriction_reachable[OF rsub closed] by (simp add: U_def)
  show ?thesis using ef roots rsub usub reach
    by (auto simp: environment_closed_def environment_restriction_uses)
qed

section \<open>Explicit environment composition\<close>

definition merge_environment ::
  "'u artifact_environment \<Rightarrow> 'u artifact_environment \<Rightarrow> 'u artifact_environment" where
  "merge_environment E F =
    \<lparr>environment_artifacts = environment_artifacts E \<union> environment_artifacts F,
     environment_bindings = environment_bindings E \<union> environment_bindings F\<rparr>"

definition environments_compatible ::
  "'u artifact_environment \<Rightarrow> 'u artifact_environment \<Rightarrow> bool" where
  "environments_compatible E F \<longleftrightarrow>
    (\<forall>u R S. artifact_at E u R \<longrightarrow> artifact_at F u S \<longrightarrow> R = S) \<and>
    (\<forall>u k v w. binds_slot E u k v \<longrightarrow> binds_slot F u k w \<longrightarrow> v = w)"

lemma artifact_at_merge [simp]:
  "artifact_at (merge_environment E F) u R \<longleftrightarrow> artifact_at E u R \<or> artifact_at F u R"
  by (simp add: artifact_at_def merge_environment_def)

lemma binds_slot_merge [simp]:
  "binds_slot (merge_environment E F) u k v \<longleftrightarrow> binds_slot E u k v \<or> binds_slot F u k v"
  by (simp add: binds_slot_def merge_environment_def)

lemma environment_merge_uses:
  "environment_uses (merge_environment E F) = environment_uses E \<union> environment_uses F"
  by (auto simp: environment_uses_def rel_dom_def merge_environment_def)

lemma environment_merge_formed_iff:
  assumes "environment_formed E" "environment_formed F"
  shows "environment_formed (merge_environment E F) \<longleftrightarrow> environments_compatible E F"
proof -
  have asv: "single_valued (environment_artifacts E)" "single_valued (environment_artifacts F)"
    and bsv: "single_valued (environment_bindings E)" "single_valued (environment_bindings F)"
    using assms by (auto simp: environment_formed_def)
  have sv: "single_valued (environment_artifacts (merge_environment E F)) \<and>
      single_valued (environment_bindings (merge_environment E F)) \<longleftrightarrow>
    environments_compatible E F"
    using single_valued_union_iff[OF asv] single_valued_union_iff[OF bsv]
    by (auto simp: merge_environment_def environments_compatible_def artifact_at_def binds_slot_def)
  have af: "finite (environment_artifacts (merge_environment E F))"
    and bf: "finite (environment_bindings (merge_environment E F))"
    using assms by (auto simp: environment_formed_def merge_environment_def)
  have vals: "\<forall>u R. artifact_at (merge_environment E F) u R \<longrightarrow> exact_formed R"
    using assms by (auto simp: environment_formed_def)
  have refs: "\<forall>u k v. binds_slot (merge_environment E F) u k v \<longrightarrow>
    (\<exists>R. artifact_at (merge_environment E F) u R \<and> k \<in> rra_carrier (object_structure R)) \<and>
    v \<in> environment_uses (merge_environment E F)"
    using assms
    by (auto simp: environment_formed_def environment_merge_uses; blast)
  show ?thesis using sv af bf vals refs by (simp add: environment_formed_def)
qed

lemma environment_merge_preserves_interpretation:
  assumes "interpret_citation E u c t"
  shows "interpret_citation (merge_environment E F) u c t"
  using assms by (cases c) auto

lemma compatible_merge_cannot_rebind:
  assumes "environment_formed E" "environment_formed F" "environments_compatible E F"
    and old: "interpret_citation E u c x"
    and combined: "interpret_citation (merge_environment E F) u c y"
  shows "x = y"
proof -
  have formed: "environment_formed (merge_environment E F)"
    using assms(1-3) environment_merge_formed_iff by blast
  have retained: "interpret_citation (merge_environment E F) u c x"
    by (rule environment_merge_preserves_interpretation[OF old])
  show ?thesis by (rule citation_interpretation_functional[OF formed retained combined])
qed

definition rename_environment ::
  "('u \<Rightarrow> 'v) \<Rightarrow> 'u artifact_environment \<Rightarrow> 'v artifact_environment" where
  "rename_environment h E =
    \<lparr>environment_artifacts = (\<lambda>(u,R). (h u,R)) ` environment_artifacts E,
     environment_bindings = (\<lambda>((u,k),v). ((h u,k),h v)) ` environment_bindings E\<rparr>"

lemma artifact_at_renaming:
  "artifact_at (rename_environment h E) v R \<longleftrightarrow>
    (\<exists>u. v = h u \<and> artifact_at E u R)"
  by (auto simp: artifact_at_def rename_environment_def intro: rev_image_eqI)

lemma binds_slot_renaming:
  "binds_slot (rename_environment h E) u k v \<longleftrightarrow>
    (\<exists>a b. u = h a \<and> v = h b \<and> binds_slot E a k b)"
  by (auto simp: binds_slot_def rename_environment_def intro: rev_image_eqI)

lemma environment_renaming_uses:
  "environment_uses (rename_environment h E) = h ` environment_uses E"
  by (auto simp: environment_uses_def rel_dom_def rename_environment_def intro: rev_image_eqI)

lemma artifact_at_renamed_use:
  assumes "inj h"
  shows "artifact_at (rename_environment h E) (h u) R \<longleftrightarrow> artifact_at E u R"
  using assms by (auto simp: artifact_at_renaming inj_eq)

lemma binds_slot_renamed_use:
  assumes "inj h"
  shows "binds_slot (rename_environment h E) (h u) k (h v) \<longleftrightarrow> binds_slot E u k v"
  using assms by (auto simp: binds_slot_renaming inj_eq)

lemma environment_renaming_formed:
  assumes "environment_formed E" "inj h"
  shows "environment_formed (rename_environment h E)"
proof -
  have af: "finite (environment_artifacts (rename_environment h E))"
    and bf: "finite (environment_bindings (rename_environment h E))"
    using assms(1) by (auto simp: environment_formed_def rename_environment_def)
  have asv: "single_valued (environment_artifacts (rename_environment h E))"
    and bsv: "single_valued (environment_bindings (rename_environment h E))"
    using assms
    by (auto simp: environment_formed_def rename_environment_def single_valued_def inj_eq)
  have vals: "\<forall>u R. artifact_at (rename_environment h E) u R \<longrightarrow> exact_formed R"
    using assms(1) by (auto simp: environment_formed_def artifact_at_renaming)
  have refs: "\<forall>u k v. binds_slot (rename_environment h E) u k v \<longrightarrow>
    (\<exists>R. artifact_at (rename_environment h E) u R \<and> k \<in> rra_carrier (object_structure R)) \<and>
    v \<in> environment_uses (rename_environment h E)"
    using assms(1)
    by (auto simp: environment_formed_def artifact_at_renaming binds_slot_renaming
      environment_renaming_uses; blast)
  show ?thesis using af bf asv bsv vals refs by (simp add: environment_formed_def)
qed

lemma citation_use_renaming:
  assumes "inj h"
  shows "interpret_citation (rename_environment h E) (h u) c t = interpret_citation E u c t"
  using assms
  by (cases c; auto simp: artifact_at_renaming binds_slot_renaming inj_eq)

lemma citation_location_use_renaming:
  assumes "inj h"
  shows "citation_location (rename_environment h E) (h u) c (h v) a \<longleftrightarrow>
    citation_location E u c v a"
  using assms
  by (cases c; auto simp: artifact_at_renamed_use[OF assms] binds_slot_renamed_use[OF assms] inj_eq)

definition sum_environment ::
  "'u artifact_environment \<Rightarrow> 'v artifact_environment \<Rightarrow> ('u + 'v) artifact_environment" where
  "sum_environment E F = merge_environment (rename_environment Inl E) (rename_environment Inr F)"

lemma separated_environments_compatible:
  "environments_compatible (rename_environment Inl E) (rename_environment Inr F)"
  by (auto simp: environments_compatible_def artifact_at_renaming binds_slot_renaming)

lemma sum_environment_formed:
  assumes "environment_formed E" "environment_formed F"
  shows "environment_formed (sum_environment E F)"
  unfolding sum_environment_def
  using environment_merge_formed_iff[
    OF environment_renaming_formed[OF assms(1), of Inl]
       environment_renaming_formed[OF assms(2), of Inr]]
    separated_environments_compatible[of E F]
  by simp

lemma sum_environment_left_interpretation:
  "interpret_citation (sum_environment E F) (Inl u) c t = interpret_citation E u c t"
  by (cases c; auto simp: sum_environment_def artifact_at_renaming binds_slot_renaming)

lemma sum_environment_right_interpretation:
  "interpret_citation (sum_environment E F) (Inr u) c t = interpret_citation F u c t"
  by (cases c; auto simp: sum_environment_def artifact_at_renaming binds_slot_renaming)

lemma repeated_artifact_uses_stay_distinct:
  assumes "artifact_at E u R" "artifact_at F v R"
  shows "artifact_at (sum_environment E F) (Inl u) R"
    and "artifact_at (sum_environment E F) (Inr v) R"
    and "(Inl u :: 'u + 'v) \<noteq> Inr v"
  using assms by (auto simp: sum_environment_def artifact_at_renaming)

text \<open>
  The sum constructors label copies in this construction account, exactly as
  piece occurrences label assembly inputs. No such label is added to the
  artifact values. Shared interfaces use merge only after explicit
  identification, and formation then requires agreement of both kinds of
  assignment.
\<close>

section \<open>Equal artifacts do not identify semantic uses\<close>

definition singleton_environment :: "exact_artifact \<Rightarrow> unit artifact_environment" where
  "singleton_environment R =
    \<lparr>environment_artifacts = {((),R)}, environment_bindings = {}\<rparr>"

lemma singleton_environment_closed:
  assumes "exact_formed R"
  shows "environment_closed (singleton_environment R) {()} {}"
  using assms
  by (auto simp: environment_closed_def environment_formed_def singleton_environment_def
    artifact_at_def binds_slot_def environment_uses_def environment_reachable_def
    environment_edges_def rel_dom_def single_valued_def)

definition one_binding_environment ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> bool artifact_environment" where
  "one_binding_environment R k S =
    \<lparr>environment_artifacts = {(False,R),(True,S)},
     environment_bindings = {((False,k),True)}\<rparr>"

lemma one_binding_environment_closed:
  assumes "exact_formed R" "exact_formed S" "k \<in> rra_carrier (object_structure R)"
  shows "environment_closed (one_binding_environment R k S) {False} {(False,k)}"
proof -
  have ef: "environment_formed (one_binding_environment R k S)"
    using assms
    by (auto simp: environment_formed_def one_binding_environment_def artifact_at_def
      binds_slot_def environment_uses_def rel_dom_def single_valued_def)
  have reach: "environment_reachable (one_binding_environment R k S) {False} = UNIV"
  proof (rule set_eqI)
    fix b
    show "b \<in> environment_reachable (one_binding_environment R k S) {False} \<longleftrightarrow> b \<in> UNIV"
      by (cases b)
         (auto simp: environment_reachable_def environment_edges_def binds_slot_def one_binding_environment_def)
  qed
  show ?thesis using ef reach
    by (auto simp: environment_closed_def environment_uses_def rel_dom_def one_binding_environment_def)
qed

lemma same_artifact_different_closed_interpretations:
  "\<exists>E F :: bool artifact_environment. \<exists>R x y.
    environment_closed E {False} {(False,[0])} \<and>
    environment_closed F {False} {(False,[0])} \<and>
    artifact_at E False R \<and> artifact_at F False R \<and>
    anchor_formed (R,[]) \<and>
    interpret_citation E False (External_Whole [0]) x \<and>
    interpret_citation F False (External_Whole [0]) y \<and> x \<noteq> y"
proof -
  let ?R = "\<lparr>object_structure =
    \<lparr>rra_carrier = {[],[0]}, rra_incidence = {([],[0],[0])}\<rparr>,
    object_data = empty_basis\<rparr> :: exact_artifact"
  let ?E = "one_binding_environment ?R [0] empty_artifact"
  let ?F = "one_binding_environment ?R [0] ?R"
  have rf: "exact_formed ?R"
    by (simp add: exact_formed_def object_formed_def rra_formed_def octets_formed_def)
  have ec: "environment_closed ?E {False} {(False,[0])}"
    by (rule one_binding_environment_closed[OF rf empty_artifact_formed]) simp
  have fc: "environment_closed ?F {False} {(False,[0])}"
    by (rule one_binding_environment_closed[OF rf rf]) simp
  have es: "artifact_at ?E False ?R" and fs: "artifact_at ?F False ?R"
    by (simp_all add: artifact_at_def one_binding_environment_def)
  have af: "anchor_formed (?R,[])"
    using rf by (simp add: anchor_formed_def)
  have ei: "interpret_citation ?E False (External_Whole [0]) (Whole_Artifact empty_artifact)"
    using empty_artifact_formed
    by (auto simp: one_binding_environment_def artifact_at_def binds_slot_def)
  have fi: "interpret_citation ?F False (External_Whole [0]) (Whole_Artifact ?R)"
    using rf by (auto simp: one_binding_environment_def artifact_at_def binds_slot_def)
  have neq: "Whole_Artifact empty_artifact \<noteq> Whole_Artifact ?R"
    by (simp add: empty_artifact_def exact_identity_iff rra_identity)
  show ?thesis
    by (rule exI[of _ ?E], rule exI[of _ ?F], rule exI[of _ ?R],
        rule exI[of _ "Whole_Artifact empty_artifact"], rule exI[of _ "Whole_Artifact ?R"])
       (use ec fc es fs af ei fi neq in blast)
qed

section \<open>Inclusion of explicit environment material\<close>

definition environment_included :: "'u artifact_environment \<Rightarrow> 'u artifact_environment \<Rightarrow> bool" where
  "environment_included E F \<longleftrightarrow>
    environment_artifacts E \<subseteq> environment_artifacts F \<and>
    environment_bindings E \<subseteq> environment_bindings F"

lemma included_uses:
  assumes "environment_included E F"
  shows "environment_uses E \<subseteq> environment_uses F"
  using assms by (auto simp: environment_included_def environment_uses_def rel_dom_def)

lemma environment_included_antisym:
  assumes "environment_included E F" "environment_included F E"
  shows "E = F"
  using assms by (cases E; cases F) (auto simp: environment_included_def)

lemma included_artifact:
  assumes "environment_included E F" "artifact_at E u R"
  shows "artifact_at F u R"
  using assms by (auto simp: environment_included_def artifact_at_def)

lemma included_binding:
  assumes "environment_included E F" "binds_slot E u k v"
  shows "binds_slot F u k v"
  using assms by (auto simp: environment_included_def binds_slot_def)

lemma environment_edges_included:
  assumes "environment_included E F"
  shows "environment_edges E\<subseteq>environment_edges F"
  using included_binding[OF assms] by (auto simp: environment_edges_def)

lemma environment_reachable_mono:
  assumes included: "environment_included E F" and roots: "U\<subseteq>V"
  shows "environment_reachable E U\<subseteq>environment_reachable F V"
proof -
  have paths: "(environment_edges E)\<^sup>*\<subseteq>(environment_edges F)\<^sup>*"
    by (rule rtrancl_mono[OF environment_edges_included[OF included]])
  show ?thesis using roots paths by (auto simp: environment_reachable_def)
qed

lemma included_interpretation:
  assumes "environment_included E F" "interpret_citation E u c t"
  shows "interpret_citation F u c t"
  using assms by (cases c) (auto dest: included_artifact included_binding)

lemma included_location:
  assumes "environment_included E F" "citation_location E u c v a"
  shows "citation_location F u c v a"
  using assms by (cases c) (auto dest: included_artifact included_binding)

lemma environment_included_refl [simp]: "environment_included E E"
  by (simp add: environment_included_def)

lemma environment_included_trans:
  assumes "environment_included E F" "environment_included F G"
  shows "environment_included E G"
  using assms by (auto simp: environment_included_def)

lemma environment_included_merge_left:
  "environment_included E (merge_environment E F)"
  by (auto simp: environment_included_def merge_environment_def)

lemma environment_included_merge_right:
  "environment_included F (merge_environment E F)"
  by (auto simp: environment_included_def merge_environment_def)


section \<open>Placing one fresh artifact use without changing existing bindings\<close>

definition add_artifact_use ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> exact_artifact \<Rightarrow> 'u artifact_environment" where
  "add_artifact_use E u R = E\<lparr>environment_artifacts := insert (u,R) (environment_artifacts E)\<rparr>"

lemma added_artifact_at [simp]:
  "artifact_at (add_artifact_use E u R) v S \<longleftrightarrow> (v=u \<and> S=R) \<or> artifact_at E v S"
  by (auto simp: add_artifact_use_def artifact_at_def)

lemma added_artifact_bindings [simp]:
  "binds_slot (add_artifact_use E u R) v k w \<longleftrightarrow> binds_slot E v k w"
  by (simp add: add_artifact_use_def binds_slot_def)

lemma added_artifact_uses [simp]:
  "environment_uses (add_artifact_use E u R) = insert u (environment_uses E)"
  by (auto simp: add_artifact_use_def environment_uses_def rel_dom_def)

lemma added_artifact_included: "environment_included E (add_artifact_use E u R)"
  by (auto simp: environment_included_def add_artifact_use_def)

lemma added_artifact_formed:
  assumes ef: "environment_formed E" and rf: "exact_formed R" and fresh: "u \<notin> environment_uses E"
  shows "environment_formed (add_artifact_use E u R)"
proof -
  have absent: "\<forall>S. \<not> artifact_at E u S" using fresh by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
  have artifact_graph: "single_valued (insert (u,R) (environment_artifacts E))"
    using ef absent by (auto simp: environment_formed_def artifact_at_def single_valued_def)
  have refs: "\<forall>v k w. binds_slot (add_artifact_use E u R) v k w \<longrightarrow>
    (\<exists>S. artifact_at (add_artifact_use E u R) v S \<and> k \<in> rra_carrier (object_structure S)) \<and>
    w \<in> environment_uses (add_artifact_use E u R)"
  proof (intro allI impI)
    fix v k w assume added: "binds_slot (add_artifact_use E u R) v k w"
    have old: "binds_slot E v k w" using added by simp
    obtain S where original: "artifact_at E v S" "k \<in> rra_carrier (object_structure S)" "w \<in> environment_uses E"
      using ef old unfolding environment_formed_def by blast
    show "(\<exists>S. artifact_at (add_artifact_use E u R) v S \<and> k \<in> rra_carrier (object_structure S)) \<and>
      w \<in> environment_uses (add_artifact_use E u R)" using original by auto
  qed
  show ?thesis using ef rf artifact_graph refs
    by (auto simp: environment_formed_def add_artifact_use_def artifact_at_def)
qed

section \<open>Preallocating a finite family of exact artifact uses\<close>

definition artifact_family_environment :: "'u set \<Rightarrow> ('u \<Rightarrow> exact_artifact) \<Rightarrow> 'u artifact_environment" where
  "artifact_family_environment U R = \<lparr>environment_artifacts = (\<lambda>u. (u,R u)) ` U, environment_bindings = {}\<rparr>"

lemma artifact_family_at [simp]:
  "artifact_at (artifact_family_environment U R) u T \<longleftrightarrow> u \<in> U \<and> T=R u"
  by (auto simp: artifact_family_environment_def artifact_at_def)

lemma artifact_family_uses [simp]:
  "environment_uses (artifact_family_environment U R) = U"
  by (auto simp: artifact_family_environment_def environment_uses_def rel_dom_def)

lemma artifact_family_unbound [simp]:
  "\<not> binds_slot (artifact_family_environment U R) u k v"
  by (simp add: artifact_family_environment_def binds_slot_def)

lemma artifact_family_formed:
  assumes "finite U" "\<forall>u\<in>U. exact_formed (R u)"
  shows "environment_formed (artifact_family_environment U R)"
  using assms by (auto simp: environment_formed_def artifact_family_environment_def
      artifact_at_def binds_slot_def single_valued_def)

locale fresh_artifact_family =
  fixes E :: "'u artifact_environment" and U :: "'u set" and R :: "'u \<Rightarrow> exact_artifact"
  assumes existing: "environment_formed E" and finite: "finite U"
    and fresh: "U\<inter>environment_uses E={}" and formed: "\<forall>u\<in>U. exact_formed (R u)"
begin

abbreviation extended where "extended \<equiv> merge_environment E (artifact_family_environment U R)"

lemma no_old_artifact:
  assumes "u\<in>U"
  shows "\<not>artifact_at E u T"
  using assms fresh by (auto simp: environment_uses_def rel_dom_def artifact_at_def)

lemma compatible: "environments_compatible E (artifact_family_environment U R)"
  using no_old_artifact by (auto simp: environments_compatible_def)

lemma extended_formed: "environment_formed extended"
  using environment_merge_formed_iff[OF existing artifact_family_formed[OF finite formed]] compatible by blast

lemma included: "environment_included E extended" by (rule environment_included_merge_left)

lemma old_artifacts:
  assumes "u\<in>environment_uses E"
  shows "artifact_at extended u T \<longleftrightarrow> artifact_at E u T"
  using assms fresh by auto

lemma new_artifacts:
  assumes "u\<in>U"
  shows "artifact_at extended u T \<longleftrightarrow> T=R u"
  using assms no_old_artifact[OF assms] by simp

lemma bindings: "binds_slot extended u k v \<longleftrightarrow> binds_slot E u k v"
  by simp

lemma new_unbound:
  assumes member: "u\<in>U"
  shows "\<not>binds_slot extended u k v"
proof
  assume "binds_slot extended u k v"
  then have old: "binds_slot E u k v" by simp
  obtain T where art: "artifact_at E u T" using existing old unfolding environment_formed_def by blast
  show False using no_old_artifact[OF member, of T] art by blast
qed

end

end
