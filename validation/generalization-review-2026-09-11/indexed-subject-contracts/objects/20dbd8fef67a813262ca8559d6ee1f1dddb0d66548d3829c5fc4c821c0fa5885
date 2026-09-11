theory Factor_Application_Retention
  imports Factor_Presentation_Restriction Factor_Future_Applications
begin

section \<open>The complete call grammar determines its retained bindings\<close>

lemma native_application_slots_bound:
  assumes app: "native_application_at E u r d t I K" and slot: "k \<in> K"
  shows "(u,k) \<in> rel_dom (environment_bindings E)"
proof -
  obtain cite a J A where parts: "citation_location E u cite (fst d) (snd d)"
    "term_quoted_at E u a t J A" "K=citation_slots cite \<union> A"
    using app by (auto simp: native_application_at_def)
  show ?thesis using located_citation_slots_bound[OF parts(1)] term_quoted_slots_bound[OF parts(2)] slot parts(3) by auto
qed

lemma native_application_read_environment:
  assumes app: "native_application_at E u r d t I K" and boundary: "read_boundary_formed E U D"
    and source: "u \<in> U" and slots: "\<forall>k\<in>K. (u,k) \<in> D"
  shows "native_application_at (read_environment E U D) u r d t I K"
proof -
  let ?F = "read_environment E U D"
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  obtain R ps c a cite C J A where parts: "artifact_at E u R" "record_at R r ps [c,a]"
    "citation_at R c cite C" "citation_location E u cite (fst d) (snd d)"
    "term_quoted_at E u a t J A" "insert r (set ps) \<inter> (C \<union> J) = {}" "C \<inter> J = {}"
    "I=insert r (set ps \<union> C \<union> J)" "K=citation_slots cite \<union> A" "I \<inter> K = {}"
    using app by (auto simp: native_application_at_def)
  have art: "artifact_at ?F u R" using parts(1) source by (simp add: read_environment_uses_def)
  have cite_slots: "\<forall>k\<in>citation_slots cite. (u,k) \<in> D" and arg_slots: "\<forall>k\<in>A. (u,k) \<in> D"
    using slots parts(9) by auto
  have location: "citation_location ?F u cite (fst d) (snd d)"
    using read_environment_location[OF source cite_slots] parts(4) by simp
  have argument: "term_quoted_at ?F u a t J A"
    by (rule term_quoted_read_environment[OF parts(5) boundary source arg_slots])
  show ?thesis using ff art location argument parts(2,3,6-10) unfolding native_application_at_def by blast
qed

definition native_application_demands ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> ('u\<times>local_address) set" where
  "native_application_demands E u r =
    {(u,k) |d t I K k. native_application_at E u r d t I K \<and> k\<in>K}"

lemma native_application_demands_at:
  assumes app: "native_application_at E u r d t I K"
  shows "native_application_demands E u r=image (Pair u) K"
proof
  show "native_application_demands E u r\<subseteq>image (Pair u) K"
  proof
    fix x assume member: "x\<in>native_application_demands E u r"
    obtain e v J L k where parts: "x=(u,k)" "native_application_at E u r e v J L" "k\<in>L"
      using member by (auto simp: native_application_demands_def)
    have same: "L=K" using native_application_unique[OF parts(2) app] by blast
    show "x\<in>image (Pair u) K" using parts(1,3) same by auto
  qed
  show "image (Pair u) K\<subseteq>native_application_demands E u r"
  proof
    fix x assume member: "x\<in>image (Pair u) K"
    obtain k where parts: "x=(u,k)" "k\<in>K" using member by auto
    show "x\<in>native_application_demands E u r" unfolding native_application_demands_def
      by (rule CollectI, rule exI[of _ d], rule exI[of _ t], rule exI[of _ I],
          rule exI[of _ K], rule exI[of _ k]) (use app parts in simp)
  qed
qed

theorem native_application_read_boundary:
  assumes app: "native_application_at E u r d t I K"
  shows "read_boundary_formed E {u} (native_application_demands E u r)"
proof -
  obtain R where ef: "environment_formed E" and art: "artifact_at E u R"
    using app by (auto simp: native_application_at_def)
  have source: "u\<in>environment_uses E" using art by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
  have slots: "image (Pair u) K\<subseteq>rel_dom (environment_bindings E)"
    using native_application_slots_bound[OF app] by blast
  show ?thesis using ef source slots native_application_demands_at[OF app]
    by (auto simp: read_boundary_formed_def)
qed

lemma native_application_demands_stable:
  assumes app: "native_application_at E u r d t I K" and boundary: "read_boundary_formed E U D"
    and source: "u\<in>U" and demands: "native_application_demands E u r\<subseteq>D"
  shows "native_application_demands (read_environment E U D) u r=native_application_demands E u r"
proof -
  have slots: "\<forall>k\<in>K. (u,k)\<in>D" using demands native_application_demands_at[OF app] by blast
  have kept: "native_application_at (read_environment E U D) u r d t I K"
    by (rule native_application_read_environment[OF app boundary source slots])
  show ?thesis using native_application_demands_at[OF kept] native_application_demands_at[OF app] by simp
qed

lemma native_application_demands_included:
  assumes app: "native_application_at E u r d t I K" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_application_demands F u r=native_application_demands E u r"
  using native_application_demands_at[OF native_application_included[OF app included ff]]
    native_application_demands_at[OF app] by simp

text \<open>
  Call retention follows its actual citation and term quotation. The source
  artifact and every demanded binding are retained exactly; the targets'
  outgoing bindings are needed only when another selected reader inspects them.
\<close>

end
