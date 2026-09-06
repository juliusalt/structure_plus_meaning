theory Factor_Judgment_Retention
  imports Factor_Application_Retention
begin

section \<open>The program and call determine their complete reference boundary\<close>

definition native_judgment_sources ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> 'u set" where
  "native_judgment_sources E pu pr au=native_package_sources E pu pr \<union> {au}"

definition native_judgment_demands ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u \<Rightarrow> local_address \<Rightarrow> ('u\<times>local_address) set" where
  "native_judgment_demands E pu pr au ar=
    native_package_demands E pu pr \<union> native_application_demands E au ar"

definition native_judgment_environment ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u \<Rightarrow> local_address \<Rightarrow> 'u artifact_environment" where
  "native_judgment_environment E pu pr au ar=
    read_environment E (native_judgment_sources E pu pr au) (native_judgment_demands E pu pr au ar)"

lemma native_judgment_read_boundary:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "read_boundary_formed E (native_judgment_sources E pu pr au) (native_judgment_demands E pu pr au ar)"
  unfolding native_judgment_sources_def native_judgment_demands_def
  by (rule read_boundary_union[OF native_package_read_boundary[OF package] native_application_read_boundary[OF app]])

lemma native_judgment_environment_included:
  "environment_included (native_judgment_environment E pu pr au ar) E"
  unfolding native_judgment_environment_def by (rule read_environment_included)

lemma native_judgment_boundary_included:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and included: "environment_included E F" and ff: "environment_formed F"
  shows "native_judgment_sources F pu pr au=native_judgment_sources E pu pr au"
    "native_judgment_demands F pu pr au ar=native_judgment_demands E pu pr au ar"
  using native_package_boundary_included[OF package included ff]
    native_application_demands_included[OF app included ff]
  by (simp_all add: native_judgment_sources_def native_judgment_demands_def)

theorem native_judgment_environment_recovers:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_package_at (native_judgment_environment E pu pr au ar) pu pr P"
    "native_application_at (native_judgment_environment E pu pr au ar) au ar d t I K"
    "environment_formed (native_judgment_environment E pu pr au ar)"
proof -
  let ?U = "native_judgment_sources E pu pr au"
  let ?D = "native_judgment_demands E pu pr au ar"
  let ?F = "native_judgment_environment E pu pr au ar"
  have boundary: "read_boundary_formed E ?U ?D" by (rule native_judgment_read_boundary[OF package app])
  have ff: "environment_formed ?F"
    unfolding native_judgment_environment_def by (rule read_environment_formed[OF boundary])
  have program: "environment_included (native_package_environment E pu pr) ?F"
    unfolding native_package_environment_def native_judgment_environment_def
    by (rule read_environment_mono) (auto simp: native_judgment_sources_def native_judgment_demands_def)
  show "native_package_at ?F pu pr P" by (rule native_package_dependency_locality[OF package ff program])
  have source: "au\<in>?U" by (simp add: native_judgment_sources_def)
  have slots: "\<forall>k\<in>K. (au,k)\<in>?D"
    by (simp add: native_judgment_demands_def native_application_demands_at[OF app])
  show "native_application_at ?F au ar d t I K"
    unfolding native_judgment_environment_def
    by (rule native_application_read_environment[OF app boundary source slots])
  show "environment_formed ?F" by (rule ff)
qed

lemma native_judgment_environment_boundary:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_judgment_sources (native_judgment_environment E pu pr au ar) pu pr au=native_judgment_sources E pu pr au"
    "native_judgment_demands (native_judgment_environment E pu pr au ar) pu pr au ar=native_judgment_demands E pu pr au ar"
proof -
  have ef: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have kept: "native_package_at (native_judgment_environment E pu pr au ar) pu pr P"
    "native_application_at (native_judgment_environment E pu pr au ar) au ar d t I K"
    using native_judgment_environment_recovers(1,2)[OF package app] by blast+
  show "native_judgment_sources (native_judgment_environment E pu pr au ar) pu pr au=native_judgment_sources E pu pr au"
    "native_judgment_demands (native_judgment_environment E pu pr au ar) pu pr au ar=native_judgment_demands E pu pr au ar"
    using native_judgment_boundary_included[OF kept native_judgment_environment_included ef] by simp_all
qed

theorem native_judgment_environment_idempotent:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_judgment_environment (native_judgment_environment E pu pr au ar) pu pr au ar =
    native_judgment_environment E pu pr au ar"
  using native_judgment_environment_boundary[OF package app]
  by (simp add: native_judgment_environment_def read_environment_idempotent)

theorem native_judgment_program_environment:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_package_environment (native_judgment_environment E pu pr au ar) pu pr =
    native_package_environment E pu pr"
proof -
  have ef: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have kept: "native_package_at (native_judgment_environment E pu pr au ar) pu pr P"
    by (rule native_judgment_environment_recovers(1)[OF package app])
  show ?thesis
    using native_package_environment_extension[OF kept native_judgment_environment_included ef] by simp
qed

theorem native_judgment_environment_closed:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "environment_closed (native_judgment_environment E pu pr au ar) {pu,au}
    (native_judgment_demands (native_judgment_environment E pu pr au ar) pu pr au ar)"
proof -
  let ?U = "native_judgment_sources E pu pr au"
  let ?D = "native_judgment_demands E pu pr au ar"
  let ?F = "native_judgment_environment E pu pr au ar"
  have boundary: "read_boundary_formed E ?U ?D" by (rule native_judgment_read_boundary[OF package app])
  have roots: "{pu,au}\<subseteq>?U"
    by (auto simp: native_judgment_sources_def native_package_sources_def)
  have sources: "native_package_sources ?F pu pr=native_package_sources E pu pr"
  proof -
    have kept: "native_package_at ?F pu pr P" by (rule native_judgment_environment_recovers(1)[OF package app])
    have ef: "environment_formed E"
      using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
    show ?thesis using native_package_boundary_included(1)[OF kept native_judgment_environment_included ef] by simp
  qed
  have root_inclusion: "environment_reachable ?F {pu}\<subseteq>environment_reachable ?F {pu,au}"
    by (rule environment_reachable_mono[OF environment_included_refl]) auto
  have program: "native_package_sources E pu pr\<subseteq>environment_reachable ?F {pu,au}"
    using native_package_sources_reachable[of ?F pu pr] sources root_inclusion by blast
  have call: "{au}\<subseteq>environment_reachable ?F {pu,au}"
    by (auto simp: environment_reachable_def)
  have reach: "?U\<subseteq>environment_reachable ?F {pu,au}"
    using program call by (auto simp: native_judgment_sources_def)
  have closed: "environment_closed ?F {pu,au} ?D"
    using read_environment_closed_from[OF boundary roots] reach by (simp add: native_judgment_environment_def)
  show ?thesis using closed native_judgment_environment_boundary(2)[OF package app] by simp
qed

theorem native_judgment_environment_least:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and included: "environment_included F E"
    and retained_package: "native_package_at F pu pr P" and retained_app: "native_application_at F au ar d t J L"
  shows "environment_included (native_judgment_environment E pu pr au ar) F"
proof -
  have ef: "environment_formed E" and ff: "environment_formed F"
    using native_package_projection(1)[OF package] native_package_projection(1)[OF retained_package]
    by (auto simp: native_package_formed_def)
  have same: "native_judgment_sources E pu pr au=native_judgment_sources F pu pr au"
    "native_judgment_demands E pu pr au ar=native_judgment_demands F pu pr au ar"
    using native_judgment_boundary_included[OF retained_package retained_app included ef] by blast+
  have boundary: "read_boundary_formed F (native_judgment_sources F pu pr au) (native_judgment_demands F pu pr au ar)"
    by (rule native_judgment_read_boundary[OF retained_package retained_app])
  have sources: "native_judgment_sources E pu pr au\<subseteq>environment_uses F"
    and demands: "native_judgment_demands E pu pr au ar\<subseteq>rel_dom (environment_bindings F)"
    using boundary same by (auto simp: read_boundary_formed_def)
  show ?thesis unfolding native_judgment_environment_def
    by (rule read_environment_least[OF ef ff included sources demands])
qed

theorem native_judgment_environment_extension:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and included: "environment_included E F" and ff: "environment_formed F"
  shows "native_judgment_environment F pu pr au ar=native_judgment_environment E pu pr au ar"
proof -
  let ?A = "native_judgment_environment E pu pr au ar"
  let ?B = "native_judgment_environment F pu pr au ar"
  have future_package: "native_package_at F pu pr P" by (rule native_package_included[OF package included ff])
  have future_app: "native_application_at F au ar d t I K" by (rule native_application_included[OF app included ff])
  have old: "native_package_at ?A pu pr P" "native_application_at ?A au ar d t I K"
    using native_judgment_environment_recovers(1,2)[OF package app] by blast+
  have future: "native_package_at ?B pu pr P" "native_application_at ?B au ar d t I K"
    using native_judgment_environment_recovers(1,2)[OF future_package future_app] by blast+
  have old_in_future: "environment_included ?A F"
    by (rule environment_included_trans[OF native_judgment_environment_included included])
  have upper: "environment_included ?B ?A"
    by (rule native_judgment_environment_least[OF future_package future_app old_in_future old])
  have new_in_old: "environment_included ?B E"
    by (rule environment_included_trans[OF upper native_judgment_environment_included])
  have lower: "environment_included ?A ?B"
    by (rule native_judgment_environment_least[OF package app new_in_old future])
  show ?thesis by (rule environment_included_antisym[OF upper lower])
qed


theorem native_judgment_environment_truth:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_positive_holds (native_judgment_environment E pu pr au ar) pu pr au ar \<longleftrightarrow>
    native_positive_holds E pu pr au ar"
proof -
  have kept: "native_package_at (native_judgment_environment E pu pr au ar) pu pr P"
    "native_application_at (native_judgment_environment E pu pr au ar) au ar d t I K"
    using native_judgment_environment_recovers(1,2)[OF package app] by blast+
  show ?thesis
    by (simp only: native_positive_holds_with_reads[OF kept] native_positive_holds_with_reads[OF package app])
qed

lemma native_judgment_positions:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "(pu,pr)\<in>environment_positions E" "(au,ar)\<in>environment_positions E"
proof -
  obtain R M where art: "artifact_at E pu R" and family: "family_at R pr M"
    using package by (auto simp: native_package_at_def native_root_family_at_def)
  have program_root: "pr\<in>rra_carrier (object_structure R)"
    using family by (simp add: family_at_def)
  show "(pu,pr)\<in>environment_positions E" using art program_root by auto
  obtain S ps c a where source: "artifact_at E au S" and rec: "record_at S ar ps [c,a]"
    using app by (auto simp: native_application_at_def)
  have call_root: "ar\<in>rra_carrier (object_structure S)" using rec by (simp add: record_at_def)
  show "(au,ar)\<in>environment_positions E" using source call_root by auto
qed

text \<open>
  The program and call have a least retained environment independently of any
  derivation or evidence reader. Every retained binding comes from those two
  grammars. Recovery, native truth, and the canonical program environment are
  preserved. The result is closed from the actual program and call uses and
  is unchanged by another restriction.

  Application restriction belongs at this boundary. Its proofs have been moved
  from the proof-metadata restriction theory without changing their statements.
  Proof restriction now imports the application results.
\<close>

end
