theory Factor_Replay_Retention
  imports Factor_Proof_Reachability Factor_Application_Retention
begin

section \<open>The three readers determine one complete retention boundary\<close>

definition native_replay_sources ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> 'u native_derivation_graph \<Rightarrow> 'u set" where
  "native_replay_sources E pu pr au G =
    native_package_sources E pu pr\<union>{au}\<union>native_graph_sources G"

definition native_replay_demands ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u native_derivation_graph \<Rightarrow> ('u\<times>local_address) set" where
  "native_replay_demands E pu pr au ar G =
    native_package_demands E pu pr\<union>native_application_demands E au ar\<union>native_graph_demands E G"

definition native_replay_environment ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u native_derivation_graph \<Rightarrow> 'u artifact_environment" where
  "native_replay_environment E pu pr au ar G =
    read_environment E (native_replay_sources E pu pr au G) (native_replay_demands E pu pr au ar G)"

theorem native_replay_read_boundary:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
  shows "read_boundary_formed E (native_replay_sources E pu pr au G) (native_replay_demands E pu pr au ar G)"
  unfolding native_replay_sources_def native_replay_demands_def
  by (rule read_boundary_union[OF read_boundary_union[
    OF native_package_read_boundary[OF package] native_application_read_boundary[OF app]]
    native_graph_read_boundary[OF graph]])

lemma native_replay_environment_included:
  "environment_included (native_replay_environment E pu pr au ar G) E"
  unfolding native_replay_environment_def by (rule read_environment_included)

theorem native_replay_boundary_included:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_replay_sources F pu pr au G=native_replay_sources E pu pr au G"
    "native_replay_demands F pu pr au ar G=native_replay_demands E pu pr au ar G"
  using native_package_boundary_included[OF package included ff]
    native_application_demands_included[OF app included ff]
    native_graph_demands_included[OF graph included ff]
  by (simp_all add: native_replay_sources_def native_replay_demands_def)

theorem native_replay_environment_recovers:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
  shows "native_package_at (native_replay_environment E pu pr au ar G) pu pr P"
    "native_application_at (native_replay_environment E pu pr au ar G) au ar d t I K"
    "native_schema_graph_at (native_replay_environment E pu pr au ar G) root G"
    "environment_formed (native_replay_environment E pu pr au ar G)"
proof -
  let ?U = "native_replay_sources E pu pr au G"
  let ?D = "native_replay_demands E pu pr au ar G"
  let ?F = "native_replay_environment E pu pr au ar G"
  have boundary: "read_boundary_formed E ?U ?D" by (rule native_replay_read_boundary[OF package app graph])
  have ff: "environment_formed ?F" unfolding native_replay_environment_def by (rule read_environment_formed[OF boundary])
  have program: "environment_included (native_package_environment E pu pr) ?F"
    unfolding native_package_environment_def native_replay_environment_def
    by (rule read_environment_mono) (auto simp: native_replay_sources_def native_replay_demands_def)
  show "native_package_at ?F pu pr P" by (rule native_package_dependency_locality[OF package ff program])
  have source: "au\<in>?U" by (simp add: native_replay_sources_def)
  have slots: "\<forall>k\<in>K. (au,k)\<in>?D"
    by (simp add: native_replay_demands_def native_application_demands_at[OF app])
  show "native_application_at ?F au ar d t I K"
    unfolding native_replay_environment_def
    by (rule native_application_read_environment[OF app boundary source slots])
  show "native_schema_graph_at ?F root G" unfolding native_replay_environment_def
    by (rule native_schema_graph_read_environment[OF graph boundary])
       (auto simp: native_replay_sources_def native_replay_demands_def)
  show "environment_formed ?F" by (rule ff)
qed

theorem native_replay_environment_boundary:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
  shows "native_replay_sources (native_replay_environment E pu pr au ar G) pu pr au G=native_replay_sources E pu pr au G"
    "native_replay_demands (native_replay_environment E pu pr au ar G) pu pr au ar G=native_replay_demands E pu pr au ar G"
proof -
  have ef: "environment_formed E" by (rule native_schema_graph_environment[OF graph])
  have preserved: "native_package_at (native_replay_environment E pu pr au ar G) pu pr P"
    "native_application_at (native_replay_environment E pu pr au ar G) au ar d t I K"
    "native_schema_graph_at (native_replay_environment E pu pr au ar G) root G"
    using native_replay_environment_recovers(1-3)[OF package app graph] by blast+
  show "native_replay_sources (native_replay_environment E pu pr au ar G) pu pr au G=native_replay_sources E pu pr au G"
    "native_replay_demands (native_replay_environment E pu pr au ar G) pu pr au ar G=native_replay_demands E pu pr au ar G"
    using native_replay_boundary_included[OF preserved native_replay_environment_included ef] by simp_all
qed

theorem native_replay_environment_idempotent:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
  shows "native_replay_environment (native_replay_environment E pu pr au ar G) pu pr au ar G =
    native_replay_environment E pu pr au ar G"
  using native_replay_environment_boundary[OF package app graph]
  by (simp add: native_replay_environment_def read_environment_idempotent)

theorem native_replay_environment_closed:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G"
  shows "environment_closed (native_replay_environment E pu pr au ar G) {pu,au,fst root}
    (native_replay_demands (native_replay_environment E pu pr au ar G) pu pr au ar G)"
proof -
  let ?U = "native_replay_sources E pu pr au G"
  let ?D = "native_replay_demands E pu pr au ar G"
  let ?F = "native_replay_environment E pu pr au ar G"
  let ?B = "{pu,au,fst root}"
  have boundary: "read_boundary_formed E ?U ?D" by (rule native_replay_read_boundary[OF package app graph])
  have root: "root\<in>schema_graph_nodes G" using graph
    by (simp add: native_schema_graph_at_def schema_graph_formed_def)
  have roots: "?B\<subseteq>?U"
    using root by (auto simp: native_replay_sources_def native_package_sources_def native_graph_sources_def)
  have kept: "native_package_at ?F pu pr P" "native_application_at ?F au ar d t I K" "native_schema_graph_at ?F root G"
    using native_replay_environment_recovers(1-3)[OF package app graph] by blast+
  have ef: "environment_formed E" by (rule native_schema_graph_environment[OF graph])
  have package_sources: "native_package_sources ?F pu pr=native_package_sources E pu pr"
    using native_package_boundary_included(1)[OF kept(1) native_replay_environment_included ef] by simp
  have program_roots: "environment_reachable ?F {pu}\<subseteq>environment_reachable ?F ?B"
    by (rule environment_reachable_mono[OF environment_included_refl]) auto
  have proof_roots: "environment_reachable ?F {fst root}\<subseteq>environment_reachable ?F ?B"
    by (rule environment_reachable_mono[OF environment_included_refl]) auto
  have program: "native_package_sources E pu pr\<subseteq>environment_reachable ?F ?B"
    using native_package_sources_reachable[of ?F pu pr] package_sources program_roots by blast
  have evidence: "native_graph_sources G\<subseteq>environment_reachable ?F ?B"
    using native_graph_sources_reachable[OF kept(3)] proof_roots by blast
  have call: "{au}\<subseteq>environment_reachable ?F ?B"
    by (auto simp: environment_reachable_def)
  have reach: "?U\<subseteq>environment_reachable ?F ?B"
    using program evidence call by (auto simp: native_replay_sources_def)
  have closed: "environment_closed ?F ?B ?D"
    using read_environment_closed_from[OF boundary roots] reach by (simp add: native_replay_environment_def)
  show ?thesis using closed native_replay_environment_boundary(2)[OF package app graph] by simp
qed

theorem native_replay_environment_least:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    and graph: "native_schema_graph_at E root G" and included: "environment_included F E"
    and retained_package: "native_package_at F pu pr P" and retained_app: "native_application_at F au ar d t J L"
    and retained_graph: "native_schema_graph_at F root G"
  shows "environment_included (native_replay_environment E pu pr au ar G) F"
proof -
  have ef: "environment_formed E" by (rule native_schema_graph_environment[OF graph])
  have ff: "environment_formed F" by (rule native_schema_graph_environment[OF retained_graph])
  have same: "native_replay_sources E pu pr au G=native_replay_sources F pu pr au G"
    "native_replay_demands E pu pr au ar G=native_replay_demands F pu pr au ar G"
    using native_replay_boundary_included[OF retained_package retained_app retained_graph included ef] by blast+
  have boundary: "read_boundary_formed F (native_replay_sources F pu pr au G) (native_replay_demands F pu pr au ar G)"
    by (rule native_replay_read_boundary[OF retained_package retained_app retained_graph])
  have sources: "native_replay_sources E pu pr au G\<subseteq>environment_uses F"
    and demands: "native_replay_demands E pu pr au ar G\<subseteq>rel_dom (environment_bindings F)"
    using boundary same by (auto simp: read_boundary_formed_def)
  show ?thesis unfolding native_replay_environment_def
    by (rule read_environment_least[OF ef ff included sources demands])
qed

text \<open>
  The selected program, call, and proof supply the source uses and all demanded
  slots. Their roles do not impose a fixed number of evidence links. The
  resulting environment preserves all three readings, is closed from their
  actual roots, and is unchanged by another restriction. It is included in
  every retained subenvironment supporting the same readings. These results
  require no derivation-validity or truth premise.
\<close>

end
