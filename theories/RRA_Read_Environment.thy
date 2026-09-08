theory RRA_Read_Environment
  imports RRA_Citation_Closure
begin

section \<open>Retaining structural sources and the slots actually read\<close>

definition read_boundary_formed ::
  "'u artifact_environment \<Rightarrow> 'u set \<Rightarrow> ('u \<times> local_address) set \<Rightarrow> bool" where
  "read_boundary_formed E U D \<longleftrightarrow> environment_formed E \<and>
    U \<subseteq> environment_uses E \<and> D \<subseteq> rel_dom (environment_bindings E) \<and> fst ` D \<subseteq> U"

definition read_environment_uses ::
  "'u artifact_environment \<Rightarrow> 'u set \<Rightarrow> ('u \<times> local_address) set \<Rightarrow> 'u set" where
  "read_environment_uses E U D = U \<union> {v. \<exists>u k. (u,k) \<in> D \<and> binds_slot E u k v}"

definition read_environment ::
  "'u artifact_environment \<Rightarrow> 'u set \<Rightarrow> ('u \<times> local_address) set \<Rightarrow>
    'u artifact_environment" where
  "read_environment E U D =
    \<lparr>environment_artifacts = {entry\<in>environment_artifacts E. fst entry \<in> read_environment_uses E U D},
      environment_bindings = {entry\<in>environment_bindings E. fst entry \<in> D}\<rparr>"

lemma artifact_at_read_environment [simp]:
  "artifact_at (read_environment E U D) u R \<longleftrightarrow>
    u \<in> read_environment_uses E U D \<and> artifact_at E u R"
  by (auto simp: read_environment_def artifact_at_def)

lemma binds_slot_read_environment [simp]:
  "binds_slot (read_environment E U D) u k v \<longleftrightarrow> (u,k) \<in> D \<and> binds_slot E u k v"
  by (auto simp: read_environment_def binds_slot_def)

lemma read_environment_included:
  "environment_included (read_environment E U D) E"
  by (auto simp: environment_included_def read_environment_def)

lemma request_environment_as_read_environment:
  "request_environment E Q=read_environment E (fst ` Q) (requested_slots E Q)"
  by (simp add: request_environment_def requested_uses_def read_environment_def read_environment_uses_def)

lemma requested_read_boundary:
  assumes formed: "citation_requests_formed E Q"
  shows "read_boundary_formed E (fst ` Q) (requested_slots E Q)"
proof -
  have ef: "environment_formed E" using formed by (simp add: citation_requests_formed_def)
  have sources: "fst ` Q\<subseteq>environment_uses E"
    using requested_uses_subset[OF formed] by (auto simp: requested_uses_def)
  have slots: "requested_slots E Q\<subseteq>rel_dom (environment_bindings E)"
    by (rule requested_slots_subset[OF formed])
  have owners: "fst ` requested_slots E Q\<subseteq>fst ` Q"
    by (auto dest: requested_slot_source)
  show ?thesis using ef sources slots owners by (simp add: read_boundary_formed_def)
qed

lemma read_boundary_union:
  assumes "read_boundary_formed E U D" "read_boundary_formed E V C"
  shows "read_boundary_formed E (U\<union>V) (D\<union>C)"
  using assms by (auto simp: read_boundary_formed_def)

lemma read_environment_mono:
  assumes "U\<subseteq>V" "D\<subseteq>C"
  shows "environment_included (read_environment E U D) (read_environment E V C)"
  using assms by (auto simp: environment_included_def read_environment_def read_environment_uses_def)

lemma request_environment_read_included:
  assumes "image fst Q\<subseteq>U" "requested_slots E Q\<subseteq>D"
  shows "environment_included (request_environment E Q) (read_environment E U D)"
  unfolding request_environment_as_read_environment
  by (rule read_environment_mono[OF assms])

lemma read_environment_uses_subset:
  assumes "read_boundary_formed E U D"
  shows "read_environment_uses E U D \<subseteq> environment_uses E"
  using assms by (auto simp: read_boundary_formed_def read_environment_uses_def environment_formed_def; blast)

lemma read_environment_use_equation:
  assumes "read_boundary_formed E U D"
  shows "environment_uses (read_environment E U D) = read_environment_uses E U D"
  using read_environment_uses_subset[OF assms]
  by (auto simp: environment_uses_def read_environment_def rel_dom_def)

lemma read_environment_domain:
  assumes "read_boundary_formed E U D"
  shows "rel_dom (environment_bindings (read_environment E U D)) = D"
  using assms by (auto simp: read_boundary_formed_def read_environment_def rel_dom_def; blast)

lemma read_environment_formed:
  assumes boundary: "read_boundary_formed E U D"
  shows "environment_formed (read_environment E U D)"
proof -
  let ?F = "read_environment E U D"
  have ef: "environment_formed E" using boundary by (simp add: read_boundary_formed_def)
  have finite: "finite (environment_artifacts ?F)" "finite (environment_bindings ?F)"
    using ef by (auto simp: environment_formed_def read_environment_def)
  have unique: "single_valued (environment_artifacts ?F)" "single_valued (environment_bindings ?F)"
    using ef by (auto simp: environment_formed_def read_environment_def single_valued_def)
  have artifacts: "\<And>u R. artifact_at ?F u R \<Longrightarrow> exact_formed R"
    using ef by (auto simp: environment_formed_def)
  have bindings: "\<And>u k v. binds_slot ?F u k v \<Longrightarrow>
    (\<exists>R. artifact_at ?F u R \<and> k \<in> rra_carrier (object_structure R)) \<and> v \<in> environment_uses ?F"
  proof -
    fix u k v assume bind: "binds_slot ?F u k v"
    have demand: "(u,k) \<in> D" and old: "binds_slot E u k v" using bind by auto
    have source: "u \<in> U" using boundary demand by (auto simp: read_boundary_formed_def)
    obtain R where art: "artifact_at E u R" and key: "k \<in> rra_carrier (object_structure R)"
      using ef old unfolding environment_formed_def by blast
    have copied: "artifact_at ?F u R" using source art by (simp add: read_environment_uses_def)
    have target: "v \<in> read_environment_uses E U D"
      using demand old by (auto simp: read_environment_uses_def)
    show "(\<exists>R. artifact_at ?F u R \<and> k \<in> rra_carrier (object_structure R)) \<and> v \<in> environment_uses ?F"
      using copied key target read_environment_use_equation[OF boundary] by blast
  qed
  show ?thesis using finite unique artifacts bindings by (auto simp: environment_formed_def)
qed

lemma read_environment_source:
  assumes "u \<in> U"
  shows "artifact_at (read_environment E U D) u R \<longleftrightarrow> artifact_at E u R"
  using assms by (simp add: read_environment_uses_def)

lemma read_environment_external_values:
  assumes "(u,k) \<in> D"
  shows "external_slot_values (read_environment E U D) u k = external_slot_values E u k"
  using assms by (auto simp: external_slot_values_def read_environment_uses_def)

lemma read_environment_citation:
  assumes source: "u \<in> U" and slots: "\<forall>k\<in>citation_slots c. (u,k) \<in> D"
  shows "interpret_citation (read_environment E U D) u c t \<longleftrightarrow> interpret_citation E u c t"
  using source slots by (cases c) (auto simp: read_environment_uses_def)

lemma read_environment_location:
  assumes source: "u \<in> U" and slots: "\<forall>k\<in>citation_slots c. (u,k) \<in> D"
  shows "citation_location (read_environment E U D) u c v a \<longleftrightarrow> citation_location E u c v a"
  using source slots by (cases c) (auto simp: read_environment_uses_def)

lemma read_environment_reachable:
  assumes boundary: "read_boundary_formed E U D"
  shows "environment_reachable (read_environment E U D) U = read_environment_uses E U D"
proof -
  let ?F = "read_environment E U D"
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  have roots: "U \<subseteq> environment_uses ?F"
    by (simp add: read_environment_use_equation[OF boundary] read_environment_uses_def)
  have upper: "environment_reachable ?F U \<subseteq> read_environment_uses E U D"
    using environment_reachable_in_uses[OF ff roots] by (simp add: read_environment_use_equation[OF boundary])
  have lower: "read_environment_uses E U D \<subseteq> environment_reachable ?F U"
  proof
    fix v assume member: "v \<in> read_environment_uses E U D"
    show "v \<in> environment_reachable ?F U"
    proof (cases "v \<in> U")
      case True
      then show ?thesis using environment_roots_reachable[of U ?F] by blast
    next
      case False
      obtain u k where demand: "(u,k) \<in> D" and bind: "binds_slot E u k v"
        using member False by (auto simp: read_environment_uses_def)
      have source: "u \<in> U" using boundary demand by (auto simp: read_boundary_formed_def)
      have edge: "(u,v) \<in> environment_edges ?F" using demand bind by (auto simp: environment_edges_def)
      show ?thesis using source edge by (auto simp: environment_reachable_def)
    qed
  qed
  show ?thesis using upper lower by blast
qed

theorem read_environment_closed:
  assumes boundary: "read_boundary_formed E U D"
  shows "environment_closed (read_environment E U D) U D"
  using read_environment_formed[OF boundary] read_environment_use_equation[OF boundary]
    read_environment_domain[OF boundary] read_environment_reachable[OF boundary]
  by (auto simp: environment_closed_def read_environment_uses_def)

theorem read_environment_closed_from:
  assumes boundary: "read_boundary_formed E U D" and roots: "B \<subseteq> U"
    and reachable: "U \<subseteq> environment_reachable (read_environment E U D) B"
  shows "environment_closed (read_environment E U D) B D"
proof -
  let ?F = "read_environment E U D"
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  have base: "B \<subseteq> environment_uses ?F"
    using roots by (auto simp: read_environment_use_equation[OF boundary] read_environment_uses_def)
  have upper: "environment_reachable ?F B \<subseteq> environment_uses ?F"
    by (rule environment_reachable_in_uses[OF ff base])
  have lower: "environment_uses ?F \<subseteq> environment_reachable ?F B"
    using environment_reachable_least[OF reachable environment_reachable_edge_closed[of ?F B]]
    by (simp add: read_environment_use_equation[OF boundary] read_environment_reachable[OF boundary])
  show ?thesis using ff base upper lower read_environment_domain[OF boundary]
    by (auto simp: environment_closed_def)
qed

lemma read_boundary_retained:
  assumes "read_boundary_formed E U D"
  shows "read_boundary_formed (read_environment E U D) U D"
  using assms read_environment_formed[OF assms] read_environment_domain[OF assms]
    read_environment_use_equation[OF assms]
  by (auto simp: read_boundary_formed_def read_environment_uses_def)

lemma read_environment_idempotent:
  "read_environment (read_environment E U D) U D = read_environment E U D"
  by (auto simp: read_environment_def read_environment_uses_def binds_slot_def
      intro!: artifact_environment.equality)

theorem read_environment_least:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and included: "environment_included F E"
    and sources: "U \<subseteq> environment_uses F"
    and slots: "D \<subseteq> rel_dom (environment_bindings F)"
  shows "environment_included (read_environment E U D) F"
proof -
  have demands: "\<And>u k v. (u,k) \<in> D \<Longrightarrow> binds_slot E u k v \<Longrightarrow> binds_slot F u k v"
  proof -
    fix u k v assume demand: "(u,k) \<in> D" and bind: "binds_slot E u k v"
    obtain w where other: "binds_slot F u k w"
      using slots demand by (auto simp: rel_dom_def binds_slot_def)
    have in_e: "binds_slot E u k w" by (rule included_binding[OF included other])
    have same: "w = v" by (rule environment_binding_unique[OF ef in_e bind])
    show "binds_slot F u k v" using other same by simp
  qed
  have uses: "read_environment_uses E U D \<subseteq> environment_uses F"
    using sources demands ff by (auto simp: read_environment_uses_def environment_formed_def; blast)
  have artifacts: "\<And>u R. u \<in> read_environment_uses E U D \<Longrightarrow>
    artifact_at E u R \<Longrightarrow> artifact_at F u R"
  proof -
    fix u R assume member: "u \<in> read_environment_uses E U D" and art: "artifact_at E u R"
    obtain S where other: "artifact_at F u S"
      using uses member by (auto simp: environment_uses_def rel_dom_def artifact_at_def)
    have in_e: "artifact_at E u S" by (rule included_artifact[OF included other])
    have same: "S = R" by (rule environment_artifact_unique[OF ef in_e art])
    show "artifact_at F u R" using other same by simp
  qed
  show ?thesis using artifacts demands
    by (auto simp: environment_included_def read_environment_def artifact_at_def binds_slot_def)
qed

theorem read_environment_closed_fixed:
  assumes boundary: "read_boundary_formed E U D" and closed: "environment_closed E B D"
    and roots: "B\<subseteq>U"
  shows "read_environment E U D=E"
proof -
  let ?F="read_environment E U D"
  have ff: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  have bindings: "environment_bindings ?F=environment_bindings E"
    using closed by (auto simp: environment_closed_def read_environment_def rel_dom_def)
  have edges: "environment_edges ?F=environment_edges E"
    by (simp only: environment_edges_def binds_slot_def bindings)
  have retained_roots: "B\<subseteq>environment_uses ?F"
    using roots by (auto simp: read_environment_use_equation[OF boundary] read_environment_uses_def)
  have reachable: "environment_reachable E B\<subseteq>environment_uses ?F"
    using environment_reachable_in_uses[OF ff retained_roots]
    by (simp only: environment_reachable_def edges)
  have uses: "environment_uses E\<subseteq>read_environment_uses E U D"
    using closed reachable by (simp add: environment_closed_def read_environment_use_equation[OF boundary])
  have artifacts: "environment_artifacts ?F=environment_artifacts E"
    using uses by (auto simp: environment_uses_def rel_dom_def read_environment_def)
  show ?thesis by (rule artifact_environment.equality[OF artifacts bindings]) simp
qed


lemma read_environment_fixed_required_coverage:
  "read_environment E U D=E \<longleftrightarrow>
    environment_uses E\<subseteq>read_environment_uses E U D \<and>
    rel_dom (environment_bindings E)\<subseteq>D"
proof
  assume fixed: "read_environment E U D=E"
  have uses: "environment_uses E\<subseteq>read_environment_uses E U D"
  proof
    fix u assume "u\<in>environment_uses E"
    then obtain R where source: "artifact_at E u R"
      by (auto simp: environment_uses_def rel_dom_def artifact_at_def)
    have "artifact_at (read_environment E U D) u R" by (simp only: fixed; rule source)
    then show "u\<in>read_environment_uses E U D" by simp
  qed
  have slots: "rel_dom (environment_bindings E)\<subseteq>D"
  proof
    fix x assume "x\<in>rel_dom (environment_bindings E)"
    then obtain v where binding: "(x,v)\<in>environment_bindings E" by (auto simp: rel_dom_def)
    have "(x,v)\<in>environment_bindings (read_environment E U D)" by (simp only: fixed; rule binding)
    then show "x\<in>D" by (simp add: read_environment_def)
  qed
  show "environment_uses E\<subseteq>read_environment_uses E U D \<and>
    rel_dom (environment_bindings E)\<subseteq>D" using uses slots by blast
next
  assume coverage: "environment_uses E\<subseteq>read_environment_uses E U D \<and>
    rel_dom (environment_bindings E)\<subseteq>D"
  have artifacts: "environment_artifacts (read_environment E U D)=environment_artifacts E"
    using coverage by (auto simp: read_environment_def environment_uses_def rel_dom_def)
  have bindings: "environment_bindings (read_environment E U D)=environment_bindings E"
    using coverage by (auto simp: read_environment_def rel_dom_def)
  show "read_environment E U D=E" by (rule artifact_environment.equality[OF artifacts bindings]) simp
qed

text \<open>
  This finite restriction is a general helper. A higher grammar must determine
  both the structural source uses and every demanded slot. Structural reads can
  have no citations, so their source artifacts cannot be recovered from a set
  of citation requests alone. The restriction retains exact artifact values
  and the existing targets of demanded bindings; it never changes a binding.
\<close>

end
