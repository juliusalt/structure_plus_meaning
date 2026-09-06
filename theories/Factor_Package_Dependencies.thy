theory Factor_Package_Dependencies
  imports Factor_Presentation_Restriction
begin

section \<open>The package root determines every structural source and slot\<close>

definition native_package_roots ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u definition_site set" where
  "native_package_roots E u r = {d. \<exists>Q. native_root_family_at E u r Q \<and> d \<in> rel_ran Q}"

lemma native_package_roots_from_family:
  assumes family: "native_root_family_at E u r Q"
  shows "native_package_roots E u r = rel_ran Q"
proof -
  have unique: "\<And>W. native_root_family_at E u r W \<Longrightarrow> W = Q"
    by (rule native_root_family_unique[OF _ family])
  show ?thesis using family unique unfolding native_package_roots_def by blast
qed

definition native_package_sites ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u definition_site set" where
  "native_package_sites E u r = native_definition_sites E (native_package_roots E u r)"

definition native_package_sources ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u set" where
  "native_package_sources E u r = insert u (fst ` native_package_sites E u r)"

definition native_root_requests ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> ('u \<times> local_address) set" where
  "native_root_requests E u r = {u} \<times> family_endpoints E u r"

definition native_package_demands ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> ('u \<times> local_address) set" where
  "native_package_demands E u r = requested_slots E (native_root_requests E u r) \<union>
    {(v,k). \<exists>a. (v,a) \<in> native_package_sites E u r \<and> k \<in> native_definition_slots E v a}"

definition native_package_environment ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u artifact_environment" where
  "native_package_environment E u r =
    read_environment E (native_package_sources E u r) (native_package_demands E u r)"

lemma native_package_projection:
  assumes package: "native_package_at E u r P"
  shows "native_package_formed E (native_package_roots E u r)"
    and "P = native_program E (native_package_roots E u r)"
    and "system_definitions P = native_package_sites E u r"
proof -
  obtain Q where family: "native_root_family_at E u r Q"
    and formed: "native_package_formed E (rel_ran Q)" and prog: "P = native_program E (rel_ran Q)"
    using package by (auto simp: native_package_at_def)
  have roots: "native_package_roots E u r = rel_ran Q" by (rule native_package_roots_from_family[OF family])
  show "native_package_formed E (native_package_roots E u r)" using formed roots by simp
  show "P = native_program E (native_package_roots E u r)" using prog roots by simp
  show "system_definitions P = native_package_sites E u r"
    using native_program_definitions[OF formed] prog roots by (simp add: native_package_sites_def)
qed

lemma native_root_requests_formed:
  assumes family: "native_root_family_at E u r Q"
  shows "citation_requests_formed E (native_root_requests E u r)"
proof -
  have ef: "environment_formed E" using family by (simp add: native_root_family_at_def)
  obtain R M where parts: "artifact_at E u R" "family_at R r M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>d. (s,d) \<in> Q \<and> located_at E u a (fst d) (snd d))"
    using family by (auto simp: native_root_family_at_def)
  have ends: "family_endpoints E u r = rel_ran M" by (rule family_endpoints_from_read[OF ef parts(1,2)])
  have finite: "finite (native_root_requests E u r)"
    using finite_rel_ran[OF family_socket_graph_finite[OF parts(2)]]
    by (simp add: native_root_requests_def ends)
  have reads: "\<forall>v a. (v,a) \<in> native_root_requests E u r \<longrightarrow> (\<exists>t. anchored_at E v a t)"
  proof (intro allI impI)
    fix v a assume member: "(v,a) \<in> native_root_requests E u r"
    have use: "v = u" and endpoint: "a \<in> rel_ran M" using member by (auto simp: native_root_requests_def ends)
    obtain s where socket: "(s,a) \<in> M" using endpoint by (auto simp: rel_ran_def)
    obtain d where loc: "located_at E u a (fst d) (snd d)" using parts(3) socket by blast
    obtain S where target: "artifact_at E (fst d) S" using located_at_has_artifact[OF loc] by blast
    have anchor: "anchored_at E u a (Occurrence_Anchor (S,snd d))" by (rule located_at_target[OF ef loc target])
    show "\<exists>t. anchored_at E v a t" using anchor use by blast
  qed
  show ?thesis using ef finite reads by (simp add: citation_requests_formed_def)
qed

theorem native_package_read_boundary:
  assumes package: "native_package_at E u r P"
  shows "read_boundary_formed E (native_package_sources E u r) (native_package_demands E u r)"
proof -
  have formed: "native_package_formed E (native_package_roots E u r)" by (rule native_package_projection(1)[OF package])
  have ef: "environment_formed E" using formed by (simp add: native_package_formed_def)
  obtain Q where family: "native_root_family_at E u r Q" using package by (auto simp: native_package_at_def)
  obtain R where art: "artifact_at E u R" using family by (auto simp: native_root_family_at_def)
  have root_use: "u \<in> environment_uses E" using art by (auto simp: environment_uses_def artifact_at_def rel_dom_def)
  have sites: "native_package_sites E u r \<subseteq> environment_positions E"
    using native_package_sites(1)[OF formed] by (simp add: native_package_sites_def)
  have site_uses: "\<And>v a. (v,a) \<in> native_package_sites E u r \<Longrightarrow> v \<in> environment_uses E"
  proof -
    fix v a assume member: "(v,a) \<in> native_package_sites E u r"
    have pos: "(v,a) \<in> environment_positions E" using sites member by blast
    obtain S where art: "artifact_at E v S" using pos by auto
    show "v \<in> environment_uses E" using art by (auto simp: environment_uses_def rel_dom_def artifact_at_def)
  qed
  have sources: "native_package_sources E u r \<subseteq> environment_uses E"
    using site_uses root_use by (auto simp: native_package_sources_def)
  have qformed: "citation_requests_formed E (native_root_requests E u r)" by (rule native_root_requests_formed[OF family])
  have demands: "native_package_demands E u r \<subseteq> rel_dom (environment_bindings E)"
    using requested_slots_subset[OF qformed]
    by (auto simp: native_package_demands_def dest: native_definition_slots_bound)
  have owners: "fst ` native_package_demands E u r \<subseteq> native_package_sources E u r"
  proof
    fix v assume "v \<in> fst ` native_package_demands E u r"
    then obtain k where member: "(v,k) \<in> native_package_demands E u r" by auto
    show "v \<in> native_package_sources E u r"
    proof (cases "(v,k) \<in> requested_slots E (native_root_requests E u r)")
      case True
      have "v \<in> fst ` native_root_requests E u r" by (rule requested_slot_source[OF True])
      then have "v = u" by (auto simp: native_root_requests_def split: if_splits)
      then show ?thesis by (simp add: native_package_sources_def)
    next
      case False
      obtain a where "(v,a) \<in> native_package_sites E u r" using member False by (auto simp: native_package_demands_def)
      then show ?thesis by (auto simp: native_package_sources_def intro: rev_image_eqI)
    qed
  qed
  show ?thesis using ef sources demands owners by (simp add: read_boundary_formed_def)
qed

lemma native_package_environment_formed:
  assumes "native_package_at E u r P"
  shows "environment_formed (native_package_environment E u r)"
  unfolding native_package_environment_def by (rule read_environment_formed[OF native_package_read_boundary[OF assms]])

lemma native_package_environment_included:
  "environment_included (native_package_environment E u r) E"
  unfolding native_package_environment_def by (rule read_environment_included)

lemma native_package_environment_sources:
  assumes "v \<in> native_package_sources E u r"
  shows "artifact_at (native_package_environment E u r) v R \<longleftrightarrow> artifact_at E v R"
  unfolding native_package_environment_def by (rule read_environment_source[OF assms])

lemma native_package_environment_definition:
  assumes package: "native_package_at E u r P" and site: "(v,a) \<in> native_package_sites E u r"
    and defn: "native_definition_at E v a p C"
  shows "native_definition_at (native_package_environment E u r) v a p C"
    and "native_definition_slots (native_package_environment E u r) v a = native_definition_slots E v a"
proof -
  have boundary: "read_boundary_formed E (native_package_sources E u r) (native_package_demands E u r)"
    by (rule native_package_read_boundary[OF package])
  have source: "v \<in> native_package_sources E u r" using site by (auto simp: native_package_sources_def intro: rev_image_eqI)
  have slots: "\<forall>k\<in>native_definition_slots E v a. (v,k) \<in> native_package_demands E u r"
    using site by (auto simp: native_package_demands_def)
  show "native_definition_at (native_package_environment E u r) v a p C"
    unfolding native_package_environment_def by (rule native_definition_read_environment(1)[OF defn boundary source slots])
  show "native_definition_slots (native_package_environment E u r) v a = native_definition_slots E v a"
    unfolding native_package_environment_def by (rule native_definition_read_environment(2)[OF defn boundary source slots])
qed

lemma native_package_environment_roots:
  assumes package: "native_package_at E u r P" and family: "native_root_family_at E u r Q"
  shows "native_root_family_at (native_package_environment E u r) u r Q"
proof -
  have boundary: "read_boundary_formed E (native_package_sources E u r) (native_package_demands E u r)"
    by (rule native_package_read_boundary[OF package])
  have source: "u \<in> native_package_sources E u r" by (simp add: native_package_sources_def)
  have slots: "requested_slots E ({u} \<times> family_endpoints E u r) \<subseteq> native_package_demands E u r"
    by (auto simp: native_package_demands_def native_root_requests_def)
  show ?thesis unfolding native_package_environment_def
    by (rule native_root_family_read_environment[OF family boundary source slots])
qed


section \<open>Dependency traversal is unchanged by the derived restriction\<close>

lemma native_definition_edges_included:
  assumes included: "environment_included E F" and formed: "environment_formed F"
  shows "native_definition_edges E \<subseteq> native_definition_edges F"
proof
  fix edge assume member: "edge \<in> native_definition_edges E"
  obtain d e p C c S where shape: "edge = (d,e)" and parts:
    "native_definition_at E (fst d) (snd d) p C" "(c,S) \<in> C" "e \<in> schema_dependencies S"
    using member by (auto simp: native_definition_edges_def)
  have copied: "native_definition_at F (fst d) (snd d) p C"
    by (rule native_definition_included[OF parts(1) included formed])
  show "edge \<in> native_definition_edges F" using shape copied parts(2,3)
    unfolding native_definition_edges_def by blast
qed

lemma native_package_environment_sites:
  assumes package: "native_package_at E u r P"
  shows "native_package_sites (native_package_environment E u r) u r = native_package_sites E u r"
proof -
  let ?F = "native_package_environment E u r"
  let ?B = "native_package_roots E u r"
  have ef: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  obtain Q where family: "native_root_family_at E u r Q" using package by (auto simp: native_package_at_def)
  have copied_family: "native_root_family_at ?F u r Q" by (rule native_package_environment_roots[OF package family])
  have roots: "native_package_roots ?F u r = ?B"
    by (simp only: native_package_roots_from_family[OF copied_family] native_package_roots_from_family[OF family])
  have subset: "native_definition_edges ?F \<subseteq> native_definition_edges E"
    by (rule native_definition_edges_included[OF native_package_environment_included ef])
  have upper: "native_package_sites ?F u r \<subseteq> native_package_sites E u r"
    using rtrancl_mono[OF subset] by (auto simp: native_package_sites_def native_definition_sites_def roots)
  have lower: "native_package_sites E u r \<subseteq> native_package_sites ?F u r"
  proof
    fix d assume member: "d \<in> native_package_sites E u r"
    obtain a where root: "a \<in> ?B" and path: "(a,d) \<in> (native_definition_edges E)\<^sup>*"
      using member by (auto simp: native_package_sites_def native_definition_sites_def)
    have copied_path: "(a,d) \<in> (native_definition_edges ?F)\<^sup>*"
      using path
    proof (induction rule: rtrancl_induct)
      case base
      show ?case by simp
    next
      case (step y z)
      have site: "y \<in> native_package_sites E u r"
        using root step.hyps(1) by (auto simp: native_package_sites_def native_definition_sites_def)
      obtain p C c S where read: "native_definition_at E (fst y) (snd y) p C"
        and clause: "(c,S) \<in> C" and dependency: "z \<in> schema_dependencies S"
        using step.hyps(2) by (auto simp: native_definition_edges_def)
      have position: "(fst y,snd y) \<in> native_package_sites E u r" using site by simp
      have copied: "native_definition_at ?F (fst y) (snd y) p C"
        by (rule native_package_environment_definition(1)[OF package position read])
      have edge: "(y,z) \<in> native_definition_edges ?F"
        using copied clause dependency unfolding native_definition_edges_def by blast
      show ?case by (rule rtrancl_into_rtrancl[OF step.IH edge])
    qed
    show "d \<in> native_package_sites ?F u r"
      using root copied_path by (auto simp: native_package_sites_def native_definition_sites_def roots)
  qed
  show ?thesis using upper lower by blast
qed

theorem native_package_environment_recovers:
  assumes package: "native_package_at E u r P"
  shows "native_package_at (native_package_environment E u r) u r P"
proof -
  let ?F = "native_package_environment E u r"
  obtain Q where family: "native_root_family_at E u r Q"
    and formed: "native_package_formed E (rel_ran Q)" and prog: "P = native_program E (rel_ran Q)"
    using package by (auto simp: native_package_at_def)
  have ff: "environment_formed ?F" by (rule native_package_environment_formed[OF package])
  have ef: "environment_formed E" using formed by (simp add: native_package_formed_def)
  have copied_family: "native_root_family_at ?F u r Q" by (rule native_package_environment_roots[OF package family])
  have old_roots: "native_package_roots E u r = rel_ran Q" by (rule native_package_roots_from_family[OF family])
  have new_roots: "native_package_roots ?F u r = rel_ran Q" by (rule native_package_roots_from_family[OF copied_family])
  have sites: "native_definition_sites ?F (rel_ran Q) = native_definition_sites E (rel_ran Q)"
    using native_package_environment_sites[OF package] by (simp add: native_package_sites_def old_roots new_roots)
  have read: "\<And>d p C. d \<in> native_definition_sites E (rel_ran Q) \<Longrightarrow>
    native_definition_at E (fst d) (snd d) p C \<Longrightarrow> native_definition_at ?F (fst d) (snd d) p C"
  proof -
    fix d p C assume site: "d \<in> native_definition_sites E (rel_ran Q)"
      and defn: "native_definition_at E (fst d) (snd d) p C"
    have position: "(fst d,snd d) \<in> native_package_sites E u r"
      using site by (simp add: native_package_sites_def old_roots)
    show "native_definition_at ?F (fst d) (snd d) p C"
      by (rule native_package_environment_definition(1)[OF package position defn])
  qed
  have complete: "native_package_formed ?F (rel_ran Q)"
    using formed ff read sites unfolding native_package_formed_def by blast
  have graph: "native_definition_graph ?F (rel_ran Q) = native_definition_graph E (rel_ran Q)"
  proof
    show "native_definition_graph ?F (rel_ran Q) \<subseteq> native_definition_graph E (rel_ran Q)"
      using sites native_definition_included[OF _ native_package_environment_included ef]
      by (auto simp: native_definition_graph_def)
    show "native_definition_graph E (rel_ran Q) \<subseteq> native_definition_graph ?F (rel_ran Q)"
      using read sites by (auto simp: native_definition_graph_def)
  qed
  have same_program: "native_program ?F (rel_ran Q) = P" using graph prog by (simp add: native_program_def)
  show ?thesis using copied_family complete same_program unfolding native_package_at_def by blast
qed


lemma native_package_environment_requests:
  assumes package: "native_package_at E u r P"
  shows "native_root_requests (native_package_environment E u r) u r = native_root_requests E u r"
    and "requested_slots (native_package_environment E u r)
      (native_root_requests (native_package_environment E u r) u r) =
      requested_slots E (native_root_requests E u r)"
proof -
  let ?F = "native_package_environment E u r"
  have boundary: "read_boundary_formed E (native_package_sources E u r) (native_package_demands E u r)"
    by (rule native_package_read_boundary[OF package])
  have ef: "environment_formed E" using boundary by (simp add: read_boundary_formed_def)
  have ff: "environment_formed ?F" by (rule native_package_environment_formed[OF package])
  obtain Q where family: "native_root_family_at E u r Q" using package by (auto simp: native_package_at_def)
  obtain R M where art: "artifact_at E u R" and shape: "family_at R r M"
    using family by (auto simp: native_root_family_at_def)
  have root: "u \<in> native_package_sources E u r" by (simp add: native_package_sources_def)
  have same_artifacts: "\<And>R. artifact_at ?F u R \<longleftrightarrow> artifact_at E u R"
    by (rule native_package_environment_sources[OF root])
  have copied: "artifact_at ?F u R" using art same_artifacts[of R] by simp
  have ends: "family_endpoints ?F u r = family_endpoints E u r"
    by (simp only: family_endpoints_from_read[OF ff copied shape] family_endpoints_from_read[OF ef art shape])
  show requests: "native_root_requests ?F u r = native_root_requests E u r"
    by (simp only: native_root_requests_def ends)
  show "requested_slots ?F (native_root_requests ?F u r) = requested_slots E (native_root_requests E u r)"
    apply (simp only: requests)
    by (auto simp: requested_slots_def native_root_requests_def same_artifacts; blast)
qed

theorem native_package_demands_stable:
  assumes package: "native_package_at E u r P"
  shows "native_package_demands (native_package_environment E u r) u r = native_package_demands E u r"
proof -
  let ?F = "native_package_environment E u r"
  have sites: "native_package_sites ?F u r = native_package_sites E u r" by (rule native_package_environment_sites[OF package])
  have roots: "requested_slots ?F (native_root_requests ?F u r) = requested_slots E (native_root_requests E u r)"
    by (rule native_package_environment_requests(2)[OF package])
  have each: "\<And>v a. (v,a) \<in> native_package_sites E u r \<Longrightarrow>
    native_definition_slots ?F v a = native_definition_slots E v a"
  proof -
    fix v a assume site: "(v,a) \<in> native_package_sites E u r"
    have formed: "native_package_formed E (native_package_roots E u r)" by (rule native_package_projection(1)[OF package])
    obtain p C where defn: "native_definition_at E v a p C"
      using formed site by (auto simp: native_package_formed_def native_package_sites_def)
    show "native_definition_slots ?F v a = native_definition_slots E v a"
      by (rule native_package_environment_definition(2)[OF package site defn])
  qed
  show ?thesis by (auto simp: native_package_demands_def sites roots each)
qed

lemma native_package_sources_stable:
  assumes "native_package_at E u r P"
  shows "native_package_sources (native_package_environment E u r) u r = native_package_sources E u r"
  by (simp only: native_package_sources_def native_package_environment_sites[OF assms])

theorem native_package_environment_idempotent:
  assumes "native_package_at E u r P"
  shows "native_package_environment (native_package_environment E u r) u r = native_package_environment E u r"
proof -
  have sources: "native_package_sources (native_package_environment E u r) u r = native_package_sources E u r"
    by (rule native_package_sources_stable[OF assms])
  have demands: "native_package_demands (native_package_environment E u r) u r = native_package_demands E u r"
    by (rule native_package_demands_stable[OF assms])
  show ?thesis
    unfolding native_package_environment_def[of "native_package_environment E u r" u r]
    apply (simp only: sources demands)
    by (simp only: native_package_environment_def read_environment_idempotent)
qed


section \<open>All retained uses are reachable from the selected root\<close>

lemma prospective_call_use_edge:
  assumes call: "prospective_call_at E u V r d p I K"
  shows "u = fst d \<or> (u,fst d) \<in> environment_edges E"
proof -
  obtain cite where loc: "citation_location E u cite (fst d) (snd d)"
    using call by (auto simp: prospective_call_at_def)
  show ?thesis using loc by (cases cite) (auto simp: environment_edges_def)
qed

lemma native_definition_edge_uses:
  assumes edge: "(d,e) \<in> native_definition_edges E"
  shows "fst d = fst e \<or> (fst d,fst e) \<in> environment_edges E"
proof -
  obtain p C c S where defn: "native_definition_at E (fst d) (snd d) p C"
    and clause: "(c,S) \<in> C" and dependency: "e \<in> schema_dependencies S"
    using edge by (auto simp: native_definition_edges_def)
  obtain a where schema: "native_schema_at E (fst d) a S" using native_definition_clause_origin[OF defn clause] by blast
  obtain V m where family: "native_premise_family_at E (fst d) V m (schema_premises S) (schema_material_premises S)"
    using schema by (auto simp: native_schema_at_def)
  obtain s q where member: "(s,e,q) \<in> schema_premises S"
    using dependency by (auto simp: schema_dependencies_def rel_ran_def)
  obtain x I K where call: "prospective_call_at E (fst d) V x e q I K"
    using native_premise_family_call_origin[OF family member] by blast
  show ?thesis by (rule prospective_call_use_edge[OF call])
qed

lemma native_definition_path_uses:
  assumes path: "(d,e) \<in> (native_definition_edges E)\<^sup>*"
  shows "(fst d,fst e) \<in> (environment_edges E)\<^sup>*"
  using path
proof (induction rule: rtrancl_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have one: "(fst y,fst z) \<in> (environment_edges E)\<^sup>*"
    using native_definition_edge_uses[OF step.hyps(2)] by auto
  show ?case by (rule rtrancl_trans[OF step.IH one])
qed

lemma native_package_site_use_reachable:
  assumes site: "d \<in> native_package_sites E u r"
  shows "fst d \<in> environment_reachable E {u}"
proof -
  obtain a where root: "a \<in> native_package_roots E u r"
    and path: "(a,d) \<in> (native_definition_edges E)\<^sup>*"
    using site by (auto simp: native_package_sites_def native_definition_sites_def)
  obtain Q s where family: "native_root_family_at E u r Q" and member: "(s,a) \<in> Q"
    using root by (auto simp: native_package_roots_def rel_ran_def)
  obtain x where loc: "located_at E u x (fst a) (snd a)"
    using native_root_family_origin[OF family member] by blast
  have first: "(u,fst a) \<in> (environment_edges E)\<^sup>*" using located_at_use_edge[OF loc] by auto
  have rest: "(fst a,fst d) \<in> (environment_edges E)\<^sup>*" by (rule native_definition_path_uses[OF path])
  have whole: "(u,fst d) \<in> (environment_edges E)\<^sup>*" by (rule rtrancl_trans[OF first rest])
  show ?thesis using whole by (simp add: environment_reachable_def)
qed

lemma native_package_sources_reachable:
  "native_package_sources E u r \<subseteq> environment_reachable E {u}"
  using native_package_site_use_reachable[of _ E u r]
  by (auto simp: native_package_sources_def environment_reachable_def)

theorem native_package_environment_closed:
  assumes package: "native_package_at E u r P"
  shows "environment_closed (native_package_environment E u r) {u}
    (native_package_demands (native_package_environment E u r) u r)"
proof -
  let ?F = "native_package_environment E u r"
  let ?U = "native_package_sources E u r"
  let ?D = "native_package_demands E u r"
  have boundary: "read_boundary_formed E ?U ?D" by (rule native_package_read_boundary[OF package])
  have roots: "{u} \<subseteq> ?U" by (simp add: native_package_sources_def)
  have reachable: "?U \<subseteq> environment_reachable ?F {u}"
    using native_package_sources_reachable[of ?F u r] native_package_sources_stable[OF package] by simp
  have closed: "environment_closed ?F {u} ?D"
    unfolding native_package_environment_def
    by (rule read_environment_closed_from[OF boundary roots]) (use reachable in \<open>simp only: native_package_environment_def\<close>)
  show ?thesis using closed native_package_demands_stable[OF package] by simp
qed

definition closed_native_package_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u native_system \<Rightarrow> bool" where
  "closed_native_package_at E u r P \<longleftrightarrow> native_package_at E u r P \<and>
    environment_closed E {u} (native_package_demands E u r)"

theorem native_package_closed_restriction:
  assumes "native_package_at E u r P"
  shows "closed_native_package_at (native_package_environment E u r) u r P"
  using native_package_environment_recovers[OF assms] native_package_environment_closed[OF assms]
  by (simp add: closed_native_package_at_def)

text \<open>
  The root citation family, complete definition traversal, and pattern/call
  readers determine a finite environment restriction. It preserves the entire
  recovered program and derives the same sources and demands when read again.
  Every retained use is reachable from the package root. Literal artifacts
  remain exact data values; their bindings are retained only if the grammar
  separately reads syntax at that use.
\<close>

end
