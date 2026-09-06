theory Factor_Package_Locality
  imports Factor_Package_Dependencies
begin

section \<open>A formed extension cannot change a recovered package\<close>

theorem native_dependency_package_included:
  assumes formed: "native_package_formed E B"
    and included: "environment_included E F" and ff: "environment_formed F"
  shows "native_package_formed F B \<and> native_program F B = native_program E B"
proof -
  let ?S = "native_definition_sites E B"
  have ef: "environment_formed E" using formed by (simp add: native_package_formed_def)
  have complete: "\<And>d. d \<in> ?S \<Longrightarrow> \<exists>p C. native_definition_at E (fst d) (snd d) p C"
    using formed by (simp add: native_package_formed_def)
  have closed: "\<And>d e. d \<in> ?S \<Longrightarrow> (d,e) \<in> native_definition_edges F \<Longrightarrow> e \<in> ?S"
  proof -
    fix d e assume site: "d \<in> ?S" and edge: "(d,e) \<in> native_definition_edges F"
    obtain p C where defn: "native_definition_at E (fst d) (snd d) p C" using complete[OF site] by blast
    have copied: "native_definition_at F (fst d) (snd d) p C" by (rule native_definition_included[OF defn included ff])
    obtain q D c S where other: "native_definition_at F (fst d) (snd d) q D"
      and clause: "(c,S) \<in> D" and dependency: "e \<in> schema_dependencies S"
      using edge by (auto simp: native_definition_edges_def)
    have same: "q = p \<and> D = C" by (rule native_definition_unique[OF other copied])
    have source_clause: "(c,S) \<in> C" using clause same by simp
    have old_edge: "(d,e) \<in> native_definition_edges E"
      using defn source_clause dependency unfolding native_definition_edges_def by blast
    show "e \<in> ?S" by (rule native_definition_step[OF site old_edge])
  qed
  have roots: "B \<subseteq> ?S" by (rule native_definition_roots)
  have upper: "native_definition_sites F B \<subseteq> ?S" by (rule native_definition_sites_least[OF roots closed])
  have edges: "native_definition_edges E \<subseteq> native_definition_edges F"
    by (rule native_definition_edges_included[OF included ff])
  have lower: "?S \<subseteq> native_definition_sites F B"
    using rtrancl_mono[OF edges] by (auto simp: native_definition_sites_def)
  have sites: "native_definition_sites F B = ?S" using upper lower by blast
  have copied_complete: "native_package_formed F B"
  proof (unfold native_package_formed_def, rule conjI[OF ff], intro ballI)
    fix d assume site: "d \<in> native_definition_sites F B"
    have old: "d \<in> ?S" using site sites by simp
    obtain p C where defn: "native_definition_at E (fst d) (snd d) p C" using complete[OF old] by blast
    have copied: "native_definition_at F (fst d) (snd d) p C" by (rule native_definition_included[OF defn included ff])
    show "\<exists>p C. native_definition_at F (fst d) (snd d) p C" using copied by blast
  qed
  have graph: "native_definition_graph F B = native_definition_graph E B"
  proof
    show "native_definition_graph F B \<subseteq> native_definition_graph E B"
    proof
      fix entry assume member: "entry \<in> native_definition_graph F B"
      obtain d p C where shape: "entry = (d,p,C)" by (cases entry) auto
      have site: "d \<in> ?S" and read: "native_definition_at F (fst d) (snd d) p C"
        using member sites by (auto simp: native_definition_graph_def shape)
      obtain q D where old: "native_definition_at E (fst d) (snd d) q D" using complete[OF site] by blast
      have copied: "native_definition_at F (fst d) (snd d) q D" by (rule native_definition_included[OF old included ff])
      have same: "p = q \<and> C = D" by (rule native_definition_unique[OF read copied])
      show "entry \<in> native_definition_graph E B" using shape site old same by (simp add: native_definition_graph_def)
    qed
    show "native_definition_graph E B \<subseteq> native_definition_graph F B"
      using sites native_definition_included[OF _ included ff] by (auto simp: native_definition_graph_def)
  qed
  have copied_program: "native_program F B = native_program E B" using graph by (simp add: native_program_def)
  show ?thesis using copied_complete copied_program by blast
qed

theorem native_package_included:
  assumes package: "native_package_at E u r P"
    and included: "environment_included E F" and ff: "environment_formed F"
  shows "native_package_at F u r P"
proof -
  obtain Q where family: "native_root_family_at E u r Q"
    and formed: "native_package_formed E (rel_ran Q)" and prog: "P = native_program E (rel_ran Q)"
    using package by (auto simp: native_package_at_def)
  have copied_family: "native_root_family_at F u r Q" by (rule native_root_family_included[OF family included ff])
  have copied_program: "native_package_formed F (rel_ran Q) \<and> native_program F (rel_ran Q) = native_program E (rel_ran Q)"
    by (rule native_dependency_package_included[OF formed included ff])
  show ?thesis unfolding native_package_at_def
    by (rule exI[of _ Q]) (use copied_family copied_program prog in auto)
qed

theorem native_package_dependency_locality:
  assumes package: "native_package_at E u r P"
    and ff: "environment_formed F"
    and included: "environment_included (native_package_environment E u r) F"
  shows "native_package_at F u r P"
proof -
  have retained: "native_package_at (native_package_environment E u r) u r P"
    by (rule native_package_environment_recovers[OF package])
  show ?thesis by (rule native_package_included[OF retained included ff])
qed

theorem native_package_dependency_equivalence:
  assumes package: "native_package_at E u r P" and ff: "environment_formed F"
    and included: "environment_included (native_package_environment E u r) F"
  shows "native_package_at E u r T \<longleftrightarrow> native_package_at F u r T"
proof -
  have copied: "native_package_at F u r P" by (rule native_package_dependency_locality[OF package ff included])
  show ?thesis
  proof
    assume source: "native_package_at E u r T"
    have same: "T = P" by (rule native_package_unique[OF source package])
    show "native_package_at F u r T" using copied same by simp
  next
    assume target: "native_package_at F u r T"
    have same: "T = P" by (rule native_package_unique[OF target copied])
    show "native_package_at E u r T" using package same by simp
  qed
qed


section \<open>Every retained slot is required by a valid reading\<close>

lemma native_premise_family_slots_included:
  assumes family: "native_premise_family_at E u V r Q C" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_premise_family_slots F u V r = native_premise_family_slots E u V r"
proof -
  have ef: "environment_formed E" using family by (simp add: native_premise_family_at_def)
  obtain R M where parts: "artifact_at E u R" "family_at R r M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow>
      (\<exists>p I K. (s,p) \<in> socket_sum Q C \<and> native_premise_at E u V a p I K)"
    using family by (auto simp: native_premise_family_at_def)
  have art: "artifact_at F u R" by (rule included_artifact[OF included parts(1)])
  have old_ends: "family_endpoints E u r = rel_ran M" by (rule family_endpoints_from_read[OF ef parts(1,2)])
  have new_ends: "family_endpoints F u r = rel_ran M" by (rule family_endpoints_from_read[OF ff art parts(2)])
  have each: "\<And>a. a \<in> rel_ran M \<Longrightarrow> native_premise_slots F u V a = native_premise_slots E u V a"
  proof -
    fix a assume member: "a \<in> rel_ran M"
    obtain s where socket: "(s,a) \<in> M" using member by (auto simp: rel_ran_def)
    obtain p I K where read: "native_premise_at E u V a p I K" using parts(3) socket by blast
    have copied: "native_premise_at F u V a p I K" by (rule native_premise_included[OF read included ff])
    show "native_premise_slots F u V a = native_premise_slots E u V a"
      by (simp only: native_premise_slots_of_read[OF copied] native_premise_slots_of_read[OF read])
  qed
  show ?thesis by (simp add: native_premise_family_slots_def old_ends new_ends each)
qed

lemma prospective_family_slots_included:
  assumes family: "prospective_family_at E u V r Q" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "prospective_family_slots F u V r = prospective_family_slots E u V r"
proof -
  have ef: "environment_formed E" using family by (simp add: prospective_family_at_def)
  obtain R M where parts: "artifact_at E u R" "family_at R r M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>d p I K. (s,d,p) \<in> Q \<and> prospective_call_at E u V a d p I K)"
    using family by (auto simp: prospective_family_at_def)
  have art: "artifact_at F u R" by (rule included_artifact[OF included parts(1)])
  have old_ends: "family_endpoints E u r = rel_ran M" by (rule family_endpoints_from_read[OF ef parts(1,2)])
  have new_ends: "family_endpoints F u r = rel_ran M" by (rule family_endpoints_from_read[OF ff art parts(2)])
  have each: "\<And>a. a \<in> rel_ran M \<Longrightarrow> prospective_call_slots F u V a = prospective_call_slots E u V a"
  proof -
    fix a assume member: "a \<in> rel_ran M"
    obtain s where socket: "(s,a) \<in> M" using member by (auto simp: rel_ran_def)
    obtain d p I K where call: "prospective_call_at E u V a d p I K" using parts(3) socket by blast
    have copied: "prospective_call_at F u V a d p I K" by (rule prospective_call_included[OF call included ff])
    show "prospective_call_slots F u V a = prospective_call_slots E u V a"
      by (simp only: prospective_call_slots_of_read[OF copied] prospective_call_slots_of_read[OF call])
  qed
  show ?thesis by (simp add: prospective_family_slots_def old_ends new_ends each)
qed

lemma native_schema_slots_included:
  assumes schema: "native_schema_at E u r S" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_schema_slots F u r = native_schema_slots E u r"
proof -
  have ef: "environment_formed E" using schema by (simp add: native_schema_at_def)
  obtain R ps b c m V I K where parts:
    "artifact_at E u R" "record_at R r ps [b,c,m]" "binder_scope_at R b V"
    "pattern_quoted_at E u V c (schema_conclusion S) I K"
    "native_premise_family_at E u V m (schema_premises S) (schema_material_premises S)"
    using schema by (auto simp: native_schema_at_def)
  have art: "artifact_at F u R" by (rule included_artifact[OF included parts(1)])
  have head: "pattern_quoted_at F u V c (schema_conclusion S) I K" by (rule pattern_quoted_included[OF parts(4) included ff])
  have head_slots: "pattern_slots F u V c = pattern_slots E u V c"
    by (simp only: pattern_slots_of_quote[OF head] pattern_slots_of_quote[OF parts(4)])
  have body_slots: "native_premise_family_slots F u V m = native_premise_family_slots E u V m"
    by (rule native_premise_family_slots_included[OF parts(5) included ff])
  show ?thesis by (simp only: native_schema_slots_from_fields[OF ef parts(1-3)]
      native_schema_slots_from_fields[OF ff art parts(2,3)] head_slots body_slots)
qed

lemma native_schema_family_slots_included:
  assumes family: "native_schema_family_at E u r C" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_schema_family_slots F u r = native_schema_family_slots E u r"
proof -
  have ef: "environment_formed E" using family by (simp add: native_schema_family_at_def)
  obtain R M where parts: "artifact_at E u R" "family_at R r M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>S. (s,S) \<in> C \<and> native_schema_at E u a S)"
    using family by (auto simp: native_schema_family_at_def)
  have art: "artifact_at F u R" by (rule included_artifact[OF included parts(1)])
  have old_ends: "family_endpoints E u r = rel_ran M" by (rule family_endpoints_from_read[OF ef parts(1,2)])
  have new_ends: "family_endpoints F u r = rel_ran M" by (rule family_endpoints_from_read[OF ff art parts(2)])
  have each: "\<And>a. a \<in> rel_ran M \<Longrightarrow> native_schema_slots F u a = native_schema_slots E u a"
  proof -
    fix a assume member: "a \<in> rel_ran M"
    obtain s where socket: "(s,a) \<in> M" using member by (auto simp: rel_ran_def)
    obtain S where schema: "native_schema_at E u a S" using parts(3) socket by blast
    show "native_schema_slots F u a = native_schema_slots E u a" by (rule native_schema_slots_included[OF schema included ff])
  qed
  show ?thesis by (simp add: native_schema_family_slots_def old_ends new_ends each)
qed

lemma native_definition_slots_included:
  assumes defn: "native_definition_at E u r p C" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_definition_slots F u r = native_definition_slots E u r"
proof -
  have ef: "environment_formed E" using defn by (simp add: native_definition_at_def)
  obtain R ps i m I K where parts: "artifact_at E u R" "record_at R r ps [i,m]"
    "scoped_pattern_at E u i p I K" "native_schema_family_at E u m C"
    using defn by (auto simp: native_definition_at_def)
  have art: "artifact_at F u R" by (rule included_artifact[OF included parts(1)])
  have interface: "scoped_pattern_at F u i p I K" by (rule scoped_pattern_included[OF parts(3) included ff])
  have interface_slots: "scoped_pattern_slots F u i = scoped_pattern_slots E u i"
    by (simp only: scoped_pattern_slots_of_quote[OF interface] scoped_pattern_slots_of_quote[OF parts(3)])
  have body_slots: "native_schema_family_slots F u m = native_schema_family_slots E u m"
    by (rule native_schema_family_slots_included[OF parts(4) included ff])
  show ?thesis by (simp only: native_definition_slots_from_fields[OF ef parts(1,2)]
      native_definition_slots_from_fields[OF ff art parts(2)] interface_slots body_slots)
qed

theorem native_package_boundary_included:
  assumes package: "native_package_at E u r P" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_package_sources F u r = native_package_sources E u r"
    and "native_package_demands F u r = native_package_demands E u r"
proof -
  have copied: "native_package_at F u r P" by (rule native_package_included[OF package included ff])
  have sites: "native_package_sites F u r = native_package_sites E u r"
    using native_package_projection(3)[OF package] native_package_projection(3)[OF copied] by simp
  show "native_package_sources F u r = native_package_sources E u r" by (simp only: native_package_sources_def sites)
  obtain Q where family: "native_root_family_at E u r Q" using package by (auto simp: native_package_at_def)
  have ef: "environment_formed E" using family by (simp add: native_root_family_at_def)
  obtain R M where art: "artifact_at E u R" and raw: "family_at R r M"
    using family by (auto simp: native_root_family_at_def)
  have f_art: "artifact_at F u R" by (rule included_artifact[OF included art])
  have ends: "family_endpoints F u r = family_endpoints E u r"
    by (simp only: family_endpoints_from_read[OF ef art raw] family_endpoints_from_read[OF ff f_art raw])
  have artifacts: "\<And>S. artifact_at F u S \<longleftrightarrow> artifact_at E u S"
  proof -
    fix S
    have left: "artifact_at F u S \<Longrightarrow> S = R" by (rule environment_artifact_unique[OF ff _ f_art])
    have right: "artifact_at E u S \<Longrightarrow> artifact_at F u S" by (rule included_artifact[OF included])
    show "artifact_at F u S \<longleftrightarrow> artifact_at E u S" using left right art by blast
  qed
  have roots: "requested_slots F (native_root_requests F u r) = requested_slots E (native_root_requests E u r)"
    by (auto simp: requested_slots_def native_root_requests_def ends artifacts; blast)
  have each: "\<And>v a. (v,a) \<in> native_package_sites E u r \<Longrightarrow>
    native_definition_slots F v a = native_definition_slots E v a"
  proof -
    fix v a assume site: "(v,a) \<in> native_package_sites E u r"
    have formed: "native_package_formed E (native_package_roots E u r)" by (rule native_package_projection(1)[OF package])
    obtain p C where defn: "native_definition_at E v a p C"
      using formed site by (auto simp: native_package_formed_def native_package_sites_def)
    show "native_definition_slots F v a = native_definition_slots E v a"
      by (rule native_definition_slots_included[OF defn included ff])
  qed
  show "native_package_demands F u r = native_package_demands E u r"
    by (auto simp: native_package_demands_def sites roots each)
qed

theorem native_package_dependency_material_required:
  assumes package: "native_package_at E u r P" and smaller: "native_package_at F u r T"
    and included: "environment_included F E"
  shows "environment_included (native_package_environment E u r) F"
proof -
  have ef: "environment_formed E" and ff: "environment_formed F"
    using native_package_projection(1)[OF package] native_package_projection(1)[OF smaller]
    by (auto simp: native_package_formed_def)
  have sources: "native_package_sources E u r = native_package_sources F u r"
    and demands: "native_package_demands E u r = native_package_demands F u r"
    by (rule native_package_boundary_included[OF smaller included ef])+
  have boundary: "read_boundary_formed F (native_package_sources F u r) (native_package_demands F u r)"
    by (rule native_package_read_boundary[OF smaller])
  have uses: "native_package_sources E u r \<subseteq> environment_uses F"
    and slots: "native_package_demands E u r \<subseteq> rel_dom (environment_bindings F)"
    using boundary sources demands by (auto simp: read_boundary_formed_def)
  show ?thesis unfolding native_package_environment_def
    by (rule read_environment_least[OF ef ff included uses slots])
qed

theorem native_package_environment_extension:
  assumes package: "native_package_at E u r P" and included: "environment_included E F"
    and ff: "environment_formed F"
  shows "native_package_environment F u r = native_package_environment E u r"
proof -
  let ?A = "native_package_environment E u r"
  let ?B = "native_package_environment F u r"
  have future: "native_package_at F u r P" by (rule native_package_included[OF package included ff])
  have old_closed: "native_package_at ?A u r P" by (rule native_package_environment_recovers[OF package])
  have new_closed: "native_package_at ?B u r P" by (rule native_package_environment_recovers[OF future])
  have old_in_future: "environment_included ?A F"
    by (rule environment_included_trans[OF native_package_environment_included included])
  have upper: "environment_included ?B ?A"
    by (rule native_package_dependency_material_required[OF future old_closed old_in_future])
  have new_in_old: "environment_included ?B E"
    by (rule environment_included_trans[OF upper native_package_environment_included])
  have lower: "environment_included ?A ?B"
    by (rule native_package_dependency_material_required[OF package new_closed new_in_old])
  show ?thesis by (rule environment_included_antisym[OF upper lower])
qed

text \<open>
  Only the grammar-derived closed package must be retained. The containing
  environment can add fresh argument artifacts and their bindings, provided
  it remains formed. Every interface, clause, and callee in the recovered
  program stays fixed. This is compatible extension of one explicit package,
  not an ambient resolver or a bound on future arguments.
\<close>

end
