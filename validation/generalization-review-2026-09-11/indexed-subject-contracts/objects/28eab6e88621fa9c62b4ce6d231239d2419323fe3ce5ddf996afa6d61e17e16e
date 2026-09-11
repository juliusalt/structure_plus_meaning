theory RRA_Publication_Dependencies
  imports RRA_Publication RRA_Generation_Dependencies RRA_Read_Environment
begin

section \<open>Complete publication fields at one source artifact\<close>

lemma selection_at_source:
  assumes selection: "selection_at E u r S" and art: "artifact_at E u R"
  shows "\<exists>M g. family_at R r M \<and> inj_on g (rel_dom M) \<and>
    (\<forall>s d. (s,d)\<in>M \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))) \<and>
    S=Abs_fset (image g (rel_dom M))"
proof -
  obtain T M g where facts: "environment_formed E" "artifact_at E u T" "family_at T r M"
    "inj_on g (rel_dom M)"
    "\<forall>s d. (s,d)\<in>M \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
    "S=Abs_fset (image g (rel_dom M))"
    using selection unfolding selection_at_def by blast
  have same: "R=T" by (rule environment_artifact_unique[OF facts(1) art facts(2)])
  show ?thesis using facts(3-6) same by blast
qed

lemma target_selection_at_source:
  assumes selection: "target_selection_at E u r T" and art: "artifact_at E u R"
  shows "\<exists>M g. family_at R r M \<and>
    (\<forall>s d. (s,d)\<in>M \<longrightarrow> anchored_at E u d (g s)) \<and>
    inj_on snd (graph_map (rel_dom M) g) \<and> T=rel_ran (graph_map (rel_dom M) g)"
proof -
  obtain A M g where facts: "environment_formed E" "artifact_at E u A" "family_at A r M"
    "\<forall>s d. (s,d)\<in>M \<longrightarrow> anchored_at E u d (g s)"
    "inj_on snd (graph_map (rel_dom M) g)" "T=rel_ran (graph_map (rel_dom M) g)"
    using selection unfolding target_selection_at_def anchor_family_at_def by blast
  have same: "R=A" by (rule environment_artifact_unique[OF facts(1) art facts(2)])
  show ?thesis using facts(3-6) same by blast
qed

lemma selection_family_reference:
  assumes selection: "selection_at E u r S" and art: "artifact_at E u R"
    and family: "family_at R r M" and member: "d\<in>rel_ran M"
  shows "\<exists>v a G. located_at E u d v a \<and> generation_at E v a G"
proof -
  obtain N g where other: "family_at R r N"
    "\<forall>s d. (s,d)\<in>N \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
    using selection_at_source[OF selection art] by blast
  have same: "M=N" by (rule family_at_unique[OF family other(1)])
  show ?thesis using member other(2) same by (auto simp: rel_ran_def; blast)
qed

lemma target_selection_family_reference:
  assumes selection: "target_selection_at E u r T" and art: "artifact_at E u R"
    and family: "family_at R r M" and member: "d\<in>rel_ran M"
  shows "\<exists>t. anchored_at E u d t"
proof -
  obtain N g where other: "family_at R r N"
    "\<forall>s d. (s,d)\<in>N \<longrightarrow> anchored_at E u d (g s)"
    using target_selection_at_source[OF selection art] by blast
  have same: "M=N" by (rule family_at_unique[OF family other(1)])
  show ?thesis using member other(2) same by (auto simp: rel_ran_def)
qed

definition publication_syntax_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow>
    (local_address\<times>local_address) set \<Rightarrow> (local_address\<times>local_address) set \<Rightarrow>
    (local_address\<times>local_address) set \<Rightarrow> bool" where
  "publication_syntax_at R root M N K \<longleftrightarrow>
    (\<exists>ps sr dr er. record_at R root ps [sr,dr,er] \<and>
      family_at R sr M \<and> family_at R dr N \<and> family_at R er K)"

lemma publication_syntax_unique:
  assumes first: "publication_syntax_at R root M N K"
    and second: "publication_syntax_at R root M' N' K'"
  shows "M=M' \<and> N=N' \<and> K=K'"
proof -
  obtain ps sr dr er where a: "record_at R root ps [sr,dr,er]"
    "family_at R sr M" "family_at R dr N" "family_at R er K"
    using first unfolding publication_syntax_at_def by blast
  obtain qs sr' dr' er' where b: "record_at R root qs [sr',dr',er']"
    "family_at R sr' M'" "family_at R dr' N'" "family_at R er' K'"
    using second unfolding publication_syntax_at_def by blast
  have endpoints: "sr=sr' \<and> dr=dr' \<and> er=er'"
    using record_at_unique[OF a(1) b(1)] by simp
  show ?thesis using a(2-4) b(2-4) endpoints by (meson family_at_unique)
qed

definition publication_citation_roots :: "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "publication_citation_roots R root=
    {d. \<exists>M N K. publication_syntax_at R root M N K \<and> d\<in>rel_ran M\<union>rel_ran N\<union>rel_ran K}"

definition publication_generation_roots :: "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "publication_generation_roots R root=
    {d. \<exists>M N K. publication_syntax_at R root M N K \<and> d\<in>rel_ran M}"

lemma publication_roots_from_syntax:
  assumes shape: "publication_syntax_at R root M N K"
  shows "publication_citation_roots R root=rel_ran M\<union>rel_ran N\<union>rel_ran K"
    and "publication_generation_roots R root=rel_ran M"
proof -
  have project: "\<And>P. (\<exists>A B C. publication_syntax_at R root A B C \<and> P A B C)\<longleftrightarrow>P M N K"
  proof -
    fix P
    show "(\<exists>A B C. publication_syntax_at R root A B C \<and> P A B C)\<longleftrightarrow>P M N K"
    proof
      assume "\<exists>A B C. publication_syntax_at R root A B C \<and> P A B C"
      then obtain A B C where other: "publication_syntax_at R root A B C" and holds: "P A B C" by blast
      have same: "M=A \<and> N=B \<and> K=C" by (rule publication_syntax_unique[OF shape other])
      show "P M N K" using holds same by simp
    next
      assume "P M N K"
      then show "\<exists>A B C. publication_syntax_at R root A B C \<and> P A B C" using shape by blast
    qed
  qed
  show "publication_citation_roots R root=rel_ran M\<union>rel_ran N\<union>rel_ran K"
    by (simp only: publication_citation_roots_def project) auto
  show "publication_generation_roots R root=rel_ran M"
    by (simp only: publication_generation_roots_def project) auto
qed

lemma publication_syntax_carrier:
  assumes shape: "publication_syntax_at R root M N K"
  shows "root\<in>rra_carrier (object_structure R)"
    and "publication_citation_roots R root\<subseteq>rra_carrier (object_structure R)"
proof -
  obtain ps sr dr er where rec: "record_at R root ps [sr,dr,er]"
    and families: "family_at R sr M" "family_at R dr N" "family_at R er K"
    using shape unfolding publication_syntax_at_def by blast
  show "root\<in>rra_carrier (object_structure R)" using rec by (simp add: record_at_def)
  have endpoints: "rel_ran M\<union>rel_ran N\<union>rel_ran K\<subseteq>rra_carrier (object_structure R)"
    using families by (auto simp: family_at_def rel_ran_def headed_incidence_def object_formed_def rra_formed_def)
  show "publication_citation_roots R root\<subseteq>rra_carrier (object_structure R)"
    using endpoints by (simp add: publication_roots_from_syntax[OF shape])
qed

lemma publication_at_families:
  assumes pub: "publication_at E u root P"
  shows "\<exists>R ps sr dr er M N K. artifact_at E u R \<and> record_at R root ps [sr,dr,er] \<and>
    family_at R sr M \<and> family_at R dr N \<and> family_at R er K \<and>
    snapshot_at E u sr (publication_snapshot P) \<and>
    target_selection_at E u dr (fset (publication_dependencies P)) \<and>
    target_selection_at E u er (fset (publication_evidence P))"
proof -
  obtain R ps sr dr er where fields: "artifact_at E u R" "record_at R root ps [sr,dr,er]"
    "snapshot_at E u sr (publication_snapshot P)"
    "target_selection_at E u dr (fset (publication_dependencies P))"
    "target_selection_at E u er (fset (publication_evidence P))"
    using pub unfolding publication_at_def by blast
  have selected: "selection_at E u sr (publication_snapshot P)" using fields(3) by (simp add: snapshot_at_def)
  obtain M where m: "family_at R sr M" using selection_at_source[OF selected fields(1)] by blast
  obtain N where n: "family_at R dr N" using target_selection_at_source[OF fields(4,1)] by blast
  obtain K where k: "family_at R er K" using target_selection_at_source[OF fields(5,1)] by blast
  show ?thesis using fields m n k by blast
qed

lemma publication_generation_reference:
  assumes pub: "publication_at E u root P" and art: "artifact_at E u R"
    and member: "d\<in>publication_generation_roots R root"
  shows "\<exists>v a G. located_at E u d v a \<and> generation_at E v a G"
proof -
  have ef: "environment_formed E" using pub by (simp add: publication_at_def)
  obtain T ps sr dr er M N K where fields: "artifact_at E u T" "record_at T root ps [sr,dr,er]"
    "family_at T sr M" "family_at T dr N" "family_at T er K"
    "snapshot_at E u sr (publication_snapshot P)"
    using publication_at_families[OF pub] by blast
  have shape: "publication_syntax_at T root M N K" using fields(2-5)
    unfolding publication_syntax_at_def by blast
  have same: "R=T" by (rule environment_artifact_unique[OF ef art fields(1)])
  have endpoint: "d\<in>rel_ran M" using member same publication_roots_from_syntax(2)[OF shape] by simp
  have selection: "selection_at E u sr (publication_snapshot P)" using fields(6) by (simp add: snapshot_at_def)
  show ?thesis by (rule selection_family_reference[OF selection fields(1,3) endpoint])
qed

lemma publication_citations_interpretable:
  assumes pub: "publication_at E u root P" and art: "artifact_at E u R"
    and member: "d\<in>publication_citation_roots R root"
  shows "\<exists>t. anchored_at E u d t"
proof -
  have ef: "environment_formed E" using pub by (simp add: publication_at_def)
  obtain T ps sr dr er M N K where fields: "artifact_at E u T" "record_at T root ps [sr,dr,er]"
    "family_at T sr M" "family_at T dr N" "family_at T er K"
    "snapshot_at E u sr (publication_snapshot P)"
    "target_selection_at E u dr (fset (publication_dependencies P))"
    "target_selection_at E u er (fset (publication_evidence P))"
    using publication_at_families[OF pub] by blast
  have shape: "publication_syntax_at T root M N K" using fields(2-5)
    unfolding publication_syntax_at_def by blast
  have same: "R=T" by (rule environment_artifact_unique[OF ef art fields(1)])
  have endpoint: "d\<in>rel_ran M\<union>rel_ran N\<union>rel_ran K"
    using member same publication_roots_from_syntax(1)[OF shape] by simp
  show ?thesis
  proof (cases "d\<in>rel_ran M")
    case True
    have root: "d\<in>publication_generation_roots R root"
      using True same publication_roots_from_syntax(2)[OF shape] by simp
    obtain v a G where loc: "located_at E u d v a"
      using publication_generation_reference[OF pub art root] by blast
    obtain A where target: "artifact_at E v A" using located_at_has_artifact[OF loc] by blast
    show ?thesis using located_at_target[OF ef loc target] by blast
  next
    case False
    show ?thesis using endpoint False
      target_selection_family_reference[OF fields(7,1,4)]
      target_selection_family_reference[OF fields(8,1,5)] by blast
  qed
qed

section \<open>The grammar determines all requests\<close>

definition publication_direct_requests ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> ('u\<times>local_address) set" where
  "publication_direct_requests E u root=
    {(u,d) |d. \<exists>R. artifact_at E u R \<and> d\<in>publication_citation_roots R root}"

definition publication_generation_sites ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> ('u\<times>local_address) set" where
  "publication_generation_sites E u root=
    {(v,a). \<exists>R d. artifact_at E u R \<and> d\<in>publication_generation_roots R root \<and> located_at E u d v a}"

definition publication_requests ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> ('u\<times>local_address) set" where
  "publication_requests E u root=publication_direct_requests E u root \<union>
    generation_requests E (publication_generation_sites E u root)"

definition publication_environment ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u artifact_environment" where
  "publication_environment E u root=read_environment E
    (insert u (image fst (publication_requests E u root))) (requested_slots E (publication_requests E u root))"

lemma publication_direct_requests_subset:
  "publication_direct_requests E u root\<subseteq>environment_positions E"
proof
  fix q assume "q\<in>publication_direct_requests E u root"
  then obtain d R where q: "q=(u,d)" and art: "artifact_at E u R"
    and member: "d\<in>publication_citation_roots R root"
    by (auto simp: publication_direct_requests_def)
  obtain M N K where shape: "publication_syntax_at R root M N K"
    using member by (auto simp: publication_citation_roots_def)
  have "d\<in>rra_carrier (object_structure R)" using publication_syntax_carrier(2)[OF shape] member by blast
  then show "q\<in>environment_positions E" using art q by auto
qed

lemma publication_generation_sites_have_cores:
  assumes pub: "publication_at E u root P" and site: "(v,a)\<in>publication_generation_sites E u root"
  shows "\<exists>G. generation_at E v a G"
proof -
  obtain R d where art: "artifact_at E u R" and member: "d\<in>publication_generation_roots R root"
    and loc: "located_at E u d v a"
    using site by (auto simp: publication_generation_sites_def)
  obtain w b G where other: "located_at E u d w b" and gen: "generation_at E w b G"
    using publication_generation_reference[OF pub art member] by blast
  have ef: "environment_formed E" using pub by (simp add: publication_at_def)
  have same: "v=w \<and> a=b" by (rule located_at_unique[OF ef loc other])
  show ?thesis using gen same by blast
qed

theorem publication_requests_formed:
  assumes pub: "publication_at E u root P"
  shows "citation_requests_formed E (publication_requests E u root)"
proof -
  have ef: "environment_formed E" using pub by (simp add: publication_at_def)
  have finite: "finite (publication_direct_requests E u root)"
    by (rule finite_subset[OF publication_direct_requests_subset environment_positions_finite[OF ef]])
  have direct: "citation_requests_formed E (publication_direct_requests E u root)"
    using ef finite publication_citations_interpretable[OF pub]
    by (auto simp: citation_requests_formed_def publication_direct_requests_def)
  have roots: "\<forall>v a. (v,a)\<in>publication_generation_sites E u root \<longrightarrow> (\<exists>G. generation_at E v a G)"
    using publication_generation_sites_have_cores[OF pub] by blast
  have generations: "citation_requests_formed E (generation_requests E (publication_generation_sites E u root))"
    by (rule generation_requests_formed[OF ef roots])
  show ?thesis unfolding publication_requests_def by (rule citation_requests_union[OF direct generations])
qed

lemma publication_read_boundary:
  assumes pub: "publication_at E u root P"
  shows "read_boundary_formed E (insert u (image fst (publication_requests E u root)))
    (requested_slots E (publication_requests E u root))"
proof -
  have base: "read_boundary_formed E (image fst (publication_requests E u root))
    (requested_slots E (publication_requests E u root))"
    by (rule requested_read_boundary[OF publication_requests_formed[OF pub]])
  have source: "u\<in>environment_uses E" using pub
    by (auto simp: publication_at_def environment_uses_def artifact_at_def rel_dom_def)
  show ?thesis using base source by (auto simp: read_boundary_formed_def)
qed

lemma publication_environment_formed:
  assumes "publication_at E u root P"
  shows "environment_formed (publication_environment E u root)"
  unfolding publication_environment_def by (rule read_environment_formed[OF publication_read_boundary[OF assms]])

lemma publication_environment_included:
  "environment_included (publication_environment E u root) E"
  unfolding publication_environment_def by (rule read_environment_included)

lemma publication_environment_source:
  "artifact_at (publication_environment E u root) u R\<longleftrightarrow>artifact_at E u R"
  by (simp add: publication_environment_def read_environment_uses_def)

section \<open>Retention preserves the entire publication\<close>

lemma selection_at_included:
  assumes source: "selection_at E u r S" and included: "environment_included E F"
    and formed: "environment_formed F"
  shows "selection_at F u r S"
proof -
  obtain R M g where fields: "artifact_at E u R" "family_at R r M" "inj_on g (rel_dom M)"
    "\<forall>s d. (s,d)\<in>M \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
    "S=Abs_fset (image g (rel_dom M))"
    using source unfolding selection_at_def by blast
  have copied: "artifact_at F u R" by (rule included_artifact[OF included fields(1)])
  have refs: "\<forall>s d. (s,d)\<in>M \<longrightarrow>
    (\<exists>v a. located_at F u d v a \<and> generation_at F v a (g s))"
    using fields(4) included_located[OF included] generation_at_included[OF _ included formed] by blast
  show ?thesis using formed copied fields(2,3,5) refs unfolding selection_at_def by blast
qed

lemma target_selection_at_included:
  assumes source: "target_selection_at E u r T" and included: "environment_included E F"
    and formed: "environment_formed F"
  shows "target_selection_at F u r T"
proof -
  obtain R M g where fields: "artifact_at E u R" "family_at R r M"
    "\<forall>s d. (s,d)\<in>M \<longrightarrow> anchored_at E u d (g s)"
    "inj_on snd (graph_map (rel_dom M) g)" "T=rel_ran (graph_map (rel_dom M) g)"
    using source unfolding target_selection_at_def anchor_family_at_def by blast
  have copied: "artifact_at F u R" by (rule included_artifact[OF included fields(1)])
  have refs: "\<forall>s d. (s,d)\<in>M \<longrightarrow> anchored_at F u d (g s)"
    using fields(3) included_anchor[OF included] by blast
  show ?thesis using formed copied fields(2,4,5) refs
    unfolding target_selection_at_def anchor_family_at_def by blast
qed

lemma publication_at_included:
  assumes source: "publication_at E u root P" and included: "environment_included E F"
    and formed: "environment_formed F"
  shows "publication_at F u root P"
  using source included formed unfolding publication_at_def snapshot_at_def
  by (meson included_artifact selection_at_included target_selection_at_included)

lemma selection_at_transfer:
  assumes selection: "selection_at E u r S" and art: "artifact_at E u R"
    and family: "family_at R r M" and formed: "environment_formed F" and copied: "artifact_at F u R"
    and refs: "\<And>d v a G. d\<in>rel_ran M \<Longrightarrow> located_at E u d v a \<Longrightarrow> generation_at E v a G \<Longrightarrow>
      located_at F u d v a \<and> generation_at F v a G"
  shows "selection_at F u r S"
proof -
  obtain N g where other: "family_at R r N" "inj_on g (rel_dom N)"
    "\<forall>s d. (s,d)\<in>N \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
    "S=Abs_fset (image g (rel_dom N))"
    using selection_at_source[OF selection art] by blast
  have same: "M=N" by (rule family_at_unique[OF family other(1)])
  have transferred: "\<forall>s d. (s,d)\<in>N \<longrightarrow>
    (\<exists>v a. located_at F u d v a \<and> generation_at F v a (g s))"
  proof (intro allI impI)
    fix s d assume pair: "(s,d)\<in>N"
    obtain v a where loc: "located_at E u d v a" and gen: "generation_at E v a (g s)"
      using other(3) pair by blast
    have endpoint: "d\<in>rel_ran M" using pair same by (auto simp: rel_ran_def)
    show "\<exists>v a. located_at F u d v a \<and> generation_at F v a (g s)"
      using refs[OF endpoint loc gen] by blast
  qed
  show ?thesis using formed copied other(1,2,4) transferred unfolding selection_at_def by blast
qed

lemma target_selection_at_transfer:
  assumes selection: "target_selection_at E u r T" and art: "artifact_at E u R"
    and family: "family_at R r M" and formed: "environment_formed F" and copied: "artifact_at F u R"
    and refs: "\<And>d t. d\<in>rel_ran M \<Longrightarrow> anchored_at E u d t \<Longrightarrow> anchored_at F u d t"
  shows "target_selection_at F u r T"
proof -
  obtain N g where other: "family_at R r N"
    "\<forall>s d. (s,d)\<in>N \<longrightarrow> anchored_at E u d (g s)"
    "inj_on snd (graph_map (rel_dom N) g)" "T=rel_ran (graph_map (rel_dom N) g)"
    using target_selection_at_source[OF selection art] by blast
  have same: "M=N" by (rule family_at_unique[OF family other(1)])
  have transferred: "\<forall>s d. (s,d)\<in>N \<longrightarrow> anchored_at F u d (g s)"
    using other(2) same refs by (auto simp: rel_ran_def; blast)
  show ?thesis using formed copied other(1,3,4) transferred
    unfolding target_selection_at_def anchor_family_at_def by blast
qed

lemma publication_at_transfer:
  assumes pub: "publication_at E u root P" and formed: "environment_formed F"
    and artifacts: "\<And>R. artifact_at E u R \<Longrightarrow> artifact_at F u R"
    and anchors: "\<And>d t. (u,d)\<in>publication_direct_requests E u root \<Longrightarrow>
      anchored_at E u d t \<Longrightarrow> anchored_at F u d t"
    and locations: "\<And>d v a. (u,d)\<in>publication_direct_requests E u root \<Longrightarrow>
      located_at E u d v a \<Longrightarrow> located_at F u d v a"
    and generations: "\<And>v a G. (v,a)\<in>publication_generation_sites E u root \<Longrightarrow>
      generation_at E v a G \<Longrightarrow> generation_at F v a G"
  shows "publication_at F u root P"
proof -
  obtain R ps sr dr er M N K where fields: "artifact_at E u R" "record_at R root ps [sr,dr,er]"
    "family_at R sr M" "family_at R dr N" "family_at R er K"
    "snapshot_at E u sr (publication_snapshot P)"
    "target_selection_at E u dr (fset (publication_dependencies P))"
    "target_selection_at E u er (fset (publication_evidence P))"
    using publication_at_families[OF pub] by blast
  have shape: "publication_syntax_at R root M N K" using fields(2-5)
    unfolding publication_syntax_at_def by blast
  have requests: "\<And>d. d\<in>rel_ran M\<union>rel_ran N\<union>rel_ran K \<Longrightarrow>
    (u,d)\<in>publication_direct_requests E u root"
    using fields(1) publication_roots_from_syntax(1)[OF shape]
    by (auto simp: publication_direct_requests_def)
  have copied: "artifact_at F u R" by (rule artifacts[OF fields(1)])
  have selection: "selection_at E u sr (publication_snapshot P)" using fields(6) by (simp add: snapshot_at_def)
  have selected: "selection_at F u sr (publication_snapshot P)"
  proof (rule selection_at_transfer[OF selection fields(1,3) formed copied])
    fix d v a G assume member: "d\<in>rel_ran M"
      and loc: "located_at E u d v a" and gen: "generation_at E v a G"
    have request: "(u,d)\<in>publication_direct_requests E u root" by (rule requests) (use member in simp)
    have site: "(v,a)\<in>publication_generation_sites E u root"
      using fields(1) loc member publication_roots_from_syntax(2)[OF shape]
      by (auto simp: publication_generation_sites_def)
    show "located_at F u d v a \<and> generation_at F v a G"
      using locations[OF request loc] generations[OF site gen] by blast
  qed
  have snapshot: "snapshot_at F u sr (publication_snapshot P)"
    using selected fields(6) by (simp add: snapshot_at_def)
  have dependencies: "target_selection_at F u dr (fset (publication_dependencies P))"
    by (rule target_selection_at_transfer[OF fields(7,1,4) formed copied])
       (use requests anchors in blast)
  have evidence: "target_selection_at F u er (fset (publication_evidence P))"
    by (rule target_selection_at_transfer[OF fields(8,1,5) formed copied])
       (use requests anchors in blast)
  show ?thesis using formed copied fields(2) snapshot dependencies evidence
    unfolding publication_at_def by blast
qed

theorem publication_at_restriction:
  assumes pub: "publication_at E u root P"
  shows "publication_at (publication_environment E u root) u root P"
proof -
  let ?Q="publication_requests E u root"
  let ?F="publication_environment E u root"
  let ?S="publication_generation_sites E u root"
  let ?C="generation_requests E ?S"
  have ef: "environment_formed E" using pub by (simp add: publication_at_def)
  have ff: "environment_formed ?F" by (rule publication_environment_formed[OF pub])
  have qformed: "citation_requests_formed E ?Q" by (rule publication_requests_formed[OF pub])
  have direct: "publication_direct_requests E u root\<subseteq>?Q" by (simp add: publication_requests_def)
  have recursive: "?C\<subseteq>?Q" by (simp add: publication_requests_def)
  have requests: "environment_included (request_environment E ?Q) ?F"
    unfolding publication_environment_def by (rule request_environment_read_included) auto
  have cores: "environment_included (request_environment E ?C) ?F"
    unfolding publication_environment_def
    by (rule request_environment_read_included)
       (use recursive requested_slots_mono[OF recursive] in auto)
  have roots: "\<forall>v a. (v,a)\<in>?S \<longrightarrow> (\<exists>G. generation_at E v a G)"
    using publication_generation_sites_have_cores[OF pub] by blast
  show ?thesis
  proof (rule publication_at_transfer[OF pub ff])
    fix R assume "artifact_at E u R"
    then show "artifact_at ?F u R" by (simp add: publication_environment_source)
  next
    fix d t assume member: "(u,d)\<in>publication_direct_requests E u root" and anchor: "anchored_at E u d t"
    have request: "(u,d)\<in>?Q" using direct member by blast
    have retained: "anchored_at (request_environment E ?Q) u d t"
      using requested_anchor_preserved[OF qformed request] anchor by simp
    show "anchored_at ?F u d t" by (rule included_anchor[OF requests retained])
  next
    fix d v a assume member: "(u,d)\<in>publication_direct_requests E u root" and loc: "located_at E u d v a"
    have request: "(u,d)\<in>?Q" using direct member by blast
    have retained: "located_at (request_environment E ?Q) u d v a"
      using requested_located_preserved[OF qformed request] loc by simp
    show "located_at ?F u d v a" by (rule included_located[OF requests retained])
  next
    fix v a G assume member: "(v,a)\<in>?S" and gen: "generation_at E v a G"
    have site: "(v,a)\<in>generation_read_sites E ?S" using generation_read_sites_roots[of ?S E] member by blast
    have retained: "generation_at (request_environment E ?C) v a G"
      by (rule generation_at_request_restriction[OF ef roots gen site])
    show "generation_at ?F v a G" by (rule generation_at_included[OF retained cores ff])
  qed
qed

section \<open>Successful readings determine one least retained environment\<close>

lemma publication_source_extension:
  assumes pub: "publication_at F u root P" and included: "environment_included F E"
    and formed: "environment_formed E"
  shows "artifact_at E u R\<longleftrightarrow>artifact_at F u R"
proof
  assume art: "artifact_at E u R"
  obtain T where source: "artifact_at F u T" using pub unfolding publication_at_def by blast
  have old: "artifact_at E u T" by (rule included_artifact[OF included source])
  have same: "R=T" by (rule environment_artifact_unique[OF formed art old])
  show "artifact_at F u R" using source same by simp
next
  assume "artifact_at F u R"
  then show "artifact_at E u R" by (rule included_artifact[OF included])
qed

lemma publication_generation_sites_extension:
  assumes pub: "publication_at F u root P" and included: "environment_included F E"
    and formed: "environment_formed E"
  shows "publication_generation_sites E u root=publication_generation_sites F u root"
proof -
  have sources: "\<And>R. artifact_at E u R\<longleftrightarrow>artifact_at F u R"
    by (rule publication_source_extension[OF pub included formed])
  have locations: "\<And>R d v a. artifact_at E u R \<Longrightarrow> d\<in>publication_generation_roots R root \<Longrightarrow>
    located_at E u d v a \<Longrightarrow> located_at F u d v a"
  proof -
    fix R d v a assume art: "artifact_at E u R" and member: "d\<in>publication_generation_roots R root"
      and loc: "located_at E u d v a"
    have copied: "artifact_at F u R" using art sources by simp
    obtain w b G where other: "located_at F u d w b"
      using publication_generation_reference[OF pub copied member] by blast
    have old: "located_at E u d w b" by (rule included_located[OF included other])
    have same: "v=w \<and> a=b" by (rule located_at_unique[OF formed loc old])
    show "located_at F u d v a" using other same by simp
  qed
  show ?thesis using sources locations included
    by (auto simp: publication_generation_sites_def; blast intro: included_located[OF included])
qed

theorem publication_requests_extension:
  assumes pub: "publication_at F u root P" and included: "environment_included F E"
    and formed: "environment_formed E"
  shows "publication_requests E u root=publication_requests F u root"
proof -
  have sources: "\<And>R. artifact_at E u R\<longleftrightarrow>artifact_at F u R"
    by (rule publication_source_extension[OF pub included formed])
  have direct: "publication_direct_requests E u root=publication_direct_requests F u root"
    by (simp only: publication_direct_requests_def sources)
  have sites: "publication_generation_sites E u root=publication_generation_sites F u root"
    by (rule publication_generation_sites_extension[OF pub included formed])
  have roots: "\<forall>v a. (v,a)\<in>publication_generation_sites F u root \<longrightarrow> (\<exists>G. generation_at F v a G)"
    using publication_generation_sites_have_cores[OF pub] by blast
  have recursive: "generation_requests E (publication_generation_sites F u root)=
    generation_requests F (publication_generation_sites F u root)"
    by (rule generation_requests_extension[OF roots included formed])
  show ?thesis by (simp only: publication_requests_def direct sites recursive)
qed

theorem publication_successful_reading_requires_dependencies:
  assumes pub: "publication_at F u root P" and included: "environment_included F E"
    and formed: "environment_formed E"
  shows "environment_included (publication_environment E u root) F"
proof -
  let ?Q="publication_requests E u root"
  have ff: "environment_formed F" using pub by (simp add: publication_at_def)
  have requests: "citation_requests_formed F ?Q"
    using publication_requests_formed[OF pub] publication_requests_extension[OF pub included formed] by simp
  have source: "u\<in>environment_uses F" using pub
    by (auto simp: publication_at_def environment_uses_def artifact_at_def rel_dom_def)
  have sources: "insert u (image fst ?Q)\<subseteq>environment_uses F"
    using source requested_uses_subset[OF requests] by (auto simp: requested_uses_def)
  have slots: "requested_slots E ?Q\<subseteq>rel_dom (environment_bindings F)"
    using requested_slots_extension[OF formed requests included] requested_slots_subset[OF requests] by simp
  show ?thesis unfolding publication_environment_def
    by (rule read_environment_least[OF formed ff included sources slots])
qed

theorem publication_requests_restricted:
  assumes pub: "publication_at E u root P"
  shows "publication_requests (publication_environment E u root) u root=publication_requests E u root"
proof -
  have formed: "environment_formed E" using pub by (simp add: publication_at_def)
  show ?thesis using publication_requests_extension[OF publication_at_restriction[OF pub]
      publication_environment_included formed] by simp
qed

theorem publication_slots_restricted:
  assumes pub: "publication_at E u root P"
  shows "requested_slots (publication_environment E u root)
    (publication_requests (publication_environment E u root) u root)=requested_slots E (publication_requests E u root)"
proof -
  have formed: "environment_formed E" using pub by (simp add: publication_at_def)
  have requests: "citation_requests_formed (publication_environment E u root) (publication_requests E u root)"
    using publication_requests_formed[OF publication_at_restriction[OF pub]]
      publication_requests_restricted[OF pub] by simp
  show ?thesis using requested_slots_extension[OF formed requests publication_environment_included]
    by (simp only: publication_requests_restricted[OF pub])
qed

theorem publication_environment_idempotent:
  assumes pub: "publication_at E u root P"
  shows "publication_environment (publication_environment E u root) u root=publication_environment E u root"
proof -
  have requests: "publication_requests (publication_environment E u root) u root=publication_requests E u root"
    by (rule publication_requests_restricted[OF pub])
  have slots: "requested_slots (publication_environment E u root)
    (publication_requests (publication_environment E u root) u root)=requested_slots E (publication_requests E u root)"
    by (rule publication_slots_restricted[OF pub])
  have fixed: "requested_slots (publication_environment E u root)
    (publication_requests E u root)=requested_slots E (publication_requests E u root)"
    using slots by (simp only: requests)
  have outer: "publication_environment (publication_environment E u root) u root=
    read_environment (publication_environment E u root) (insert u (image fst (publication_requests E u root)))
      (requested_slots E (publication_requests E u root))"
    by (simp only: publication_environment_def[of "publication_environment E u root" u root] requests fixed)
  have repeated: "read_environment (publication_environment E u root)
    (insert u (image fst (publication_requests E u root))) (requested_slots E (publication_requests E u root))=
    publication_environment E u root"
    by (simp only: publication_environment_def read_environment_idempotent)
  show ?thesis by (rule trans[OF outer repeated])
qed

theorem publication_minimal_environment_locality:
  assumes pub: "publication_at E u root P" and formed: "environment_formed F"
    and included: "environment_included (publication_environment E u root) F"
  shows "publication_at E u root Q\<longleftrightarrow>publication_at F u root Q"
proof -
  have retained: "publication_at F u root P"
    by (rule publication_at_included[OF publication_at_restriction[OF pub] included formed])
  show ?thesis
  proof
    assume other: "publication_at E u root Q"
    have same: "P=Q" by (rule publication_at_unique[OF pub other])
    show "publication_at F u root Q" using retained same by simp
  next
    assume other: "publication_at F u root Q"
    have same: "P=Q" by (rule publication_at_unique[OF retained other])
    show "publication_at E u root Q" using pub same by simp
  qed
qed

definition publication_environment_closed ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> publication_view \<Rightarrow> bool" where
  "publication_environment_closed E u root P \<longleftrightarrow> publication_at E u root P \<and>
    environment_closed E {u} (requested_slots E (publication_requests E u root))"

lemma publication_closed_environment_fixed:
  assumes closed: "publication_environment_closed E u root P"
  shows "publication_environment E u root=E"
proof -
  have pub: "publication_at E u root P" and boundary:
    "environment_closed E {u} (requested_slots E (publication_requests E u root))"
    using closed by (auto simp: publication_environment_closed_def)
  show ?thesis unfolding publication_environment_def
    by (rule read_environment_closed_fixed[OF publication_read_boundary[OF pub] boundary]) auto
qed

theorem publication_closed_restriction:
  assumes pub: "publication_at E u root P"
  shows "publication_environment_closed (publication_environment E u root) u root P"
proof -
  let ?F="publication_environment E u root"
  let ?Q="publication_requests E u root"
  let ?S="publication_generation_sites ?F u root"
  let ?U="insert u (image fst ?Q)"
  let ?D="requested_slots E ?Q"
  have retained: "publication_at ?F u root P" by (rule publication_at_restriction[OF pub])
  have requests: "publication_requests ?F u root=?Q" by (rule publication_requests_restricted[OF pub])
  have seeds: "image fst ?S\<subseteq>environment_reachable ?F {u}"
  proof
    fix v assume "v\<in>image fst ?S"
    then obtain a R d where loc: "located_at ?F u d v a"
      by (auto simp: publication_generation_sites_def)
    show "v\<in>environment_reachable ?F {u}"
      using located_at_use_edge[OF loc] by (auto simp: environment_reachable_def)
  qed
  have descendants: "environment_reachable ?F (image fst ?S)\<subseteq>environment_reachable ?F {u}"
    by (rule environment_reachable_least[OF seeds environment_reachable_edge_closed])
  have queried: "image fst ?Q\<subseteq>environment_reachable ?F {u}"
  proof
    fix v assume "v\<in>image fst ?Q"
    then obtain d where request: "(v,d)\<in>publication_requests ?F u root" using requests by auto
    show "v\<in>environment_reachable ?F {u}"
    proof (cases "(v,d)\<in>publication_direct_requests ?F u root")
      case True
      have "v=u" using True by (auto simp: publication_direct_requests_def)
      then show ?thesis by (auto simp: environment_reachable_def)
    next
      case False
      have recursive: "(v,d)\<in>generation_requests ?F ?S" using request False by (simp add: publication_requests_def)
      obtain a where site: "(v,a)\<in>generation_read_sites ?F ?S"
        using recursive by (auto simp: generation_requests_def)
      show ?thesis using generation_read_site_use_reachable[OF site] descendants by blast
    qed
  qed
  have reachable: "?U\<subseteq>environment_reachable ?F {u}"
    using queried environment_roots_reachable[of "{u}" ?F] by blast
  have boundary: "read_boundary_formed E ?U ?D" by (rule publication_read_boundary[OF pub])
  have closed: "environment_closed ?F {u} ?D"
    unfolding publication_environment_def
    by (rule read_environment_closed_from[OF boundary]) (use reachable in \<open>auto simp: publication_environment_def\<close>)
  show ?thesis using retained closed publication_slots_restricted[OF pub]
    by (simp add: publication_environment_closed_def)
qed

theorem publication_least_environment_unique:
  assumes pub: "publication_at F u root P" and included: "environment_included F E"
    and formed: "environment_formed E" and upper: "environment_included F (publication_environment E u root)"
  shows "F=publication_environment E u root"
  by (rule environment_included_antisym[OF upper
        publication_successful_reading_requires_dependencies[OF pub included formed]])

text \<open>
  The record and its complete families determine the direct requests. Only
  snapshot citations continue the generation reader, whose predecessor graph
  determines every recursive request. Dependency, evidence, locus, payload,
  and cause targets are retained as exact material without interpreting their
  outgoing bindings. The source publication artifact is retained even when
  every family is empty.

  Restriction retains the same publication, derives the same requests on
  rereading, and is closed from the publication use alone. Every included
  environment that still reads the publication must contain this restriction.
  Its view supplies neither evidence validity nor authority, and equal views
  do not identify different publication sites.
\<close>

end
