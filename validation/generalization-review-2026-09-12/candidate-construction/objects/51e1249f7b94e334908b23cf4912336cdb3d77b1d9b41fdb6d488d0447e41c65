theory RRA_Evidence
  imports RRA_Structural_Syntax
begin

section \<open>Exact links recovered from structural records\<close>

definition link_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
   exact_target \<Rightarrow> exact_target \<Rightarrow> bool" where
  "link_at E u l A B \<longleftrightarrow>
    (\<exists>R ps ar br. artifact_at E u R \<and> record_at R l ps [ar,br] \<and>
      anchored_at E u ar A \<and> anchored_at E u br B)"

lemma link_atI:
  assumes "artifact_at E u R" "record_at R l ps [ar,br]"
    "anchored_at E u ar A" "anchored_at E u br B"
  shows "link_at E u l A B"
  using assms unfolding link_at_def by blast

lemma link_at_unique:
  assumes formed: "environment_formed E"
    and first: "link_at E u l A B" and second: "link_at E u l C D"
  shows "A = C \<and> B = D"
proof -
  obtain R ps ar br where a: "artifact_at E u R" "record_at R l ps [ar,br]"
    "anchored_at E u ar A" "anchored_at E u br B"
    using first unfolding link_at_def by blast
  obtain S qs cr dr where b: "artifact_at E u S" "record_at S l qs [cr,dr]"
    "anchored_at E u cr C" "anchored_at E u dr D"
    using second unfolding link_at_def by blast
  have same: "R = S" by (rule environment_artifact_unique[OF formed a(1) b(1)])
  have endpoints: "ar = cr \<and> br = dr"
    using record_at_unique[OF a(2)] b(2) same by auto
  show ?thesis
    using anchored_at_unique[OF formed a(3)] anchored_at_unique[OF formed a(4)]
      b(3,4) endpoints by blast
qed

lemma link_targets_formed:
  assumes "link_at E u l A B"
  shows "target_formed A \<and> target_formed B"
  using assms unfolding link_at_def by (meson anchored_at_target_formed)

lemma link_environment_locality:
  assumes agree: "environment_agrees_on E F U"
    and closed: "environment_edge_closed E U" and member: "u \<in> U"
  shows "link_at E u l A B = link_at F u l A B"
proof -
  have arts: "\<forall>R. artifact_at E u R = artifact_at F u R"
    using agree member by (simp add: environment_agrees_on_def)
  have targets: "\<forall>r t. anchored_at E u r t = anchored_at F u r t"
    using anchored_at_environment_locality[OF agree closed member] by blast
  show ?thesis using arts targets unfolding link_at_def by blast
qed

section \<open>Envelopes retain link occurrences\<close>

type_synonym evidence_links =
  "(local_address \<times> (exact_target \<times> exact_target)) set"

definition envelope_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
   evidence_links \<Rightarrow> bool" where
  "envelope_at E u root L \<longleftrightarrow>
    environment_formed E \<and>
    (\<exists>R M. artifact_at E u R \<and> family_at R root M \<and>
      (\<forall>s l. (s,l) \<in> M \<longrightarrow> (\<exists>A B. link_at E u l A B)) \<and>
      L = {(s,(A,B)) |s l A B. (s,l) \<in> M \<and> link_at E u l A B})"

lemma envelope_atI:
  assumes "environment_formed E" "artifact_at E u R" "family_at R root M"
    "\<And>s l. (s,l) \<in> M \<Longrightarrow> \<exists>A B. link_at E u l A B"
    "L = {(s,(A,B)) |s l A B. (s,l) \<in> M \<and> link_at E u l A B}"
  shows "envelope_at E u root L"
  using assms unfolding envelope_at_def by blast

lemma envelope_at_unique:
  assumes first: "envelope_at E u root L" and second: "envelope_at E u root N"
  shows "L = N"
proof -
  obtain R M where a: "environment_formed E" "artifact_at E u R" "family_at R root M"
    "L = {(s,(A,B)) |s l A B. (s,l) \<in> M \<and> link_at E u l A B}"
    using first unfolding envelope_at_def by blast
  obtain S K where b: "artifact_at E u S" "family_at S root K"
    "N = {(s,(A,B)) |s l A B. (s,l) \<in> K \<and> link_at E u l A B}"
    using second unfolding envelope_at_def by blast
  have same: "R = S" by (rule environment_artifact_unique[OF a(1,2) b(1)])
  have sockets: "M = K" using family_at_unique[OF a(3)] b(2) same by blast
  show ?thesis using a(4) b(3) sockets by simp
qed

lemma envelope_complete_socket_domain:
  assumes env: "envelope_at E u root L"
    and art: "artifact_at E u R" and fam: "family_at R root M"
  shows "rel_dom L = rel_dom M"
proof -
  obtain S N where a: "environment_formed E" "artifact_at E u S" "family_at S root N"
    "\<forall>s l. (s,l) \<in> N \<longrightarrow> (\<exists>A B. link_at E u l A B)"
    "L = {(s,(A,B)) |s l A B. (s,l) \<in> N \<and> link_at E u l A B}"
    using env unfolding envelope_at_def by blast
  have same: "R = S" by (rule environment_artifact_unique[OF a(1) art a(2)])
  have sockets: "M = N" using family_at_unique[OF fam] a(3) same by blast
  show ?thesis using a(4) unfolding a(5) sockets rel_dom_def by (auto; blast)
qed

lemma envelope_single_valued:
  assumes env: "envelope_at E u root L"
  shows "single_valued L"
proof -
  obtain R M where art: "artifact_at E u R" and a: "environment_formed E" "family_at R root M"
    "L = {(s,(A,B)) |s l A B. (s,l) \<in> M \<and> link_at E u l A B}"
    using env unfolding envelope_at_def by blast
  have sv: "single_valued M" using a(2) by (simp add: family_at_def)
  show ?thesis
    using link_at_unique[OF a(1)] sv a(3)
    unfolding single_valued_def by blast
qed

lemma envelope_finite:
  assumes env: "envelope_at E u root L"
  shows "finite L"
proof -
  obtain R M where art: "artifact_at E u R" and fam: "family_at R root M"
    using env unfolding envelope_at_def by blast
  have domain: "finite (rel_dom L)"
    using envelope_complete_socket_domain[OF env art fam]
      finite_rel_dom[OF family_socket_graph_finite[OF fam]] by simp
  show ?thesis by (rule finite_single_valued[OF domain envelope_single_valued[OF env]])
qed

lemma envelope_targets_formed:
  assumes "envelope_at E u root L" "(s,(A,B)) \<in> L"
  shows "target_formed A \<and> target_formed B"
  using assms unfolding envelope_at_def by (auto dest: link_targets_formed)

lemma envelope_environment_locality:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and agree: "environment_agrees_on E F U"
    and closed: "environment_edge_closed E U" and member: "u \<in> U"
  shows "envelope_at E u root L = envelope_at F u root L"
proof -
  have arts: "\<forall>R. artifact_at E u R = artifact_at F u R"
    using agree member by (simp add: environment_agrees_on_def)
  have links: "\<forall>l A B. link_at E u l A B = link_at F u l A B"
    using link_environment_locality[OF agree closed member] by blast
  show ?thesis by (simp only: envelope_at_def ef ff arts links)
qed

lemma envelope_uniform_links:
  assumes formed: "environment_formed E" and art: "artifact_at E u R"
    and fam: "family_at R root M"
    and links: "\<And>s l. (s,l) \<in> M \<Longrightarrow> link_at E u l A B"
  shows "envelope_at E u root (graph_map (rel_dom M) (\<lambda>_. (A,B)))"
proof -
  have fixed: "\<And>s l C D. (s,l) \<in> M \<Longrightarrow>
    link_at E u l C D \<longleftrightarrow> C = A \<and> D = B"
  proof -
    fix s l C D assume member: "(s,l) \<in> M"
    have known: "link_at E u l A B" by (rule links[OF member])
    show "link_at E u l C D \<longleftrightarrow> C = A \<and> D = B"
      using known link_at_unique[OF formed known] by blast
  qed
  have projection: "graph_map (rel_dom M) (\<lambda>_. (A,B)) =
    {(s,(C,D)) |s l C D. (s,l) \<in> M \<and> link_at E u l C D}"
    using fixed by (auto simp: graph_map_def rel_dom_def; blast)
  show ?thesis
    by (rule envelope_atI[OF formed art fam _ projection]) (use links in blast)
qed

lemma repeated_links_in_a_closed_envelope:
  "\<exists>E :: unit artifact_environment. \<exists>root L.
    environment_closed E {()} {} \<and> envelope_at E () root L \<and>
    card (rel_dom L) = 2 \<and> card (rel_ran L) = 1"
proof -
  let ?R = "\<lparr>object_structure =
    \<lparr>rra_carrier = {[],[0],[1],[2],[3],[4],[5]},
      rra_incidence = {([],[1],[0]),([],[5],[0]),
        ([0],[2],[4]),([0],[3],[4]),([2],[2],[3])}\<rparr>,
    object_data = empty_basis\<rparr> :: exact_artifact"
  let ?E = "singleton_environment ?R"
  let ?M = "{([1],[0]),([5],[0])} :: (local_address \<times> local_address) set"
  let ?T = "Whole_Artifact ?R"
  let ?L = "{([1],(?T,?T)),([5],(?T,?T))} :: evidence_links"
  have formed: "exact_formed ?R"
    by (auto simp: exact_formed_def object_formed_def rra_formed_def octets_formed_def)
  have obj: "object_formed ?R" using formed by (simp add: exact_formed_def)
  have closed: "environment_closed ?E {()} {}"
    by (rule singleton_environment_closed[OF formed])
  have ef: "environment_formed ?E" using closed by (simp add: environment_closed_def)
  have art: "artifact_at ?E () ?R" by (simp add: artifact_at_def singleton_environment_def)
  have fam: "family_at ?R [] ?M"
    using obj by (auto simp: family_at_def headed_incidence_def single_valued_def rel_dom_def)
  have tail: "record_path (object_structure ?R) [0] [3] [[3]] [[4]]"
    by (rule record_path.path_last)
       (auto simp: headed_incidence_def field_endpoint_def)
  have path: "record_path (object_structure ?R) [0] [2] [[2],[3]] [[4],[4]]"
    by (rule record_path.path_slot[OF _ _ _ tail])
       (auto simp: headed_incidence_def field_endpoint_def)
  have rec: "record_at ?R [0] [[2],[3]] [[4],[4]]"
    using obj path by (auto simp: record_at_def raw_record_at_def headed_incidence_def)
  have raw: "raw_citation_at ?R [4] Local_Whole {[4]}"
    by (rule raw_citation_at.local_whole) (auto simp: headed_incidence_def)
  have cite: "citation_at ?R [4] Local_Whole {[4]}"
    using formed raw by (simp add: citation_at_def)
  have interpreted: "interpret_citation ?E () Local_Whole ?T"
    using art formed by auto
  have anchored: "anchored_at ?E () [4] ?T"
    by (rule anchored_atI[OF art cite interpreted])
  have link: "link_at ?E () [0] ?T ?T"
    by (rule link_atI[OF art rec anchored anchored])
  have all_links: "\<And>s l. (s,l) \<in> ?M \<Longrightarrow> link_at ?E () l ?T ?T"
    using link by auto
  have env0: "envelope_at ?E () [] (graph_map (rel_dom ?M) (\<lambda>_. (?T,?T)))"
    by (rule envelope_uniform_links[OF ef art fam all_links])
  have env: "envelope_at ?E () [] ?L"
    using env0 by (simp add: rel_dom_image)
  have sizes: "card (rel_dom ?L) = 2" "card (rel_ran ?L) = 1"
    by (simp_all add: rel_dom_image rel_ran_image)
  show ?thesis
    by (rule exI[of _ ?E], rule exI[of _ "[]"], rule exI[of _ ?L])
       (use closed env sizes in blast)
qed

text \<open>
  An envelope is a complete family of link occurrences. Socket identity is
  retained even when two sockets reach the same link or the same pair of
  targets. Its formation asserts neither truth of a target nor acceptance by
  an authority. Those judgments require their own supplied structure.
\<close>

end
