theory RRA_Generation_Dependencies
  imports RRA_Generation RRA_Citation_Closure
begin

section \<open>Requests determined by the generation grammar\<close>

definition generation_syntax_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow>
   (local_address \<times> local_address) set \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow> bool" where
  "generation_syntax_at R root lr M payr cr \<longleftrightarrow>
    (\<exists>ps pr. record_at R root ps [lr,pr,payr,cr] \<and> family_at R pr M)"

lemma generation_syntax_unique:
  assumes left: "generation_syntax_at R root lr M payr cr"
    and right: "generation_syntax_at R root lr' M' payr' cr'"
  shows "lr = lr' \<and> M = M' \<and> payr = payr' \<and> cr = cr'"
proof -
  obtain ps pr where a: "record_at R root ps [lr,pr,payr,cr]" "family_at R pr M"
    using left unfolding generation_syntax_at_def by blast
  obtain qs qr where b: "record_at R root qs [lr',qr,payr',cr']" "family_at R qr M'"
    using right unfolding generation_syntax_at_def by blast
  have fields: "lr = lr' \<and> pr = qr \<and> payr = payr' \<and> cr = cr'"
    using record_at_unique[OF a(1) b(1)] by simp
  have members: "M = M'" using family_at_unique[OF a(2)] b(2) fields by blast
  show ?thesis using fields members by blast
qed

definition generation_citation_roots :: "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "generation_citation_roots R root = {x. \<exists>lr M payr cr.
    generation_syntax_at R root lr M payr cr \<and> x \<in> {lr,payr,cr} \<union> rel_ran M}"

definition generation_predecessor_roots :: "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address set" where
  "generation_predecessor_roots R root = {x. \<exists>lr M payr cr.
    generation_syntax_at R root lr M payr cr \<and> x \<in> rel_ran M}"

lemma generation_roots_from_syntax:
  assumes shape: "generation_syntax_at R root lr M payr cr"
  shows "generation_citation_roots R root = {lr,payr,cr} \<union> rel_ran M"
    and "generation_predecessor_roots R root = rel_ran M"
proof -
  have project: "\<And>P. (\<exists>l N p c. generation_syntax_at R root l N p c \<and> P l N p c) \<longleftrightarrow>
    P lr M payr cr"
  proof -
    fix P
    show "(\<exists>l N p c. generation_syntax_at R root l N p c \<and> P l N p c) \<longleftrightarrow> P lr M payr cr"
    proof
      assume "\<exists>l N p c. generation_syntax_at R root l N p c \<and> P l N p c"
      then obtain l N p c where other: "generation_syntax_at R root l N p c" and holds: "P l N p c" by blast
      have eq: "lr = l \<and> M = N \<and> payr = p \<and> cr = c"
        by (rule generation_syntax_unique[OF shape other])
      show "P lr M payr cr" using holds eq by simp
    next
      assume holds: "P lr M payr cr"
      show "\<exists>l N p c. generation_syntax_at R root l N p c \<and> P l N p c"
        by (rule exI[of _ lr], rule exI[of _ M], rule exI[of _ payr], rule exI[of _ cr])
           (use shape holds in blast)
    qed
  qed
  show "generation_citation_roots R root = {lr,payr,cr} \<union> rel_ran M"
    by (simp only: generation_citation_roots_def project) auto
  show "generation_predecessor_roots R root = rel_ran M"
    by (simp only: generation_predecessor_roots_def project) auto
qed

lemma generation_syntax_carrier:
  assumes shape: "generation_syntax_at R root lr M payr cr"
  shows "root \<in> rra_carrier (object_structure R)"
    and "generation_citation_roots R root \<subseteq> rra_carrier (object_structure R)"
proof -
  obtain ps pr where rec: "record_at R root ps [lr,pr,payr,cr]" and fam: "family_at R pr M"
    using shape unfolding generation_syntax_at_def by blast
  show "root \<in> rra_carrier (object_structure R)" using rec by (simp add: record_at_def)
  have endpoints: "{lr,payr,cr} \<subseteq> rra_carrier (object_structure R)"
    using record_endpoints_in_carrier[OF rec] by auto
  have family: "rel_ran M \<subseteq> rra_carrier (object_structure R)"
    using fam by (auto simp: family_at_def rel_ran_def headed_incidence_def object_formed_def rra_formed_def)
  show "generation_citation_roots R root \<subseteq> rra_carrier (object_structure R)"
    using endpoints family by (simp add: generation_roots_from_syntax[OF shape])
qed

lemma generation_fields_syntax:
  assumes "generation_fields_at E u root l M p c"
  shows "\<exists>R lr payr cr. artifact_at E u R \<and> generation_syntax_at R root lr M payr cr \<and>
    anchored_at E u lr l \<and> anchored_at E u payr p \<and> anchored_at E u cr c"
  using assms unfolding generation_fields_at_def generation_syntax_at_def by blast

lemma generation_at_syntax:
  assumes "generation_at E u root G"
  shows "\<exists>R lr M payr cr. artifact_at E u R \<and> generation_syntax_at R root lr M payr cr"
  using assms by (cases rule: generation_at.cases) (meson generation_fields_syntax)

lemma generation_citations_interpretable:
  assumes gen: "generation_at E u root G" and art: "artifact_at E u R"
    and request: "x \<in> generation_citation_roots R root"
  shows "\<exists>t. anchored_at E u x t"
proof -
  obtain l M p c g where fields: "generation_fields_at E u root l M p c"
    and refs: "\<forall>s d. (s,d) \<in> M \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
    using gen by (cases rule: generation_at.cases) blast
  have ef: "environment_formed E" by (rule generation_at_environment_formed[OF gen])
  obtain S lr payr cr where a: "artifact_at E u S" "generation_syntax_at S root lr M payr cr"
    "anchored_at E u lr l" "anchored_at E u payr p" "anchored_at E u cr c"
    using generation_fields_syntax[OF fields] by blast
  have same: "R = S" by (rule environment_artifact_unique[OF ef art a(1)])
  have members: "x \<in> {lr,payr,cr} \<union> rel_ran M"
    using request generation_roots_from_syntax(1)[OF a(2)] same by simp
  show ?thesis
  proof (cases "x \<in> {lr,payr,cr}")
    case True
    then show ?thesis using a(3-5) by blast
  next
    case False
    obtain s where pair: "(s,x) \<in> M" using members False by (auto simp: rel_ran_def)
    obtain v b where loc: "located_at E u x v b" using refs pair by blast
    obtain T where target: "artifact_at E v T" using located_at_has_artifact[OF loc] by blast
    show ?thesis using located_at_target[OF ef loc target] by blast
  qed
qed

section \<open>Recursive predecessor locations\<close>

definition generation_request_edges ::
  "'u artifact_environment \<Rightarrow> (('u \<times> local_address) \<times> ('u \<times> local_address)) set" where
  "generation_request_edges E = {((u,r),(v,a)). \<exists>R d.
    artifact_at E u R \<and> d \<in> generation_predecessor_roots R r \<and> located_at E u d v a}"

definition generation_read_sites ::
  "'u artifact_environment \<Rightarrow> ('u \<times> local_address) set \<Rightarrow> ('u \<times> local_address) set" where
  "generation_read_sites E roots = {v. \<exists>u\<in>roots. (u,v) \<in> (generation_request_edges E)\<^sup>*}"

definition generation_requests ::
  "'u artifact_environment \<Rightarrow> ('u \<times> local_address) set \<Rightarrow> ('u \<times> local_address) set" where
  "generation_requests E roots = {(u,x). \<exists>r R.
    (u,r) \<in> generation_read_sites E roots \<and> artifact_at E u R \<and> x \<in> generation_citation_roots R r}"

lemma generation_request_edge_positions:
  assumes edge: "(s,t) \<in> generation_request_edges E"
  shows "s \<in> environment_positions E \<and> t \<in> environment_positions E"
proof -
  obtain u r v a R d where st: "s = (u,r)" "t = (v,a)"
    and art: "artifact_at E u R" and root: "d \<in> generation_predecessor_roots R r"
    and loc: "located_at E u d v a"
    using edge by (auto simp: generation_request_edges_def)
  obtain lr M payr cr where shape: "generation_syntax_at R r lr M payr cr"
    using root unfolding generation_predecessor_roots_def by blast
  have source: "(u,r) \<in> environment_positions E"
    using art generation_syntax_carrier(1)[OF shape] by auto
  obtain T where target: "artifact_at E v T" "anchor_formed (T,a)"
    using located_at_has_artifact[OF loc] by blast
  have destination: "(v,a) \<in> environment_positions E"
    using target by (auto simp: anchor_formed_def)
  show ?thesis using st source destination by simp
qed

lemma generation_read_sites_subset:
  assumes roots: "roots \<subseteq> environment_positions E"
  shows "generation_read_sites E roots \<subseteq> environment_positions E"
proof
  fix t assume "t \<in> generation_read_sites E roots"
  then obtain s where source: "s \<in> roots" and path: "(s,t) \<in> (generation_request_edges E)\<^sup>*"
    by (auto simp: generation_read_sites_def)
  have member: "s \<in> environment_positions E" using source roots by blast
  show "t \<in> environment_positions E"
    using path member by (induction rule: rtrancl_induct) (auto dest: generation_request_edge_positions)
qed

lemma generation_read_sites_finite:
  assumes formed: "environment_formed E" and roots: "roots \<subseteq> environment_positions E"
  shows "finite (generation_read_sites E roots)"
  by (rule finite_subset[OF generation_read_sites_subset[OF roots] environment_positions_finite[OF formed]])

lemma generation_requests_subset:
  "generation_requests E roots \<subseteq> environment_positions E"
proof
  fix request assume "request \<in> generation_requests E roots"
  then obtain u x r R where eq: "request = (u,x)" and art: "artifact_at E u R"
    and member: "x \<in> generation_citation_roots R r"
    by (auto simp: generation_requests_def)
  obtain lr M payr cr where shape: "generation_syntax_at R r lr M payr cr"
    using member unfolding generation_citation_roots_def by blast
  have "x \<in> rra_carrier (object_structure R)"
    using generation_syntax_carrier(2)[OF shape] member by blast
  then show "request \<in> environment_positions E" using art eq by auto
qed

lemma generation_requests_finite:
  assumes "environment_formed E"
  shows "finite (generation_requests E roots)"
  by (rule finite_subset[OF generation_requests_subset environment_positions_finite[OF assms]])

lemma generation_request_edge_has_core:
  assumes gen: "generation_at E u r G" and edge: "((u,r),(v,a)) \<in> generation_request_edges E"
  shows "\<exists>H. generation_at E v a H"
proof -
  have ef: "environment_formed E" by (rule generation_at_environment_formed[OF gen])
  obtain R d where art: "artifact_at E u R" and member: "d \<in> generation_predecessor_roots R r"
    and loc: "located_at E u d v a"
    using edge by (auto simp: generation_request_edges_def)
  obtain l M p c g where fields: "generation_fields_at E u r l M p c"
    and refs: "\<forall>s d. (s,d) \<in> M \<longrightarrow>
      (\<exists>w b. located_at E u d w b \<and> generation_at E w b (g s))"
    using gen by (cases rule: generation_at.cases) blast
  obtain S lr payr cr where source: "artifact_at E u S" and shape: "generation_syntax_at S r lr M payr cr"
    using generation_fields_syntax[OF fields] by blast
  have same: "R = S" by (rule environment_artifact_unique[OF ef art source])
  have predecessor: "d \<in> rel_ran M" using member generation_roots_from_syntax(2)[OF shape] same by simp
  obtain s where pair: "(s,d) \<in> M" using predecessor by (auto simp: rel_ran_def)
  obtain w b where other: "located_at E u d w b" and child: "generation_at E w b (g s)"
    using refs pair by blast
  have target: "v = w \<and> a = b" by (rule located_at_unique[OF ef loc other])
  show ?thesis using child target by blast
qed

lemma generation_read_sites_have_cores:
  assumes roots: "\<forall>u r. (u,r) \<in> roots \<longrightarrow> (\<exists>G. generation_at E u r G)"
    and site: "(u,r) \<in> generation_read_sites E roots"
  shows "\<exists>G. generation_at E u r G"
proof -
  let ?valid = "\<lambda>p. \<exists>G. generation_at E (fst p) (snd p) G"
  have step: "\<And>s t. (s,t) \<in> generation_request_edges E \<Longrightarrow> ?valid s \<Longrightarrow> ?valid t"
  proof -
    fix s t assume edge: "(s,t) \<in> generation_request_edges E" and valid: "?valid s"
    obtain su sr where s: "s = (su,sr)" by (cases s)
    obtain tu tr where t: "t = (tu,tr)" by (cases t)
    obtain G where source: "generation_at E su sr G" using valid s by auto
    have pair: "((su,sr),(tu,tr)) \<in> generation_request_edges E" using edge s t by simp
    show "?valid t" using generation_request_edge_has_core[OF source pair] t by simp
  qed
  obtain source where initial: "source \<in> roots" and path: "(source,(u,r)) \<in> (generation_request_edges E)\<^sup>*"
    using site by (auto simp: generation_read_sites_def)
  have start: "?valid source" using roots initial by (cases source) auto
  have "?valid (u,r)" using path start by (induction rule: rtrancl_induct) (auto intro: step)
  then show ?thesis by simp
qed

theorem generation_requests_formed:
  assumes formed: "environment_formed E"
    and roots: "\<forall>u r. (u,r) \<in> roots \<longrightarrow> (\<exists>G. generation_at E u r G)"
  shows "citation_requests_formed E (generation_requests E roots)"
proof -
  have fin: "finite (generation_requests E roots)" by (rule generation_requests_finite[OF formed])
  have interpretable: "\<forall>u x. (u,x) \<in> generation_requests E roots \<longrightarrow> (\<exists>t. anchored_at E u x t)"
  proof (intro allI impI)
    fix u x assume request: "(u,x) \<in> generation_requests E roots"
    obtain r R where site: "(u,r) \<in> generation_read_sites E roots" and art: "artifact_at E u R"
      and member: "x \<in> generation_citation_roots R r"
      using request by (auto simp: generation_requests_def)
    obtain G where gen: "generation_at E u r G" using generation_read_sites_have_cores[OF roots site] by blast
    show "\<exists>t. anchored_at E u x t" by (rule generation_citations_interpretable[OF gen art member])
  qed
  show ?thesis using formed fin interpretable by (simp add: citation_requests_formed_def)
qed

lemma generation_read_sites_step:
  assumes "s \<in> generation_read_sites E roots" "(s,t) \<in> generation_request_edges E"
  shows "t \<in> generation_read_sites E roots"
proof -
  obtain q where root: "q \<in> roots" and path: "(q,s) \<in> (generation_request_edges E)\<^sup>*"
    using assms(1) by (auto simp: generation_read_sites_def)
  have extended: "(q,t) \<in> (generation_request_edges E)\<^sup>*"
    by (rule rtrancl_into_rtrancl[OF path assms(2)])
  show ?thesis using root extended by (auto simp: generation_read_sites_def)
qed

lemma generation_read_sites_roots:
  "roots \<subseteq> generation_read_sites E roots"
  by (auto simp: generation_read_sites_def)

section \<open>Recovery from the exact dependency restriction\<close>

lemma generation_fields_included:
  assumes included: "environment_included E F" and target: "environment_formed F"
    and fields: "generation_fields_at E u r l M p c"
  shows "generation_fields_at F u r l M p c"
  using fields target included unfolding generation_fields_at_def
  by (meson included_artifact included_anchor)

lemma generation_at_included:
  assumes source: "generation_at E u r G" and included: "environment_included E F"
    and target: "environment_formed F"
  shows "generation_at F u r G"
  using source
proof (induction rule: generation_at.induct)
  case (generation u root l M p c g)
  have fields: "generation_fields_at F u root l M p c"
    by (rule generation_fields_included[OF included target generation.hyps(1)])
  have refs: "\<forall>s d. (s,d) \<in> M \<longrightarrow>
    (\<exists>v a. located_at F u d v a \<and> generation_at F v a (g s))"
    using generation.IH included by (meson included_located)
  show ?case by (rule generation_at.generation[OF fields generation.hyps(2) refs])
qed

lemma generation_at_request_restriction:
  assumes formed: "environment_formed E"
    and roots: "\<forall>u r. (u,r) \<in> roots \<longrightarrow> (\<exists>G. generation_at E u r G)"
    and gen: "generation_at E u r G" and site: "(u,r) \<in> generation_read_sites E roots"
  shows "generation_at (request_environment E (generation_requests E roots)) u r G"
proof -
  let ?Q = "generation_requests E roots"
  let ?F = "request_environment E ?Q"
  have qformed: "citation_requests_formed E ?Q" by (rule generation_requests_formed[OF formed roots])
  have ff: "environment_formed ?F" by (rule request_environment_formed[OF qformed])
  show ?thesis using gen site
  proof (induction rule: generation_at.induct)
    case (generation u root l M p c g)
    obtain R ps lr pr payr cr where a: "artifact_at E u R"
      "record_at R root ps [lr,pr,payr,cr]" "family_at R pr M"
      "anchored_at E u lr l" "anchored_at E u payr p" "anchored_at E u cr c"
      using generation.hyps(1) unfolding generation_fields_at_def by blast
    have shape: "generation_syntax_at R root lr M payr cr"
      using a(2,3) unfolding generation_syntax_at_def by blast
    have requests: "\<And>x. x \<in> {lr,payr,cr} \<union> rel_ran M \<Longrightarrow> (u,x) \<in> ?Q"
      using generation.prems a(1) generation_roots_from_syntax(1)[OF shape]
      by (auto simp: generation_requests_def)
    have ql: "(u,lr) \<in> ?Q" and qp: "(u,payr) \<in> ?Q" and qc: "(u,cr) \<in> ?Q"
      by (auto intro: requests)
    have use_member: "u \<in> requested_uses E ?Q"
      using ql by (auto simp: requested_uses_def intro: rev_image_eqI)
    have art: "artifact_at ?F u R" using a(1) use_member by simp
    have locus: "anchored_at ?F u lr l" using requested_anchor_preserved[OF qformed ql] a(4) by simp
    have payload: "anchored_at ?F u payr p" using requested_anchor_preserved[OF qformed qp] a(5) by simp
    have cause: "anchored_at ?F u cr c" using requested_anchor_preserved[OF qformed qc] a(6) by simp
    have fields: "generation_fields_at ?F u root l M p c"
      by (rule generation_fields_atI[OF ff art a(2,3) locus payload cause])
    have refs: "\<forall>s d. (s,d) \<in> M \<longrightarrow>
      (\<exists>v b. located_at ?F u d v b \<and> generation_at ?F v b (g s))"
    proof (intro allI impI)
      fix s d assume pair: "(s,d) \<in> M"
      obtain v b where loc: "located_at E u d v b"
        and ih: "(v,b) \<in> generation_read_sites E roots \<Longrightarrow> generation_at ?F v b (g s)"
        using generation.IH pair by blast
      have member: "d \<in> rel_ran M" using pair by (auto simp: rel_ran_def)
      have request: "(u,d) \<in> ?Q" by (rule requests) (use member in simp)
      have pred: "d \<in> generation_predecessor_roots R root"
        using member by (simp add: generation_roots_from_syntax(2)[OF shape])
      have edge: "((u,root),(v,b)) \<in> generation_request_edges E"
        using a(1) pred loc by (auto simp: generation_request_edges_def)
      have child_site: "(v,b) \<in> generation_read_sites E roots"
        by (rule generation_read_sites_step[OF generation.prems edge])
      have child: "generation_at ?F v b (g s)" by (rule ih[OF child_site])
      have relocated: "located_at ?F u d v b"
        using requested_located_preserved[OF qformed request] loc by simp
      show "\<exists>v b. located_at ?F u d v b \<and> generation_at ?F v b (g s)"
        using relocated child by blast
    qed
    show ?case by (rule generation_at.generation[OF fields generation.hyps(2) refs])
  qed
qed

theorem generation_core_dependency_locality:
  assumes formed: "environment_formed E"
    and roots: "\<forall>u r. (u,r) \<in> roots \<longrightarrow> (\<exists>G. generation_at E u r G)"
    and site: "(u,r) \<in> generation_read_sites E roots"
  shows "generation_at (request_environment E (generation_requests E roots)) u r G \<longleftrightarrow>
    generation_at E u r G"
proof
  assume "generation_at (request_environment E (generation_requests E roots)) u r G"
  then show "generation_at E u r G"
    by (rule generation_at_included[OF _ request_environment_included formed])
next
  assume "generation_at E u r G"
  then show "generation_at (request_environment E (generation_requests E roots)) u r G"
    by (rule generation_at_request_restriction[OF formed roots _ site])
qed

lemma generation_request_edges_included:
  assumes "environment_included E F"
  shows "generation_request_edges E \<subseteq> generation_request_edges F"
  using assms unfolding generation_request_edges_def
  by (auto dest: included_artifact included_located)

lemma generation_request_edge_restricted:
  assumes formed: "citation_requests_formed E (generation_requests E roots)"
    and site: "s \<in> generation_read_sites E roots" and edge: "(s,t) \<in> generation_request_edges E"
  shows "(s,t) \<in> generation_request_edges (request_environment E (generation_requests E roots))"
proof -
  let ?Q = "generation_requests E roots"
  let ?F = "request_environment E ?Q"
  obtain u r v a R d where st: "s = (u,r)" "t = (v,a)"
    and art: "artifact_at E u R" and member: "d \<in> generation_predecessor_roots R r"
    and loc: "located_at E u d v a"
    using edge by (auto simp: generation_request_edges_def)
  have citation: "d \<in> generation_citation_roots R r"
    using member unfolding generation_predecessor_roots_def generation_citation_roots_def by blast
  have request: "(u,d) \<in> ?Q" using site st art citation by (auto simp: generation_requests_def)
  have use_member: "u \<in> requested_uses E ?Q"
    using request by (auto simp: requested_uses_def intro: rev_image_eqI)
  have copied: "artifact_at ?F u R" using art use_member by simp
  have relocated: "located_at ?F u d v a"
    using requested_located_preserved[OF formed request] loc by simp
  show ?thesis using st copied member relocated by (auto simp: generation_request_edges_def)
qed

lemma generation_read_sites_restricted:
  assumes formed: "citation_requests_formed E (generation_requests E roots)"
  shows "generation_read_sites (request_environment E (generation_requests E roots)) roots =
    generation_read_sites E roots"
proof -
  let ?F = "request_environment E (generation_requests E roots)"
  have included: "generation_request_edges ?F \<subseteq> generation_request_edges E"
    by (rule generation_request_edges_included[OF request_environment_included])
  have upper: "generation_read_sites ?F roots \<subseteq> generation_read_sites E roots"
    using rtrancl_mono[OF included] by (auto simp: generation_read_sites_def)
  have lower: "generation_read_sites E roots \<subseteq> generation_read_sites ?F roots"
  proof
    fix t assume "t \<in> generation_read_sites E roots"
    then obtain source where root: "source \<in> roots" and path: "(source,t) \<in> (generation_request_edges E)\<^sup>*"
      by (auto simp: generation_read_sites_def)
    have copied: "(source,t) \<in> (generation_request_edges ?F)\<^sup>*"
      using path
    proof (induction rule: rtrancl_induct)
      case base
      then show ?case by simp
    next
      case (step y z)
      have site: "y \<in> generation_read_sites E roots"
        using root step.hyps(1) by (auto simp: generation_read_sites_def)
      have edge: "(y,z) \<in> generation_request_edges ?F"
        by (rule generation_request_edge_restricted[OF formed site step.hyps(2)])
      show ?case by (rule rtrancl_into_rtrancl[OF step.IH edge])
    qed
    show "t \<in> generation_read_sites ?F roots" using root copied by (auto simp: generation_read_sites_def)
  qed
  show ?thesis using upper lower by blast
qed

theorem generation_requests_restricted:
  assumes formed: "citation_requests_formed E (generation_requests E roots)"
  shows "generation_requests (request_environment E (generation_requests E roots)) roots =
    generation_requests E roots"
proof -
  let ?Q = "generation_requests E roots"
  let ?F = "request_environment E ?Q"
  have sites: "generation_read_sites ?F roots = generation_read_sites E roots"
    by (rule generation_read_sites_restricted[OF formed])
  have upper: "generation_requests ?F roots \<subseteq> ?Q"
    using sites by (auto simp: generation_requests_def)
  have lower: "?Q \<subseteq> generation_requests ?F roots"
  proof
    fix request assume member: "request \<in> ?Q"
    obtain u x r R where eq: "request = (u,x)" and site: "(u,r) \<in> generation_read_sites E roots"
      and art: "artifact_at E u R" and citation: "x \<in> generation_citation_roots R r"
      using member by (auto simp: generation_requests_def)
    have use_member: "u \<in> requested_uses E ?Q"
      using member eq by (auto simp: requested_uses_def intro: rev_image_eqI)
    have copied: "artifact_at ?F u R" using art use_member by simp
    show "request \<in> generation_requests ?F roots"
      using eq site copied citation sites by (auto simp: generation_requests_def)
  qed
  show ?thesis using upper lower by blast
qed

lemma generation_request_edge_uses:
  assumes edge: "(s,t) \<in> generation_request_edges E"
  shows "fst s = fst t \<or> (fst s,fst t) \<in> environment_edges E"
proof -
  obtain u r v a d where st: "s = (u,r)" "t = (v,a)" and loc: "located_at E u d v a"
    using edge by (auto simp: generation_request_edges_def)
  show ?thesis using located_at_use_edge[OF loc] st by simp
qed

lemma generation_request_path_uses:
  assumes path: "(s,t) \<in> (generation_request_edges E)\<^sup>*"
  shows "(fst s,fst t) \<in> (environment_edges E)\<^sup>*"
  using path
proof (induction rule: rtrancl_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have one: "(fst y,fst z) \<in> (environment_edges E)\<^sup>*"
    using generation_request_edge_uses[OF step.hyps(2)] by auto
  show ?case by (rule rtrancl_trans[OF step.IH one])
qed

lemma generation_read_site_use_reachable:
  assumes site: "(u,r) \<in> generation_read_sites E roots"
  shows "u \<in> environment_reachable E (fst ` roots)"
proof -
  obtain source where root: "source \<in> roots" and path: "(source,(u,r)) \<in> (generation_request_edges E)\<^sup>*"
    using site by (auto simp: generation_read_sites_def)
  have use_root: "fst source \<in> fst ` roots" using root by simp
  have use_path: "(fst source,u) \<in> (environment_edges E)\<^sup>*"
    using generation_request_path_uses[OF path] by simp
  show ?thesis using use_root use_path unfolding environment_reachable_def by blast
qed

lemma generation_site_has_request:
  assumes gen: "generation_at E u r G" and site: "(u,r) \<in> generation_read_sites E roots"
  shows "u \<in> fst ` generation_requests E roots"
proof -
  obtain R lr M payr cr where art: "artifact_at E u R" and shape: "generation_syntax_at R r lr M payr cr"
    using generation_at_syntax[OF gen] by blast
  have member: "lr \<in> generation_citation_roots R r"
    by (simp add: generation_roots_from_syntax(1)[OF shape])
  have request: "(u,lr) \<in> generation_requests E roots"
    using site art member by (auto simp: generation_requests_def)
  show ?thesis using request by (auto intro: rev_image_eqI)
qed

definition generation_environment_closed ::
  "'u artifact_environment \<Rightarrow> ('u \<times> local_address) set \<Rightarrow> bool" where
  "generation_environment_closed E roots \<longleftrightarrow>
    (\<forall>u r. (u,r) \<in> roots \<longrightarrow> (\<exists>G. generation_at E u r G)) \<and>
    environment_closed E (fst ` roots) (requested_slots E (generation_requests E roots))"

theorem generation_closed_restriction:
  assumes formed: "environment_formed E"
    and roots: "\<forall>u r. (u,r) \<in> roots \<longrightarrow> (\<exists>G. generation_at E u r G)"
  shows "generation_environment_closed (request_environment E (generation_requests E roots)) roots"
proof -
  let ?Q = "generation_requests E roots"
  let ?F = "request_environment E ?Q"
  have qformed: "citation_requests_formed E ?Q" by (rule generation_requests_formed[OF formed roots])
  have requests: "generation_requests ?F roots = ?Q" by (rule generation_requests_restricted[OF qformed])
  have root_sources: "fst ` roots \<subseteq> fst ` ?Q"
  proof
    fix u assume "u \<in> fst ` roots"
    then obtain r where member: "(u,r) \<in> roots" by auto
    obtain G where gen: "generation_at E u r G" using roots member by blast
    have site: "(u,r) \<in> generation_read_sites E roots"
      using generation_read_sites_roots[of roots E] member by blast
    show "u \<in> fst ` ?Q" by (rule generation_site_has_request[OF gen site])
  qed
  have reachable: "fst ` ?Q \<subseteq> environment_reachable ?F (fst ` roots)"
  proof
    fix u assume member: "u \<in> fst ` ?Q"
    obtain x where request: "(u,x) \<in> generation_requests ?F roots" using member requests by auto
    obtain r where site: "(u,r) \<in> generation_read_sites ?F roots"
      using request by (auto simp: generation_requests_def)
    show "u \<in> environment_reachable ?F (fst ` roots)" by (rule generation_read_site_use_reachable[OF site])
  qed
  have closed: "environment_closed ?F (fst ` roots) (requested_slots E ?Q)"
    by (rule request_environment_closed_from[OF qformed root_sources reachable])
  have retained: "\<forall>u r. (u,r) \<in> roots \<longrightarrow> (\<exists>G. generation_at ?F u r G)"
  proof (intro allI impI)
    fix u r assume member: "(u,r) \<in> roots"
    obtain G where gen: "generation_at E u r G" using roots member by blast
    have site: "(u,r) \<in> generation_read_sites E roots"
      using generation_read_sites_roots[of roots E] member by blast
    show "\<exists>G. generation_at ?F u r G"
      using generation_at_request_restriction[OF formed roots gen site] by blast
  qed
  show ?thesis using retained closed requests
    by (simp add: generation_environment_closed_def)
qed

theorem generation_minimal_environment_locality:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and roots: "\<forall>u r. (u,r) \<in> roots \<longrightarrow> (\<exists>G. generation_at E u r G)"
    and included: "environment_included (request_environment E (generation_requests E roots)) F"
    and site: "(u,r) \<in> generation_read_sites E roots"
  shows "generation_at E u r G \<longleftrightarrow> generation_at F u r G"
proof
  assume source: "generation_at E u r G"
  have restricted: "generation_at (request_environment E (generation_requests E roots)) u r G"
    by (rule generation_at_request_restriction[OF ef roots source site])
  show "generation_at F u r G" by (rule generation_at_included[OF restricted included ff])
next
  assume target: "generation_at F u r G"
  obtain H where source: "generation_at E u r H" using generation_read_sites_have_cores[OF roots site] by blast
  have restricted: "generation_at (request_environment E (generation_requests E roots)) u r H"
    by (rule generation_at_request_restriction[OF ef roots source site])
  have other: "generation_at F u r H" by (rule generation_at_included[OF restricted included ff])
  have same: "G = H" by (rule generation_at_unique[OF target other])
  show "generation_at E u r G" using source same by simp
qed

corollary generation_dependency_material_is_required:
  assumes formed: "environment_formed E"
    and roots: "\<forall>u r. (u,r) \<in> roots \<longrightarrow> (\<exists>G. generation_at E u r G)"
    and smaller: "citation_requests_formed F (generation_requests E roots)"
    and included: "environment_included F E"
  shows "environment_included (request_environment E (generation_requests E roots)) F"
  by (rule request_environment_least[OF generation_requests_formed[OF formed roots] smaller included])

section \<open>Every successful reading requires the same recursive references\<close>

lemma generation_request_edge_extension:
  assumes gen: "generation_at F u r G" and included: "environment_included F E"
    and formed: "environment_formed E"
    and edge: "((u,r),(v,a))\<in>generation_request_edges E"
  shows "((u,r),(v,a))\<in>generation_request_edges F"
proof -
  obtain R d where art: "artifact_at E u R"
    and member: "d\<in>generation_predecessor_roots R r" and loc: "located_at E u d v a"
    using edge by (auto simp: generation_request_edges_def)
  obtain l M p c g where fields: "generation_fields_at F u r l M p c"
    and refs: "\<forall>s d. (s,d)\<in>M \<longrightarrow>
      (\<exists>w b. located_at F u d w b \<and> generation_at F w b (g s))"
    using gen by (cases rule: generation_at.cases) blast
  obtain S lr payr cr where source: "artifact_at F u S"
    and shape: "generation_syntax_at S r lr M payr cr"
    using generation_fields_syntax[OF fields] by blast
  have old: "artifact_at E u S" by (rule included_artifact[OF included source])
  have same: "R=S" by (rule environment_artifact_unique[OF formed art old])
  have predecessor: "d\<in>rel_ran M"
    using member generation_roots_from_syntax(2)[OF shape] same by simp
  obtain s where pair: "(s,d)\<in>M" using predecessor by (auto simp: rel_ran_def)
  obtain w b where other: "located_at F u d w b" using refs pair by blast
  have other_old: "located_at E u d w b" by (rule included_located[OF included other])
  have destination: "v=w \<and> a=b" by (rule located_at_unique[OF formed loc other_old])
  show ?thesis using source member same other destination
    by (auto simp: generation_request_edges_def)
qed

lemma generation_read_sites_extension:
  assumes roots: "\<forall>u r. (u,r)\<in>roots \<longrightarrow> (\<exists>G. generation_at F u r G)"
    and included: "environment_included F E" and formed: "environment_formed E"
  shows "generation_read_sites E roots=generation_read_sites F roots"
proof -
  have edges: "generation_request_edges F\<subseteq>generation_request_edges E"
    by (rule generation_request_edges_included[OF included])
  have lower: "generation_read_sites F roots\<subseteq>generation_read_sites E roots"
    using rtrancl_mono[OF edges] by (auto simp: generation_read_sites_def)
  have upper: "generation_read_sites E roots\<subseteq>generation_read_sites F roots"
  proof
    fix t assume "t\<in>generation_read_sites E roots"
    then obtain s where root: "s\<in>roots" and path: "(s,t)\<in>(generation_request_edges E)\<^sup>*"
      by (auto simp: generation_read_sites_def)
    have copied: "(s,t)\<in>(generation_request_edges F)\<^sup>*"
      using path
    proof (induction rule: rtrancl_induct)
      case base
      show ?case by simp
    next
      case (step y z)
      obtain u r where y: "y=(u,r)" by (cases y)
      obtain v a where z: "z=(v,a)" by (cases z)
      have site: "(u,r)\<in>generation_read_sites F roots"
        using root step.IH y by (auto simp: generation_read_sites_def)
      obtain G where gen: "generation_at F u r G"
        using generation_read_sites_have_cores[OF roots site] by blast
      have edge: "((u,r),(v,a))\<in>generation_request_edges E" using step.hyps(2) y z by simp
      have retained: "(y,z)\<in>generation_request_edges F"
        using generation_request_edge_extension[OF gen included formed edge] y z by simp
      show ?case by (rule rtrancl_into_rtrancl[OF step.IH retained])
    qed
    show "t\<in>generation_read_sites F roots" using root copied by (auto simp: generation_read_sites_def)
  qed
  show ?thesis using lower upper by blast
qed

theorem generation_requests_extension:
  assumes roots: "\<forall>u r. (u,r)\<in>roots \<longrightarrow> (\<exists>G. generation_at F u r G)"
    and included: "environment_included F E" and formed: "environment_formed E"
  shows "generation_requests E roots=generation_requests F roots"
proof -
  have sites: "generation_read_sites E roots=generation_read_sites F roots"
    by (rule generation_read_sites_extension[OF roots included formed])
  have sources: "\<And>u r R. (u,r)\<in>generation_read_sites E roots \<Longrightarrow>
    artifact_at E u R \<Longrightarrow> artifact_at F u R"
  proof -
    fix u r R assume site: "(u,r)\<in>generation_read_sites E roots" and art: "artifact_at E u R"
    have retained: "(u,r)\<in>generation_read_sites F roots" using site sites by simp
    obtain G where gen: "generation_at F u r G"
      using generation_read_sites_have_cores[OF roots retained] by blast
    obtain S lr M payr cr where source: "artifact_at F u S"
      using generation_at_syntax[OF gen] by blast
    have old: "artifact_at E u S" by (rule included_artifact[OF included source])
    have same: "R=S" by (rule environment_artifact_unique[OF formed art old])
    show "artifact_at F u R" using source same by simp
  qed
  show ?thesis using sites sources included
    by (auto simp: generation_requests_def; blast intro: included_artifact[OF included])
qed

theorem generation_successful_reading_requires_dependencies:
  assumes roots: "\<forall>u r. (u,r)\<in>roots \<longrightarrow> (\<exists>G. generation_at F u r G)"
    and included: "environment_included F E"
    and ef: "environment_formed E" and ff: "environment_formed F"
  shows "environment_included (request_environment E (generation_requests E roots)) F"
proof -
  have retained: "citation_requests_formed F (generation_requests E roots)"
    using generation_requests_formed[OF ff roots] generation_requests_extension[OF roots included ef] by simp
  have source: "citation_requests_formed E (generation_requests E roots)"
    using retained ef by (auto simp: citation_requests_formed_def; meson included_anchor[OF included])
  show ?thesis by (rule request_environment_least[OF source retained included])
qed

text \<open>
  The selected generation roots determine all recursive read sites and all
  citation requests. Locus, payload, and cause citations observe exact targets;
  their target artifacts are not automatically read as generation syntax.
  Only predecessor citations continue that reader. No certificate chooses the
  demanded slots. Restriction preserves each recovered core and derives the
  same dependency boundary when the restricted package is read again.
\<close>

section \<open>The cause citation retains its actual target use\<close>

definition generation_cause_location ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u \<Rightarrow> local_address \<Rightarrow> bool" where
  "generation_cause_location E u r v a \<longleftrightarrow>
    environment_formed E \<and>
    (\<exists>R lr M payr cr. artifact_at E u R \<and>
      generation_syntax_at R r lr M payr cr \<and> located_at E u cr v a)"

lemma generation_cause_location_unique:
  assumes first: "generation_cause_location E u r v a"
    and second: "generation_cause_location E u r w b"
  shows "v=w \<and> a=b"
proof -
  obtain R lr M payr cr where left: "environment_formed E" "artifact_at E u R"
    "generation_syntax_at R r lr M payr cr" "located_at E u cr v a"
    using first unfolding generation_cause_location_def by blast
  obtain S ls N pays cs where right: "artifact_at E u S"
    "generation_syntax_at S r ls N pays cs" "located_at E u cs w b"
    using second unfolding generation_cause_location_def by blast
  have same: "R=S" by (rule environment_artifact_unique[OF left(1,2) right(1)])
  have endpoint: "cr=cs"
    using generation_syntax_unique[OF left(3)] right(2) same by blast
  show ?thesis using located_at_unique[OF left(1,4)] right(3) endpoint by blast
qed

lemma generation_cause_location_artifact:
  assumes "generation_cause_location E u r v a"
  shows "\<exists>C. artifact_at E v C \<and> anchor_formed (C,a)"
  using assms unfolding generation_cause_location_def
  by (meson located_at_has_artifact)

lemma generation_cause_location_target:
  assumes gen: "generation_at E u r G"
    and site: "generation_cause_location E u r v a"
    and art: "artifact_at E v C"
  shows "generation_cause G=Occurrence_Anchor (C,a)"
proof -
  obtain l M p c g where fields: "generation_fields_at E u r l M p c"
    and core: "G=Generation l (Abs_fset (g ` rel_dom M)) p c"
    using gen by (cases rule: generation_at.cases) blast
  obtain R lr payr cr where left: "artifact_at E u R"
    "generation_syntax_at R r lr M payr cr" "anchored_at E u cr c"
    using generation_fields_syntax[OF fields] by blast
  obtain S ls N pays cs where right: "environment_formed E" "artifact_at E u S"
    "generation_syntax_at S r ls N pays cs" "located_at E u cs v a"
    using site unfolding generation_cause_location_def by blast
  have same: "R=S" by (rule environment_artifact_unique[OF right(1) left(1) right(2)])
  have endpoint: "cr=cs"
    using generation_syntax_unique[OF left(2)] right(3) same by blast
  have target: "anchored_at E u cr (Occurrence_Anchor (C,a))"
    using located_at_target[OF right(1,4) art] endpoint by simp
  have cause: "c=Occurrence_Anchor (C,a)"
    by (rule anchored_at_unique[OF right(1) left(3) target])
  show ?thesis using core cause by simp
qed

lemma generation_cause_location_complete:
  assumes gen: "generation_at E u r G"
    and cause: "generation_cause G=Occurrence_Anchor (C,a)"
  shows "\<exists>v. generation_cause_location E u r v a \<and> artifact_at E v C"
proof -
  obtain l M p c g where fields: "generation_fields_at E u r l M p c"
    and core: "G=Generation l (Abs_fset (g ` rel_dom M)) p c"
    using gen by (cases rule: generation_at.cases) blast
  obtain R lr payr cr where syntax_fields: "artifact_at E u R"
    "generation_syntax_at R r lr M payr cr" "anchored_at E u cr c"
    using generation_fields_syntax[OF fields] by blast
  have anchored: "anchored_at E u cr (Occurrence_Anchor (C,a))"
    using syntax_fields(3) cause core by simp
  obtain v where loc: "located_at E u cr v a" and art: "artifact_at E v C"
    using anchored_occurrence_location[OF anchored] by blast
  have ef: "environment_formed E" by (rule generation_at_environment_formed[OF gen])
  have selected: "generation_cause_location E u r v a"
    using ef syntax_fields(1,2) loc unfolding generation_cause_location_def by blast
  show ?thesis using selected art by blast
qed


lemma whole_cause_has_no_location:
  assumes gen: "generation_at E u r G"
    and whole: "generation_cause G=Whole_Artifact R"
  shows "\<not>generation_cause_location E u r v a"
proof
  assume site: "generation_cause_location E u r v a"
  obtain C where art: "artifact_at E v C"
    using generation_cause_location_artifact[OF site] by blast
  have "generation_cause G=Occurrence_Anchor (C,a)"
    by (rule generation_cause_location_target[OF gen site art])
  then show False using whole by simp
qed

lemma generation_cause_location_locality:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and agree: "environment_agrees_on E F U"
    and closed: "environment_edge_closed E U" and member: "u\<in>U"
  shows "generation_cause_location E u r v a = generation_cause_location F u r v a"
proof -
  have arts: "\<forall>R. artifact_at E u R = artifact_at F u R"
    using agree member by (simp add: environment_agrees_on_def)
  show ?thesis
    by (simp only: generation_cause_location_def ef ff arts
      located_at_environment_locality[OF agree closed member])
qed


end
