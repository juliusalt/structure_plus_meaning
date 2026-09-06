theory RRA_Generation
  imports RRA_Structural_Syntax "HOL-Library.FSet"
begin

section \<open>Finite exact generation cores\<close>

datatype generation_core =
  Generation
    (generation_locus: exact_target)
    (generation_predecessors: "generation_core fset")
    (generation_payload: exact_target)
    (generation_cause: exact_target)

inductive generation_formed :: "generation_core \<Rightarrow> bool" where
  formed:
    "target_formed l \<Longrightarrow> target_formed p \<Longrightarrow> target_formed c \<Longrightarrow>
     (\<forall>H\<in>fset P. generation_formed H) \<Longrightarrow>
     generation_formed (Generation l P p c)"

lemma generation_identity:
  "G = H \<longleftrightarrow>
    generation_locus G = generation_locus H \<and>
    generation_predecessors G = generation_predecessors H \<and>
    generation_payload G = generation_payload H \<and>
    generation_cause G = generation_cause H"
  by (cases G; cases H) auto

lemma generation_formed_fields:
  assumes "generation_formed G"
  shows "target_formed (generation_locus G) \<and>
    target_formed (generation_payload G) \<and>
    target_formed (generation_cause G) \<and>
    (\<forall>H\<in>fset (generation_predecessors G). generation_formed H)"
  using assms by (cases rule: generation_formed.cases) auto

definition predecessor_edges :: "(generation_core \<times> generation_core) set" where
  "predecessor_edges = {(H,G). H \<in> fset (generation_predecessors G)}"

lemma predecessor_size_decreases:
  assumes "(H,G) \<in> predecessor_edges"
  shows "size H < size G"
proof (cases G)
  case (Generation l P p c)
  have member: "H \<in> fset P" using assms Generation by (simp add: predecessor_edges_def)
  have bound: "Suc (size H) \<le> (\<Sum>K\<in>fset P. Suc (size K))"
    by (rule member_le_sum[OF member]) simp_all
  show ?thesis using bound by (simp add: Generation)
qed

lemma predecessor_ancestry_decreases:
  assumes "(H,G) \<in> predecessor_edges\<^sup>+"
  shows "size H < size G"
  using assms
  by (induction rule: trancl_induct)
     (auto dest: predecessor_size_decreases intro: less_trans)

lemma predecessor_acyclic:
  "acyclic_edges predecessor_edges"
  using predecessor_ancestry_decreases
  by (auto simp: acyclic_edges_def)

lemma predecessor_well_founded:
  "wf predecessor_edges"
proof -
  have sub: "predecessor_edges \<subseteq> measure size"
    using predecessor_size_decreases by auto
  show ?thesis by (rule wf_subset[OF wf_measure sub])
qed

lemma base_core_exists:
  "\<exists>G. generation_formed G \<and> generation_predecessors G = {||}"
proof -
  let ?T = "Whole_Artifact empty_artifact"
  have formed: "generation_formed (Generation ?T {||} ?T ?T)"
    by (rule generation_formed.formed) auto
  show ?thesis using formed by force
qed

text \<open>
  These are recovered values, not a second stored graph. Direct predecessor
  membership is an extensional finite relation. Repeating the same direct edge
  would add no historical fact. Evidence, publication, and authority do not
  occur among these fields. The cause field records an exact target; the
  formation relation does not validate the account found there.
\<close>

section \<open>Recovering the four fields from an artifact use\<close>

definition generation_fields_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
   exact_target \<Rightarrow> (local_address \<times> local_address) set \<Rightarrow>
   exact_target \<Rightarrow> exact_target \<Rightarrow> bool" where
  "generation_fields_at E u root l M p c \<longleftrightarrow>
    environment_formed E \<and>
    (\<exists>R ps lr pr payr cr. artifact_at E u R \<and>
      record_at R root ps [lr,pr,payr,cr] \<and> family_at R pr M \<and>
      anchored_at E u lr l \<and> anchored_at E u payr p \<and> anchored_at E u cr c)"

lemma generation_fields_atI:
  assumes "environment_formed E" "artifact_at E u R"
    "record_at R root ps [lr,pr,payr,cr]" "family_at R pr M"
    "anchored_at E u lr l" "anchored_at E u payr p" "anchored_at E u cr c"
  shows "generation_fields_at E u root l M p c"
  using assms unfolding generation_fields_at_def by blast

lemma generation_fields_unique:
  assumes first: "generation_fields_at E u root l M p c"
    and second: "generation_fields_at E u root l' M' p' c'"
  shows "l = l' \<and> M = M' \<and> p = p' \<and> c = c'"
proof -
  obtain R ps lr pr payr cr where a: "environment_formed E" "artifact_at E u R"
    "record_at R root ps [lr,pr,payr,cr]" "family_at R pr M"
    "anchored_at E u lr l" "anchored_at E u payr p" "anchored_at E u cr c"
    using first unfolding generation_fields_at_def by blast
  obtain S qs lr' pr' payr' cr' where b: "artifact_at E u S"
    "record_at S root qs [lr',pr',payr',cr']" "family_at S pr' M'"
    "anchored_at E u lr' l'" "anchored_at E u payr' p'" "anchored_at E u cr' c'"
    using second unfolding generation_fields_at_def by blast
  have same: "R = S" by (rule environment_artifact_unique[OF a(1,2) b(1)])
  have endpoints: "lr = lr' \<and> pr = pr' \<and> payr = payr' \<and> cr = cr'"
    using record_at_unique[OF a(3)] b(2) same by auto
  have maps: "M = M'" using family_at_unique[OF a(4)] b(3) same endpoints by blast
  have loc: "l = l'" using anchored_at_unique[OF a(1,5)] b(4) endpoints by blast
  have payload: "p = p'" using anchored_at_unique[OF a(1,6)] b(5) endpoints by blast
  have cause: "c = c'" using anchored_at_unique[OF a(1,7)] b(6) endpoints by blast
  show ?thesis using maps loc payload cause by blast
qed

lemma generation_fields_formed:
  assumes "generation_fields_at E u root l M p c"
  shows "environment_formed E \<and> finite M \<and>
    target_formed l \<and> target_formed p \<and> target_formed c"
  using assms unfolding generation_fields_at_def
  by (meson anchored_at_target_formed family_socket_graph_finite)

lemma generation_fields_locality:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and agree: "environment_agrees_on E F U"
    and closed: "environment_edge_closed E U" and member: "u \<in> U"
  shows "generation_fields_at E u r l M p c = generation_fields_at F u r l M p c"
proof -
  have arts: "\<forall>R. artifact_at E u R = artifact_at F u R"
    using agree member by (simp add: environment_agrees_on_def)
  have targets: "\<forall>a t. anchored_at E u a t = anchored_at F u a t"
    using anchored_at_environment_locality[OF agree closed member] by blast
  show ?thesis by (simp only: generation_fields_at_def ef ff arts targets)
qed

section \<open>Predecessors resolve recursively within their cited use\<close>

inductive generation_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow> bool"
  for E where
  generation:
    "generation_fields_at E u root l M p c \<Longrightarrow>
     inj_on g (rel_dom M) \<Longrightarrow>
     (\<forall>s d. (s,d) \<in> M \<longrightarrow>
       (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))) \<Longrightarrow>
     generation_at E u root (Generation l (Abs_fset (g ` rel_dom M)) p c)"

lemma generation_at_environment_formed:
  assumes "generation_at E u r G"
  shows "environment_formed E"
  using assms by (cases rule: generation_at.cases)
    (auto dest: generation_fields_formed)

lemma generation_base_at:
  assumes fields: "generation_fields_at E u r l {} p c"
  shows "generation_at E u r (Generation l {||} p c)"
proof -
  let ?g = "\<lambda>_ :: local_address. Generation l {||} p c"
  have raw: "generation_at E u r
      (Generation l (Abs_fset (?g ` rel_dom ({} :: (local_address \<times> local_address) set))) p c)"
    by (rule generation_at.generation[where g="?g", OF fields]) (auto simp: rel_dom_def)
  have empty: "Abs_fset {} = ({||} :: generation_core fset)"
    by (rule fset_inject[THEN iffD1]) (simp add: Abs_fset_inverse)
  show ?thesis using raw empty by (simp add: rel_dom_def)
qed

lemma generation_at_unique:
  assumes first: "generation_at E u r G" and second: "generation_at E u r H"
  shows "G = H"
  using first second
proof (induction arbitrary: H rule: generation_at.induct)
  case (generation u root l M p c g)
  obtain l' M' p' c' h where other:
    "generation_fields_at E u root l' M' p' c'"
    "\<forall>s d. (s,d) \<in> M' \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (h s))"
    "H = Generation l' (Abs_fset (h ` rel_dom M')) p' c'"
    using generation.prems by (cases rule: generation_at.cases) blast
  have same: "l = l' \<and> M = M' \<and> p = p' \<and> c = c'"
    by (rule generation_fields_unique[OF generation.hyps(1) other(1)])
  have formed: "environment_formed E"
    using generation_fields_formed[OF generation.hyps(1)] by blast
  have pointwise: "\<And>s. s \<in> rel_dom M \<Longrightarrow> g s = h s"
  proof -
    fix s assume member: "s \<in> rel_dom M"
    obtain d where edge: "(s,d) \<in> M" using member by (auto simp: rel_dom_def)
    obtain v a where loc: "located_at E u d v a"
      and ih: "\<And>K. generation_at E v a K \<Longrightarrow> g s = K"
      using generation.IH edge by blast
    obtain w b where loc': "located_at E u d w b" and gen': "generation_at E w b (h s)"
      using other(2) same edge by blast
    have location: "v = w \<and> a = b" by (rule located_at_unique[OF formed loc loc'])
    show "g s = h s" using ih gen' location by blast
  qed
  have preds: "g ` rel_dom M = h ` rel_dom M'"
    using pointwise same by auto
  show ?case using same preds other(3) by simp
qed

lemma generation_at_formed:
  assumes "generation_at E u r G"
  shows "generation_formed G"
  using assms
proof (induction rule: generation_at.induct)
  case (generation u root l M p c g)
  have fields: "finite M \<and> target_formed l \<and> target_formed p \<and> target_formed c"
    using generation_fields_formed[OF generation.hyps(1)] by blast
  have finite: "finite (g ` rel_dom M)"
    using finite_rel_dom fields by blast
  have projection: "fset (Abs_fset (g ` rel_dom M)) = g ` rel_dom M"
    by (rule Abs_fset_inverse) (use finite in simp)
  have predecessors: "\<forall>H\<in>g ` rel_dom M. generation_formed H"
    using generation.IH unfolding rel_dom_def by blast
  show ?case by (rule generation_formed.formed)
    (use fields predecessors projection in auto)
qed

lemma generation_at_has_anchor:
  assumes "generation_at E u r G"
  shows "\<exists>R. artifact_at E u R \<and> anchor_formed (R,r)"
proof -
  obtain l M p c where fields: "generation_fields_at E u r l M p c"
    using assms by (cases rule: generation_at.cases) blast
  obtain R ps xs where formed: "environment_formed E" and art: "artifact_at E u R"
    and rec: "record_at R r ps xs"
    using fields unfolding generation_fields_at_def by blast
  have exact: "exact_formed R" using formed art by (auto simp: environment_formed_def)
  have root: "r \<in> rra_carrier (object_structure R)"
    using rec by (simp add: record_at_def)
  show ?thesis using art exact root unfolding anchor_formed_def by auto
qed

lemma generation_predecessor_resolves:
  assumes source: "generation_at E u r G"
    and member: "H \<in> fset (generation_predecessors G)"
  shows "\<exists>l M p c s d v a. generation_fields_at E u r l M p c \<and>
    (s,d) \<in> M \<and> located_at E u d v a \<and> generation_at E v a H"
proof -
  obtain l M p c g where fields: "generation_fields_at E u r l M p c"
    and refs: "\<forall>s d. (s,d) \<in> M \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
    and core: "G = Generation l (Abs_fset (g ` rel_dom M)) p c"
    using source by (cases rule: generation_at.cases) blast
  have finite: "finite (g ` rel_dom M)"
    using generation_fields_formed[OF fields] finite_rel_dom by blast
  have projection: "fset (Abs_fset (g ` rel_dom M)) = g ` rel_dom M"
    by (rule Abs_fset_inverse) (use finite in simp)
  obtain s d where edge: "(s,d) \<in> M" and target: "H = g s"
    using member core projection by (auto simp: rel_dom_def)
  obtain v a where loc: "located_at E u d v a" and gen: "generation_at E v a H"
    using refs edge target by blast
  show ?thesis using fields edge loc gen by blast
qed

lemma generation_predecessor_is_formed:
  assumes "generation_at E u r G" "H \<in> fset (generation_predecessors G)"
  shows "generation_formed H"
  using generation_at_formed[OF assms(1)] generation_formed_fields assms(2) by blast

lemma generation_at_environment_transfer:
  assumes source: "generation_at E u r G" and target: "environment_formed F"
    and agree: "environment_agrees_on E F U"
    and closed: "environment_edge_closed E U" and member: "u \<in> U"
  shows "generation_at F u r G"
  using source member
proof (induction rule: generation_at.induct)
  case (generation u root l M p c g)
  have ef: "environment_formed E"
    using generation_fields_formed[OF generation.hyps(1)] by blast
  have fields: "generation_fields_at F u root l M p c"
    using generation.hyps(1)
      generation_fields_locality[OF ef target agree closed generation.prems] by blast
  have refs: "\<forall>s d. (s,d) \<in> M \<longrightarrow>
    (\<exists>v a. located_at F u d v a \<and> generation_at F v a (g s))"
  proof (intro allI impI)
    fix s d assume edge: "(s,d) \<in> M"
    obtain v a where loc: "located_at E u d v a"
      and ih: "v \<in> U \<Longrightarrow> generation_at F v a (g s)"
      using generation.IH edge by blast
    have inside: "v \<in> U"
      by (rule located_at_stays_in_boundary[OF closed generation.prems loc])
    have gen: "generation_at F v a (g s)" by (rule ih[OF inside])
    have relocated: "located_at F u d v a"
      using loc located_at_environment_locality[OF agree closed generation.prems] by blast
    show "\<exists>v a. located_at F u d v a \<and> generation_at F v a (g s)"
      using relocated gen by blast
  qed
  show ?case by (rule generation_at.generation[OF fields generation.hyps(2) refs])
qed

lemma generation_at_environment_locality:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and agree: "environment_agrees_on E F U"
    and closed: "environment_edge_closed E U" and member: "u \<in> U"
  shows "generation_at E u r G = generation_at F u r G"
proof
  assume source: "generation_at E u r G"
  show "generation_at F u r G"
    by (rule generation_at_environment_transfer[OF source ff agree closed member])
next
  assume source: "generation_at F u r G"
  have reverse: "environment_agrees_on F E U"
    using agree by (simp add: environment_agreement_symmetric)
  have fclosed: "environment_edge_closed F U"
    by (rule environment_agreement_preserves_closure[OF agree closed])
  show "generation_at E u r G"
    by (rule generation_at_environment_transfer[OF source ef reverse fclosed member])
qed

text \<open>
  The recovered core is independent of the artifact containing its presentation
  except through the targets that the presentation actually reads. In
  particular, a local whole-artifact citation observes its complete container.
  Replacing such a target can change the core. Changing selecting artifacts or
  bindings outside the declared dependency boundary cannot do so.
\<close>

section \<open>A closed structural base presentation\<close>

definition base_generation_artifact :: exact_artifact where
  "base_generation_artifact =
    \<lparr>object_structure =
      \<lparr>rra_carrier = {[],[1],[2],[3],[4],[7],[8],[9]},
        rra_incidence = {([],[1],[7]),([],[2],[8]),([],[3],[7]),([],[4],[7]),
          ([1],[1],[2]),([2],[2],[3]),([3],[3],[4]),([7],[9],[9])}\<rparr>,
      object_data = empty_basis\<rparr>"

lemma base_generation_artifact_formed:
  "exact_formed base_generation_artifact"
  by (auto simp: base_generation_artifact_def exact_formed_def object_formed_def
      rra_formed_def octets_formed_def)

lemma base_generation_record:
  "record_at base_generation_artifact [] [[1],[2],[3],[4]] [[7],[8],[7],[7]]"
proof -
  let ?S = "object_structure base_generation_artifact"
  have last: "record_path ?S [] [4] [[4]] [[7]]"
    by (rule record_path.path_last)
       (auto simp: base_generation_artifact_def headed_incidence_def field_endpoint_def)
  have third: "record_path ?S [] [3] [[3],[4]] [[7],[7]]"
    by (rule record_path.path_slot[OF _ _ _ last])
       (auto simp: base_generation_artifact_def headed_incidence_def field_endpoint_def)
  have second: "record_path ?S [] [2] [[2],[3],[4]] [[8],[7],[7]]"
    by (rule record_path.path_slot[OF _ _ _ third])
       (auto simp: base_generation_artifact_def headed_incidence_def field_endpoint_def)
  have first: "record_path ?S [] [1] [[1],[2],[3],[4]] [[7],[8],[7],[7]]"
    by (rule record_path.path_slot[OF _ _ _ second])
       (auto simp: base_generation_artifact_def headed_incidence_def field_endpoint_def)
  have obj: "object_formed base_generation_artifact"
    using base_generation_artifact_formed by (simp add: exact_formed_def)
  show ?thesis using obj first
    by (auto simp: record_at_def raw_record_at_def base_generation_artifact_def headed_incidence_def)
qed

lemma base_generation_family:
  "family_at base_generation_artifact [8] {}"
proof -
  have obj: "object_formed base_generation_artifact"
    using base_generation_artifact_formed by (simp add: exact_formed_def)
  show ?thesis using obj
    by (auto simp: family_at_def base_generation_artifact_def headed_incidence_def
      single_valued_def rel_dom_def)
qed

lemma base_generation_citation:
  "citation_at base_generation_artifact [7] (External_Whole [9]) {[7]}"
proof -
  have raw: "raw_citation_at base_generation_artifact [7] (External_Whole [9]) {[7]}"
    by (rule raw_citation_at.external_whole)
       (auto simp: base_generation_artifact_def headed_incidence_def)
  show ?thesis using base_generation_artifact_formed raw
    by (simp add: citation_at_def base_generation_artifact_def)
qed

lemma closed_base_generation:
  assumes target: "exact_formed R"
  defines "E \<equiv> one_binding_environment base_generation_artifact [9] R"
  shows "environment_closed E {False} {(False,[9])}"
    and "artifact_at E False base_generation_artifact"
    and "generation_at E False [] (Generation (Whole_Artifact R) {||} (Whole_Artifact R) (Whole_Artifact R))"
proof -
  have closed: "environment_closed E {False} {(False,[9])}"
    unfolding E_def by (rule one_binding_environment_closed[OF base_generation_artifact_formed target])
      (simp add: base_generation_artifact_def)
  have ef: "environment_formed E" using closed by (simp add: environment_closed_def)
  have art: "artifact_at E False base_generation_artifact"
    by (simp add: E_def one_binding_environment_def artifact_at_def)
  have interpreted: "interpret_citation E False (External_Whole [9]) (Whole_Artifact R)"
    using target by (auto simp: E_def one_binding_environment_def artifact_at_def binds_slot_def)
  have anchored: "anchored_at E False [7] (Whole_Artifact R)"
    by (rule anchored_atI[OF art base_generation_citation interpreted])
  have fields: "generation_fields_at E False [] (Whole_Artifact R) {} (Whole_Artifact R) (Whole_Artifact R)"
    by (rule generation_fields_atI[OF ef art base_generation_record base_generation_family
        anchored anchored anchored])
  show "environment_closed E {False} {(False,[9])}" by (rule closed)
  show "artifact_at E False base_generation_artifact" by (rule art)
  show "generation_at E False [] (Generation (Whole_Artifact R) {||} (Whole_Artifact R) (Whole_Artifact R))"
    by (rule generation_base_at[OF fields])
qed

lemma same_presentation_different_generation_cores:
  "\<exists>E F :: bool artifact_environment. \<exists>R G H.
    environment_closed E {False} {(False,[9])} \<and>
    environment_closed F {False} {(False,[9])} \<and>
    artifact_at E False R \<and> artifact_at F False R \<and>
    generation_at E False [] G \<and> generation_at F False [] H \<and> G \<noteq> H"
proof -
  let ?E = "one_binding_environment base_generation_artifact [9] empty_artifact"
  let ?F = "one_binding_environment base_generation_artifact [9] base_generation_artifact"
  let ?A = "Whole_Artifact empty_artifact"
  let ?B = "Whole_Artifact base_generation_artifact"
  have left: "environment_closed ?E {False} {(False,[9])}"
    "artifact_at ?E False base_generation_artifact"
    "generation_at ?E False [] (Generation ?A {||} ?A ?A)"
    using closed_base_generation[OF empty_artifact_formed] by auto
  have right: "environment_closed ?F {False} {(False,[9])}"
    "artifact_at ?F False base_generation_artifact"
    "generation_at ?F False [] (Generation ?B {||} ?B ?B)"
    using closed_base_generation[OF base_generation_artifact_formed] by auto
  have different: "Generation ?A {||} ?A ?A \<noteq> Generation ?B {||} ?B ?B"
    by (simp add: empty_artifact_def base_generation_artifact_def exact_identity_iff rra_identity)
  show ?thesis
    by (rule exI[of _ ?E], rule exI[of _ ?F], rule exI[of _ base_generation_artifact],
        rule exI[of _ "Generation ?A {||} ?A ?A"], rule exI[of _ "Generation ?B {||} ?B ?B"])
       (use left right different in blast)
qed

end
