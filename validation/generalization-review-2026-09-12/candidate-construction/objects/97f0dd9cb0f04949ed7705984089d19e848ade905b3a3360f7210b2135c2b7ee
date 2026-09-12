theory RRA_Selection
  imports RRA_Generation
begin

section \<open>Selections are finite sets of exact cores\<close>

type_synonym generation_selection = "generation_core fset"
type_synonym selection_snapshot = generation_selection

lemma ffilter_empty_set [simp]: "ffilter P {||} = {||}"
  by (rule fset_inject[THEN iffD1]) auto

lemma ffilter_true [simp]: "ffilter (\<lambda>_. True) S = S"
  by (rule fset_inject[THEN iffD1]) auto

definition selection_formed :: "generation_selection \<Rightarrow> bool" where
  "selection_formed S \<longleftrightarrow> (\<forall>G\<in>fset S. generation_formed G)"

definition selection_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
   generation_selection \<Rightarrow> bool" where
  "selection_at E u root S \<longleftrightarrow>
    environment_formed E \<and>
    (\<exists>R M g. artifact_at E u R \<and> family_at R root M \<and> inj_on g (rel_dom M) \<and>
      (\<forall>s d. (s,d) \<in> M \<longrightarrow>
        (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))) \<and>
      S = Abs_fset (g ` rel_dom M))"

lemma selection_at_unique:
  assumes first: "selection_at E u root S" and second: "selection_at E u root T"
  shows "S = T"
proof -
  obtain R M g where a: "environment_formed E" "artifact_at E u R" "family_at R root M"
    "\<forall>s d. (s,d) \<in> M \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
    "S = Abs_fset (g ` rel_dom M)"
    using first unfolding selection_at_def by blast
  obtain R' M' h where b: "artifact_at E u R'" "family_at R' root M'"
    "\<forall>s d. (s,d) \<in> M' \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (h s))"
    "T = Abs_fset (h ` rel_dom M')"
    using second unfolding selection_at_def by blast
  have same: "R = R'" by (rule environment_artifact_unique[OF a(1,2) b(1)])
  have sockets: "M = M'" using family_at_unique[OF a(3)] b(2) same by blast
  have pointwise: "\<And>s. s \<in> rel_dom M \<Longrightarrow> g s = h s"
  proof -
    fix s assume "s \<in> rel_dom M"
    then obtain d where edge: "(s,d) \<in> M" by (auto simp: rel_dom_def)
    obtain v x where loc: "located_at E u d v x" and gen: "generation_at E v x (g s)"
      using a(4) edge by blast
    obtain w y where loc': "located_at E u d w y" and gen': "generation_at E w y (h s)"
      using b(3) edge sockets by blast
    have places: "v = w \<and> x = y" by (rule located_at_unique[OF a(1) loc loc'])
    show "g s = h s" using generation_at_unique[OF gen] gen' places by blast
  qed
  have images: "g ` rel_dom M = h ` rel_dom M'" using pointwise sockets by auto
  show ?thesis using a(5) b(4) images by simp
qed

lemma selection_at_formed:
  assumes "selection_at E u root S"
  shows "selection_formed S"
proof -
  obtain R M g where a: "artifact_at E u R" "family_at R root M"
    "\<forall>s d. (s,d) \<in> M \<longrightarrow>
      (\<exists>v a. located_at E u d v a \<and> generation_at E v a (g s))"
    "S = Abs_fset (g ` rel_dom M)"
    using assms unfolding selection_at_def by blast
  have finite: "finite (g ` rel_dom M)"
    using finite_rel_dom[OF family_socket_graph_finite[OF a(2)]] by simp
  have projection: "fset S = g ` rel_dom M"
    using Abs_fset_inverse[of "g ` rel_dom M"] a(4) finite by simp
  have formed: "\<forall>s\<in>rel_dom M. generation_formed (g s)"
  proof (intro ballI)
    fix s assume "s \<in> rel_dom M"
    then obtain d where edge: "(s,d) \<in> M" by (auto simp: rel_dom_def)
    obtain v x where gen: "generation_at E v x (g s)" using a(3) edge by blast
    show "generation_formed (g s)" by (rule generation_at_formed[OF gen])
  qed
  show ?thesis using formed projection by (auto simp: selection_formed_def)
qed

lemma selection_environment_locality:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and agree: "environment_agrees_on E F U"
    and closed: "environment_edge_closed E U" and member: "u \<in> U"
  shows "selection_at E u root S = selection_at F u root S"
proof -
  have arts: "\<forall>R. artifact_at E u R = artifact_at F u R"
    using agree member by (simp add: environment_agrees_on_def)
  have locations: "\<forall>d v a. located_at E u d v a = located_at F u d v a"
    using located_at_environment_locality[OF agree closed member] by blast
  have cores: "\<And>d v a G. located_at E u d v a \<Longrightarrow>
    generation_at E v a G = generation_at F v a G"
  proof -
    fix d v a G assume loc: "located_at E u d v a"
    have inside: "v \<in> U" by (rule located_at_stays_in_boundary[OF closed member loc])
    show "generation_at E v a G = generation_at F v a G"
      by (rule generation_at_environment_locality[OF ef ff agree closed inside])
  qed
  have refs: "\<forall>d v a G.
    (located_at E u d v a \<and> generation_at E v a G) =
    (located_at F u d v a \<and> generation_at F v a G)"
    using locations cores by blast
  show ?thesis by (simp only: selection_at_def ef ff arts refs)
qed

section \<open>At most one selected generation per locus\<close>

definition snapshot_loci :: "selection_snapshot \<Rightarrow> exact_target set" where
  "snapshot_loci S = generation_locus ` fset S"

definition snapshot_formed :: "selection_snapshot \<Rightarrow> bool" where
  "snapshot_formed S \<longleftrightarrow> selection_formed S \<and> inj_on generation_locus (fset S)"

definition snapshot_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
   selection_snapshot \<Rightarrow> bool" where
  "snapshot_at E u r S \<longleftrightarrow> selection_at E u r S \<and> snapshot_formed S"

lemma snapshot_at_unique:
  assumes "snapshot_at E u r S" "snapshot_at E u r T"
  shows "S = T"
  using assms unfolding snapshot_at_def by (meson selection_at_unique)

lemma snapshot_at_locality:
  assumes "environment_formed E" "environment_formed F" "environment_agrees_on E F U"
    "environment_edge_closed E U" "u \<in> U"
  shows "snapshot_at E u r S = snapshot_at F u r S"
  unfolding snapshot_at_def by (simp only: selection_environment_locality[OF assms])

definition snapshot_lookup :: "selection_snapshot \<Rightarrow> exact_target \<Rightarrow> generation_core option" where
  "snapshot_lookup S l =
    (if l \<in> snapshot_loci S then Some (THE G. G \<in> fset S \<and> generation_locus G = l) else None)"

lemma snapshot_empty_formed [simp]: "snapshot_formed {||}"
  by (simp add: snapshot_formed_def selection_formed_def)

lemma snapshot_loci_formed:
  assumes "snapshot_formed S" "l \<in> snapshot_loci S"
  shows "target_formed l"
proof -
  obtain G where member: "G \<in> fset S" and locus: "generation_locus G = l"
    using assms(2) by (auto simp: snapshot_loci_def)
  have formed: "generation_formed G"
    using assms(1) member by (auto simp: snapshot_formed_def selection_formed_def)
  show ?thesis using generation_formed_fields[OF formed] locus by simp
qed

lemma snapshot_empty_lookup [simp]: "snapshot_lookup {||} l = None"
  by (simp add: snapshot_lookup_def snapshot_loci_def)

lemma snapshot_member_unique:
  assumes "snapshot_formed S" "G \<in> fset S" "H \<in> fset S"
    "generation_locus G = generation_locus H"
  shows "G = H"
  using assms by (auto simp: snapshot_formed_def inj_on_def)

lemma snapshot_lookup_member:
  assumes formed: "snapshot_formed S" and member: "G \<in> fset S"
  shows "snapshot_lookup S (generation_locus G) = Some G"
proof -
  have unique: "(THE H. H \<in> fset S \<and> generation_locus H = generation_locus G) = G"
  proof (rule the_equality)
    show "G \<in> fset S \<and> generation_locus G = generation_locus G" using member by simp
    fix H assume other: "H \<in> fset S \<and> generation_locus H = generation_locus G"
    show "H = G" by (rule snapshot_member_unique[OF formed _ member]) (use other in auto)
  qed
  show ?thesis using member unique by (simp add: snapshot_lookup_def snapshot_loci_def)
qed

lemma snapshot_lookup_none:
  "snapshot_lookup S l = None \<longleftrightarrow> l \<notin> snapshot_loci S"
  by (simp add: snapshot_lookup_def)

lemma snapshot_lookup_some:
  assumes formed: "snapshot_formed S"
  shows "snapshot_lookup S l = Some G \<longleftrightarrow>
    G \<in> fset S \<and> generation_locus G = l"
proof
  assume selected: "snapshot_lookup S l = Some G"
  have present: "l \<in> snapshot_loci S"
    using selected by (auto simp: snapshot_lookup_def split: if_splits)
  then obtain H where member: "H \<in> fset S" and locus: "generation_locus H = l"
    by (auto simp: snapshot_loci_def)
  have lookup: "snapshot_lookup S l = Some H"
    using snapshot_lookup_member[OF formed member] locus by simp
  show "G \<in> fset S \<and> generation_locus G = l" using selected lookup member locus by simp
next
  assume "G \<in> fset S \<and> generation_locus G = l"
  then show "snapshot_lookup S l = Some G" using snapshot_lookup_member[OF formed] by blast
qed

lemma snapshot_determined_by_lookup:
  assumes sf: "snapshot_formed S" and tf: "snapshot_formed T"
    and same: "\<And>l. snapshot_lookup S l = snapshot_lookup T l"
  shows "S = T"
proof -
  have sets: "fset S = fset T"
  proof (rule set_eqI)
    fix G
    show "G \<in> fset S \<longleftrightarrow> G \<in> fset T"
      using snapshot_lookup_some[OF sf, of "generation_locus G" G]
        snapshot_lookup_some[OF tf, of "generation_locus G" G]
        same[of "generation_locus G"] by simp
  qed
  show ?thesis using sets by (simp add: fset_inject)
qed

text \<open>
  A snapshot stores selected cores once. Its locus graph and lookup are
  derived from the locus already in each core. Snapshot formation does not
  assert that its selections are current, accepted, justified, or successors
  of any other snapshot.
\<close>

section \<open>Exact finite replacement of selections\<close>

definition replace_snapshot ::
  "selection_snapshot \<Rightarrow> selection_snapshot \<Rightarrow> exact_target fset \<Rightarrow>
   selection_snapshot" where
  "replace_snapshot S W D =
    ffilter (\<lambda>G. generation_locus G \<notin> snapshot_loci W \<union> fset D) S |\<union>| W"

lemma replace_snapshot_members:
  "G \<in> fset (replace_snapshot S W D) \<longleftrightarrow>
    G \<in> fset W \<or>
    (G \<in> fset S \<and> generation_locus G \<notin> snapshot_loci W \<and> generation_locus G \<notin> fset D)"
  by (auto simp: replace_snapshot_def)

lemma replace_snapshot_formed:
  assumes "snapshot_formed S" "snapshot_formed W"
  shows "snapshot_formed (replace_snapshot S W D)"
  using assms
  by (auto simp: snapshot_formed_def selection_formed_def inj_on_def
    replace_snapshot_members snapshot_loci_def; metis imageI)

lemma replace_snapshot_loci:
  "snapshot_loci (replace_snapshot S W D) =
    snapshot_loci W \<union> (snapshot_loci S - (snapshot_loci W \<union> fset D))"
  by (auto simp: snapshot_loci_def replace_snapshot_members)

lemma replace_snapshot_lookup:
  assumes sf: "snapshot_formed S" and wf: "snapshot_formed W"
  shows "snapshot_lookup (replace_snapshot S W D) l =
    (if l \<in> snapshot_loci W then snapshot_lookup W l
     else if l \<in> fset D then None else snapshot_lookup S l)"
proof -
  have formed: "snapshot_formed (replace_snapshot S W D)"
    by (rule replace_snapshot_formed[OF sf wf])
  show ?thesis
  proof (cases "l \<in> snapshot_loci W")
    case True
    then obtain G where member: "G \<in> fset W" and locus: "generation_locus G = l"
      by (auto simp: snapshot_loci_def)
    have in_result: "G \<in> fset (replace_snapshot S W D)"
      using member by (simp add: replace_snapshot_members)
    show ?thesis
      using snapshot_lookup_member[OF formed in_result] snapshot_lookup_member[OF wf member]
        True locus by simp
  next
    case False
    show ?thesis
    proof (cases "l \<in> fset D")
      case True
      have absent: "l \<notin> snapshot_loci (replace_snapshot S W D)"
        using False True by (simp add: replace_snapshot_loci)
      show ?thesis using snapshot_lookup_none[of "replace_snapshot S W D" l]
        absent False True by simp
    next
      case untouched: False
      show ?thesis
      proof (cases "l \<in> snapshot_loci S")
        case True
        then obtain G where member: "G \<in> fset S" and locus: "generation_locus G = l"
          by (auto simp: snapshot_loci_def)
        have in_result: "G \<in> fset (replace_snapshot S W D)"
          using member locus False untouched by (simp add: replace_snapshot_members)
        show ?thesis
          using snapshot_lookup_member[OF formed in_result] snapshot_lookup_member[OF sf member]
            False untouched locus by simp
      next
        case absent: False
        have result_absent: "l \<notin> snapshot_loci (replace_snapshot S W D)"
          using False absent by (simp add: replace_snapshot_loci)
        show ?thesis
          using snapshot_lookup_none[of S l] snapshot_lookup_none[of "replace_snapshot S W D" l]
            absent result_absent False untouched by simp
      qed
    qed
  qed
qed

end
