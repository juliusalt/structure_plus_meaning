theory RRA_Publication_Construction
  imports RRA_Collection_Selections RRA_Generation_Construction RRA_Publication_Dependencies
begin

section \<open>Publishing complete selections with the supplied generation uses\<close>

theorem publication_record_extension:
  fixes E :: "local_address option artifact_environment"
  assumes ef: "environment_formed E" and pf: "publication_formed P"
    and gs: "distinct gs" "set gs=fset (publication_snapshot P)"
    and ds: "distinct ds" "set ds=fset (publication_dependencies P)"
    and es: "distinct es" "set es=fset (publication_evidence P)"
    and generations: "\<And>i. i<length gs \<Longrightarrow> generation_at E (v i) (a i) (gs!i)"
  shows "\<exists>H u. environment_formed H \<and> environment_included E H \<and> publication_at H u [] P"
proof -
  have anchors: "\<forall>i\<in>{..<length gs}. \<exists>R. artifact_at E (v i) R \<and> anchor_formed (R,a i)"
    using generation_at_has_anchor[OF generations] by auto
  obtain R where chosen: "\<forall>i\<in>{..<length gs}. artifact_at E (v i) (R i) \<and> anchor_formed (R i,a i)"
    using bchoice[OF anchors] by blast
  let ?T="set ds\<union>set es"
  have targets: "\<forall>t\<in>?T. target_formed t" using pf ds(2) es(2) by (auto simp: publication_formed_def)
  have tf: "\<forall>S\<in>image target_artifact ?T. exact_formed S"
    using targets by (auto intro: target_formed_artifact)
  obtain F :: "local_address option artifact_environment" where ff: "environment_formed F"
    and into_f: "environment_included E F"
    and literals: "\<forall>S\<in>image target_artifact ?T. \<exists>u. artifact_at F u S"
    using finite_artifact_extension[OF _ tf ef] by auto
  have target_sites: "\<forall>t\<in>?T. \<exists>u. artifact_at F u (target_artifact t)" using literals by blast
  obtain w where located_targets: "\<forall>t\<in>?T. artifact_at F (w t) (target_artifact t)"
    using bchoice[OF target_sites] by blast
  let ?as="map (\<lambda>i. Occurrence_Anchor (R i,a i)) [0..<length gs]"
  let ?xss="[?as,ds,es]"
  let ?site="\<lambda>j i. if j=0 then v i else w (?xss!j!i)"
  have af: "\<forall>t\<in>set ?as. target_formed t" using chosen by auto
  interpret frame: collection_record_frame ?xss
    by (rule collection_record_frame.intro) (use af targets in auto)
  have artifacts: "\<And>j i. j<length ?xss \<Longrightarrow> i<length (?xss!j) \<Longrightarrow>
      artifact_at F (?site j i) (target_artifact (?xss!j!i))"
  proof -
    fix j i assume field: "j<length ?xss" and index: "i<length (?xss!j)"
    show "artifact_at F (?site j i) (target_artifact (?xss!j!i))"
    proof (cases "j=0")
      case True
      have bound: "i<length gs" using index True by simp
      have old: "artifact_at E (v i) (R i)" using chosen bound by simp
      have kept: "artifact_at F (v i) (R i)" by (rule included_artifact[OF into_f old])
      show ?thesis using kept bound True by simp
    next
      case False
      have small: "j<3" using field by simp
      have cases: "j=1 \<or> j=2" using small False by arith
      have member: "?xss!j!i\<in>?T" using index cases by auto
      show ?thesis using located_targets[rule_format, OF member] False by simp
    qed
  qed
  obtain H u where hf: "environment_formed H" and into_h: "environment_included F H"
    and source: "artifact_at H u (collection_record_syntax ?xss)"
    and refs: "\<forall>j<length ?xss. \<forall>i<length (?xss!j).
      anchored_at H u (collection_field_node j i) (?xss!j!i) \<and>
      (\<forall>S b. ?xss!j!i=Occurrence_Anchor (S,b) \<longrightarrow>
        located_at H u (collection_field_node j i) (?site j i) b)"
    using frame.reference_extension[OF ff artifacts] by blast
  have included: "environment_included E H" by (rule environment_included_trans[OF into_f into_h])
  have generation_refs: "\<And>i. i<length gs \<Longrightarrow>
      located_at H u (collection_field_node 0 i) (v i) (a i) \<and> generation_at H (v i) (a i) (gs!i)"
  proof -
    fix i assume index: "i<length gs"
    have row: "\<forall>S b. ?xss!0!i=Occurrence_Anchor (S,b) \<longrightarrow>
      located_at H u (collection_field_node 0 i) (?site 0 i) b"
      using refs[rule_format, of 0 i] index by auto
    have loc: "located_at H u (collection_field_node 0 i) (v i) (a i)" using row index by simp
    have gen: "generation_at H (v i) (a i) (gs!i)"
      by (rule generation_at_included[OF generations[OF index] included hf])
    show "located_at H u (collection_field_node 0 i) (v i) (a i) \<and> generation_at H (v i) (a i) (gs!i)"
      using loc gen by blast
  qed
  have selection: "selection_at H u (syntax_branch 0 []) (publication_snapshot P)"
    by (rule frame.generation_selection[OF hf source _ gs(1) _ gs(2) generation_refs]) simp_all
  have snapshot: "snapshot_at H u (syntax_branch 0 []) (publication_snapshot P)"
    using selection pf by (simp add: snapshot_at_def publication_formed_def)
  have dependencies: "target_selection_at H u (syntax_branch 1 []) (fset (publication_dependencies P))"
  proof -
    have anchors: "\<And>i. i<length (?xss!1) \<Longrightarrow>
      anchored_at H u (collection_field_node 1 i) (?xss!1!i)"
      using refs[rule_format, of 1] by auto
    have selected: "target_selection_at H u (syntax_branch 1 []) (set (?xss!1))"
      by (rule frame.target_selection[OF hf source _ _ anchors]) (use ds(1) in simp_all)
    show ?thesis using selected ds(2) by simp
  qed
  have evidence: "target_selection_at H u (syntax_branch 2 []) (fset (publication_evidence P))"
  proof -
    have anchors: "\<And>i. i<length (?xss!2) \<Longrightarrow>
      anchored_at H u (collection_field_node 2 i) (?xss!2!i)"
      using refs[rule_format, of 2] by auto
    have selected: "target_selection_at H u (syntax_branch 2 []) (set (?xss!2))"
      by (rule frame.target_selection[OF hf source _ _ anchors]) (use es(1) in simp_all)
    show ?thesis using selected es(2) by simp
  qed
  have record_read: "record_at (collection_record_syntax ?xss) [] (family_ports 3)
      [syntax_branch 0 [],syntax_branch 1 [],syntax_branch 2 []]"
    using frame.fields by (simp add: eval_nat_numeral)
  have pub: "publication_at H u [] P"
    using hf source record_read snapshot dependencies evidence unfolding publication_at_def by blast
  show ?thesis using hf included pub by blast
qed

section \<open>Every formed publication view has an actual closed presentation\<close>

theorem publication_presentation_total:
  assumes formed: "publication_formed P"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>u. publication_at E u [] P"
proof -
  have cores: "\<forall>G\<in>fset (publication_snapshot P). generation_formed G"
    using formed by (simp add: publication_formed_def snapshot_formed_def selection_formed_def)
  have each: "\<forall>G\<in>fset (publication_snapshot P).
      \<exists>E :: local_address option artifact_environment. \<exists>u r. generation_at E u r G"
  proof (intro ballI)
    fix G assume member: "G\<in>fset (publication_snapshot P)"
    have gf: "generation_formed G" using cores member by blast
    obtain E :: "local_address option artifact_environment" and u where gen: "generation_at E u [] G"
      using generation_presentation_total[OF gf] by blast
    show "\<exists>E :: local_address option artifact_environment. \<exists>u r. generation_at E u r G"
      using gen by blast
  qed
  obtain E :: "local_address option artifact_environment" where ef: "environment_formed E"
    and readings: "\<forall>G\<in>fset (publication_snapshot P). \<exists>u r. generation_at E u r G"
    using finite_generation_presentations_together[OF finite_fset each] by blast
  obtain gs where gs: "distinct gs" "set gs=fset (publication_snapshot P)"
    using finite_distinct_list[OF finite_fset[of "publication_snapshot P"]] by blast
  obtain ds where ds: "distinct ds" "set ds=fset (publication_dependencies P)"
    using finite_distinct_list[OF finite_fset[of "publication_dependencies P"]] by blast
  obtain es where es: "distinct es" "set es=fset (publication_evidence P)"
    using finite_distinct_list[OF finite_fset[of "publication_evidence P"]] by blast
  have sites: "\<forall>i\<in>{..<length gs}. \<exists>s. generation_at E (fst s) (snd s) (gs!i)"
  proof (intro ballI)
    fix i assume index: "i\<in>{..<length gs}"
    have bound: "i<length gs" using index by simp
    have member: "gs!i\<in>fset (publication_snapshot P)" using nth_mem[OF bound] gs(2) by simp
    obtain u r where gen: "generation_at E u r (gs!i)" using readings member by blast
    show "\<exists>s. generation_at E (fst s) (snd s) (gs!i)"
      by (rule exI[of _ "(u,r)"]) (use gen in simp)
  qed
  obtain s where chosen: "\<forall>i\<in>{..<length gs}. generation_at E (fst (s i)) (snd (s i)) (gs!i)"
    using bchoice[OF sites] by blast
  have refs: "\<And>i. i<length gs \<Longrightarrow> generation_at E (fst (s i)) (snd (s i)) (gs!i)"
    using chosen by simp
  show ?thesis using publication_record_extension[OF ef formed gs ds es refs] by blast
qed

corollary closed_publication_presentation_total:
  assumes formed: "publication_formed P"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>u.
    publication_environment_closed E u [] P \<and> publication_environment E u []=E"
proof -
  obtain F :: "local_address option artifact_environment" and u where pub: "publication_at F u [] P"
    using publication_presentation_total[OF formed] by blast
  let ?E="publication_environment F u []"
  have closed: "publication_environment_closed ?E u [] P" by (rule publication_closed_restriction[OF pub])
  have fixed: "publication_environment ?E u []=?E" by (rule publication_environment_idempotent[OF pub])
  show ?thesis using closed fixed by blast
qed

lemma singleton_publication_exists:
  assumes formed: "generation_formed G"
  shows "\<exists>F :: local_address option artifact_environment. \<exists>v P.
    publication_environment_closed F v [] P \<and> publication_snapshot P={|G|} \<and>
    snapshot_lookup (publication_snapshot P) (generation_locus G)=Some G"
proof -
  let ?P="\<lparr>publication_snapshot={|G|}, publication_dependencies={||}, publication_evidence={||}\<rparr>"
  have sf: "snapshot_formed {|G|}" using formed by (simp add: snapshot_formed_def selection_formed_def)
  have pf: "publication_formed ?P" using sf by (simp add: publication_formed_def)
  obtain F :: "local_address option artifact_environment" and v where pub: "publication_environment_closed F v [] ?P"
    using closed_publication_presentation_total[OF pf] by blast
  have selected: "snapshot_lookup {|G|} (generation_locus G)=Some G"
    by (rule snapshot_lookup_member[OF sf]) simp
  show ?thesis by (rule exI[of _ F], rule exI[of _ v], rule exI[of _ ?P])
    (use pub selected in simp)
qed

text \<open>
  Every formed view has a complete actual publication record. Its snapshot
  citations retain the exact uses and bindings from which each selected core
  is read; equal artifact values do not collapse different use environments.
  Dependency and evidence selections receive exact target citations and do
  not acquire semantic or evidential force.

  Distinct complete lists supply construction witnesses for the three finite
  selections. The existing readers determine their values from the resulting
  incidence, including the empty case. Restricting to the grammar-derived
  publication environment gives a closed finite scope with exactly the same
  view. No adoption or cause-validity premise is needed.
\<close>

end
