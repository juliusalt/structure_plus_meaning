theory RRA_Generation_Construction
  imports RRA_Generation_Frames RRA_Generation_Transport RRA_Literal_Extension
begin

section \<open>Installing a generation record with references to existing uses\<close>

theorem generation_record_extension:
  fixes E :: "local_address option artifact_environment" and n :: nat
  assumes ef: "environment_formed E"
    and lf: "target_formed l" and pf: "target_formed p" and cf: "target_formed c"
    and distinct: "inj_on g {..<n}"
    and predecessors: "\<forall>i<n. generation_at E (v i) (a i) (g i)"
  shows "\<exists>H u. environment_formed H \<and> environment_included E H \<and>
    generation_at H u [] (Generation l (Abs_fset (g ` {..<n})) p c)"
proof -
  have targets: "\<forall>i\<in>{..<n}. \<exists>R. artifact_at E (v i) R \<and> anchor_formed (R,a i)"
  proof (intro ballI)
    fix i assume index: "i \<in> {..<n}"
    have gen: "generation_at E (v i) (a i) (g i)" using predecessors index by auto
    show "\<exists>R. artifact_at E (v i) R \<and> anchor_formed (R,a i)"
      by (rule generation_at_has_anchor[OF gen])
  qed
  obtain T where chosen: "\<forall>i\<in>{..<n}. artifact_at E (v i) (T i) \<and> anchor_formed (T i,a i)"
    using bchoice[OF targets] by blast
  let ?as = "map (\<lambda>i. (T i,a i)) [0..<n]"
  interpret frame: generation_frame l p c ?as
    by (rule generation_frame.intro[OF lf pf cf]) (use chosen in auto)
  let ?R = "frame.framed"
  let ?u = "fresh_use_map (environment_uses E) None (Some [])"
  let ?B = "add_artifact_use E ?u ?R"
  let ?D = "(\<lambda>i. (generation_predecessor_slot i,v i)) ` {..<n}"
  let ?F = "add_source_bindings ?B ?u ?D"
  let ?L = "{(syntax_branch 0 [4],target_artifact l),
    (syntax_branch 2 [4],target_artifact p),(syntax_branch 3 [4],target_artifact c)}"
  have fresh: "?u \<notin> environment_uses E"
    using fresh_use_map_outside[OF environment_uses_finite[OF ef], of None "[]"] by blast
  have unbound: "\<And>k w. \<not> binds_slot E ?u k w"
  proof -
    fix k w show "\<not> binds_slot E ?u k w"
    proof
      assume bound: "binds_slot E ?u k w"
      obtain S where art: "artifact_at E ?u S" using ef bound unfolding environment_formed_def by blast
      have "?u \<in> environment_uses E" using art by (auto simp: environment_uses_def rel_dom_def artifact_at_def)
      then show False using fresh by blast
    qed
  qed
  have bf: "environment_formed ?B" by (rule added_artifact_formed[OF ef frame.formed fresh])
  have source_b: "artifact_at ?B ?u ?R" by simp
  have df: "finite ?D" by simp
  have dsv: "single_valued ?D"
    using generation_predecessor_slots_injective by (auto simp: single_valued_def inj_def)
  have dslots: "rel_dom ?D \<subseteq> rra_carrier (object_structure ?R)"
    using frame.predecessor_slots_inside by (auto simp: rel_dom_def)
  have dtargets: "rel_ran ?D \<subseteq> environment_uses ?B"
  proof -
    have old: "rel_ran ?D \<subseteq> environment_uses E"
      using chosen by (auto simp: rel_ran_def environment_uses_def rel_dom_def artifact_at_def)
    show ?thesis using old included_uses[OF added_artifact_included, of E ?u ?R] by blast
  qed
  have ff: "environment_formed ?F"
    by (rule add_source_bindings_formed[OF bf source_b df dsv dslots dtargets])
       (use unbound in simp)
  have source_f: "artifact_at ?F ?u ?R" by simp
  have lfinite: "finite ?L" by simp
  have lsv: "single_valued ?L" by (auto simp: single_valued_def eval_nat_numeral)
  have lformed: "\<forall>k R. (k,R) \<in> ?L \<longrightarrow> exact_formed R"
    using target_formed_artifact[OF lf] target_formed_artifact[OF pf] target_formed_artifact[OF cf] by auto
  have lslots: "rel_dom ?L \<subseteq> rra_carrier (object_structure ?R)"
    using frame.literal_slots_inside by (auto simp: rel_dom_def)
  have separate: "\<And>i. generation_predecessor_slot i \<noteq> syntax_branch 0 [4] \<and>
    generation_predecessor_slot i \<noteq> syntax_branch 2 [4] \<and>
    generation_predecessor_slot i \<noteq> syntax_branch 3 [4]"
    using generation_predecessor_slots_separate[where j=0]
      generation_predecessor_slots_separate[where j=2]
      generation_predecessor_slots_separate[where j=3] by auto
  have lunbound: "\<And>k w. k \<in> rel_dom ?L \<Longrightarrow> \<not> binds_slot ?F ?u k w"
    using separate unbound by (auto simp: rel_dom_def)
  interpret literals: literal_extension ?F ?u ?R ?L
    by (rule literal_extension.intro[OF ff source_f lfinite lsv lformed lslots lunbound])
  let ?H = "literals.installed"
  have included: "environment_included E ?H"
    by (rule environment_included_trans[OF
        environment_included_trans[OF added_artifact_included add_source_included] literals.included])
  have source_h: "artifact_at ?H ?u ?R" by (rule literals.source)
  have lvalue: "external_slot_values ?H ?u (syntax_branch 0 [4])={target_artifact l}"
    by (rule literals.literal_singleton) simp
  have pvalue: "external_slot_values ?H ?u (syntax_branch 2 [4])={target_artifact p}"
    by (rule literals.literal_singleton) simp
  have cvalue: "external_slot_values ?H ?u (syntax_branch 3 [4])={target_artifact c}"
    by (rule literals.literal_singleton) simp
  have locus: "anchored_at ?H ?u (syntax_branch 0 []) l"
    by (rule anchored_atI[OF source_h frame.locus_citation
        literal_citation_mapped_interpretation[where f="syntax_branch 0", OF lf lvalue]])
  have payload: "anchored_at ?H ?u (syntax_branch 2 []) p"
    by (rule anchored_atI[OF source_h frame.payload_citation
        literal_citation_mapped_interpretation[where f="syntax_branch 2", OF pf pvalue]])
  have cause: "anchored_at ?H ?u (syntax_branch 3 []) c"
    by (rule anchored_atI[OF source_h frame.cause_citation
        literal_citation_mapped_interpretation[where f="syntax_branch 3", OF cf cvalue]])
  have family: "family_at ?R (syntax_branch 1 []) (generation_frame_members n)"
    using frame.predecessor_family by simp
  have fields: "generation_fields_at ?H ?u [] l (generation_frame_members n) p c"
    by (rule generation_fields_atI[OF literals.formed source_h frame.fields family locus payload cause])
  have locations: "\<And>i. i<n \<Longrightarrow>
    located_at ?H ?u (generation_predecessor_node i) (v i) (a i)"
  proof -
    fix i assume index: "i<n"
    have entry: "(generation_predecessor_slot i,v i) \<in> ?D"
      by (rule image_eqI[where x=i]) (use index in auto)
    have bound_f: "binds_slot ?F ?u (generation_predecessor_slot i) (v i)" using entry by simp
    have bound_h: "binds_slot ?H ?u (generation_predecessor_slot i) (v i)"
      by (rule included_binding[OF literals.included bound_f])
    have original: "artifact_at E (v i) (T i)" and anchor: "anchor_formed (T i,a i)"
      using chosen index by auto
    have target: "artifact_at ?H (v i) (T i)" by (rule included_artifact[OF included original])
    have loc: "citation_location ?H ?u (External (generation_predecessor_slot i) (a i)) (v i) (a i)"
      using bound_h target anchor by auto
    have at: "i<length ?as" using index by simp
    have cite: "citation_at ?R (generation_predecessor_node i)
      (External (generation_predecessor_slot i) (a i))
      (syntax_branch 1 ` (syntax_branch i ` literal_interior (Occurrence_Anchor (T i,a i))))"
      using frame.predecessor_citation[OF at] index by simp
    show "located_at ?H ?u (generation_predecessor_node i) (v i) (a i)"
      using source_h cite loc unfolding located_at_def by blast
  qed
  obtain h where hinj: "inj_on h (rel_dom (generation_frame_members n))"
    and hat: "\<forall>i<n. h (generation_predecessor_socket n i)=g i"
    and hvalues: "h ` rel_dom (generation_frame_members n)=g ` {..<n}"
    using generation_predecessor_assignment[OF distinct] by blast
  have refs: "\<forall>s d. (s,d) \<in> generation_frame_members n \<longrightarrow>
    (\<exists>w b. located_at ?H ?u d w b \<and> generation_at ?H w b (h s))"
  proof (intro allI impI)
    fix s d assume edge: "(s,d) \<in> generation_frame_members n"
    obtain i where index: "i<n" and s: "s=generation_predecessor_socket n i"
      and d: "d=generation_predecessor_node i" using edge by (auto simp: generation_frame_member)
    have old: "generation_at E (v i) (a i) (g i)" using predecessors index by blast
    have kept: "generation_at ?H (v i) (a i) (g i)"
      by (rule generation_at_included[OF old included literals.formed])
    have same: "h s=g i" using hat index s by simp
    show "\<exists>w b. located_at ?H ?u d w b \<and> generation_at ?H w b (h s)"
      by (rule exI[of _ "v i"], rule exI[of _ "a i"])
         (use locations[OF index] kept in \<open>simp only: d same; blast\<close>)
  qed
  have recovered: "generation_at ?H ?u [] (Generation l (Abs_fset (g ` {..<n})) p c)"
    using generation_at.generation[OF fields hinj refs] by (simp only: hvalues)
  show ?thesis using literals.formed included recovered by blast
qed

section \<open>Every formed finite core has an actual presentation\<close>

theorem generation_presentation_total:
  assumes "generation_formed G"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>u. generation_at E u [] G"
  using assms
proof (induction G rule: generation_core.induct)
  case (Generation l P p c)
  have parts: "target_formed l" "target_formed p" "target_formed c"
    "\<forall>H\<in>fset P. generation_formed H"
    using generation_formed_fields[OF Generation.prems] by simp_all
  have each: "\<forall>H\<in>fset P. \<exists>E :: local_address option artifact_environment.
    \<exists>u r. generation_at E u r H" using Generation.IH parts(4) by blast
  obtain E :: "local_address option artifact_environment" where ef: "environment_formed E"
    and all: "\<forall>H\<in>fset P. \<exists>u r. generation_at E u r H"
    using finite_generation_presentations_together[OF finite_fset each] by blast
  obtain Gs where listed: "set Gs=fset P" and different: "distinct Gs"
    using finite_distinct_list[OF finite_fset[of P]] by blast
  let ?n = "length Gs"
  let ?g = "\<lambda>i. Gs!i"
  have sites: "\<forall>i\<in>{..<?n}. \<exists>s. generation_at E (fst s) (snd s) (?g i)"
  proof (intro ballI)
    fix i assume index: "i \<in> {..<?n}"
    have bound: "i<length Gs" using index by simp
    have member: "Gs!i \<in> fset P" using nth_mem[OF bound] listed by simp
    obtain u r where gen: "generation_at E u r (Gs!i)" using all member by blast
    show "\<exists>s. generation_at E (fst s) (snd s) (?g i)"
      by (rule exI[of _ "(u,r)"]) (use gen in simp)
  qed
  obtain s where chosen: "\<forall>i\<in>{..<?n}. generation_at E (fst (s i)) (snd (s i)) (?g i)"
    using bchoice[OF sites] by blast
  have distinct: "inj_on ?g {..<?n}" by (rule inj_on_nth[OF different]) simp
  have reads: "\<forall>i<?n. generation_at E (fst (s i)) (snd (s i)) (?g i)" using chosen by simp
  obtain H :: "local_address option artifact_environment" and u
    where gen: "generation_at H u [] (Generation l (Abs_fset (?g ` {..<?n})) p c)"
    using generation_record_extension[OF ef parts(1-3) distinct reads] by blast
  have members: "?g ` {..<?n}=fset P" using listed by (auto simp: set_conv_nth)
  have same: "Abs_fset (?g ` {..<?n})=P"
    by (rule fset_inject[THEN iffD1]) (simp add: members Abs_fset_inverse)
  show ?case using gen same by blast
qed

corollary closed_generation_presentation_total:
  assumes formed: "generation_formed G"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>u.
    generation_at E u [] G \<and> generation_environment_closed E {(u,[])}"
proof -
  obtain E :: "local_address option artifact_environment" and u
    where gen: "generation_at E u [] G" using generation_presentation_total[OF formed] by blast
  have ef: "environment_formed E" by (rule generation_at_environment_formed[OF gen])
  have roots: "\<forall>v r. (v,r) \<in> {(u,[])} \<longrightarrow> (\<exists>H. generation_at E v r H)"
    using gen by auto
  let ?F = "request_environment E (generation_requests E {(u,[])})"
  have closed: "generation_environment_closed ?F {(u,[])}"
    by (rule generation_closed_restriction[OF ef roots])
  have site: "(u,[]) \<in> generation_read_sites E {(u,[])}"
    using generation_read_sites_roots[of "{(u,[])}" E] by blast
  have retained: "generation_at ?F u [] G"
    by (rule generation_at_request_restriction[OF ef roots gen site])
  show ?thesis using closed retained by blast
qed

text \<open>
  The extension retains every old artifact use and binding. Each predecessor
  reference targets its supplied use and address, and the recovered predecessor
  set is exactly the finite injective family. The three other fields receive
  explicit literal bindings. No cause validity or authority premise is used.

  Totality follows by constructing each finite predecessor family, placing its
  presentations at disjoint uses, and adding the parent record. Empty
  predecessor sets use the same construction. Generation formation and actual
  presentation are thereby connected without making formation validate a cause.
\<close>

end
