theory RRA_Generation_Record_Construction
  imports RRA_Generation_Frames RRA_Generation_Transport RRA_Literal_Extension RRA_Included_Artifacts
begin

definition generation_record_frame where
  "generation_record_frame l p c as=syntax_family_construction.record_framed
    [literal_syntax l,
      syntax_family_construction.framed (map (\<lambda>a. literal_syntax (Occurrence_Anchor a)) as),
      literal_syntax p,literal_syntax c]"

definition generation_record_use where
  "generation_record_use E=fresh_use_map (environment_uses E) None (Some [])"

lemma generation_record_use_fresh:
  assumes formed: "environment_formed E"
  shows "generation_record_use E\<notin>environment_uses E"
  using fresh_use_map_outside[OF environment_uses_finite[OF formed], of None "[]"]
  by (simp only: generation_record_use_def; blast)

definition generation_record_predecessor_environment where
  "generation_record_predecessor_environment E l p c as v=(let
    u=generation_record_use E; R=generation_record_frame l p c as
    in add_source_bindings (add_artifact_use E u R) u
      ((\<lambda>i. (generation_predecessor_slot i,v i)) ` {..<length as}))"

definition generation_record_environment where
  "generation_record_environment E l p c as v=(let
    F=generation_record_predecessor_environment E l p c as v;
    u=generation_record_use E; R=generation_record_frame l p c as
    in graft_environment F u (literal_environment R
      {(syntax_branch 0 [4],target_artifact l),(syntax_branch 2 [4],target_artifact p),
        (syntax_branch 3 [4],target_artifact c)}))"

locale generation_record_construction =
  fixes E :: "local_address option artifact_environment"
    and l p c :: exact_target and as :: "(exact_artifact\<times>local_address) list"
    and v :: "nat\<Rightarrow>local_address option"
  assumes ef: "environment_formed E"
    and lf: "target_formed l" and pf: "target_formed p" and cf: "target_formed c"
    and chosen: "\<forall>i\<in>{..<length as}. artifact_at E (v i) (fst (as!i)) \<and> anchor_formed (fst (as!i),snd (as!i))"
begin

abbreviation n where "n\<equiv>length as"
abbreviation record_use where "record_use\<equiv>generation_record_use E"
abbreviation installed where "installed\<equiv>generation_record_environment E l p c as v"

sublocale frame: generation_frame l p c as
  by (rule generation_frame.intro[OF lf pf cf])
    (use chosen in \<open>auto simp: set_conv_nth\<close>)

theorem properties:
  "environment_formed installed"
  "environment_included E installed"
  "generation_fields_at installed record_use [] l (generation_frame_members n) p c"
  "\<forall>i<n. located_at installed record_use (generation_predecessor_node i) (v i) (snd (as!i))"
proof -
  let ?R = "frame.framed"
  let ?u = "fresh_use_map (environment_uses E) None (Some [])"
  let ?B = "add_artifact_use E ?u ?R"
  let ?D = "(\<lambda>i. (generation_predecessor_slot i,v i)) ` {..<n}"
  let ?F = "add_source_bindings ?B ?u ?D"
  let ?L = "{(syntax_branch 0 [4],target_artifact l),
    (syntax_branch 2 [4],target_artifact p),(syntax_branch 3 [4],target_artifact c)}"
  have fresh: "?u \<notin> environment_uses E"
    using generation_record_use_fresh[OF ef] by (simp only: generation_record_use_def; blast)
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
    located_at ?H ?u (generation_predecessor_node i) (v i) (snd (as!i))"
  proof -
    fix i assume index: "i<n"
    have entry: "(generation_predecessor_slot i,v i) \<in> ?D"
      by (rule image_eqI[where x=i]) (use index in auto)
    have bound_f: "binds_slot ?F ?u (generation_predecessor_slot i) (v i)" using entry by simp
    have bound_h: "binds_slot ?H ?u (generation_predecessor_slot i) (v i)"
      by (rule included_binding[OF literals.included bound_f])
    have original: "artifact_at E (v i) (fst (as!i))" and anchor: "anchor_formed (fst (as!i),snd (as!i))"
      using chosen index by auto
    have target: "artifact_at ?H (v i) (fst (as!i))" by (rule included_artifact[OF included original])
    have loc: "citation_location ?H ?u (External (generation_predecessor_slot i) (snd (as!i))) (v i) (snd (as!i))"
      using bound_h target anchor by auto
    have at: "i<length as" using index by simp
    have cite: "citation_at ?R (generation_predecessor_node i)
      (External (generation_predecessor_slot i) (snd (as!i)))
      (syntax_branch 1 ` (syntax_branch i ` literal_interior (Occurrence_Anchor (fst (as!i),snd (as!i)))))"
      using frame.predecessor_citation[OF at] index by simp
    show "located_at ?H ?u (generation_predecessor_node i) (v i) (snd (as!i))"
      using source_h cite loc unfolding located_at_def by blast
  qed
  have same: "?H=installed" "?u=record_use"
    by (simp_all only: generation_record_environment_def generation_record_predecessor_environment_def
      generation_record_frame_def generation_record_use_def Let_def)
  show "environment_formed installed" using literals.formed same(1) by metis
  show "environment_included E installed" using included same(1) by metis
  show "generation_fields_at installed record_use [] l (generation_frame_members n) p c"
    using fields same by metis
  show "\<forall>i<n. located_at installed record_use (generation_predecessor_node i) (v i) (snd (as!i))"
    using locations same by metis
qed

theorem old_artifacts:
  "w\<in>environment_uses E \<Longrightarrow> artifact_at installed w R \<longleftrightarrow> artifact_at E w R"
  by (rule included_existing_artifact[OF properties(2,1)])

theorem old_bindings:
  assumes existing: "w\<in>environment_uses E"
  shows "binds_slot installed w k z \<longleftrightarrow> binds_slot E w k z"
proof -
  have separate: "w\<noteq>record_use" using generation_record_use_fresh[OF ef] existing by blast
  show ?thesis by (simp add: generation_record_environment_def
    generation_record_predecessor_environment_def Let_def graft_environment_def
    renamed_literal_bindings separate)
qed

theorem recovers:
  assumes distinct: "inj_on g {..<n}"
    and predecessors: "\<forall>i<n. generation_at E (v i) (snd (as!i)) (g i)"
  shows "generation_at installed record_use [] (Generation l (Abs_fset (g ` {..<n})) p c)"
proof -
  obtain h where hinj: "inj_on h (rel_dom (generation_frame_members n))"
    and hat: "\<forall>i<n. h (generation_predecessor_socket n i)=g i"
    and hvalues: "h ` rel_dom (generation_frame_members n)=g ` {..<n}"
    using generation_predecessor_assignment[OF distinct] by blast
  have refs: "\<forall>s d. (s,d) \<in> generation_frame_members n \<longrightarrow>
    (\<exists>w b. located_at installed record_use d w b \<and> generation_at installed w b (h s))"
  proof (intro allI impI)
    fix s d assume edge: "(s,d) \<in> generation_frame_members n"
    obtain i where index: "i<n" and s: "s=generation_predecessor_socket n i"
      and d: "d=generation_predecessor_node i" using edge by (auto simp: generation_frame_member)
    have old: "generation_at E (v i) (snd (as!i)) (g i)" using predecessors index by blast
    have kept: "generation_at installed (v i) (snd (as!i)) (g i)"
      by (rule generation_at_included[OF old properties(2) properties(1)])
    have same: "h s=g i" using hat index s by simp
    show "\<exists>w b. located_at installed record_use d w b \<and> generation_at installed w b (h s)"
      by (rule exI[of _ "v i"], rule exI[of _ "snd (as!i)"])
         (use properties(4)[rule_format, OF index] kept in \<open>simp only: d same; blast\<close>)
  qed
  have recovered: "generation_at installed record_use [] (Generation l (Abs_fset (g ` {..<n})) p c)"
    using generation_at.generation[OF properties(3) hinj refs] by (simp only: hvalues)
  show ?thesis by (rule recovered)
qed

end

text \<open>
  The original record, predecessor-slot and literal-installation argument has
  one explicit constructor. Its complete actual targets and existing anchor
  readings determine the new frame and bindings. Recursive predecessor recovery
  instantiates this constructor under the original injective-family premise.
  Neither field formation nor predecessor recovery validates the cause.
\<close>

end
