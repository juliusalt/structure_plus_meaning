theory RRA_Fresh_Generation_Frames
  imports RRA_Generation_Record_Construction RRA_Embedded_Literal_Extensions
begin

definition generation_record_literals where
  "generation_record_literals l p c=
    {(syntax_branch 0 [4],target_artifact l),(syntax_branch 2 [4],target_artifact p),
      (syntax_branch 3 [4],target_artifact c)}"

definition fresh_generation_predecessor_environment where
  "fresh_generation_predecessor_environment E u l p c as v=
    add_source_bindings (add_artifact_use E u (generation_record_frame l p c as)) u
      ((\<lambda>i. (generation_predecessor_slot i,v i)) ` {..<length as})"

locale fresh_generation_frame =
  fixes E :: "local_address option artifact_environment" and u :: "local_address option"
    and l p c :: exact_target and as :: "(exact_artifact\<times>local_address) list"
    and v :: "nat\<Rightarrow>local_address option"
  assumes ef: "environment_formed E"
    and lf: "target_formed l" and pf: "target_formed p" and cf: "target_formed c"
    and chosen: "\<forall>i\<in>{..<length as}. artifact_at E (v i) (fst (as!i)) \<and>
      anchor_formed (fst (as!i),snd (as!i))"
    and fresh: "u\<notin>environment_uses E"
begin

abbreviation n where "n\<equiv>length as"
abbreviation R where "R\<equiv>generation_record_frame l p c as"
abbreviation D where "D\<equiv>(\<lambda>i. (generation_predecessor_slot i,v i)) ` {..<n}"
abbreviation F where "F\<equiv>fresh_generation_predecessor_environment E u l p c as v"
abbreviation L where "L\<equiv>generation_record_literals l p c"

sublocale frame: generation_frame l p c as
  by (rule generation_frame.intro[OF lf pf cf])
    (use chosen in \<open>auto simp: set_conv_nth\<close>)

lemma frame_same: "R=frame.framed" by (simp only: generation_record_frame_def)

lemma original_unbound: "\<not>binds_slot E u k w"
  using environment_binding_uses(1)[OF ef, of u k w] fresh by blast

lemma predecessor_formed: "environment_formed F"
proof -
  let ?B="add_artifact_use E u R"
  have bf: "environment_formed ?B"
    by (rule added_artifact_formed[OF ef _ fresh]) (simp only: frame_same; rule frame.formed)
  have source: "artifact_at ?B u R" by simp
  have finite: "finite D" by simp
  have functional: "single_valued D"
    using generation_predecessor_slots_injective by (auto simp: single_valued_def inj_def)
  have slots: "rel_dom D\<subseteq>rra_carrier (object_structure R)"
    using frame.predecessor_slots_inside by (auto simp: rel_dom_def frame_same)
  have targets: "rel_ran D\<subseteq>environment_uses ?B"
  proof -
    have old: "rel_ran D\<subseteq>environment_uses E"
      using chosen by (auto simp: rel_ran_def environment_uses_def rel_dom_def artifact_at_def)
    show ?thesis using old included_uses[OF added_artifact_included, of E u R] by blast
  qed
  have unbound: "\<And>k w. k\<in>rel_dom D \<Longrightarrow> \<not>binds_slot ?B u k w"
    using original_unbound by simp
  show ?thesis unfolding fresh_generation_predecessor_environment_def
    by (rule add_source_bindings_formed[OF bf source finite functional slots targets unbound])
qed

lemma predecessor_included: "environment_included E F"
  unfolding fresh_generation_predecessor_environment_def
  by (rule environment_included_trans[OF added_artifact_included add_source_included])

lemma predecessor_source: "artifact_at F u R"
  by (simp add: fresh_generation_predecessor_environment_def)

lemma predecessor_bindings:
  "binds_slot F w k z \<longleftrightarrow> binds_slot E w k z \<or> (w=u \<and> (k,z)\<in>D)"
  by (simp only: fresh_generation_predecessor_environment_def add_source_binding added_artifact_bindings)

lemma predecessor_at:
  "i<n \<Longrightarrow> binds_slot F u (generation_predecessor_slot i) (v i)"
  by (auto simp: predecessor_bindings)

lemma literal_slots_unbound: "k\<in>rel_dom L \<Longrightarrow> \<not>binds_slot F u k w"
  using generation_predecessor_slots_separate[where j=0]
    generation_predecessor_slots_separate[where j=2]
    generation_predecessor_slots_separate[where j=3] original_unbound
  by (auto simp: predecessor_bindings generation_record_literals_def rel_dom_def)

sublocale literals: literal_extension F u R L
proof (rule literal_extension.intro[OF predecessor_formed predecessor_source])
  show "finite L" by (simp add: generation_record_literals_def)
  show "single_valued L" by (auto simp: generation_record_literals_def single_valued_def eval_nat_numeral)
  show "\<forall>k T. (k,T)\<in>L \<longrightarrow> exact_formed T"
    using target_formed_artifact[OF lf] target_formed_artifact[OF pf] target_formed_artifact[OF cf]
    by (auto simp: generation_record_literals_def)
  show "rel_dom L\<subseteq>rra_carrier (object_structure R)"
    using frame.literal_slots_inside by (auto simp: generation_record_literals_def rel_dom_def frame_same)
  show "\<And>k w. k\<in>rel_dom L \<Longrightarrow> \<not>binds_slot F u k w" by (rule literal_slots_unbound)
qed

end

context generation_record_construction
begin

sublocale fresh_frame: fresh_generation_frame E record_use l p c as v
  by (rule fresh_generation_frame.intro[OF ef lf pf cf chosen generation_record_use_fresh[OF ef]])

lemma original_predecessor_instance:
  "generation_record_predecessor_environment E l p c as v=fresh_frame.F"
  by (simp only: generation_record_predecessor_environment_def
    fresh_generation_predecessor_environment_def Let_def)

end

text \<open>
  The chosen fresh use is a premise. Predecessor attachment and the literal
  installation prerequisites are established once for every such choice.
  The original allocator supplies one exact instance of this contract.
\<close>

end
