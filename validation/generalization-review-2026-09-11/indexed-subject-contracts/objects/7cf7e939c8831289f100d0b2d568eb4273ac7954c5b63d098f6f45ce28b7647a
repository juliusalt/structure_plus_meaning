theory RRA_Replacement
  imports RRA_Transaction
begin

section \<open>Replacing one selected generation under its exact expectation\<close>

definition replacement_transaction :: "generation_core \<Rightarrow> generation_core \<Rightarrow> structural_transaction" where
  "replacement_transaction G H=
    \<lparr>expected_selected={|G|}, expected_absent={||},
     proposed_selected={|H|}, proposed_absent={||}\<rparr>"

lemma replacement_transaction_boundaries:
  "comparison_loci (replacement_transaction G H)={generation_locus G}"
  "changed_loci (replacement_transaction G H)={generation_locus H}"
  by (simp_all add: replacement_transaction_def comparison_loci_def changed_loci_def snapshot_loci_def)

lemma replacement_transaction_formed:
  "transaction_formed (replacement_transaction G H)\<longleftrightarrow>
    generation_formed G \<and> generation_formed H \<and> generation_locus H=generation_locus G"
  by (auto simp: transaction_formed_def replacement_transaction_def
    comparison_loci_def changed_loci_def snapshot_loci_def snapshot_formed_def selection_formed_def)

lemma replacement_comparison:
  assumes formed: "generation_formed G"
  shows "comparison_passes S (replacement_transaction G H)\<longleftrightarrow>
    snapshot_lookup S (generation_locus G)=Some G"
proof -
  have snapshot: "snapshot_formed {|G|}" using formed by (simp add: snapshot_formed_def selection_formed_def)
  have selected: "snapshot_lookup {|G|} (generation_locus G)=Some G"
    by (rule snapshot_lookup_member[OF snapshot]) simp
  show ?thesis by (simp add: comparison_passes_def comparison_loci_def snapshot_loci_def
    replacement_transaction_def selected)
qed

theorem selected_generation_replacement:
  assumes snapshot: "snapshot_formed S"
    and selected: "snapshot_lookup S (generation_locus G)=Some G"
    and formed: "generation_formed H" and locus: "generation_locus H=generation_locus G"
  shows "transact S (replacement_transaction G H) (Applied (replace_snapshot S {|H|} {||}))"
proof -
  have member: "G\<in>fset S" using selected by (simp add: snapshot_lookup_some[OF snapshot])
  have old: "generation_formed G" using snapshot member
    by (auto simp: snapshot_formed_def selection_formed_def)
  have transaction: "transaction_formed (replacement_transaction G H)"
    using old formed locus by (simp add: replacement_transaction_formed)
  have compare: "comparison_passes S (replacement_transaction G H)"
    using selected by (simp add: replacement_comparison[OF old])
  show ?thesis using snapshot transaction compare
    by (simp add: transact_applied_iff transaction_update_def replacement_transaction_def)
qed

theorem replacement_result:
  assumes transition: "transact S (replacement_transaction G H) (Applied U)"
  shows "snapshot_lookup U (generation_locus H)=Some H"
    and "\<And>l. l\<noteq>generation_locus H \<Longrightarrow> snapshot_lookup U l=snapshot_lookup S l"
    and "G\<noteq>H \<Longrightarrow> U\<noteq>S"
proof -
  have formed: "generation_formed G" "generation_formed H" and locus: "generation_locus H=generation_locus G"
    and compare: "comparison_passes S (replacement_transaction G H)"
    using transition by (auto simp: transact_applied_iff replacement_transaction_formed)
  have snapshot: "snapshot_formed {|H|}" using formed(2)
    by (simp add: snapshot_formed_def selection_formed_def)
  have chosen: "snapshot_lookup {|H|} (generation_locus H)=Some H"
    by (rule snapshot_lookup_member[OF snapshot]) simp
  show selected: "snapshot_lookup U (generation_locus H)=Some H"
    using successful_transaction_lookup[OF transition, of "generation_locus H"] chosen
    by (simp add: replacement_transaction_def snapshot_loci_def)
  show "\<And>l. l\<noteq>generation_locus H \<Longrightarrow> snapshot_lookup U l=snapshot_lookup S l"
    by (rule successful_transaction_no_extra_change[OF transition])
       (simp add: replacement_transaction_boundaries)
  show "G\<noteq>H \<Longrightarrow> U\<noteq>S"
    using compare selected locus by (auto simp: replacement_comparison[OF formed(1)])
qed

theorem replacement_expectation_conflict:
  assumes snapshot: "snapshot_formed S" and old: "generation_formed G" and new: "generation_formed H"
    and locus: "generation_locus H=generation_locus G"
    and different: "snapshot_lookup S (generation_locus G)\<noteq>Some G"
  shows "transact S (replacement_transaction G H)
    (Conflict (observed_comparison S (replacement_transaction G H)))"
  using assms by (simp add: transact_conflict_iff replacement_transaction_formed replacement_comparison[OF old])

text \<open>
  This transaction compares exactly the locus it replaces. Its expectation is
  the supplied complete old generation, and its write is the supplied complete
  new generation at the same locus. Other selections remain unchanged and do
  not become extra comparison requirements. A different observed generation
  gives a structural conflict. Neither outcome proves historical succession,
  cause validity, publication, or semantic permission.
\<close>

end
