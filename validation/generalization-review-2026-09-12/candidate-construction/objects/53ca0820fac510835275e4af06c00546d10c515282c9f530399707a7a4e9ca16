theory RRA_Transaction
  imports RRA_Selection
begin

section \<open>Finite expectations and proposed selections\<close>

record structural_transaction =
  expected_selected :: selection_snapshot
  expected_absent :: "exact_target fset"
  proposed_selected :: selection_snapshot
  proposed_absent :: "exact_target fset"

definition comparison_loci :: "structural_transaction \<Rightarrow> exact_target set" where
  "comparison_loci T = snapshot_loci (expected_selected T) \<union> fset (expected_absent T)"

definition changed_loci :: "structural_transaction \<Rightarrow> exact_target set" where
  "changed_loci T = snapshot_loci (proposed_selected T) \<union> fset (proposed_absent T)"

definition transaction_formed :: "structural_transaction \<Rightarrow> bool" where
  "transaction_formed T \<longleftrightarrow>
    snapshot_formed (expected_selected T) \<and> snapshot_formed (proposed_selected T) \<and>
    (\<forall>l\<in>fset (expected_absent T). target_formed l) \<and>
    (\<forall>l\<in>fset (proposed_absent T). target_formed l) \<and>
    snapshot_loci (expected_selected T) \<inter> fset (expected_absent T) = {} \<and>
    snapshot_loci (proposed_selected T) \<inter> fset (proposed_absent T) = {} \<and>
    changed_loci T \<subseteq> comparison_loci T"

type_synonym comparison_observation = "(exact_target \<times> generation_core option) set"

definition observed_comparison ::
  "selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow> comparison_observation" where
  "observed_comparison S T = graph_map (comparison_loci T) (snapshot_lookup S)"

definition comparison_passes :: "selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow> bool" where
  "comparison_passes S T \<longleftrightarrow>
    (\<forall>l\<in>comparison_loci T.
      snapshot_lookup S l = snapshot_lookup (expected_selected T) l)"

definition transaction_update ::
  "selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow> selection_snapshot" where
  "transaction_update S T = replace_snapshot S (proposed_selected T) (proposed_absent T)"

datatype transaction_result =
    Applied selection_snapshot
  | Conflict comparison_observation

definition transact ::
  "selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow> transaction_result \<Rightarrow> bool" where
  "transact S T result \<longleftrightarrow>
    snapshot_formed S \<and> transaction_formed T \<and>
    result = (if comparison_passes S T then Applied (transaction_update S T)
      else Conflict (observed_comparison S T))"

fun transaction_output :: "transaction_result \<Rightarrow> selection_snapshot option" where
  "transaction_output (Applied S) = Some S"
| "transaction_output (Conflict C) = None"

lemma transaction_result_determined:
  assumes "transact S T x" "transact S T y"
  shows "x = y"
  using assms by (simp add: transact_def)

lemma transaction_result_exists:
  assumes "snapshot_formed S" "transaction_formed T"
  shows "\<exists>!result. transact S T result"
  using assms by (simp add: transact_def)

lemma transact_applied_iff:
  "transact S T (Applied S') \<longleftrightarrow>
    snapshot_formed S \<and> transaction_formed T \<and>
    comparison_passes S T \<and> S' = transaction_update S T"
  by (auto simp: transact_def split: if_splits)

lemma transact_conflict_iff:
  "transact S T (Conflict C) \<longleftrightarrow>
    snapshot_formed S \<and> transaction_formed T \<and>
    \<not> comparison_passes S T \<and> C = observed_comparison S T"
  by (auto simp: transact_def split: if_splits)

lemma transaction_update_formed:
  assumes "snapshot_formed S" "transaction_formed T"
  shows "snapshot_formed (transaction_update S T)"
  using assms unfolding transaction_update_def
  by (intro replace_snapshot_formed) (auto simp: transaction_formed_def)

lemma successful_transaction_formed:
  assumes "transact S T (Applied S')"
  shows "snapshot_formed S'"
  using assms transaction_update_formed by (auto simp: transact_applied_iff)

lemma observed_comparison_complete:
  "rel_dom (observed_comparison S T) = comparison_loci T"
  by (simp add: observed_comparison_def graph_map_dom)

lemma observed_comparison_exact:
  "(l,v) \<in> observed_comparison S T \<longleftrightarrow>
    l \<in> comparison_loci T \<and> v = snapshot_lookup S l"
  by (auto simp: observed_comparison_def graph_map_def)

lemma observed_comparison_finite:
  "finite (observed_comparison S T)"
proof -
  have finite: "finite (comparison_loci T)"
    by (simp add: comparison_loci_def snapshot_loci_def)
  have exact: "exact_map (comparison_loci T) (snapshot_lookup S ` comparison_loci T)
    (observed_comparison S T)"
    unfolding observed_comparison_def by (rule graph_map_exact[OF finite])
  show ?thesis using exact by (simp add: exact_map_def)
qed

lemma conflict_contains_every_observation:
  assumes "transact S T (Conflict C)"
  shows "rel_dom C = comparison_loci T"
    and "\<forall>l\<in>comparison_loci T. (l,snapshot_lookup S l) \<in> C"
    and "finite C"
    and "transaction_output (Conflict C) = None"
  using assms observed_comparison_complete[of S T] observed_comparison_finite[of S T]
  by (auto simp: transact_conflict_iff observed_comparison_exact)

lemma successful_transaction_lookup:
  assumes trans: "transact S T (Applied S')"
  shows "snapshot_lookup S' l =
    (if l \<in> snapshot_loci (proposed_selected T)
     then snapshot_lookup (proposed_selected T) l
     else if l \<in> fset (proposed_absent T) then None else snapshot_lookup S l)"
proof -
  have sf: "snapshot_formed S" and wf: "snapshot_formed (proposed_selected T)"
    and out: "S' = transaction_update S T"
    using trans by (auto simp: transact_applied_iff transaction_formed_def)
  show ?thesis
    using replace_snapshot_lookup[OF sf wf, of "proposed_absent T" l] out
    by (simp add: transaction_update_def)
qed

lemma successful_transaction_all_writes:
  assumes "transact S T (Applied S')"
  shows "fset (proposed_selected T) \<subseteq> fset S'"
  using assms by (auto simp: transact_applied_iff transaction_update_def replace_snapshot_members)

lemma successful_transaction_all_withdrawals:
  assumes "transact S T (Applied S')"
  shows "snapshot_loci S' \<inter> fset (proposed_absent T) = {}"
  using assms by (auto simp: transact_applied_iff transaction_update_def
    transaction_formed_def replace_snapshot_loci)

lemma successful_transaction_no_extra_change:
  assumes trans: "transact S T (Applied S')" and outside: "l \<notin> changed_loci T"
  shows "snapshot_lookup S' l = snapshot_lookup S l"
  using successful_transaction_lookup[OF trans, of l] outside
  by (simp add: changed_loci_def)

lemma no_partial_success:
  assumes trans: "transact S T (Applied S')"
  shows "\<not> (\<exists>G\<in>fset (proposed_selected T). G \<notin> fset S') \<and>
    \<not> (\<exists>l\<in>fset (proposed_absent T). l \<in> snapshot_loci S')"
  using successful_transaction_all_writes[OF trans]
    successful_transaction_all_withdrawals[OF trans] by blast

definition empty_transaction :: structural_transaction where
  "empty_transaction =
    \<lparr>expected_selected={||}, expected_absent={||},
      proposed_selected={||}, proposed_absent={||}\<rparr>"

lemma empty_transaction_formed [simp]: "transaction_formed empty_transaction"
  by (simp add: empty_transaction_def transaction_formed_def
    comparison_loci_def changed_loci_def snapshot_loci_def)

lemma empty_transaction_preserves_snapshot:
  assumes "snapshot_formed S"
  shows "transact S empty_transaction (Applied S)"
proof -
  have compare: "comparison_passes S empty_transaction"
    by (simp add: comparison_passes_def comparison_loci_def empty_transaction_def snapshot_loci_def)
  have update: "transaction_update S empty_transaction = S"
    by (simp add: transaction_update_def empty_transaction_def replace_snapshot_def snapshot_loci_def)
  show ?thesis using assms compare update by (simp add: transact_applied_iff)
qed

definition admission_transaction :: "selection_snapshot \<Rightarrow> structural_transaction" where
  "admission_transaction W =
    \<lparr>expected_selected={||}, expected_absent=fimage generation_locus W,
      proposed_selected=W, proposed_absent={||}\<rparr>"

lemma admission_transaction_formed:
  assumes formed: "snapshot_formed W"
  shows "transaction_formed (admission_transaction W)"
proof -
  have loci: "\<forall>l\<in>snapshot_loci W. target_formed l"
    using snapshot_loci_formed[OF formed] by blast
  show ?thesis using formed loci
    by (auto simp: transaction_formed_def admission_transaction_def
      comparison_loci_def changed_loci_def snapshot_loci_def)
qed

lemma admit_complete_snapshot:
  assumes formed: "snapshot_formed W"
  shows "transact {||} (admission_transaction W) (Applied W)"
proof -
  have tf: "transaction_formed (admission_transaction W)"
    by (rule admission_transaction_formed[OF formed])
  have compare: "comparison_passes {||} (admission_transaction W)"
    by (simp add: comparison_passes_def admission_transaction_def)
  have update: "transaction_update {||} (admission_transaction W) = W"
    by (simp add: transaction_update_def admission_transaction_def replace_snapshot_def)
  show ?thesis using tf compare update by (simp add: transact_applied_iff)
qed

lemma admitting_a_selected_locus_conflicts:
  assumes sf: "snapshot_formed S" and wf: "snapshot_formed W"
    and selected: "G \<in> fset S" and proposed: "generation_locus G \<in> snapshot_loci W"
  shows "transact S (admission_transaction W)
    (Conflict (observed_comparison S (admission_transaction W)))"
proof -
  have tf: "transaction_formed (admission_transaction W)"
    by (rule admission_transaction_formed[OF wf])
  have observed: "snapshot_lookup S (generation_locus G) = Some G"
    by (rule snapshot_lookup_member[OF sf selected])
  have compared: "generation_locus G \<in> comparison_loci (admission_transaction W)"
    using proposed by (simp add: comparison_loci_def admission_transaction_def snapshot_loci_def)
  have fails: "\<not> comparison_passes S (admission_transaction W)"
    using observed compared by (auto simp: comparison_passes_def admission_transaction_def)
  show ?thesis using sf tf fails by (simp add: transact_conflict_iff)
qed

text \<open>
  Comparison includes both expected selections and expected absence. Every
  proposed change must belong to that complete comparison boundary. Successful
  replacement changes all proposed loci together and preserves every other
  selection. A conflict contains every observed comparison, including ones
  that agreed, and supplies no successor snapshot.

  These relations select existing exact cores. They do not create succession,
  validate a cause, accept a publication, or assert currentness. Removing a
  selection does not alter the generation that was selected.
\<close>

section \<open>Transaction fields are structural projections\<close>

definition transaction_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
   structural_transaction \<Rightarrow> bool" where
  "transaction_at E u root T \<longleftrightarrow>
    environment_formed E \<and> transaction_formed T \<and>
    (\<exists>R ps er ar wr dr. artifact_at E u R \<and> record_at R root ps [er,ar,wr,dr] \<and>
      snapshot_at E u er (expected_selected T) \<and>
      target_selection_at E u ar (fset (expected_absent T)) \<and>
      snapshot_at E u wr (proposed_selected T) \<and>
      target_selection_at E u dr (fset (proposed_absent T)))"

lemma structural_transaction_identity:
  fixes S T :: structural_transaction
  shows "S = T \<longleftrightarrow>
    expected_selected S = expected_selected T \<and> expected_absent S = expected_absent T \<and>
    proposed_selected S = proposed_selected T \<and> proposed_absent S = proposed_absent T"
  by (cases S; cases T) auto

lemma transaction_at_unique:
  assumes first: "transaction_at E u root S" and second: "transaction_at E u root T"
  shows "S = T"
proof -
  obtain R ps er ar wr dr where a: "environment_formed E" "artifact_at E u R"
    "record_at R root ps [er,ar,wr,dr]" "snapshot_at E u er (expected_selected S)"
    "target_selection_at E u ar (fset (expected_absent S))"
    "snapshot_at E u wr (proposed_selected S)"
    "target_selection_at E u dr (fset (proposed_absent S))"
    using first unfolding transaction_at_def by blast
  obtain R' qs er' ar' wr' dr' where b: "artifact_at E u R'"
    "record_at R' root qs [er',ar',wr',dr']" "snapshot_at E u er' (expected_selected T)"
    "target_selection_at E u ar' (fset (expected_absent T))"
    "snapshot_at E u wr' (proposed_selected T)"
    "target_selection_at E u dr' (fset (proposed_absent T))"
    using second unfolding transaction_at_def by blast
  have same: "R = R'" by (rule environment_artifact_unique[OF a(1,2) b(1)])
  have endpoints: "er = er' \<and> ar = ar' \<and> wr = wr' \<and> dr = dr'"
    using record_at_unique[OF a(3)] b(2) same by auto
  have expected: "expected_selected S = expected_selected T"
    using snapshot_at_unique[OF a(4)] b(3) endpoints by blast
  have expected_none: "fset (expected_absent S) = fset (expected_absent T)"
    using target_selection_unique[OF a(5)] b(4) endpoints by blast
  have proposed: "proposed_selected S = proposed_selected T"
    using snapshot_at_unique[OF a(6)] b(5) endpoints by blast
  have proposed_none: "fset (proposed_absent S) = fset (proposed_absent T)"
    using target_selection_unique[OF a(7)] b(6) endpoints by blast
  show ?thesis using expected expected_none proposed proposed_none
    by (simp add: structural_transaction_identity fset_inject)
qed

lemma transaction_at_locality:
  assumes ef: "environment_formed E" and ff: "environment_formed F"
    and agree: "environment_agrees_on E F U"
    and closed: "environment_edge_closed E U" and member: "u \<in> U"
  shows "transaction_at E u root T = transaction_at F u root T"
proof -
  have arts: "\<forall>R. artifact_at E u R = artifact_at F u R"
    using agree member by (simp add: environment_agrees_on_def)
  show ?thesis
    by (simp only: transaction_at_def ef ff arts snapshot_at_locality[OF assms]
        target_selection_locality[OF assms])
qed

end
