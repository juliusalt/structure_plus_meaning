theory Factor_Transaction_Values
  imports Factor_Generation_Values RRA_Transaction
begin

section \<open>Complete snapshot data retains the selected exact cores\<close>

definition snapshot_value_presents :: "selection_snapshot \<Rightarrow> factor_term \<Rightarrow> bool" where
  "snapshot_value_presents S t \<longleftrightarrow> snapshot_formed S \<and>
    data_collection_presents generation_value_presents (fset S) t"

theorem snapshot_value_presentation_class:
  "presentation_class snapshot_value_presents snapshot_formed (\<lambda>t. \<exists>S. snapshot_value_presents S t)"
proof -
  have raw: "presentation_class (data_fset_presents generation_value_presents)
      (\<lambda>S. \<forall>G\<in>fset S. generation_formed G)
      (presented_predicate (data_sequence_presents generation_value_presents) distinct)"
    by (rule data_fset_presentation_class[OF generation_value_presentation_class])
  have restricted: "presentation_class
      (\<lambda>S t. snapshot_formed S \<and> data_fset_presents generation_value_presents S t)
      snapshot_formed (\<lambda>t. \<exists>S. snapshot_formed S \<and> data_fset_presents generation_value_presents S t)"
    by (rule presentation_class_subdomain[OF raw]) (simp add: snapshot_formed_def selection_formed_def)
  show ?thesis using restricted by (simp only: presentation_class_def snapshot_value_presents_def)
qed

interpretation snapshot_values: presentation_class snapshot_value_presents snapshot_formed
  "\<lambda>t. \<exists>S. snapshot_value_presents S t"
  by (rule snapshot_value_presentation_class)

lemma snapshot_value_presents_formed:
  assumes present: "snapshot_value_presents S t"
  shows "snapshot_formed S \<and> term_formed t \<and> self_contained_term t"
proof -
  have sf: "snapshot_formed S" and members: "data_collection_presents generation_value_presents (fset S) t"
    using present by (auto simp: snapshot_value_presents_def)
  have tf: "term_formed t" by (rule data_collection_presents_formed[OF members])
    (meson generation_value_presents_formed)
  have closed: "self_contained_term t" by (rule data_collection_presents_self_contained[OF members])
    (meson generation_value_presents_formed)
  show ?thesis using sf tf closed by blast
qed

lemma snapshot_value_presents_unique:
  assumes first: "snapshot_value_presents S t" and second: "snapshot_value_presents U t"
  shows "S=U"
  by (rule snapshot_values.recovery[OF first second])

theorem snapshot_value_presents_total:
  assumes formed: "snapshot_formed S"
  shows "\<exists>t. snapshot_value_presents S t"
  by (rule snapshot_values.total[OF formed])

theorem snapshot_quotation_presentation_class:
  "presentation_class
    (composed_presentation snapshot_value_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    snapshot_formed
    (\<lambda>p. \<exists>t. (\<exists>S. snapshot_value_presents S t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF snapshot_value_presentation_class])
    (use snapshot_value_presents_formed in blast)

section \<open>The four independent transaction fields as ordinary data\<close>

definition transaction_value_presents :: "structural_transaction \<Rightarrow> factor_term \<Rightarrow> bool" where
  "transaction_value_presents T t \<longleftrightarrow> transaction_formed T \<and>
    (\<exists>a b c d. snapshot_value_presents (expected_selected T) a \<and>
      data_collection_presents target_value_presents (fset (expected_absent T)) b \<and>
      snapshot_value_presents (proposed_selected T) c \<and>
      data_collection_presents target_value_presents (fset (proposed_absent T)) d \<and>
      t=Pair_Term a (Pair_Term b (Pair_Term c d)))"

theorem transaction_value_presentation_class:
  "presentation_class transaction_value_presents transaction_formed
    (\<lambda>t. \<exists>T. transaction_value_presents T t)"
proof -
  let ?S="\<lambda>t. \<exists>U. snapshot_value_presents U t"
  let ?T="presented_predicate (data_sequence_presents target_value_presents) distinct"
  let ?tail="\<lambda>t. \<exists>p q. ?S p \<and> ?T q \<and> t=Pair_Term p q"
  let ?middle="\<lambda>t. \<exists>p q. ?T p \<and> ?tail q \<and> t=Pair_Term p q"
  let ?A="\<lambda>t. \<exists>p q. ?S p \<and> ?middle q \<and> t=Pair_Term p q"
  let ?R="factor_pair_presents snapshot_value_presents
    (factor_pair_presents (data_fset_presents target_value_presents)
      (factor_pair_presents snapshot_value_presents (data_fset_presents target_value_presents)))"
  let ?D="\<lambda>z. snapshot_formed (fst z) \<and>
    ((\<forall>x\<in>fset (fst (snd z)). target_formed x) \<and>
      (snapshot_formed (fst (snd (snd z))) \<and> (\<forall>x\<in>fset (snd (snd (snd z))). target_formed x)))"
  have fields: "presentation_class ?R ?D ?A"
    by (rule factor_pair_class[OF snapshot_value_presentation_class
      factor_pair_class[OF data_fset_presentation_class[OF target_value_presentation_class]
        factor_pair_class[OF snapshot_value_presentation_class
          data_fset_presentation_class[OF target_value_presentation_class]]]])
  let ?observe="\<lambda>T. (expected_selected T,(expected_absent T,(proposed_selected T,proposed_absent T)))"
  have observed: "presentation_class (\<lambda>T t. transaction_formed T \<and> ?R (?observe T) t)
      transaction_formed (\<lambda>t. \<exists>T. transaction_formed T \<and> ?R (?observe T) t)"
  proof (rule presentation_class_observations[OF fields])
    fix T assume "transaction_formed T"
    then show "?D (?observe T)" by (simp add: transaction_formed_def)
  next
    fix T U assume "transaction_formed T" "transaction_formed U" "?observe T=?observe U"
    then show "T=U" by (simp add: structural_transaction_identity)
  qed
  have reading: "(transaction_formed T \<and> ?R (?observe T) t) \<longleftrightarrow> transaction_value_presents T t" for T t
    by (auto simp: transaction_value_presents_def factor_pair_presents_def; blast)
  show ?thesis using observed by (simp only: reading)
qed

interpretation transaction_values: presentation_class transaction_value_presents transaction_formed
  "\<lambda>t. \<exists>T. transaction_value_presents T t"
  by (rule transaction_value_presentation_class)

theorem transaction_value_presents_unique:
  assumes first: "transaction_value_presents S t" and second: "transaction_value_presents T t"
  shows "S=T"
  by (rule transaction_values.recovery[OF first second])

lemma transaction_value_presents_formed:
  assumes present: "transaction_value_presents T t"
  shows "transaction_formed T \<and> term_formed t \<and> self_contained_term t"
proof -
  obtain a b c d where formed: "transaction_formed T"
    and fields: "snapshot_value_presents (expected_selected T) a"
      "data_collection_presents target_value_presents (fset (expected_absent T)) b"
      "snapshot_value_presents (proposed_selected T) c"
      "data_collection_presents target_value_presents (fset (proposed_absent T)) d"
      "t=Pair_Term a (Pair_Term b (Pair_Term c d))"
    using present unfolding transaction_value_presents_def by blast
  have bf: "term_formed b" by (rule data_collection_presents_formed[OF fields(2)])
    (meson target_value_presents_formed)
  have df: "term_formed d" by (rule data_collection_presents_formed[OF fields(4)])
    (meson target_value_presents_formed)
  have bc: "self_contained_term b" by (rule data_collection_presents_self_contained[OF fields(2)])
    (meson target_value_presents_formed)
  have dc: "self_contained_term d" by (rule data_collection_presents_self_contained[OF fields(4)])
    (meson target_value_presents_formed)
  show ?thesis using formed fields(5) bf df bc dc
    snapshot_value_presents_formed[OF fields(1)] snapshot_value_presents_formed[OF fields(3)] by simp
qed

theorem transaction_value_presents_total:
  assumes formed: "transaction_formed T"
  shows "\<exists>t. transaction_value_presents T t"
  by (rule transaction_values.total[OF formed])

theorem transaction_quotation_presentation_class:
  "presentation_class
    (composed_presentation transaction_value_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    transaction_formed
    (\<lambda>p. \<exists>t. (\<exists>T. transaction_value_presents T t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF transaction_value_presentation_class])
    (use transaction_value_presents_formed in blast)

theorem transaction_value_quotation_total:
  assumes "transaction_formed T"
  shows "\<exists>t C. transaction_value_presents T t \<and> complete_data_quoted_at C [] t"
proof -
  obtain t where present: "transaction_value_presents T t"
    using transaction_value_presents_total[OF assms] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using transaction_value_presents_formed[OF present] by auto
  show ?thesis using present complete_data_quotation_total[OF formed closed] by blast
qed

section \<open>The complete supplied context determines the transaction outcome\<close>

abbreviation transaction_context_presents ::
  "(selection_snapshot\<times>structural_transaction) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "transaction_context_presents z t \<equiv> factor_pair_presents snapshot_value_presents transaction_value_presents z t"

definition transaction_execution_presents ::
  "((selection_snapshot\<times>structural_transaction)\<times>transaction_result) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "transaction_execution_presents z t \<longleftrightarrow> transaction_context_presents (fst z) t \<and>
    transact (fst (fst z)) (snd (fst z)) (snd z)"

theorem transaction_execution_presentation_class:
  "presentation_class transaction_execution_presents
    (\<lambda>z. transact (fst (fst z)) (snd (fst z)) (snd z))
    (\<lambda>t. \<exists>z. transaction_context_presents z t)"
proof -
  let ?D="\<lambda>z. snapshot_formed (fst z) \<and> transaction_formed (snd z)"
  let ?A="\<lambda>t. \<exists>p q. (\<exists>S. snapshot_value_presents S p) \<and>
    (\<exists>T. transaction_value_presents T q) \<and> t=Pair_Term p q"
  interpret inputs: presentation_class transaction_context_presents ?D ?A
    by (rule factor_pair_class[OF snapshot_value_presentation_class transaction_value_presentation_class])
  have determined: "transact (fst z) (snd z) x \<Longrightarrow> transact (fst z) (snd z) y \<Longrightarrow> x=y" for z x y
    by (rule transaction_result_determined)
  have result: "presentation_class
      (\<lambda>z t. transaction_context_presents (fst z) t \<and> transact (fst (fst z)) (snd (fst z)) (snd z))
      (\<lambda>z. ?D (fst z) \<and> transact (fst (fst z)) (snd (fst z)) (snd z))
      (\<lambda>t. \<exists>z out. transaction_context_presents z t \<and> transact (fst z) (snd z) out)"
    by (rule presentation_class_determined[OF inputs.presentation_class_axioms determined])
  have domain: "(?D (fst z) \<and> transact (fst (fst z)) (snd (fst z)) (snd z)) \<longleftrightarrow>
      transact (fst (fst z)) (snd (fst z)) (snd z)" for z
    by (auto simp: transact_def)
  have admission: "(\<exists>z out. transaction_context_presents z t \<and> transact (fst z) (snd z) out) \<longleftrightarrow>
      (\<exists>z. transaction_context_presents z t)" for t
    using inputs.subject_boundary transaction_result_exists by blast
  show ?thesis using result by (simp only: presentation_class_def transaction_execution_presents_def domain admission)
qed

theorem transaction_execution_presented_outcome:
  assumes presented: "transaction_execution_presents ((S,T),out) t"
  shows "transact S T out"
    and "out=Applied U \<longrightarrow> comparison_passes S T \<and> U=transaction_update S T \<and>
      (\<forall>l. snapshot_lookup U l =
        (if l\<in>snapshot_loci (proposed_selected T) then snapshot_lookup (proposed_selected T) l
         else if l\<in>fset (proposed_absent T) then None else snapshot_lookup S l))"
    and "out=Conflict C \<longrightarrow> \<not>comparison_passes S T \<and>
      C=observed_comparison S T \<and> rel_dom C=comparison_loci T \<and>
      (\<forall>l\<in>comparison_loci T. (l,snapshot_lookup S l)\<in>C) \<and> finite C \<and>
      transaction_output out=None"
proof -
  have actual: "transact S T out" using presented by (simp add: transaction_execution_presents_def)
  show "transact S T out" by (rule actual)
  show "out=Applied U \<longrightarrow> comparison_passes S T \<and> U=transaction_update S T \<and>
      (\<forall>l. snapshot_lookup U l =
        (if l\<in>snapshot_loci (proposed_selected T) then snapshot_lookup (proposed_selected T) l
         else if l\<in>fset (proposed_absent T) then None else snapshot_lookup S l))"
    using actual successful_transaction_lookup by (auto simp: transact_applied_iff)
  show "out=Conflict C \<longrightarrow> \<not>comparison_passes S T \<and>
      C=observed_comparison S T \<and> rel_dom C=comparison_loci T \<and>
      (\<forall>l\<in>comparison_loci T. (l,snapshot_lookup S l)\<in>C) \<and> finite C \<and>
      transaction_output out=None"
    using actual conflict_contains_every_observation by (auto simp: transact_conflict_iff)
qed

text \<open>
  Snapshot data contains every exact selected core, including its recursive
  history. Transaction data keeps expected selections, expected absence,
  proposed selections, and proposed absence in four separate positions. Each
  finite collection admits every complete presentation. Equal presented data
  recovers the exact source fields, without asserting comparison success,
  continuation permission, cause validity, or authority.

  The value classes use the general finite-set, product, subdomain, and
  observation constructions. The original snapshot and transaction formation
  conditions remain their independent domains. Complete quotations use the
  same composition rule.

  Together with the supplied initial snapshot, these fields also determine
  the whole execution result. Its class recovers a successful update or the
  complete failed comparison, including every observed locus and value. No
  outcome field is added to the supplied transaction, and no conflict is
  presented as a partially applied update.
\<close>

end
