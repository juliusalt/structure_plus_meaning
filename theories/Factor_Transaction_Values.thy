theory Factor_Transaction_Values
  imports Factor_Generation_Values RRA_Transaction
begin

section \<open>Complete snapshot data retains the selected exact cores\<close>

definition snapshot_value_presents :: "selection_snapshot \<Rightarrow> factor_term \<Rightarrow> bool" where
  "snapshot_value_presents S t \<longleftrightarrow> snapshot_formed S \<and>
    data_collection_presents generation_value_presents (fset S) t"

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
proof -
  have left: "data_collection_presents generation_value_presents (fset S) t"
    and right: "data_collection_presents generation_value_presents (fset U) t"
    using first second by (auto simp: snapshot_value_presents_def)
  have "fset S=fset U" by (rule data_collection_presents_unique[OF left right])
    (rule generation_value_presents_unique; assumption)
  then show ?thesis by (simp add: fset_inject)
qed

theorem snapshot_value_presents_total:
  assumes formed: "snapshot_formed S"
  shows "\<exists>t. snapshot_value_presents S t"
proof -
  have cores: "\<forall>G\<in>fset S. generation_formed G"
    using formed by (simp add: snapshot_formed_def selection_formed_def)
  have each: "\<forall>G\<in>fset S. \<exists>t. generation_value_presents G t"
    using cores generation_value_presents_total by blast
  obtain t where "data_collection_presents generation_value_presents (fset S) t"
    using data_collection_presents_total[OF finite_fset each] by blast
  then show ?thesis using formed unfolding snapshot_value_presents_def by blast
qed

section \<open>The four independent transaction fields as ordinary data\<close>

definition transaction_value_presents :: "structural_transaction \<Rightarrow> factor_term \<Rightarrow> bool" where
  "transaction_value_presents T t \<longleftrightarrow> transaction_formed T \<and>
    (\<exists>a b c d. snapshot_value_presents (expected_selected T) a \<and>
      data_collection_presents target_value_presents (fset (expected_absent T)) b \<and>
      snapshot_value_presents (proposed_selected T) c \<and>
      data_collection_presents target_value_presents (fset (proposed_absent T)) d \<and>
      t=Pair_Term a (Pair_Term b (Pair_Term c d)))"

theorem transaction_value_presents_unique:
  assumes first: "transaction_value_presents S t" and second: "transaction_value_presents T t"
  shows "S=T"
proof -
  obtain a b c d where left: "snapshot_value_presents (expected_selected S) a"
    "data_collection_presents target_value_presents (fset (expected_absent S)) b"
    "snapshot_value_presents (proposed_selected S) c"
    "data_collection_presents target_value_presents (fset (proposed_absent S)) d"
    "t=Pair_Term a (Pair_Term b (Pair_Term c d))"
    using first unfolding transaction_value_presents_def by blast
  obtain a' b' c' d' where right: "snapshot_value_presents (expected_selected T) a'"
    "data_collection_presents target_value_presents (fset (expected_absent T)) b'"
    "snapshot_value_presents (proposed_selected T) c'"
    "data_collection_presents target_value_presents (fset (proposed_absent T)) d'"
    "t=Pair_Term a' (Pair_Term b' (Pair_Term c' d'))"
    using second unfolding transaction_value_presents_def by blast
  have same: "a'=a" "b'=b" "c'=c" "d'=d" using left(5) right(5) by simp_all
  have other: "snapshot_value_presents (expected_selected T) a"
    "data_collection_presents target_value_presents (fset (expected_absent T)) b"
    "snapshot_value_presents (proposed_selected T) c"
    "data_collection_presents target_value_presents (fset (proposed_absent T)) d"
    using right(1-4) same by simp_all
  have selected: "expected_selected S=expected_selected T" "proposed_selected S=proposed_selected T"
    by (rule snapshot_value_presents_unique[OF left(1) other(1)])
       (rule snapshot_value_presents_unique[OF left(3) other(3)])
  have absent: "fset (expected_absent S)=fset (expected_absent T)"
    by (rule data_collection_presents_unique[OF left(2) other(2)])
       (rule target_value_presents_unique; assumption)
  have removed: "fset (proposed_absent S)=fset (proposed_absent T)"
    by (rule data_collection_presents_unique[OF left(4) other(4)])
       (rule target_value_presents_unique; assumption)
  show ?thesis using selected absent removed by (simp add: structural_transaction_identity fset_inject)
qed

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
proof -
  have sf: "snapshot_formed (expected_selected T)" "snapshot_formed (proposed_selected T)"
    and absent: "\<forall>l\<in>fset (expected_absent T). target_formed l"
    and removed: "\<forall>l\<in>fset (proposed_absent T). target_formed l"
    using formed by (auto simp: transaction_formed_def)
  obtain a c where snapshots: "snapshot_value_presents (expected_selected T) a"
    "snapshot_value_presents (proposed_selected T) c"
    using snapshot_value_presents_total[OF sf(1)] snapshot_value_presents_total[OF sf(2)] by blast
  have each_absent: "\<forall>l\<in>fset (expected_absent T). \<exists>v. target_value_presents l v"
    using absent target_value_presents_total by blast
  have each_removed: "\<forall>l\<in>fset (proposed_absent T). \<exists>v. target_value_presents l v"
    using removed target_value_presents_total by blast
  obtain b where expected: "data_collection_presents target_value_presents (fset (expected_absent T)) b"
    using data_collection_presents_total[OF finite_fset each_absent] by blast
  obtain d where proposed: "data_collection_presents target_value_presents (fset (proposed_absent T)) d"
    using data_collection_presents_total[OF finite_fset each_removed] by blast
  show ?thesis using formed snapshots expected proposed unfolding transaction_value_presents_def by blast
qed

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

text \<open>
  Snapshot data contains every exact selected core, including its recursive
  history. Transaction data keeps expected selections, expected absence,
  proposed selections, and proposed absence in four separate positions. Each
  finite collection admits every complete presentation. Equal presented data
  recovers the exact source fields, without asserting comparison success,
  continuation permission, cause validity, or authority.
\<close>

end
