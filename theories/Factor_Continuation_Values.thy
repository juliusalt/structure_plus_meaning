theory Factor_Continuation_Values
  imports Factor_Transaction_Values Factor_Site_Values
begin

section \<open>Before, proposal, claimed after, and complete submitted material\<close>

definition continuation_value_presents ::
  "selection_snapshot \<Rightarrow> structural_transaction \<Rightarrow> selection_snapshot \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    factor_term \<Rightarrow> bool" where
  "continuation_value_presents S T U C cu cr t \<longleftrightarrow>
    (\<exists>s v w c. snapshot_value_presents S s \<and> transaction_value_presents T v \<and>
      snapshot_value_presents U w \<and> site_value_presents C cu cr c \<and>
      t=Pair_Term s (Pair_Term v (Pair_Term w c)))"

theorem continuation_value_presents_unique:
  assumes first: "continuation_value_presents S T U C cu cr t"
    and second: "continuation_value_presents V W X D du dr t"
  shows "S=V \<and> T=W \<and> U=X \<and> C=D \<and> cu=du \<and> cr=dr"
proof -
  obtain s v w c where left: "snapshot_value_presents S s" "transaction_value_presents T v"
    "snapshot_value_presents U w" "site_value_presents C cu cr c"
    "t=Pair_Term s (Pair_Term v (Pair_Term w c))"
    using first unfolding continuation_value_presents_def by blast
  obtain s' v' w' c' where right: "snapshot_value_presents V s'" "transaction_value_presents W v'"
    "snapshot_value_presents X w'" "site_value_presents D du dr c'"
    "t=Pair_Term s' (Pair_Term v' (Pair_Term w' c'))"
    using second unfolding continuation_value_presents_def by blast
  have same: "s'=s" "v'=v" "w'=w" "c'=c" using left(5) right(5) by simp_all
  have other: "snapshot_value_presents V s" "transaction_value_presents W v"
    "snapshot_value_presents X w" "site_value_presents D du dr c"
    using right(1-4) same by simp_all
  show ?thesis using snapshot_value_presents_unique[OF left(1) other(1)]
    transaction_value_presents_unique[OF left(2) other(2)]
    snapshot_value_presents_unique[OF left(3) other(3)] site_value_presents_unique[OF left(4) other(4)] by blast
qed

lemma continuation_value_presents_formed:
  assumes present: "continuation_value_presents S T U C cu cr t"
  shows "snapshot_formed S \<and> transaction_formed T \<and> snapshot_formed U \<and>
    environment_formed C \<and> (cu,cr)\<in>environment_positions C \<and>
    term_formed t \<and> self_contained_term t"
proof -
  obtain s v w c where fields: "snapshot_value_presents S s" "transaction_value_presents T v"
    "snapshot_value_presents U w" "site_value_presents C cu cr c"
    "t=Pair_Term s (Pair_Term v (Pair_Term w c))"
    using present unfolding continuation_value_presents_def by blast
  have site: "(cu,cr)\<in>environment_positions C" using fields(4) by (simp add: site_value_presents_def)
  show ?thesis using snapshot_value_presents_formed[OF fields(1)]
    transaction_value_presents_formed[OF fields(2)] snapshot_value_presents_formed[OF fields(3)]
    site_value_presents_formed[OF fields(4)] fields(5) site by simp
qed

lemma continuation_value_is_pair:
  assumes "continuation_value_presents S T U C cu cr t"
  shows "\<exists>a b. t=Pair_Term a b"
  using assms unfolding continuation_value_presents_def by blast

theorem continuation_value_presents_total:
  assumes before: "snapshot_formed S" and proposal: "transaction_formed T"
    and after: "snapshot_formed U" and material: "environment_formed C"
    and site: "(cu,cr)\<in>environment_positions C"
  shows "\<exists>t. continuation_value_presents S T U C cu cr t"
proof -
  obtain s v w c where fields: "snapshot_value_presents S s" "transaction_value_presents T v"
    "snapshot_value_presents U w" "site_value_presents C cu cr c"
    using snapshot_value_presents_total[OF before] transaction_value_presents_total[OF proposal]
      snapshot_value_presents_total[OF after] site_value_presents_total[OF material site] by blast
  show ?thesis using fields unfolding continuation_value_presents_def by blast
qed

theorem continuation_value_quotation_total:
  assumes "snapshot_formed S" "transaction_formed T" "snapshot_formed U"
    "environment_formed C" "(cu,cr)\<in>environment_positions C"
  shows "\<exists>t R. continuation_value_presents S T U C cu cr t \<and> complete_data_quoted_at R [] t"
proof -
  obtain t where present: "continuation_value_presents S T U C cu cr t"
    using continuation_value_presents_total[OF assms] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using continuation_value_presents_formed[OF present] by auto
  show ?thesis using present complete_data_quotation_total[OF formed closed] by blast
qed

text \<open>
  The claimed after snapshot is supplied independently. The advancement join
  checks it against the structural transaction result. Complete submitted
  material includes an actual site and its entire finite environment, so an
  ordinary program may inspect its structure and bindings. The site has no
  built-in evidence grammar or truth. Each policy must state what it requires.

  Histories remain in exact cores. Construction input occurrences and semantic
  dependencies can be inspected in their own supplied records and scopes;
  this argument imposes no equation between those boundaries. Complete data
  quotation introduces no external binding into their recovery.
\<close>

end
