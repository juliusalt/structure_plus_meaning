theory Factor_Assembly_Support
  imports Factor_Transition_Values
begin

section \<open>Two exact artifacts and the remaining complete supporting scope\<close>

definition assembly_support_presents ::
  "exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> factor_term \<Rightarrow> bool" where
  "assembly_support_presents D R N nu nr t \<longleftrightarrow>
    (\<exists>a n. artifact_pair_presents D R a \<and> site_value_presents N nu nr n \<and> t=Pair_Term a n)"

theorem assembly_support_presents_unique:
  assumes first: "assembly_support_presents D R N nu nr t"
    and second: "assembly_support_presents D' R' N' nu' nr' t"
  shows "D=D' \<and> R=R' \<and> N=N' \<and> nu=nu' \<and> nr=nr'"
proof -
  obtain a n where left: "artifact_pair_presents D R a" "site_value_presents N nu nr n" "t=Pair_Term a n"
    using first unfolding assembly_support_presents_def by blast
  obtain b m where right: "artifact_pair_presents D' R' b" "site_value_presents N' nu' nr' m" "t=Pair_Term b m"
    using second unfolding assembly_support_presents_def by blast
  have same: "b=a" "m=n" using left(3) right(3) by simp_all
  have other: "artifact_pair_presents D' R' a" "site_value_presents N' nu' nr' n"
    using right(1,2) same by simp_all
  show ?thesis using artifact_pair_presents_unique[OF left(1) other(1)]
    site_value_presents_unique[OF left(2) other(2)] by blast
qed

lemma assembly_support_presents_formed:
  assumes present: "assembly_support_presents D R N nu nr t"
  shows "exact_formed D \<and> exact_formed R \<and> environment_formed N \<and>
    (nu,nr)\<in>environment_positions N \<and> term_formed t \<and> self_contained_term t"
proof -
  obtain a n where fields: "artifact_pair_presents D R a" "site_value_presents N nu nr n" "t=Pair_Term a n"
    using present unfolding assembly_support_presents_def by blast
  have site: "(nu,nr)\<in>environment_positions N" using fields(2) by (simp add: site_value_presents_def)
  show ?thesis using artifact_pair_presents_formed[OF fields(1)]
    site_value_presents_formed[OF fields(2)] site fields(3) by simp
qed

theorem assembly_support_presents_total:
  assumes "exact_formed D" "exact_formed R" "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>t. assembly_support_presents D R N nu nr t"
  using artifact_pair_presents_total[OF assms(1,2)] site_value_presents_total[OF assms(3,4)]
  unfolding assembly_support_presents_def by blast

definition assembly_support_at ::
  "local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "assembly_support_at M mu mr D R N nu nr \<longleftrightarrow> environment_formed M \<and>
    (\<exists>V t. artifact_at M mu V \<and> complete_data_quoted_at V mr t \<and>
      assembly_support_presents D R N nu nr t)"

theorem assembly_support_at_unique:
  assumes first: "assembly_support_at M mu mr D R N nu nr"
    and second: "assembly_support_at M mu mr D' R' N' nu' nr'"
  shows "D=D' \<and> R=R' \<and> N=N' \<and> nu=nu' \<and> nr=nr'"
proof -
  obtain V t where left: "environment_formed M" "artifact_at M mu V"
    "complete_data_quoted_at V mr t" "assembly_support_presents D R N nu nr t"
    using first unfolding assembly_support_at_def by blast
  obtain V' w where right: "artifact_at M mu V'" "complete_data_quoted_at V' mr w"
    "assembly_support_presents D' R' N' nu' nr' w"
    using second unfolding assembly_support_at_def by blast
  have artifact: "V'=V" using environment_artifact_unique[OF left(1,2) right(1)] by simp
  have same: "t=w" using complete_data_quotation_unique[OF left(3)] right(2) artifact by blast
  have other: "assembly_support_presents D' R' N' nu' nr' t" using right(3) same by simp
  show ?thesis by (rule assembly_support_presents_unique[OF left(4) other])
qed

lemma assembly_support_at_formed:
  assumes support: "assembly_support_at M mu mr D R N nu nr"
  shows "environment_formed M \<and> (mu,mr)\<in>environment_positions M \<and>
    exact_formed D \<and> exact_formed R \<and> environment_formed N \<and> (nu,nr)\<in>environment_positions N"
proof -
  obtain V t where fields: "environment_formed M" "artifact_at M mu V"
    "complete_data_quoted_at V mr t" "assembly_support_presents D R N nu nr t"
    using support unfolding assembly_support_at_def by blast
  have anchor: "anchor_formed (V,mr)" by (rule complete_data_quotation_anchor[OF fields(3)])
  have site: "(mu,mr)\<in>environment_positions M" using fields(2) anchor by (auto simp: anchor_formed_def)
  show ?thesis using fields(1) site assembly_support_presents_formed[OF fields(4)] by blast
qed

theorem assembly_support_native:
  assumes support: "assembly_support_at M mu mr D R N nu nr"
  shows "\<exists>V t. artifact_at M mu V \<and> assembly_support_presents D R N nu nr t \<and>
    term_quoted_at M mu mr t (rra_carrier (object_structure V)) {}"
proof -
  obtain V t where fields: "environment_formed M" "artifact_at M mu V"
    "complete_data_quoted_at V mr t" "assembly_support_presents D R N nu nr t"
    using support unfolding assembly_support_at_def by blast
  have native: "term_quoted_at M mu mr t (rra_carrier (object_structure V)) {}"
    by (rule self_contained_quoted_in_environment[OF complete_data_quotation_native[OF fields(3)] fields(1,2)])
  show ?thesis using fields(2,4) native by blast
qed

theorem assembly_support_total:
  assumes "exact_formed D" "exact_formed R" "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>M. assembly_support_at M None [] D R N nu nr"
proof -
  obtain t where present: "assembly_support_presents D R N nu nr t"
    using assembly_support_presents_total[OF assms] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using assembly_support_presents_formed[OF present] by auto
  have quote: "complete_data_quoted_at (term_syntax t) [] t"
    by (rule complete_data_quotation_total[OF formed closed])
  have artifact: "exact_formed (term_syntax t)" using complete_data_quotation_formed[OF quote] by blast
  let ?M="artifact_family_environment {None :: local_address option} (\<lambda>_. term_syntax t)"
  have mf: "environment_formed ?M" by (rule artifact_family_formed) (use artifact in auto)
  have source: "artifact_at ?M None (term_syntax t)" by simp
  show ?thesis using mf source quote present unfolding assembly_support_at_def by blast
qed

text \<open>
  This value stores two complete exact artifacts and one complete remaining
  scope with an actual site. Higher readers use the artifacts as a construction
  frame and its proof. Their whole structure determines their quotation roots;
  the construction account and candidate are not copied into this value.

  Every complete presentation is admitted as data. The native reading covers
  the whole source artifact and uses no slots. Formation and unique recovery
  establish no currentness, construction validity, historical relation, or
  acceptance. The remaining scope still needs its own complete admission.
\<close>

end
