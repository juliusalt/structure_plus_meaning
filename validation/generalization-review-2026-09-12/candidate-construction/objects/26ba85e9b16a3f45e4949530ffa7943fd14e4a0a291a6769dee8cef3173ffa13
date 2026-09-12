theory Factor_Interpretation_Support
  imports Factor_Site_Values
begin

section \<open>Two relative entry coordinates and complete remaining material\<close>

definition interpretation_support_presents ::
  "(local_address option\<times>local_address) \<Rightarrow> (local_address option\<times>local_address) \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    factor_term \<Rightarrow> bool" where
  "interpretation_support_presents a b N nu nr t \<longleftrightarrow>
    octets_formed (snd a) \<and> octets_formed (snd b) \<and>
    (\<exists>n. site_value_presents N nu nr n \<and>
      t=Pair_Term (Pair_Term (site_data_term (fst a) (snd a)) (site_data_term (fst b) (snd b))) n)"

theorem interpretation_support_presents_unique:
  assumes first: "interpretation_support_presents a b N nu nr t"
    and second: "interpretation_support_presents c d L lu lr t"
  shows "a=c \<and> b=d \<and> N=L \<and> nu=lu \<and> nr=lr"
proof -
  obtain n where left: "site_value_presents N nu nr n"
    "t=Pair_Term (Pair_Term (site_data_term (fst a) (snd a)) (site_data_term (fst b) (snd b))) n"
    using first unfolding interpretation_support_presents_def by blast
  obtain m where right: "site_value_presents L lu lr m"
    "t=Pair_Term (Pair_Term (site_data_term (fst c) (snd c)) (site_data_term (fst d) (snd d))) m"
    using second unfolding interpretation_support_presents_def by blast
  have same: "a=c" "b=d" "n=m" using left(2) right(2) by (simp_all add: prod_eq_iff)
  have other: "site_value_presents L lu lr n" using right(1) same(3) by simp
  show ?thesis using same site_value_presents_unique[OF left(1) other] by blast
qed

lemma interpretation_support_presents_formed:
  assumes present: "interpretation_support_presents a b N nu nr t"
  shows "octets_formed (snd a) \<and> octets_formed (snd b) \<and>
    environment_formed N \<and> (nu,nr)\<in>environment_positions N \<and>
    term_formed t \<and> self_contained_term t"
proof -
  obtain n where parts: "octets_formed (snd a)" "octets_formed (snd b)" "site_value_presents N nu nr n"
    "t=Pair_Term (Pair_Term (site_data_term (fst a) (snd a)) (site_data_term (fst b) (snd b))) n"
    using present unfolding interpretation_support_presents_def by blast
  have site: "(nu,nr)\<in>environment_positions N" using parts(3) by (simp add: site_value_presents_def)
  show ?thesis using parts(1,2,4) site site_value_presents_formed[OF parts(3)] by simp
qed

theorem interpretation_support_presents_total:
  assumes "octets_formed (snd a)" "octets_formed (snd b)"
    "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>t. interpretation_support_presents a b N nu nr t"
  using site_value_presents_total[OF assms(3,4)] assms(1,2)
  unfolding interpretation_support_presents_def by blast

definition interpretation_support_at ::
  "local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    (local_address option\<times>local_address) \<Rightarrow> (local_address option\<times>local_address) \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "interpretation_support_at M mu mr a b N nu nr \<longleftrightarrow> environment_formed M \<and>
    (\<exists>V t. artifact_at M mu V \<and> complete_data_quoted_at V mr t \<and>
      interpretation_support_presents a b N nu nr t)"

theorem interpretation_support_at_unique:
  assumes first: "interpretation_support_at M mu mr a b N nu nr"
    and second: "interpretation_support_at M mu mr c d L lu lr"
  shows "a=c \<and> b=d \<and> N=L \<and> nu=lu \<and> nr=lr"
proof -
  obtain V t where left: "environment_formed M" "artifact_at M mu V" "complete_data_quoted_at V mr t"
    "interpretation_support_presents a b N nu nr t"
    using first unfolding interpretation_support_at_def by blast
  obtain W s where right: "artifact_at M mu W" "complete_data_quoted_at W mr s"
    "interpretation_support_presents c d L lu lr s"
    using second unfolding interpretation_support_at_def by blast
  have artifact: "W=V" using environment_artifact_unique[OF left(1,2) right(1)] by simp
  have same: "t=s" using complete_data_quotation_unique[OF left(3)] right(2) artifact by blast
  have other: "interpretation_support_presents c d L lu lr t" using right(3) same by simp
  show ?thesis by (rule interpretation_support_presents_unique[OF left(4) other])
qed

lemma interpretation_support_at_formed:
  assumes support: "interpretation_support_at M mu mr a b N nu nr"
  shows "environment_formed M \<and> (mu,mr)\<in>environment_positions M \<and>
    octets_formed (snd a) \<and> octets_formed (snd b) \<and>
    environment_formed N \<and> (nu,nr)\<in>environment_positions N"
proof -
  obtain V t where fields: "environment_formed M" "artifact_at M mu V" "complete_data_quoted_at V mr t"
    "interpretation_support_presents a b N nu nr t"
    using support unfolding interpretation_support_at_def by blast
  have anchor: "anchor_formed (V,mr)" by (rule complete_data_quotation_anchor[OF fields(3)])
  have site: "(mu,mr)\<in>environment_positions M" using fields(2) anchor by (auto simp: anchor_formed_def)
  show ?thesis using fields(1) site interpretation_support_presents_formed[OF fields(4)] by blast
qed

theorem interpretation_support_native:
  assumes support: "interpretation_support_at M mu mr a b N nu nr"
  shows "\<exists>V t. artifact_at M mu V \<and> interpretation_support_presents a b N nu nr t \<and>
    term_quoted_at M mu mr t (rra_carrier (object_structure V)) {}"
proof -
  obtain V t where fields: "environment_formed M" "artifact_at M mu V" "complete_data_quoted_at V mr t"
    "interpretation_support_presents a b N nu nr t"
    using support unfolding interpretation_support_at_def by blast
  have native: "term_quoted_at M mu mr t (rra_carrier (object_structure V)) {}"
    by (rule self_contained_quoted_in_environment[OF complete_data_quotation_native[OF fields(3)] fields(1,2)])
  show ?thesis using fields(2,4) native by blast
qed

theorem interpretation_support_total:
  assumes "octets_formed (snd a)" "octets_formed (snd b)"
    "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>M. interpretation_support_at M None [] a b N nu nr"
proof -
  obtain t where present: "interpretation_support_presents a b N nu nr t"
    using interpretation_support_presents_total[OF assms] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using interpretation_support_presents_formed[OF present] by auto
  have quote: "complete_data_quoted_at (term_syntax t) [] t"
    by (rule complete_data_quotation_total[OF formed closed])
  have artifact: "exact_formed (term_syntax t)" using complete_data_quotation_formed[OF quote] by blast
  let ?M="artifact_family_environment {None :: local_address option} (\<lambda>_. term_syntax t)"
  have mf: "environment_formed ?M" by (rule artifact_family_formed) (use artifact in auto)
  have source: "artifact_at ?M None (term_syntax t)" by simp
  show ?thesis using mf source quote present unfolding interpretation_support_at_def by blast
qed

text \<open>
  This complete value contains two coordinates relative to a separately fixed
  candidate scope. It stores no old or candidate program, environment, package
  root, truth relation, or authority frame. The two coordinates may coincide.
  Their byte formation alone does not make them actual definition sites.

  The complete remaining environment and its actual selected site are retained
  once. Every native data reading covers the whole source without external
  slots. Higher interpretation and transition profiles must supply the exact
  scopes and establish the meaning of the selected entries.
\<close>

end
