theory Factor_Dependency_Support
  imports Factor_Site_Values
begin

section \<open>One exact policy frame, a finite proof collection, and remaining material\<close>

definition dependency_support_presents ::
  "exact_artifact \<Rightarrow> exact_artifact set \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> factor_term \<Rightarrow> bool" where
  "dependency_support_presents D Rs N nu nr t \<longleftrightarrow>
    (\<exists>d rs n. artifact_value_presents D d \<and> data_collection_presents artifact_value_presents Rs rs \<and>
      site_value_presents N nu nr n \<and> t=Pair_Term (Pair_Term d rs) n)"

theorem dependency_support_presents_unique:
  assumes first: "dependency_support_presents D Rs N nu nr t"
    and second: "dependency_support_presents D' Rs' N' nu' nr' t"
  shows "D=D' \<and> Rs=Rs' \<and> N=N' \<and> nu=nu' \<and> nr=nr'"
proof -
  obtain d rs n where left: "artifact_value_presents D d" "data_collection_presents artifact_value_presents Rs rs"
    "site_value_presents N nu nr n" "t=Pair_Term (Pair_Term d rs) n"
    using first unfolding dependency_support_presents_def by blast
  obtain e ss m where right: "artifact_value_presents D' e" "data_collection_presents artifact_value_presents Rs' ss"
    "site_value_presents N' nu' nr' m" "t=Pair_Term (Pair_Term e ss) m"
    using second unfolding dependency_support_presents_def by blast
  have same: "e=d" "ss=rs" "m=n" using left(4) right(4) by simp_all
  have other: "artifact_value_presents D' d" "data_collection_presents artifact_value_presents Rs' rs"
    "site_value_presents N' nu' nr' n" using right(1-3) same by simp_all
  have collection: "Rs=Rs'"
    by (rule data_collection_presents_unique[OF left(2) other(2)])
       (rule artifact_value_presents_unique; assumption)
  show ?thesis using artifact_value_presents_unique[OF left(1) other(1)] collection
    site_value_presents_unique[OF left(3) other(3)] by blast
qed

lemma dependency_support_presents_formed:
  assumes present: "dependency_support_presents D Rs N nu nr t"
  shows "exact_formed D \<and> finite Rs \<and> (\<forall>R\<in>Rs. exact_formed R) \<and>
    environment_formed N \<and> (nu,nr)\<in>environment_positions N \<and>
    term_formed t \<and> self_contained_term t"
proof -
  obtain d rs n where fields: "artifact_value_presents D d" "data_collection_presents artifact_value_presents Rs rs"
    "site_value_presents N nu nr n" "t=Pair_Term (Pair_Term d rs) n"
    using present unfolding dependency_support_presents_def by blast
  have fin: "finite Rs" by (rule data_collection_presents_finite[OF fields(2)])
  have members: "\<forall>R\<in>Rs. exact_formed R"
    using data_collection_presents_sources[OF fields(2)] artifact_value_presents_formed by blast
  have tf: "term_formed rs"
    by (rule data_collection_presents_formed[OF fields(2)]) (meson artifact_value_presents_formed)
  have closed: "self_contained_term rs"
    by (rule data_collection_presents_self_contained[OF fields(2)]) (meson artifact_value_presents_formed)
  have site: "(nu,nr)\<in>environment_positions N" using fields(3) by (simp add: site_value_presents_def)
  show ?thesis using artifact_value_presents_formed[OF fields(1)] site_value_presents_formed[OF fields(3)]
    fin members tf closed site fields(4) by simp
qed

theorem dependency_support_presents_total:
  assumes df: "exact_formed D" and finite: "finite Rs" and rf: "\<forall>R\<in>Rs. exact_formed R"
    and nf: "environment_formed N" and site: "(nu,nr)\<in>environment_positions N"
  shows "\<exists>t. dependency_support_presents D Rs N nu nr t"
proof -
  obtain d where frame: "artifact_value_presents D d" using artifact_value_presents_total[OF df] by blast
  have each: "\<forall>R\<in>Rs. \<exists>t. artifact_value_presents R t" using rf artifact_value_presents_total by blast
  obtain rs where collection: "data_collection_presents artifact_value_presents Rs rs"
    using data_collection_presents_total[OF finite each] by blast
  obtain n where scope: "site_value_presents N nu nr n" using site_value_presents_total[OF nf site] by blast
  show ?thesis by (rule exI[of _ "Pair_Term (Pair_Term d rs) n"])
    (use frame collection scope in \<open>auto simp: dependency_support_presents_def\<close>)
qed

definition dependency_support_at ::
  "local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    exact_artifact \<Rightarrow> exact_artifact set \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "dependency_support_at M mu mr D Rs N nu nr \<longleftrightarrow> environment_formed M \<and>
    (\<exists>V t. artifact_at M mu V \<and> complete_data_quoted_at V mr t \<and>
      dependency_support_presents D Rs N nu nr t)"

theorem dependency_support_at_unique:
  assumes first: "dependency_support_at M mu mr D Rs N nu nr"
    and second: "dependency_support_at M mu mr D' Rs' N' nu' nr'"
  shows "D=D' \<and> Rs=Rs' \<and> N=N' \<and> nu=nu' \<and> nr=nr'"
proof -
  obtain V t where left: "environment_formed M" "artifact_at M mu V"
    "complete_data_quoted_at V mr t" "dependency_support_presents D Rs N nu nr t"
    using first unfolding dependency_support_at_def by blast
  obtain V' w where right: "artifact_at M mu V'" "complete_data_quoted_at V' mr w"
    "dependency_support_presents D' Rs' N' nu' nr' w"
    using second unfolding dependency_support_at_def by blast
  have artifact: "V'=V" using environment_artifact_unique[OF left(1,2) right(1)] by simp
  have same: "t=w" using complete_data_quotation_unique[OF left(3)] right(2) artifact by blast
  have other: "dependency_support_presents D' Rs' N' nu' nr' t" using right(3) same by simp
  show ?thesis by (rule dependency_support_presents_unique[OF left(4) other])
qed

lemma dependency_support_at_formed:
  assumes support: "dependency_support_at M mu mr D Rs N nu nr"
  shows "environment_formed M \<and> (mu,mr)\<in>environment_positions M \<and>
    exact_formed D \<and> finite Rs \<and> (\<forall>R\<in>Rs. exact_formed R) \<and>
    environment_formed N \<and> (nu,nr)\<in>environment_positions N"
proof -
  obtain V t where fields: "environment_formed M" "artifact_at M mu V"
    "complete_data_quoted_at V mr t" "dependency_support_presents D Rs N nu nr t"
    using support unfolding dependency_support_at_def by blast
  have anchor: "anchor_formed (V,mr)" by (rule complete_data_quotation_anchor[OF fields(3)])
  have site: "(mu,mr)\<in>environment_positions M" using fields(2) anchor by (auto simp: anchor_formed_def)
  show ?thesis using fields(1) site dependency_support_presents_formed[OF fields(4)] by blast
qed

theorem dependency_support_native:
  assumes support: "dependency_support_at M mu mr D Rs N nu nr"
  shows "\<exists>V t. artifact_at M mu V \<and> dependency_support_presents D Rs N nu nr t \<and>
    term_quoted_at M mu mr t (rra_carrier (object_structure V)) {}"
proof -
  obtain V t where fields: "environment_formed M" "artifact_at M mu V"
    "complete_data_quoted_at V mr t" "dependency_support_presents D Rs N nu nr t"
    using support unfolding dependency_support_at_def by blast
  have native: "term_quoted_at M mu mr t (rra_carrier (object_structure V)) {}"
    by (rule self_contained_quoted_in_environment[OF complete_data_quotation_native[OF fields(3)] fields(1,2)])
  show ?thesis using fields(2,4) native by blast
qed

theorem dependency_support_total:
  assumes "exact_formed D" "finite Rs" "\<forall>R\<in>Rs. exact_formed R"
    "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>M. dependency_support_at M None [] D Rs N nu nr"
proof -
  obtain t where present: "dependency_support_presents D Rs N nu nr t"
    using dependency_support_presents_total[OF assms] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using dependency_support_presents_formed[OF present] by auto
  have quote: "complete_data_quoted_at (term_syntax t) [] t"
    by (rule complete_data_quotation_total[OF formed closed])
  have artifact: "exact_formed (term_syntax t)" using complete_data_quotation_formed[OF quote] by blast
  let ?M="artifact_family_environment {None :: local_address option} (\<lambda>_. term_syntax t)"
  have mf: "environment_formed ?M" by (rule artifact_family_formed) (use artifact in auto)
  have source: "artifact_at ?M None (term_syntax t)" by simp
  show ?thesis using mf source quote present unfolding dependency_support_at_def by blast
qed

text \<open>
  The frame and finite collection contain exact complete artifact values.
  No subject keys, quotation roots, or second program fields are stored.
  Their later readers recover those fields from the actual artifacts.
  Every complete collection order and child presentation is admitted as data.

  Identical whole records occur once; different records may prove the same
  subject. The complete remaining scope has its own actual selected site.
  The whole native data reading uses no slots. Empty proof collections are
  formed data here; formation supplies neither proof validity nor coverage.
\<close>

end
