theory Factor_Transition_Values
  imports Factor_Site_Values
begin

section \<open>Two exact artifacts as complete data\<close>

definition artifact_pair_presents ::
  "exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> factor_term \<Rightarrow> bool" where
  "artifact_pair_presents D R t \<longleftrightarrow>
    (\<exists>a b. artifact_value_presents D a \<and> artifact_value_presents R b \<and> t=Pair_Term a b)"

theorem artifact_pair_presents_unique:
  assumes first: "artifact_pair_presents D R t" and second: "artifact_pair_presents E S t"
  shows "D=E \<and> R=S"
proof -
  obtain a b where left: "artifact_value_presents D a" "artifact_value_presents R b" "t=Pair_Term a b"
    using first unfolding artifact_pair_presents_def by blast
  obtain c d where right: "artifact_value_presents E c" "artifact_value_presents S d" "t=Pair_Term c d"
    using second unfolding artifact_pair_presents_def by blast
  have same: "c=a" "d=b" using left(3) right(3) by simp_all
  have other: "artifact_value_presents E a" "artifact_value_presents S b" using right(1,2) same by simp_all
  show ?thesis using artifact_value_presents_unique[OF left(1) other(1)]
    artifact_value_presents_unique[OF left(2) other(2)] by blast
qed

lemma artifact_pair_presents_formed:
  assumes "artifact_pair_presents D R t"
  shows "exact_formed D \<and> exact_formed R \<and> term_formed t \<and> self_contained_term t"
  using assms artifact_value_presents_formed unfolding artifact_pair_presents_def by fastforce

theorem artifact_pair_presents_total:
  assumes "exact_formed D" "exact_formed R"
  shows "\<exists>t. artifact_pair_presents D R t"
  using artifact_value_presents_total[OF assms(1)] artifact_value_presents_total[OF assms(2)]
  unfolding artifact_pair_presents_def by blast

definition artifact_pair_quoted_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "artifact_pair_quoted_at K k D R \<longleftrightarrow>
    (\<exists>t. artifact_pair_presents D R t \<and> complete_data_quoted_at K k t)"

theorem artifact_pair_whole_unique:
  assumes first: "artifact_pair_quoted_at K k D R" and second: "artifact_pair_quoted_at K a E S"
  shows "k=a \<and> D=E \<and> R=S"
proof -
  obtain t where left: "artifact_pair_presents D R t" "complete_data_quoted_at K k t"
    using first unfolding artifact_pair_quoted_at_def by blast
  obtain v where right: "artifact_pair_presents E S v" "complete_data_quoted_at K a v"
    using second unfolding artifact_pair_quoted_at_def by blast
  have same: "k=a \<and> t=v" by (rule complete_data_quotation_whole_unique[OF left(2) right(2)])
  have other: "artifact_pair_presents E S t" using right(1) same by simp
  show ?thesis using same artifact_pair_presents_unique[OF left(1) other] by blast
qed

lemma artifact_pair_quoted_formed:
  assumes "artifact_pair_quoted_at K k D R"
  shows "exact_formed K \<and> exact_formed D \<and> exact_formed R"
  using assms artifact_pair_presents_formed complete_data_quotation_formed
  unfolding artifact_pair_quoted_at_def by blast

theorem artifact_pair_quoted_total:
  assumes "exact_formed D" "exact_formed R"
  shows "\<exists>K. artifact_pair_quoted_at K [] D R"
proof -
  obtain t where present: "artifact_pair_presents D R t" using artifact_pair_presents_total[OF assms] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using artifact_pair_presents_formed[OF present] by auto
  show ?thesis using present complete_data_quotation_total[OF formed closed]
    unfolding artifact_pair_quoted_at_def by blast
qed

theorem artifact_pair_quoted_in_environment:
  assumes quote: "artifact_pair_quoted_at K k D R"
    and formed: "environment_formed F" and source: "artifact_at F u K"
  shows "\<exists>t. artifact_pair_presents D R t \<and>
    term_quoted_at F u k t (rra_carrier (object_structure K)) {}"
proof -
  obtain t where present: "artifact_pair_presents D R t" and full: "complete_data_quoted_at K k t"
    using quote unfolding artifact_pair_quoted_at_def by blast
  have native: "term_quoted_at F u k t (rra_carrier (object_structure K)) {}"
    by (rule self_contained_quoted_in_environment[OF complete_data_quotation_native[OF full] formed source])
  show ?thesis using present native by blast
qed

section \<open>An exact proposed frame and complete supporting material\<close>

definition successor_material_presents ::
  "exact_artifact \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> factor_term \<Rightarrow> bool" where
  "successor_material_presents X M mu mr t \<longleftrightarrow>
    (\<exists>x m. artifact_value_presents X x \<and> site_value_presents M mu mr m \<and> t=Pair_Term x m)"

theorem successor_material_presents_unique:
  assumes first: "successor_material_presents X M mu mr t"
    and second: "successor_material_presents Y N nu nr t"
  shows "X=Y \<and> M=N \<and> mu=nu \<and> mr=nr"
proof -
  obtain x m where left: "artifact_value_presents X x" "site_value_presents M mu mr m" "t=Pair_Term x m"
    using first unfolding successor_material_presents_def by blast
  obtain y n where right: "artifact_value_presents Y y" "site_value_presents N nu nr n" "t=Pair_Term y n"
    using second unfolding successor_material_presents_def by blast
  have same: "y=x" "n=m" using left(3) right(3) by simp_all
  have other: "artifact_value_presents Y x" "site_value_presents N nu nr m" using right(1,2) same by simp_all
  show ?thesis using artifact_value_presents_unique[OF left(1) other(1)]
    site_value_presents_unique[OF left(2) other(2)] by blast
qed

lemma successor_material_presents_formed:
  assumes present: "successor_material_presents X M mu mr t"
  shows "exact_formed X \<and> environment_formed M \<and> (mu,mr)\<in>environment_positions M \<and>
    term_formed t \<and> self_contained_term t"
proof -
  obtain x m where fields: "artifact_value_presents X x" "site_value_presents M mu mr m" "t=Pair_Term x m"
    using present unfolding successor_material_presents_def by blast
  have site: "(mu,mr)\<in>environment_positions M" using fields(2) by (simp add: site_value_presents_def)
  show ?thesis using artifact_value_presents_formed[OF fields(1)]
    site_value_presents_formed[OF fields(2)] site fields(3) by simp
qed

theorem successor_material_presents_total:
  assumes "exact_formed X" "environment_formed M" "(mu,mr)\<in>environment_positions M"
  shows "\<exists>t. successor_material_presents X M mu mr t"
  using artifact_value_presents_total[OF assms(1)] site_value_presents_total[OF assms(2,3)]
  unfolding successor_material_presents_def by blast

definition successor_material_at ::
  "local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    exact_artifact \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "successor_material_at B bu br X M mu mr \<longleftrightarrow>
    environment_formed B \<and>
    (\<exists>V t. artifact_at B bu V \<and> complete_data_quoted_at V br t \<and>
      successor_material_presents X M mu mr t)"

theorem successor_material_at_unique:
  assumes first: "successor_material_at B bu br X M mu mr"
    and second: "successor_material_at B bu br Y N nu nr"
  shows "X=Y \<and> M=N \<and> mu=nu \<and> mr=nr"
proof -
  obtain V t where left: "environment_formed B" "artifact_at B bu V"
    "complete_data_quoted_at V br t" "successor_material_presents X M mu mr t"
    using first unfolding successor_material_at_def by blast
  obtain W v where right: "artifact_at B bu W" "complete_data_quoted_at W br v"
    "successor_material_presents Y N nu nr v"
    using second unfolding successor_material_at_def by blast
  have artifacts: "W=V" using environment_artifact_unique[OF left(1,2) right(1)] by simp
  have same: "t=v" using complete_data_quotation_unique[OF left(3)] right(2) artifacts by blast
  have other: "successor_material_presents Y N nu nr t" using right(3) same by simp
  show ?thesis by (rule successor_material_presents_unique[OF left(4) other])
qed

lemma successor_material_at_formed:
  assumes body: "successor_material_at B bu br X M mu mr"
  shows "environment_formed B \<and> (bu,br)\<in>environment_positions B \<and>
    exact_formed X \<and> environment_formed M \<and> (mu,mr)\<in>environment_positions M"
proof -
  obtain V t where fields: "environment_formed B" "artifact_at B bu V"
    "complete_data_quoted_at V br t" "successor_material_presents X M mu mr t"
    using body unfolding successor_material_at_def by blast
  have anchor: "anchor_formed (V,br)" by (rule complete_data_quotation_anchor[OF fields(3)])
  have site: "(bu,br)\<in>environment_positions B" using fields(2) anchor by (auto simp: anchor_formed_def)
  show ?thesis using fields(1) site successor_material_presents_formed[OF fields(4)] by blast
qed

theorem successor_material_native:
  assumes body: "successor_material_at B bu br X M mu mr"
  shows "\<exists>V t. artifact_at B bu V \<and> successor_material_presents X M mu mr t \<and>
    term_quoted_at B bu br t (rra_carrier (object_structure V)) {}"
proof -
  obtain V t where fields: "environment_formed B" "artifact_at B bu V"
    "complete_data_quoted_at V br t" "successor_material_presents X M mu mr t"
    using body unfolding successor_material_at_def by blast
  have native: "term_quoted_at B bu br t (rra_carrier (object_structure V)) {}"
    by (rule self_contained_quoted_in_environment[OF complete_data_quotation_native[OF fields(3)] fields(1,2)])
  show ?thesis using fields(2,4) native by blast
qed

theorem successor_material_total:
  assumes "exact_formed X" "environment_formed M" "(mu,mr)\<in>environment_positions M"
  shows "\<exists>B. successor_material_at B None [] X M mu mr"
proof -
  obtain t where present: "successor_material_presents X M mu mr t"
    using successor_material_presents_total[OF assms] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using successor_material_presents_formed[OF present] by auto
  have quote: "complete_data_quoted_at (term_syntax t) [] t"
    by (rule complete_data_quotation_total[OF formed closed])
  have artifact: "exact_formed (term_syntax t)" using complete_data_quotation_formed[OF quote] by blast
  let ?B="artifact_family_environment {None :: local_address option} (\<lambda>_. term_syntax t)"
  have bf: "environment_formed ?B" by (rule artifact_family_formed) (use artifact in auto)
  have source: "artifact_at ?B None (term_syntax t)" by simp
  show ?thesis using bf source quote present unfolding successor_material_at_def by blast
qed

text \<open>
  Both values use existing complete artifact and environment presentations.
  They admit every complete enumeration and every formed readdressing of the
  whole data quotation. Each actual value uniquely recovers all its fields.
  Its native reading uses the complete source carrier and no external slots.

  The two-artifact value will retain a continuation frame and replay record.
  The other value retains an exact proposed frame and one complete supporting
  scope with an actual site. The frame's quotation root and the supporting
  material's semantic fields are recovered by their later readers. None of
  these data conditions establishes currentness, proof validity, permission,
  or completeness of an amendment certificate.
\<close>

end
