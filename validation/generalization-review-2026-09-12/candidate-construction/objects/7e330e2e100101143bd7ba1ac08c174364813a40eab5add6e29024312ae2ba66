theory Factor_Comparison_Support
  imports Factor_Program_Entry_Values
begin

section \<open>A finite structural correspondence retains both optional endpoints\<close>

type_synonym comparison_correspondence =
  "((local_address option\<times>local_address) option\<times>(local_address option\<times>local_address) option) set"

fun optional_site_data_term :: "(local_address option\<times>local_address) option \<Rightarrow> factor_term" where
  "optional_site_data_term None=Payload_Term []"
| "optional_site_data_term (Some d)=site_data_term (fst d) (snd d)"

lemma optional_site_data_term_eq [simp]:
  "optional_site_data_term d=optional_site_data_term e \<longleftrightarrow> d=e"
  by (cases d; cases e) (auto simp: site_data_term_def prod_eq_iff dest: injD[OF use_data_term_injective])

lemma optional_site_data_term_formed [simp]:
  "term_formed (optional_site_data_term d) \<longleftrightarrow>
    (case d of None \<Rightarrow> True | Some a \<Rightarrow> octets_formed (snd a))"
  by (cases d) (simp_all add: octets_formed_def)

lemma optional_site_data_term_self_contained [simp]:
  "self_contained_term (optional_site_data_term d)"
  by (cases d) simp_all

definition correspondence_row_data ::
  "((local_address option\<times>local_address) option\<times>(local_address option\<times>local_address) option) \<Rightarrow>
    factor_term" where
  "correspondence_row_data z=Pair_Term (optional_site_data_term (fst z)) (optional_site_data_term (snd z))"

lemma correspondence_row_data_eq [simp]:
  "correspondence_row_data x=correspondence_row_data y \<longleftrightarrow> x=y"
  by (simp add: correspondence_row_data_def prod_eq_iff)

lemma correspondence_row_data_self_contained [simp]:
  "self_contained_term (correspondence_row_data z)"
  by (simp add: correspondence_row_data_def)

definition correspondence_value_presents :: "comparison_correspondence \<Rightarrow> factor_term \<Rightarrow> bool" where
  "correspondence_value_presents W t \<longleftrightarrow>
    data_collection_presents (\<lambda>z v. v=correspondence_row_data z) W t \<and> term_formed t"

theorem correspondence_value_presents_unique:
  assumes "correspondence_value_presents W t" "correspondence_value_presents V t"
  shows "W=V"
  by (rule data_collection_presents_unique[OF assms(1,2)[unfolded correspondence_value_presents_def, THEN conjunct1]])
     auto

lemma correspondence_value_presents_formed:
  assumes present: "correspondence_value_presents W t"
  shows "finite W \<and> term_formed t \<and> self_contained_term t"
proof -
  have collection: "data_collection_presents (\<lambda>z v. v=correspondence_row_data z) W t"
    and formed: "term_formed t" using present by (auto simp: correspondence_value_presents_def)
  have finite: "finite W" by (rule data_collection_presents_finite[OF collection])
  have closed: "self_contained_term t"
    by (rule data_collection_presents_self_contained[OF collection]) simp
  show ?thesis using finite formed closed by blast
qed

theorem correspondence_value_presents_total:
  assumes finite: "finite W" and rows: "\<And>z. z\<in>W \<Longrightarrow> term_formed (correspondence_row_data z)"
  shows "\<exists>t. correspondence_value_presents W t"
proof -
  have each: "\<forall>z\<in>W. \<exists>t. t=correspondence_row_data z" by simp
  obtain t where collection: "data_collection_presents (\<lambda>z v. v=correspondence_row_data z) W t"
    using data_collection_presents_total[OF finite each] by blast
  have formed: "term_formed t"
    by (rule data_collection_presents_formed[OF collection]) (use rows in auto)
  show ?thesis using collection formed unfolding correspondence_value_presents_def by blast
qed

section \<open>Correspondence, reporter selection, and complete remaining material\<close>

definition comparison_support_presents ::
  "comparison_correspondence \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> (local_address option\<times>local_address) \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    factor_term \<Rightarrow> bool" where
  "comparison_support_presents W E u r d N nu nr t \<longleftrightarrow>
    (\<exists>w e n. correspondence_value_presents W w \<and> program_entry_value_presents E u r d e \<and>
      site_value_presents N nu nr n \<and> t=Pair_Term (Pair_Term w e) n)"

theorem comparison_support_presents_unique:
  assumes first: "comparison_support_presents W E u r d N nu nr t"
    and second: "comparison_support_presents V F v s e L lu lr t"
  shows "W=V \<and> E=F \<and> u=v \<and> r=s \<and> d=e \<and> N=L \<and> nu=lu \<and> nr=lr"
proof -
  obtain w a n where left: "correspondence_value_presents W w" "program_entry_value_presents E u r d a"
    "site_value_presents N nu nr n" "t=Pair_Term (Pair_Term w a) n"
    using first unfolding comparison_support_presents_def by blast
  obtain z b m where right: "correspondence_value_presents V z" "program_entry_value_presents F v s e b"
    "site_value_presents L lu lr m" "t=Pair_Term (Pair_Term z b) m"
    using second unfolding comparison_support_presents_def by blast
  have same: "z=w" "b=a" "m=n" using left(4) right(4) by simp_all
  have other: "correspondence_value_presents V w" "program_entry_value_presents F v s e a"
    "site_value_presents L lu lr n" using right(1-3) same by simp_all
  show ?thesis using correspondence_value_presents_unique[OF left(1) other(1)]
    program_entry_value_presents_unique[OF left(2) other(2)] site_value_presents_unique[OF left(3) other(3)] by blast
qed

lemma comparison_support_presents_formed:
  assumes present: "comparison_support_presents W E u r d N nu nr t"
  shows "finite W \<and> environment_formed E \<and> (u,r)\<in>environment_positions E \<and>
    d\<in>environment_positions E \<and> environment_formed N \<and> (nu,nr)\<in>environment_positions N \<and>
    term_formed t \<and> self_contained_term t"
proof -
  obtain w e n where fields: "correspondence_value_presents W w" "program_entry_value_presents E u r d e"
    "site_value_presents N nu nr n" "t=Pair_Term (Pair_Term w e) n"
    using present unfolding comparison_support_presents_def by blast
  have site: "(nu,nr)\<in>environment_positions N" using fields(3) by (simp add: site_value_presents_def)
  show ?thesis using correspondence_value_presents_formed[OF fields(1)]
    program_entry_value_presents_formed[OF fields(2)] site_value_presents_formed[OF fields(3)] site fields(4) by simp
qed

theorem comparison_support_presents_total:
  assumes "finite W" "\<And>z. z\<in>W \<Longrightarrow> term_formed (correspondence_row_data z)"
    "environment_formed E" "(u,r)\<in>environment_positions E" "d\<in>environment_positions E"
    "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>t. comparison_support_presents W E u r d N nu nr t"
  using correspondence_value_presents_total[OF assms(1,2)]
    program_entry_value_presents_total[OF assms(3-5)] site_value_presents_total[OF assms(6,7)]
  unfolding comparison_support_presents_def by blast

definition comparison_support_at ::
  "local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    comparison_correspondence \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> (local_address option\<times>local_address) \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "comparison_support_at M mu mr W E u r d N nu nr \<longleftrightarrow> environment_formed M \<and>
    (\<exists>V t. artifact_at M mu V \<and> complete_data_quoted_at V mr t \<and>
      comparison_support_presents W E u r d N nu nr t)"

theorem comparison_support_at_unique:
  assumes first: "comparison_support_at M mu mr W E u r d N nu nr"
    and second: "comparison_support_at M mu mr V F v s e L lu lr"
  shows "W=V \<and> E=F \<and> u=v \<and> r=s \<and> d=e \<and> N=L \<and> nu=lu \<and> nr=lr"
proof -
  obtain A t where left: "environment_formed M" "artifact_at M mu A" "complete_data_quoted_at A mr t"
    "comparison_support_presents W E u r d N nu nr t"
    using first unfolding comparison_support_at_def by blast
  obtain B a where right: "artifact_at M mu B" "complete_data_quoted_at B mr a"
    "comparison_support_presents V F v s e L lu lr a"
    using second unfolding comparison_support_at_def by blast
  have artifact: "B=A" using environment_artifact_unique[OF left(1,2) right(1)] by simp
  have same: "t=a" using complete_data_quotation_unique[OF left(3)] right(2) artifact by blast
  have other: "comparison_support_presents V F v s e L lu lr t" using right(3) same by simp
  show ?thesis by (rule comparison_support_presents_unique[OF left(4) other])
qed

lemma comparison_support_at_formed:
  assumes support: "comparison_support_at M mu mr W E u r d N nu nr"
  shows "environment_formed M \<and> (mu,mr)\<in>environment_positions M \<and> finite W \<and>
    environment_formed E \<and> (u,r)\<in>environment_positions E \<and> d\<in>environment_positions E \<and>
    environment_formed N \<and> (nu,nr)\<in>environment_positions N"
proof -
  obtain V t where fields: "environment_formed M" "artifact_at M mu V" "complete_data_quoted_at V mr t"
    "comparison_support_presents W E u r d N nu nr t"
    using support unfolding comparison_support_at_def by blast
  have anchor: "anchor_formed (V,mr)" by (rule complete_data_quotation_anchor[OF fields(3)])
  have site: "(mu,mr)\<in>environment_positions M" using fields(2) anchor by (auto simp: anchor_formed_def)
  show ?thesis using fields(1) site comparison_support_presents_formed[OF fields(4)] by blast
qed

theorem comparison_support_native:
  assumes support: "comparison_support_at M mu mr W E u r d N nu nr"
  shows "\<exists>V t. artifact_at M mu V \<and> comparison_support_presents W E u r d N nu nr t \<and>
    term_quoted_at M mu mr t (rra_carrier (object_structure V)) {}"
proof -
  obtain V t where fields: "environment_formed M" "artifact_at M mu V" "complete_data_quoted_at V mr t"
    "comparison_support_presents W E u r d N nu nr t"
    using support unfolding comparison_support_at_def by blast
  have native: "term_quoted_at M mu mr t (rra_carrier (object_structure V)) {}"
    by (rule self_contained_quoted_in_environment[OF complete_data_quotation_native[OF fields(3)] fields(1,2)])
  show ?thesis using fields(2,4) native by blast
qed

theorem comparison_support_total:
  assumes "finite W" "\<And>z. z\<in>W \<Longrightarrow> term_formed (correspondence_row_data z)"
    "environment_formed E" "(u,r)\<in>environment_positions E" "d\<in>environment_positions E"
    "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>M. comparison_support_at M None [] W E u r d N nu nr"
proof -
  obtain t where present: "comparison_support_presents W E u r d N nu nr t"
    using comparison_support_presents_total[OF assms] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using comparison_support_presents_formed[OF present] by auto
  have quote: "complete_data_quoted_at (term_syntax t) [] t"
    by (rule complete_data_quotation_total[OF formed closed])
  have artifact: "exact_formed (term_syntax t)" using complete_data_quotation_formed[OF quote] by blast
  let ?M="artifact_family_environment {None :: local_address option} (\<lambda>_. term_syntax t)"
  have mf: "environment_formed ?M" by (rule artifact_family_formed) (use artifact in auto)
  have source: "artifact_at ?M None (term_syntax t)" by simp
  show ?thesis using mf source quote present unfolding comparison_support_at_def by blast
qed

text \<open>
  Structural rows store optional definition coordinates relative to the old
  and candidate scopes supplied by the amendment. They do not repeat those
  environments. Every row occurs once, in any complete collection order.
  Raw formation permits empty or semantically unaccounted correspondences;
  the later comparison profile checks their independently fixed domains.

  The reporter is one complete scope with two actual sites. Its program and
  potentially infinite report relation are derived later, not stored as
  duplicate fields. The remaining material has its own complete scope and
  selected site. Every native data reading covers the whole source and has
  no external slots. None of these raw readers calls positive meaning or
  grants permission to the reporter's clauses.
\<close>

end
