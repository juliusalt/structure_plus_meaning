theory Factor_Current_Values
  imports Factor_Judgment_Values Factor_Site_Values
begin

section \<open>Two complete scopes as ordinary frame data\<close>

definition current_frame_value_presents ::
  "local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> factor_term \<Rightarrow> bool" where
  "current_frame_value_presents E pu pr au ar F v root t \<longleftrightarrow>
    (\<exists>a b. judgment_value_presents E pu pr au ar a \<and> site_value_presents F v root b \<and> t=Pair_Term a b)"

theorem current_frame_value_presents_unique:
  assumes first: "current_frame_value_presents E pu pr au ar F v root t"
    and second: "current_frame_value_presents D qu qr bu br N w s t"
  shows "E=D \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br \<and> F=N \<and> v=w \<and> root=s"
proof -
  obtain a b where left: "judgment_value_presents E pu pr au ar a" "site_value_presents F v root b"
    "t=Pair_Term a b" using first unfolding current_frame_value_presents_def by blast
  obtain c d where right: "judgment_value_presents D qu qr bu br c" "site_value_presents N w s d"
    "t=Pair_Term c d" using second unfolding current_frame_value_presents_def by blast
  have same: "c=a" "d=b" using left(3) right(3) by simp_all
  have other: "judgment_value_presents D qu qr bu br a" "site_value_presents N w s b"
    using right(1,2) same by simp_all
  show ?thesis using judgment_value_presents_unique[OF left(1) other(1)]
    site_value_presents_unique[OF left(2) other(2)] by blast
qed

lemma current_frame_value_presents_formed:
  assumes present: "current_frame_value_presents E pu pr au ar F v root t"
  shows "environment_formed E \<and> environment_formed F \<and>
    (pu,pr)\<in>environment_positions E \<and> (au,ar)\<in>environment_positions E \<and>
    (v,root)\<in>environment_positions F \<and> term_formed t \<and> self_contained_term t"
proof -
  obtain a b where fields: "judgment_value_presents E pu pr au ar a" "site_value_presents F v root b"
    "t=Pair_Term a b" using present unfolding current_frame_value_presents_def by blast
  have sites: "(pu,pr)\<in>environment_positions E" "(au,ar)\<in>environment_positions E" "(v,root)\<in>environment_positions F"
    using fields(1,2) by (auto simp: judgment_value_presents_def site_value_presents_def)
  show ?thesis using judgment_value_presents_formed[OF fields(1)] site_value_presents_formed[OF fields(2)]
    fields(3) sites by simp
qed

theorem current_frame_value_presents_total:
  assumes ef: "environment_formed E" and program: "(pu,pr)\<in>environment_positions E"
    and app: "(au,ar)\<in>environment_positions E" and ff: "environment_formed F"
    and publication: "(v,root)\<in>environment_positions F"
  shows "\<exists>t. current_frame_value_presents E pu pr au ar F v root t"
proof -
  obtain a b where fields: "judgment_value_presents E pu pr au ar a" "site_value_presents F v root b"
    using judgment_value_presents_total[OF ef program app] site_value_presents_total[OF ff publication] by blast
  show ?thesis using fields unfolding current_frame_value_presents_def by blast
qed

definition current_frame_quoted_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "current_frame_quoted_at C q E pu pr au ar F v root \<longleftrightarrow>
    (\<exists>t. current_frame_value_presents E pu pr au ar F v root t \<and> complete_data_quoted_at C q t)"

theorem current_frame_quoted_unique:
  assumes first: "current_frame_quoted_at C q E pu pr au ar F v root"
    and second: "current_frame_quoted_at C q D qu qr bu br N w s"
  shows "E=D \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br \<and> F=N \<and> v=w \<and> root=s"
proof -
  obtain t where left: "current_frame_value_presents E pu pr au ar F v root t" "complete_data_quoted_at C q t"
    using first unfolding current_frame_quoted_at_def by blast
  obtain a where right: "current_frame_value_presents D qu qr bu br N w s a" "complete_data_quoted_at C q a"
    using second unfolding current_frame_quoted_at_def by blast
  have same: "t=a" by (rule complete_data_quotation_unique[OF left(2) right(2)])
  have other: "current_frame_value_presents D qu qr bu br N w s t" using right(1) same by simp
  show ?thesis by (rule current_frame_value_presents_unique[OF left(1) other])
qed

lemma current_frame_quoted_formed:
  assumes quote: "current_frame_quoted_at C q E pu pr au ar F v root"
  shows "exact_formed C \<and> environment_formed E \<and> environment_formed F \<and>
    (pu,pr)\<in>environment_positions E \<and> (au,ar)\<in>environment_positions E \<and> (v,root)\<in>environment_positions F"
proof -
  obtain t where parts: "current_frame_value_presents E pu pr au ar F v root t" "complete_data_quoted_at C q t"
    using quote unfolding current_frame_quoted_at_def by blast
  show ?thesis using current_frame_value_presents_formed[OF parts(1)] complete_data_quotation_formed[OF parts(2)] by blast
qed

lemma current_frame_quoted_anchor:
  assumes "current_frame_quoted_at C q E pu pr au ar F v root"
  shows "anchor_formed (C,q)"
  using assms unfolding current_frame_quoted_at_def by (meson complete_data_quotation_anchor)

theorem current_frame_quoted_total:
  assumes "environment_formed E" "(pu,pr)\<in>environment_positions E" "(au,ar)\<in>environment_positions E"
    "environment_formed F" "(v,root)\<in>environment_positions F"
  shows "\<exists>C. current_frame_quoted_at C [] E pu pr au ar F v root"
proof -
  obtain t where present: "current_frame_value_presents E pu pr au ar F v root t"
    using current_frame_value_presents_total[OF assms] by blast
  have tf: "term_formed t" and closed: "self_contained_term t" using current_frame_value_presents_formed[OF present] by auto
  show ?thesis using present complete_data_quotation_total[OF tf closed] unfolding current_frame_quoted_at_def by blast
qed

theorem current_frame_quoted_in_environment:
  assumes quote: "current_frame_quoted_at C q E pu pr au ar F v root"
    and formed: "environment_formed H" and source: "artifact_at H u C"
  shows "\<exists>t. current_frame_value_presents E pu pr au ar F v root t \<and>
    term_quoted_at H u q t (rra_carrier (object_structure C)) {}"
proof -
  obtain t where parts: "current_frame_value_presents E pu pr au ar F v root t" "complete_data_quoted_at C q t"
    using quote unfolding current_frame_quoted_at_def by blast
  have native: "term_quoted_at H u q t (rra_carrier (object_structure C)) {}"
    by (rule self_contained_quoted_in_environment[OF complete_data_quotation_native[OF parts(2)] formed source])
  show ?thesis using parts(1) native by blast
qed

text \<open>
  The two fields contain a complete program-and-call scope and a complete
  single-site scope. Every field and binding is ordinary data. The value alone
  establishes neither adoption nor publication. A higher reader checks those
  roles and recovers the corresponding authority, generation, and purpose.
  Their collections admit every complete presentation and every formed
  readdressing of the whole data quotation.
\<close>

end
