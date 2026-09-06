theory Factor_Program_Entry_Values
  imports Factor_Site_Values
begin

section \<open>One complete scope with a package site and a selected entry site\<close>

definition program_entry_value_presents ::
  "local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    (local_address option\<times>local_address) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "program_entry_value_presents E u r d t \<longleftrightarrow>
    d\<in>environment_positions E \<and>
    (\<exists>s. site_value_presents E u r s \<and> t=Pair_Term s (site_data_term (fst d) (snd d)))"

theorem program_entry_value_presents_unique:
  assumes first: "program_entry_value_presents E u r d t"
    and second: "program_entry_value_presents F v s e t"
  shows "E=F \<and> u=v \<and> r=s \<and> d=e"
proof -
  obtain a where left: "site_value_presents E u r a" "t=Pair_Term a (site_data_term (fst d) (snd d))"
    using first unfolding program_entry_value_presents_def by blast
  obtain b where right: "site_value_presents F v s b" "t=Pair_Term b (site_data_term (fst e) (snd e))"
    using second unfolding program_entry_value_presents_def by blast
  have same: "a=b" "d=e" using left(2) right(2) by (simp_all add: prod_eq_iff)
  have other: "site_value_presents F v s a" using right(1) same(1) by simp
  show ?thesis using site_value_presents_unique[OF left(1) other] same(2) by blast
qed

lemma program_entry_value_presents_formed:
  assumes present: "program_entry_value_presents E u r d t"
  shows "environment_formed E \<and> (u,r)\<in>environment_positions E \<and> d\<in>environment_positions E \<and>
    term_formed t \<and> self_contained_term t"
proof -
  obtain s where fields: "d\<in>environment_positions E" "site_value_presents E u r s"
    "t=Pair_Term s (site_data_term (fst d) (snd d))"
    using present unfolding program_entry_value_presents_def by blast
  have ef: "environment_formed E" and tf: "term_formed s" and closed: "self_contained_term s"
    using site_value_presents_formed[OF fields(2)] by auto
  have address: "octets_formed (snd d)" by (rule environment_position_address[OF ef fields(1)])
  show ?thesis using ef tf closed address fields by (auto simp: site_value_presents_def)
qed

theorem program_entry_value_presents_total:
  assumes "environment_formed E" "(u,r)\<in>environment_positions E" "d\<in>environment_positions E"
  shows "\<exists>t. program_entry_value_presents E u r d t"
  using site_value_presents_total[OF assms(1,2)] assms(3)
  unfolding program_entry_value_presents_def by blast

text \<open>
  The environment occurs once. Two exact sites identify the proposed package
  root and selected definition within it. They may coincide. This raw data
  relation checks that both sites exist, without assigning either a native
  grammar, authority, truth, or permission. A program reader must separately
  recover a closed package at the first site and membership of the second.

  The complete scope and both coordinates are uniquely recoverable from every
  admitted presentation. The program itself is derived by that later reader;
  no duplicate program, application, purpose frame, or proof is stored here.
\<close>

end
