theory Factor_Target_Values
  imports Factor_Artifact_Values Factor_Coordinate_Values Factor_Complete_Data_Quotation
begin

section \<open>A complete artifact and its optional occurrence\<close>

definition target_value_presents :: "exact_target \<Rightarrow> factor_term \<Rightarrow> bool" where
  "target_value_presents x t \<longleftrightarrow> target_formed x \<and>
    (\<exists>v. artifact_value_presents (target_artifact x) v \<and>
      t=Pair_Term v (use_data_term (target_occurrence x)))"

lemma target_value_presents_formed:
  assumes "target_value_presents x t"
  shows "target_formed x \<and> term_formed t \<and> self_contained_term t"
  using assms artifact_value_presents_formed
  by (auto simp: target_value_presents_def)

theorem target_value_presents_unique:
  assumes first: "target_value_presents x t" and second: "target_value_presents y t"
  shows "x=y"
proof -
  obtain v where left: "artifact_value_presents (target_artifact x) v"
    "t=Pair_Term v (use_data_term (target_occurrence x))"
    using first unfolding target_value_presents_def by blast
  obtain w where right: "artifact_value_presents (target_artifact y) w"
    "t=Pair_Term w (use_data_term (target_occurrence y))"
    using second unfolding target_value_presents_def by blast
  have same: "v=w" and coordinate: "use_data_term (target_occurrence x)=use_data_term (target_occurrence y)"
    using left(2) right(2) by simp_all
  have other: "artifact_value_presents (target_artifact y) v" using right(1) same by simp
  have artifact: "target_artifact x=target_artifact y"
    by (rule artifact_value_presents_unique[OF left(1) other])
  have occurrence: "target_occurrence x=target_occurrence y"
    by (rule injD[OF use_data_term_injective coordinate])
  show ?thesis using artifact occurrence by (simp add: exact_target_identity)
qed

theorem target_value_presents_total:
  assumes "target_formed x"
  shows "\<exists>t. target_value_presents x t"
proof -
  obtain v where "artifact_value_presents (target_artifact x) v"
    using artifact_value_presents_total[OF target_formed_artifact[OF assms]] by blast
  then show ?thesis using assms unfolding target_value_presents_def by blast
qed

theorem target_value_quotation_total:
  assumes "target_formed x"
  shows "\<exists>t C. target_value_presents x t \<and> complete_data_quoted_at C [] t"
proof -
  obtain t where present: "target_value_presents x t"
    using target_value_presents_total[OF assms] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using target_value_presents_formed[OF present] by auto
  show ?thesis using present complete_data_quotation_total[OF formed closed] by blast
qed

text \<open>
  This is an inspectable data copy of an exact target. It retains every artifact
  field and distinguishes a whole artifact from its optional selected occurrence.
  Occurrence formation still requires the selected address to belong to that
  artifact. Its complete native quotation needs no external slot, so outer
  bindings cannot change the represented target.
\<close>

end
