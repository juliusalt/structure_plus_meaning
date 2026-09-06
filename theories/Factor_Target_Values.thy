theory Factor_Target_Values
  imports Factor_Artifact_Values Factor_Coordinate_Values Factor_Complete_Data_Quotation
begin

section \<open>A complete artifact and its optional occurrence\<close>

definition target_value_presents :: "exact_target \<Rightarrow> factor_term \<Rightarrow> bool" where
  "target_value_presents x t \<longleftrightarrow> target_formed x \<and>
    (\<exists>v. artifact_value_presents (target_artifact x) v \<and>
      t=Pair_Term v (optional_payload_term (target_occurrence x)))"

lemma target_occurrence_data_formed:
  assumes "target_formed x"
  shows "term_formed (optional_payload_term (target_occurrence x))"
  using assms by (cases x) (auto simp: anchor_formed_def exact_formed_def octets_formed_def)

lemma target_value_whole:
  "target_value_presents (Whole_Artifact R) t \<longleftrightarrow>
    (\<exists>a. artifact_value_presents R a \<and> t=Pair_Term a (Payload_Term []))"
  using artifact_value_presents_formed by (auto simp: target_value_presents_def)

lemma target_value_occurrence:
  "target_value_presents (Occurrence_Anchor (R,r)) t \<longleftrightarrow>
    r\<in>rra_carrier (object_structure R) \<and>
    (\<exists>a. artifact_value_presents R a \<and> t=Pair_Term a (Pair_Term (Payload_Term r) (Payload_Term [])))"
  using artifact_value_presents_formed by (auto simp: target_value_presents_def anchor_formed_def)

lemma target_value_presents_formed:
  assumes "target_value_presents x t"
  shows "target_formed x \<and> term_formed t \<and> self_contained_term t"
  using assms artifact_value_presents_formed target_occurrence_data_formed
  by (auto simp: target_value_presents_def)

lemma target_value_at_source:
  assumes source: "artifact_value_presents R a"
  shows "target_value_presents x (Pair_Term a opt) \<longleftrightarrow>
    target_formed x \<and> target_artifact x=R \<and> opt=optional_payload_term (target_occurrence x)"
proof
  assume present: "target_value_presents x (Pair_Term a opt)"
  have parts: "target_formed x" "artifact_value_presents (target_artifact x) a"
    "opt=optional_payload_term (target_occurrence x)"
    using present by (auto simp: target_value_presents_def)
  have same: "target_artifact x=R" by (rule artifact_value_presents_unique[OF parts(2) source])
  show "target_formed x \<and> target_artifact x=R \<and> opt=optional_payload_term (target_occurrence x)"
    using parts same by blast
next
  assume "target_formed x \<and> target_artifact x=R \<and> opt=optional_payload_term (target_occurrence x)"
  then show "target_value_presents x (Pair_Term a opt)" using source by (auto simp: target_value_presents_def)
qed

theorem target_value_presents_unique:
  assumes first: "target_value_presents x t" and second: "target_value_presents y t"
  shows "x=y"
proof -
  obtain v where left: "artifact_value_presents (target_artifact x) v"
    "t=Pair_Term v (optional_payload_term (target_occurrence x))"
    using first unfolding target_value_presents_def by blast
  obtain w where right: "artifact_value_presents (target_artifact y) w"
    "t=Pair_Term w (optional_payload_term (target_occurrence y))"
    using second unfolding target_value_presents_def by blast
  have same: "v=w" and coordinate: "optional_payload_term (target_occurrence x)=optional_payload_term (target_occurrence y)"
    using left(2) right(2) by simp_all
  have other: "artifact_value_presents (target_artifact y) v" using right(1) same by simp
  have artifact: "target_artifact x=target_artifact y"
    by (rule artifact_value_presents_unique[OF left(1) other])
  have occurrence: "target_occurrence x=target_occurrence y"
    by (rule injD[OF optional_payload_term_injective coordinate])
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
  The selected address remains one opaque payload, including the empty address.
  Occurrence formation still requires the selected address to belong to that
  artifact. Its complete native quotation needs no external slot, so outer
  bindings cannot change the represented target.
\<close>

end
