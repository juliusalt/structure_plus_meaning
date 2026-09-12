theory Factor_Amendment_Values
  imports Factor_Current_Values Factor_Generation_Values
begin

section \<open>The complete current frame, candidate, and submitted certificate\<close>

definition amendment_value_presents ::
  "local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow> exact_target \<Rightarrow>
    factor_term \<Rightarrow> bool" where
  "amendment_value_presents E pu pr au ar F v root G c t \<longleftrightarrow>
    (\<exists>f g k. current_frame_value_presents E pu pr au ar F v root f \<and>
      generation_value_presents G g \<and> target_value_presents c k \<and>
      t=Pair_Term f (Pair_Term g k))"

theorem amendment_value_presents_unique:
  assumes first: "amendment_value_presents E pu pr au ar F v root G c t"
    and second: "amendment_value_presents D qu qr bu br N w s H k t"
  shows "E=D \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br \<and>
    F=N \<and> v=w \<and> root=s \<and> G=H \<and> c=k"
proof -
  obtain f g a where left: "current_frame_value_presents E pu pr au ar F v root f"
    "generation_value_presents G g" "target_value_presents c a"
    "t=Pair_Term f (Pair_Term g a)"
    using first unfolding amendment_value_presents_def by blast
  obtain f' g' a' where right: "current_frame_value_presents D qu qr bu br N w s f'"
    "generation_value_presents H g'" "target_value_presents k a'"
    "t=Pair_Term f' (Pair_Term g' a')"
    using second unfolding amendment_value_presents_def by blast
  have same: "f'=f" "g'=g" "a'=a" using left(4) right(4) by simp_all
  have other: "current_frame_value_presents D qu qr bu br N w s f"
    "generation_value_presents H g" "target_value_presents k a"
    using right(1-3) same by simp_all
  show ?thesis using current_frame_value_presents_unique[OF left(1) other(1)]
    generation_value_presents_unique[OF left(2) other(2)]
    target_value_presents_unique[OF left(3) other(3)] by blast
qed

lemma amendment_value_presents_formed:
  assumes present: "amendment_value_presents E pu pr au ar F v root G c t"
  shows "environment_formed E \<and> environment_formed F \<and>
    (pu,pr)\<in>environment_positions E \<and> (au,ar)\<in>environment_positions E \<and>
    (v,root)\<in>environment_positions F \<and> generation_formed G \<and> target_formed c \<and>
    term_formed t \<and> self_contained_term t"
proof -
  obtain f g k where fields: "current_frame_value_presents E pu pr au ar F v root f"
    "generation_value_presents G g" "target_value_presents c k"
    "t=Pair_Term f (Pair_Term g k)"
    using present unfolding amendment_value_presents_def by blast
  show ?thesis using current_frame_value_presents_formed[OF fields(1)]
    generation_value_presents_formed[OF fields(2)] target_value_presents_formed[OF fields(3)] fields(4) by simp
qed

lemma amendment_value_is_pair:
  assumes "amendment_value_presents E pu pr au ar F v root G c t"
  shows "\<exists>x y. t=Pair_Term x y"
  using assms unfolding amendment_value_presents_def by blast

theorem amendment_value_presents_total:
  assumes env: "environment_formed E" and program: "(pu,pr)\<in>environment_positions E"
    and app: "(au,ar)\<in>environment_positions E" and publication: "environment_formed F"
    and site: "(v,root)\<in>environment_positions F"
    and candidate: "generation_formed G" and certificate: "target_formed c"
  shows "\<exists>t. amendment_value_presents E pu pr au ar F v root G c t"
proof -
  obtain f g k where fields: "current_frame_value_presents E pu pr au ar F v root f"
    "generation_value_presents G g" "target_value_presents c k"
    using current_frame_value_presents_total[OF env program app publication site]
      generation_value_presents_total[OF candidate] target_value_presents_total[OF certificate] by blast
  show ?thesis using fields unfolding amendment_value_presents_def by blast
qed

theorem amendment_value_quotation_total:
  assumes "environment_formed E" "(pu,pr)\<in>environment_positions E"
    "(au,ar)\<in>environment_positions E" "environment_formed F" "(v,root)\<in>environment_positions F"
    "generation_formed G" "target_formed c"
  shows "\<exists>t R. amendment_value_presents E pu pr au ar F v root G c t \<and>
    complete_data_quoted_at R [] t"
proof -
  obtain t where present: "amendment_value_presents E pu pr au ar F v root G c t"
    using amendment_value_presents_total[OF assms] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using amendment_value_presents_formed[OF present] by auto
  show ?thesis using present complete_data_quotation_total[OF formed closed] by blast
qed

text \<open>
  The first field presents both complete current-frame scopes. Its actual
  adoption call contains the authority, predecessor generation, and purpose.
  The predecessor's payload in turn contains its complete program scope.
  Those derived fields are not stored again. Every complete presentation of
  these scopes and of the candidate and certificate is admitted.

  A candidate's clauses, bindings, recursive history, and cause can be inspected
  as data. Neither candidate formation nor certificate presentation establishes
  the amendment conditions. The raw value does not itself assert currentness,
  a valid cause, a program payload, certificate validity, or succession.
\<close>

end
