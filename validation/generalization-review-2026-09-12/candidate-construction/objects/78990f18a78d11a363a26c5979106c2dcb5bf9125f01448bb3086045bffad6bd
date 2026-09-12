theory Factor_Adoption_Values
  imports Factor_Generation_Values
begin

section \<open>Authority, exact generation, and purpose as ordinary arguments\<close>

definition adoption_value_presents ::
  "exact_target \<Rightarrow> generation_core \<Rightarrow> exact_target \<Rightarrow> factor_term \<Rightarrow> bool" where
  "adoption_value_presents A G purpose t \<longleftrightarrow>
    (\<exists>a g p. target_value_presents A a \<and> generation_value_presents G g \<and>
      target_value_presents purpose p \<and> t=Pair_Term a (Pair_Term g p))"

theorem adoption_value_presents_unique:
  assumes first: "adoption_value_presents A G p t" and second: "adoption_value_presents B H q t"
  shows "A=B \<and> G=H \<and> p=q"
proof -
  obtain a g c where left: "target_value_presents A a" "generation_value_presents G g"
    "target_value_presents p c" "t=Pair_Term a (Pair_Term g c)"
    using first unfolding adoption_value_presents_def by blast
  obtain b h d where right: "target_value_presents B b" "generation_value_presents H h"
    "target_value_presents q d" "t=Pair_Term b (Pair_Term h d)"
    using second unfolding adoption_value_presents_def by blast
  have same: "a=b" "g=h" "c=d" using left(4) right(4) by simp_all
  have other: "target_value_presents B a" "generation_value_presents H g" "target_value_presents q c"
    using right(1-3) same by simp_all
  show ?thesis using target_value_presents_unique[OF left(1) other(1)]
    generation_value_presents_unique[OF left(2) other(2)]
    target_value_presents_unique[OF left(3) other(3)] by blast
qed

lemma adoption_value_presents_formed:
  assumes present: "adoption_value_presents A G p t"
  shows "target_formed A \<and> generation_formed G \<and> target_formed p \<and>
    term_formed t \<and> self_contained_term t"
proof -
  obtain a g c where fields: "target_value_presents A a" "generation_value_presents G g"
    "target_value_presents p c" "t=Pair_Term a (Pair_Term g c)"
    using present unfolding adoption_value_presents_def by blast
  show ?thesis using target_value_presents_formed[OF fields(1)]
    generation_value_presents_formed[OF fields(2)] target_value_presents_formed[OF fields(3)] fields(4) by simp
qed

lemma adoption_value_is_pair:
  assumes "adoption_value_presents A G p t"
  shows "\<exists>a b. t=Pair_Term a b"
  using assms unfolding adoption_value_presents_def by blast

theorem adoption_value_presents_total:
  assumes authority: "target_formed A" and core: "generation_formed G" and purpose: "target_formed p"
  shows "\<exists>t. adoption_value_presents A G p t"
proof -
  obtain a where ar: "target_value_presents A a" using target_value_presents_total[OF authority] by blast
  obtain g where gr: "generation_value_presents G g" using generation_value_presents_total[OF core] by blast
  obtain c where cr: "target_value_presents p c" using target_value_presents_total[OF purpose] by blast
  show ?thesis by (rule exI[of _ "Pair_Term a (Pair_Term g c)"])
    (use ar gr cr in \<open>auto simp: adoption_value_presents_def\<close>)
qed

theorem adoption_value_quotation_total:
  assumes "target_formed A" "generation_formed G" "target_formed p"
  shows "\<exists>t C. adoption_value_presents A G p t \<and> complete_data_quoted_at C [] t"
proof -
  obtain t where present: "adoption_value_presents A G p t" using adoption_value_presents_total[OF assms] by blast
  have formed: "term_formed t" and closed: "self_contained_term t"
    using adoption_value_presents_formed[OF present] by auto
  show ?thesis using present complete_data_quotation_total[OF formed closed] by blast
qed

text \<open>
  The three fields supply an exact authority target, a complete generation
  core, and an exact purpose target. A target has no intrinsic authority or
  purpose role outside the application using it. Every complete presentation
  of the fields is admitted as data. This representation contains no decision,
  proof, currentness, or publication field.
\<close>

end
