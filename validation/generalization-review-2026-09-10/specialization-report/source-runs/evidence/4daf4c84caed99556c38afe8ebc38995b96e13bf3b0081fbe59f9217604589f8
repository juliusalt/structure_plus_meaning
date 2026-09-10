theory Factor_Clause_Specialization_Contracts
  imports Factor_Clause_Specialization_Instances
begin

section \<open>The complete schema boundary uses the existing paired source class\<close>

definition schema_pattern_context_formed ::
  "((site_context\<times>local_address option definition_site)\<times>site_context) \<Rightarrow> bool" where
  "schema_pattern_context_formed z \<longleftrightarrow>
    (case z of (((E,u,r),d),(F,v,q)) \<Rightarrow> schema_pattern_boundary_at E u r d F v q)"

definition schema_pattern_context_presents ::
  "((site_context\<times>local_address option definition_site)\<times>site_context) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "schema_pattern_context_presents z t \<longleftrightarrow> schema_pattern_context_formed z \<and> pattern_call_sources_presents z t"

lemma schema_pattern_context_boundary:
  assumes "schema_pattern_context_formed z"
  shows "site_context_formed (fst (fst z)) \<and> site_context_formed (snd z)"
  using assms by (auto simp: schema_pattern_context_formed_def schema_pattern_boundary_at_def
    native_package_at_def native_root_family_at_def family_at_def native_schema_at_def record_at_def split: prod.splits)

lemma schema_pattern_context_fields:
  "schema_pattern_context_presents (((E,u,r),d),(F,v,q)) t \<longleftrightarrow>
    schema_pattern_boundary_at E u r d F v q \<and>
    (\<exists>a b. source_root_presents (E,u,r) a \<and> site_value_presents F v q b \<and>
      t=Pair_Term (Pair_Term a (definition_site_value d)) b)"
  by (auto simp: schema_pattern_context_presents_def schema_pattern_context_formed_def factor_pair_presents_def)

theorem schema_pattern_context_admission:
  "(293,t)\<in>positive_meaning schema_pattern_reading_system \<longleftrightarrow>
    (\<exists>z. schema_pattern_context_presents z t)"
proof -
  have actual: "site_context_formed (E,u,r) \<and> site_context_formed (F,v,q)"
    if "schema_pattern_boundary_at E u r d F v q" for E u r d F v q
    using schema_pattern_context_boundary[of "(((E,u,r),d),(F,v,q))"] that
    by (simp add: schema_pattern_context_formed_def)
  show ?thesis
  proof
    assume admitted: "(293,t)\<in>positive_meaning schema_pattern_reading_system"
    obtain E e u r d F f v q where inputs: "environment_value_presents E e" "environment_value_presents F f"
      "t=pattern_call_reading_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
        f (use_data_term v) (Payload_Term q)" "schema_pattern_boundary_at E u r d F v q"
      using admitted by (simp only: schema_pattern_reading_exact schema_pattern_reading_result_def) blast
    have sites: "source_root_presents (E,u,r) (source_root_argument e (use_data_term u) (Payload_Term r))"
      "site_value_presents F v q (Pair_Term f (site_data_term v q))"
      using inputs(1,2) actual[OF inputs(4)] by (auto simp: site_value_presents_def source_root_presents_fields)
    have presented: "schema_pattern_context_presents (((E,u,r),d),(F,v,q)) t"
      unfolding schema_pattern_context_fields
      by (rule conjI[OF inputs(4)], rule exI[of _ "source_root_argument e (use_data_term u) (Payload_Term r)"],
        rule exI[of _ "Pair_Term f (site_data_term v q)"])
        (use sites inputs(3) in \<open>simp add: site_data_term_def\<close>)
    show "\<exists>z. schema_pattern_context_presents z t" using presented by blast
  next
    assume "\<exists>z. schema_pattern_context_presents z t"
    then obtain z where presented: "schema_pattern_context_presents z t" by blast
    obtain E u r d F v q where shape: "z=(((E,u,r),d),(F,v,q))" by (metis surjective_pairing)
    obtain a b where inputs: "schema_pattern_boundary_at E u r d F v q"
      "source_root_presents (E,u,r) a" "site_value_presents F v q b"
      "t=Pair_Term (Pair_Term a (definition_site_value d)) b"
      using presented by (simp only: shape schema_pattern_context_fields) blast
    obtain e f where sources: "environment_value_presents E e" "a=source_root_argument e (use_data_term u) (Payload_Term r)"
      "environment_value_presents F f" "b=Pair_Term f (site_data_term v q)"
      using inputs(2,3) by (auto simp: site_value_presents_def source_root_presents_fields)
    show "(293,t)\<in>positive_meaning schema_pattern_reading_system"
      unfolding schema_pattern_reading_exact schema_pattern_reading_result_def
      by (rule exI[of _ E], rule exI[of _ e], rule exI[of _ u], rule exI[of _ r], rule exI[of _ d],
        rule exI[of _ F], rule exI[of _ f], rule exI[of _ v], rule exI[of _ q])
        (use sources inputs(1,4) in \<open>simp add: site_data_term_def\<close>)
  qed
qed

theorem schema_pattern_context_class:
  "presentation_class schema_pattern_context_presents schema_pattern_context_formed
    (\<lambda>t. (293,t)\<in>positive_meaning schema_pattern_reading_system)"
proof -
  have generic: "presentation_class (\<lambda>z t. schema_pattern_context_formed z \<and> pattern_call_sources_presents z t)
      schema_pattern_context_formed (\<lambda>t. \<exists>z. schema_pattern_context_formed z \<and> pattern_call_sources_presents z t)"
    by (rule presentation_class_subdomain[OF pattern_call_sources.presentation_class_axioms])
      (rule schema_pattern_context_boundary)
  show ?thesis using generic
    by (simp only: schema_pattern_context_presents_def[symmetric] schema_pattern_context_admission[symmetric])
qed

theorem schema_pattern_context_predicate:
  "(293,t)\<in>positive_meaning schema_pattern_reading_system \<longleftrightarrow>
    presented_predicate pattern_call_sources_presents schema_pattern_context_formed t"
  by (simp only: schema_pattern_context_admission schema_pattern_context_presents_def presented_predicate_def conj_commute)

theorem schema_pattern_context_at:
  assumes "pattern_call_sources_presents z t"
  shows "(293,t)\<in>positive_meaning schema_pattern_reading_system \<longleftrightarrow> schema_pattern_context_formed z"
  by (simp only: schema_pattern_context_predicate pattern_call_sources.predicate_at[OF assms])

theorem schema_pattern_context_invariance:
  assumes "pattern_call_sources_presents z t" "pattern_call_sources_presents z s"
  shows "(293,t)\<in>positive_meaning schema_pattern_reading_system \<longleftrightarrow>
    (293,s)\<in>positive_meaning schema_pattern_reading_system"
  by (simp only: schema_pattern_context_at[OF assms(1)] schema_pattern_context_at[OF assms(2)])


section \<open>The clause subject links its actual occurrence and both submitted sites\<close>

type_synonym clause_specialization_context =
  "(site_context\<times>(local_address option definition_site\<times>local_address))\<times>(site_context\<times>site_context)"

abbreviation clause_specialization_sources_presents ::
  "clause_specialization_context \<Rightarrow> factor_term \<Rightarrow> bool" where
  "clause_specialization_sources_presents \<equiv>
    factor_pair_presents
      (factor_pair_presents source_root_presents
        (factor_pair_presents site_coordinate_presents (\<lambda>c t. t=Payload_Term c)))
      (factor_pair_presents site_context_presents site_context_presents)"

interpretation clause_specialization_sources: presentation_class clause_specialization_sources_presents
  "\<lambda>z. site_context_formed (fst (fst z)) \<and> site_context_formed (fst (snd z)) \<and> site_context_formed (snd (snd z))"
  "\<lambda>t. \<exists>x y. (\<exists>a b. (\<exists>z. source_root_presents z a) \<and>
    (\<exists>d c v. site_coordinate_presents d v \<and> b=Pair_Term v (Payload_Term c)) \<and> x=Pair_Term a b) \<and>
    (\<exists>a b. (156,a)\<in>positive_meaning context_admission_system \<and>
      (156,b)\<in>positive_meaning context_admission_system \<and> y=Pair_Term a b) \<and> t=Pair_Term x y"
proof -
  let ?D="\<lambda>z. site_context_formed (fst (fst z)) \<and> site_context_formed (fst (snd z)) \<and>
    site_context_formed (snd (snd z))"
  let ?A="\<lambda>t. \<exists>x y. (\<exists>a b. (\<exists>z. source_root_presents z a) \<and>
      (\<exists>p q. (\<exists>d. site_coordinate_presents d p) \<and> (\<exists>c. q=Payload_Term c) \<and> b=Pair_Term p q) \<and>
      x=Pair_Term a b) \<and>
    (\<exists>a b. (156,a)\<in>positive_meaning context_admission_system \<and>
      (156,b)\<in>positive_meaning context_admission_system \<and> y=Pair_Term a b) \<and> t=Pair_Term x y"
  let ?B="\<lambda>t. \<exists>x y. (\<exists>a b. (\<exists>z. source_root_presents z a) \<and>
      (\<exists>d c v. site_coordinate_presents d v \<and> b=Pair_Term v (Payload_Term c)) \<and> x=Pair_Term a b) \<and>
    (\<exists>a b. (156,a)\<in>positive_meaning context_admission_system \<and>
      (156,b)\<in>positive_meaning context_admission_system \<and> y=Pair_Term a b) \<and> t=Pair_Term x y"
  have generic: "presentation_class clause_specialization_sources_presents ?D ?A"
    using factor_pair_class[OF factor_pair_class[OF source_root_presentation_class
    factor_pair_class[OF site_coordinate_presentation address_coordinate_presentation]]
    factor_pair_class[OF site_context_native_class site_context_native_class]]
    by simp
  have same: "?A=?B" by (rule ext) (auto; blast)
  show "presentation_class clause_specialization_sources_presents ?D ?B"
    using generic by (simp only: same)
qed

definition clause_specialization_context_formed :: "clause_specialization_context \<Rightarrow> bool" where
  "clause_specialization_context_formed z \<longleftrightarrow>
    (case z of (((E,u,r),(d,c)),((F,v,q),(G,w,t))) \<Rightarrow>
      schema_clause_specialization_at E u r d c F v q G w t)"

definition clause_specialization_context_presents :: "clause_specialization_context \<Rightarrow> factor_term \<Rightarrow> bool" where
  "clause_specialization_context_presents z p \<longleftrightarrow>
    clause_specialization_context_formed z \<and> clause_specialization_sources_presents z p"

lemma clause_specialization_context_boundary:
  assumes "clause_specialization_context_formed z"
  shows "site_context_formed (fst (fst z)) \<and> site_context_formed (fst (snd z)) \<and> site_context_formed (snd (snd z))"
  using assms by (auto simp: clause_specialization_context_formed_def schema_clause_specialization_at_def
    native_package_at_def native_root_family_at_def family_at_def pattern_record_at_def native_schema_at_def
    record_at_def split: prod.splits)

lemma clause_specialization_context_fields:
  "clause_specialization_context_presents (((E,u,r),(d,c)),((F,v,q),(G,w,t))) p \<longleftrightarrow>
    schema_clause_specialization_at E u r d c F v q G w t \<and>
    (\<exists>a b z. source_root_presents (E,u,r) a \<and> site_value_presents F v q b \<and> site_value_presents G w t z \<and>
      p=Pair_Term (Pair_Term a (Pair_Term (definition_site_value d) (Payload_Term c))) (Pair_Term b z))"
  by (auto simp: clause_specialization_context_presents_def clause_specialization_context_formed_def factor_pair_presents_def)

theorem clause_specialization_context_admission:
  "(294,p)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow>
    (\<exists>z. clause_specialization_context_presents z p)"
proof -
  have actual: "site_context_formed (E,u,r) \<and> site_context_formed (F,v,q) \<and> site_context_formed (G,w,t)"
    if "schema_clause_specialization_at E u r d c F v q G w t" for E u r d c F v q G w t
    using clause_specialization_context_boundary[of "(((E,u,r),(d,c)),((F,v,q),(G,w,t)))"] that
    by (simp add: clause_specialization_context_formed_def)
  show ?thesis
  proof
    assume admitted: "(294,p)\<in>positive_meaning clause_specialization_reading_system"
    obtain E e u r d c F f v q G g w t where inputs: "environment_value_presents E e"
      "environment_value_presents F f" "environment_value_presents G g"
      "p=clause_specialization_reading_argument e (use_data_term u) (Payload_Term r) (definition_site_value d)
        (Payload_Term c) f (use_data_term v) (Payload_Term q) g (use_data_term w) (Payload_Term t)"
      "schema_clause_specialization_at E u r d c F v q G w t"
      using admitted by (simp only: clause_specialization_reading_exact clause_specialization_reading_result_def) blast
    have sites: "source_root_presents (E,u,r) (source_root_argument e (use_data_term u) (Payload_Term r))"
      "site_value_presents F v q (Pair_Term f (site_data_term v q))"
      "site_value_presents G w t (Pair_Term g (site_data_term w t))"
      using inputs(1-3) actual[OF inputs(5)] by (auto simp: source_root_presents_fields site_value_presents_def)
    have presented: "clause_specialization_context_presents (((E,u,r),(d,c)),((F,v,q),(G,w,t))) p"
      unfolding clause_specialization_context_fields
      by (rule conjI[OF inputs(5)], rule exI[of _ "source_root_argument e (use_data_term u) (Payload_Term r)"],
        rule exI[of _ "Pair_Term f (site_data_term v q)"], rule exI[of _ "Pair_Term g (site_data_term w t)"])
        (use sites inputs(4) in \<open>simp add: site_data_term_def\<close>)
    show "\<exists>z. clause_specialization_context_presents z p" using presented by blast
  next
    assume "\<exists>z. clause_specialization_context_presents z p"
    then obtain z where presented: "clause_specialization_context_presents z p" by blast
    obtain E u r d c F v q G w t where shape: "z=(((E,u,r),(d,c)),((F,v,q),(G,w,t)))"
      by (metis surjective_pairing)
    obtain a b x where inputs: "schema_clause_specialization_at E u r d c F v q G w t"
      "source_root_presents (E,u,r) a" "site_value_presents F v q b" "site_value_presents G w t x"
      "p=Pair_Term (Pair_Term a (Pair_Term (definition_site_value d) (Payload_Term c))) (Pair_Term b x)"
      using presented by (simp only: shape clause_specialization_context_fields) blast
    obtain e f g where sources: "environment_value_presents E e" "a=source_root_argument e (use_data_term u) (Payload_Term r)"
      "environment_value_presents F f" "b=Pair_Term f (site_data_term v q)"
      "environment_value_presents G g" "x=Pair_Term g (site_data_term w t)"
      using inputs(2-4) by (auto simp: source_root_presents_fields site_value_presents_def)
    show "(294,p)\<in>positive_meaning clause_specialization_reading_system"
      unfolding clause_specialization_reading_exact clause_specialization_reading_result_def
      by (rule exI[of _ E], rule exI[of _ e], rule exI[of _ u], rule exI[of _ r], rule exI[of _ d],
        rule exI[of _ c], rule exI[of _ F], rule exI[of _ f], rule exI[of _ v], rule exI[of _ q],
        rule exI[of _ G], rule exI[of _ g], rule exI[of _ w], rule exI[of _ t])
        (use sources inputs(1,5) in \<open>simp add: site_data_term_def\<close>)
  qed
qed

theorem clause_specialization_context_class:
  "presentation_class clause_specialization_context_presents clause_specialization_context_formed
    (\<lambda>t. (294,t)\<in>positive_meaning clause_specialization_reading_system)"
proof -
  have generic: "presentation_class
      (\<lambda>z t. clause_specialization_context_formed z \<and> clause_specialization_sources_presents z t)
      clause_specialization_context_formed
      (\<lambda>t. \<exists>z. clause_specialization_context_formed z \<and> clause_specialization_sources_presents z t)"
    by (rule presentation_class_subdomain[OF clause_specialization_sources.presentation_class_axioms])
      (rule clause_specialization_context_boundary)
  show ?thesis using generic
    by (simp only: clause_specialization_context_presents_def[symmetric] clause_specialization_context_admission[symmetric])
qed

theorem clause_specialization_context_predicate:
  "(294,t)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow>
    presented_predicate clause_specialization_sources_presents clause_specialization_context_formed t"
  by (simp only: clause_specialization_context_admission clause_specialization_context_presents_def
    presented_predicate_def conj_commute)

theorem clause_specialization_context_at:
  assumes "clause_specialization_sources_presents z t"
  shows "(294,t)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow> clause_specialization_context_formed z"
  by (simp only: clause_specialization_context_predicate clause_specialization_sources.predicate_at[OF assms])

theorem clause_specialization_context_invariance:
  assumes "clause_specialization_sources_presents z t" "clause_specialization_sources_presents z s"
  shows "(294,t)\<in>positive_meaning clause_specialization_reading_system \<longleftrightarrow>
    (294,s)\<in>positive_meaning clause_specialization_reading_system"
  by (simp only: clause_specialization_context_at[OF assms(1)] clause_specialization_context_at[OF assms(2)])

text \<open>
  Both intrinsic relations supply subdomains of existing source, coordinate,
  and site classes combined by products. The schema boundary reuses the
  symbolic-call input class. The clause class adds the actual clause socket
  and the two complete sites for replacement and result.

  These independent subjects determine the same result under every compatible
  presentation, including when their joint intrinsic condition fails. A
  recovered coordinate does not supply a definition or clause: that origin
  remains part of the actual package relation.
\<close>

end
