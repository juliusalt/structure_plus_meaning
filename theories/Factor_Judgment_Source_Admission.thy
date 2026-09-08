theory Factor_Judgment_Source_Admission
  imports Factor_Judgment_Retention_Clauses
begin

section \<open>One complete environment supplies the actual program and application\<close>

lemma judgment_source_valuation:
  "(178,z)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>i\<in>{0,1,2,3,4,5,6,7,8}. term_formed (h i)) \<and>
      z=judgment_context_term (h 0) (h 1) (h 2) (h 3) (h 4) \<and>
      (80,source_root_argument (h 0) (h 1) (h 2))\<in>positive_meaning package_admission_system \<and>
      (58,application_reading_argument (h 0) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8))
        \<in>positive_meaning application_reading_system)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: judgment_source_schema_def schema_variables_def judgment_retention_call judgment_retention_components)

lemma judgment_source_fields:
  "(178,z)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>e pu pr au ar d t i k. z=judgment_context_term e pu pr au ar \<and>
      (80,source_root_argument e pu pr)\<in>positive_meaning package_admission_system \<and>
      (58,application_reading_argument e au ar d t i k)\<in>positive_meaning application_reading_system)"
proof
  assume "(178,z)\<in>positive_meaning judgment_retention_system"
  then show "\<exists>e pu pr au ar d t i k. z=judgment_context_term e pu pr au ar \<and>
    (80,source_root_argument e pu pr)\<in>positive_meaning package_admission_system \<and>
    (58,application_reading_argument e au ar d t i k)\<in>positive_meaning application_reading_system"
    by (simp only: judgment_source_valuation) blast
next
  assume "\<exists>e pu pr au ar d t i k. z=judgment_context_term e pu pr au ar \<and>
    (80,source_root_argument e pu pr)\<in>positive_meaning package_admission_system \<and>
    (58,application_reading_argument e au ar d t i k)\<in>positive_meaning application_reading_system"
  then obtain e pu pr au ar d t i k where shape: "z=judgment_context_term e pu pr au ar"
    and package: "(80,source_root_argument e pu pr)\<in>positive_meaning package_admission_system"
    and app: "(58,application_reading_argument e au ar d t i k)\<in>positive_meaning application_reading_system" by blast
  have formed: "term_formed e" "term_formed pu" "term_formed pr" "term_formed au" "term_formed ar"
    "term_formed d" "term_formed t" "term_formed i" "term_formed k"
    using schema_call_formed_target[OF positive_meaning_formed[OF package]]
      schema_call_formed_target[OF positive_meaning_formed[OF app]] by auto
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then au
    else if j=4 then ar else if j=5 then d else if j=6 then t else if j=7 then i else k"
  show "(178,z)\<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_source_valuation; rule exI[of _ ?h]) (use shape package app formed in auto)
qed

theorem judgment_source_exact:
  "(178,p)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> (\<exists>z. judgment_source_presents z p)"
proof
  assume "(178,p)\<in>positive_meaning judgment_retention_system"
  then obtain e x y a b d t i k where shape: "p=judgment_context_term e x y a b"
    and package: "(80,source_root_argument e x y)\<in>positive_meaning package_admission_system"
    and app: "(58,application_reading_argument e a b d t i k)\<in>positive_meaning application_reading_system"
    by (simp only: judgment_source_fields) blast
  obtain E pu pr P where source: "environment_value_presents E e"
    and program: "x=use_data_term pu" "y=Payload_Term pr" "native_package_at E pu pr P"
    using package by (auto simp: package_admission_exact)
  obtain au ar du da Is Ks where call: "a=use_data_term au" "b=Payload_Term ar"
    "native_application_at E au ar (du,da) t (set Is) (set Ks)"
    using app by (simp only: application_reading_at_source[OF source]) blast
  have readable: "\<exists>P d v I K. native_package_at E pu pr P \<and> native_application_at E au ar d v I K"
    by (rule exI[of _ P], rule exI[of _ "(du,da)"], rule exI[of _ t],
      rule exI[of _ "set Is"], rule exI[of _ "set Ks"]) (use program(3) call(3) in blast)
  have body: "\<exists>e'. environment_value_presents E e' \<and>
      p=judgment_context_term e' (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)"
    by (rule exI[of _ e]) (use source program(1,2) call(1,2) shape in simp)
  show "\<exists>z. judgment_source_presents z p"
    by (rule exI[of _ "(E,((pu,pr),(au,ar)))"])
      (simp only: judgment_source_presentation_fields; use readable body in blast)
next
  assume "\<exists>z. judgment_source_presents z p"
  then obtain z where presented: "judgment_source_presents z p" by blast
  obtain E pu pr au ar where coordinates: "z=(E,((pu,pr),(au,ar)))" by (cases z; auto)
  obtain e P d t I K where source: "environment_value_presents E e"
    and shape: "p=judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar)"
    and package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
    using presented by (simp only: coordinates judgment_source_presentation_fields) blast
  have program: "(80,source_root_argument e (use_data_term pu) (Payload_Term pr))\<in>positive_meaning package_admission_system"
    by (rule package_admission_complete[OF source package])
  obtain i k where call: "(58,application_reading_argument e (use_data_term au) (Payload_Term ar)
    (definition_site_value d) t i k)\<in>positive_meaning application_reading_system"
    using application_reading_value[OF source app] by blast
  show "(178,p)\<in>positive_meaning judgment_retention_system"
    by (simp only: judgment_source_fields) (use program call shape in blast)
qed

theorem judgment_source_native_class:
  "presentation_class judgment_source_presents judgment_source_readable
    (\<lambda>p. (178,p)\<in>positive_meaning judgment_retention_system)"
  using judgment_source_presentation_class by (simp only: judgment_source_exact)

corollary judgment_source_on_values:
  assumes source: "environment_value_presents E e"
  shows "(178,judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar))
      \<in>positive_meaning judgment_retention_system \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K)"
proof -
  have fields: "(178,judgment_context_term e pu pr au ar)\<in>positive_meaning judgment_retention_system \<longleftrightarrow>
      (80,source_root_argument e pu pr)\<in>positive_meaning package_admission_system \<and>
      (\<exists>d t i k. (58,application_reading_argument e au ar d t i k)\<in>positive_meaning application_reading_system)"
    for pu pr au ar
    by (simp only: judgment_source_fields factor_term.inject) blast
  have application: "(\<exists>d t i k. (58,application_reading_argument e (use_data_term au) (Payload_Term ar) d t i k)
      \<in>positive_meaning application_reading_system) \<longleftrightarrow>
    (\<exists>d t I K. native_application_at E au ar d t I K)"
  proof
    assume "\<exists>d t i k. (58,application_reading_argument e (use_data_term au) (Payload_Term ar) d t i k)
      \<in>positive_meaning application_reading_system"
    then obtain d t i k where read: "(58,application_reading_argument e (use_data_term au) (Payload_Term ar) d t i k)
      \<in>positive_meaning application_reading_system" by blast
    obtain du da Is Ks where app: "native_application_at E au ar (du,da) t (set Is) (set Ks)"
      using read
      by (simp only: application_reading_at_source[OF source])
        (auto simp: inj_eq[OF use_data_term_injective])
    show "\<exists>d t I K. native_application_at E au ar d t I K"
      by (rule exI[of _ "(du,da)"], rule exI[of _ t], rule exI[of _ "set Is"], rule exI[of _ "set Ks"])
        (rule app)
  next
    assume "\<exists>d t I K. native_application_at E au ar d t I K"
    then obtain d t I K where app: "native_application_at E au ar d t I K" by blast
    show "\<exists>d t i k. (58,application_reading_argument e (use_data_term au) (Payload_Term ar) d t i k)
      \<in>positive_meaning application_reading_system"
      using application_reading_value[OF source app] by blast
  qed
  show ?thesis
    by (simp only: fields package_admission_on_values[OF source] application) blast
qed

corollary judgment_source_on_context:
  assumes coordinates: "judgment_context_presents z p"
  shows "(178,p)\<in>positive_meaning judgment_retention_system \<longleftrightarrow> judgment_source_readable z"
proof -
  have unique: "w=z" if "judgment_context_presents w p" for w
    by (rule judgments.recovery[OF that coordinates])
  show ?thesis by (simp only: judgment_source_exact judgment_source_presents_def) (use coordinates unique in blast)
qed

lemma judgment_source_context_formed:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and app: "native_application_at E au ar d t I K"
  shows "term_formed (judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar))"
proof -
  have readable: "\<exists>P d v J L. native_package_at E pu pr P \<and> native_application_at E au ar d v J L"
    by (rule exI[of _ P], rule exI[of _ d], rule exI[of _ t], rule exI[of _ I], rule exI[of _ K])
      (use package app in blast)
  have present: "judgment_source_presents (E,((pu,pr),(au,ar)))
      (judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar))"
    by (simp only: judgment_source_presentation_fields) (use readable source in blast)
  show ?thesis using judgment_source_presents_formed[OF present] by blast
qed

text \<open>
  Source admission has the exact domain of an actual native package and raw
  application reading in the same complete environment. It does not ask
  whether that callee belongs to the package, accepts the operand, or holds.
  The existing context class retains every source table and both actual sites.
\<close>

end
