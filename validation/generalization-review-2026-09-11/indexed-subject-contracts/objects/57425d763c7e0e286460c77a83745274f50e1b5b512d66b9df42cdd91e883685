theory Factor_Judgment_Retention_Presentations
  imports Factor_Judgment_Presentations Factor_Judgment_Retention
begin

section \<open>The actual program and call determine their retained material\<close>

lemma native_judgment_closed_fixed_iff:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "environment_closed E {pu,au} (native_judgment_demands E pu pr au ar) \<longleftrightarrow>
    native_judgment_environment E pu pr au ar=E"
proof
  assume closed: "environment_closed E {pu,au} (native_judgment_demands E pu pr au ar)"
  have roots: "{pu,au}\<subseteq>native_judgment_sources E pu pr au"
    by (auto simp: native_judgment_sources_def native_package_sources_def)
  show "native_judgment_environment E pu pr au ar=E"
    unfolding native_judgment_environment_def
    by (rule read_environment_closed_fixed[OF native_judgment_read_boundary[OF package app] closed roots])
next
  assume fixed: "native_judgment_environment E pu pr au ar=E"
  show "environment_closed E {pu,au} (native_judgment_demands E pu pr au ar)"
    using native_judgment_environment_closed[OF package app] by (simp only: fixed)
qed

theorem native_judgment_fixed_coverage:
  "native_judgment_environment E pu pr au ar=E \<longleftrightarrow>
    environment_uses E\<subseteq>read_environment_uses E (native_judgment_sources E pu pr au)
      (native_judgment_demands E pu pr au ar) \<and>
    rel_dom (environment_bindings E)\<subseteq>native_judgment_demands E pu pr au ar"
  by (simp only: native_judgment_environment_def read_environment_fixed_required_coverage)

lemma native_judgment_environment_domains:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "environment_uses (native_judgment_environment E pu pr au ar)=
      read_environment_uses E (native_judgment_sources E pu pr au) (native_judgment_demands E pu pr au ar)"
    and "rel_dom (environment_bindings (native_judgment_environment E pu pr au ar))=
      native_judgment_demands E pu pr au ar"
  unfolding native_judgment_environment_def
  using read_environment_use_equation[OF native_judgment_read_boundary[OF package app]]
    read_environment_domain[OF native_judgment_read_boundary[OF package app]] by blast+

theorem native_judgment_retention_claim_iff:
  assumes formed: "environment_formed E"
  shows "(\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
      F=native_judgment_environment E pu pr au ar) \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at F pu pr P \<and> native_application_at F au ar d t I K \<and>
      native_judgment_environment F pu pr au ar=F) \<and> environment_included F E"
proof
  assume "\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
    F=native_judgment_environment E pu pr au ar"
  then obtain P d t I K where reads: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    and same: "F=native_judgment_environment E pu pr au ar" by blast
  have retained: "native_package_at F pu pr P" "native_application_at F au ar d t I K"
    using native_judgment_environment_recovers(1,2)[OF reads] by (simp_all only: same)
  have fixed: "native_judgment_environment F pu pr au ar=F"
    by (simp only: same native_judgment_environment_idempotent[OF reads])
  have included: "environment_included F E" by (simp only: same; rule native_judgment_environment_included)
  show "(\<exists>P d t I K. native_package_at F pu pr P \<and> native_application_at F au ar d t I K \<and>
      native_judgment_environment F pu pr au ar=F) \<and> environment_included F E"
    using retained fixed included by blast
next
  assume "(\<exists>P d t I K. native_package_at F pu pr P \<and> native_application_at F au ar d t I K \<and>
    native_judgment_environment F pu pr au ar=F) \<and> environment_included F E"
  then obtain P d t I K where reads: "native_package_at F pu pr P" "native_application_at F au ar d t I K"
    and fixed: "native_judgment_environment F pu pr au ar=F" and included: "environment_included F E" by blast
  have package: "native_package_at E pu pr P" by (rule native_package_included[OF reads(1) included formed])
  have app: "native_application_at E au ar d t I K" by (rule native_application_included[OF reads(2) included formed])
  have same: "F=native_judgment_environment E pu pr au ar"
    using native_judgment_environment_extension[OF reads included formed] fixed by simp
  show "\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
    F=native_judgment_environment E pu pr au ar" using package app same by blast
qed

section \<open>Readable sources restrict the existing shared-context class\<close>

abbreviation judgment_context_term ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "judgment_context_term e pu pr au ar \<equiv>
    Pair_Term e (Pair_Term (Pair_Term pu pr) (Pair_Term au ar))"

abbreviation judgment_context_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern" where
  "judgment_context_pattern e pu pr au ar \<equiv>
    Pattern_Pair e (Pattern_Pair (Pattern_Pair pu pr) (Pattern_Pair au ar))"

abbreviation judgment_source_readable :: "judgment_context \<Rightarrow> bool" where
  "judgment_source_readable z \<equiv> \<exists>P d t I K.
    native_package_at (fst z) (fst (fst (snd z))) (snd (fst (snd z))) P \<and>
    native_application_at (fst z) (fst (snd (snd z))) (snd (snd (snd z))) d t I K"

abbreviation judgment_required_environment :: "judgment_context \<Rightarrow> local_address option artifact_environment" where
  "judgment_required_environment z \<equiv> native_judgment_environment (fst z)
    (fst (fst (snd z))) (snd (fst (snd z))) (fst (snd (snd z))) (snd (snd (snd z)))"

abbreviation judgment_required_slots :: "judgment_context \<Rightarrow> local_address option definition_site set" where
  "judgment_required_slots z \<equiv> native_judgment_demands (fst z)
    (fst (fst (snd z))) (snd (fst (snd z))) (fst (snd (snd z))) (snd (snd (snd z)))"

abbreviation judgment_required_uses :: "judgment_context \<Rightarrow> local_address option set" where
  "judgment_required_uses z \<equiv> read_environment_uses (fst z)
    (native_judgment_sources (fst z) (fst (fst (snd z))) (snd (fst (snd z))) (fst (snd (snd z))))
    (judgment_required_slots z)"

lemma judgment_source_readable_formed:
  assumes "judgment_source_readable z"
  shows "judgment_context_formed z"
proof -
  obtain P d t I K where package: "native_package_at (fst z) (fst (fst (snd z))) (snd (fst (snd z))) P"
    and app: "native_application_at (fst z) (fst (snd (snd z))) (snd (snd (snd z))) d t I K"
    using assms by blast
  have formed: "environment_formed (fst z)"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have sites: "(fst (fst (snd z)),snd (fst (snd z)))\<in>environment_positions (fst z)"
    "(fst (snd (snd z)),snd (snd (snd z)))\<in>environment_positions (fst z)"
    by (rule native_judgment_positions[OF package app])+
  show ?thesis using formed sites by (simp add: judgment_context_formed_def)
qed

definition judgment_source_presents :: "judgment_context \<Rightarrow> factor_term \<Rightarrow> bool" where
  "judgment_source_presents z p \<longleftrightarrow> judgment_source_readable z \<and> judgment_context_presents z p"

lemma judgment_source_presentation_fields:
  "judgment_source_presents (E,((pu,pr),(au,ar))) p \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K) \<and>
    (\<exists>e. environment_value_presents E e \<and>
      p=judgment_context_term e (use_data_term pu) (Payload_Term pr) (use_data_term au) (Payload_Term ar))"
proof -
  have sites: "(pu,pr)\<in>environment_positions E \<and> (au,ar)\<in>environment_positions E"
    if reading: "\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K"
  proof -
    obtain P d t I K where reads: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
      using reading by blast
    show ?thesis using native_judgment_positions[OF reads] by blast
  qed
  show ?thesis
    by (simp only: judgment_source_presents_def judgment_value_presents_def fst_conv snd_conv site_data_term_def)
      (use sites in blast)
qed

theorem judgment_source_presentation_class:
  "presentation_class judgment_source_presents judgment_source_readable (\<lambda>p. \<exists>z. judgment_source_presents z p)"
proof -
  have restricted: "presentation_class (\<lambda>z p. judgment_source_readable z \<and> judgment_context_presents z p)
      judgment_source_readable (\<lambda>p. \<exists>z. judgment_source_readable z \<and> judgment_context_presents z p)"
    by (rule presentation_class_subdomain[OF judgment_context_presentation_class])
      (rule judgment_source_readable_formed; assumption)
  show ?thesis using restricted by (simp only: judgment_source_presents_def[abs_def])
qed

interpretation judgment_sources: presentation_class judgment_source_presents judgment_source_readable
  "\<lambda>p. \<exists>z. judgment_source_presents z p"
  by (rule judgment_source_presentation_class)

lemma judgment_source_presents_formed:
  assumes "judgment_source_presents z p"
  shows "term_formed p \<and> self_contained_term p"
  using assms judgment_context_formed_value by (auto simp: judgment_source_presents_def)

theorem judgment_source_quotation_class:
  "presentation_class
    (composed_presentation judgment_source_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    judgment_source_readable
    (\<lambda>p. \<exists>t. (\<exists>z. judgment_source_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF judgment_source_presentation_class])
    (use judgment_source_presents_formed in blast)

definition judgment_closed_source_presents :: "judgment_context \<Rightarrow> factor_term \<Rightarrow> bool" where
  "judgment_closed_source_presents z p \<longleftrightarrow>
    judgment_source_presents z p \<and> judgment_required_environment z=fst z"

theorem judgment_closed_source_presentation_class:
  "presentation_class judgment_closed_source_presents
    (\<lambda>z. judgment_source_readable z \<and> judgment_required_environment z=fst z)
    (\<lambda>p. \<exists>z. judgment_closed_source_presents z p)"
proof -
  let ?D="\<lambda>z. judgment_source_readable z \<and> judgment_required_environment z=fst z"
  have restricted: "presentation_class (\<lambda>z p. ?D z \<and> judgment_source_presents z p) ?D
      (\<lambda>p. \<exists>z. ?D z \<and> judgment_source_presents z p)"
    by (rule presentation_class_subdomain[OF judgment_source_presentation_class]) blast
  have reading: "(?D z \<and> judgment_source_presents z p) \<longleftrightarrow> judgment_closed_source_presents z p" for z p
    using judgment_sources.subject_boundary[of z p]
    by (simp only: judgment_closed_source_presents_def) blast
  show ?thesis using restricted by (simp only: reading)
qed

theorem judgment_closed_source_quotation_class:
  "presentation_class
    (composed_presentation judgment_closed_source_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. judgment_source_readable z \<and> judgment_required_environment z=fst z)
    (\<lambda>p. \<exists>t. (\<exists>z. judgment_closed_source_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF judgment_closed_source_presentation_class])
    (use judgment_source_presents_formed in \<open>auto simp: judgment_closed_source_presents_def\<close>)

section \<open>A report presents the environment determined by the source\<close>

definition judgment_retention_report_presents ::
  "(judgment_context\<times>local_address option artifact_environment) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "judgment_retention_report_presents z p \<longleftrightarrow>
    snd z=judgment_required_environment (fst z) \<and>
    factor_pair_presents judgment_source_presents environment_value_presents z p"

lemma judgment_required_environment_formed:
  assumes "judgment_source_readable z"
  shows "environment_formed (judgment_required_environment z)"
proof -
  obtain P d t I K where package: "native_package_at (fst z) (fst (fst (snd z))) (snd (fst (snd z))) P"
    and app: "native_application_at (fst z) (fst (snd (snd z))) (snd (snd (snd z))) d t I K"
    using assms by blast
  show ?thesis by (rule native_judgment_environment_recovers(3)[OF package app])
qed

lemma judgment_required_environment_domains:
  assumes "judgment_source_readable z"
  shows "environment_uses (judgment_required_environment z)=judgment_required_uses z"
    and "rel_dom (environment_bindings (judgment_required_environment z))=judgment_required_slots z"
proof -
  obtain P d t I K where package: "native_package_at (fst z) (fst (fst (snd z))) (snd (fst (snd z))) P"
    and app: "native_application_at (fst z) (fst (snd (snd z))) (snd (snd (snd z))) d t I K"
    using assms by blast
  show "environment_uses (judgment_required_environment z)=judgment_required_uses z"
    by (rule native_judgment_environment_domains(1)[OF package app])
  show "rel_dom (environment_bindings (judgment_required_environment z))=judgment_required_slots z"
    by (rule native_judgment_environment_domains(2)[OF package app])
qed

theorem judgment_retained_context:
  assumes source: "judgment_source_readable z"
  shows "judgment_source_readable (judgment_required_environment z,snd z)"
    and "judgment_required_environment (judgment_required_environment z,snd z)=judgment_required_environment z"
    and "judgment_required_uses (judgment_required_environment z,snd z)=judgment_required_uses z"
    and "judgment_required_slots (judgment_required_environment z,snd z)=judgment_required_slots z"
proof -
  obtain P d t I K where package: "native_package_at (fst z) (fst (fst (snd z))) (snd (fst (snd z))) P"
    and app: "native_application_at (fst z) (fst (snd (snd z))) (snd (snd (snd z))) d t I K"
    using source by blast
  have kept: "native_package_at (judgment_required_environment z) (fst (fst (snd z))) (snd (fst (snd z))) P"
    "native_application_at (judgment_required_environment z) (fst (snd (snd z))) (snd (snd (snd z))) d t I K"
    using native_judgment_environment_recovers(1,2)[OF package app] by blast+
  show retained: "judgment_source_readable (judgment_required_environment z,snd z)"
    by (rule exI[of _ P], rule exI[of _ d], rule exI[of _ t], rule exI[of _ I], rule exI[of _ K])
      (use kept in simp)
  show fixed: "judgment_required_environment (judgment_required_environment z,snd z)=judgment_required_environment z"
    using native_judgment_environment_idempotent[OF package app] by simp
  show "judgment_required_uses (judgment_required_environment z,snd z)=judgment_required_uses z"
    using judgment_required_environment_domains(1)[OF retained] judgment_required_environment_domains(1)[OF source] fixed by simp
  show "judgment_required_slots (judgment_required_environment z,snd z)=judgment_required_slots z"
    using judgment_required_environment_domains(2)[OF retained] judgment_required_environment_domains(2)[OF source] fixed by simp
qed

theorem judgment_retention_report_presentation_class:
  "presentation_class judgment_retention_report_presents
    (\<lambda>z. judgment_source_readable (fst z) \<and> snd z=judgment_required_environment (fst z))
    (\<lambda>p. \<exists>z. judgment_retention_report_presents z p)"
proof -
  let ?R="factor_pair_presents judgment_source_presents environment_value_presents"
  let ?D="\<lambda>z. judgment_source_readable (fst z) \<and> snd z=judgment_required_environment (fst z)"
  let ?A="\<lambda>t. \<exists>p q. (\<exists>z. judgment_source_presents z p) \<and>
    (26,q)\<in>positive_meaning environment_admission_system \<and> t=Pair_Term p q"
  have raw: "presentation_class ?R (\<lambda>z. judgment_source_readable (fst z) \<and> environment_formed (snd z)) ?A"
    by (rule factor_pair_class[OF judgment_source_presentation_class environment_presentations.presentation_class_axioms])
  have restricted: "presentation_class (\<lambda>z p. ?D z \<and> ?R z p) ?D (\<lambda>p. \<exists>z. ?D z \<and> ?R z p)"
  proof (rule presentation_class_subdomain[OF raw])
    fix z assume domain: "?D z"
    have readable: "judgment_source_readable (fst z)" using domain by blast
    have formed: "environment_formed (judgment_required_environment (fst z))"
      by (rule judgment_required_environment_formed[OF readable])
    show "judgment_source_readable (fst z) \<and> environment_formed (snd z)"
      using domain formed by simp
  qed
  have boundary: "judgment_source_readable (fst z)" if product: "?R z p" for z p
  proof -
    obtain a b where source: "judgment_source_presents (fst z) a"
      using product by (auto simp: factor_pair_presents_def)
    show ?thesis by (rule judgment_sources.subject_boundary[OF source])
  qed
  have reading: "(?D z \<and> ?R z p) \<longleftrightarrow> judgment_retention_report_presents z p" for z p
    using boundary[of z p] by (simp only: judgment_retention_report_presents_def) blast
  show ?thesis using restricted by (simp only: reading)
qed

lemma judgment_retention_report_formed:
  assumes "judgment_retention_report_presents z p"
  shows "term_formed p \<and> self_contained_term p"
proof -
  obtain a b where source: "judgment_source_presents (fst z) a"
    and expected: "environment_value_presents (snd z) b" and shape: "p=Pair_Term a b"
    using assms by (auto simp: judgment_retention_report_presents_def factor_pair_presents_def)
  have left: "term_formed a \<and> self_contained_term a" by (rule judgment_source_presents_formed[OF source])
  have right: "term_formed b \<and> self_contained_term b" using environment_value_presents_formed[OF expected] by blast
  show ?thesis using left right by (simp add: shape)
qed

theorem judgment_retention_report_quotation_class:
  "presentation_class
    (composed_presentation judgment_retention_report_presents (\<lambda>t p. complete_data_quoted_at (fst p) (snd p) t))
    (\<lambda>z. judgment_source_readable (fst z) \<and> snd z=judgment_required_environment (fst z))
    (\<lambda>p. \<exists>t. (\<exists>z. judgment_retention_report_presents z t) \<and> complete_data_quoted_at (fst p) (snd p) t)"
  by (rule complete_quotation_presentation_class[OF judgment_retention_report_presentation_class])
    (use judgment_retention_report_formed in blast)

lemma judgment_retention_report_relation:
  "(\<exists>z. judgment_retention_report_presents z (Pair_Term p q)) \<longleftrightarrow>
    presented_relation judgment_source_presents environment_value_presents
      (\<lambda>z F. F=judgment_required_environment z) p q"
  by (auto simp: judgment_retention_report_presents_def factor_pair_presents_def presented_relation_def)

text \<open>
  The subject is the existing complete environment with its actual program
  and call sites. Native package and application reading constrain this
  subject; their uniquely recovered values need no additional stored field.
  Callee membership, interface acceptance, truth, and proof are separate.

  The retained environment is the existing grammar-derived restriction.
  Its complete use and binding domains determine the coverage test.
  Readability and a fixed point in an included environment recover precisely
  the original source's least environment. Products and subdomains give all
  compatible source, closed-source, and report presentations.
\<close>

end
