theory Factor_Construction_Cause_Presentations
  imports Factor_Base_Cause_Presentations Factor_Construction_Permission_Admission
begin

section \<open>The original judgments and the actual permission profile remain distinct\<close>

abbreviation construction_judgment_context :: "judgment_context \<Rightarrow> construction_account \<Rightarrow> bool" where
  "construction_judgment_context j a \<equiv> construction_judgment_at (fst j)
    (fst (fst (snd j))) (snd (fst (snd j))) (fst (snd (snd j))) (snd (snd (snd j)))
    (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a)"

abbreviation recorded_construction_context :: "generation_source \<Rightarrow> construction_account \<Rightarrow> bool" where
  "recorded_construction_context z a \<equiv> recorded_construction_cause_at (fst (fst z))
    (fst (snd (fst z))) (snd (snd (fst z))) (snd z)
    (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a)"

definition construction_context_profile where
  "construction_context_profile C k j \<longleftrightarrow> (\<exists>d t I K.
    native_application_at (fst j) (fst (snd (snd j))) (snd (snd (snd j))) d t I K \<and>
    native_related_test_package C k (fst j) (fst (fst (snd j))) (snd (fst (snd j))) d)"

definition construction_profile_context where
  "construction_profile_context C k j a \<longleftrightarrow>
    construction_judgment_context j a \<and> construction_context_profile C k j"

definition recorded_construction_profile where
  "recorded_construction_profile C k z a \<longleftrightarrow> recorded_construction_context z a \<and>
    (\<exists>j. generation_recorded_scope z j \<and> construction_context_profile C k j)"

lemma construction_context_profile_at_reads:
  assumes app: "native_application_at F au ar d t I K"
  shows "construction_context_profile C k (F,((pu,pr),(au,ar))) \<longleftrightarrow>
    native_related_test_package C k F pu pr d"
  proof
  assume read: "construction_context_profile C k (F,((pu,pr),(au,ar)))"
  obtain e z J L where other: "native_application_at F au ar e z J L"
    and profile: "native_related_test_package C k F pu pr e"
    using read by (auto simp: construction_context_profile_def)
  have same: "e=d" using native_application_unique[OF other app] by blast
  show "native_related_test_package C k F pu pr d" using profile same by simp
next
  assume profile: "native_related_test_package C k F pu pr d"
  show "construction_context_profile C k (F,((pu,pr),(au,ar)))"
    unfolding construction_context_profile_def
    by (simp only: fst_conv snd_conv; rule exI[of _ d], rule exI[of _ t], rule exI[of _ I], rule exI[of _ K])
      (rule conjI[OF app profile])
qed

lemma construction_profile_context_boundary:
  assumes "construction_profile_context C k j a"
  shows "judgment_source_readable j \<and> construction_account_domain a"
  proof -
  obtain P d t I K where package: "native_package_at (fst j) (fst (fst (snd j))) (snd (fst (snd j))) P"
    and app: "native_application_at (fst j) (fst (snd (snd j))) (snd (snd (snd j))) d t I K"
    and built: "source_constructs (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a)"
    and coords: "construction_coordinates_formed (snd (fst a)) (snd a)"
    using assms by (auto simp: construction_profile_context_def construction_judgment_at_def factor_constructs_def)
  have readable: "judgment_source_readable j"
    by (rule exI[of _ P], rule exI[of _ d], rule exI[of _ t], rule exI[of _ I], rule exI[of _ K])
      (rule conjI[OF package app])
  show ?thesis using readable built coords by blast
qed

lemma construction_profile_context_unique:
  assumes "construction_profile_context C k j a" "construction_profile_context C k j b"
  shows "a=b"
  using construction_judgment_account_unique[OF conjunct1[OF assms(1)[unfolded construction_profile_context_def]]
    conjunct1[OF assms(2)[unfolded construction_profile_context_def]]]
  by (auto simp: prod_eq_iff)

lemma recorded_construction_context_join:
  "recorded_construction_context z a \<longleftrightarrow> (\<exists>j. generation_recorded_scope z j \<and>
    judgment_required_environment j=fst j \<and>
    generation_payload (snd z)=Whole_Artifact (construction_account_output a) \<and> construction_judgment_context j a)"
  by (auto simp: recorded_construction_cause_at_def generation_recorded_scope_def; metis fst_conv snd_conv)

lemma recorded_construction_profile_join:
  "recorded_construction_profile C k z a \<longleftrightarrow> (\<exists>j. generation_recorded_scope z j \<and>
    judgment_required_environment j=fst j \<and>
    generation_payload (snd z)=Whole_Artifact (construction_account_output a) \<and> construction_profile_context C k j a)"
  proof
  assume read: "recorded_construction_profile C k z a"
  obtain j where scope: "generation_recorded_scope z j" and profile: "construction_context_profile C k j"
    using read by (auto simp: recorded_construction_profile_def)
  have original: "recorded_construction_context z a" using read by (simp add: recorded_construction_profile_def)
  obtain h where other: "generation_recorded_scope z h" and fixed: "judgment_required_environment h=fst h"
    and payload: "generation_payload (snd z)=Whole_Artifact (construction_account_output a)"
    and judged: "construction_judgment_context h a"
    using original by (simp only: recorded_construction_context_join; blast)
  have same: "h=j" by (rule generation_recorded_scope_unique[OF other scope])
  show "\<exists>j. generation_recorded_scope z j \<and> judgment_required_environment j=fst j \<and>
    generation_payload (snd z)=Whole_Artifact (construction_account_output a) \<and> construction_profile_context C k j a"
    by (rule exI[of _ j]) (use scope profile fixed payload judged same in \<open>simp add: construction_profile_context_def\<close>)
next
  assume "\<exists>j. generation_recorded_scope z j \<and> judgment_required_environment j=fst j \<and>
    generation_payload (snd z)=Whole_Artifact (construction_account_output a) \<and> construction_profile_context C k j a"
  then obtain j where scope: "generation_recorded_scope z j" and fixed: "judgment_required_environment j=fst j"
    and payload: "generation_payload (snd z)=Whole_Artifact (construction_account_output a)"
    and judged: "construction_judgment_context j a" and profile: "construction_context_profile C k j"
    by (auto simp: construction_profile_context_def)
  have original: "recorded_construction_context z a"
    by (simp only: recorded_construction_context_join; rule exI[of _ j]) (use scope fixed payload judged in blast)
  show "recorded_construction_profile C k z a"
    unfolding recorded_construction_profile_def
    by (rule conjI[OF original], rule exI[of _ j], rule conjI[OF scope profile])
qed

lemma recorded_construction_profile_at_scope:
  assumes "generation_recorded_scope z j"
  shows "recorded_construction_profile C k z a \<longleftrightarrow>
    judgment_required_environment j=fst j \<and>
    generation_payload (snd z)=Whole_Artifact (construction_account_output a) \<and> construction_profile_context C k j a"
  proof -
  have unique: "generation_recorded_scope z h \<longleftrightarrow> h=j" for h
    using assms generation_recorded_scope_unique[OF _ assms] by blast
  show ?thesis by (simp only: recorded_construction_profile_join unique; simp)
qed

lemma recorded_construction_profile_boundary:
  assumes "recorded_construction_profile C k z a"
  shows "generation_at_context (fst z) (snd z) \<and> construction_account_domain a"
  proof -
  obtain j where scope: "generation_recorded_scope z j" and relation: "construction_profile_context C k j a"
    using assms by (simp only: recorded_construction_profile_join; blast)
  have source: "generation_at_context (fst z) (snd z)" by (rule generation_recorded_scope_source[OF scope])
  have account: "construction_account_domain a" by (rule conjunct2[OF construction_profile_context_boundary[OF relation]])
  show ?thesis by (rule conjI[OF source account])
qed

lemma recorded_construction_profile_unique:
  assumes "recorded_construction_profile C k z a" "recorded_construction_profile C k z b"
  shows "a=b"
  proof -
  obtain j where first: "generation_recorded_scope z j" and left: "construction_profile_context C k j a"
    using assms(1) by (simp only: recorded_construction_profile_join; blast)
  obtain h where second: "generation_recorded_scope z h" and right: "construction_profile_context C k h b"
    using assms(2) by (simp only: recorded_construction_profile_join; blast)
  have same: "h=j" by (rule generation_recorded_scope_unique[OF second first])
  have other: "construction_profile_context C k j b" using right same by simp
  show ?thesis by (rule construction_profile_context_unique[OF left other])
qed

theorem recorded_construction_profile_outer_invariance:
  assumes first: "generation_at_context (fst z) (snd z)" and second: "generation_at_context (fst w) (snd w)"
    and cause: "generation_cause (snd z)=generation_cause (snd w)"
    and payload: "generation_payload (snd z)=generation_payload (snd w)"
  shows "recorded_construction_profile C k z a \<longleftrightarrow> recorded_construction_profile C k w a"
proof -
  have scopes: "generation_recorded_scope z j \<longleftrightarrow> generation_recorded_scope w j" for j
    using first second cause by (simp add: generation_recorded_scope_def generation_judgment_scope_at_def)
  show ?thesis by (simp only: recorded_construction_profile_join scopes payload)
qed

section \<open>Complete sources determine accounts; reports present every compatible account\<close>

definition construction_profile_source_presents where
  "construction_profile_source_presents C k z p \<longleftrightarrow>
    judgment_context_presents (fst z) p \<and> construction_profile_context C k (fst z) (snd z)"

definition construction_profile_report_presents where
  "construction_profile_report_presents C k z p \<longleftrightarrow>
    construction_profile_context C k (fst z) (snd z) \<and>
    factor_pair_presents judgment_context_presents construction_account_presents z p"

definition recorded_construction_source_presents where
  "recorded_construction_source_presents C k z p \<longleftrightarrow>
    generation_source_presents (fst z) p \<and> recorded_construction_profile C k (fst z) (snd z)"

definition recorded_construction_report_presents where
  "recorded_construction_report_presents C k z p \<longleftrightarrow>
    recorded_construction_profile C k (fst z) (snd z) \<and>
    factor_pair_presents generation_source_presents construction_account_presents z p"

theorem construction_profile_source_class:
  "presentation_class (construction_profile_source_presents C k)
    (\<lambda>z. construction_profile_context C k (fst z) (snd z))
    (\<lambda>p. \<exists>z. construction_profile_source_presents C k z p)"
  unfolding construction_profile_source_presents_def
proof (rule presentation_class_determined_subdomain[where link="construction_profile_context C k",
    OF judgment_context_presentation_class construction_profile_context_unique])
  fix j a assume relation: "construction_profile_context C k j a"
  show "judgment_context_formed j"
    by (rule judgment_source_readable_formed[OF conjunct1[OF construction_profile_context_boundary[OF relation]]])
qed

theorem construction_profile_report_class:
  "presentation_class (construction_profile_report_presents C k)
    (\<lambda>z. construction_profile_context C k (fst z) (snd z))
    (\<lambda>p. \<exists>z. construction_profile_report_presents C k z p)"
  unfolding construction_profile_report_presents_def
  by (rule factor_pair_subdomain_class[OF judgment_context_presentation_class construction_account_presentation_class])
    (use construction_profile_context_boundary judgment_source_readable_formed in blast)

theorem recorded_construction_source_class:
  "presentation_class (recorded_construction_source_presents C k)
    (\<lambda>z. recorded_construction_profile C k (fst z) (snd z))
    (\<lambda>p. \<exists>z. recorded_construction_source_presents C k z p)"
  unfolding recorded_construction_source_presents_def
proof (rule presentation_class_determined_subdomain[where link="recorded_construction_profile C k",
    OF generation_source_presentation_class recorded_construction_profile_unique])
  fix z a assume relation: "recorded_construction_profile C k z a"
  show "generation_at_context (fst z) (snd z)"
    by (rule conjunct1[OF recorded_construction_profile_boundary[OF relation]])
qed

theorem recorded_construction_report_class:
  "presentation_class (recorded_construction_report_presents C k)
    (\<lambda>z. recorded_construction_profile C k (fst z) (snd z))
    (\<lambda>p. \<exists>z. recorded_construction_report_presents C k z p)"
  unfolding recorded_construction_report_presents_def
  by (rule factor_pair_subdomain_class[OF generation_source_presentation_class construction_account_presentation_class])
    (use recorded_construction_profile_boundary in blast)

text \<open>
  The source judgments are unchanged. The sufficient permission profile is an
  explicit additional restriction on their actual program and application.
  No program, account, proof, or replacement policy is added to a recorded
  cause. The account is determined by the actual call. A report may present
  that account with any permitted ordering; its output remains derived from
  the original input, base, selection, and origin fields.

  The general determined-component and product-subdomain rules supply all four
  classes. Their whole domains are fixed before native admission is proved.
  An independently established comparison reference is still required for
  the sufficient profile to discharge global construction permission.
\<close>

end
