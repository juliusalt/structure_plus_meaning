theory Factor_Certified_Recorded_Cause
  imports Factor_Recorded_Cause Factor_Certified_Construction
begin

section \<open>Replay evidence remains outside the recorded scope\<close>

definition certified_recorded_cause_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option definition_site \<Rightarrow>
    exact_artifact list \<Rightarrow> (local_address\<times>exact_artifact) set \<Rightarrow>
    addressed_construction \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "certified_recorded_cause_at E gu gr G H root xs B W R \<longleftrightarrow>
    (\<exists>F pu pr au ar P d t I K. generation_judgment_scope_at E gu gr G F pu pr au ar \<and>
      F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
      native_package_at F pu pr P \<and> native_application_at F au ar d t I K \<and>
      environment_included F H \<and> certified_construction_at H pu pr au ar root xs B W R)"

theorem certified_recorded_cause_exact_join:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P" and app: "native_application_at F au ar d t I K"
    and included: "environment_included F H" and hf: "environment_formed H"
  shows "certified_recorded_cause_at E gu gr G H root xs B W R \<longleftrightarrow>
    recorded_construction_cause_at E gu gr G xs B W R \<and> native_replay_at H pu pr au ar root {}"
proof -
  have retained: "native_package_at H pu pr P" "native_application_at H au ar d t I K"
    by (rule native_package_included[OF package included hf], rule native_application_included[OF app included hf])
  have fixed_scope: "certified_recorded_cause_at E gu gr G H root xs B W R \<longleftrightarrow>
    F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
    certified_construction_at H pu pr au ar root xs B W R"
  proof
    assume certified: "certified_recorded_cause_at E gu gr G H root xs B W R"
    obtain F' qu qr bu br where other: "generation_judgment_scope_at E gu gr G F' qu qr bu br"
      "F'=native_judgment_environment F' qu qr bu br" "generation_payload G=Whole_Artifact R"
      "certified_construction_at H qu qr bu br root xs B W R"
      using certified unfolding certified_recorded_cause_at_def by blast
    have same: "F'=F \<and> qu=pu \<and> qr=pr \<and> bu=au \<and> br=ar"
      by (rule generation_judgment_scope_unique[OF other(1) scope refl])
    show "F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
      certified_construction_at H pu pr au ar root xs B W R"
      using other(2-4) same by simp
  next
    assume "F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
      certified_construction_at H pu pr au ar root xs B W R"
    then show "certified_recorded_cause_at E gu gr G H root xs B W R"
      using scope package app included unfolding certified_recorded_cause_at_def by blast
  qed
  show ?thesis
    by (simp only: fixed_scope certified_construction_exact_join[OF retained]
      recorded_construction_cause_with_scope[OF scope] construction_judgment_with_reads[OF package app]; blast)
qed

theorem certified_recorded_cause_sound:
  assumes certified: "certified_recorded_cause_at E gu gr G H root xs B W R"
  shows "recorded_construction_cause_at E gu gr G xs B W R"
proof -
  obtain F pu pr au ar P d t I K where scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P" and app: "native_application_at F au ar d t I K"
    and included: "environment_included F H"
    and construction: "certified_construction_at H pu pr au ar root xs B W R"
    using certified unfolding certified_recorded_cause_at_def by blast
  obtain Q where package_h: "native_package_at H pu pr Q"
    using construction unfolding certified_construction_at_def by blast
  have hf: "environment_formed H"
    using native_package_projection(1)[OF package_h] by (simp add: native_package_formed_def)
  show ?thesis using certified_recorded_cause_exact_join[OF scope package app included hf] certified by blast
qed

theorem certified_recorded_account_unique:
  assumes first: "certified_recorded_cause_at E gu gr G H root xs B W R"
    and second: "certified_recorded_cause_at E' hu hr G' H' other ys C X S"
    and cause: "generation_cause G=generation_cause G'"
  shows "xs=ys \<and> B=C \<and> W=X \<and> R=S"
  by (rule recorded_construction_account_unique[
    OF certified_recorded_cause_sound[OF first] certified_recorded_cause_sound[OF second] cause])

theorem certified_recorded_cause_outer_transfer:
  assumes certified: "certified_recorded_cause_at E gu gr G H root xs B W R"
    and target: "generation_at E' hu hr G"
  shows "certified_recorded_cause_at E' hu hr G H root xs B W R"
proof -
  obtain F pu pr au ar P d t I K where scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and parts: "F=native_judgment_environment F pu pr au ar" "generation_payload G=Whole_Artifact R"
    "native_package_at F pu pr P" "native_application_at F au ar d t I K"
    "environment_included F H" "certified_construction_at H pu pr au ar root xs B W R"
    using certified unfolding certified_recorded_cause_at_def by blast
  have relocated: "generation_judgment_scope_at E' hu hr G F pu pr au ar"
    by (rule generation_judgment_scope_outer_transfer[OF scope target])
  show ?thesis using relocated parts unfolding certified_recorded_cause_at_def by blast
qed

theorem recorded_construction_certification_total:
  assumes valid: "recorded_construction_cause_at E gu gr G xs B W R"
  shows "\<exists>H root. certified_recorded_cause_at E gu gr G H root xs B W R"
proof -
  obtain F pu pr au ar where scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and canonical: "F=native_judgment_environment F pu pr au ar"
    and payload: "generation_payload G=Whole_Artifact R"
    and judged: "construction_judgment_at F pu pr au ar xs B W R"
    using valid unfolding recorded_construction_cause_at_def by blast
  have positive: "native_positive_holds F pu pr au ar"
    by (rule construction_judgment_truth[OF judged])
  obtain H P d t I K root where replay: "native_replay_at H pu pr au ar root {}"
    and source: "native_package_at F pu pr P" "native_application_at F au ar d t I K"
    and retained: "native_package_at H pu pr P" "native_application_at H au ar d t I K"
    and kept: "environment_included (native_judgment_environment F pu pr au ar) H"
    using native_positive_replay_total[OF positive] by blast
  have included: "environment_included F H" using kept by (simp only: canonical[symmetric])
  have claim: "construction_claim_presents xs B W R t" "factor_constructs P d xs B W R"
    using construction_judgment_with_reads[OF source] judged by blast+
  have certified: "certified_construction_at H pu pr au ar root xs B W R"
    using certified_construction_exact_join[OF retained] claim replay by blast
  have whole: "certified_recorded_cause_at E gu gr G H root xs B W R"
    using scope canonical payload source included certified unfolding certified_recorded_cause_at_def by blast
  show ?thesis using whole by blast
qed

text \<open>
  The recorded scope is read as exact data before the proof environment is
  considered. Certification checks the native program and call there, preserves
  that whole minimal environment in the proof context, and checks the separate
  retained construction derivation. Soundness recovers the independently
  defined recorded cause validity.

  Every valid recorded construction has such a certification. The strengthened
  generic replay theorem preserves the exact program-and-call environment, not
  merely its decoded argument and truth. Proof contexts and roots can differ
  while the generation and complete account remain fixed. No evidence field is
  added to the core or its recorded cause scope. Native checking of unordered
  permission admission remains a separate obligation.
\<close>

end
