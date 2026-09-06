theory Factor_Certified_Cause
  imports Factor_Cause Factor_Certified_Construction
begin

section \<open>Proof certification refers to the recorded cause\<close>

definition certified_generation_cause_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    generation_core \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u definition_site \<Rightarrow> exact_artifact list \<Rightarrow>
    (local_address\<times>exact_artifact) set \<Rightarrow> addressed_construction \<Rightarrow>
    exact_artifact \<Rightarrow> bool" where
  "certified_generation_cause_at E gu gr G pu pr root xs B W R \<longleftrightarrow>
    generation_at E gu gr G \<and> generation_payload G=Whole_Artifact R \<and>
    (\<exists>cu cr. generation_cause_location E gu gr cu cr \<and>
      certified_construction_at E pu pr cu cr root xs B W R)"

theorem certified_generation_cause_exact_join:
  assumes gen: "generation_at E gu gr G"
    and site: "generation_cause_location E gu gr cu cr"
    and package: "native_package_at E pu pr P"
    and app: "native_application_at E cu cr d t I K"
  shows "certified_generation_cause_at E gu gr G pu pr root xs B W R \<longleftrightarrow>
    construction_cause_at E gu gr G pu pr xs B W R \<and>
    native_replay_at E pu pr cu cr root {}"
proof -
  have located: "certified_generation_cause_at E gu gr G pu pr root xs B W R \<longleftrightarrow>
    generation_payload G=Whole_Artifact R \<and>
    certified_construction_at E pu pr cu cr root xs B W R"
  proof
    assume certified: "certified_generation_cause_at E gu gr G pu pr root xs B W R"
    obtain vu vr where parts: "generation_payload G=Whole_Artifact R"
      "generation_cause_location E gu gr vu vr"
      "certified_construction_at E pu pr vu vr root xs B W R"
      using certified unfolding certified_generation_cause_at_def by blast
    have same: "vu=cu \<and> vr=cr"
      by (rule generation_cause_location_unique[OF parts(2) site])
    show "generation_payload G=Whole_Artifact R \<and>
      certified_construction_at E pu pr cu cr root xs B W R"
      using parts same by simp
  next
    assume "generation_payload G=Whole_Artifact R \<and>
      certified_construction_at E pu pr cu cr root xs B W R"
    then show "certified_generation_cause_at E gu gr G pu pr root xs B W R"
      using gen site unfolding certified_generation_cause_at_def by blast
  qed
  show ?thesis
    by (simp only: located certified_construction_exact_join[OF package app]
      construction_cause_with_reads[OF gen site package app]; blast)
qed

theorem certified_generation_cause_sound:
  assumes certified: "certified_generation_cause_at E gu gr G pu pr root xs B W R"
  shows "construction_cause_at E gu gr G pu pr xs B W R"
proof -
  obtain cu cr where gen: "generation_at E gu gr G"
    and site: "generation_cause_location E gu gr cu cr"
    and construction: "certified_construction_at E pu pr cu cr root xs B W R"
    using certified unfolding certified_generation_cause_at_def by blast
  obtain P d t I K where package: "native_package_at E pu pr P"
    and app: "native_application_at E cu cr d t I K"
    using construction unfolding certified_construction_at_def by blast
  show ?thesis
    using certified_generation_cause_exact_join[OF gen site package app] certified by blast
qed

theorem certified_generation_cause_account_unique:
  assumes first: "certified_generation_cause_at E gu gr G pu pr root xs B W R"
    and second: "certified_generation_cause_at E gu gr H qu qr other ys C X S"
  shows "G=H \<and> xs=ys \<and> B=C \<and> W=X \<and> R=S"
  by (rule construction_cause_account_unique[
    OF certified_generation_cause_sound[OF first] certified_generation_cause_sound[OF second]])

text \<open>
  Certification adds closed replay of the actual cited construction application.
  It entails the independently defined cause judgment. Changing the proof root
  cannot change the recovered generation or its complete construction account.
  The construction permission's admission condition remains explicit; one
  replayed presentation does not certify that universal condition.
\<close>

end
