theory Factor_Certified_Base_Cause
  imports Factor_Base_Cause Factor_Replay
begin

section \<open>A base declaration has a separate retained derivation\<close>

definition certified_base_cause_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option definition_site \<Rightarrow>
    exact_artifact \<Rightarrow> bool" where
  "certified_base_cause_at E gu gr G H root R \<longleftrightarrow>
    (\<exists>F pu pr au ar P d I K. generation_judgment_scope_at E gu gr G F pu pr au ar \<and>
      F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
      native_package_at F pu pr P \<and>
      native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K \<and>
      environment_included F H \<and> native_replay_at H pu pr au ar root {})"

lemma certified_base_cause_with_reads:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    and included: "environment_included F H"
  shows "certified_base_cause_at E gu gr G H root R \<longleftrightarrow>
    F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
    native_replay_at H pu pr au ar root {}"
proof
  assume certified: "certified_base_cause_at E gu gr G H root R"
  obtain F' qu qr bu br where other: "generation_judgment_scope_at E gu gr G F' qu qr bu br"
    "F'=native_judgment_environment F' qu qr bu br" "generation_payload G=Whole_Artifact R"
    "native_replay_at H qu qr bu br root {}"
    using certified unfolding certified_base_cause_at_def by blast
  have same: "F'=F \<and> qu=pu \<and> qr=pr \<and> bu=au \<and> br=ar"
    by (rule generation_judgment_scope_unique[OF other(1) scope refl])
  show "F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
    native_replay_at H pu pr au ar root {}" using other(2-4) same by simp
next
  assume "F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
    native_replay_at H pu pr au ar root {}"
  then show "certified_base_cause_at E gu gr G H root R"
    using scope package app included unfolding certified_base_cause_at_def by blast
qed

theorem certified_base_cause_sound:
  assumes certified: "certified_base_cause_at E gu gr G H root R"
  shows "recorded_base_cause_at E gu gr G R"
proof -
  obtain F pu pr au ar P d I K where scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and canonical: "F=native_judgment_environment F pu pr au ar"
    and payload: "generation_payload G=Whole_Artifact R"
    and package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    and included: "environment_included F H" and replay: "native_replay_at H pu pr au ar root {}"
    using certified unfolding certified_base_cause_at_def by blast
  have hf: "environment_formed H"
    using replay unfolding native_replay_at_def native_application_at_def by blast
  have kept: "native_package_at H pu pr P"
    "native_application_at H au ar d (Target_Term (Whole_Artifact R)) I K"
    by (rule native_package_included[OF package included hf], rule native_application_included[OF app included hf])
  have positive: "native_positive_holds H pu pr au ar" by (rule native_replay_closed_sound[OF replay])
  have truth: "(d,Target_Term (Whole_Artifact R))\<in>positive_meaning P"
    using native_positive_holds_with_reads[OF kept] positive by blast
  have admitted: "base_admission_judgment_at F pu pr au ar R"
    using base_admission_with_reads[OF package app] truth by simp
  show ?thesis using scope canonical payload admitted unfolding recorded_base_cause_at_def by blast
qed

theorem certified_base_cause_exact_join:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    and included: "environment_included F H"
  shows "certified_base_cause_at E gu gr G H root R \<longleftrightarrow>
    recorded_base_cause_at E gu gr G R \<and> native_replay_at H pu pr au ar root {}"
proof
  assume certified: "certified_base_cause_at E gu gr G H root R"
  have valid: "recorded_base_cause_at E gu gr G R" by (rule certified_base_cause_sound[OF certified])
  have replay: "native_replay_at H pu pr au ar root {}"
    using certified_base_cause_with_reads[OF scope package app included] certified by blast
  show "recorded_base_cause_at E gu gr G R \<and> native_replay_at H pu pr au ar root {}"
    using valid replay by blast
next
  assume "recorded_base_cause_at E gu gr G R \<and> native_replay_at H pu pr au ar root {}"
  then show "certified_base_cause_at E gu gr G H root R"
    using recorded_base_cause_with_scope[OF scope]
      certified_base_cause_with_reads[OF scope package app included] by blast
qed

theorem certified_base_payload_unique:
  assumes first: "certified_base_cause_at E gu gr G H root R"
    and second: "certified_base_cause_at E' hu hr G' H' other S"
    and cause: "generation_cause G=generation_cause G'"
  shows "R=S"
  by (rule recorded_base_payload_unique[
    OF certified_base_cause_sound[OF first] certified_base_cause_sound[OF second] cause])

theorem certified_base_outer_transfer:
  assumes certified: "certified_base_cause_at E gu gr G H root R"
    and target: "generation_at E' hu hr G"
  shows "certified_base_cause_at E' hu hr G H root R"
proof -
  obtain F pu pr au ar P d I K where scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and parts: "F=native_judgment_environment F pu pr au ar" "generation_payload G=Whole_Artifact R"
      "native_package_at F pu pr P" "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
      "environment_included F H" "native_replay_at H pu pr au ar root {}"
    using certified unfolding certified_base_cause_at_def by blast
  have moved: "generation_judgment_scope_at E' hu hr G F pu pr au ar"
    by (rule generation_judgment_scope_outer_transfer[OF scope target])
  show ?thesis using moved parts unfolding certified_base_cause_at_def by blast
qed

theorem recorded_base_certification_total:
  assumes valid: "recorded_base_cause_at E gu gr G R"
  shows "\<exists>H root. certified_base_cause_at E gu gr G H root R"
proof -
  obtain F pu pr au ar where scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and canonical: "F=native_judgment_environment F pu pr au ar"
    and payload: "generation_payload G=Whole_Artifact R"
    and admitted: "base_admission_judgment_at F pu pr au ar R"
    using valid unfolding recorded_base_cause_at_def by blast
  obtain P d I K where source: "native_package_at F pu pr P"
    "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    using admitted unfolding base_admission_judgment_at_def by blast
  have positive: "native_positive_holds F pu pr au ar" by (rule base_admission_truth[OF admitted])
  obtain H root where replay: "native_replay_at H pu pr au ar root {}"
    and kept: "environment_included (native_judgment_environment F pu pr au ar) H"
    using native_positive_replay_total[OF positive] by blast
  have included: "environment_included F H" using kept by (simp only: canonical[symmetric])
  have certified: "certified_base_cause_at E gu gr G H root R"
    using scope canonical payload source included replay unfolding certified_base_cause_at_def by blast
  show ?thesis using certified by blast
qed

text \<open>
  Certification checks a retained derivation of the declared literal call while
  preserving the complete recorded scope. It entails the independently defined
  base admission and is available for every valid recorded base cause. Evidence
  changes neither the generation core nor its admitted payload. The raw base
  reader remains independent of this theory.
\<close>

end
