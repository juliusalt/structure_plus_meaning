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

section \<open>The certified cause over a scope reading\<close>

text \<open>
  Nothing the certified cause concludes reads how its scope was quoted: it reads the scope F, its
  sites, the package and the application at F, F's inclusion in the replay environment and the closed
  replay. It is stated once over a scope reading (@{text Factor_Base_Cause}, with the recorded cause it
  certifies), and @{const certified_base_cause_at} is its instance at
  @{const generation_judgment_scope_at}. @{text certified_base_payload_unique} rests on the cause alone
  determining the scope and stays at the whole-value reading.
\<close>

definition scope_certified_base_cause_at ::
  "'u scope_reading \<Rightarrow> 'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option definition_site \<Rightarrow>
    exact_artifact \<Rightarrow> bool" where
  "scope_certified_base_cause_at S E gu gr G H root R \<longleftrightarrow>
    (\<exists>F pu pr au ar P d I K. S E gu gr G F pu pr au ar \<and>
      F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
      native_package_at F pu pr P \<and>
      native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K \<and>
      environment_included F H \<and> native_replay_at H pu pr au ar root {})"


lemma certified_base_cause_scope_instance:
  "certified_base_cause_at E gu gr G H root R =
    scope_certified_base_cause_at generation_judgment_scope_at E gu gr G H root R"
  by (simp only: certified_base_cause_at_def scope_certified_base_cause_at_def)


lemma scope_certified_base_cause_with_reads:
  assumes determined: "scope_reading_determined S E gu gr G"
    and scope: "S E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    and included: "environment_included F H"
  shows "scope_certified_base_cause_at S E gu gr G H root R \<longleftrightarrow>
    F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
    native_replay_at H pu pr au ar root {}"
proof
  assume certified: "scope_certified_base_cause_at S E gu gr G H root R"
  obtain F' qu qr bu br where other: "S E gu gr G F' qu qr bu br"
    "F'=native_judgment_environment F' qu qr bu br" "generation_payload G=Whole_Artifact R"
    "native_replay_at H qu qr bu br root {}"
    using certified unfolding scope_certified_base_cause_at_def by blast
  have same: "F'=F \<and> qu=pu \<and> qr=pr \<and> bu=au \<and> br=ar"
    using determined other(1) scope unfolding scope_reading_determined_def by blast
  show "F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
    native_replay_at H pu pr au ar root {}" using other(2-4) same by simp
next
  assume "F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
    native_replay_at H pu pr au ar root {}"
  then show "scope_certified_base_cause_at S E gu gr G H root R"
    using scope package app included unfolding scope_certified_base_cause_at_def by blast
qed

theorem scope_certified_base_cause_sound:
  assumes certified: "scope_certified_base_cause_at S E gu gr G H root R"
  shows "scope_recorded_base_cause_at S E gu gr G R"
proof -
  obtain F pu pr au ar P d I K where scope: "S E gu gr G F pu pr au ar"
    and canonical: "F=native_judgment_environment F pu pr au ar"
    and payload: "generation_payload G=Whole_Artifact R"
    and package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    and included: "environment_included F H" and replay: "native_replay_at H pu pr au ar root {}"
    using certified unfolding scope_certified_base_cause_at_def by blast
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
  show ?thesis using scope canonical payload admitted unfolding scope_recorded_base_cause_at_def by blast
qed

theorem scope_certified_base_cause_exact_join:
  assumes determined: "scope_reading_determined S E gu gr G"
    and scope: "S E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    and included: "environment_included F H"
  shows "scope_certified_base_cause_at S E gu gr G H root R \<longleftrightarrow>
    scope_recorded_base_cause_at S E gu gr G R \<and> native_replay_at H pu pr au ar root {}"
proof
  assume certified: "scope_certified_base_cause_at S E gu gr G H root R"
  have valid: "scope_recorded_base_cause_at S E gu gr G R"
    by (rule scope_certified_base_cause_sound[OF certified])
  have replay: "native_replay_at H pu pr au ar root {}"
    using scope_certified_base_cause_with_reads[OF determined scope package app included] certified by blast
  show "scope_recorded_base_cause_at S E gu gr G R \<and> native_replay_at H pu pr au ar root {}"
    using valid replay by blast
next
  assume "scope_recorded_base_cause_at S E gu gr G R \<and> native_replay_at H pu pr au ar root {}"
  then show "scope_certified_base_cause_at S E gu gr G H root R"
    using scope_recorded_base_cause_with_scope[OF determined scope]
      scope_certified_base_cause_with_reads[OF determined scope package app included] by blast
qed

theorem scope_certified_base_outer_transfer:
  assumes transfers: "scope_reading_transfers S S'"
    and certified: "scope_certified_base_cause_at S E gu gr G H root R"
    and target: "generation_at E' hu hr G"
  shows "scope_certified_base_cause_at S' E' hu hr G H root R"
proof -
  obtain F pu pr au ar P d I K where scope: "S E gu gr G F pu pr au ar"
    and parts: "F=native_judgment_environment F pu pr au ar" "generation_payload G=Whole_Artifact R"
      "native_package_at F pu pr P" "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
      "environment_included F H" "native_replay_at H pu pr au ar root {}"
    using certified unfolding scope_certified_base_cause_at_def by blast
  have moved: "S' E' hu hr G F pu pr au ar"
    using transfers scope target unfolding scope_reading_transfers_def by blast
  show ?thesis using moved parts unfolding scope_certified_base_cause_at_def by blast
qed

theorem scope_recorded_base_certification_total:
  assumes valid: "scope_recorded_base_cause_at S E gu gr G R"
  shows "\<exists>H root. scope_certified_base_cause_at S E gu gr G H root R"
proof -
  obtain F pu pr au ar where scope: "S E gu gr G F pu pr au ar"
    and canonical: "F=native_judgment_environment F pu pr au ar"
    and payload: "generation_payload G=Whole_Artifact R"
    and admitted: "base_admission_judgment_at F pu pr au ar R"
    using valid unfolding scope_recorded_base_cause_at_def by blast
  obtain P d I K where source: "native_package_at F pu pr P"
    "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    using admitted unfolding base_admission_judgment_at_def by blast
  have positive: "native_positive_holds F pu pr au ar" by (rule base_admission_truth[OF admitted])
  obtain H root where replay: "native_replay_at H pu pr au ar root {}"
    and kept: "environment_included (native_judgment_environment F pu pr au ar) H"
    using native_positive_replay_total[OF positive] by blast
  have included: "environment_included F H" using kept by (simp only: canonical[symmetric])
  have certified: "scope_certified_base_cause_at S E gu gr G H root R"
    using scope canonical payload source included replay unfolding scope_certified_base_cause_at_def by blast
  show ?thesis using certified by blast
qed

section \<open>The whole-value reading's instances\<close>

lemma certified_base_cause_with_reads:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    and included: "environment_included F H"
  shows "certified_base_cause_at E gu gr G H root R \<longleftrightarrow>
    F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
    native_replay_at H pu pr au ar root {}"
  using scope_certified_base_cause_with_reads[OF generation_judgment_scope_determined scope package app included]
  by (simp only: certified_base_cause_scope_instance)

theorem certified_base_cause_sound:
  assumes certified: "certified_base_cause_at E gu gr G H root R"
  shows "recorded_base_cause_at E gu gr G R"
  using scope_certified_base_cause_sound[OF certified[unfolded certified_base_cause_scope_instance]]
  by (simp only: recorded_base_cause_scope_instance)

theorem certified_base_cause_exact_join:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    and included: "environment_included F H"
  shows "certified_base_cause_at E gu gr G H root R \<longleftrightarrow>
    recorded_base_cause_at E gu gr G R \<and> native_replay_at H pu pr au ar root {}"
  using scope_certified_base_cause_exact_join[OF generation_judgment_scope_determined scope package app included]
  by (simp only: certified_base_cause_scope_instance recorded_base_cause_scope_instance)

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
  using scope_certified_base_outer_transfer[OF generation_judgment_scope_transfers
      certified[unfolded certified_base_cause_scope_instance] target]
  by (simp only: certified_base_cause_scope_instance)

theorem recorded_base_certification_total:
  assumes valid: "recorded_base_cause_at E gu gr G R"
  shows "\<exists>H root. certified_base_cause_at E gu gr G H root R"
  using scope_recorded_base_certification_total[OF valid[unfolded recorded_base_cause_scope_instance]]
  by (simp only: certified_base_cause_scope_instance)

text \<open>
  Certification checks a retained derivation of the declared literal call while
  preserving the complete recorded scope. It entails the independently defined
  base admission and is available for every valid recorded base cause. Evidence
  changes neither the generation core nor its admitted payload. The raw base
  reader remains independent of this theory.
\<close>

end
