theory Factor_Base_Cause
  imports Factor_Generation_Scopes RRA_Generation_Construction
begin

section \<open>A base declaration applies an explicit definition to the exact payload\<close>

definition base_admission_judgment_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u \<Rightarrow> local_address \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "base_admission_judgment_at E pu pr au ar R \<longleftrightarrow>
    (\<exists>P d I K. native_package_at E pu pr P \<and>
      native_application_at E au ar d (Target_Term (Whole_Artifact R)) I K \<and>
      (d,Target_Term (Whole_Artifact R)) \<in> positive_meaning P)"

lemma base_admission_with_reads:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "base_admission_judgment_at E pu pr au ar R \<longleftrightarrow>
    t=Target_Term (Whole_Artifact R) \<and> (d,t)\<in>positive_meaning P"
proof
  assume admitted: "base_admission_judgment_at E pu pr au ar R"
  obtain Q e J L where other: "native_package_at E pu pr Q"
    "native_application_at E au ar e (Target_Term (Whole_Artifact R)) J L"
    "(e,Target_Term (Whole_Artifact R)) \<in> positive_meaning Q"
    using admitted unfolding base_admission_judgment_at_def by blast
  have same_program: "Q=P" by (rule native_package_unique[OF other(1) package])
  have same_call: "e=d \<and> Target_Term (Whole_Artifact R)=t"
    using native_application_unique[OF other(2) app] by blast
  show "t=Target_Term (Whole_Artifact R) \<and> (d,t)\<in>positive_meaning P"
    using other(3) same_program same_call by simp
next
  assume "t=Target_Term (Whole_Artifact R) \<and> (d,t)\<in>positive_meaning P"
  then show "base_admission_judgment_at E pu pr au ar R"
    using package app unfolding base_admission_judgment_at_def by blast
qed

lemma base_admission_truth:
  assumes "base_admission_judgment_at E pu pr au ar R"
  shows "native_positive_holds E pu pr au ar"
  using assms unfolding base_admission_judgment_at_def native_positive_holds_def by blast

lemma base_admission_formed:
  assumes "base_admission_judgment_at E pu pr au ar R"
  shows "exact_formed R"
proof -
  obtain d I K where app: "native_application_at E au ar d (Target_Term (Whole_Artifact R)) I K"
    using assms unfolding base_admission_judgment_at_def by blast
  show ?thesis using native_application_properties[OF app] by simp
qed

lemma base_admission_payload_unique:
  assumes first: "base_admission_judgment_at E pu pr au ar R"
    and second: "base_admission_judgment_at E qu qr au ar S"
  shows "R=S"
proof -
  obtain d I K where left: "native_application_at E au ar d (Target_Term (Whole_Artifact R)) I K"
    using first unfolding base_admission_judgment_at_def by blast
  obtain e J L where right: "native_application_at E au ar e (Target_Term (Whole_Artifact S)) J L"
    using second unfolding base_admission_judgment_at_def by blast
  show ?thesis using native_application_unique[OF left right] by simp
qed

theorem base_admission_presentation_invariance:
  assumes first: "native_package_at E pu pr P"
      "native_application_at E au ar d (Target_Term (Whole_Artifact R)) I K"
    and second: "native_package_at F qu qr P"
      "native_application_at F bu br d (Target_Term (Whole_Artifact R)) J L"
  shows "native_application_formed E pu pr au ar \<longleftrightarrow> native_application_formed F qu qr bu br"
    and "base_admission_judgment_at E pu pr au ar R \<longleftrightarrow>
      base_admission_judgment_at F qu qr bu br R"
  by (simp_all only: native_application_formed_with_reads[OF first]
      native_application_formed_with_reads[OF second]
      base_admission_with_reads[OF first] base_admission_with_reads[OF second])

theorem base_admission_recordable:
  fixes E :: "local_address option artifact_environment"
  assumes admitted: "base_admission_judgment_at E pu pr au ar R"
  shows "\<exists>F C. judgment_value_quoted_at C [] F pu pr au ar \<and>
    F=native_judgment_environment F pu pr au ar \<and> base_admission_judgment_at F pu pr au ar R \<and>
    native_package_environment F pu pr=native_package_environment E pu pr"
proof -
  obtain P d I K where package: "native_package_at E pu pr P"
    and app: "native_application_at E au ar d (Target_Term (Whole_Artifact R)) I K"
    and truth: "(d,Target_Term (Whole_Artifact R))\<in>positive_meaning P"
    using admitted unfolding base_admission_judgment_at_def by blast
  obtain F C where quote: "judgment_value_quoted_at C [] F pu pr au ar"
    and canonical: "F=native_judgment_environment F pu pr au ar"
    and kept: "native_package_at F pu pr P"
      "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    and program: "native_package_environment F pu pr=native_package_environment E pu pr"
    using native_judgment_recordable[OF package app] by blast
  have valid: "base_admission_judgment_at F pu pr au ar R"
    using kept truth unfolding base_admission_judgment_at_def by blast
  show ?thesis using quote canonical valid program by blast
qed

section \<open>The complete declaration is recorded in the generation cause\<close>

definition recorded_base_cause_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    exact_artifact \<Rightarrow> bool" where
  "recorded_base_cause_at E gu gr G R \<longleftrightarrow>
    (\<exists>F pu pr au ar. generation_judgment_scope_at E gu gr G F pu pr au ar \<and>
      F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
      base_admission_judgment_at F pu pr au ar R)"

theorem recorded_base_cause_with_scope:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
  shows "recorded_base_cause_at E gu gr G R \<longleftrightarrow>
    F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
    base_admission_judgment_at F pu pr au ar R"
proof
  assume valid: "recorded_base_cause_at E gu gr G R"
  obtain F' qu qr bu br where other: "generation_judgment_scope_at E gu gr G F' qu qr bu br"
    "F'=native_judgment_environment F' qu qr bu br" "generation_payload G=Whole_Artifact R"
    "base_admission_judgment_at F' qu qr bu br R"
    using valid unfolding recorded_base_cause_at_def by blast
  have same: "F'=F \<and> qu=pu \<and> qr=pr \<and> bu=au \<and> br=ar"
    by (rule generation_judgment_scope_unique[OF other(1) scope refl])
  show "F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
    base_admission_judgment_at F pu pr au ar R" using other(2-4) same by simp
next
  assume "F=native_judgment_environment F pu pr au ar \<and> generation_payload G=Whole_Artifact R \<and>
    base_admission_judgment_at F pu pr au ar R"
  then show "recorded_base_cause_at E gu gr G R" using scope unfolding recorded_base_cause_at_def by blast
qed

theorem recorded_base_payload_unique:
  assumes first: "recorded_base_cause_at E gu gr G R"
    and second: "recorded_base_cause_at E' hu hr G' S"
    and cause: "generation_cause G=generation_cause G'"
  shows "R=S"
proof -
  obtain F pu pr au ar where left: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    "base_admission_judgment_at F pu pr au ar R"
    using first unfolding recorded_base_cause_at_def by blast
  obtain F' qu qr bu br where right: "generation_judgment_scope_at E' hu hr G' F' qu qr bu br"
    "base_admission_judgment_at F' qu qr bu br S"
    using second unfolding recorded_base_cause_at_def by blast
  have same: "F=F' \<and> pu=qu \<and> pr=qr \<and> au=bu \<and> ar=br"
    by (rule generation_judgment_scope_unique[OF left(1) right(1) cause])
  have other: "base_admission_judgment_at F pu pr au ar S" using right(2) same by simp
  show ?thesis by (rule base_admission_payload_unique[OF left(2) other])
qed

theorem recorded_base_outer_transfer:
  assumes valid: "recorded_base_cause_at E gu gr G R" and target: "generation_at E' hu hr G"
  shows "recorded_base_cause_at E' hu hr G R"
proof -
  obtain F pu pr au ar where scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and parts: "F=native_judgment_environment F pu pr au ar" "generation_payload G=Whole_Artifact R"
      "base_admission_judgment_at F pu pr au ar R"
    using valid unfolding recorded_base_cause_at_def by blast
  have moved: "generation_judgment_scope_at E' hu hr G F pu pr au ar"
    by (rule generation_judgment_scope_outer_transfer[OF scope target])
  show ?thesis using moved parts unfolding recorded_base_cause_at_def by blast
qed

theorem recorded_base_scope_closed:
  assumes scope: "generation_judgment_scope_at E gu gr G F pu pr au ar"
    and valid: "recorded_base_cause_at E gu gr G R"
  shows "environment_closed F {pu,au} (native_judgment_demands F pu pr au ar)"
proof -
  have canonical: "F=native_judgment_environment F pu pr au ar"
    and admitted: "base_admission_judgment_at F pu pr au ar R"
    using recorded_base_cause_with_scope[OF scope] valid by blast+
  obtain P d I K where package: "native_package_at F pu pr P"
    and app: "native_application_at F au ar d (Target_Term (Whole_Artifact R)) I K"
    using admitted unfolding base_admission_judgment_at_def by blast
  show ?thesis using native_judgment_environment_closed[OF package app]
    by (simp only: canonical[symmetric])
qed

theorem base_admission_generation_total:
  fixes E :: "local_address option artifact_environment"
  assumes admitted: "base_admission_judgment_at E pu pr au ar R"
    and locus: "target_formed l" and predecessors: "\<forall>G\<in>fset P. generation_formed G"
  shows "\<exists>F C. \<exists>A :: local_address option artifact_environment. \<exists>u.
    judgment_value_quoted_at C [] F pu pr au ar \<and>
    F=native_judgment_environment F pu pr au ar \<and>
    native_package_environment F pu pr=native_package_environment E pu pr \<and>
    generation_at A u [] (Generation l P (Whole_Artifact R) (Occurrence_Anchor (C,[]))) \<and>
    generation_environment_closed A {(u,[])} \<and>
    recorded_base_cause_at A u [] (Generation l P (Whole_Artifact R) (Occurrence_Anchor (C,[]))) R"
proof -
  obtain F C where quote: "judgment_value_quoted_at C [] F pu pr au ar"
    and canonical: "F=native_judgment_environment F pu pr au ar"
    and kept: "base_admission_judgment_at F pu pr au ar R"
    and program: "native_package_environment F pu pr=native_package_environment E pu pr"
    using base_admission_recordable[OF admitted] by blast
  have rf: "exact_formed R" by (rule base_admission_formed[OF admitted])
  have anchor: "anchor_formed (C,[])" by (rule judgment_value_quoted_anchor[OF quote])
  let ?G = "Generation l P (Whole_Artifact R) (Occurrence_Anchor (C,[]))"
  have formed: "generation_formed ?G"
    by (rule generation_formed.formed[OF locus _ _ predecessors]) (use rf anchor in simp_all)
  obtain A :: "local_address option artifact_environment" and u where gen: "generation_at A u [] ?G"
    and closed: "generation_environment_closed A {(u,[])}"
    using closed_generation_presentation_total[OF formed] by blast
  have cause: "generation_cause ?G=Occurrence_Anchor (C,[])" by simp
  have scope: "generation_judgment_scope_at A u [] ?G F pu pr au ar"
    by (rule generation_judgment_scope_from_core[OF gen cause quote])
  have valid: "recorded_base_cause_at A u [] ?G R"
    using recorded_base_cause_with_scope[OF scope] canonical kept by simp
  show ?thesis by (rule exI[of _ F], rule exI[of _ C], rule exI[of _ A], rule exI[of _ u])
    (use quote canonical program gen closed valid in blast)
qed

text \<open>
  Base admission is an application of a supplied native definition to a
  whole-artifact literal. Its force comes from the independent positive
  meaning of that definition. The literal presents the exact payload directly;
  all native quotations of that literal give the same formation and truth.
  There is no selected serialization of an unordered artifact in this argument.

  A recorded declaration contains its complete minimal program-and-call scope
  as exact data. Equal causes determine the same payload across outer
  environments. Each admitted declaration has an actual closed generation.
  Historical predecessors remain explicit and separate; the empty family
  supplies an initial generation without imposing a rule on continuation.
\<close>

end
