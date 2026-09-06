theory Factor_Base_Programs
  imports Factor_Certified_Base_Cause Factor_Compiled_Applications Factor_Pattern_Programs
begin

section \<open>An ordinary native program can admit exactly one selected artifact\<close>

theorem exact_base_admission_program:
  assumes formed: "exact_formed R"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and>
    (\<forall>S. exact_formed S \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and>
      native_application_at F au [] d (Target_Term (Whole_Artifact S)) I K \<and>
      native_application_formed F pu [] au [] \<and>
      (base_admission_judgment_at F pu [] au [] S \<longleftrightarrow> S=R) \<and>
      native_package_environment F pu []=E \<and>
      (\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
proof -
  let ?t = "Target_Term (Whole_Artifact R)"
  let ?p = "exact_term_pattern ?t :: unit term_pattern"
  let ?P = "recognizer_system () ?p"
  have pf: "pattern_formed ?p" using formed by simp
  have sf: "schema_system_formed ?P" by (rule recognizer_system_formed[OF pf])
  have member: "()\<in>system_definitions ?P"
    by (auto simp: recognizer_system_def system_definitions_def rel_dom_def)
  obtain g :: "unit \<Rightarrow> local_address option definition_site"
    and E :: "local_address option artifact_environment" and pu Q
    where closed: "closed_native_package_at E pu [] Q"
    and future: "\<forall>d\<in>system_definitions ?P. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and>
        (native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed ?P d t) \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> (d,t)\<in>positive_meaning ?P) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using compiled_program_future_applications[OF sf] by blast
  have every: "\<forall>S. exact_formed S \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and>
      native_application_at F au [] (g ()) (Target_Term (Whole_Artifact S)) I K \<and>
      native_application_formed F pu [] au [] \<and>
      (base_admission_judgment_at F pu [] au [] S \<longleftrightarrow> S=R) \<and>
      native_package_environment F pu []=E \<and>
      (\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
  proof (intro allI impI)
    fix S assume sformed: "exact_formed S"
    let ?arg = "Target_Term (Whole_Artifact S)"
    have tf: "term_formed ?arg" using sformed by simp
    obtain F au I K where ff: "environment_formed F" and included: "environment_included E F"
      and fresh: "au\<notin>environment_uses E"
      and package: "native_package_at F pu [] Q" and app: "native_application_at F au [] (g ()) ?arg I K"
      and canonical: "native_package_environment F pu []=E"
      and boundary: "native_application_formed F pu [] au [] \<longleftrightarrow> schema_call_formed ?P () ?arg"
      and truth: "native_positive_holds F pu [] au [] \<longleftrightarrow> ((),?arg)\<in>positive_meaning ?P"
      and artifacts: "\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T"
      and bindings: "\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w"
      using future[rule_format, OF member tf] by blast
    have call: "native_application_formed F pu [] au []"
      using boundary recognizer_call_formed[OF pf, of "()" ?arg] tf by blast
    have recognized: "((),?arg)\<in>positive_meaning ?P \<longleftrightarrow> S=R"
      using recognizer_positive_meaning[OF pf, of ?arg "()"]
      by (simp only: exact_term_pattern_accepts term_formed.simps target_formed.simps
          factor_term.inject exact_target.inject formed simp_thms)
    have accepted: "base_admission_judgment_at F pu [] au [] S \<longleftrightarrow> S=R"
      using base_admission_with_reads[OF package app] native_positive_holds_with_reads[OF package app]
        truth recognized by simp
    show "\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] (g ()) ?arg I K \<and>
      native_application_formed F pu [] au [] \<and>
      (base_admission_judgment_at F pu [] au [] S \<longleftrightarrow> S=R) \<and>
      native_package_environment F pu []=E \<and>
      (\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)"
      by (rule exI[of _ F], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
         (use ff included fresh package app call accepted canonical artifacts bindings in blast)
  qed
  show ?thesis by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g ()"])
    (use closed every in blast)
qed

corollary every_formed_payload_has_a_certified_base_generation:
  assumes formed: "exact_formed R" and locus: "target_formed l"
  shows "\<exists>C. \<exists>E :: local_address option artifact_environment. \<exists>u H root.
    generation_at E u [] (Generation l {||} (Whole_Artifact R) (Occurrence_Anchor (C,[]))) \<and>
    generation_environment_closed E {(u,[])} \<and>
    recorded_base_cause_at E u [] (Generation l {||} (Whole_Artifact R) (Occurrence_Anchor (C,[]))) R \<and>
    certified_base_cause_at E u [] (Generation l {||} (Whole_Artifact R) (Occurrence_Anchor (C,[]))) H root R"
proof -
  obtain E :: "local_address option artifact_environment" and pu Q d
    where package: "closed_native_package_at E pu [] Q" and future:
    "\<forall>S. exact_formed S \<longrightarrow> (\<exists>F au I K.
      environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
      native_package_at F pu [] Q \<and> native_application_at F au [] d (Target_Term (Whole_Artifact S)) I K \<and>
      native_application_formed F pu [] au [] \<and>
      (base_admission_judgment_at F pu [] au [] S \<longleftrightarrow> S=R) \<and>
      native_package_environment F pu []=E \<and>
      (\<forall>v\<in>environment_uses E. \<forall>T. artifact_at F v T \<longleftrightarrow> artifact_at E v T) \<and>
      (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w))"
    using exact_base_admission_program[OF formed] by blast
  obtain F :: "local_address option artifact_environment" and au
    where admitted: "base_admission_judgment_at F pu [] au [] R"
    using future[rule_format, OF formed] by blast
  have empty: "\<forall>G\<in>fset {||}. generation_formed G" by simp
  obtain C and A :: "local_address option artifact_environment" and u
    where gen: "generation_at A u [] (Generation l {||} (Whole_Artifact R) (Occurrence_Anchor (C,[])))"
    and closed: "generation_environment_closed A {(u,[])}"
    and valid: "recorded_base_cause_at A u [] (Generation l {||} (Whole_Artifact R) (Occurrence_Anchor (C,[]))) R"
    using base_admission_generation_total[OF admitted locus empty] by blast
  obtain H root where certified:
    "certified_base_cause_at A u [] (Generation l {||} (Whole_Artifact R) (Occurrence_Anchor (C,[]))) H root R"
    using recorded_base_certification_total[OF valid] by blast
  show ?thesis using gen closed valid certified by blast
qed

text \<open>
  For each formed selected artifact, one ordinary finite program admits exactly
  that artifact. The same closed native program receives every future formed
  payload. All such applications are formed, while admission distinguishes exact
  values, and every old artifact and binding remains unchanged.

  Choosing this explicit program supplies a certified initial base generation
  for any formed payload at any stated formed locus. This is an existence result
  for a supplied policy. It does not choose which policy an authority adopts.
\<close>

end
