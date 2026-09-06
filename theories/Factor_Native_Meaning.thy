theory Factor_Native_Meaning
  imports Factor_Applications Factor_Package_Locality Factor_Positive_Locality
begin

section \<open>Native application truth uses the independently fixed meaning\<close>

definition native_positive_holds ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> bool" where
  "native_positive_holds E pu pr au ar \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
      (d,t) \<in> positive_meaning P)"

theorem native_positive_holds_with_reads:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_positive_holds E pu pr au ar \<longleftrightarrow> (d,t) \<in> positive_meaning P"
proof
  assume holds: "native_positive_holds E pu pr au ar"
  obtain T e x J W where other: "native_package_at E pu pr T" "native_application_at E au ar e x J W"
    "(e,x) \<in> positive_meaning T" using holds by (auto simp: native_positive_holds_def)
  have programs: "T = P" by (rule native_package_unique[OF other(1) package])
  have calls: "e = d \<and> x = t" using native_application_unique[OF other(2) app] by blast
  show "(d,t) \<in> positive_meaning P" using other(3) programs calls by simp
next
  assume holds: "(d,t) \<in> positive_meaning P"
  show "native_positive_holds E pu pr au ar" using package app holds unfolding native_positive_holds_def by blast
qed

theorem native_positive_holds_formed:
  assumes "native_positive_holds E pu pr au ar"
  shows "native_application_formed E pu pr au ar"
proof -
  obtain P d t I K where parts: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    "(d,t) \<in> positive_meaning P" using assms by (auto simp: native_positive_holds_def)
  have call: "schema_call_formed P d t" by (rule positive_meaning_formed[OF parts(3)])
  show ?thesis using parts(1,2) call unfolding native_application_formed_def by blast
qed

theorem native_positive_holds_closed_program:
  assumes "native_positive_holds E pu pr au ar"
  shows "\<exists>P d t I K.
    closed_native_package_at (native_package_environment E pu pr) pu pr P \<and>
    native_application_at E au ar d t I K \<and> (d,t) \<in> positive_meaning P"
proof -
  obtain P d t I K where parts: "native_package_at E pu pr P" "native_application_at E au ar d t I K"
    "(d,t) \<in> positive_meaning P" using assms by (auto simp: native_positive_holds_def)
  have closed: "closed_native_package_at (native_package_environment E pu pr) pu pr P"
    by (rule native_package_closed_restriction[OF parts(1)])
  show ?thesis using closed parts(2,3) by blast
qed

theorem native_positive_holds_dependency_locality:
  assumes package: "native_package_at E pu pr P" and ff: "environment_formed F"
    and included: "environment_included (native_package_environment E pu pr) F"
    and source: "native_application_at E au ar d t I K"
    and target: "native_application_at F bu br d t J W"
  shows "native_positive_holds E pu pr au ar \<longleftrightarrow> native_positive_holds F pu pr bu br"
proof -
  have copied: "native_package_at F pu pr P" by (rule native_package_dependency_locality[OF package ff included])
  show ?thesis by (simp only: native_positive_holds_with_reads[OF package source]
      native_positive_holds_with_reads[OF copied target])
qed

text \<open>
  Truth is defined after native definition and application recovery. It has no
  proof, evidence, retention, or implementation premise. The package's own
  dependency restriction is closed and determines the same program. Argument
  syntax stays in its supplied environment, so closing the program does not
  discard or bound future argument material.
\<close>

end

