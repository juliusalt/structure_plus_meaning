theory Factor_Executable_Judgment_Retention
  imports Factor_Executable_Application_Retention Factor_Judgment_Retention
begin

definition finite_native_judgment_sources where
  "finite_native_judgment_sources E pu pr au=finite_native_package_sources E pu pr |\<union>| {|au|}"

lemma finite_native_judgment_sources_correct:
  "fset (finite_native_judgment_sources E pu pr au)=
    native_judgment_sources (decode_finite_environment E) pu pr au"
  by (simp add: finite_native_judgment_sources_def native_judgment_sources_def
    finite_native_package_sources_correct)

definition finite_native_judgment_demands where
  "finite_native_judgment_demands E pu pr au ar=
    finite_native_package_demands E pu pr |\<union>| finite_native_application_demands E au ar"

lemma finite_native_judgment_demands_correct:
  "fset (finite_native_judgment_demands E pu pr au ar)=
    native_judgment_demands (decode_finite_environment E) pu pr au ar"
  by (simp add: finite_native_judgment_demands_def native_judgment_demands_def
    finite_native_package_demands_correct finite_native_application_demands_correct)

definition finite_native_judgment_environment where
  "finite_native_judgment_environment E pu pr au ar=finite_read_environment E
    (finite_native_judgment_sources E pu pr au) (finite_native_judgment_demands E pu pr au ar)"

theorem finite_native_judgment_environment_correct:
  "decode_finite_environment (finite_native_judgment_environment E pu pr au ar)=
    native_judgment_environment (decode_finite_environment E) pu pr au ar"
  by (simp add: finite_native_judgment_environment_def native_judgment_environment_def
    finite_read_environment_correct finite_native_judgment_sources_correct finite_native_judgment_demands_correct)

theorem finite_native_judgment_environment_recovers:
  assumes package: "P |\<in>| finite_native_package_readings E pu pr"
    and app: "((d,t),I,K) |\<in>| finite_application_readings E au ar"
  shows "P |\<in>| finite_native_package_readings (finite_native_judgment_environment E pu pr au ar) pu pr"
    "((d,t),I,K) |\<in>| finite_application_readings (finite_native_judgment_environment E pu pr au ar) au ar"
    "finite_environment_formed (finite_native_judgment_environment E pu pr au ar)"
proof -
  have original: "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    and application: "native_application_at (decode_finite_environment E) au ar d
      (decode_finite_term t) (fset I) (fset K)"
    using package app by (simp_all only: finite_native_package_readings_correct finite_application_readings_correct)
  show "P |\<in>| finite_native_package_readings (finite_native_judgment_environment E pu pr au ar) pu pr"
    "((d,t),I,K) |\<in>| finite_application_readings (finite_native_judgment_environment E pu pr au ar) au ar"
    "finite_environment_formed (finite_native_judgment_environment E pu pr au ar)"
    using native_judgment_environment_recovers[OF original application]
    by (simp_all only: finite_native_package_readings_correct finite_application_readings_correct
      finite_environment_formed_correct finite_native_judgment_environment_correct)
qed

theorem finite_native_judgment_environment_idempotent:
  assumes package: "P |\<in>| finite_native_package_readings E pu pr"
    and app: "((d,t),I,K) |\<in>| finite_application_readings E au ar"
  shows "finite_native_judgment_environment (finite_native_judgment_environment E pu pr au ar) pu pr au ar=
    finite_native_judgment_environment E pu pr au ar"
  using native_judgment_environment_idempotent[OF package[unfolded finite_native_package_readings_correct]
    app[unfolded finite_application_readings_correct]]
  by (simp only: decode_finite_environment_injective[symmetric] finite_native_judgment_environment_correct)

definition finite_native_judgment_ready where
  "finite_native_judgment_ready E pu pr au ar=(finite_native_package_readings E pu pr\<noteq>{||} \<and>
    finite_application_readings E au ar\<noteq>{||})"

theorem finite_native_judgment_ready_correct:
  "finite_native_judgment_ready E pu pr au ar \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at (decode_finite_environment E) pu pr P \<and>
      native_application_at (decode_finite_environment E) au ar d t I K)"
proof
  assume ready: "finite_native_judgment_ready E pu pr au ar"
  obtain P d t I K where package: "P |\<in>| finite_native_package_readings E pu pr"
    and app: "((d,t),I,K) |\<in>| finite_application_readings E au ar"
    using ready by (auto simp: finite_native_judgment_ready_def)
  show "\<exists>P d t I K. native_package_at (decode_finite_environment E) pu pr P \<and>
    native_application_at (decode_finite_environment E) au ar d t I K"
    using package app by (simp only: finite_native_package_readings_correct finite_application_readings_correct; blast)
next
  assume "\<exists>P d t I K. native_package_at (decode_finite_environment E) pu pr P \<and>
    native_application_at (decode_finite_environment E) au ar d t I K"
  then obtain P d t I K where package: "native_package_at (decode_finite_environment E) pu pr P"
    and app: "native_application_at (decode_finite_environment E) au ar d t I K" by blast
  have source: "finite_native_package_readings E pu pr\<noteq>{||}"
    using finite_native_package_readings_complete[OF package] by auto
  have call: "finite_application_readings E au ar\<noteq>{||}"
    using finite_application_readings_complete[OF app] by auto
  show "finite_native_judgment_ready E pu pr au ar"
    using source call by (simp only: finite_native_judgment_ready_def; blast)
qed

text \<open>
  The two actual readers determine the complete judgment boundary. Its finite
  implementation is exactly the original least environment, preserving the
  program and call while remaining independent of graph replay or truth.
  Replay retention reuses these same two source and demand components.
\<close>

end
