theory Factor_Executable_Application_Retention
  imports Factor_Executable_Dependencies Factor_Executable_Calls Factor_Application_Retention
begin

definition finite_native_application_demands ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> ('u \<times> local_address) fset" where
  "finite_native_application_demands E u r =
    fimage (Pair u) (finite_reading_slots (finite_application_readings E u r))"

theorem finite_native_application_demands_correct:
  "fset (finite_native_application_demands E u r) = native_application_demands (decode_finite_environment E) u r"
proof -
  have projected: "fset (finite_reading_slots (finite_application_readings E u r)) =
      {k. \<exists>q I K. native_application_at (decode_finite_environment E) u r (fst q) (snd q) I K \<and> k \<in> K}"
  proof (rule finite_reading_slots_correct[where D=decode_finite_call_term])
    show "(q,I,K) |\<in>| finite_application_readings E u r \<longleftrightarrow>
        native_application_at (decode_finite_environment E) u r
          (fst (decode_finite_call_term q)) (snd (decode_finite_call_term q)) (fset I) (fset K)" for q I K
      by (cases q) (simp add: finite_application_readings_correct)
    fix q I K assume read: "native_application_at (decode_finite_environment E) u r (fst q) (snd q) I K"
    show "\<exists>p J A. (p,J,A) |\<in>| finite_application_readings E u r \<and> fset A=K"
      using finite_application_readings_complete[OF read] by blast
  qed
  show ?thesis by (auto simp: finite_native_application_demands_def native_application_demands_def
      fimage.rep_eq projected split: prod.splits; force)
qed

end
