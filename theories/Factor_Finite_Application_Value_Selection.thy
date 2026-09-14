theory Factor_Finite_Application_Value_Selection
  imports Factor_Executable_Calls
begin

definition finite_application_value_ready where
  "finite_application_value_ready E u r d t=fBex (finite_application_readings E u r)
    (\<lambda>((e,v),I,K). e=d \<and> v=t)"

theorem finite_application_value_ready_exact:
  "finite_application_value_ready E u r d t \<longleftrightarrow>
    (\<exists>I K. native_application_at (decode_finite_environment E) u r d (decode_finite_term t) I K)"
proof
  assume "finite_application_value_ready E u r d t"
  then obtain I K where member: "((d,t),I,K) |\<in>| finite_application_readings E u r"
    by (auto simp: finite_application_value_ready_def Bex_def split_paired_Ex)
  show "\<exists>I K. native_application_at (decode_finite_environment E) u r d (decode_finite_term t) I K"
    using member by (simp only: finite_application_readings_correct; blast)
next
  assume "\<exists>I K. native_application_at (decode_finite_environment E) u r d (decode_finite_term t) I K"
  then obtain I K where app: "native_application_at (decode_finite_environment E) u r d (decode_finite_term t) I K" by blast
  obtain v J A where member: "((d,v),J,A) |\<in>| finite_application_readings E u r"
    and same: "decode_finite_term v=decode_finite_term t"
    using finite_application_readings_complete[OF app] by blast
  have "v=t" using same by simp
  then show "finite_application_value_ready E u r d t"
    using member by (auto simp: finite_application_value_ready_def)
qed

end
