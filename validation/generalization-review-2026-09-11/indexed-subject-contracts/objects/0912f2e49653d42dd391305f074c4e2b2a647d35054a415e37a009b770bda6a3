theory Factor_Specialization_Report_Programs
  imports Factor_Specialization_Reports Factor_Compiled_Applications
begin

section \<open>The report operation has one fixed native program\<close>

theorem fixed_native_specialization_report:
  "\<exists>E :: local_address option artifact_environment. \<exists>pu Q g.
    closed_native_package_at E pu [] Q \<and> native_package_environment E pu []=E \<and> inj_on g {342::nat} \<and>
    (\<forall>d\<in>{342::nat}. \<forall>t. term_formed t \<longrightarrow>
      (\<exists>F au I K. environment_formed F \<and> environment_included E F \<and> au\<notin>environment_uses E \<and>
        native_package_at F pu [] Q \<and> native_application_at F au [] (g d) t I K \<and>
        native_package_environment F pu []=E \<and> native_application_formed F pu [] au [] \<and>
        (native_positive_holds F pu [] au [] \<longleftrightarrow> specialization_report_result t) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>R. artifact_at F v R \<longleftrightarrow> artifact_at E v R) \<and>
        (\<forall>v\<in>environment_uses E. \<forall>k w. binds_slot F v k w \<longleftrightarrow> binds_slot E v k w)))"
  by (rule compiled_exact_operations[OF specialization_report_formed])
    (auto simp: specialization_report_call specialization_report_exact)

text \<open>
  This instantiates the existing general compilation contract. Its package and
  public site precede every later submitted report. The exact subject remains
  the specialization together with the complete report at its actual target.
  Compilation preserves the retained program scope, artifacts, and bindings.
\<close>

end
