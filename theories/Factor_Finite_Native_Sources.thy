theory Factor_Finite_Native_Sources
  imports Factor_Executable_Packages Finite_Singleton_Selection
begin

section \<open>The complete native source is returned with an exact admission boundary\<close>

definition finite_native_source :: "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u finite_native_system option" where
  "finite_native_source E u r=finite_singleton_option (finite_native_package_readings E u r)"

lemma finite_native_source_member:
  "finite_native_source E u r=Some P \<longleftrightarrow> P |\<in>| finite_native_package_readings E u r"
proof -
  have singleton: "finite_native_package_readings E u r={|P|} \<longleftrightarrow>
    P |\<in>| finite_native_package_readings E u r"
    using finite_native_package_readings_unique[of P E u r]
    by (auto intro!: fset_inject[THEN iffD1] set_eqI)
  show ?thesis by (simp only: finite_native_source_def finite_singleton_option_some singleton)
qed

theorem finite_native_source_correct:
  "finite_native_source E u r=Some P \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P)"
  by (simp only: finite_native_source_member finite_native_package_readings_correct)

theorem finite_native_source_absent:
  "finite_native_source E u r=None \<longleftrightarrow>
    \<not>(\<exists>N. native_package_at (decode_finite_environment E) u r N)"
proof -
  have exists: "(\<exists>P. finite_native_source E u r=Some P) \<longleftrightarrow>
    (\<exists>N. native_package_at (decode_finite_environment E) u r N)"
    using finite_native_package_readings_complete[of E u r]
    by (auto simp: finite_native_source_member finite_native_package_readings_correct)
  show ?thesis using exists by (cases "finite_native_source E u r") auto
qed

export_code finite_native_source checking SML

text \<open>
  Uniqueness and complete finite reading supply the existing singleton
  selector. No program model, satisfaction table or coordinate function is
  supplied to this operation. A returned value is the complete actual source;
  None means that no native package is readable at these exact inputs.
\<close>

end
