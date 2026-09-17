theory Factor_Finite_Native_Observations
  imports Factor_Executable_Packages Factor_Executable_Environment_Values_Base
begin

section \<open>Recover complete source and target programs from the returned environment\<close>

definition finite_native_package_observation where
  "finite_native_package_observation F pu pr N M u=(let original=finite_native_package_readings F pu pr in
    (finite_environment_formed F,N |\<in>| original,M |\<in>| original,
      u,finite_native_package_readings F u [],fcard (finite_environment_artifacts F),fcard (finite_environment_bindings F),
      (finite_environment_artifact_rows F,sorted_list_of_fset (finite_environment_bindings F))))"

lemma finite_native_package_observation_conditions:
  "fst (finite_native_package_observation F pu pr N M u)\<longleftrightarrow>environment_formed (decode_finite_environment F)"
  "fst (snd (finite_native_package_observation F pu pr N M u))\<longleftrightarrow>
    native_package_at (decode_finite_environment F) pu pr (decode_finite_system N)"
  "fst (snd (snd (finite_native_package_observation F pu pr N M u)))\<longleftrightarrow>
    native_package_at (decode_finite_environment F) pu pr (decode_finite_system M)"
  by (simp_all add: finite_native_package_observation_def Let_def finite_environment_formed_correct
    finite_native_package_readings_correct)

end
