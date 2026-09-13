theory Factor_Finite_Requirement_Goals
  imports Factor_Executable_Systems Factor_Finite_Checked_Requirements Factor_Admission_Goal_Sequences
begin

definition finite_admission_requirements_supported where
  "finite_admission_requirements_supported gs P=list_all
    (\<lambda>g. finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P) gs"

lemma finite_admission_requirements_supported_correct:
  "finite_admission_requirements_supported gs P \<longleftrightarrow>
    (\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P))"
  by (simp only: finite_admission_requirements_supported_def list_all_iff less_eq_fset.rep_eq
    finite_admission_goal_sites_correct finite_system_definitions_correct)

end
