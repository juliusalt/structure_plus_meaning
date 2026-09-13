theory Factor_Finite_Native_Requirements
  imports Factor_Finite_Native_Requirement_Construction Factor_Finite_Requirement_Goals
    Factor_Finite_Source_Construction
begin

lemma native_requirement_source_constructor:
  "finite_native_source_constructor (finite_admission_requirements_supported gs) (finite_construct_native_requirements gs)
    (\<lambda>P t. admission_requirements_hold (positive_meaning (decode_finite_system P)) gs t)"
  by (unfold_locales)
    (use finite_construct_native_requirements_total in
      \<open>simp only: finite_admission_requirements_supported_def list_all_iff admission_requirements_realized_def; blast\<close>)

definition finite_construct_source_requirements where
  "finite_construct_source_requirements E pu pr gs=finite_construct_source
    (finite_admission_requirements_supported gs) (finite_construct_native_requirements gs) E pu pr"

theorem finite_construct_source_requirements_total:
  "(\<exists>d F u. finite_construct_source_requirements E pu pr gs=Some (d,F,u)) \<longleftrightarrow>
    (\<exists>P. finite_native_source E pu pr=Some P \<and>
      (\<forall>g\<in>set gs. finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P))"
  by (simp only: finite_construct_source_requirements_def
    finite_native_source_constructor.total[OF native_requirement_source_constructor]
    finite_admission_requirements_supported_def list_all_iff)

theorem finite_construct_source_requirements_correct:
  assumes result: "finite_construct_source_requirements E pu pr gs=Some (d,F,u)"
  shows "\<exists>P Q e T. native_package_at (decode_finite_environment E) pu pr (decode_finite_system P) \<and>
    (\<forall>g\<in>set gs. admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P)) \<and>
    admission_requirements_realized (decode_finite_system P) gs e (decode_finite_system Q) \<and>
    finite_environment_formed F \<and> environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
    native_package_at (decode_finite_environment F) pu pr (decode_finite_system P) \<and>
    native_package_at (decode_finite_environment F) u [] T \<and> d\<in>system_definitions T \<and>
    (\<forall>t. (d,t)\<in>positive_meaning T \<longleftrightarrow>
      admission_requirements_hold (positive_meaning (decode_finite_system P)) gs t) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
      artifact_at (decode_finite_environment F) w A \<longleftrightarrow> artifact_at (decode_finite_environment E) w A) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
      binds_slot (decode_finite_environment F) w k v \<longleftrightarrow> binds_slot (decode_finite_environment E) w k v)"
  using finite_native_source_constructor.correct[OF native_requirement_source_constructor
    result[unfolded finite_construct_source_requirements_def]]
  by (simp only: finite_admission_requirements_supported_correct admission_requirements_realized_def; blast)

export_code finite_construct_source_requirements checking SML

end
