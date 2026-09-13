theory Factor_Finite_Native_Admission_Construction
  imports Factor_Finite_Native_Admission_Installation Factor_Admission_Goal_Construction
begin

section \<open>Native callbacks instantiate the shared goal constructor\<close>

interpretation finite_native_admission: admission_goal_constructor
    "decode_finite_system :: local_address option finite_native_system \<Rightarrow> local_address option native_system"
    finite_native_admission_leaf finite_native_admission_pair finite_native_admission_list
proof
  fix P :: "local_address option finite_native_system" and d
  assume source: "schema_system_formed (decode_finite_system P)"
    and member: "d\<in>system_definitions (decode_finite_system P)"
  show "finite_native_admission_leaf d P=Some (d,P)"
    using member by (simp add: finite_native_admission_leaf_def finite_system_definitions_correct)
next
  fix P :: "local_address option finite_native_system" and a b
  assume source: "schema_system_formed (decode_finite_system P)"
    and first: "a\<in>system_definitions (decode_finite_system P)"
    and second: "b\<in>system_definitions (decode_finite_system P)"
  interpret step: finite_native_pair_installation P a b
    by (unfold_locales) (use source first second in
      \<open>simp_all only: finite_system_formed_correct finite_system_definitions_correct\<close>)
  show "\<exists>d Q. finite_native_admission_pair a b P=Some (d,Q) \<and>
      admission_extension (decode_finite_system P) (decode_finite_system Q) \<and>
      d\<in>system_definitions (decode_finite_system Q) \<and>
      (\<forall>x. (d,x)\<in>positive_meaning (decode_finite_system Q) \<longleftrightarrow>
        (\<exists>y z. x=Pair_Term y z \<and> (a,y)\<in>positive_meaning (decode_finite_system P) \<and>
          (b,z)\<in>positive_meaning (decode_finite_system P)))"
    using step.result step.install.extension step.install.member step.exact by blast
next
  fix P :: "local_address option finite_native_system" and a
  assume source: "schema_system_formed (decode_finite_system P)"
    and member: "a\<in>system_definitions (decode_finite_system P)"
  interpret step: finite_native_list_installation P a
    by (unfold_locales) (use source member in
      \<open>simp_all only: finite_system_formed_correct finite_system_definitions_correct\<close>)
  show "\<exists>d Q. finite_native_admission_list a P=Some (d,Q) \<and>
      admission_extension (decode_finite_system P) (decode_finite_system Q) \<and>
      d\<in>system_definitions (decode_finite_system Q) \<and>
      (\<forall>x. (d,x)\<in>positive_meaning (decode_finite_system Q) \<longleftrightarrow>
        (\<exists>xs. x=data_list_term xs \<and> (\<forall>y\<in>set xs. (a,y)\<in>positive_meaning (decode_finite_system P))))"
    using step.result step.install.extension step.install.member step.exact by blast
qed

theorem finite_construct_native_admission_total:
  assumes "finite_system_formed P" "finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
  shows "\<exists>d Q. finite_construct_native_admission g P=Some (d,Q) \<and>
    admission_goal_realized (decode_finite_system P) g d (decode_finite_system Q)"
  using finite_native_admission.total assms
  by (simp only: finite_construct_native_admission_def finite_system_formed_correct
    less_eq_fset.rep_eq finite_admission_goal_sites_correct finite_system_definitions_correct; blast)

theorem finite_construct_native_admission_correct:
  assumes "finite_system_formed P" "finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
    "finite_construct_native_admission g P=Some (d,Q)"
  shows "admission_goal_realized (decode_finite_system P) g d (decode_finite_system Q)"
  using finite_construct_native_admission_total[OF assms(1,2)] assms(3) by auto

lemma native_admission_source_constructor:
  "finite_native_source_constructor
    (\<lambda>P. finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P)
    (finite_construct_native_admission g)
    (\<lambda>P t. admission_goal_holds (positive_meaning (decode_finite_system P)) g t)"
  by (unfold_locales)
    (use finite_construct_native_admission_total in \<open>simp only: admission_goal_realized_def; blast\<close>)

section \<open>Actual source recovery establishes the complete constructor premise\<close>

theorem finite_native_admission_target_conditions:
  "finite_native_admission_target E pu pr g=Some (P,d,Q) \<longleftrightarrow>
    finite_native_source E pu pr=Some P \<and>
    finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P \<and>
    finite_construct_native_admission g P=Some (d,Q)"
  by (simp only: finite_native_admission_target_def finite_native_source_target_conditions)

theorem finite_native_admission_target_correct:
  assumes result: "finite_native_admission_target E pu pr g=Some (P,d,Q)"
  shows "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    "admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P)"
    "admission_goal_realized (decode_finite_system P) g d (decode_finite_system Q)"
  using finite_native_source_constructor.target_correct[OF native_admission_source_constructor
    result[unfolded finite_native_admission_target_def]]
  by (simp only: less_eq_fset.rep_eq finite_admission_goal_sites_correct finite_system_definitions_correct admission_goal_realized_def; blast)+

theorem finite_native_admission_target_total:
  "(\<exists>d Q. finite_native_admission_target E pu pr g=Some (P,d,Q)) \<longleftrightarrow>
    finite_native_source E pu pr=Some P \<and>
    finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
  by (simp only: finite_native_admission_target_def
    finite_native_source_constructor.target_total[OF native_admission_source_constructor])

lemma finite_native_admission_target_ready:
  assumes result: "finite_native_admission_target E pu pr g=Some (P,d,Q)"
  shows "finite_source_extension_context E pu pr Q=Some P"
  by (rule finite_native_source_constructor.target_ready[OF native_admission_source_constructor
    result[unfolded finite_native_admission_target_def]])


theorem finite_construct_source_admission_total:
  "(\<exists>d F u. finite_construct_source_admission E pu pr g=Some (d,F,u)) \<longleftrightarrow>
    (\<exists>P. finite_native_source E pu pr=Some P \<and>
      finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P)"
  by (simp only: finite_construct_source_admission_def
    finite_native_source_constructor.total[OF native_admission_source_constructor])

theorem finite_construct_source_admission_correct:
  assumes result: "finite_construct_source_admission E pu pr g=Some (d,F,u)"
  shows "\<exists>P Q e T. native_package_at (decode_finite_environment E) pu pr (decode_finite_system P) \<and>
    admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P) \<and>
    admission_goal_realized (decode_finite_system P) g e (decode_finite_system Q) \<and>
    finite_environment_formed F \<and> environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
    native_package_at (decode_finite_environment F) pu pr (decode_finite_system P) \<and>
    native_package_at (decode_finite_environment F) u [] T \<and>
    d\<in>system_definitions T \<and>
    (\<forall>t. (d,t)\<in>positive_meaning T \<longleftrightarrow> admission_goal_holds (positive_meaning (decode_finite_system P)) g t) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
      artifact_at (decode_finite_environment F) w A \<longleftrightarrow> artifact_at (decode_finite_environment E) w A) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
      binds_slot (decode_finite_environment F) w k v \<longleftrightarrow> binds_slot (decode_finite_environment E) w k v)"
  using finite_native_source_constructor.correct[OF native_admission_source_constructor
    result[unfolded finite_construct_source_admission_def]]
  by (simp only: less_eq_fset.rep_eq finite_admission_goal_sites_correct finite_system_definitions_correct
    admission_goal_realized_def; blast)

end
