theory Factor_Finite_Native_Requirement_Construction
  imports Factor_Finite_Native_Admission_Construction Factor_Admission_Goal_Sequences
    Factor_Finite_Native_Requirement_Guards
begin

section \<open>The native constructor instantiates the shared occurrence traversal\<close>

lemma native_requirement_constructor: "admission_goal_constructor
    (decode_finite_system :: local_address option finite_native_system\<Rightarrow>local_address option native_system)
    finite_native_admission_leaf finite_native_admission_pair finite_native_admission_list"
  by (unfold_locales)
    (rule finite_native_admission.leaf_step | rule finite_native_admission.pair_step |
      rule finite_native_admission.collection_step | assumption)+

definition finite_construct_native_admission_sequence where
  "finite_construct_native_admission_sequence gs P=construct_admission_sequence finite_construct_native_admission gs P"

theorem finite_construct_native_admission_sequence_total:
  assumes "finite_system_formed P"
    "\<forall>g\<in>set gs. finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
  shows "\<exists>ds Q. finite_construct_native_admission_sequence gs P=Some (ds,Q) \<and>
    admission_extension (decode_finite_system P) (decode_finite_system Q) \<and>
    admission_goal_results (decode_finite_system P) gs ds (decode_finite_system Q)"
  using admission_goal_constructor.sequence_total[OF native_requirement_constructor, where s=P and gs=gs] assms
  by (simp only: finite_construct_native_admission_sequence_def finite_construct_native_admission_def[abs_def]
    finite_system_formed_correct less_eq_fset.rep_eq finite_admission_goal_sites_correct
    finite_system_definitions_correct; blast)

theorem finite_construct_native_admission_sequence_correct:
  assumes "finite_system_formed P"
    "\<forall>g\<in>set gs. finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
    "finite_construct_native_admission_sequence gs P=Some (ds,Q)"
  shows "admission_extension (decode_finite_system P) (decode_finite_system Q) \<and>
    admission_goal_results (decode_finite_system P) gs ds (decode_finite_system Q)"
  using finite_construct_native_admission_sequence_total[OF assms(1,2)] assms(3) by auto

section \<open>One final guard requires every original goal of the same term\<close>

definition finite_construct_native_requirements where
  "finite_construct_native_requirements gs P=(case finite_construct_native_admission_sequence gs P of
    None \<Rightarrow> None | Some (ds,Q) \<Rightarrow> finite_native_requirement_guard ds Q)"

lemma finite_construct_native_requirements_conditions:
  "finite_construct_native_requirements gs P=Some (e,R) \<longleftrightarrow>
    (\<exists>ds Q. finite_construct_native_admission_sequence gs P=Some (ds,Q) \<and>
      finite_native_requirement_guard ds Q=Some (e,R))"
  by (auto simp: finite_construct_native_requirements_def split: option.splits prod.splits)

theorem finite_construct_native_requirements_occurrences:
  assumes "finite_system_formed P"
    "\<forall>g\<in>set gs. finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
    "finite_construct_native_requirements gs P=Some (e,R)"
  shows "\<exists>ds Q. finite_construct_native_admission_sequence gs P=Some (ds,Q) \<and>
    finite_native_requirement_guard ds Q=Some (e,R) \<and> length ds=length gs \<and>
    (\<forall>i<length gs. ds!i\<in>system_definitions (decode_finite_system Q) \<and>
      (\<forall>t. (ds!i,t)\<in>positive_meaning (decode_finite_system Q) \<longleftrightarrow>
        admission_goal_holds (positive_meaning (decode_finite_system P)) (gs!i) t))"
proof -
  obtain ds Q where sequence: "finite_construct_native_admission_sequence gs P=Some (ds,Q)"
    and guard: "finite_native_requirement_guard ds Q=Some (e,R)"
    using assms(3) by (simp only: finite_construct_native_requirements_conditions; blast)
  have results: "admission_goal_results (decode_finite_system P) gs ds (decode_finite_system Q)"
    using finite_construct_native_admission_sequence_correct[OF assms(1,2) sequence] by blast
  have length: "length ds=length gs" using admission_goal_results_length[OF results] by simp
  have each: "ds!i\<in>system_definitions (decode_finite_system Q) \<and>
      (\<forall>t. (ds!i,t)\<in>positive_meaning (decode_finite_system Q) \<longleftrightarrow>
        admission_goal_holds (positive_meaning (decode_finite_system P)) (gs!i) t)"
    if bound: "i<length gs" for i
    using admission_goal_results_at[OF results bound] by blast
  show ?thesis by (rule exI[of _ ds], rule exI[of _ Q])
    (use sequence guard length each in blast)
qed

theorem finite_construct_native_requirements_total:
  assumes source: "finite_system_formed P"
    and supported: "\<forall>g\<in>set gs. finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
  shows "\<exists>d Q. finite_construct_native_requirements gs P=Some (d,Q) \<and>
    admission_requirements_realized (decode_finite_system P) gs d (decode_finite_system Q)"
proof -
  obtain ds Q where sequence: "finite_construct_native_admission_sequence gs P=Some (ds,Q)"
    and extension: "admission_extension (decode_finite_system P) (decode_finite_system Q)"
    and results: "admission_goal_results (decode_finite_system P) gs ds (decode_finite_system Q)"
    using finite_construct_native_admission_sequence_total[OF source supported] by blast
  have formed: "finite_system_formed Q"
    using extension by (simp only: admission_extension_def finite_system_formed_correct; blast)
  have members: "set ds\<subseteq>fset (finite_system_definitions Q)"
    using admission_goal_results_members[OF results] by (simp only: finite_system_definitions_correct)
  interpret guard: finite_native_requirement_guard_installation Q ds
    by (unfold_locales) (rule formed, rule members)
  have complete: "admission_extension (decode_finite_system P) (decode_finite_system guard.install.target)"
    by (rule admission_extension_trans[OF extension guard.install.extension])
  have meaning: "(guard.install.entry,t)\<in>positive_meaning (decode_finite_system guard.install.target) \<longleftrightarrow>
      term_formed t \<and> (\<forall>g\<in>set gs. admission_goal_holds (positive_meaning (decode_finite_system P)) g t)" for t
    by (simp only: guard.exact admission_goal_results_all[OF results])
  have realized: "admission_requirements_realized (decode_finite_system P) gs guard.install.entry
      (decode_finite_system guard.install.target)"
    using complete guard.install.member meaning by (simp only: admission_requirements_realized_def admission_requirements_hold_def; blast)
  have constructed: "finite_construct_native_requirements gs P=Some (guard.install.entry,guard.install.target)"
    by (simp only: finite_construct_native_requirements_def sequence option.case prod.case guard.result)
  show ?thesis using constructed realized by blast
qed

theorem finite_construct_native_requirements_correct:
  assumes "finite_system_formed P"
    "\<forall>g\<in>set gs. finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
    "finite_construct_native_requirements gs P=Some (d,Q)"
  shows "admission_requirements_realized (decode_finite_system P) gs d (decode_finite_system Q)"
  using finite_construct_native_requirements_total[OF assms(1,2)] assms(3) by auto

export_code finite_construct_native_requirements checking SML

end
