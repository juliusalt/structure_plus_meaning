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

section \<open>Actual source recovery establishes the complete constructor premise\<close>

theorem finite_native_admission_target_conditions:
  "finite_native_admission_target E pu pr g=Some (P,d,Q) \<longleftrightarrow>
    finite_native_source E pu pr=Some P \<and>
    finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P \<and>
    finite_construct_native_admission g P=Some (d,Q)"
  by (cases d) (auto simp: finite_native_admission_target_def split: option.splits prod.splits if_splits)

theorem finite_native_admission_target_correct:
  assumes result: "finite_native_admission_target E pu pr g=Some (P,d,Q)"
  shows "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    "admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P)"
    "admission_goal_realized (decode_finite_system P) g d (decode_finite_system Q)"
proof -
  have source: "finite_native_source E pu pr=Some P"
    and supported: "finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
    and constructed: "finite_construct_native_admission g P=Some (d,Q)"
    using result by (simp only: finite_native_admission_target_conditions; blast)+
  show native: "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    using source by (simp only: finite_native_source_correct)
  show "admission_goal_sites g\<subseteq>system_definitions (decode_finite_system P)"
    using supported by (simp only: less_eq_fset.rep_eq finite_admission_goal_sites_correct finite_system_definitions_correct)
  have formed: "finite_system_formed P"
    using native_package_system_formed[OF native] by (simp only: finite_system_formed_correct)
  show "admission_goal_realized (decode_finite_system P) g d (decode_finite_system Q)"
    by (rule finite_construct_native_admission_correct[OF formed supported constructed])
qed

theorem finite_native_admission_target_total:
  "(\<exists>d Q. finite_native_admission_target E pu pr g=Some (P,d,Q)) \<longleftrightarrow>
    finite_native_source E pu pr=Some P \<and>
    finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
proof
  assume "\<exists>d Q. finite_native_admission_target E pu pr g=Some (P,d,Q)"
  then show "finite_native_source E pu pr=Some P \<and> finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
    by (simp only: finite_native_admission_target_conditions; blast)
next
  assume ready: "finite_native_source E pu pr=Some P \<and> finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
  have native: "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    using ready by (simp only: finite_native_source_correct; blast)
  have formed: "finite_system_formed P"
    using native_package_system_formed[OF native] by (simp only: finite_system_formed_correct)
  show "\<exists>d Q. finite_native_admission_target E pu pr g=Some (P,d,Q)"
    using finite_construct_native_admission_total[OF formed, of g] ready
    by (simp only: finite_native_admission_target_conditions; blast)
qed

lemma finite_native_admission_target_ready:
  assumes result: "finite_native_admission_target E pu pr g=Some (P,d,Q)"
  shows "finite_source_extension_context E pu pr Q=Some P"
  using finite_native_admission_target_correct(1,3)[OF result]
  by (simp only: finite_source_extension_context_correct admission_goal_realized_def admission_extension_def; blast)

theorem finite_construct_source_admission_total:
  "(\<exists>d F u. finite_construct_source_admission E pu pr g=Some (d,F,u)) \<longleftrightarrow>
    (\<exists>P. finite_native_source E pu pr=Some P \<and>
      finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P)"
proof
  assume "\<exists>d F u. finite_construct_source_admission E pu pr g=Some (d,F,u)"
  then show "\<exists>P. finite_native_source E pu pr=Some P \<and>
      finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
    by (auto simp: finite_construct_source_admission_def finite_native_admission_target_conditions
      split: option.splits prod.splits)
next
  assume "\<exists>P. finite_native_source E pu pr=Some P \<and>
      finite_admission_goal_sites g |\<subseteq>| finite_system_definitions P"
  then obtain P d Q where target: "finite_native_admission_target E pu pr g=Some (P,d,Q)"
    by (simp only: finite_native_admission_target_total[symmetric]; blast)
  obtain F u where installed: "finite_extend_source_native E pu pr Q=Some (P,F,u)"
    using finite_extend_source_native_total[of E pu pr Q P] finite_native_admission_target_ready[OF target] by blast
  show "\<exists>d F u. finite_construct_source_admission E pu pr g=Some (d,F,u)"
    by (simp add: finite_construct_source_admission_def target installed)
qed

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
proof -
  obtain P e Q N where target: "finite_native_admission_target E pu pr g=Some (P,e,Q)"
    and installed: "finite_extend_source_native E pu pr Q=Some (N,F,u)"
    and entry: "d=finite_program_coordinates E (finite_system_definitions P) (finite_system_definitions Q) id e"
    using result by (auto simp: finite_construct_source_admission_def split: option.splits prod.splits)
  have ready: "finite_source_extension_context E pu pr Q=Some P"
    by (rule finite_native_admission_target_ready[OF target])
  have same: "N=P" using installed ready by (simp only: finite_extend_source_native_conditions; auto)
  interpret run: finite_source_native_run E F pu u pr P Q
    by (unfold_locales) (use installed same in simp)
  let ?h="finite_program_coordinates E (finite_system_definitions P) (finite_system_definitions Q) id"
  obtain T where native: "native_package_at (decode_finite_environment F) u [] T"
    and variant: "system_alpha_variant (rename_system ?h (decode_finite_system Q)) T"
    and definitions: "system_definitions T=image ?h (fset (finite_system_definitions Q))"
    using run.correct by blast
  have injective: "inj_on ?h (system_definitions (decode_finite_system Q))"
    using run.correct by (simp only: finite_system_definitions_correct; blast)
  have realized: "admission_goal_realized (decode_finite_system P) g e (decode_finite_system Q)"
    by (rule finite_native_admission_target_correct(3)[OF target])
  have formed: "schema_system_formed (decode_finite_system Q)"
    and member: "e\<in>system_definitions (decode_finite_system Q)"
    and meaning: "\<And>t. (e,t)\<in>positive_meaning (decode_finite_system Q) \<longleftrightarrow>
      admission_goal_holds (positive_meaning (decode_finite_system P)) g t"
    using realized by (simp only: admission_goal_realized_def admission_extension_def; blast)+
  have target_member: "d\<in>system_definitions T"
    using member by (simp only: definitions entry finite_system_definitions_correct; rule imageI)
  have exact: "\<And>t. (d,t)\<in>positive_meaning T \<longleftrightarrow>
      admission_goal_holds (positive_meaning (decode_finite_system P)) g t"
    by (simp only: entry system_variant_renamed_meaning_at[OF formed injective variant member] meaning)
  show ?thesis by (rule exI[of _ P], rule exI[of _ Q], rule exI[of _ e], rule exI[of _ T])
    (use finite_native_admission_target_correct(1,2)[OF target] realized run.correct native target_member exact in blast)
qed

end
