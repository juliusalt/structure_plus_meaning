theory Factor_Finite_Source_Construction
  imports Factor_Finite_Source_Entry_Installation Factor_Admission_Installation
begin

definition finite_native_source_target where
  "finite_native_source_target supported C E pu pr=(case finite_native_source E pu pr of None \<Rightarrow> None
    | Some P \<Rightarrow> if supported P then map_option (\<lambda>(e,Q). (P,e,Q)) (C P) else None)"

lemma finite_native_source_target_conditions:
  "finite_native_source_target supported C E pu pr=Some (P,e,Q) \<longleftrightarrow>
    finite_native_source E pu pr=Some P \<and> supported P \<and> C P=Some (e,Q)"
  by (auto simp: finite_native_source_target_def split: option.splits prod.splits if_splits)

definition finite_construct_source where
  "finite_construct_source supported C E pu pr=(case finite_native_source_target supported C E pu pr of
    None \<Rightarrow> None | Some (P,e,Q) \<Rightarrow> finite_install_source_entry E pu pr Q e)"

locale finite_native_source_constructor =
  fixes supported :: "local_address option finite_native_system\<Rightarrow>bool"
    and C :: "local_address option finite_native_system\<Rightarrow>
      (local_address option definition_site\<times>local_address option finite_native_system) option"
    and expected :: "local_address option finite_native_system\<Rightarrow>factor_term\<Rightarrow>bool"
  assumes construct_total: "\<And>P. finite_system_formed P \<Longrightarrow> supported P \<Longrightarrow>
    \<exists>e Q. C P=Some (e,Q) \<and> admission_extension (decode_finite_system P) (decode_finite_system Q) \<and>
      e\<in>system_definitions (decode_finite_system Q) \<and>
      (\<forall>t. (e,t)\<in>positive_meaning (decode_finite_system Q) \<longleftrightarrow> expected P t)"
begin

theorem target_total:
  "(\<exists>e Q. finite_native_source_target supported C E pu pr=Some (P,e,Q)) \<longleftrightarrow>
    finite_native_source E pu pr=Some P \<and> supported P"
proof
  assume "\<exists>e Q. finite_native_source_target supported C E pu pr=Some (P,e,Q)"
  then show "finite_native_source E pu pr=Some P \<and> supported P"
    by (simp only: finite_native_source_target_conditions; blast)
next
  assume ready: "finite_native_source E pu pr=Some P \<and> supported P"
  have source: "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    using ready by (simp only: finite_native_source_correct; blast)
  have formed: "finite_system_formed P"
    using native_package_system_formed[OF source] by (simp only: finite_system_formed_correct)
  show "\<exists>e Q. finite_native_source_target supported C E pu pr=Some (P,e,Q)"
    using construct_total[OF formed] ready by (simp only: finite_native_source_target_conditions; blast)
qed

theorem target_correct:
  assumes result: "finite_native_source_target supported C E pu pr=Some (P,e,Q)"
  shows "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P) \<and>
    supported P \<and> C P=Some (e,Q) \<and>
    admission_extension (decode_finite_system P) (decode_finite_system Q) \<and>
    e\<in>system_definitions (decode_finite_system Q) \<and>
      (\<forall>t. (e,t)\<in>positive_meaning (decode_finite_system Q) \<longleftrightarrow> expected P t)"
proof -
  have source: "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    and supported: "supported P" and constructed: "C P=Some (e,Q)"
    using result by (simp only: finite_native_source_target_conditions finite_native_source_correct; blast)+
  have formed: "finite_system_formed P"
    using native_package_system_formed[OF source] by (simp only: finite_system_formed_correct)
  have complete: "admission_extension (decode_finite_system P) (decode_finite_system Q) \<and>
      e\<in>system_definitions (decode_finite_system Q) \<and>
      (\<forall>t. (e,t)\<in>positive_meaning (decode_finite_system Q) \<longleftrightarrow> expected P t)"
    using construct_total[OF formed supported] constructed by auto
  show ?thesis using source supported constructed complete by blast
qed

lemma target_ready:
  "finite_native_source_target supported C E pu pr=Some (P,e,Q) \<Longrightarrow>
    finite_source_extension_context E pu pr Q=Some P"
  using target_correct
  by (simp only: finite_source_extension_context_correct admission_extension_def; blast)

theorem total:
  "(\<exists>d F u. finite_construct_source supported C E pu pr=Some (d,F,u)) \<longleftrightarrow>
    (\<exists>P. finite_native_source E pu pr=Some P \<and> supported P)"
proof
  assume "\<exists>d F u. finite_construct_source supported C E pu pr=Some (d,F,u)"
  then show "\<exists>P. finite_native_source E pu pr=Some P \<and> supported P"
    by (auto simp: finite_construct_source_def finite_native_source_target_conditions split: option.splits prod.splits)
next
  assume "\<exists>P. finite_native_source E pu pr=Some P \<and> supported P"
  then obtain P e Q where target: "finite_native_source_target supported C E pu pr=Some (P,e,Q)"
    by (simp only: target_total[symmetric]; blast)
  have member: "e |\<in>| finite_system_definitions Q"
    using target_correct[OF target] by (simp only: finite_system_definitions_correct; blast)
  obtain d F u where installed: "finite_install_source_entry E pu pr Q e=Some (d,F,u)"
    using finite_install_source_entry_total[of E pu pr Q e] member target_ready[OF target] by blast
  show "\<exists>d F u. finite_construct_source supported C E pu pr=Some (d,F,u)"
    by (simp add: finite_construct_source_def target installed)
qed

theorem correct:
  assumes result: "finite_construct_source supported C E pu pr=Some (d,F,u)"
  shows "\<exists>P e Q T. native_package_at (decode_finite_environment E) pu pr (decode_finite_system P) \<and>
    supported P \<and> C P=Some (e,Q) \<and>
    admission_extension (decode_finite_system P) (decode_finite_system Q) \<and>
    e\<in>system_definitions (decode_finite_system Q) \<and>
    (\<forall>t. (e,t)\<in>positive_meaning (decode_finite_system Q) \<longleftrightarrow> expected P t) \<and>
    finite_environment_formed F \<and> environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
    native_package_at (decode_finite_environment F) pu pr (decode_finite_system P) \<and>
    native_package_at (decode_finite_environment F) u [] T \<and> d\<in>system_definitions T \<and>
    (\<forall>t. (d,t)\<in>positive_meaning T \<longleftrightarrow> expected P t) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
      artifact_at (decode_finite_environment F) w A \<longleftrightarrow> artifact_at (decode_finite_environment E) w A) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
      binds_slot (decode_finite_environment F) w k v \<longleftrightarrow> binds_slot (decode_finite_environment E) w k v)"
proof -
  obtain P e Q where target: "finite_native_source_target supported C E pu pr=Some (P,e,Q)"
    and installed: "finite_install_source_entry E pu pr Q e=Some (d,F,u)"
    using result by (auto simp: finite_construct_source_def split: option.splits prod.splits)
  show ?thesis by (rule exI[of _ P], rule exI[of _ e], rule exI[of _ Q])
    (use target_correct[OF target]
      finite_install_source_entry_correct[OF installed target_ready[OF target]] in blast)
qed

end

end
