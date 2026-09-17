theory Factor_Finite_Source_Entry_Installation
  imports Factor_Finite_Source_Extensions
begin

section \<open>Install a complete extension and return one of its placed entries\<close>

definition finite_install_source_entry where
  "finite_install_source_entry E pu pr Q e=(if e |\<in>| finite_system_definitions Q then
    map_option (\<lambda>(P,F,u).
      (finite_program_coordinates E (finite_system_definitions P) (finite_system_definitions Q) id e,F,u))
      (finite_extend_source_native E pu pr Q) else None)"

theorem finite_install_source_entry_conditions:
  "finite_install_source_entry E pu pr Q e=Some (d,F,u) \<longleftrightarrow>
    (\<exists>P. finite_extend_source_native E pu pr Q=Some (P,F,u) \<and>
      e |\<in>| finite_system_definitions Q \<and>
      d=finite_program_coordinates E (finite_system_definitions P) (finite_system_definitions Q) id e)"
  by (auto simp: finite_install_source_entry_def split: option.splits prod.splits if_splits)

theorem finite_install_source_entry_total:
  "(\<exists>d F u. finite_install_source_entry E pu pr Q e=Some (d,F,u)) \<longleftrightarrow>
    e |\<in>| finite_system_definitions Q \<and> (\<exists>P. finite_source_extension_context E pu pr Q=Some P)"
  by (simp only: finite_install_source_entry_conditions; use finite_extend_source_native_total[of E pu pr Q] in blast)

theorem finite_install_source_entry_correct:
  assumes result: "finite_install_source_entry E pu pr Q e=Some (d,F,u)"
    and source_context: "finite_source_extension_context E pu pr Q=Some P"
  shows "\<exists>T. native_package_at (decode_finite_environment E) pu pr (decode_finite_system P) \<and>
    finite_environment_formed F \<and> environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
    native_package_at (decode_finite_environment F) pu pr (decode_finite_system P) \<and>
    native_package_at (decode_finite_environment F) u [] T \<and> d\<in>system_definitions T \<and>
    (\<forall>t. (d,t)\<in>positive_meaning T \<longleftrightarrow> (e,t)\<in>positive_meaning (decode_finite_system Q)) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
      artifact_at (decode_finite_environment F) w A \<longleftrightarrow> artifact_at (decode_finite_environment E) w A) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
      binds_slot (decode_finite_environment F) w k v \<longleftrightarrow> binds_slot (decode_finite_environment E) w k v)"
proof -
  obtain N where installed0: "finite_extend_source_native E pu pr Q=Some (N,F,u)"
    and member: "e |\<in>| finite_system_definitions Q"
    and entry0: "d=finite_program_coordinates E (finite_system_definitions N) (finite_system_definitions Q) id e"
    using result by (simp only: finite_install_source_entry_conditions; blast)
  have same: "N=P"
    using installed0 source_context by (simp only: finite_extend_source_native_conditions; auto)
  have installed: "finite_extend_source_native E pu pr Q=Some (P,F,u)"
    and entry: "d=finite_program_coordinates E (finite_system_definitions P) (finite_system_definitions Q) id e"
    using installed0 entry0 by (simp only: same)+
  have source: "native_package_at (decode_finite_environment E) pu pr (decode_finite_system P)"
    and formed: "schema_system_formed (decode_finite_system Q)"
    using source_context by (simp only: finite_source_extension_context_correct; blast)+
  interpret run: finite_source_native_run E F pu u pr P Q
    by (unfold_locales) (rule installed)
  let ?h="finite_program_coordinates E (finite_system_definitions P) (finite_system_definitions Q) id"
  obtain T where native: "native_package_at (decode_finite_environment F) u [] T"
    and variant: "system_alpha_variant (rename_system ?h (decode_finite_system Q)) T"
    and definitions: "system_definitions T=image ?h (fset (finite_system_definitions Q))"
    using run.correct[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1] by blast
  have injective: "inj_on ?h (system_definitions (decode_finite_system Q))"
    using run.correct[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
    by (simp only: finite_system_definitions_correct)
  have old_member: "e\<in>system_definitions (decode_finite_system Q)"
    using member by (simp only: finite_system_definitions_correct)
  have target_member: "d\<in>system_definitions T"
    using member by (simp only: definitions entry; rule imageI)
  have meaning: "\<And>t. (d,t)\<in>positive_meaning T \<longleftrightarrow>
      (e,t)\<in>positive_meaning (decode_finite_system Q)"
    by (simp only: entry system_variant_renamed_meaning_at[OF formed injective variant old_member])
  show ?thesis by (rule exI[of _ T])
    (use source run.correct native target_member meaning in blast)
qed

end
