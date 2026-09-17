theory Factor_Finite_Native_Extension_Cases
  imports Factor_Finite_Mapped_Extensions Factor_Finite_Requirement_Installation Factor_Finite_Checked_Requirements
    Factor_Native_Requirement_Cases Factor_Finite_Guard_Source_Extensions Factor_Finite_Native_Observations
begin

definition finite_source_requirement_extension where
  "finite_source_requirement_extension b paired=(let E=finite_guard_source b; P=finite_nat_guard_source_model b in
    case finite_checked_admission_sequence (finite_system_definitions P) [source_requirement_goal paired] 1 of None \<Rightarrow> None
    | Some (ds,k,cs) \<Rightarrow>
      (let Q=finite_required_admission_system P ds k cs;
        h=finite_program_coordinates E (finite_system_definitions P) (finite_system_definitions Q) native_guard_source_coordinate in
        map_option (\<lambda>(F,u). (F,u,h k)) (finite_extend_mapped_native E P Q native_guard_source_coordinate)))"

lemma finite_source_requirement_checked:
  "finite_checked_admission_sequence (finite_system_definitions (finite_nat_guard_source_model b))
    [source_requirement_goal paired] 1=Some (source_requirement_sequence paired)"
  using source_requirement_checked[where b=b and paired=paired]
  by (simp only: finite_checked_admission_sequence_correct finite_system_definitions_correct finite_nat_guard_source_model_correct)

locale finite_source_requirement_case =
  fixes b paired :: bool and ds :: "nat list" and k :: nat and cs :: "admission_instruction list"
  assumes sequence: "source_requirement_sequence paired=(ds,k,cs)"
begin

abbreviation source where "source \<equiv> finite_nat_guard_source_model b"
abbreviation goal where "goal \<equiv> finite_required_admission_system source ds k cs"
abbreviation environment where "environment \<equiv> finite_guard_source b"
abbreviation placement where
  "placement \<equiv> finite_program_coordinates environment (finite_system_definitions source) (finite_system_definitions goal) native_guard_source_coordinate"

lemma plan: "checked_admission_sequence (system_definitions (nat_guard_source_model b))
    [source_requirement_goal paired] 1=Some (ds,k,cs)"
  by (simp only: source_requirement_checked sequence)
lemma extension: "admission_extension (nat_guard_source_model b) (decode_finite_system goal)"
  by (simp only: finite_required_admission_system_correct finite_nat_guard_source_model_correct;
    rule checked_admission_sequence_installed(2)[OF nat_guard_source_model_formed plan])
lemma target_formed: "finite_system_formed goal" using extension by (simp add: admission_extension_def finite_system_formed_correct)
lemma agreement: "systems_agree_on (decode_finite_system source) (decode_finite_system goal)
    (system_definitions (decode_finite_system source))"
  using extension by (simp add: finite_nat_guard_source_model_correct admission_extension_def)

sublocale installed: finite_mapped_native_extension environment source goal None "[0]"
    "decode_finite_system (finite_guard_source_program b)" native_guard_source_coordinate
  by (rule finite_guard_source_extension_profile[OF target_formed agreement])

lemma result:
  "finite_source_requirement_extension b paired=
    map_option (\<lambda>(F,u). (F,u,placement k)) (finite_extend_mapped_native environment source goal native_guard_source_coordinate)"
  by (simp only: finite_source_requirement_extension_def Let_def finite_source_requirement_checked sequence option.simps prod.case)

theorem total: "\<exists>F u d. finite_source_requirement_extension b paired=Some (F,u,d)"
  using installed.total by (simp only: result; auto)

theorem correct:
  assumes built: "finite_source_requirement_extension b paired=Some (F,u,d)"
  shows "finite_environment_formed F \<and>
    native_package_at (decode_finite_environment F) None [0] (decode_finite_system (finite_guard_source_program b)) \<and>
    (\<exists>T. native_package_at (decode_finite_environment F) u [] T \<and>
      system_alpha_variant (rename_system placement (required_admission_system (nat_guard_source_model b) ds k cs)) T \<and>
      d\<in>system_definitions T \<and>
      (\<forall>t. (d,t)\<in>positive_meaning T \<longleftrightarrow> term_formed t \<and>
        admission_goal_holds (native_guard_source_calls b) (source_requirement_goal paired) t))"
proof -
  have installed: "finite_extend_mapped_native environment source goal native_guard_source_coordinate=Some (F,u)"
    and entry: "d=placement k" using built by (auto simp: result split: option.splits prod.splits)
  obtain T where actual: "finite_environment_formed F"
    "native_package_at (decode_finite_environment F) None [0] (decode_finite_system (finite_guard_source_program b))"
    "native_package_at (decode_finite_environment F) u [] T"
    "system_alpha_variant (rename_system placement (decode_finite_system goal)) T"
    "system_definitions T=image placement (fset (finite_system_definitions goal))"
    using installed.correct[OF installed] by (elim conjE exE) blast
  have source: "schema_system_formed (decode_finite_system goal)" using target_formed by (simp only: finite_system_formed_correct)
  have injective: "inj_on placement (system_definitions (decode_finite_system goal))"
    using installed.coordinates(1) by (simp only: finite_system_definitions_correct)
  have member: "k\<in>system_definitions (decode_finite_system goal)" by simp
  have target_member: "d\<in>system_definitions T" using actual(5) member by (simp only: entry finite_system_definitions_correct; blast)
  have meaning: "\<forall>t. (d,t)\<in>positive_meaning T \<longleftrightarrow> term_formed t \<and>
    admission_goal_holds (native_guard_source_calls b) (source_requirement_goal paired) t"
    by (simp only: entry system_variant_renamed_meaning_at[OF source injective actual(4) member]
      finite_required_admission_system_correct finite_nat_guard_source_model_correct
      checked_admission_sequence_installed(3)[OF nat_guard_source_model_formed plan] nat_guard_source_model_basis; simp)
  have target: "\<exists>T. native_package_at (decode_finite_environment F) u [] T \<and>
      system_alpha_variant (rename_system placement (required_admission_system (nat_guard_source_model b) ds k cs)) T \<and>
      d\<in>system_definitions T \<and>
      (\<forall>t. (d,t)\<in>positive_meaning T \<longleftrightarrow> term_formed t \<and>
        admission_goal_holds (native_guard_source_calls b) (source_requirement_goal paired) t)"
    by (rule exI[of _ T]) (use actual(3,4) target_member meaning in
      \<open>simp only: finite_required_admission_system_correct finite_nat_guard_source_model_correct; blast\<close>)
  show ?thesis using actual(1,2) target by blast
qed

end

definition finite_native_extension_report where
  "finite_native_extension_report b paired=map_option (\<lambda>(F,u,d).
    (d,finite_native_package_observation F None [0] (finite_guard_source_program b) (finite_guard_source_program (\<not>b)) u))
    (finite_source_requirement_extension b paired)"

end
