theory Factor_Native_System_Extensions
  imports Factor_Native_Group_Extensions Factor_Fresh_Program_Coordinates
begin

section \<open>Install an ordinary program extension over its actual retained native source\<close>

theorem native_mapped_extension_total:
  fixes E :: "local_address option artifact_environment"
    and P Q :: "('a,'s,'d,'c) schema_system"
    and g :: "'d\<Rightarrow>local_address option definition_site"
  assumes native: "native_package_at E pu pr N"
    and source: "schema_system_formed P" and target: "schema_system_formed Q"
    and old_agreement: "systems_agree_on P Q (system_definitions P)"
    and source_injective: "inj_on g (system_definitions P)"
    and source_variant: "system_alpha_variant (rename_system g P) N"
  shows "\<exists>F h v T. environment_formed F \<and> environment_included E F \<and>
    native_package_at F pu pr N \<and> native_package_at F v [] T \<and>
    inj_on h (system_definitions Q) \<and> (\<forall>d\<in>system_definitions P. h d=g d) \<and>
    system_definitions T=h ` system_definitions Q \<and>
    system_alpha_variant (rename_system h Q) T \<and>
    positive_meaning T=map_prod h id ` positive_meaning Q \<and>
    (\<forall>d\<in>system_definitions Q. \<forall>t.
      schema_call_formed T (h d) t \<longleftrightarrow> schema_call_formed Q d t) \<and>
    (\<forall>d\<in>system_definitions Q-system_definitions P.
      fst (h d)\<notin>environment_uses E \<and> snd (h d)=[]) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>k z. binds_slot F w k z \<longleftrightarrow> binds_slot E w k z)"
proof -
  have environment: "environment_formed E"
    using native_package_projection(1)[OF native] by (simp add: native_package_formed_def)
  have inside: "system_definitions P\<subseteq>system_definitions Q"
    by (rule whole_agreement_definitions[OF old_agreement])
  have source_sites: "g ` system_definitions P=system_definitions N"
    using source_variant by (simp add: system_alpha_variant_def renamed_system_definitions)
  have positions: "g ` system_definitions P\<subseteq>environment_positions E"
    using native_package_entry_position[OF native] source_sites by blast
  obtain h where coordinates: "inj_on h (system_definitions Q)"
    "\<forall>d\<in>system_definitions P. h d=g d"
    "\<forall>d\<in>system_definitions Q-system_definitions P. snd (h d)=[]"
    "fst ` h ` (system_definitions Q-system_definitions P)\<inter>environment_uses E={}"
    using fresh_program_coordinates[OF environment system_definitions_finite[OF target] source_injective positions] by blast
  let ?S="rename_system h P"
  let ?V="rename_system h Q"
  let ?D="system_definitions ?V-system_definitions ?S"
  let ?C="system_restriction ?V ?D"
  have source_injective_h: "inj_on h (system_definitions P)" by (rule inj_on_subset[OF coordinates(1) inside])
  have same_source: "?S=rename_system g P" by (rule renamed_system_agreeing_coordinates[OF source coordinates(2)])
  have source_native: "system_alpha_variant ?S N" using source_variant same_source by simp
  have sf: "schema_system_formed ?S" by (rule renamed_system_formed[OF source source_injective_h])
  have vf: "schema_system_formed ?V" by (rule renamed_system_formed[OF target coordinates(1)])
  have agree: "systems_agree_on ?S ?V (system_definitions ?S)"
    by (simp only: renamed_system_definitions;
      rule renamed_system_extension_agreement[OF source target old_agreement coordinates(1)])
  have group: "schema_system_formed_over (system_definitions ?S) ?C"
    and complete: "system_union ?S ?C=?V"
    by (rule extension_definition_group[OF sf vf agree])+
  have image_difference: "h ` (system_definitions Q-system_definitions P)=
    h ` system_definitions Q-h ` system_definitions P"
    by (rule inj_on_image_set_diff[OF coordinates(1) _ inside]) auto
  have definitions: "system_definitions ?C=h ` (system_definitions Q-system_definitions P)"
    by (auto simp: renamed_system_definitions image_difference)
  have roots: "\<forall>d\<in>system_definitions ?C. snd d=[]"
    by (simp only: definitions) (use coordinates(3) in auto)
  have fresh: "fst ` system_definitions ?C\<inter>environment_uses E={}"
    using coordinates(4) by (simp only: definitions)
  obtain F v T where installed: "environment_formed F" "environment_included E F"
    "native_package_at F pu pr N" "native_package_at F v [] T"
    "system_alpha_variant (system_union ?S ?C) T"
    "\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A"
    "\<forall>w\<in>environment_uses E. \<forall>k z. binds_slot F w k z \<longleftrightarrow> binds_slot E w k z"
    using native_group_extension_total[OF native source_native group roots fresh] by blast
  have variant: "system_alpha_variant ?V T" using installed(5) complete by simp
  have domain: "system_definitions T=h ` system_definitions Q"
    using variant by (simp add: system_alpha_variant_def renamed_system_definitions)
  have meaning: "positive_meaning T=map_prod h id ` positive_meaning Q"
    using system_alpha_positive_meaning[OF variant] renamed_system_positive_meaning[OF target coordinates(1)] by simp
  have calls: "\<forall>d\<in>system_definitions Q. \<forall>t.
    schema_call_formed T (h d) t \<longleftrightarrow> schema_call_formed Q d t"
    using system_alpha_calls[OF variant] renamed_system_call[OF target coordinates(1)] by blast
  have fresh_sites: "\<forall>d\<in>system_definitions Q-system_definitions P.
    fst (h d)\<notin>environment_uses E \<and> snd (h d)=[]"
    using coordinates(3,4) by auto
  show ?thesis by (rule exI[of _ F], rule exI[of _ h], rule exI[of _ v], rule exI[of _ T])
    (use installed(1-4,6,7) coordinates(1,2) domain variant meaning calls fresh_sites in blast)
qed

text \<open>
  The independently formed extension retains every old source interface and
  complete clause family. Its added definitions are derived by restriction.
  Their coordinates extend the actual source map; all old addresses stay fixed.
  The native group constructor therefore installs the complete extension over
  the retained material. The resulting whole-program correspondence includes
  recursion and all future arguments. No source-domain substitute supplies
  the source meaning, and no old artifact or outgoing binding is replaced.
\<close>

end
