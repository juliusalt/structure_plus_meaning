theory Factor_Mapped_Extension_Coordinates
  imports Factor_Native_Group_Extensions Factor_Fresh_Program_Coordinates
begin

section \<open>The whole source correspondence fixes actual existing positions\<close>

lemma native_renamed_source_positions:
  assumes native: "native_package_at E pu pr N"
    and variant: "system_alpha_variant (rename_system g P) N"
  shows "image g (system_definitions P)\<subseteq>environment_positions E"
proof -
  have sites: "image g (system_definitions P)=system_definitions N"
    using variant by (simp add: system_alpha_variant_def renamed_system_definitions)
  show ?thesis using native_package_entry_position[OF native] by (simp only: sites; blast)
qed

section \<open>One coordinate argument relocates an entire extension\<close>

locale mapped_extension_coordinates =
  fixes P Q :: "('a,'s,'d,'c) schema_system" and g h :: "'d\<Rightarrow>'e"
  assumes source: "schema_system_formed P" and target: "schema_system_formed Q"
    and agreement: "systems_agree_on P Q (system_definitions P)"
    and injective: "inj_on h (system_definitions Q)"
    and fixed: "\<forall>d\<in>system_definitions P. h d=g d"
begin

abbreviation old where "old \<equiv> rename_system h P"
abbreviation goal where "goal \<equiv> rename_system h Q"
abbreviation added where "added \<equiv> system_definitions goal-system_definitions old"
abbreviation group where "group \<equiv> system_restriction goal added"

lemma inside: "system_definitions P\<subseteq>system_definitions Q"
  by (rule whole_agreement_definitions[OF agreement])
lemma source_injective: "inj_on h (system_definitions P)" by (rule inj_on_subset[OF injective inside])
lemma source_equation: "old=rename_system g P"
  by (rule renamed_system_agreeing_coordinates[OF source fixed])
lemma source_formed: "schema_system_formed old" by (rule renamed_system_formed[OF source source_injective])
lemma target_formed: "schema_system_formed goal" by (rule renamed_system_formed[OF target injective])
lemma target_agreement: "systems_agree_on old goal (system_definitions old)"
  by (simp only: renamed_system_definitions; rule renamed_system_extension_agreement[OF source target agreement injective])

lemma additions: "added=image h (system_definitions Q-system_definitions P)"
  using inj_on_image_set_diff[OF injective Diff_subset inside]
  by (simp only: renamed_system_definitions)

lemma group_formed: "schema_system_formed_over (system_definitions old) group"
  and whole: "system_union old group=goal"
  by (rule extension_definition_group[OF source_formed target_formed target_agreement])+

lemma group_definitions: "system_definitions group=image h (system_definitions Q-system_definitions P)"
  by (auto simp: additions[symmetric])

end

end
