theory Factor_Finite_Mapped_Extensions
  imports Factor_Finite_Native_Extensions Factor_Finite_Program_Coordinates Factor_Mapped_Extension_Coordinates
begin

section \<open>Execute automatic placement and complete native extension together\<close>

definition finite_extend_mapped_native :: "local_address option finite_artifact_environment\<Rightarrow>
    ('a::linorder,'s::linorder,'d::linorder,'c::linorder) finite_schema_system\<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system\<Rightarrow>('d\<Rightarrow>local_address option definition_site)\<Rightarrow>
    (local_address option finite_artifact_environment\<times>local_address option) option" where
  "finite_extend_mapped_native E P Q g=(let h=finite_program_coordinates E (finite_system_definitions P) (finite_system_definitions Q) g in
    finite_extend_native E (finite_rename_system h P) (finite_rename_system h Q))"

locale finite_mapped_native_extension =
  fixes E :: "local_address option finite_artifact_environment"
    and P Q :: "('a::linorder,'s::linorder,'d::linorder,'c::linorder) finite_schema_system"
    and pu :: "local_address option" and pr :: local_address
    and N :: "local_address option native_system"
    and g :: "'d\<Rightarrow>local_address option definition_site"
  assumes native: "native_package_at (decode_finite_environment E) pu pr N"
    and source: "finite_system_formed P" and target: "finite_system_formed Q"
    and agreement: "systems_agree_on (decode_finite_system P) (decode_finite_system Q)
      (system_definitions (decode_finite_system P))"
    and injective: "inj_on g (fset (finite_system_definitions P))"
    and source_variant: "system_alpha_variant (rename_system g (decode_finite_system P)) N"
begin

abbreviation placement where "placement \<equiv> finite_program_coordinates E (finite_system_definitions P) (finite_system_definitions Q) g"
abbreviation old where "old \<equiv> finite_rename_system placement P"
abbreviation goal where "goal \<equiv> finite_rename_system placement Q"

lemma environment: "finite_environment_formed E"
  using native_package_projection(1)[OF native]
  by (simp add: finite_environment_formed_correct native_package_formed_def)
lemma positions: "image g (fset (finite_system_definitions P))\<subseteq>environment_positions (decode_finite_environment E)"
  by (simp only: finite_system_definitions_correct; rule native_renamed_source_positions[OF native source_variant])

lemma coordinates:
  "inj_on placement (fset (finite_system_definitions Q))"
  "\<forall>d\<in>fset (finite_system_definitions P). placement d=g d"
  "\<forall>d\<in>fset (finite_system_definitions Q)-fset (finite_system_definitions P). snd (placement d)=[]"
  "image fst (image placement (fset (finite_system_definitions Q)-fset (finite_system_definitions P)))\<inter>
    fset (finite_environment_uses E)={}"
  using finite_program_coordinates_properties[OF environment injective positions] by (simp only: Let_def; blast)+

sublocale maps: mapped_extension_coordinates "decode_finite_system P" "decode_finite_system Q" g placement
  by (rule mapped_extension_coordinates.intro)
    (use source target agreement coordinates(1,2) in
      \<open>simp_all only: finite_system_formed_correct finite_system_definitions_correct\<close>)

lemma old_variant: "system_alpha_variant (decode_finite_system old) N"
  by (simp only: finite_rename_system_correct maps.source_equation; rule source_variant)
lemma goal_formed: "finite_system_formed goal"
  by (simp only: finite_system_formed_correct finite_rename_system_correct; rule maps.target_formed)
lemma old_agreement: "systems_agree_on (decode_finite_system old) (decode_finite_system goal)
    (system_definitions (decode_finite_system old))"
  by (simp only: finite_rename_system_correct; rule maps.target_agreement)
lemma new_definitions:
  "fset (finite_system_definitions goal)-fset (finite_system_definitions old)=
    image placement (fset (finite_system_definitions Q)-fset (finite_system_definitions P))"
  by (simp only: finite_system_definitions_correct finite_rename_system_correct; rule maps.additions)
lemma roots: "\<forall>d\<in>fset (finite_system_definitions goal)-fset (finite_system_definitions old). snd d=[]"
  by (simp only: new_definitions; use coordinates(3) in auto)
lemma fresh: "image fst (fset (finite_system_definitions goal)-fset (finite_system_definitions old))\<inter>
    fset (finite_environment_uses E)={}"
  by (simp only: new_definitions; rule coordinates(4))

sublocale installation: finite_native_extension E old goal pu pr N
  by (rule finite_native_extension.intro[OF native old_variant goal_formed old_agreement roots fresh])

theorem total: "\<exists>F u. finite_extend_mapped_native E P Q g=Some (F,u)"
  using installation.total by (simp only: finite_extend_mapped_native_def Let_def)

theorem correct:
  assumes result: "finite_extend_mapped_native E P Q g=Some (F,u)"
  shows "finite_environment_formed F \<and>
    environment_included (decode_finite_environment E) (decode_finite_environment F) \<and>
    native_package_at (decode_finite_environment F) pu pr N \<and>
    inj_on placement (fset (finite_system_definitions Q)) \<and>
    (\<forall>d\<in>fset (finite_system_definitions P). placement d=g d) \<and>
    (\<exists>T. native_package_at (decode_finite_environment F) u [] T \<and>
      system_alpha_variant (rename_system placement (decode_finite_system Q)) T \<and>
      system_definitions T=image placement (fset (finite_system_definitions Q)) \<and>
      positive_meaning T=image (map_prod placement id) (positive_meaning (decode_finite_system Q)) \<and>
      (\<forall>d\<in>fset (finite_system_definitions Q). \<forall>t.
        schema_call_formed T (placement d) t \<longleftrightarrow> schema_call_formed (decode_finite_system Q) d t)) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
      artifact_at (decode_finite_environment F) w A \<longleftrightarrow> artifact_at (decode_finite_environment E) w A) \<and>
    (\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
      binds_slot (decode_finite_environment F) w k v \<longleftrightarrow> binds_slot (decode_finite_environment E) w k v)"
proof -
  have result': "finite_extend_native E old goal=Some (F,u)"
    using result by (simp only: finite_extend_mapped_native_def Let_def)
  have installed: "finite_environment_formed F"
    "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    "native_package_at (decode_finite_environment F) pu pr N"
    "\<exists>T. native_package_at (decode_finite_environment F) u [] T \<and>
      system_definitions T=system_definitions (decode_finite_system goal) \<and>
      system_alpha_variant (decode_finite_system goal) T"
    "\<forall>w\<in>fset (finite_environment_uses E). \<forall>A.
      artifact_at (decode_finite_environment F) w A \<longleftrightarrow> artifact_at (decode_finite_environment E) w A"
    "\<forall>w\<in>fset (finite_environment_uses E). \<forall>k v.
      binds_slot (decode_finite_environment F) w k v \<longleftrightarrow> binds_slot (decode_finite_environment E) w k v"
    using installation.correct[OF result'] by blast+
  obtain T where native: "native_package_at (decode_finite_environment F) u [] T"
    and definitions: "system_definitions T=system_definitions (decode_finite_system goal)"
    and variant: "system_alpha_variant (decode_finite_system goal) T" using installed(4) by blast
  have target_formed: "schema_system_formed (decode_finite_system Q)" using target by (simp only: finite_system_formed_correct)
  have injective: "inj_on placement (system_definitions (decode_finite_system Q))"
    using coordinates(1) by (simp only: finite_system_definitions_correct)
  have variant': "system_alpha_variant (rename_system placement (decode_finite_system Q)) T"
    using variant by (simp only: finite_rename_system_correct)
  have meaning: "positive_meaning T=image (map_prod placement id) (positive_meaning (decode_finite_system Q))"
    using system_alpha_positive_meaning[OF variant'] renamed_system_positive_meaning[OF target_formed injective] by simp
  have calls: "\<forall>d\<in>fset (finite_system_definitions Q). \<forall>t.
    schema_call_formed T (placement d) t \<longleftrightarrow> schema_call_formed (decode_finite_system Q) d t"
    using system_alpha_calls[OF variant'] renamed_system_call[OF target_formed injective]
    by (simp only: finite_system_definitions_correct; blast)
  have target: "\<exists>T. native_package_at (decode_finite_environment F) u [] T \<and>
      system_alpha_variant (rename_system placement (decode_finite_system Q)) T \<and>
      system_definitions T=image placement (fset (finite_system_definitions Q)) \<and>
      positive_meaning T=image (map_prod placement id) (positive_meaning (decode_finite_system Q)) \<and>
      (\<forall>d\<in>fset (finite_system_definitions Q). \<forall>t.
        schema_call_formed T (placement d) t \<longleftrightarrow> schema_call_formed (decode_finite_system Q) d t)"
    by (rule exI[of _ T]) (use native variant' definitions meaning calls in
      \<open>simp only: finite_rename_system_correct renamed_system_definitions finite_system_definitions_correct; blast\<close>)
  show ?thesis using installed(1-3,5,6) coordinates(1,2) target by blast
qed

end

end
