theory Native_Control_Guard_Transport
  imports Native_Control_Finite_Guard
begin

locale finite_guard_installation = quoted_judgment_rows xs for xs +
  fixes E F :: "local_address option finite_artifact_environment" and u :: "local_address option"
  assumes environment: "finite_environment_formed E"
    and selected: "finite_select_roots E []=(F,u)"
begin

sublocale closed: closed_program_installation E F u "finite_quoted_judgment xs"
  by (rule closed_program_installation.intro[OF environment selected finite_guard_formed])

abbreviation placement where
  "placement \<equiv> finite_program_coordinates F (finite_system_definitions empty_installation_program)
    (finite_system_definitions (finite_quoted_judgment xs)) (\<lambda>_. (None,[]))"

lemma total:
  "\<exists>K v. finite_extend_mapped_native F empty_installation_program (finite_quoted_judgment xs)
    (\<lambda>_. (None,[]))=Some (K,v)"
  by (rule closed.total)

theorem installed_guard:
  assumes built: "finite_extend_mapped_native F empty_installation_program (finite_quoted_judgment xs)
    (\<lambda>_. (None,[]))=Some (K,v)"
  obtains T where "finite_environment_formed K"
    "environment_included (decode_finite_environment E) (decode_finite_environment K)"
    "native_package_at (decode_finite_environment K) v [] T"
    "inj_on placement (system_definitions artifact_system)"
    "system_alpha_variant (rename_system placement artifact_system) T"
    "\<And>z. (placement 369,z)\<in>positive_meaning T \<longleftrightarrow>
      (\<exists>R r t. z=Target_Term (Whole_Artifact R) \<and> complete_data_quoted_at R r t \<and>
        t\<in>decode_finite_term ` set xs)"
proof -
  obtain T where formed: "finite_environment_formed K"
    and native: "native_package_at (decode_finite_environment K) v [] T"
    and injective: "inj_on placement (fset (finite_system_definitions (finite_quoted_judgment xs)))"
    and variant: "system_alpha_variant (rename_system placement (decode_finite_system (finite_quoted_judgment xs))) T"
    using closed.install.correct[OF built] by blast
  have inj: "inj_on placement (system_definitions artifact_system)"
    using injective by (simp only: finite_system_definitions_correct finite_guard_exact)
  have var: "system_alpha_variant (rename_system placement artifact_system) T"
    using variant by (simp only: finite_guard_exact)
  have meaning: "(placement 369,z)\<in>positive_meaning T \<longleftrightarrow>
      (\<exists>R r t. z=Target_Term (Whole_Artifact R) \<and> complete_data_quoted_at R r t \<and>
        t\<in>decode_finite_term ` set xs)" for z
    using system_variant_renamed_meaning_at[OF artifact_formed inj var artifact_entry, of z]
    by (simp only: artifact_exact)
  show thesis by (rule that[OF formed closed.original_environment_preserved[OF built] native inj var meaning])
qed

corollary installed_guard_body:
  assumes built: "finite_extend_mapped_native F empty_installation_program (finite_quoted_judgment xs)
    (\<lambda>_. (None,[]))=Some (K,v)"
    and package: "native_package_at (decode_finite_environment K) v [] T"
    and quoted: "complete_data_quoted_at R r t"
  shows "(placement 369,Target_Term (Whole_Artifact R))\<in>positive_meaning T
    \<longleftrightarrow> t\<in>decode_finite_term ` set xs"
proof (rule installed_guard[OF built])
  fix S
  assume formed: "finite_environment_formed K"
    and preserved: "environment_included (decode_finite_environment E) (decode_finite_environment K)"
    and native: "native_package_at (decode_finite_environment K) v [] S"
    and inj: "inj_on placement (system_definitions artifact_system)"
    and var: "system_alpha_variant (rename_system placement artifact_system) S"
    and meaning: "\<And>z. (placement 369,z)\<in>positive_meaning S \<longleftrightarrow>
      (\<exists>R r t. z=Target_Term (Whole_Artifact R) \<and> complete_data_quoted_at R r t \<and>
        t\<in>decode_finite_term ` set xs)"
  have same: "T=S" by (rule native_package_unique[OF package native])
  show ?thesis using system_variant_renamed_meaning_at[OF artifact_formed inj var artifact_entry,
    of "Target_Term (Whole_Artifact R)"]
    by (simp only: same artifact_on_complete_body[OF quoted])
qed

end

text \<open>The exact target, injective placement and original native package are
  derived from the actual installation result. This closes those conditional
  transport premises for the supplied formed environment and rows. It does not
  assert that installation has executed or that a certified policy cause exists.\<close>

end
