theory Factor_Program_Compilation
  imports Factor_Program_Semantics Factor_System_Relocation Factor_Root_Environments
begin

section \<open>Native program representation from arbitrary finite source coordinates\<close>

lemma program_coordinates_exist:
  assumes formed: "schema_system_formed P"
  shows "\<exists>g :: 'd \<Rightarrow> local_address option definition_site.
    inj_on g (system_definitions P) \<and> schema_system_formed (rename_system g P) \<and>
    (\<forall>d\<in>system_definitions (rename_system g P). snd d=[])"
proof -
  obtain f where addresses: "finite_addressing (system_definitions P) f"
    using finite_addressing_exists[OF system_definitions_finite[OF formed]] by blast
  let ?g = "\<lambda>d. (Some (f d),[])"
  have injective: "inj_on ?g (system_definitions P)" using addresses by (auto simp: finite_addressing_def inj_on_def)
  have target: "schema_system_formed (rename_system ?g P)" by (rule renamed_system_formed[OF formed injective])
  have roots: "\<forall>d\<in>system_definitions (rename_system ?g P). snd d=[]"
    by (simp only: renamed_system_definitions) auto
  show ?thesis by (rule exI[of _ ?g]) (use injective target roots in blast)
qed

theorem program_native_representation:
  assumes formed: "schema_system_formed P"
  shows "\<exists>g :: 'd \<Rightarrow> local_address option definition_site. \<exists>E.
    inj_on g (system_definitions P) \<and> native_package_formed E (g ` system_definitions P) \<and>
    system_alpha_variant (rename_system g P) (native_program E (g ` system_definitions P)) \<and>
    positive_meaning (native_program E (g ` system_definitions P)) = map_prod g id ` positive_meaning P"
proof -
  obtain g :: "'d \<Rightarrow> local_address option definition_site" where coordinates:
    "inj_on g (system_definitions P)" "schema_system_formed (rename_system g P)"
    "\<forall>d\<in>system_definitions (rename_system g P). snd d=[]"
    using program_coordinates_exist[OF formed] by metis
  obtain E where native: "native_package_formed E (system_definitions (rename_system g P))"
    "system_alpha_variant (rename_system g P) (native_program E (system_definitions (rename_system g P)))"
    using rooted_native_program_variant[OF coordinates(2,3)] by metis
  have meaning: "positive_meaning (native_program E (system_definitions (rename_system g P))) =
    map_prod g id ` positive_meaning P"
    using system_alpha_positive_meaning[OF native(2)] renamed_system_positive_meaning[OF formed coordinates(1)] by simp
  show ?thesis by (rule exI[of _ g], rule exI[of _ E])
    (use coordinates(1) native meaning in \<open>simp only: renamed_system_definitions\<close>)
qed

theorem program_compilation_total:
  assumes formed: "schema_system_formed P"
  shows "\<exists>g :: 'd \<Rightarrow> local_address option definition_site. \<exists>E u Q.
    inj_on g (system_definitions P) \<and> closed_native_package_at E u [] Q \<and>
    native_package_environment E u [] = E \<and>
    system_alpha_variant (rename_system g P) Q \<and>
    positive_meaning Q = map_prod g id ` positive_meaning P"
proof -
  obtain g :: "'d \<Rightarrow> local_address option definition_site" and F where compiled:
    "inj_on g (system_definitions P)" "native_package_formed F (g ` system_definitions P)"
    "system_alpha_variant (rename_system g P) (native_program F (g ` system_definitions P))"
    "positive_meaning (native_program F (g ` system_definitions P)) = map_prod g id ` positive_meaning P"
    using program_native_representation[OF formed] by metis
  let ?Q = "native_program F (g ` system_definitions P)"
  obtain G u where selector: "native_package_at G u [] ?Q"
    using native_dependency_package_selectable[OF compiled(2)] by blast
  let ?E = "native_package_environment G u []"
  have closed: "closed_native_package_at ?E u [] ?Q" by (rule native_package_closed_restriction[OF selector])
  have canonical: "native_package_environment ?E u [] = ?E" by (rule native_package_environment_idempotent[OF selector])
  show ?thesis by (rule exI[of _ g], rule exI[of _ ?E], rule exI[of _ u], rule exI[of _ ?Q])
    (use compiled(1,3,4) closed canonical in blast)
qed

text \<open>
  Every formed finite source system has an actual finite native program with
  exactly corresponding positive meaning. Definition coordinates are chosen
  injectively, and private interface and clause coordinates are handled by
  the compiler. The construction includes recursion and empty systems.
  A structural root selector is constructed, and the grammar-derived dependency
  restriction supplies a closed finite environment retaining the same program.
\<close>

end
