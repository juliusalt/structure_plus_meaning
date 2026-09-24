theory Factor_Finite_Closed_Installation
  imports Factor_Finite_Root_Environments Factor_Finite_Mapped_Extensions
begin

section \<open>A whole program installed as the extension of the empty program\<close>

text \<open>
  A complete finite program is installed as an extension of the empty program over an environment whose
  empty package is actually selected and read. The mapped native extension then supplies the whole
  target's placement, compilation, installation and root selection, and its correctness the exact
  package, the injective placement, the alpha variant and the preservation of old material. Moved here
  from \<open>Native_Control_Closed_Installation\<close>, polymorphic in the program's coordinates (task 342).
\<close>

definition finite_empty_environment :: "'u finite_artifact_environment" where
  "finite_empty_environment=\<lparr>finite_environment_artifacts={||},finite_environment_bindings={||}\<rparr>"

lemma finite_empty_environment_formed [simp]: "finite_environment_formed finite_empty_environment"
  by (simp add: finite_empty_environment_def finite_environment_formed_def finite_relation_functional_def)

definition empty_installation_program :: "('a::linorder,'s::linorder,'d::linorder,'c::linorder) finite_schema_system" where
  "empty_installation_program=\<lparr>finite_system_interfaces={||},finite_system_clauses={||}\<rparr>"

lemma empty_installation_formed [simp]: "finite_system_formed empty_installation_program"
  by (simp add: empty_installation_program_def finite_system_formed_def finite_relation_functional_def)

lemma empty_installation_definitions [simp]: "finite_system_definitions empty_installation_program={||}"
  by (simp add: empty_installation_program_def finite_system_definitions_def)

lemma empty_native_program:
  "native_program E {}=\<lparr>system_interfaces={},system_clauses={}\<rparr>"
  by (auto simp: native_program_def native_definition_graph_def native_definition_sites_def)

lemma selected_empty_package:
  assumes formed: "finite_environment_formed E"
    and selected: "finite_select_roots E []=(F,u)"
  shows "native_package_at (decode_finite_environment F) u []
    (\<lparr>system_interfaces={},system_clauses={}\<rparr>)"
proof -
  have targets: "set []\<subseteq>environment_positions (decode_finite_environment E)" by simp
  have ff: "finite_environment_formed F"
    and roots: "native_root_family_at (decode_finite_environment F) u [] {}"
    using finite_select_roots_correct[OF formed targets selected] by simp_all
  have package: "native_package_formed (decode_finite_environment F) {}"
    using ff by (simp add: native_package_formed_def native_definition_sites_def
      finite_environment_formed_correct)
  show ?thesis unfolding native_package_at_def
    by (rule exI[of _ "{}"]) (use roots package in \<open>simp add: empty_native_program\<close>)
qed

locale closed_program_installation =
  fixes E F :: "local_address option finite_artifact_environment" and u :: "local_address option"
    and Q :: "('a::linorder,'s::linorder,'d::linorder,'c::linorder) finite_schema_system"
  assumes environment: "finite_environment_formed E"
    and selected: "finite_select_roots E []=(F,u)"
    and target: "finite_system_formed Q"
begin

sublocale install: finite_mapped_native_extension F empty_installation_program Q u "[]"
    "\<lparr>system_interfaces={},system_clauses={}\<rparr>" "\<lambda>_. (None,[])"
proof (rule finite_mapped_native_extension.intro[OF selected_empty_package[OF environment selected]
    empty_installation_formed target])
  show "systems_agree_on (decode_finite_system empty_installation_program) (decode_finite_system Q)
      (system_definitions (decode_finite_system empty_installation_program))"
    by (simp add: empty_installation_program_def decode_finite_system_def
      system_definitions_def map_relation_values_def rel_dom_def systems_agree_on_def)
  show "inj_on (\<lambda>_. (None,[])) (fset (finite_system_definitions empty_installation_program))" by simp
  show "system_alpha_variant (rename_system (\<lambda>_. (None,[])) (decode_finite_system empty_installation_program))
      \<lparr>system_interfaces={},system_clauses={}\<rparr>"
    by (simp add: empty_installation_program_def decode_finite_system_def rename_system_def
      map_relation_values_def system_alpha_variant_def schema_system_formed_def system_definitions_def
      rel_dom_def single_valued_def)
qed

lemma total:
  "\<exists>K v. finite_extend_mapped_native F empty_installation_program Q (\<lambda>_. (None,[]))=Some (K,v)"
  by (rule install.total)

theorem original_environment_preserved:
  assumes built: "finite_extend_mapped_native F empty_installation_program Q (\<lambda>_. (None,[]))=Some (K,v)"
  shows "environment_included (decode_finite_environment E) (decode_finite_environment K)"
proof -
  have first: "environment_included (decode_finite_environment E) (decode_finite_environment F)"
    by (rule finite_select_roots_correct(2)[OF environment _ selected]) simp
  have second: "environment_included (decode_finite_environment F) (decode_finite_environment K)"
    using install.correct[OF built] by blast
  show ?thesis by (rule environment_included_trans[OF first second])
qed

text \<open>The original formed environment is preserved. The empty package is
  actually constructed and read; it is not an unsupported assumed program.
  The complete target still needs its actual finite representation and
  formation. The inherited install.correct supplies the exact package,
  injective placement, full alpha variant and all old-binding preservation.\<close>

end

end
