theory Factor_Program_Construction
  imports Factor_System_Clauses Factor_Rooted_Code_Families Factor_Reference_Packages Factor_Native_Program_Variants Factor_Closed_Native_Definitions
begin

section \<open>Compiling every definition before installing recursive references\<close>

theorem rooted_program_code_total:
  fixes P :: "('a,'s,local_address option definition_site,'c) schema_system"
  assumes formed: "schema_system_formed P"
    and roots: "\<forall>d\<in>system_definitions P. snd d = []"
  shows "\<exists>E K. environment_formed E \<and>
    (\<forall>d\<in>system_definitions P.
      definition_code_for (system_interface P d) (system_clause_family P d) (K d) \<and>
      artifact_at E (fst d) (code_artifact (K d)) \<and>
      syntax_references E (fst d) (code_literals (K d)) (code_callees (K d)) \<and>
      native_definition_at E (fst d) (snd d) (code_interface (K d)) (code_clauses (K d)))"
proof -
  have addresses: "\<forall>d\<in>system_definitions P. \<forall>S\<in>rel_ran (system_clause_family P d).
    \<forall>e\<in>schema_dependencies S. octets_formed (snd e)"
  proof (intro ballI)
    fix d S e assume member: "d\<in>system_definitions P"
      and schema: "S\<in>rel_ran (system_clause_family P d)" and callee: "e\<in>schema_dependencies S"
    have target: "e\<in>system_definitions P"
      using system_clause_family_dependencies[OF formed, of d] schema callee by blast
    have empty: "snd e=[]" using roots target by blast
    show "octets_formed (snd e)" by (simp add: empty octets_formed_def)
  qed
  obtain K where codes: "\<forall>d\<in>system_definitions P.
    definition_code_for (system_interface P d) (system_clause_family P d) (K d)"
    using definition_codes_on[OF formed subset_refl addresses] by blast
  interpret family: rooted_code_family P "system_definitions P" K
    by (rule rooted_code_family.intro[OF formed subset_refl roots codes])
  have callees: "\<forall>u\<in>family.uses. \<forall>d\<in>rel_ran (family.callees u).
    fst d\<in>family.uses \<and> snd d\<in>rra_carrier (object_structure (family.artifacts (fst d)))"
    using family.callee_source family.internal_anchor by blast
  obtain E where built: "environment_formed E"
    "\<forall>u\<in>family.uses. artifact_at E u (family.artifacts u) \<and>
      syntax_references E u (family.literals u) (family.callees u)"
    using preallocated_reference_environment[OF family.finite_uses family.artifact_formation
      family.profiles family.bounds callees] by blast
  show ?thesis by (rule exI[of _ E], rule exI[of _ K])
    (use built(1) family.installed[OF built] in blast)
qed

section \<open>Complete recovered definition families form closed program dependencies\<close>

theorem rooted_native_program_total:
  fixes P :: "('a,'s,local_address option definition_site,'c) schema_system"
  assumes formed: "schema_system_formed P" and roots: "\<forall>d\<in>system_definitions P. snd d = []"
  shows "\<exists>E K. native_package_formed E (system_definitions P) \<and>
    native_definition_sites E (system_definitions P) = system_definitions P \<and>
    (\<forall>d\<in>system_definitions P.
      definition_code_for (system_interface P d) (system_clause_family P d) (K d) \<and>
      native_definition_at E (fst d) (snd d) (code_interface (K d)) (code_clauses (K d)))"
proof -
  obtain E K where built: "environment_formed E"
    "\<forall>d\<in>system_definitions P.
      definition_code_for (system_interface P d) (system_clause_family P d) (K d) \<and>
      artifact_at E (fst d) (code_artifact (K d)) \<and>
      syntax_references E (fst d) (code_literals (K d)) (code_callees (K d)) \<and>
      native_definition_at E (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))"
    using rooted_program_code_total[OF formed roots] by metis
  have definitions: "\<forall>d\<in>system_definitions P.
    native_definition_at E (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))" using built(2) by blast
  have closed: "\<forall>d\<in>system_definitions P.
    (\<Union>S\<in>rel_ran (code_clauses (K d)). schema_dependencies S) \<subseteq> system_definitions P"
  proof (intro ballI)
    fix d assume member: "d \<in> system_definitions P"
    have code: "definition_code_for (system_interface P d) (system_clause_family P d) (K d)" using built(2) member by blast
    show "(\<Union>S\<in>rel_ran (code_clauses (K d)). schema_dependencies S) \<subseteq> system_definitions P"
      by (rule definition_code_source_dependencies[OF formed code])
  qed
  show ?thesis by (rule exI[of _ E], rule exI[of _ K])
    (use built(2) native_complete_definition_family[OF built(1) definitions closed] in blast)
qed

theorem rooted_native_program_variant:
  fixes P :: "('a,'s,local_address option definition_site,'c) schema_system"
  assumes formed: "schema_system_formed P" and roots: "\<forall>d\<in>system_definitions P. snd d = []"
  shows "\<exists>E. native_package_formed E (system_definitions P) \<and>
    system_alpha_variant P (native_program E (system_definitions P))"
proof -
  obtain E K where built: "native_package_formed E (system_definitions P)"
    "native_definition_sites E (system_definitions P) = system_definitions P"
    "\<forall>d\<in>system_definitions P.
      definition_code_for (system_interface P d) (system_clause_family P d) (K d) \<and>
      native_definition_at E (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))"
    using rooted_native_program_total[OF formed roots] by metis
  have readings: "\<exists>p C f h. native_definition_at E (fst d) (snd d) p C \<and>
    inj_on f (pattern_variables (system_interface P d)) \<and> p=rename_pattern f (system_interface P d) \<and>
    schema_family_variant h (system_clause_family P d) C" if "d\<in>system_definitions P" for d
    using built(3) that definition_code_properties(4) by blast
  have variant: "system_alpha_variant P (native_program E (system_definitions P))"
  proof (rule native_program_variant_from_readings[OF formed built(1) sym[OF built(2)]])
    fix d assume member: "d\<in>system_definitions P"
    show "\<exists>p C f h. native_definition_at E (fst d) (snd d) p C \<and>
      inj_on f (pattern_variables (system_interface P d)) \<and> p=rename_pattern f (system_interface P d) \<and>
      schema_family_variant h (system_clause_family P d) C" by (rule readings[OF member])
  qed
  show ?thesis using built(1) variant by blast
qed

text \<open>
  An arbitrary finite formed source system whose definitions use distinct
  empty-root sites receives all of its code artifacts and references together.
  No acyclicity assumption is used. Every recovered definition is the compiled
  source definition, and following all recovered callees reaches exactly the
  complete source definition set. Root selection syntax and relocation from
  arbitrary source definition coordinates are separate construction steps.
\<close>

end
