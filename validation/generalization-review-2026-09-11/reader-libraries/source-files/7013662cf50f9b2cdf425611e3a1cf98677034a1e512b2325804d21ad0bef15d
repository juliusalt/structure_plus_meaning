theory Factor_Program_Construction
  imports Factor_System_Clauses Factor_Definition_Code Factor_Reference_Packages Factor_Packages
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
  have each: "\<forall>d\<in>system_definitions P.
    \<exists>K. definition_code_for (system_interface P d) (system_clause_family P d) K"
  proof (intro ballI)
    fix d assume member: "d \<in> system_definitions P"
    have pf: "pattern_formed (system_interface P d)" by (rule system_interface_formed[OF formed member])
    have bound: "(\<Union>S\<in>rel_ran (system_clause_family P d). schema_dependencies S) \<subseteq> system_definitions P"
      by (rule system_clause_family_dependencies[OF formed])
    have addresses: "\<forall>S\<in>rel_ran (system_clause_family P d). \<forall>e\<in>schema_dependencies S. octets_formed (snd e)"
    proof (intro ballI)
      fix S e assume clause: "S \<in> rel_ran (system_clause_family P d)" and dependency: "e \<in> schema_dependencies S"
      have member: "e \<in> system_definitions P" using bound clause dependency by blast
      have empty: "snd e=[]" using roots member by blast
      show "octets_formed (snd e)" by (simp add: empty octets_formed_def)
    qed
    show "\<exists>K. definition_code_for (system_interface P d) (system_clause_family P d) K"
      by (rule definition_code_total[OF pf system_clause_family_finite[OF formed]
          system_clause_family_functional[OF formed] system_clause_family_formed[OF formed] addresses])
  qed
  obtain K :: "local_address option definition_site \<Rightarrow> definition_code" where codes:
    "\<forall>d\<in>system_definitions P. definition_code_for (system_interface P d) (system_clause_family P d) (K d)"
    using bchoice[OF each] by blast
  let ?U = "fst ` system_definitions P"
  let ?R = "\<lambda>u. code_artifact (K (u,[]))"
  let ?L = "\<lambda>u. code_literals (K (u,[]))"
  let ?C = "\<lambda>u. code_callees (K (u,[]))"
  have fin: "finite ?U" using system_definitions_finite[OF formed] by simp
  have site_shape: "\<And>d. d \<in> system_definitions P \<Longrightarrow> (fst d,[]) = d"
  proof -
    fix d assume member: "d \<in> system_definitions P"
    have empty: "snd d=[]" using roots member by blast
    show "(fst d,[]) = d" using empty by (cases d) simp
  qed
  have use_site: "\<forall>u\<in>?U. (u,[]) \<in> system_definitions P"
  proof (intro ballI)
    fix u assume member: "u \<in> ?U"
    obtain d where old: "d \<in> system_definitions P" "u=fst d" using member by blast
    show "(u,[]) \<in> system_definitions P" using old site_shape[OF old(1)] by simp
  qed
  have use_codes: "\<forall>u\<in>?U. definition_code_for (system_interface P (u,[])) (system_clause_family P (u,[])) (K (u,[]))"
    using codes use_site by blast
  have artifacts: "\<forall>u\<in>?U. exact_formed (?R u)" using use_codes definition_code_properties(1) by blast
  have profiles: "\<forall>u\<in>?U. reference_table_formed (?L u) (?C u)" using use_codes definition_code_properties(5) by blast
  have bounds: "\<forall>u\<in>?U. rel_dom (?L u) \<union> rel_dom (?C u) \<subseteq> rra_carrier (object_structure (?R u))"
    using use_codes definition_code_properties(6) by blast
  have callees: "\<forall>u\<in>?U. \<forall>d\<in>rel_ran (?C u).
    fst d \<in> ?U \<and> snd d \<in> rra_carrier (object_structure (?R (fst d)))"
  proof (intro ballI)
    fix u d assume member: "u \<in> ?U" and dependency: "d \<in> rel_ran (?C u)"
    have code: "definition_code_for (system_interface P (u,[])) (system_clause_family P (u,[])) (K (u,[]))"
      using use_codes member by blast
    have inside: "d \<in> system_definitions P"
      using dependency definition_code_properties(7)[OF code] system_clause_family_dependencies[OF formed, of "(u,[])"] by blast
    have target_code: "definition_code_for (system_interface P d) (system_clause_family P d) (K d)"
      using codes inside by blast
    have target_use: "fst d \<in> ?U" by (rule imageI[OF inside])
    have root: "[] \<in> rra_carrier (object_structure (code_artifact (K d)))"
      by (rule definition_code_properties(3)[OF target_code])
    have shape: "(fst d,[]) = d" by (rule site_shape[OF inside])
    have empty: "snd d=[]" using roots inside by blast
    show "fst d \<in> ?U \<and> snd d \<in> rra_carrier (object_structure (?R (fst d)))"
      using target_use root shape empty by simp
  qed
  obtain E where built: "environment_formed E"
    "\<forall>u\<in>?U. artifact_at E u (?R u) \<and> syntax_references E u (?L u) (?C u)"
    using preallocated_reference_environment[OF fin artifacts profiles bounds callees] by metis
  have result: "\<forall>d\<in>system_definitions P.
    definition_code_for (system_interface P d) (system_clause_family P d) (K d) \<and>
    artifact_at E (fst d) (code_artifact (K d)) \<and>
    syntax_references E (fst d) (code_literals (K d)) (code_callees (K d)) \<and>
    native_definition_at E (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))"
  proof (intro ballI)
    fix d assume member: "d \<in> system_definitions P"
    have code: "definition_code_for (system_interface P d) (system_clause_family P d) (K d)" using codes member by blast
    have use: "fst d \<in> ?U" by (rule imageI[OF member])
    have shape: "(fst d,[]) = d" by (rule site_shape[OF member])
    have row: "artifact_at E (fst d) (?R (fst d)) \<and> syntax_references E (fst d) (?L (fst d)) (?C (fst d))"
      using built(2) use by blast
    have source: "artifact_at E (fst d) (code_artifact (K d))"
      and refs: "syntax_references E (fst d) (code_literals (K d)) (code_callees (K d))"
      using row shape by simp_all
    have native: "native_definition_at E (fst d) [] (code_interface (K d)) (code_clauses (K d))"
      using definition_code_properties(8)[OF code] built(1) source refs by blast
    show "definition_code_for (system_interface P d) (system_clause_family P d) (K d) \<and>
      artifact_at E (fst d) (code_artifact (K d)) \<and>
      syntax_references E (fst d) (code_literals (K d)) (code_callees (K d)) \<and>
      native_definition_at E (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))"
      using code source refs native roots member by simp
  qed
  show ?thesis by (rule exI[of _ E], rule exI[of _ K]) (use built(1) result in blast)
qed

section \<open>Complete recovered definition families form closed program dependencies\<close>

lemma native_complete_definition_family:
  assumes ef: "environment_formed E"
    and definitions: "\<forall>d\<in>D. native_definition_at E (fst d) (snd d) (p d) (Cs d)"
    and closed: "\<forall>d\<in>D. (\<Union>S\<in>rel_ran (Cs d). schema_dependencies S) \<subseteq> D"
  shows "native_definition_sites E D = D" "native_package_formed E D"
proof -
  have steps: "\<And>d e. d \<in> D \<Longrightarrow> (d,e) \<in> native_definition_edges E \<Longrightarrow> e \<in> D"
  proof -
    fix d e assume member: "d \<in> D" and edge: "(d,e) \<in> native_definition_edges E"
    obtain q C c S where other: "native_definition_at E (fst d) (snd d) q C" "(c,S) \<in> C" "e \<in> schema_dependencies S"
      using edge unfolding native_definition_edges_def by blast
    have original: "native_definition_at E (fst d) (snd d) (p d) (Cs d)" using definitions member by blast
    have same: "C=Cs d" using native_definition_unique[OF other(1) original] by blast
    have source: "S \<in> rel_ran (Cs d)" using other(2) same by (auto simp: rel_ran_def)
    show "e \<in> D" using closed member source other(3) by blast
  qed
  have subset: "native_definition_sites E D \<subseteq> D" by (rule native_definition_sites_least[OF _ steps]) simp
  show sites: "native_definition_sites E D = D" using subset native_definition_roots[of D E] by blast
  show "native_package_formed E D" using ef definitions sites by (auto simp: native_package_formed_def)
qed

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
      using definition_code_dependencies[OF code] definition_code_properties(7)[OF code]
        system_clause_family_dependencies[OF formed, of d] by simp
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
  let ?Q = "native_program E (system_definitions P)"
  have qf: "schema_system_formed ?Q" by (rule native_program_formed[OF built(1)])
  have defs: "system_definitions P = system_definitions ?Q"
    using native_program_definitions[OF built(1)] built(2) by simp
  have fields: "\<forall>d\<in>system_definitions P. \<exists>f h.
    inj_on f (pattern_variables (system_interface P d)) \<and>
    system_interface ?Q d = rename_pattern f (system_interface P d) \<and>
    schema_family_variant h (system_clause_family P d) (system_clause_family ?Q d)"
  proof (intro ballI)
    fix d assume member: "d \<in> system_definitions P"
    have code: "definition_code_for (system_interface P d) (system_clause_family P d) (K d)"
      and read: "native_definition_at E (fst d) (snd d) (code_interface (K d)) (code_clauses (K d))"
      using built(3) member by blast+
    have site: "d \<in> native_definition_sites E (system_definitions P)" using built(2) member by simp
    have interface_entry: "(d,code_interface (K d)) \<in> system_interfaces ?Q"
      by (simp only: native_program_complete_at(1)[OF site read])
    have interface: "system_interface ?Q d = code_interface (K d)"
      by (rule system_interface_unique[OF qf interface_entry])
    have family: "system_clause_family ?Q d = code_clauses (K d)"
    proof (rule set_eqI)
      fix x :: "local_address \<times> local_address option native_schema"
      obtain c S where shape: "x=(c,S)" by (cases x)
      show "x \<in> system_clause_family ?Q d \<longleftrightarrow> x \<in> code_clauses (K d)"
        by (simp only: shape system_clause_member native_program_complete_at(2)[OF site read])
    qed
    show "\<exists>f h. inj_on f (pattern_variables (system_interface P d)) \<and>
      system_interface ?Q d = rename_pattern f (system_interface P d) \<and>
      schema_family_variant h (system_clause_family P d) (system_clause_family ?Q d)"
      using definition_code_properties(4)[OF code] interface family by simp
  qed
  have variant: "system_alpha_variant P ?Q" using formed qf defs fields by (simp add: system_alpha_variant_def)
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
