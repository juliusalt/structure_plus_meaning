theory Factor_Finite_Program_Compilation
  imports Factor_Finite_Definition_Compilation Factor_Finite_System_Fields Keyed_Option_Maps Factor_Rooted_Code_Families
begin

section \<open>Compile every selected definition from the complete finite source\<close>

definition finite_compile_system_definition :: "('a::linorder,'s::linorder,local_address option definition_site,'c::linorder)
    finite_schema_system\<Rightarrow>local_address option definition_site\<Rightarrow>finite_definition_code option" where
  "finite_compile_system_definition P d=(case finite_system_interface_option P d of None \<Rightarrow> None
    | Some p \<Rightarrow> finite_compile_definition p (finite_system_clause_family P d))"

definition finite_compile_definitions where
  "finite_compile_definitions P ds=keyed_option_map (finite_compile_system_definition P) ds"

theorem finite_compile_system_definition_correct:
  assumes formed: "finite_system_formed P" and member: "d |\<in>| finite_system_definitions P"
    and result: "finite_compile_system_definition P d=Some K"
  shows "definition_code_for (system_interface (decode_finite_system P) d)
    (system_clause_family (decode_finite_system P) d) (decode_finite_definition_code K)"
proof -
  obtain p where interface: "finite_system_interface_option P d=Some p"
    "decode_finite_pattern p=system_interface (decode_finite_system P) d"
    using finite_system_interface_option_correct[OF formed member] by blast
  have code: "finite_compile_definition p (finite_system_clause_family P d)=Some K"
    using result by (simp add: finite_compile_system_definition_def interface(1))
  show ?thesis using finite_compile_definition_correct[OF code]
    by (simp only: interface(2) finite_system_clause_family_correct)
qed

theorem finite_compile_system_definition_total:
  assumes formed: "finite_system_formed P" and member: "d |\<in>| finite_system_definitions P"
    and addresses: "\<forall>e\<in>system_definitions (decode_finite_system P). octets_formed (snd e)"
  shows "\<exists>K. finite_compile_system_definition P d=Some K"
proof -
  let ?P="decode_finite_system P"
  let ?C="finite_system_clause_family P d"
  have pf: "schema_system_formed ?P" using formed by (simp only: finite_system_formed_correct)
  have source: "d\<in>system_definitions ?P" using member by (simp only: finite_system_definitions_correct)
  obtain p where interface: "finite_system_interface_option P d=Some p"
    "decode_finite_pattern p=system_interface ?P d"
    using finite_system_interface_option_correct[OF formed member] by blast
  have pattern: "finite_pattern_formed p"
    by (simp only: finite_pattern_formed_correct interface(2); rule system_interface_formed[OF pf source])
  have schema_injective: "inj (decode_finite_schema :: ('a,'s,local_address option definition_site) finite_factor_schema\<Rightarrow>_)"
    by (auto simp: inj_def)
  have functional: "finite_relation_functional ?C"
    using system_clause_family_functional[OF pf, of d]
    by (simp only: finite_system_clause_family_correct[symmetric] map_relation_values_functional[OF schema_injective]
      finite_relation_functional_correct)
  have each: "finite_schema_formed S \<and> fBall (finite_schema_dependencies S) (\<lambda>e. octets_formed (snd e))"
    if member: "S\<in>rel_ran (fset ?C)" for S
  proof -
    have schema: "decode_finite_schema S\<in>rel_ran (system_clause_family ?P d)"
      using member by (auto simp: finite_system_clause_family_correct[symmetric] map_relation_values_def rel_ran_def)
    have sf: "schema_formed (decode_finite_schema S)" using system_clause_family_formed[OF pf] schema by blast
    have dependencies: "schema_dependencies (decode_finite_schema S)\<subseteq>system_definitions ?P"
      using system_clause_family_dependencies[OF pf, of d] schema by blast
    show ?thesis using sf dependencies addresses
      by (auto simp: finite_schema_formed_correct finite_schema_dependencies_correct)
  qed
  obtain K where code: "finite_compile_definition p ?C=Some K"
    using finite_compile_definition_total[OF pattern functional] each by blast
  show ?thesis using code by (auto simp: finite_compile_system_definition_def interface(1))
qed

lemma finite_compile_definitions_total:
  assumes formed: "finite_system_formed P" and members: "set ds\<subseteq>fset (finite_system_definitions P)"
    and addresses: "\<forall>e\<in>system_definitions (decode_finite_system P). octets_formed (snd e)"
  shows "\<exists>rows. finite_compile_definitions P ds=Some rows"
proof -
  have each: "\<forall>d\<in>set ds. \<exists>K. finite_compile_system_definition P d=Some K"
    by (intro ballI; rule finite_compile_system_definition_total[OF formed _ addresses]) (use members in blast)
  have defined: "finite_compile_definitions P ds\<noteq>None"
    using each by (auto simp: finite_compile_definitions_def keyed_option_map_domain)
  show ?thesis using defined by (cases "finite_compile_definitions P ds") auto
qed

theorem finite_compile_definitions_correct:
  assumes formed: "finite_system_formed P" and members: "set ds\<subseteq>fset (finite_system_definitions P)"
    and result: "finite_compile_definitions P ds=Some rows"
  shows "map fst rows=ds"
    and "\<forall>d\<in>set ds. definition_code_for (system_interface (decode_finite_system P) d)
      (system_clause_family (decode_finite_system P) d)
      (decode_finite_definition_code (the (map_of rows d)))"
proof -
  have exact: "keyed_option_map (finite_compile_system_definition P) ds=Some rows"
    using result by (simp only: finite_compile_definitions_def)
  show "map fst rows=ds" by (rule keyed_option_map_result(1)[OF exact])
  show "\<forall>d\<in>set ds. definition_code_for (system_interface (decode_finite_system P) d)
      (system_clause_family (decode_finite_system P) d)
      (decode_finite_definition_code (the (map_of rows d)))"
    by (intro ballI; rule finite_compile_system_definition_correct[OF formed _ keyed_option_map_lookup[OF exact]])
      (use members in auto)
qed

export_code finite_compile_system_definition finite_compile_definitions checking SML

end
