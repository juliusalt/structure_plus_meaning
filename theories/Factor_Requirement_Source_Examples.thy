theory Factor_Requirement_Source_Examples
  imports Factor_Requirement_Source_Readings Factor_Requirement_Packages Factor_Selected_Definition_Graphs
begin

section \<open>Complete native packages are recovered from the executed source artifacts\<close>

definition finite_guard_source_program :: "bool \<Rightarrow> local_address option finite_native_system" where
  "finite_guard_source_program b=\<lparr>
    finite_system_interfaces={|((None,[Suc 0]),Finite_Variable [4])|},
    finite_system_clauses={|(((None,[Suc 0]),[7]),if b then finite_variable_schema else finite_equality_schema)|}\<rparr>"

definition finite_guard_program :: "bool \<Rightarrow> local_address option finite_native_system" where
  "finite_guard_program b=\<lparr>
    finite_system_interfaces={|((None,[Suc 0]),Finite_Variable [4]),((Some [Suc 0],[Suc 0]),Finite_Variable [4])|},
    finite_system_clauses={|(((None,[Suc 0]),[7]),if b then finite_variable_schema else finite_equality_schema),
      (((Some [Suc 0],[Suc 0]),[7]),finite_guard_schema)|}\<rparr>"

lemma finite_guard_source_included:
  "environment_included (decode_finite_environment (finite_guard_source b))
    (decode_finite_environment (finite_guard_environment b))"
  by (auto simp: finite_guard_source_def finite_guard_environment_def environment_included_def map_relation_values_def)

lemma finite_guard_source_dependencies [simp]:
  "schema_dependencies (decode_finite_schema finite_variable_schema)={}"
  "schema_dependencies (decode_finite_schema finite_equality_schema)={}"
  by (simp add: finite_variable_schema_def finite_equality_schema_def schema_dependencies_def rel_ran_def)+

lemma finite_guard_source_choice_dependencies [simp]:
  "schema_dependencies (decode_finite_schema (if b then finite_variable_schema else finite_equality_schema))={}"
  by (cases b) simp_all

lemma finite_guard_dependencies [simp]:
  "schema_dependencies (decode_finite_schema finite_guard_schema)={(None,[Suc 0])}"
  by (auto simp: finite_guard_schema_def finite_variable_schema_def schema_dependencies_def rel_ran_def map_relation_values_def)

lemma finite_guard_source_package:
  "native_package_at (decode_finite_environment (finite_guard_source b)) None [0]
    (decode_finite_system (finite_guard_source_program b))"
proof -
  let ?E="decode_finite_environment (finite_guard_source b)"
  let ?S="decode_finite_schema (if b then finite_variable_schema else finite_equality_schema)"
  let ?G="{((None,[Suc 0]),Pattern_Variable [4],{([7],?S)})}
    ::(local_address option definition_site \<times> local_address term_pattern \<times>
      (local_address \<times> local_address option native_schema) set) set"
  have ef: "environment_formed ?E" using finite_guard_environments_formed(1)[where b=b]
    by (simp only: finite_environment_formed_correct)
  have domain: "rel_dom ?G={(None,[Suc 0])}" by (auto simp: rel_dom_def)
  have reads: "native_definition_at ?E (fst d) (snd d) p C" if "(d,p,C)\<in>?G" for d p C
    using that finite_source_definition[where b=b] by auto
  have closed: "schema_dependencies S\<subseteq>rel_dom ?G" if "(d,p,C)\<in>?G" "(c,S)\<in>C" for d p C c S
    using that by auto
  have graph: "native_package_formed ?E {(None,[Suc 0])}" "native_definition_graph ?E {(None,[Suc 0])}=?G"
    using native_closed_definition_graph(2,3)[OF ef reads closed] by (simp_all only: domain)
  have program: "native_program ?E {(None,[Suc 0])}=decode_finite_system (finite_guard_source_program b)"
    by (simp only: native_program_def graph(2);
      auto simp: finite_guard_source_program_def decode_finite_system_def map_relation_values_def)
  have roots: "native_root_family_at ?E None [0] {([16],(None,[Suc 0]))}"
    using finite_guard_source_roots[where b=b] by simp
  show ?thesis unfolding native_package_at_def
    by (rule exI[of _ "{([16],(None,[Suc 0]))}"]) (use roots graph(1) program in \<open>auto simp: rel_ran_def\<close>)
qed

lemma finite_guard_package:
  "native_package_at (decode_finite_environment (finite_guard_environment b)) (Some [Suc 0]) [0]
    (decode_finite_system (finite_guard_program b))"
proof -
  let ?E="decode_finite_environment (finite_guard_environment b)"
  let ?S="decode_finite_schema (if b then finite_variable_schema else finite_equality_schema)"
  let ?T="decode_finite_schema finite_guard_schema"
  let ?k="(None,[Suc 0])" let ?g="(Some [Suc 0],[Suc 0])"
  let ?G="{(?k,Pattern_Variable [4],{([7],?S)}),(?g,Pattern_Variable [4],{([7],?T)})}
    ::(local_address option definition_site \<times> local_address term_pattern \<times>
      (local_address \<times> local_address option native_schema) set) set"
  have ef: "environment_formed ?E" using finite_guard_environments_formed(2)[where b=b]
    by (simp only: finite_environment_formed_correct)
  have old: "native_definition_at ?E None [Suc 0] (Pattern_Variable [4]) {([7],?S)}"
    using native_definition_included[OF finite_source_definition[where b=b]
      finite_guard_source_included[where b=b] ef] by simp
  have raw: "native_definition_at ?E (Some [Suc 0]) [Suc 0] (Pattern_Variable [4]) {([7],?T)}"
    using finite_guard_raw_definition[where b=b] by simp
  have domain: "rel_dom ?G={?k,?g}" by (auto simp: rel_dom_def)
  have reads: "native_definition_at ?E (fst d) (snd d) p C" if "(d,p,C)\<in>?G" for d p C
    using that old raw by auto
  have closed: "schema_dependencies S\<subseteq>rel_dom ?G" if "(d,p,C)\<in>?G" "(c,S)\<in>C" for d p C c S
    using that by (auto simp: domain)
  have start: "?g\<in>native_definition_sites ?E {?g}" using native_definition_roots[of "{?g}" ?E] by auto
  have edge: "(?g,?k)\<in>native_definition_edges ?E"
    by (simp only: native_definition_edges_at[OF raw]; auto)
  have reached: "?k\<in>native_definition_sites ?E {?g}" by (rule native_definition_step[OF start edge])
  have roots_inside: "{?g}\<subseteq>rel_dom ?G" by (simp add: domain)
  have coverage: "rel_dom ?G\<subseteq>native_definition_sites ?E {?g}" using start reached by (simp add: domain)
  have package: "native_package_formed ?E {?g}"
    by (rule native_selected_definition_graph(2)[OF ef reads closed roots_inside coverage])
  have graph: "native_definition_graph ?E {?g}=?G"
    by (rule native_selected_definition_graph(3)[OF ef reads closed roots_inside coverage])
  have program: "native_program ?E {?g}=decode_finite_system (finite_guard_program b)"
    by (simp only: native_program_def graph;
      auto simp: finite_guard_program_def decode_finite_system_def map_relation_values_def)
  have roots: "native_root_family_at ?E (Some [Suc 0]) [0] {([16],?g)}"
    using finite_guard_roots[where b=b] by simp
  show ?thesis unfolding native_package_at_def
    by (rule exI[of _ "{([16],?g)}"]) (use roots package program in \<open>auto simp: rel_ran_def\<close>)
qed

lemma finite_guard_definition:
  "native_single_clause_at (decode_finite_environment (finite_guard_environment b)) (Some [Suc 0]) [Suc 0]
    (decode_finite_schema finite_guard_schema)"
  using finite_guard_raw_definition[where b=b] by (auto simp: native_single_clause_at_def)

lemma finite_variable_definition:
  "native_single_clause_at (decode_finite_environment (finite_guard_source True)) None [Suc 0]
    (decode_finite_schema finite_variable_schema)"
  using finite_source_definition[where b=True] by (auto simp: native_single_clause_at_def)

lemma finite_guard_source_definitions [simp]:
  "system_definitions (decode_finite_system (finite_guard_source_program b))={(None,[Suc 0])}"
  by (auto simp: finite_guard_source_program_def system_definitions_def rel_dom_def map_relation_values_def)

lemma finite_guard_definitions [simp]:
  "system_definitions (decode_finite_system (finite_guard_program b))={(None,[Suc 0]),(Some [Suc 0],[Suc 0])}"
  by (auto simp: finite_guard_program_def system_definitions_def rel_dom_def map_relation_values_def)

section \<open>The same guard calls different meanings at the same actual source site\<close>

lemma finite_variable_requirement_schema:
  "schema_alpha_variant (requirement_guard_schema ({}::(nat\<times>local_address option definition_site) set))
    (decode_finite_schema finite_variable_schema)"
  unfolding schema_alpha_variant_def
  by (rule exI[of _ "\<lambda>_. [10]"], rule exI[of _ "\<lambda>_. [26]"])
    (auto simp: finite_variable_schema_def finite_equality_schema_def decode_finite_schema_def
      requirement_guard_schema_def schema_variables_def schema_sockets_def rel_dom_def rename_schema_def map_socket_graph_def map_relation_values_def)

lemma finite_guard_requirement_schema:
  "schema_alpha_variant (requirement_guard_schema {(0::nat,(None,[Suc 0]))})
    (decode_finite_schema finite_guard_schema)"
  unfolding schema_alpha_variant_def
  by (rule exI[of _ "\<lambda>_. [10]"], rule exI[of _ "\<lambda>_. [26]"])
    (auto simp: finite_guard_schema_def finite_variable_schema_def finite_equality_schema_def decode_finite_schema_def
      requirement_guard_schema_def schema_variables_def schema_sockets_def rel_dom_def rename_schema_def map_socket_graph_def map_relation_values_def)

theorem finite_guard_source_meaning:
  "((None,[Suc 0]),t)\<in>positive_meaning (decode_finite_system (finite_guard_source_program b)) \<longleftrightarrow>
    (if b then term_formed t else (\<exists>x. term_formed x \<and> t=Pair_Term x x))"
proof (cases b)
  case False
  have same: "decode_finite_system (finite_guard_source_program False)=native_equality_program"
    by (simp add: finite_guard_source_program_def native_equality_program_def decode_finite_system_def
      finite_equality_schema_correct map_relation_values_def)
  show ?thesis using native_equality_exact[of t] by (simp only: False same; simp)
next
  case True
  have member: "(None,[Suc 0])\<in>system_definitions (decode_finite_system (finite_guard_source_program True))" by simp
  have read: "native_single_clause_at (decode_finite_environment (finite_guard_source True))
      (fst (None,[Suc 0])) (snd (None,[Suc 0])) (decode_finite_schema finite_variable_schema)"
    using finite_variable_definition by simp
  have actual: "((None,[Suc 0]),t)\<in>positive_meaning (decode_finite_system (finite_guard_source_program True))
      \<longleftrightarrow> term_formed t \<and>
        (\<forall>(s,k)\<in>({}::(nat\<times>local_address option definition_site) set).
          (k,t)\<in>positive_meaning (decode_finite_system (finite_guard_source_program True)))"
    by (rule native_requirement_meaning[OF finite_guard_source_package[where b=True] _
        finite_guard_source_package[where b=True] member read finite_variable_requirement_schema])
      (auto simp: environment_included_def single_valued_def rel_ran_def)
  show ?thesis using actual by (simp only: True; simp)
qed

theorem finite_guard_program_meaning:
  "((Some [Suc 0],[Suc 0]),t)\<in>positive_meaning (decode_finite_system (finite_guard_program b)) \<longleftrightarrow>
    (if b then term_formed t else (\<exists>x. term_formed x \<and> t=Pair_Term x x))"
proof -
  have member: "(Some [Suc 0],[Suc 0])\<in>system_definitions (decode_finite_system (finite_guard_program b))" by simp
  have read: "native_single_clause_at (decode_finite_environment (finite_guard_environment b))
      (fst (Some [Suc 0],[Suc 0])) (snd (Some [Suc 0],[Suc 0])) (decode_finite_schema finite_guard_schema)"
    using finite_guard_definition by simp
  have actual: "((Some [Suc 0],[Suc 0]),t)\<in>positive_meaning (decode_finite_system (finite_guard_program b)) \<longleftrightarrow>
      term_formed t \<and> (\<forall>(s,k)\<in>{(0::nat,(None,[Suc 0]))}.
        (k,t)\<in>positive_meaning (decode_finite_system (finite_guard_source_program b)))"
    by (rule native_requirement_meaning[OF finite_guard_source_package finite_guard_source_included
        finite_guard_package member read finite_guard_requirement_schema])
      (auto simp: single_valued_def rel_ran_def)
  show ?thesis by (simp only: actual; auto simp: finite_guard_source_meaning split: if_splits)
qed

definition native_guard_source_meaning_report where
  "native_guard_source_meaning_report b=(
    sorted_list_of_set (system_definitions (decode_finite_system (finite_guard_program b))),
    ((Some [Suc 0],[Suc 0]),Payload_Term [])\<in>positive_meaning (decode_finite_system (finite_guard_program b)))"

lemma native_guard_source_meaning_report_code [code]:
  "native_guard_source_meaning_report b=([(None,[Suc 0]),(Some [Suc 0],[Suc 0])],b)"
  by (simp add: native_guard_source_meaning_report_def finite_guard_program_meaning octets_formed_def)

export_code native_guard_source_meaning_report integer_of_nat
  in SML module_name Native_Guard_Source_Meaning file_prefix native_guard_source_meaning

text \<open>
  Complete native package recovery fixes both original source programs and
  both installed programs. Their domains are equal, and the installed guard
  schema is identical. Nevertheless, its meaning on the same empty payload
  changes with the actual source clause. The source-retaining native checker
  rejects that replacement under the original declared source.
\<close>

end
