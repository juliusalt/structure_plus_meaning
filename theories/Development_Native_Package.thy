theory Development_Native_Package
  imports Development_Package_Program Factor_Finite_Closed_Installation Factor_Definition_Closure
    Factor_Program_Scopes Factor_Executable_Dependencies Keyed_Demanded_Sites
begin

text \<open>
  The development's native package (task 342, N2b of DECISIONS.md "Problems about native definitions are posed,
  answered and judged at the development package's rows"): the joined program of \<open>Development_Package_Program\<close>
  compiled once by the executable compiler into one closed native package, kept, whose root family selects
  the entries the loop calls, one or more per notion. Every contract of a notion holds at its entry of the
  package by one transport through the join and the compilation.
\<close>

section \<open>Dependency edges under renaming and alpha variation\<close>

lemma renamed_dependency_edge:
  assumes "(d,e)\<in>system_dependency_edges P"
  shows "(g d,g e)\<in>system_dependency_edges (rename_system g P)"
proof -
  obtain c S where clause: "((d,c),S)\<in>system_clauses P" and dep: "e\<in>schema_dependencies S"
    using assms by (auto simp: system_dependency_edges_def)
  have "((g d,c),rename_schema id id g S)\<in>system_clauses (rename_system g P)"
    using clause by (auto simp: rename_system_def intro!: image_eqI[where x="((d,c),S)"])
  moreover have "g e\<in>schema_dependencies (rename_schema id id g S)" using dep by (simp add: renamed_schema_dependencies)
  ultimately show ?thesis by (auto simp: system_dependency_edges_def)
qed

lemma variant_dependency_edge:
  assumes variant: "system_alpha_variant P Q" and edge: "(d,e)\<in>system_dependency_edges P"
  shows "(d,e)\<in>system_dependency_edges Q"
proof -
  obtain c S where clause: "((d,c),S)\<in>system_clauses P" and dep: "e\<in>schema_dependencies S"
    using edge by (auto simp: system_dependency_edges_def)
  have formed: "schema_system_formed P" using variant by (simp add: system_alpha_variant_def)
  have member: "d\<in>system_definitions P" using formed clause unfolding schema_system_formed_def by blast
  obtain h where family: "schema_family_variant h (system_clause_family P d) (system_clause_family Q d)"
    using variant member unfolding system_alpha_variant_def by blast
  obtain T where target: "(h c,T)\<in>system_clause_family Q d" and alpha: "schema_alpha_variant S T"
    using family clause unfolding schema_family_variant_def by fastforce
  have "e\<in>schema_dependencies T" using alpha dep by (auto simp: schema_alpha_variant_def renamed_schema_dependencies)
  then show ?thesis using target by (auto simp: system_dependency_edges_def)
qed

lemma definition_closure_map:
  assumes edges: "\<And>d e. (d,e)\<in>system_dependency_edges P \<Longrightarrow> (g d,g e)\<in>system_dependency_edges Q"
  shows "g ` system_definition_closure P R\<subseteq>system_definition_closure Q (g ` R)"
proof
  fix y assume "y\<in>g ` system_definition_closure P R"
  then obtain r d where root: "r\<in>R" and path: "(r,d)\<in>(system_dependency_edges P)\<^sup>*" and y: "y=g d"
    by (auto simp: system_definition_closure_def)
  have "(g r,g d)\<in>(system_dependency_edges Q)\<^sup>*"
    using path by (induction rule: rtrancl_induct) (auto intro: rtrancl_into_rtrancl edges)
  then show "y\<in>system_definition_closure Q (g ` R)" using root y by (auto simp: system_definition_closure_def)
qed

section \<open>A rule program's reach from its roots is the demanded traversal\<close>

text \<open>
  A rule program is read as rows at sites: a site's rows are its rules, and a rule demands the callees of
  its schema. The demanded traversal of \<open>Finite_Demanded_Closures\<close> over this reading reads a site once, and
  only once a root has reached it; bounded by the program's own sites, which its formation closes under the
  callees, it returns exactly the rooted sites (\<open>finite_demanded_readings_within_exact\<close>). It is evaluated
  through its keyed refinement (\<open>keyed_demanded_sites_exact\<close>), with the sites their own key.
\<close>

definition rule_rows :: "('d\<times>(local_address\<times>('a,'s,'d) finite_factor_schema) list) list \<Rightarrow> 'd \<Rightarrow>
    (local_address\<times>('a,'s,'d) finite_factor_schema) fset" where
  "rule_rows ds d=(case map_of ds d of None \<Rightarrow> {||} | Some rs \<Rightarrow> fset_of_list rs)"

lemma rule_rows_member:
  assumes "x |\<in>| rule_rows ds d"
  obtains rs where "(d,rs)\<in>set ds" "x\<in>set rs"
  using assms unfolding rule_rows_def
  by (cases "map_of ds d") (auto intro: that dest: map_of_SomeD simp: fset_of_list_elem)

lemma rule_rows_outside:
  assumes "d\<notin>fst ` set ds"
  shows "rule_rows ds d={||}"
proof -
  have "map_of ds d=None" using assms by (simp add: map_of_eq_None_iff)
  then show ?thesis by (simp add: rule_rows_def)
qed

section \<open>The entries the loop calls reach every definition of the joined program\<close>

text \<open>
  The roots are the entries the loop calls: readiness's settled and ready, the reach, the verdict's entry,
  the witnesses' three (excess, undeclared, malformed), request construction's entry and admission, and the
  decomposition's application, each at its site in the joined program.
\<close>

definition development_package_entries :: "local_address option definition_site list" where
  "development_package_entries=[relocate_site 1 readiness_settled,relocate_site 1 readiness_ready,reach_reached,
    verdict_entry,witness_excess,witness_undeclared,witness_malformed,relocate_site 2 request_entry,
    relocate_site 2 request_admission,decomposition_relocation decomposition_applies]"

lemma package_sites: "system_definitions package_program=fst ` set package_definitions"
  unfolding package_program_def finite_package_program_def by (rule finite_rule_program_definitions)

lemma relocated_identity: "relocated_definitions id ds=ds"
  by (simp add: relocated_definitions_def finite_rename_schema_fixed case_prod_unfold)

lemma development_package_entry_sites:
  "readiness_settled\<in>fst ` set readiness_definitions" "readiness_ready\<in>fst ` set readiness_definitions"
  "reach_reached\<in>fst ` set reach_definitions" "verdict_entry\<in>fst ` set native_verdict_definitions"
  "witness_excess\<in>fst ` set verdict_witness_definitions" "witness_undeclared\<in>fst ` set verdict_witness_definitions"
  "witness_malformed\<in>fst ` set verdict_witness_definitions" "request_entry\<in>fst ` set native_request_definitions"
  "request_admission\<in>fst ` set native_request_definitions"
  "decomposition_applies\<in>fst ` set decomposition_definitions"
  by code_simp+

lemma development_package_entries_sites: "set development_package_entries\<subseteq>system_definitions package_program"
  using development_package_entry_sites
  by (auto simp: development_package_entries_def package_sites package_members image_Un relocated_definitions_sites)

lemma package_part_reached:
  assumes whole: "set (relocated_definitions g ds)\<subseteq>set package_definitions"
    and formed: "schema_system_formed (decode_finite_system (finite_rule_program ds))"
    and inside: "roots |\<subseteq>| fset_of_list (map fst ds)"
    and starts: "g ` fset roots\<subseteq>system_definition_closure package_program R"
    and walked: "case keyed_demanded_sites id id (rule_rows ds) (\<lambda>x. finite_schema_dependencies (snd x)) roots of
      None \<Rightarrow> False | Some S \<Rightarrow> fset_of_list (map fst xs) |\<subseteq>| S"
  shows "g ` fst ` set xs\<subseteq>system_definition_closure package_program R"
proof -
  let ?U="fset_of_list (map fst ds)"
  let ?read="rule_rows ds"
  let ?succ="\<lambda>x. finite_schema_dependencies (snd x)"
  let ?C="system_definition_closure package_program R"
  have closed: "e |\<in>| ?U" if site: "d |\<in>| ?U" and row: "y |\<in>| ?read d" and dep: "e |\<in>| ?succ y" for d y e
  proof -
    obtain rs where rule: "(d,rs)\<in>set ds" "y\<in>set rs" using row by (rule rule_rows_member)
    obtain c F where y: "y=(c,F)" by (cases y)
    have "((d,c),decode_finite_schema F)\<in>system_clauses (decode_finite_system (finite_rule_program ds))"
      unfolding finite_rule_program_clause using rule y by blast
    then have "schema_dependencies (decode_finite_schema F)\<subseteq>system_definitions (decode_finite_system (finite_rule_program ds))"
      using formed unfolding schema_system_formed_def by blast
    then show ?thesis using dep y
      by (auto simp: finite_schema_dependencies_correct[symmetric] finite_rule_program_definitions fset_of_list.rep_eq)
  qed
  have step: "g e\<in>?C" if at: "g x\<in>?C" and row: "y |\<in>| ?read x" and dep: "e |\<in>| ?succ y" for x y e
  proof -
    obtain rs' where rule1: "(x,rs')\<in>set ds" and rule2': "y\<in>set rs'" using row by (rule rule_rows_member)
    obtain c F where y: "y=(c,F)" by (cases y)
    have rule: "(x,rs')\<in>set ds" "(c,F)\<in>set rs'" using rule1 rule2' y by simp_all
    have callee: "e |\<in>| finite_schema_dependencies F" using dep y by simp
    let ?F="finite_rename_schema id id g F"
    have "(g x,map (\<lambda>(c,F). (c,finite_rename_schema id id g F)) rs')\<in>set (relocated_definitions g ds)"
      unfolding relocated_definitions_def set_map by (rule image_eqI[where x="(x,rs')"]) (simp_all add: rule(1))
    then have member: "(g x,map (\<lambda>(c,F). (c,finite_rename_schema id id g F)) rs')\<in>set package_definitions"
      using whole by blast
    have inner: "(c,?F)\<in>set (map (\<lambda>(c,F). (c,finite_rename_schema id id g F)) rs')"
      unfolding set_map by (rule image_eqI[where x="(c,F)"]) (simp_all add: rule(2))
    have clause: "((g x,c),decode_finite_schema ?F)\<in>system_clauses package_program"
      unfolding package_program_def finite_package_program_def finite_rule_program_clause
      using member inner by blast
    have "g e\<in>schema_dependencies (decode_finite_schema ?F)"
      using callee by (simp add: finite_rename_schema_correct renamed_schema_dependencies
        finite_schema_dependencies_correct[symmetric])
    then have edge: "(g x,g e)\<in>system_dependency_edges package_program"
      unfolding system_dependency_edges_def using clause by blast
    show "g e\<in>?C" by (rule system_definition_closure_step[OF at edge])
  qed
  have restrict: "(\<lambda>d. if d |\<in>| ?U then ?read d else {||})=?read"
    by (rule ext) (auto simp: rule_rows_outside fset_of_list.rep_eq)
  have sites: "finite_demanded_sites ?read ?succ roots=Some (finite_rooted_sites ?read ?succ ?U roots)"
    using finite_demanded_readings_within_exact[where read="?read" and succ="?succ" and U="?U" and roots=roots,
      OF inside closed] finite_demanded_sites_readings[of ?read ?succ roots]
    by (simp only: restrict option.map fst_conv)
  have least: "finite_rooted_sites ?read ?succ ?U roots |\<subseteq>| ffilter (\<lambda>d. g d\<in>?C) ?U"
  proof (rule finite_rooted_sites_least)
    show "roots |\<subseteq>| ffilter (\<lambda>d. g d\<in>?C) ?U" using inside starts by (auto simp: less_eq_fset.rep_eq ffilter.rep_eq)
    fix d e assume d: "d |\<in>| ffilter (\<lambda>d. g d\<in>?C) ?U" and edge: "(d,e) |\<in>| finite_row_edges ?read ?succ ?U"
    obtain y where y: "y |\<in>| ?read d" "e |\<in>| ?succ y" using edge by (auto simp: finite_row_edges_member)
    have "d |\<in>| ?U" "g d\<in>?C" using d by simp_all
    then show "e |\<in>| ffilter (\<lambda>d. g d\<in>?C) ?U" using closed[OF _ y] step[OF _ y] by simp
  qed
  have keyed: "keyed_demanded_sites id id ?read ?succ roots=finite_demanded_sites ?read ?succ roots"
    by (rule keyed_demanded_sites_exact) simp
  obtain S where result: "finite_demanded_sites ?read ?succ roots=Some S"
    and covered: "fset_of_list (map fst xs) |\<subseteq>| S" using walked unfolding keyed by (auto split: option.splits)
  have same: "S=finite_rooted_sites ?read ?succ ?U roots" using result sites by simp
  have sub: "fset_of_list (map fst xs) |\<subseteq>| ffilter (\<lambda>d. g d\<in>?C) ?U"
    using order_trans[OF covered least[folded same]] .
  show ?thesis using sub by (auto simp: less_eq_fset.rep_eq ffilter.rep_eq fset_of_list.rep_eq)
qed

lemma package_entries_closure:
  "set development_package_entries\<subseteq>system_definition_closure package_program (set development_package_entries)"
  by (rule system_definition_closure_roots)

theorem package_entries_reach:
  "system_definition_closure package_program (set development_package_entries)=system_definitions package_program"
proof (rule antisym)
  show "system_definition_closure package_program (set development_package_entries)\<subseteq>system_definitions package_program"
    by (rule system_definition_closure_boundary(1)[OF package_program_formed development_package_entries_sites])
  let ?C="system_definition_closure package_program (set development_package_entries)"
  have roots: "x\<in>set development_package_entries \<Longrightarrow> x\<in>?C" for x using package_entries_closure by blast
  have verdict: "id ` fst ` set native_verdict_definitions\<subseteq>?C"
  proof (rule package_part_reached[where roots="{|verdict_entry,reach_reached|}"])
    show "schema_system_formed (decode_finite_system (finite_rule_program native_verdict_definitions))"
      by (rule package_parts_formed(1))
    show "{|verdict_entry,reach_reached|} |\<subseteq>| fset_of_list (map fst native_verdict_definitions)" by code_simp
    show "set (relocated_definitions id native_verdict_definitions)\<subseteq>set package_definitions"
      by (auto simp: relocated_identity package_members)
    show "id ` fset {|verdict_entry,reach_reached|}\<subseteq>?C" using roots by (auto simp: development_package_entries_def)
    show "case keyed_demanded_sites id id (rule_rows native_verdict_definitions) (\<lambda>x. finite_schema_dependencies (snd x))
        {|verdict_entry,reach_reached|} of None \<Rightarrow> False
      | Some S \<Rightarrow> fset_of_list (map fst native_verdict_definitions) |\<subseteq>| S" by code_simp
  qed
  have witnesses: "id ` fst ` set verdict_witness_definitions\<subseteq>?C"
  proof (rule package_part_reached[where roots="{|witness_excess,witness_undeclared,witness_malformed|}"])
    show "schema_system_formed (decode_finite_system (finite_rule_program verdict_witness_definitions))"
      by (rule package_parts_formed(3))
    show "{|witness_excess,witness_undeclared,witness_malformed|} |\<subseteq>| fset_of_list (map fst verdict_witness_definitions)"
      by code_simp
    show "set (relocated_definitions id verdict_witness_definitions)\<subseteq>set package_definitions"
      by (auto simp: relocated_identity package_members)
    show "id ` fset {|witness_excess,witness_undeclared,witness_malformed|}\<subseteq>?C"
      using roots by (auto simp: development_package_entries_def)
    show "case keyed_demanded_sites id id (rule_rows verdict_witness_definitions) (\<lambda>x. finite_schema_dependencies (snd x))
        {|witness_excess,witness_undeclared,witness_malformed|} of None \<Rightarrow> False
      | Some S \<Rightarrow> fset_of_list (map fst verdict_witness_definitions) |\<subseteq>| S" by code_simp
  qed
  have readiness: "relocate_site 1 ` fst ` set readiness_definitions\<subseteq>?C"
  proof (rule package_part_reached[where roots="{|readiness_settled,readiness_ready|}"])
    show "schema_system_formed (decode_finite_system (finite_rule_program readiness_definitions))"
      by (rule native_readiness_formed[unfolded native_readiness_system_def finite_native_readiness_def])
    show "{|readiness_settled,readiness_ready|} |\<subseteq>| fset_of_list (map fst readiness_definitions)" by code_simp
    show "set (relocated_definitions (relocate_site 1) readiness_definitions)\<subseteq>set package_definitions"
      by (auto simp: package_members)
    show "relocate_site 1 ` fset {|readiness_settled,readiness_ready|}\<subseteq>?C"
      using roots by (auto simp: development_package_entries_def)
    show "case keyed_demanded_sites id id (rule_rows readiness_definitions) (\<lambda>x. finite_schema_dependencies (snd x))
        {|readiness_settled,readiness_ready|} of None \<Rightarrow> False
      | Some S \<Rightarrow> fset_of_list (map fst readiness_definitions) |\<subseteq>| S" by code_simp
  qed
  have request: "relocate_site 2 ` fst ` set native_request_definitions\<subseteq>?C"
  proof (rule package_part_reached[where roots="{|request_entry,request_admission|}"])
    show "schema_system_formed (decode_finite_system (finite_rule_program native_request_definitions))"
      by (rule native_request_formed[unfolded native_request_system_def finite_native_request_def])
    show "{|request_entry,request_admission|} |\<subseteq>| fset_of_list (map fst native_request_definitions)" by code_simp
    show "set (relocated_definitions (relocate_site 2) native_request_definitions)\<subseteq>set package_definitions"
      by (auto simp: package_members)
    show "relocate_site 2 ` fset {|request_entry,request_admission|}\<subseteq>?C"
      using roots by (auto simp: development_package_entries_def)
    show "case keyed_demanded_sites id id (rule_rows native_request_definitions) (\<lambda>x. finite_schema_dependencies (snd x))
        {|request_entry,request_admission|} of None \<Rightarrow> False
      | Some S \<Rightarrow> fset_of_list (map fst native_request_definitions) |\<subseteq>| S" by code_simp
  qed
  have decomposition: "decomposition_relocation ` fst ` set (take 6 decomposition_definitions)\<subseteq>?C"
  proof (rule package_part_reached[where ds=decomposition_definitions and roots="{|decomposition_applies|}"])
    show "schema_system_formed (decode_finite_system (finite_rule_program decomposition_definitions))"
      by (rule native_decomposition_formed[unfolded native_decomposition_system_def finite_native_decomposition_def])
    show "{|decomposition_applies|} |\<subseteq>| fset_of_list (map fst decomposition_definitions)" by code_simp
    show "set (relocated_definitions decomposition_relocation decomposition_definitions)\<subseteq>set package_definitions"
      by (auto simp: package_members)
    show "decomposition_relocation ` fset {|decomposition_applies|}\<subseteq>?C"
      using roots by (auto simp: development_package_entries_def)
    show "case keyed_demanded_sites id id (rule_rows decomposition_definitions) (\<lambda>x. finite_schema_dependencies (snd x))
        {|decomposition_applies|} of None \<Rightarrow> False
      | Some S \<Rightarrow> fset_of_list (map fst (take 6 decomposition_definitions)) |\<subseteq>| S" by code_simp
  qed
  have reach: "set reach_definitions\<subseteq>set native_verdict_definitions"
    using native_verdict_whole(3) by (auto simp: verdict_unreached_definitions_def)
  have rows: "set verdict_rows_definitions\<subseteq>set native_verdict_definitions" by (rule native_verdict_whole(1))
  have mentions: "set (drop 1 verdict_mentions_definitions)\<subseteq>set native_verdict_definitions"
    by (auto simp: native_verdict_definitions_def)
  have "decomposition_relocation ` fst ` set decomposition_definitions=
      fst ` set (relocated_definitions decomposition_relocation decomposition_definitions)"
    by (simp only: relocated_definitions_sites)
  also have "\<dots>=decomposition_relocation ` fst ` set (take 6 decomposition_definitions)\<union>
      fst ` set verdict_rows_definitions\<union>fst ` set (drop 1 verdict_mentions_definitions)"
    by (simp only: decomposition_relocated set_append image_Un relocated_definitions_sites Un_assoc)
  finally have split: "decomposition_relocation ` fst ` set decomposition_definitions=
      decomposition_relocation ` fst ` set (take 6 decomposition_definitions)\<union>
      fst ` set verdict_rows_definitions\<union>fst ` set (drop 1 verdict_mentions_definitions)" .
  show "system_definitions package_program\<subseteq>?C"
    unfolding package_sites package_members image_Un relocated_definitions_sites
    unfolding split
  proof (intro Un_least)
    show "fst ` set reach_definitions\<subseteq>?C" using image_mono[OF reach, of fst] verdict by simp
    show "fst ` set verdict_rows_definitions\<subseteq>?C" using image_mono[OF rows, of fst] verdict by simp
    show "fst ` set (drop 1 verdict_mentions_definitions)\<subseteq>?C" using image_mono[OF mentions, of fst] verdict by simp
  qed (use verdict witnesses readiness request decomposition in simp_all)
qed

section \<open>The joined program compiled once, by the executable compiler\<close>

text \<open>
  The joined program is installed as the extension of the empty program over the empty environment's
  selected empty package (\<open>Factor_Finite_Closed_Installation\<close>): the mapped native extension places its
  definitions at fresh uses, compiles them by \<open>finite_compile_definitions\<close>, installs the compiled rows and
  selects them. The installation is a choice made outside the process, as the seed's is.
\<close>

definition development_package_source :: "local_address option finite_artifact_environment\<times>local_address option" where
  "development_package_source=finite_select_roots finite_empty_environment []"

interpretation development_installation: closed_program_installation finite_empty_environment
  "fst development_package_source" "snd development_package_source" finite_package_program
proof (rule closed_program_installation.intro)
  show "finite_environment_formed (finite_empty_environment::local_address option finite_artifact_environment)"
    by (rule finite_empty_environment_formed)
  show "finite_select_roots finite_empty_environment []=(fst development_package_source,snd development_package_source)"
    by (simp add: development_package_source_def)
  show "finite_system_formed finite_package_program"
    using package_program_formed by (simp only: package_program_def finite_system_formed_correct)
qed

definition development_package_compiled :: "local_address option finite_artifact_environment\<times>local_address option" where
  "development_package_compiled=the (finite_extend_mapped_native (fst development_package_source)
    empty_installation_program finite_package_program (\<lambda>_. (None,[])))"

definition development_package_placement :: "local_address option definition_site \<Rightarrow> local_address option definition_site" where
  "development_package_placement=finite_program_coordinates (fst development_package_source) {||}
    (finite_system_definitions finite_package_program) (\<lambda>_. (None,[]))"

lemma development_package_built:
  "finite_extend_mapped_native (fst development_package_source) empty_installation_program finite_package_program
    (\<lambda>_. (None,[]))=Some development_package_compiled"
  using development_installation.total unfolding development_package_compiled_def by auto

lemma development_package_compiled_facts:
  "finite_environment_formed (fst development_package_compiled)"
  "inj_on development_package_placement (system_definitions package_program)"
  "\<exists>T. native_package_at (decode_finite_environment (fst development_package_compiled)) (snd development_package_compiled) [] T \<and>
    system_alpha_variant (rename_system development_package_placement package_program) T \<and>
    system_definitions T=development_package_placement ` system_definitions package_program \<and>
    positive_meaning T=map_prod development_package_placement id ` positive_meaning package_program"
proof -
  obtain F u where pair: "development_package_compiled=(F,u)" by (cases development_package_compiled)
  note facts=development_installation.install.correct[OF development_package_built[unfolded pair]]
  have defs: "fset (finite_system_definitions finite_package_program)=system_definitions package_program"
    by (simp only: package_program_def finite_system_definitions_correct)
  have placement: "finite_program_coordinates (fst development_package_source)
      (finite_system_definitions (empty_installation_program::local_address option finite_native_system))
      (finite_system_definitions finite_package_program) (\<lambda>_. (None,[]))=development_package_placement"
    by (simp add: development_package_placement_def)
  note facts'=facts[unfolded placement defs package_program_def[symmetric]]
  show "finite_environment_formed (fst development_package_compiled)" using facts' by (simp add: pair)
  show "inj_on development_package_placement (system_definitions package_program)" using facts' by blast
  show "\<exists>T. native_package_at (decode_finite_environment (fst development_package_compiled)) (snd development_package_compiled) [] T \<and>
    system_alpha_variant (rename_system development_package_placement package_program) T \<and>
    system_definitions T=development_package_placement ` system_definitions package_program \<and>
    positive_meaning T=map_prod development_package_placement id ` positive_meaning package_program"
    using facts' by (simp add: pair) blast
qed

definition development_package_program :: "local_address option native_system" where
  "development_package_program=(THE T. native_package_at (decode_finite_environment (fst development_package_compiled))
    (snd development_package_compiled) [] T)"

lemma development_package_compilation:
  "native_package_at (decode_finite_environment (fst development_package_compiled)) (snd development_package_compiled) []
    development_package_program"
  "system_alpha_variant (rename_system development_package_placement package_program) development_package_program"
  "system_definitions development_package_program=development_package_placement ` system_definitions package_program"
  "positive_meaning development_package_program=map_prod development_package_placement id ` positive_meaning package_program"
proof -
  obtain T where T: "native_package_at (decode_finite_environment (fst development_package_compiled)) (snd development_package_compiled) [] T"
    "system_alpha_variant (rename_system development_package_placement package_program) T"
    "system_definitions T=development_package_placement ` system_definitions package_program"
    "positive_meaning T=map_prod development_package_placement id ` positive_meaning package_program"
    using development_package_compiled_facts(3) by blast
  have same: "development_package_program=T" unfolding development_package_program_def
    by (metis T(1) native_package_unique the_equality)
  show "native_package_at (decode_finite_environment (fst development_package_compiled)) (snd development_package_compiled) []
    development_package_program"
    "system_alpha_variant (rename_system development_package_placement package_program) development_package_program"
    "system_definitions development_package_program=development_package_placement ` system_definitions package_program"
    "positive_meaning development_package_program=map_prod development_package_placement id ` positive_meaning package_program"
    using T by (simp_all add: same)
qed

section \<open>The package: the compiled environment, selected at the entries, closed and kept\<close>

definition development_package_selection :: "local_address option finite_artifact_environment\<times>local_address option" where
  "development_package_selection=finite_select_roots (fst development_package_compiled)
    (map development_package_placement development_package_entries)"

definition development_package_use :: "local_address option" where
  "development_package_use=snd development_package_selection"

definition development_package_environment :: "local_address option finite_artifact_environment" where
  "development_package_environment=finite_native_package_environment
    (fst development_package_selection) development_package_use []"

lemma development_package_environment_decode:
  "decode_finite_environment development_package_environment=native_package_environment
    (decode_finite_environment (fst development_package_selection)) development_package_use []"
  by (simp only: development_package_environment_def finite_native_package_environment_correct)

lemma development_package_reach:
  "system_definition_closure development_package_program (development_package_placement ` set development_package_entries)=
    system_definitions development_package_program"
proof (rule antisym)
  have formed: "schema_system_formed development_package_program"
    using development_package_compilation(2) by (simp add: system_alpha_variant_def)
  have roots: "development_package_placement ` set development_package_entries\<subseteq>system_definitions development_package_program"
    using development_package_entries_sites development_package_compilation(3) by auto
  show "system_definition_closure development_package_program (development_package_placement ` set development_package_entries)\<subseteq>
      system_definitions development_package_program"
    by (rule system_definition_closure_boundary(1)[OF formed roots])
  have edges: "(development_package_placement d,development_package_placement e)\<in>system_dependency_edges development_package_program"
    if "(d,e)\<in>system_dependency_edges package_program" for d e
    by (rule variant_dependency_edge[OF development_package_compilation(2) renamed_dependency_edge[OF that]])
  show "system_definitions development_package_program\<subseteq>
      system_definition_closure development_package_program (development_package_placement ` set development_package_entries)"
    using definition_closure_map[of package_program development_package_placement development_package_program,
      OF edges, of "set development_package_entries"]
    by (simp only: package_entries_reach development_package_compilation(3))
qed

theorem development_package_selected:
  "native_package_at (decode_finite_environment (fst development_package_selection)) development_package_use []
    development_package_program"
  "native_package_roots (decode_finite_environment (fst development_package_selection)) development_package_use []=
    development_package_placement ` set development_package_entries"
proof -
  let ?F="decode_finite_environment (fst development_package_compiled)"
  let ?u="snd development_package_compiled"
  let ?T="development_package_program"
  let ?R="development_package_placement ` set development_package_entries"
  have compiled: "native_package_at ?F ?u [] ?T" by (rule development_package_compilation(1))
  have ff: "finite_environment_formed (fst development_package_compiled)" by (rule development_package_compiled_facts(1))
  obtain A :: "(local_address\<times>local_address option definition_site) set"
    where formed: "native_package_formed ?F (rel_ran A)" and program: "?T=native_program ?F (rel_ran A)"
    using compiled unfolding native_package_at_def by blast
  have tdefs: "system_definitions ?T=native_definition_sites ?F (rel_ran A)"
    using native_program_definitions[OF formed] program by simp
  have roots: "?R\<subseteq>system_definitions ?T"
    using development_package_entries_sites development_package_compilation(3) by auto
  have targets: "set (map development_package_placement development_package_entries)\<subseteq>environment_positions ?F"
    using roots tdefs native_package_sites(1)[OF formed] by auto
  obtain G v where sel: "development_package_selection=(G,v)" by (cases development_package_selection)
  note selected=finite_select_roots_correct[OF ff targets sel[unfolded development_package_selection_def]]
  have gf: "environment_formed (decode_finite_environment G)"
    using selected(1) by (simp only: finite_environment_formed_correct)
  have moved: "native_package_at (decode_finite_environment G) ?u [] ?T"
    by (rule native_package_included[OF compiled selected(2) gf])
  obtain B :: "(local_address\<times>local_address option definition_site) set"
    where formedB: "native_package_formed (decode_finite_environment G) (rel_ran B)"
    and programB: "?T=native_program (decode_finite_environment G) (rel_ran B)"
    using moved unfolding native_package_at_def by blast
  have bdefs: "system_definitions ?T=native_definition_sites (decode_finite_environment G) (rel_ran B)"
    using native_program_definitions[OF formedB] programB by simp
  have closure: "system_definition_closure ?T ?R=native_definition_sites (decode_finite_environment G) ?R"
    using native_program_definition_closure[of ?R "decode_finite_environment G" "rel_ran B"] roots bdefs programB by simp
  have sites: "native_definition_sites (decode_finite_environment G) ?R=native_definition_sites (decode_finite_environment G) (rel_ran B)"
    using closure development_package_reach bdefs by simp
  have formedR: "native_package_formed (decode_finite_environment G) ?R"
    using formedB unfolding native_package_formed_def sites by blast
  have graph: "native_definition_graph (decode_finite_environment G) ?R=native_definition_graph (decode_finite_environment G) (rel_ran B)"
    by (simp add: native_definition_graph_def sites)
  have programR: "?T=native_program (decode_finite_environment G) ?R"
    unfolding programB native_program_def graph by (rule refl)
  have family: "native_root_family_at (decode_finite_environment G) v []
      (set (zip (family_ports (length (map development_package_placement development_package_entries)))
        (map development_package_placement development_package_entries)))"
    by (rule selected(4))
  have range: "rel_ran (set (zip (family_ports (length (map development_package_placement development_package_entries)))
        (map development_package_placement development_package_entries)))=?R"
    using selected(5) by simp
  show "native_package_at (decode_finite_environment (fst development_package_selection)) development_package_use []
    development_package_program"
    unfolding development_package_use_def sel fst_conv snd_conv native_package_at_def
    using family range formedR programR by metis
  show "native_package_roots (decode_finite_environment (fst development_package_selection)) development_package_use []=?R"
    unfolding development_package_use_def sel fst_conv snd_conv
    using native_package_roots_from_family[OF family] range by simp
qed

theorem development_package:
  "closed_native_package_at (decode_finite_environment development_package_environment) development_package_use [] development_package_program"
  "native_package_environment (decode_finite_environment development_package_environment) development_package_use []=decode_finite_environment development_package_environment"
  "native_package_roots (decode_finite_environment development_package_environment) development_package_use []=
    development_package_placement ` set development_package_entries"
  "native_definition_sites (decode_finite_environment development_package_environment) (development_package_placement ` set development_package_entries)=
    system_definitions development_package_program"
  "system_alpha_variant (rename_system development_package_placement package_program) development_package_program"
  "positive_meaning development_package_program=map_prod development_package_placement id ` positive_meaning package_program"
  "inj_on development_package_placement (system_definitions package_program)"
proof -
  let ?G="decode_finite_environment (fst development_package_selection)"
  let ?R="development_package_placement ` set development_package_entries"
  have selected: "native_package_at ?G development_package_use [] development_package_program"
    by (rule development_package_selected)
  show closed: "closed_native_package_at (decode_finite_environment development_package_environment) development_package_use [] development_package_program"
    unfolding development_package_environment_decode by (rule native_package_closed_restriction[OF selected])
  show "native_package_environment (decode_finite_environment development_package_environment) development_package_use []=decode_finite_environment development_package_environment"
    unfolding development_package_environment_decode by (rule native_package_environment_idempotent[OF selected])
  show roots: "native_package_roots (decode_finite_environment development_package_environment) development_package_use []=?R"
    unfolding development_package_environment_decode native_package_roots_stable[OF selected]
    by (rule development_package_selected(2))
  have kept: "native_package_at (decode_finite_environment development_package_environment) development_package_use [] development_package_program"
    using closed by (simp add: closed_native_package_at_def)
  obtain C :: "(local_address\<times>local_address option definition_site) set"
    where family: "native_root_family_at (decode_finite_environment development_package_environment) development_package_use [] C"
    and formed: "native_package_formed (decode_finite_environment development_package_environment) (rel_ran C)"
    and program: "development_package_program=native_program (decode_finite_environment development_package_environment) (rel_ran C)"
    using kept unfolding native_package_at_def by blast
  have range: "rel_ran C=?R" using native_package_roots_from_family[OF family] roots by simp
  show "native_definition_sites (decode_finite_environment development_package_environment) ?R=system_definitions development_package_program"
    using native_program_definitions[OF formed] program range by simp
  show "system_alpha_variant (rename_system development_package_placement package_program) development_package_program"
    by (rule development_package_compilation(2))
  show "positive_meaning development_package_program=map_prod development_package_placement id ` positive_meaning package_program"
    by (rule development_package_compilation(4))
  show "inj_on development_package_placement (system_definitions package_program)"
    by (rule development_package_compiled_facts(2))
qed

text \<open>
  Every site of the package is reached from its entries (\<open>development_package_reach\<close>), so the package's
  membership is exactly its definitions: the definitions its entries reach.
\<close>

section \<open>The package's program scope\<close>

theorem development_package_scope:
  "\<exists>C. exact_formed C \<and>
    program_scope_quoted_at C [] (decode_finite_environment development_package_environment) development_package_use [] development_package_program"
  using program_scope_quoted_total[OF development_package_selected(1)]
  by (simp only: development_package_environment_decode)

corollary development_package_scope_minimal:
  assumes "program_scope_quoted_at C q (decode_finite_environment development_package_environment) development_package_use [] development_package_program"
  shows "native_package_environment (decode_finite_environment development_package_environment) development_package_use []=decode_finite_environment development_package_environment"
  by (rule program_scope_is_minimal[OF assms])

section \<open>Every notion's contracts at its entry of the package\<close>

text \<open>
  One transport per notion composes the joined program's (\<open>package_readiness\<close> and its neighbours) with the
  compilation's (\<open>system_variant_renamed_meaning_at\<close>); each contract then holds at the notion's entry of the
  package as an instance, the transport and the contract joined by transitivity.
\<close>

lemma development_package_meaning:
  assumes "d\<in>system_definitions package_program"
  shows "(development_package_placement d,t)\<in>positive_meaning development_package_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning package_program"
  by (rule system_variant_renamed_meaning_at[OF package_program_formed development_package(7)
    development_package(5) assms])

theorem development_package_verdict:
  assumes site: "d\<in>fst ` set native_verdict_definitions"
  shows "(development_package_placement d,t)\<in>positive_meaning development_package_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning native_verdict_system"
proof -
  have member: "d\<in>system_definitions package_program" using site by (auto simp: package_sites package_members)
  show ?thesis unfolding development_package_meaning[OF member] by (rule package_verdict[OF site])
qed

theorem development_package_reach_system:
  assumes site: "d\<in>fst ` set reach_definitions"
  shows "(development_package_placement d,t)\<in>positive_meaning development_package_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning native_reach_system"
proof -
  have member: "d\<in>system_definitions package_program" using site by (auto simp: package_sites package_members)
  show ?thesis unfolding development_package_meaning[OF member] by (rule package_reach[OF site])
qed

theorem development_package_witnesses:
  assumes site: "d\<in>fst ` set verdict_witness_definitions"
  shows "(development_package_placement d,t)\<in>positive_meaning development_package_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning verdict_witness_system"
proof -
  have member: "d\<in>system_definitions package_program" using site by (auto simp: package_sites package_members)
  show ?thesis unfolding development_package_meaning[OF member] by (rule package_witnesses[OF site])
qed

theorem development_package_readiness:
  assumes site: "d\<in>fst ` set readiness_definitions"
  shows "(development_package_placement (relocate_site 1 d),t)\<in>positive_meaning development_package_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning native_readiness_system"
proof -
  have member: "relocate_site 1 d\<in>system_definitions package_program"
    using site by (auto simp: package_sites package_members image_Un relocated_definitions_sites)
  show ?thesis unfolding development_package_meaning[OF member] by (rule package_readiness[OF site])
qed

theorem development_package_request:
  assumes site: "d\<in>fst ` set native_request_definitions"
  shows "(development_package_placement (relocate_site 2 d),t)\<in>positive_meaning development_package_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning native_request_system"
proof -
  have member: "relocate_site 2 d\<in>system_definitions package_program"
    using site by (auto simp: package_sites package_members image_Un relocated_definitions_sites)
  show ?thesis unfolding development_package_meaning[OF member] by (rule package_request[OF site])
qed

theorem development_package_decomposition:
  assumes site: "d\<in>fst ` set decomposition_definitions"
  shows "(development_package_placement (decomposition_relocation d),t)\<in>positive_meaning development_package_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning native_decomposition_system"
proof -
  have member: "decomposition_relocation d\<in>system_definitions package_program"
    using site by (auto simp: package_sites package_members image_Un relocated_definitions_sites)
  show ?thesis unfolding development_package_meaning[OF member] by (rule package_decomposition[OF site])
qed

lemmas development_package_settled_exact=
  trans[OF development_package_readiness[OF development_package_entry_sites(1)] native_settled_exact]
lemmas development_package_ready_exact=
  trans[OF development_package_readiness[OF development_package_entry_sites(2)] native_ready_exact]
lemmas development_package_reached_exact=
  trans[OF development_package_reach_system[OF development_package_entry_sites(3)] native_reached_exact]
lemmas development_package_verdict_entry=
  trans[OF development_package_verdict[OF development_package_entry_sites(4)] native_verdict_entry]
lemmas development_package_excess_witness_exact=
  trans[OF development_package_witnesses[OF development_package_entry_sites(5)] native_excess_witness_exact]
lemmas development_package_undeclared_witness_exact=
  trans[OF development_package_witnesses[OF development_package_entry_sites(6)] native_undeclared_witness_exact]
lemmas development_package_request_entry=
  trans[OF development_package_request[OF development_package_entry_sites(8)] native_request_entry]
lemmas development_package_decomposition_applies=
  trans[OF development_package_decomposition[OF development_package_entry_sites(10)] native_decomposition_applies]

end
