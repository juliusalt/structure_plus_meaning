theory Development_Given_Installation
  imports Development_Native_Package Development_Given_Readers Factor_Package_Membership
    Factor_Package_Retention_Admission Factor_Site_Values Factor_Finite_Native_Sources
    RRA_Finite_Environment_Positions Native_Execution_Refinements
begin

text \<open>
  The given of the native loop's first problem (DECISIONS.md "The native loop's first problem is what a problem
  is; the problem of Q2, second, exercises its answer", and "Every distinction a native program relies on comes
  from a native notion", its #320's builds): the given's rooted readers (\<open>Development_Given_Readers\<close>) installed
  beside the development package (\<open>Development_Native_Package\<close>) in one environment, and one site whose package
  holds exactly the development package's definitions and the readers'. Installing the given is a choice made
  outside the process, as the development package's installation and the seed's are.
\<close>

section \<open>General facts the installation consumes\<close>

text \<open>A rooted program is reached from its roots, since it agrees with its source on everything it holds.\<close>

lemma rooted_system_reach:
  assumes formed: "schema_system_formed P" and roots: "roots\<subseteq>system_definitions P"
  shows "system_definition_closure (rooted_system P roots) roots=system_definitions (rooted_system P roots)"
proof (rule antisym)
  have rooted: "schema_system_formed (rooted_system P roots)" by (rule rooted_system_formed[OF formed])
  have inside: "roots\<subseteq>system_definitions (rooted_system P roots)" by (rule rooted_system_roots[OF formed roots])
  show "system_definition_closure (rooted_system P roots) roots\<subseteq>system_definitions (rooted_system P roots)"
    by (rule system_definition_closure_boundary(1)[OF rooted inside])
  have kept: "(d,e)\<in>system_dependency_edges (rooted_system P roots)"
    if d: "d\<in>system_definitions (rooted_system P roots)" and edge: "(d,e)\<in>system_dependency_edges P" for d e
  proof -
    obtain c S where clause: "((d,c),S)\<in>system_clauses P" and dep: "e\<in>schema_dependencies S"
      using edge by (auto simp: system_dependency_edges_def)
    have "((d,c),S)\<in>system_clauses (rooted_system P roots)"
      using rooted_system_agreement[of P roots] d clause unfolding systems_agree_on_def by blast
    then show ?thesis using dep by (auto simp: system_dependency_edges_def)
  qed
  have closed: "system_dependency_closed P (system_definition_closure (rooted_system P roots) roots)"
    unfolding system_dependency_closed_def
  proof (intro ballI allI impI)
    fix d e assume d: "d\<in>system_definition_closure (rooted_system P roots) roots"
      and edge: "(d,e)\<in>system_dependency_edges P"
    have "d\<in>system_definitions (rooted_system P roots)"
      using system_definition_closure_boundary(1)[OF rooted inside] d by blast
    then show "e\<in>system_definition_closure (rooted_system P roots) roots"
      by (rule system_definition_closure_step[OF d kept[OF _ edge]])
  qed
  show "system_definitions (rooted_system P roots)\<subseteq>system_definition_closure (rooted_system P roots) roots"
    unfolding rooted_system_definitions[OF formed roots]
    by (rule system_definition_closure_least[OF system_definition_closure_roots closed])
qed

text \<open>The sites a package's roots reach are its definitions when its program is reached from those roots.\<close>

lemma reached_package_sites:
  fixes E :: "'u artifact_environment"
  assumes package: "native_package_at E u r P" and roots: "R\<subseteq>system_definitions P"
    and reach: "system_definition_closure P R=system_definitions P"
  shows "native_definition_sites E R=system_definitions P"
    and "\<forall>d\<in>native_definition_sites E R. \<exists>p C. native_definition_at E (fst d) (snd d) p C"
    and "system_definitions P\<subseteq>environment_positions E"
proof -
  obtain B :: "(local_address\<times>'u definition_site) set"
    where formed: "native_package_formed E (rel_ran B)" and program: "P=native_program E (rel_ran B)"
    using package unfolding native_package_at_def by blast
  have defs: "system_definitions P=native_definition_sites E (rel_ran B)"
    using native_program_definitions[OF formed] program by simp
  have "system_definition_closure P R=native_definition_sites E R"
    using native_program_definition_closure[of R E "rel_ran B"] roots defs program by simp
  then show sites: "native_definition_sites E R=system_definitions P" using reach by simp
  show "\<forall>d\<in>native_definition_sites E R. \<exists>p C. native_definition_at E (fst d) (snd d) p C"
    using formed unfolding native_package_formed_def sites defs by blast
  show "system_definitions P\<subseteq>environment_positions E" using native_package_sites(1)[OF formed] defs by simp
qed

lemma native_definition_sites_union:
  "native_definition_sites E (A\<union>B)=native_definition_sites E A\<union>native_definition_sites E B"
  by (auto simp: native_definition_sites_def)

text \<open>
  The payloads a program states are the payload leaves of its patterns, which neither a change of its
  definition coordinates nor an alpha variant of its clauses and interfaces moves.
\<close>

lemma pattern_leaves_rename [simp]: "pattern_leaves (rename_pattern f p)=pattern_leaves p"
  by (induction p) simp_all

lemma material_leaves_rename [simp]: "material_leaves (rename_material_pattern f M)=material_leaves M"
  by (simp add: material_leaves_def material_fields_def rename_material_pattern_def)

lemma schema_leaves_rename [simp]: "schema_leaves (rename_schema f h g S)=schema_leaves S"
proof -
  have calls: "(\<Union>(s,d,p)\<in>map_socket_graph h g (rename_pattern f) (schema_premises S). pattern_leaves p)=
      (\<Union>(s,d,p)\<in>schema_premises S. pattern_leaves p)"
    by (simp add: map_socket_graph_def case_prod_beta)
  have material: "(\<Union>(s,M)\<in>(\<lambda>(s,M). (h s,rename_material_pattern f M)) ` schema_material_premises S. material_leaves M)=
      (\<Union>(s,M)\<in>schema_material_premises S. material_leaves M)"
    by (simp add: case_prod_beta)
  show ?thesis unfolding schema_leaves_def rename_schema_def using calls material by simp
qed

lemma system_payloads_rename: "system_payloads (rename_system g P)=system_payloads P"
proof -
  have "system_leaves (rename_system g P)=system_leaves P"
    by (simp add: system_leaves_def rename_system_def case_prod_beta)
  then show ?thesis by (simp add: system_payloads_def)
qed

lemma schema_alpha_variant_payloads:
  assumes "schema_alpha_variant S T"
  shows "schema_payloads T=schema_payloads S"
proof -
  obtain f h where "T=rename_schema f h id S" using assms unfolding schema_alpha_variant_def by blast
  then show ?thesis by (simp add: schema_payloads_def)
qed

lemma system_alpha_variant_payloads:
  assumes variant: "system_alpha_variant P Q"
  shows "system_payloads Q=system_payloads P"
proof -
  have pf: "schema_system_formed P" and qf: "schema_system_formed Q"
    and defs: "system_definitions P=system_definitions Q" using variant by (simp_all add: system_alpha_variant_def)
  have each: "definition_payloads (system_interface Q d) (system_clause_family Q d)=
      definition_payloads (system_interface P d) (system_clause_family P d)"
    if member: "d\<in>system_definitions P" for d
  proof -
    obtain f h where interface: "system_interface Q d=rename_pattern f (system_interface P d)"
      and family: "schema_family_variant h (system_clause_family P d) (system_clause_family Q d)"
      using variant member unfolding system_alpha_variant_def by blast
    have clauses: "(\<Union>(e,T)\<in>system_clause_family Q d. schema_payloads T)=
        (\<Union>(c,S)\<in>system_clause_family P d. schema_payloads S)"
    proof (rule set_eqI, rule iffI)
      fix v assume "v\<in>(\<Union>(e,T)\<in>system_clause_family Q d. schema_payloads T)"
      then have "\<exists>x\<in>system_clause_family Q d. v\<in>schema_payloads (snd x)" by (simp only: UN_iff case_prod_beta)
      then obtain x where x: "x\<in>system_clause_family Q d" and v: "v\<in>schema_payloads (snd x)" by (rule bexE)
      have t: "(fst x,snd x)\<in>system_clause_family Q d" using x by simp
      have "fst x\<in>rel_dom (system_clause_family Q d)" using t by (rule rel_domI)
      then obtain c where c: "c\<in>rel_dom (system_clause_family P d)" and e: "fst x=h c"
        using family unfolding schema_family_variant_def by blast
      obtain S where s: "(c,S)\<in>system_clause_family P d" using c by (auto simp: rel_dom_def)
      obtain T' where t': "(h c,T')\<in>system_clause_family Q d" and alpha: "schema_alpha_variant S T'"
        using family s unfolding schema_family_variant_def by blast
      have sv: "single_valued (system_clause_family Q d)" using family unfolding schema_family_variant_def by blast
      have t2: "(h c,snd x)\<in>system_clause_family Q d" using t e by simp
      have same: "T'=snd x" by (rule single_valued_outputs[OF sv t' t2])
      have payload: "v\<in>schema_payloads S" using v schema_alpha_variant_payloads[OF alpha] same by simp
      show "v\<in>(\<Union>(c,S)\<in>system_clause_family P d. schema_payloads S)"
        unfolding UN_iff case_prod_beta using s payload by (intro bexI[where x="(c,S)"]) simp_all
    next
      fix v assume "v\<in>(\<Union>(c,S)\<in>system_clause_family P d. schema_payloads S)"
      then have "\<exists>x\<in>system_clause_family P d. v\<in>schema_payloads (snd x)" by (simp only: UN_iff case_prod_beta)
      then obtain x where x: "x\<in>system_clause_family P d" and v: "v\<in>schema_payloads (snd x)" by (rule bexE)
      have s: "(fst x,snd x)\<in>system_clause_family P d" using x by simp
      obtain T where t: "(h (fst x),T)\<in>system_clause_family Q d" and alpha: "schema_alpha_variant (snd x) T"
        using family s unfolding schema_family_variant_def by blast
      have payload: "v\<in>schema_payloads T" using v schema_alpha_variant_payloads[OF alpha] by simp
      show "v\<in>(\<Union>(e,T)\<in>system_clause_family Q d. schema_payloads T)"
        unfolding UN_iff case_prod_beta using t payload by (intro bexI[where x="(h (fst x),T)"]) simp_all
    qed
    show ?thesis unfolding definition_payloads_def interface pattern_leaves_rename clauses ..
  qed
  show ?thesis unfolding system_payloads_definitions[OF qf] system_payloads_definitions[OF pf] defs[symmetric]
    by (rule SUP_cong[OF refl each])
qed

section \<open>The readers installed beside the development package\<close>

lemma development_package_kept:
  "native_package_at (decode_finite_environment development_package_environment) development_package_use []
    development_package_program"
  using development_package(1) by (simp add: closed_native_package_at_def)

lemma development_package_environment_formed: "finite_environment_formed development_package_environment"
  using development_package_kept
  unfolding finite_environment_formed_correct native_package_at_def native_root_family_at_def by blast

text \<open>
  The closed installation route: the empty package is selected over the development package's environment,
  and the readers' rooted program is installed as its mapped extension, each definition at a fresh use.
\<close>

definition given_readers_source :: "local_address option finite_artifact_environment\<times>local_address option" where
  "given_readers_source=finite_select_roots development_package_environment []"

interpretation given_installation: closed_program_installation development_package_environment
  "fst given_readers_source" "snd given_readers_source" finite_rooted_given_readers
proof (rule closed_program_installation.intro)
  show "finite_environment_formed development_package_environment" by (rule development_package_environment_formed)
  show "finite_select_roots development_package_environment []=(fst given_readers_source,snd given_readers_source)"
    by (simp add: given_readers_source_def)
  show "finite_system_formed finite_rooted_given_readers" by (rule finite_rooted_given_readers_formed)
qed

definition given_readers_installed :: "local_address option finite_artifact_environment\<times>local_address option" where
  "given_readers_installed=the (finite_extend_mapped_native (fst given_readers_source)
    empty_installation_program finite_rooted_given_readers (\<lambda>_. (None,[])))"

definition given_readers_placement :: "nat \<Rightarrow> local_address option definition_site" where
  "given_readers_placement=finite_program_coordinates (fst given_readers_source) {||}
    (finite_system_definitions finite_rooted_given_readers) (\<lambda>_. (None,[]))"

lemma given_readers_built:
  "finite_extend_mapped_native (fst given_readers_source) empty_installation_program finite_rooted_given_readers
    (\<lambda>_. (None,[]))=Some given_readers_installed"
  using given_installation.total unfolding given_readers_installed_def by auto

lemma given_readers_installation:
  "finite_environment_formed (fst given_readers_installed)"
  "environment_included (decode_finite_environment development_package_environment)
    (decode_finite_environment (fst given_readers_installed))"
  "inj_on given_readers_placement (system_definitions given_rooted_readers_system)"
  "\<exists>T. native_package_at (decode_finite_environment (fst given_readers_installed)) (snd given_readers_installed) [] T \<and>
    system_alpha_variant (rename_system given_readers_placement given_rooted_readers_system) T \<and>
    system_definitions T=given_readers_placement ` system_definitions given_rooted_readers_system"
proof -
  obtain K v where pair: "given_readers_installed=(K,v)" by (cases given_readers_installed)
  note facts=given_installation.install.correct[OF given_readers_built[unfolded pair]]
  have defs: "fset (finite_system_definitions finite_rooted_given_readers)=system_definitions given_rooted_readers_system"
    by (simp only: finite_system_definitions_correct finite_rooted_given_readers_exact)
  have placement: "finite_program_coordinates (fst given_readers_source)
      (finite_system_definitions (empty_installation_program::(nat,nat,nat,nat) finite_schema_system))
      (finite_system_definitions finite_rooted_given_readers) (\<lambda>_. (None,[]))=given_readers_placement"
    by (simp add: given_readers_placement_def)
  note facts'=facts[unfolded placement defs finite_rooted_given_readers_exact]
  show "finite_environment_formed (fst given_readers_installed)" using facts' by (simp add: pair)
  show "environment_included (decode_finite_environment development_package_environment)
      (decode_finite_environment (fst given_readers_installed))"
    using given_installation.original_environment_preserved[OF given_readers_built[unfolded pair]] by (simp add: pair)
  show "inj_on given_readers_placement (system_definitions given_rooted_readers_system)" using facts' by blast
  show "\<exists>T. native_package_at (decode_finite_environment (fst given_readers_installed)) (snd given_readers_installed) [] T \<and>
    system_alpha_variant (rename_system given_readers_placement given_rooted_readers_system) T \<and>
    system_definitions T=given_readers_placement ` system_definitions given_rooted_readers_system"
    using facts' by (simp add: pair) blast
qed

definition given_readers_program :: "local_address option native_system" where
  "given_readers_program=(THE T. native_package_at (decode_finite_environment (fst given_readers_installed))
    (snd given_readers_installed) [] T)"

lemma given_readers_compilation:
  "native_package_at (decode_finite_environment (fst given_readers_installed)) (snd given_readers_installed) []
    given_readers_program"
  "system_alpha_variant (rename_system given_readers_placement given_rooted_readers_system) given_readers_program"
  "system_definitions given_readers_program=given_readers_placement ` system_definitions given_rooted_readers_system"
proof -
  obtain T where T: "native_package_at (decode_finite_environment (fst given_readers_installed)) (snd given_readers_installed) [] T"
    "system_alpha_variant (rename_system given_readers_placement given_rooted_readers_system) T"
    "system_definitions T=given_readers_placement ` system_definitions given_rooted_readers_system"
    using given_readers_installation(4) by blast
  have same: "given_readers_program=T" unfolding given_readers_program_def
    by (metis T(1) native_package_unique the_equality)
  show "native_package_at (decode_finite_environment (fst given_readers_installed)) (snd given_readers_installed) []
    given_readers_program"
    "system_alpha_variant (rename_system given_readers_placement given_rooted_readers_system) given_readers_program"
    "system_definitions given_readers_program=given_readers_placement ` system_definitions given_rooted_readers_system"
    using T by (simp_all add: same)
qed

text \<open>The development package is read in the readers' environment as before.\<close>

lemma given_development_package_kept:
  "native_package_at (decode_finite_environment (fst given_readers_installed)) development_package_use []
    development_package_program"
  by (rule native_package_included[OF development_package_kept given_readers_installation(2)])
    (simp only: finite_environment_formed_correct[symmetric] given_readers_installation(1))

section \<open>Each reader's contract at its placed site\<close>

lemma given_entry_rooted:
  assumes "d|\<in>|given_reader_entries"
  shows "d\<in>system_definitions given_rooted_readers_system"
  using given_rooted_entries assms by blast

lemma given_installed_meaning:
  assumes "d\<in>system_definitions given_rooted_readers_system"
  shows "(given_readers_placement d,t)\<in>positive_meaning given_readers_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning given_rooted_readers_system"
  by (rule system_variant_renamed_meaning_at[OF given_rooted_readers_formed given_readers_installation(3)
    given_readers_compilation(2) assms])

lemmas given_installed_definition_call_admission_exact=given_rooted_definition_call_admission_exact[unfolded
  given_installed_meaning[OF given_entry_rooted[OF given_rooted_members(1)], symmetric]]
lemmas given_installed_package_closure_admission_exact=given_rooted_package_closure_admission_exact[unfolded
  given_installed_meaning[OF given_entry_rooted[OF given_rooted_members(2)], symmetric]]
lemmas given_installed_root_family_reading_exact=given_rooted_root_family_reading_exact[unfolded
  given_installed_meaning[OF given_entry_rooted[OF given_rooted_members(3)], symmetric]]
lemmas given_installed_package_admission_exact=given_rooted_package_admission_exact[unfolded
  given_installed_meaning[OF given_entry_rooted[OF given_rooted_members(4)], symmetric]]
lemmas given_installed_definition_clause_reading_exact=given_rooted_definition_clause_reading_exact[unfolded
  given_installed_meaning[OF given_entry_rooted[OF given_rooted_members(5)], symmetric]]
lemmas given_installed_definition_edge_reading_exact=given_rooted_definition_edge_reading_exact[unfolded
  given_installed_meaning[OF given_entry_rooted[OF given_rooted_members(6)], symmetric]]
lemmas given_installed_package_membership_exact=given_rooted_package_membership_exact[unfolded
  given_installed_meaning[OF given_entry_rooted[OF given_rooted_members(7)], symmetric]]
lemmas given_installed_environment_inclusion_exact=given_rooted_environment_inclusion_exact[unfolded
  given_installed_meaning[OF given_entry_rooted[OF given_rooted_members(8)], symmetric]]
lemmas given_installed_package_retention_admission_exact=given_rooted_package_retention_admission_exact[unfolded
  given_installed_meaning[OF given_entry_rooted[OF given_rooted_members(9)], symmetric]]
lemmas given_installed_use_additions_on_values=given_rooted_use_additions_on_values[unfolded
  given_installed_meaning[OF given_entry_rooted[OF given_rooted_members(10)], symmetric]]
lemmas given_installed_use_absence_exact=given_rooted_use_absence_exact[unfolded
  given_installed_meaning[OF given_entry_rooted[OF given_rooted_members(11)], symmetric]]
lemmas given_installed_payload_audit_exact=given_rooted_payload_audit_exact[unfolded
  given_installed_meaning[OF given_entry_rooted[OF given_rooted_members(12)], symmetric]]

section \<open>The readers' package is reached from their entries\<close>

lemma given_readers_edges:
  assumes "(d,e)\<in>system_dependency_edges given_rooted_readers_system"
  shows "(given_readers_placement d,given_readers_placement e)\<in>system_dependency_edges given_readers_program"
  by (rule variant_dependency_edge[OF given_readers_compilation(2) renamed_dependency_edge[OF assms]])

lemma given_reader_entries_guard: "fset given_reader_entries\<subseteq>system_definitions guard_readers_system"
  using given_rooted_entries rooted_system_subdomain[of guard_readers_system "fset given_reader_entries"]
  unfolding given_rooted_readers_system_def by (rule subset_trans)

lemma given_rooted_reach:
  "system_definition_closure given_rooted_readers_system (fset given_reader_entries)=
    system_definitions given_rooted_readers_system"
  unfolding given_rooted_readers_system_def by (rule rooted_system_reach[OF guard_readers_formed given_reader_entries_guard])

lemma given_readers_reach:
  "system_definition_closure given_readers_program (given_readers_placement ` fset given_reader_entries)=
    system_definitions given_readers_program"
proof (rule antisym)
  have formed: "schema_system_formed given_readers_program"
    using given_readers_compilation(2) by (simp add: system_alpha_variant_def)
  have roots: "given_readers_placement ` fset given_reader_entries\<subseteq>system_definitions given_readers_program"
    using given_rooted_entries given_readers_compilation(3) by auto
  show "system_definition_closure given_readers_program (given_readers_placement ` fset given_reader_entries)\<subseteq>
      system_definitions given_readers_program"
    by (rule system_definition_closure_boundary(1)[OF formed roots])
  show "system_definitions given_readers_program\<subseteq>
      system_definition_closure given_readers_program (given_readers_placement ` fset given_reader_entries)"
    using definition_closure_map[of given_rooted_readers_system given_readers_placement given_readers_program,
      OF given_readers_edges, of "fset given_reader_entries"]
    by (simp only: given_rooted_reach given_readers_compilation(3))
qed

section \<open>The given: one site over the development package's entries and the readers'\<close>

definition given_roots :: "local_address option definition_site list" where
  "given_roots=map development_package_placement development_package_entries @
    map given_readers_placement (sorted_list_of_fset given_reader_entries)"

lemma given_roots_set:
  "set given_roots=development_package_placement ` set development_package_entries \<union>
    given_readers_placement ` fset given_reader_entries"
  by (simp add: given_roots_def sorted_list_of_fset.rep_eq)

definition given_selection :: "local_address option finite_artifact_environment\<times>local_address option" where
  "given_selection=finite_select_roots (fst given_readers_installed) given_roots"

definition given_environment :: "local_address option finite_artifact_environment" where
  "given_environment=fst given_selection"

definition given_use :: "local_address option" where
  "given_use=snd given_selection"

definition given_program :: "local_address option native_system" where
  "given_program=native_program (decode_finite_environment given_environment) (set given_roots)"

lemma development_package_roots_in:
  "development_package_placement ` set development_package_entries\<subseteq>system_definitions development_package_program"
  using development_package_entries_sites development_package_compilation(3) by auto

lemma given_readers_roots_in:
  "given_readers_placement ` fset given_reader_entries\<subseteq>system_definitions given_readers_program"
  using given_rooted_entries given_readers_compilation(3) by auto

theorem given_package:
  "native_package_at (decode_finite_environment given_environment) given_use [] given_program"
  "system_definitions given_program=system_definitions development_package_program \<union> system_definitions given_readers_program"
  "environment_formed (decode_finite_environment given_environment)"
  "native_package_at (decode_finite_environment given_environment) development_package_use [] development_package_program"
  "native_package_at (decode_finite_environment given_environment) (snd given_readers_installed) [] given_readers_program"
  "environment_included (decode_finite_environment development_package_environment) (decode_finite_environment given_environment)"
  "given_use\<notin>fset (finite_environment_uses (fst given_readers_installed))"
proof -
  let ?K="fst given_readers_installed"
  let ?R1="development_package_placement ` set development_package_entries"
  let ?R2="given_readers_placement ` fset given_reader_entries"
  note dev_sites=reached_package_sites[OF given_development_package_kept development_package_roots_in development_package_reach]
  note rd_sites=reached_package_sites[OF given_readers_compilation(1) given_readers_roots_in given_readers_reach]
  have targets: "set given_roots\<subseteq>environment_positions (decode_finite_environment ?K)"
    using dev_sites(3) rd_sites(3) development_package_roots_in given_readers_roots_in by (auto simp: given_roots_set)
  obtain G v where sel: "given_selection=(G,v)" by (cases given_selection)
  note selected=finite_select_roots_correct[OF given_readers_installation(1) targets sel[unfolded given_selection_def]]
  have env: "given_environment=G" "given_use=v" unfolding given_environment_def given_use_def sel by simp_all
  have gf: "environment_formed (decode_finite_environment G)"
    using selected(1) by (simp only: finite_environment_formed_correct)
  have devG: "native_package_at (decode_finite_environment G) development_package_use [] development_package_program"
    by (rule native_package_included[OF given_development_package_kept selected(2) gf])
  have rdG: "native_package_at (decode_finite_environment G) (snd given_readers_installed) [] given_readers_program"
    by (rule native_package_included[OF given_readers_compilation(1) selected(2) gf])
  note dev_sitesG=reached_package_sites[OF devG development_package_roots_in development_package_reach]
  note rd_sitesG=reached_package_sites[OF rdG given_readers_roots_in given_readers_reach]
  have union: "native_definition_sites (decode_finite_environment G) (set given_roots)=
      system_definitions development_package_program \<union> system_definitions given_readers_program"
    unfolding given_roots_set native_definition_sites_union dev_sitesG(1) rd_sitesG(1) ..
  have formed: "native_package_formed (decode_finite_environment G) (set given_roots)"
    unfolding native_package_formed_def native_definition_sites_union given_roots_set
    using gf dev_sitesG(2) rd_sitesG(2) by blast
  have range: "rel_ran (set (zip (family_ports (length given_roots)) given_roots))=set given_roots"
    by (rule selected(5))
  show "native_package_at (decode_finite_environment given_environment) given_use [] given_program"
    unfolding given_program_def env native_package_at_def
    by (rule exI[where x="set (zip (family_ports (length given_roots)) given_roots)"])
      (simp only: selected(4) range formed simp_thms)
  show "system_definitions given_program=system_definitions development_package_program \<union>
      system_definitions given_readers_program"
    unfolding given_program_def env native_program_definitions[OF formed] union ..
  show "environment_formed (decode_finite_environment given_environment)" unfolding env by (rule gf)
  show "native_package_at (decode_finite_environment given_environment) development_package_use [] development_package_program"
    unfolding env by (rule devG)
  show "native_package_at (decode_finite_environment given_environment) (snd given_readers_installed) [] given_readers_program"
    unfolding env by (rule rdG)
  show "environment_included (decode_finite_environment development_package_environment) (decode_finite_environment given_environment)"
    unfolding env by (rule environment_included_trans[OF given_readers_installation(2) selected(2)])
  show "given_use\<notin>fset (finite_environment_uses ?K)" unfolding env by (rule selected(3))
qed

text \<open>
  The mapped extension's premises at the readers' own package, which stays in the given's environment: the
  form in which the guard's definitions are installed over the readers.
\<close>

lemma given_readers_extensible:
  "native_package_at (decode_finite_environment given_environment) (snd given_readers_installed) [] given_readers_program"
  "finite_system_formed finite_rooted_given_readers"
  "inj_on given_readers_placement (fset (finite_system_definitions finite_rooted_given_readers))"
  "system_alpha_variant (rename_system given_readers_placement (decode_finite_system finite_rooted_given_readers))
    given_readers_program"
  using given_package(5) finite_rooted_given_readers_formed given_readers_installation(3) given_readers_compilation(2)
  by (simp_all only: finite_system_definitions_correct finite_rooted_given_readers_exact)

section \<open>Every definition means at the given what it means in its own package\<close>

lemma given_development_meaning:
  assumes "d\<in>system_definitions development_package_program"
  shows "(d,t)\<in>positive_meaning given_program \<longleftrightarrow> (d,t)\<in>positive_meaning development_package_program"
  by (rule native_packages_shared_meaning[OF given_package(1) given_package(4)]) (use assms given_package(2) in auto)

lemma given_readers_meaning:
  assumes "d\<in>system_definitions given_rooted_readers_system"
  shows "(given_readers_placement d,t)\<in>positive_meaning given_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning given_rooted_readers_system"
proof -
  have member: "given_readers_placement d\<in>system_definitions given_readers_program"
    using assms given_readers_compilation(3) by simp
  have "(given_readers_placement d,t)\<in>positive_meaning given_program \<longleftrightarrow>
      (given_readers_placement d,t)\<in>positive_meaning given_readers_program"
    by (rule native_packages_shared_meaning[OF given_package(1) given_package(5)]) (use member given_package(2) in auto)
  then show ?thesis using given_installed_meaning[OF assms] by simp
qed

lemma given_development_entries:
  "development_package_placement (relocate_site 1 readiness_settled)\<in>system_definitions development_package_program"
  "development_package_placement (relocate_site 1 readiness_ready)\<in>system_definitions development_package_program"
  "development_package_placement reach_reached\<in>system_definitions development_package_program"
  "development_package_placement verdict_entry\<in>system_definitions development_package_program"
  "development_package_placement witness_excess\<in>system_definitions development_package_program"
  "development_package_placement witness_undeclared\<in>system_definitions development_package_program"
  "development_package_placement witness_malformed\<in>system_definitions development_package_program"
  "development_package_placement (relocate_site 2 request_entry)\<in>system_definitions development_package_program"
  "development_package_placement (relocate_site 2 request_admission)\<in>system_definitions development_package_program"
  "development_package_placement (decomposition_relocation decomposition_applies)\<in>system_definitions development_package_program"
  using development_package_roots_in by (auto simp: development_package_entries_def)

text \<open>Each notion's contract at its entry of the development package holds at the given, as an instance.\<close>

lemmas given_settled_exact=trans[OF given_development_meaning[OF given_development_entries(1)] development_package_settled_exact]
lemmas given_ready_exact=trans[OF given_development_meaning[OF given_development_entries(2)] development_package_ready_exact]
lemmas given_reached_exact=trans[OF given_development_meaning[OF given_development_entries(3)] development_package_reached_exact]
lemmas given_verdict_entry=trans[OF given_development_meaning[OF given_development_entries(4)] development_package_verdict_entry]
lemmas given_excess_witness_exact=
  trans[OF given_development_meaning[OF given_development_entries(5)] development_package_excess_witness_exact]
lemmas given_undeclared_witness_exact=
  trans[OF given_development_meaning[OF given_development_entries(6)] development_package_undeclared_witness_exact]
lemmas given_request_entry=trans[OF given_development_meaning[OF given_development_entries(8)] development_package_request_entry]
lemmas given_decomposition_applies=
  trans[OF given_development_meaning[OF given_development_entries(10)] development_package_decomposition_applies]

text \<open>Each reader's contract holds at the given at its placed entry, as an instance.\<close>

lemmas given_definition_call_admission_exact_at=given_rooted_definition_call_admission_exact[unfolded
  given_readers_meaning[OF given_entry_rooted[OF given_rooted_members(1)], symmetric]]
lemmas given_package_closure_admission_exact_at=given_rooted_package_closure_admission_exact[unfolded
  given_readers_meaning[OF given_entry_rooted[OF given_rooted_members(2)], symmetric]]
lemmas given_root_family_reading_exact_at=given_rooted_root_family_reading_exact[unfolded
  given_readers_meaning[OF given_entry_rooted[OF given_rooted_members(3)], symmetric]]
lemmas given_package_admission_exact_at=given_rooted_package_admission_exact[unfolded
  given_readers_meaning[OF given_entry_rooted[OF given_rooted_members(4)], symmetric]]
lemmas given_definition_clause_reading_exact_at=given_rooted_definition_clause_reading_exact[unfolded
  given_readers_meaning[OF given_entry_rooted[OF given_rooted_members(5)], symmetric]]
lemmas given_definition_edge_reading_exact_at=given_rooted_definition_edge_reading_exact[unfolded
  given_readers_meaning[OF given_entry_rooted[OF given_rooted_members(6)], symmetric]]
lemmas given_package_membership_exact_at=given_rooted_package_membership_exact[unfolded
  given_readers_meaning[OF given_entry_rooted[OF given_rooted_members(7)], symmetric]]
lemmas given_environment_inclusion_exact_at=given_rooted_environment_inclusion_exact[unfolded
  given_readers_meaning[OF given_entry_rooted[OF given_rooted_members(8)], symmetric]]
lemmas given_package_retention_admission_exact_at=given_rooted_package_retention_admission_exact[unfolded
  given_readers_meaning[OF given_entry_rooted[OF given_rooted_members(9)], symmetric]]
lemmas given_use_additions_on_values_at=given_rooted_use_additions_on_values[unfolded
  given_readers_meaning[OF given_entry_rooted[OF given_rooted_members(10)], symmetric]]
lemmas given_use_absence_exact_at=given_rooted_use_absence_exact[unfolded
  given_readers_meaning[OF given_entry_rooted[OF given_rooted_members(11)], symmetric]]
lemmas given_payload_audit_exact_at=given_rooted_payload_audit_exact[unfolded
  given_readers_meaning[OF given_entry_rooted[OF given_rooted_members(12)], symmetric]]

section \<open>The given's membership, read natively\<close>

corollary given_membership:
  assumes source: "environment_value_presents (decode_finite_environment given_environment) e"
  shows "(83,package_subject_argument e (use_data_term given_use) (Payload_Term []) (definition_site_value d))
      \<in>positive_meaning package_membership_system \<longleftrightarrow>
    d\<in>system_definitions development_package_program \<or> d\<in>system_definitions given_readers_program"
  using package_membership_at_package[OF source given_package(1)] given_package(2) by simp

section \<open>The given's payloads\<close>

theorem given_payloads:
  "system_payloads development_package_program={[]}"
  "system_payloads given_readers_program=system_payloads given_rooted_readers_system"
  "system_payloads given_program=system_payloads development_package_program \<union> system_payloads given_readers_program"
  "system_payloads given_program=insert [] (system_payloads given_rooted_readers_system)"
proof -
  show dev: "system_payloads development_package_program={[]}"
    by (simp add: system_alpha_variant_payloads[OF development_package(5)] system_payloads_rename package_payloads)
  show rd: "system_payloads given_readers_program=system_payloads given_rooted_readers_system"
    by (simp add: system_alpha_variant_payloads[OF given_readers_compilation(2)] system_payloads_rename)
  have gf: "schema_system_formed given_program" by (rule native_package_system_formed[OF given_package(1)])
  have fields: "definition_payloads (system_interface given_program d) (system_clause_family given_program d)=
      definition_payloads (system_interface P d) (system_clause_family P d)"
    if package: "native_package_at (decode_finite_environment given_environment) w [] P"
      and inside: "system_definitions P\<subseteq>system_definitions given_program" and member: "d\<in>system_definitions P"
    for P w d
  proof -
    have pf: "schema_system_formed P" by (rule native_package_system_formed[OF package])
    have agree: "systems_agree_on P given_program (system_definitions P \<inter> system_definitions given_program)"
      by (rule native_packages_agree_on_shared_definitions[OF package given_package(1)])
    have shared: "d\<in>system_definitions P \<inter> system_definitions given_program" using inside member by blast
    show ?thesis using systems_agree_on_fields[OF pf gf agree shared member] by simp
  qed
  have devf: "schema_system_formed development_package_program" by (rule native_package_system_formed[OF given_package(4)])
  have rdf: "schema_system_formed given_readers_program" by (rule native_package_system_formed[OF given_package(5)])
  have devin: "system_definitions development_package_program\<subseteq>system_definitions given_program"
    and rdin: "system_definitions given_readers_program\<subseteq>system_definitions given_program"
    using given_package(2) by blast+
  have devpart: "(\<Union>d\<in>system_definitions development_package_program.
      definition_payloads (system_interface given_program d) (system_clause_family given_program d))=
    system_payloads development_package_program"
    unfolding system_payloads_definitions[OF devf] by (rule SUP_cong[OF refl fields[OF given_package(4) devin]])
  have rdpart: "(\<Union>d\<in>system_definitions given_readers_program.
      definition_payloads (system_interface given_program d) (system_clause_family given_program d))=
    system_payloads given_readers_program"
    unfolding system_payloads_definitions[OF rdf] by (rule SUP_cong[OF refl fields[OF given_package(5) rdin]])
  have "system_payloads given_program=
      (\<Union>d\<in>system_definitions development_package_program.
        definition_payloads (system_interface given_program d) (system_clause_family given_program d)) \<union>
      (\<Union>d\<in>system_definitions given_readers_program.
        definition_payloads (system_interface given_program d) (system_clause_family given_program d))"
    by (simp only: system_payloads_definitions[OF gf] given_package(2) UN_Un)
  also have "\<dots>=system_payloads development_package_program \<union> system_payloads given_readers_program"
    by (simp only: devpart rdpart)
  finally show whole: "system_payloads given_program=system_payloads development_package_program \<union> system_payloads given_readers_program" .
  show "system_payloads given_program=insert [] (system_payloads given_rooted_readers_system)"
    unfolding whole dev rd by simp
qed

lemmas given_rooted_payloads_exact=finite_system_payloads_exact[of finite_rooted_given_readers,
  unfolded finite_rooted_given_readers_exact]

corollary given_payload_audit:
  assumes source: "environment_value_presents (decode_finite_environment given_environment) e"
  shows "(\<forall>d\<in>system_definitions given_program.
      (505,source_root_argument e (use_data_term (fst d)) (Payload_Term (snd d)))\<in>positive_meaning payload_audit_system)
    \<longleftrightarrow> system_payloads given_rooted_readers_system\<subseteq>{[]}"
  using payload_audit_package[OF source given_package(1)] by (simp add: given_payloads(4))

section \<open>The given's site value and its least scope\<close>

corollary given_site_value: "\<exists>z. site_value_presents (decode_finite_environment given_environment) given_use [] z"
  by (rule site_value_presents_total[OF given_package(3) native_package_root_position[OF given_package(1)]])

text \<open>
  Beyond its package's least scope the given's environment holds three root selectors, each kept: the
  development package's (its site stays the development package's), the empty package's of the closed
  installation route (the route's source, which the readers' installation extends), and the readers' (the site
  over which the guard's definitions are installed). None is reached from the given's site, so the given's
  environment is not closed at it and package retention is not admitted there; it is admitted at the given's
  least scope, the package environment the given's site retains.
\<close>

corollary given_least_scope_retention:
  assumes "site_value_presents (native_package_environment (decode_finite_environment given_environment) given_use [])
    given_use [] z"
  shows "(122,z)\<in>positive_meaning package_retention_admission_system"
  using package_retention_admission_on_values[OF assms] native_package_closed_restriction[OF given_package(1)] by blast

section \<open>The construction executed\<close>

text \<open>
  The given's environment is computed over the development package's kept environment, and its package read
  back by the native package reader, over the reader's refinements (\<open>Native_Execution_Refinements\<close>): its
  size in addresses and the number of definitions read back, the development package's and the readers'.
\<close>

value "(fcard (finite_environment_positions development_package_environment),
  fcard (finite_environment_positions given_environment),
  map_option (\<lambda>P. fcard (finite_system_definitions P)) (finite_native_source given_environment given_use []))"

end
