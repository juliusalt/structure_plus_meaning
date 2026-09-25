theory Development_First_Problem_Asked
  imports Development_First_Problem_Guard Development_Given_Installation Factor_Program_Entry_Values
    Factor_Use_Renaming
begin

text \<open>
  The first problem's asked relation as native content (DECISIONS.md "The native loop's first problem is what
  a problem is; the problem of Q2, second, exercises its answer", its least form): a native program's entry,
  read at the pair of a given and a candidate. The program is the guard's (\<open>Development_First_Problem_Guard\<close>)
  joined with the given's readers' joined program and rooted at the given's reader entries and the guard's
  entry, so that it agrees with the readers the given carries on all their definitions; it is installed over
  the given's reader package by the mapped extension, the readers at their installed sites and the guard's
  definitions at fresh uses. The installed entry means the guard's contract, and its relation over pairs of
  site values is equivariant under use permutations, one permutation acting on both members of the pair.
\<close>

section \<open>The asked relation's program: the guard's views joined with the given's readers, rooted\<close>

lemma asked_guard_formed [simp]: "schema_system_formed first_problem_guard_system"
  by (rule first_problem_guard.guarded_formed)

lemma asked_guard_definitions:
  "system_definitions first_problem_guard_system=insert 526 (system_definitions first_problem_goals_system)"
  by (simp add: install_requirement_guard_def added_view_definitions)

lemma asked_numbers_fresh:
  assumes "d\<in>{520,521,522,523,524,525,526}"
  shows "d\<notin>system_definitions given_program_system"
proof -
  have "d\<notin>system_definitions guard_readers_system" by (rule guard_fresh) (use assms in auto)
  moreover have "d\<notin>system_definitions granted_readers_system" using assms granted_readers_bound by auto
  ultimately show ?thesis by (simp only: given_program_definitions Un_iff) blast
qed

lemma asked_overlap:
  "system_definitions given_program_system\<inter>system_definitions first_problem_guard_system\<subseteq>
    system_definitions guard_readers_system"
proof
  fix x assume x: "x\<in>system_definitions given_program_system\<inter>system_definitions first_problem_guard_system"
  have "x\<in>{520,521,522,523,524,525,526} \<or> x\<in>system_definitions guard_readers_system"
    using x by (auto simp: asked_guard_definitions)
  then show "x\<in>system_definitions guard_readers_system" using x asked_numbers_fresh by blast
qed

lemma asked_overlap_agreement:
  "systems_agree_on given_program_system first_problem_guard_system
    (system_definitions given_program_system\<inter>system_definitions first_problem_guard_system)"
proof -
  have readers: "systems_agree_on given_program_system guard_readers_system (system_definitions guard_readers_system)"
    by (rule systems_agree_on_sym[OF guard_program_agreement])
  have inside: "system_definitions guard_readers_system\<subseteq>system_definitions first_problem_goals_system" by auto
  have guard: "systems_agree_on guard_readers_system first_problem_guard_system (system_definitions guard_readers_system)"
    by (rule systems_agree_on_transitive[OF goals_extension_agreement
      systems_agree_on_subdomain[OF first_problem_guard.guarded_old_agreement inside]])
  show ?thesis
    by (rule systems_agree_on_subdomain[OF systems_agree_on_transitive[OF readers guard] asked_overlap])
qed

definition asked_joined_system :: "(nat,nat,nat,nat) schema_system" where
  "asked_joined_system=system_union given_program_system first_problem_guard_system"

lemma asked_joined_formed [simp]: "schema_system_formed asked_joined_system"
  unfolding asked_joined_system_def
  by (rule system_union_agree_formed[OF given_program_formed asked_guard_formed asked_overlap_agreement])

lemma asked_joined_definitions:
  "system_definitions asked_joined_system=system_definitions given_program_system\<union>
    system_definitions first_problem_guard_system"
  by (simp only: asked_joined_system_def system_union_definitions)

lemma asked_guard_meaning_joined:
  assumes "d\<in>system_definitions first_problem_guard_system"
  shows "(d,t)\<in>positive_meaning asked_joined_system \<longleftrightarrow> (d,t)\<in>positive_meaning first_problem_guard_system"
  by (rule whole_system_agreement_meaning[OF asked_guard_formed asked_joined_formed
    system_union_agree_right[OF given_program_formed asked_overlap_agreement, folded asked_joined_system_def] assms])

text \<open>
  The roots: every entry the given's readers are rooted at, and the guard's entry. Rooting keeps the least
  program these roots reach (@{const rooted_system}), which holds the readers the given carries and the
  guard's views.
\<close>

definition asked_roots :: "nat fset" where
  "asked_roots=given_reader_entries |\<union>| {|526|}"

definition asked_program_system :: "(nat,nat,nat,nat) schema_system" where
  "asked_program_system=rooted_system asked_joined_system (fset asked_roots)"

lemma asked_roots_joined: "fset asked_roots\<subseteq>system_definitions asked_joined_system"
  using given_reader_entries_program by (auto simp: asked_roots_def asked_joined_definitions asked_guard_definitions)

lemma asked_program_formed [simp]: "schema_system_formed asked_program_system"
  unfolding asked_program_system_def by (rule rooted_system_formed[OF asked_joined_formed])

lemma asked_program_definitions:
  "system_definitions asked_program_system=system_definition_closure asked_joined_system (fset asked_roots)"
  unfolding asked_program_system_def by (rule rooted_system_definitions[OF asked_joined_formed asked_roots_joined])

lemma asked_entry_member: "526\<in>system_definitions asked_program_system"
  using rooted_system_roots[OF asked_joined_formed asked_roots_joined]
  unfolding asked_program_system_def by (auto simp: asked_roots_def)

theorem asked_program_guard_meaning:
  assumes "d\<in>system_definitions asked_program_system" and "d\<in>system_definitions first_problem_guard_system"
  shows "(d,t)\<in>positive_meaning asked_program_system \<longleftrightarrow> (d,t)\<in>positive_meaning first_problem_guard_system"
  using rooted_system_meaning_at[OF asked_joined_formed assms(1)[unfolded asked_program_system_def]]
    asked_guard_meaning_joined[OF assms(2)] unfolding asked_program_system_def by blast

text \<open>The program keeps every definition of the readers the given carries, and agrees with them there.\<close>

lemma asked_readers_inside:
  "system_definitions given_rooted_readers_system\<subseteq>system_definitions asked_program_system"
proof -
  have clauses: "system_clauses given_program_system\<subseteq>system_clauses asked_joined_system"
    unfolding asked_joined_system_def system_union_def by (simp only: schema_system.select_convs Un_upper1)
  have edges: "system_dependency_edges given_program_system\<subseteq>system_dependency_edges asked_joined_system"
  proof
    fix x assume "x\<in>system_dependency_edges given_program_system"
    then obtain d e c S where x: "x=(d,e)" and cl: "((d,c),S)\<in>system_clauses given_program_system"
      and dep: "e\<in>schema_dependencies S"
      by (auto simp only: system_dependency_edges_def mem_Collect_eq split: prod.splits)
    have "((d,c),S)\<in>system_clauses asked_joined_system" by (rule subsetD[OF clauses cl])
    then show "x\<in>system_dependency_edges asked_joined_system"
      using dep unfolding x system_dependency_edges_def by auto
  qed
  have closed: "system_dependency_closed given_program_system
      (system_definition_closure asked_joined_system (fset asked_roots))"
    unfolding system_dependency_closed_def
  proof (intro ballI allI impI)
    fix d e assume member: "d\<in>system_definition_closure asked_joined_system (fset asked_roots)"
      and edge: "(d,e)\<in>system_dependency_edges given_program_system"
    show "e\<in>system_definition_closure asked_joined_system (fset asked_roots)"
      by (rule system_definition_closure_step[OF member subsetD[OF edges edge]])
  qed
  have roots: "fset given_reader_entries\<subseteq>system_definition_closure asked_joined_system (fset asked_roots)"
    using system_definition_closure_roots[of "fset asked_roots" asked_joined_system] by (auto simp: asked_roots_def)
  show ?thesis
    unfolding given_rooted_readers_system_def asked_program_definitions
      rooted_system_definitions[OF given_program_formed given_reader_entries_program]
    by (rule system_definition_closure_least[OF roots closed])
qed

theorem asked_readers_agreement:
  "systems_agree_on given_rooted_readers_system asked_program_system (system_definitions given_rooted_readers_system)"
proof -
  have rooted: "systems_agree_on given_rooted_readers_system given_program_system
      (system_definitions given_rooted_readers_system)"
    unfolding given_rooted_readers_system_def by (rule systems_agree_on_sym[OF rooted_system_agreement])
  have sub: "system_definitions given_rooted_readers_system\<subseteq>system_definitions given_program_system"
    unfolding given_rooted_readers_system_def by (rule rooted_system_subdomain)
  have joined: "systems_agree_on given_program_system asked_joined_system (system_definitions given_rooted_readers_system)"
    by (rule systems_agree_on_subdomain[OF system_union_agree_left[OF asked_guard_formed asked_overlap_agreement,
      folded asked_joined_system_def] sub])
  have asked: "systems_agree_on asked_joined_system asked_program_system (system_definitions given_rooted_readers_system)"
    by (rule systems_agree_on_subdomain[OF rooted_system_agreement[of asked_joined_system "fset asked_roots",
      folded asked_program_system_def] asked_readers_inside])
  show ?thesis by (rule systems_agree_on_transitive[OF systems_agree_on_transitive[OF rooted joined] asked])
qed

section \<open>Its finite presentation, derived from its parts'\<close>

text \<open>
  The joined program's presentation is the finite union of the given's joined program's piece
  (@{const finite_given_program}) and the guard's, which is the given's readers' piece
  (@{const finite_given_readers}) extended by the guard's view steps; the asked program is its restriction to
  the closure its roots compute (@{thm [source] finite_system_of_rooted}). No piece is reduced again.
\<close>

definition finite_asked_joined_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_asked_joined_program=finite_system_of asked_joined_system"

local_setup \<open>Native_Finite_Equations.note_composed @{binding finite_asked_joined_program_code}
  @{thm finite_asked_joined_program_def} [@{thm finite_given_program_def}, @{thm finite_given_readers_def}] []\<close>

definition finite_asked_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_asked_program=finite_system_of asked_program_system"

lemma finite_asked_program_code [code]:
  "finite_asked_program=finite_system_restriction finite_asked_joined_program
    (finite_definition_closure finite_asked_joined_program asked_roots)"
  unfolding finite_asked_program_def finite_asked_joined_program_def asked_program_system_def
  by (rule finite_system_of_rooted[OF asked_joined_formed])

lemma finite_asked_program_exact: "decode_finite_system finite_asked_program=asked_program_system"
  unfolding finite_asked_program_def by (rule decode_finite_system_of[OF asked_program_formed])

lemma finite_asked_program_formed: "finite_system_formed finite_asked_program"
  by (simp only: finite_system_formed_correct finite_asked_program_exact asked_program_formed)

theorem finite_asked_program_extends:
  "systems_agree_on (decode_finite_system finite_rooted_given_readers) (decode_finite_system finite_asked_program)
    (system_definitions (decode_finite_system finite_rooted_given_readers))"
  by (simp only: finite_rooted_given_readers_exact finite_asked_program_exact asked_readers_agreement)

section \<open>The installation over the given's reader package\<close>

interpretation asked_installation: finite_mapped_native_extension given_environment finite_rooted_given_readers
    finite_asked_program "snd given_readers_installed" "[]" given_readers_program given_readers_placement
  by (rule finite_mapped_native_extension.intro[OF given_readers_extensible(1,2) finite_asked_program_formed
    finite_asked_program_extends given_readers_extensible(3,4)])

definition asked_placement :: "nat \<Rightarrow> local_address option definition_site" where
  "asked_placement=finite_program_coordinates given_environment (finite_system_definitions finite_rooted_given_readers)
    (finite_system_definitions finite_asked_program) given_readers_placement"

definition asked_installed :: "local_address option finite_artifact_environment\<times>local_address option" where
  "asked_installed=the (finite_extend_mapped_native given_environment finite_rooted_given_readers finite_asked_program
    given_readers_placement)"

lemma asked_built:
  "finite_extend_mapped_native given_environment finite_rooted_given_readers finite_asked_program
    given_readers_placement=Some asked_installed"
  using asked_installation.total unfolding asked_installed_def by auto

definition asked_environment :: "local_address option finite_artifact_environment" where
  "asked_environment=fst asked_installed"

definition asked_use :: "local_address option" where
  "asked_use=snd asked_installed"

definition asked_entry :: "local_address option definition_site" where
  "asked_entry=asked_placement 526"

lemma asked_correct:
  "finite_environment_formed asked_environment \<and>
    environment_included (decode_finite_environment given_environment) (decode_finite_environment asked_environment) \<and>
    native_package_at (decode_finite_environment asked_environment) (snd given_readers_installed) [] given_readers_program \<and>
    inj_on asked_placement (system_definitions asked_program_system) \<and>
    (\<forall>d\<in>system_definitions given_rooted_readers_system. asked_placement d=given_readers_placement d) \<and>
    (\<exists>T. native_package_at (decode_finite_environment asked_environment) asked_use [] T \<and>
      system_alpha_variant (rename_system asked_placement asked_program_system) T \<and>
      system_definitions T=asked_placement ` system_definitions asked_program_system \<and>
      positive_meaning T=map_prod asked_placement id ` positive_meaning asked_program_system \<and>
      (\<forall>d\<in>system_definitions asked_program_system. \<forall>t.
        schema_call_formed T (asked_placement d) t \<longleftrightarrow> schema_call_formed asked_program_system d t)) \<and>
    (\<forall>w\<in>fset (finite_environment_uses given_environment). \<forall>A.
      artifact_at (decode_finite_environment asked_environment) w A \<longleftrightarrow> artifact_at (decode_finite_environment given_environment) w A) \<and>
    (\<forall>w\<in>fset (finite_environment_uses given_environment). \<forall>k v.
      binds_slot (decode_finite_environment asked_environment) w k v \<longleftrightarrow> binds_slot (decode_finite_environment given_environment) w k v)"
proof -
  have built: "finite_extend_mapped_native given_environment finite_rooted_given_readers finite_asked_program
      given_readers_placement=Some (fst asked_installed,snd asked_installed)"
    using asked_built by simp
  show ?thesis
  using asked_installation.correct[OF built]
  unfolding asked_placement_def[symmetric] asked_environment_def[symmetric] asked_use_def[symmetric]
    finite_system_definitions_correct finite_asked_program_exact finite_rooted_given_readers_exact .
qed

definition asked_program :: "local_address option native_system" where
  "asked_program=(THE T. native_package_at (decode_finite_environment asked_environment) asked_use [] T)"

theorem asked_installation:
  "finite_environment_formed asked_environment"
  "environment_included (decode_finite_environment given_environment) (decode_finite_environment asked_environment)"
  "native_package_at (decode_finite_environment asked_environment) (snd given_readers_installed) [] given_readers_program"
  "\<forall>d\<in>system_definitions given_rooted_readers_system. asked_placement d=given_readers_placement d"
  "inj_on asked_placement (system_definitions asked_program_system)"
  "native_package_at (decode_finite_environment asked_environment) asked_use [] asked_program"
  "system_alpha_variant (rename_system asked_placement asked_program_system) asked_program"
  "system_definitions asked_program=asked_placement ` system_definitions asked_program_system"
  "positive_meaning asked_program=map_prod asked_placement id ` positive_meaning asked_program_system"
  "\<forall>w\<in>fset (finite_environment_uses given_environment). \<forall>A.
    artifact_at (decode_finite_environment asked_environment) w A \<longleftrightarrow> artifact_at (decode_finite_environment given_environment) w A"
  "\<forall>w\<in>fset (finite_environment_uses given_environment). \<forall>k v.
    binds_slot (decode_finite_environment asked_environment) w k v \<longleftrightarrow> binds_slot (decode_finite_environment given_environment) w k v"
proof -
  note c=asked_correct
  have ex: "\<exists>T. native_package_at (decode_finite_environment asked_environment) asked_use [] T \<and>
      system_alpha_variant (rename_system asked_placement asked_program_system) T \<and>
      system_definitions T=asked_placement ` system_definitions asked_program_system \<and>
      positive_meaning T=map_prod asked_placement id ` positive_meaning asked_program_system \<and>
      (\<forall>d\<in>system_definitions asked_program_system. \<forall>t.
        schema_call_formed T (asked_placement d) t \<longleftrightarrow> schema_call_formed asked_program_system d t)"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF c]]]]]])
  have program: "native_package_at (decode_finite_environment asked_environment) asked_use [] asked_program \<and>
      system_alpha_variant (rename_system asked_placement asked_program_system) asked_program \<and>
      system_definitions asked_program=asked_placement ` system_definitions asked_program_system \<and>
      positive_meaning asked_program=map_prod asked_placement id ` positive_meaning asked_program_system"
    using ex
  proof (rule exE)
    fix T assume T0: "native_package_at (decode_finite_environment asked_environment) asked_use [] T \<and>
      system_alpha_variant (rename_system asked_placement asked_program_system) T \<and>
      system_definitions T=asked_placement ` system_definitions asked_program_system \<and>
      positive_meaning T=map_prod asked_placement id ` positive_meaning asked_program_system \<and>
      (\<forall>d\<in>system_definitions asked_program_system. \<forall>t.
        schema_call_formed T (asked_placement d) t \<longleftrightarrow> schema_call_formed asked_program_system d t)"
    have package: "native_package_at (decode_finite_environment asked_environment) asked_use [] T"
      by (rule conjunct1[OF T0])
    have same: "asked_program=T" unfolding asked_program_def
      by (rule the_equality[where P="\<lambda>T. native_package_at (decode_finite_environment asked_environment) asked_use [] T",
        OF package]) (rule native_package_unique[OF _ package])
    show ?thesis unfolding same
      by (intro conjI conjunct1[OF T0] conjunct1[OF conjunct2[OF T0]] conjunct1[OF conjunct2[OF conjunct2[OF T0]]]
        conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF T0]]]])
  qed
  show "finite_environment_formed asked_environment" by (rule conjunct1[OF c])
  show "environment_included (decode_finite_environment given_environment) (decode_finite_environment asked_environment)"
    by (rule conjunct1[OF conjunct2[OF c]])
  show "native_package_at (decode_finite_environment asked_environment) (snd given_readers_installed) [] given_readers_program"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF c]]])
  show "inj_on asked_placement (system_definitions asked_program_system)"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF c]]]])
  show "\<forall>d\<in>system_definitions given_rooted_readers_system. asked_placement d=given_readers_placement d"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF c]]]]])
  show "\<forall>w\<in>fset (finite_environment_uses given_environment). \<forall>A.
      artifact_at (decode_finite_environment asked_environment) w A \<longleftrightarrow> artifact_at (decode_finite_environment given_environment) w A"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF c]]]]]]])
  show "\<forall>w\<in>fset (finite_environment_uses given_environment). \<forall>k v.
      binds_slot (decode_finite_environment asked_environment) w k v \<longleftrightarrow> binds_slot (decode_finite_environment given_environment) w k v"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF c]]]]]]])
  show "native_package_at (decode_finite_environment asked_environment) asked_use [] asked_program"
    "system_alpha_variant (rename_system asked_placement asked_program_system) asked_program"
    "system_definitions asked_program=asked_placement ` system_definitions asked_program_system"
    "positive_meaning asked_program=map_prod asked_placement id ` positive_meaning asked_program_system"
    by (rule conjunct1[OF program], rule conjunct1[OF conjunct2[OF program]],
      rule conjunct1[OF conjunct2[OF conjunct2[OF program]]], rule conjunct2[OF conjunct2[OF conjunct2[OF program]]])
qed

text \<open>The guard's definitions stand at uses fresh in the given's environment, each at an artifact root.\<close>

lemmas asked_fresh=asked_installation.coordinates(3,4)[folded asked_placement_def,
  unfolded finite_system_definitions_correct finite_asked_program_exact finite_rooted_given_readers_exact]

section \<open>The guard's contract at the installed entry\<close>

lemma asked_installed_meaning:
  assumes "d\<in>system_definitions asked_program_system"
  shows "(asked_placement d,t)\<in>positive_meaning asked_program \<longleftrightarrow> (d,t)\<in>positive_meaning asked_program_system"
  by (rule system_variant_renamed_meaning_at[OF asked_program_formed asked_installation(5,7) assms])

lemma asked_entry_meaning:
  "(asked_entry,t)\<in>positive_meaning asked_program \<longleftrightarrow> (526,t)\<in>positive_meaning first_problem_guard_system"
  unfolding asked_entry_def asked_installed_meaning[OF asked_entry_member]
  by (rule asked_program_guard_meaning[OF asked_entry_member]) (simp add: asked_guard_definitions)

theorem asked_entry_contract:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "(asked_entry,Pair_Term t w)\<in>positive_meaning asked_program \<longleftrightarrow>
    environment_included E F \<and> (\<exists>R. native_package_at F v s R \<and>
      (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
        fst d\<notin>environment_uses E) \<and>
      (\<forall>d\<in>system_definitions R. fst d\<notin>environment_uses E \<longrightarrow>
        (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})))"
  unfolding asked_entry_meaning by (rule first_problem_guard_contract[OF first second])

section \<open>The asked relation's term\<close>

lemma asked_entry_positions:
  "(asked_use,[])\<in>environment_positions (decode_finite_environment asked_environment)"
  "asked_entry\<in>environment_positions (decode_finite_environment asked_environment)"
proof -
  show "(asked_use,[])\<in>environment_positions (decode_finite_environment asked_environment)"
    by (rule native_package_site_position[OF asked_installation(6)])
  have "asked_placement ` system_definitions asked_program_system\<subseteq>
      environment_positions (decode_finite_environment asked_environment)"
    by (rule native_renamed_source_positions[OF asked_installation(6,7)])
  then show "asked_entry\<in>environment_positions (decode_finite_environment asked_environment)"
    using asked_entry_member unfolding asked_entry_def by blast
qed

theorem asked_entry_term:
  "\<exists>t. program_entry_value_presents (decode_finite_environment asked_environment) asked_use [] asked_entry t"
  "program_entry_value_presents (decode_finite_environment asked_environment) asked_use [] asked_entry t \<Longrightarrow>
    program_entry_value_presents F v s e t \<Longrightarrow>
    F=decode_finite_environment asked_environment \<and> v=asked_use \<and> s=[] \<and> e=asked_entry"
  "program_entry_value_presents (decode_finite_environment asked_environment) asked_use [] asked_entry t \<Longrightarrow>
    term_formed t \<and> self_contained_term t"
proof -
  have formed: "environment_formed (decode_finite_environment asked_environment)"
    using asked_installation(1) by (simp only: finite_environment_formed_correct)
  show "\<exists>t. program_entry_value_presents (decode_finite_environment asked_environment) asked_use [] asked_entry t"
    by (rule program_entry_value_presents_total[OF formed asked_entry_positions])
  show "program_entry_value_presents (decode_finite_environment asked_environment) asked_use [] asked_entry t \<Longrightarrow>
      program_entry_value_presents F v s e t \<Longrightarrow>
      F=decode_finite_environment asked_environment \<and> v=asked_use \<and> s=[] \<and> e=asked_entry"
    by (drule (1) program_entry_value_presents_unique) auto
  show "program_entry_value_presents (decode_finite_environment asked_environment) asked_use [] asked_entry t \<Longrightarrow>
      term_formed t \<and> self_contained_term t"
    by (drule program_entry_value_presents_formed) blast
qed

section \<open>The asked relation is equivariant under use permutations\<close>

text \<open>
  The relation over a pair of site contexts, the given's first: the four goals' conjunction. One permutation of
  uses acts on both members (@{const package_additions_renaming}). Each goal's clause is its reader's:
  environment inclusion's (@{thm [source] environment_inclusion_equivariant}), package admission's
  (@{thm [source] package_admission_equivariant}), and the additions notion's at the callee boundary's and at
  the audit's (@{thm [source] package_additions_equivariant} with @{thm [source] use_absence_callee_equivariant}
  and @{thm [source] audit_callee_equivariant}); the conjunction is the notion's construction.
\<close>

definition asked_relation :: "site_context\<times>site_context \<Rightarrow> bool" where
  "asked_relation z \<longleftrightarrow> environment_included (fst (fst z)) (fst (snd z)) \<and>
    (\<exists>R. native_package_at (fst (snd z)) (fst (snd (snd z))) (snd (snd (snd z))) R) \<and>
    package_additions_relation (\<lambda>E u r F v s d. fst d\<notin>environment_uses E) z \<and>
    package_additions_relation
      (\<lambda>E u r F v s d. \<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]}) z"

theorem asked_entry_on_values:
  assumes first: "site_value_presents E u r t" and second: "site_value_presents F v s w"
  shows "(asked_entry,Pair_Term t w)\<in>positive_meaning asked_program \<longleftrightarrow> asked_relation ((E,u,r),(F,v,s))"
  unfolding asked_entry_meaning first_problem_guard_on_values[OF first second] asked_relation_def by simp

lemma asked_inclusion_equivariant:
  "renaming_equivariant bij package_additions_renaming (\<lambda>z. site_context_formed (fst z) \<and> site_context_formed (snd z))
    (\<lambda>z. environment_included (fst (fst z)) (fst (snd z)))"
proof (unfold renaming_equivariant_def, intro allI impI)
  fix h :: "local_address option \<Rightarrow> local_address option" and z :: "site_context\<times>site_context"
  assume h: "bij h" and formed: "site_context_formed (fst z) \<and> site_context_formed (snd z)"
  show "environment_included (fst (fst (package_additions_renaming h z))) (fst (snd (package_additions_renaming h z))) \<longleftrightarrow>
      environment_included (fst (fst z)) (fst (snd z))"
    using environment_inclusion_equivariant[unfolded renaming_equivariant_def, rule_format, of h "(fst (fst z),fst (snd z))"]
      h formed by (simp add: product_action_def)
qed

lemma asked_admission_equivariant:
  "renaming_equivariant bij package_additions_renaming (\<lambda>z. site_context_formed (fst z) \<and> site_context_formed (snd z))
    (\<lambda>z. \<exists>R. native_package_at (fst (snd z)) (fst (snd (snd z))) (snd (snd (snd z))) R)"
proof (unfold renaming_equivariant_def, intro allI impI)
  fix h :: "local_address option \<Rightarrow> local_address option" and z :: "site_context\<times>site_context"
  assume h: "bij h" and formed: "site_context_formed (fst z) \<and> site_context_formed (snd z)"
  show "(\<exists>R. native_package_at (fst (snd (package_additions_renaming h z))) (fst (snd (snd (package_additions_renaming h z))))
      (snd (snd (snd (package_additions_renaming h z)))) R) \<longleftrightarrow>
      (\<exists>R. native_package_at (fst (snd z)) (fst (snd (snd z))) (snd (snd (snd z))) R)"
    using package_admission_equivariant[unfolded renaming_equivariant_def, rule_format, of h "snd z"] h formed
    by (simp add: product_action_def)
qed

theorem asked_relation_equivariant:
  "renaming_equivariant bij package_additions_renaming (\<lambda>z. site_context_formed (fst z) \<and> site_context_formed (snd z))
    asked_relation"
  unfolding asked_relation_def
  by (intro renaming_equivariant_conj asked_inclusion_equivariant asked_admission_equivariant
    package_additions_equivariant[OF use_absence_callee_equivariant]
    package_additions_equivariant[OF audit_callee_equivariant])

text \<open>
  The installed entry is non-nominal by the notion's contract (@{thm [source] presented_predicate_renaming}):
  it is exact to the asked relation presented on pairs of site values, so it is invariant along every
  renaming correspondence of the pair.
\<close>

lemma asked_entry_presented:
  "(asked_entry,p)\<in>positive_meaning asked_program \<longleftrightarrow>
    presented_predicate (factor_pair_presents (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
      (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)) asked_relation p"
proof
  assume holds: "(asked_entry,p)\<in>positive_meaning asked_program"
  have guard: "(526,p)\<in>positive_meaning first_problem_guard_system" using holds by (simp only: asked_entry_meaning)
  have "(392,p)\<in>positive_meaning first_problem_guard_system"
    using first_problem_guard_refusal[of 2 392 p] guard by (auto simp: first_problem_requirements_def)
  then have "(392,p)\<in>positive_meaning use_additions_system"
    by (simp only: first_problem_guard.unchanged_original_meaning[OF goal_sites(3)] first_problem_goals_components(4))
  then have "package_additions_result (\<lambda>t. (393,t)\<in>positive_meaning use_additions_system) p"
    by (simp only: use_additions.exact)
  then obtain E u r t F v s w where p: "p=Pair_Term t w" and first: "site_value_presents E u r t"
    and second: "site_value_presents F v s w" by blast
  have relation: "asked_relation ((E,u,r),(F,v,s))"
    by (rule iffD1[OF asked_entry_on_values[OF first second] holds[unfolded p]])
  have presents: "factor_pair_presents (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
      (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t) ((E,u,r),(F,v,s)) p"
    using first second unfolding p factor_pair_presents_def by simp
  show "presented_predicate (factor_pair_presents (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
      (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)) asked_relation p"
    unfolding presented_predicate_def by (rule exI[where x="((E,u,r),(F,v,s))"]) (rule conjI[OF presents relation])
next
  assume "presented_predicate (factor_pair_presents (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
      (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)) asked_relation p"
  then obtain z where presents: "factor_pair_presents (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
      (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t) z p" and holds: "asked_relation z"
    unfolding presented_predicate_def by blast
  obtain t w where p: "p=Pair_Term t w"
    and first: "site_value_presents (fst (fst z)) (fst (snd (fst z))) (snd (snd (fst z))) t"
    and second: "site_value_presents (fst (snd z)) (fst (snd (snd z))) (snd (snd (snd z))) w"
    using presents unfolding factor_pair_presents_def by blast
  have "asked_relation ((fst (fst z),fst (snd (fst z)),snd (snd (fst z))),(fst (snd z),fst (snd (snd z)),snd (snd (snd z))))"
    using holds by simp
  then show "(asked_entry,p)\<in>positive_meaning asked_program"
    unfolding p by (rule iffD2[OF asked_entry_on_values[OF first second]])
qed

corollary asked_entry_renaming:
  "\<forall>h. bij h \<longrightarrow> rel_fun (renaming_correspondence
      (factor_pair_presents (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)
        (\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t)) package_additions_renaming h) (=)
    (\<lambda>p. (asked_entry,p)\<in>positive_meaning asked_program) (\<lambda>p. (asked_entry,p)\<in>positive_meaning asked_program)"
proof -
  let ?S="\<lambda>z t. site_value_presents (fst z) (fst (snd z)) (snd (snd z)) t"
  have presented: "presentation_class (factor_pair_presents ?S ?S)
      (\<lambda>z. site_context_formed (fst z) \<and> site_context_formed (snd z)) (\<lambda>p. \<exists>z. factor_pair_presents ?S ?S z p)"
    using presentation_class.recovered_admission[OF factor_pair_class[OF site_presentations.presentation_class_axioms
      site_presentations.presentation_class_axioms]] by simp
  have action: "renaming_action bij package_additions_renaming
      (\<lambda>z. site_context_formed (fst z) \<and> site_context_formed (snd z))"
    by (rule renaming_action_product[OF site_context_renaming_action site_context_renaming_action])
  show ?thesis
    by (rule iffD2[OF presented_predicate_renaming[OF presented action asked_entry_presented] asked_relation_equivariant])
qed

text \<open>
  Installing the guard's program over the given's readers is a choice made outside the native process, a
  residual as the seed's installation is. The given is unchanged: the asked relation stands in an environment
  that includes it, and a candidate's environment includes the given's, not this one.
\<close>

end
