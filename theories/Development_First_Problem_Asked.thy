theory Development_First_Problem_Asked
  imports Development_First_Problem_Guard Development_First_Problem_Additions Development_Given_Extensions
    Factor_Program_Entry_Values Factor_Use_Renaming
begin

text \<open>
  The first problem's asked relation as native content (DECISIONS.md "The native loop's first problem is what
  a problem is; the problem of Q2, second, exercises its answer", its least form): a native program's entry,
  read at the pair of a given and a candidate. The program is the guard's (\<open>Development_First_Problem_Guard\<close>)
  joined with the given's readers' joined program and rooted at the given's reader entries and the guard's
  entry, so that it agrees with the readers the given carries on all their definitions; it is installed over
  the given's reader package by the mapped extension, the readers at their installed sites and the guard's
  definitions at fresh uses, as every extension of the readers is (\<open>Development_Given_Extensions\<close>). The
  installed entry means the guard's contract, and its relation over pairs of site values is equivariant under
  use permutations, one permutation acting on both members of the pair.
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

lemma asked_given_agreement:
  "systems_agree_on given_program_system asked_joined_system (system_definitions given_program_system)"
  by (rule system_union_agree_left[OF asked_guard_formed asked_overlap_agreement, folded asked_joined_system_def])

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

text \<open>
  The program keeps every definition of the readers the given carries, and agrees with them there
  (@{thm [source] rooted_system_agreement_inside}).
\<close>

lemma asked_entries_roots: "fset given_reader_entries\<subseteq>fset asked_roots"
  by (auto simp: asked_roots_def)

lemma asked_readers_inside:
  "system_definitions given_rooted_readers_system\<subseteq>system_definitions asked_program_system"
  unfolding given_rooted_readers_system_def asked_program_system_def
  by (rule rooted_system_agreement_inside(1)[OF given_program_formed asked_joined_formed asked_given_agreement
    given_reader_entries_program asked_entries_roots])

theorem asked_readers_agreement:
  "systems_agree_on given_rooted_readers_system asked_program_system (system_definitions given_rooted_readers_system)"
  unfolding given_rooted_readers_system_def asked_program_system_def
  by (rule rooted_system_agreement_inside(2)[OF given_program_formed asked_joined_formed asked_given_agreement
    given_reader_entries_program asked_entries_roots])

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

text \<open>
  The asked program extends the given's readers, so it is installed over their package as every such extension is:
  the instance of @{text given_readers_extension} at its finite presentation.
\<close>

interpretation asked_extension: given_readers_extension finite_asked_program
  by (rule given_readers_extension.intro[OF finite_asked_program_formed])
    (simp only: finite_asked_program_exact asked_readers_agreement)

definition asked_placement :: "nat \<Rightarrow> local_address option definition_site" where
  "asked_placement=given_readers_extension.installed_placement finite_asked_program"

definition asked_installed :: "local_address option finite_artifact_environment\<times>local_address option" where
  "asked_installed=given_readers_extension.installed finite_asked_program"

lemma asked_built:
  "finite_extend_mapped_native given_environment finite_rooted_given_readers finite_asked_program
    given_readers_placement=Some asked_installed"
  unfolding asked_installed_def by (rule asked_extension.built)

definition asked_environment :: "local_address option finite_artifact_environment" where
  "asked_environment=given_readers_extension.installed_environment finite_asked_program"

definition asked_use :: "local_address option" where
  "asked_use=given_readers_extension.installed_use finite_asked_program"

definition asked_entry :: "local_address option definition_site" where
  "asked_entry=asked_placement 526"

text \<open>
  The asked installation's constants are defined through the interpretation of @{text given_readers_extension}; their
  code equations are the locale's definitions at the asked program.
\<close>

lemma asked_installation_code [code]:
  "asked_environment=fst (the (finite_extend_mapped_native given_environment finite_rooted_given_readers
    finite_asked_program given_readers_placement))"
  "asked_use=snd (the (finite_extend_mapped_native given_environment finite_rooted_given_readers
    finite_asked_program given_readers_placement))"
  "asked_placement=finite_program_coordinates given_environment (finite_system_definitions finite_rooted_given_readers)
    (finite_system_definitions finite_asked_program) given_readers_placement"
  by (simp_all only: asked_environment_def asked_use_def asked_placement_def asked_extension.installed_environment_def
    asked_extension.installed_use_def asked_extension.installed_def asked_extension.installed_placement_def)

lemmas asked_correct=asked_extension.correct[folded asked_placement_def asked_environment_def asked_use_def,
  unfolded finite_asked_program_exact]

definition asked_program :: "local_address option native_system" where
  "asked_program=given_readers_extension.installed_program finite_asked_program"

lemmas asked_installation=asked_extension.installation[folded asked_placement_def asked_environment_def
  asked_use_def asked_program_def, unfolded finite_asked_program_exact]

text \<open>The guard's definitions stand at uses fresh in the given's environment, each at an artifact root.\<close>

lemmas asked_fresh=asked_extension.fresh[folded asked_placement_def, unfolded finite_asked_program_exact]

section \<open>The guard's contract at the installed entry\<close>

lemma asked_installed_meaning:
  assumes "d\<in>system_definitions asked_program_system"
  shows "(asked_placement d,t)\<in>positive_meaning asked_program \<longleftrightarrow> (d,t)\<in>positive_meaning asked_program_system"
  by (rule asked_extension.installed_meaning[folded asked_placement_def asked_program_def,
    unfolded finite_asked_program_exact, OF assms])

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
  using asked_extension.installed_positions[folded asked_placement_def asked_environment_def asked_use_def,
    unfolded finite_asked_program_exact] asked_entry_member
  unfolding asked_entry_def by blast+

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

section \<open>The asked relation over additions: the guard over additions joined with the given's readers, rooted\<close>

text \<open>
  Course (c) of task 928's entry: the asked relation reads a candidate by its additions over the given. The
  program is the guard over additions (@{text Development_First_Problem_Additions}, its entry 990) joined with the
  given's readers' joined program and rooted at the given's reader entries and 990, as the program above is at 526;
  it stands beside that program, which stays the notion the guard over additions is exact to. The two joined
  programs meet only inside the given's guard readers: every site of the guard over additions not below 506 is
  fresh to the given, and the rest is complete data admission's or the payload audit's, which both agree with.
\<close>

lemma asked_additions_given_below: "system_definitions given_program_system\<subseteq>{..<506}"
proof -
  have guard: "system_definitions guard_readers_system\<subseteq>{..<506}"
  proof
    fix x assume "x\<in>system_definitions guard_readers_system"
    then have "x\<in>system_definitions complete_data_admission_system \<or>
        x\<in>{156,157,158,159,390,391,392,393,500,501,502,503,504,505}"
      using guard_readers_bound by blast
    then show "x\<in>{..<506}" using complete_below by auto
  qed
  have granted: "system_definitions granted_readers_system\<subseteq>{..<506}" using granted_readers_bound by auto
  show ?thesis using guard granted by (simp only: given_program_definitions Un_subset_iff)
qed

lemma asked_additions_guard_formed [simp]: "schema_system_formed additions_guard_system"
  by (rule additions_guard.guarded_formed)

lemma asked_additions_guard_definitions:
  "system_definitions additions_guard_system=insert 990 (system_definitions additions_goals_system)"
  by (simp add: install_requirement_guard_def added_view_definitions)

lemma asked_additions_guard_bound:
  "system_definitions additions_guard_system\<subseteq>system_definitions additions_readers_system\<union>
    {980,981,982,983,984,985,986,987,988,989,990,991,992}"
  by (auto simp: asked_additions_guard_definitions)

lemma asked_additions_complete_guard: "system_definitions complete_data_admission_system\<subseteq>system_definitions guard_readers_system"
  by (rule whole_agreement_definitions[OF complete_data_guard_agreement])

lemma asked_additions_overlap:
  "system_definitions given_program_system\<inter>system_definitions additions_guard_system\<subseteq>
    system_definitions guard_readers_system"
proof
  fix x assume x: "x\<in>system_definitions given_program_system\<inter>system_definitions additions_guard_system"
  have low: "x<506" using x asked_additions_given_below by blast
  have far: "x\<notin>{980,981,982,983,984,985,986,987,988,989,990,991,992}"
    "x\<notin>{950,951,952,953,954}" "x\<notin>{955,956,957,958,959,960,961,962,963,964,965,966}"
    "x\<notin>{500,501,502,503,504,505} \<or> x\<in>{500,501,502,503,504,505}"
    using low by auto
  have readers: "x\<in>system_definitions additions_readers_system" using x far(1) asked_additions_guard_bound by blast
  have audit: "system_definitions payload_audit_system\<subseteq>system_definitions guard_readers_system"
    by (simp only: guard_readers_definitions) blast
  show "x\<in>system_definitions guard_readers_system"
    using readers far(2,3) lookup_complete_definitions membership_complete_definitions asked_additions_complete_guard audit
    unfolding additions_readers_definitions extension_formation_sites extension_package_sites by blast
qed

lemma asked_additions_readers_guard_agreement:
  "systems_agree_on guard_readers_system additions_guard_system
    (system_definitions guard_readers_system\<inter>system_definitions additions_guard_system)"
proof -
  have guard_low: "system_definitions guard_readers_system\<subseteq>{..<506}"
    using asked_additions_given_below by (simp only: given_program_definitions Un_subset_iff)
  have complete: "systems_agree_on complete_data_admission_system guard_readers_system
      (system_definitions complete_data_admission_system\<inter>system_definitions guard_readers_system)"
    by (rule systems_agree_on_subdomain[OF complete_data_guard_agreement Int_lower1])
  have formation: "systems_agree_on extension_formation_system guard_readers_system
      (system_definitions extension_formation_system\<inter>system_definitions guard_readers_system)"
  proof (rule common_component_overlap_agreement[OF complete_formation_agreement complete])
    show "system_definitions extension_formation_system\<inter>system_definitions guard_readers_system\<subseteq>
        system_definitions complete_data_admission_system"
    proof
      fix x assume x: "x\<in>system_definitions extension_formation_system\<inter>system_definitions guard_readers_system"
      have "x\<notin>{950,951,952,953,954}" using x guard_low by auto
      then show "x\<in>system_definitions complete_data_admission_system"
        using x lookup_complete_definitions unfolding extension_formation_sites by blast
    qed
  qed
  have package: "systems_agree_on extension_package_system guard_readers_system
      (system_definitions extension_package_system\<inter>system_definitions guard_readers_system)"
  proof (rule common_component_overlap_agreement[OF complete_package_agreement complete])
    show "system_definitions extension_package_system\<inter>system_definitions guard_readers_system\<subseteq>
        system_definitions complete_data_admission_system"
    proof
      fix x assume x: "x\<in>system_definitions extension_package_system\<inter>system_definitions guard_readers_system"
      have "x\<in>system_definitions guard_readers_system" using x by (rule IntD2)
      from subsetD[OF guard_low this] have "x<506" by (simp only: lessThan_iff)
      then have "x\<notin>{955,956,957,958,959,960,961,962,963,964,965,966}" "x\<notin>{950,951,952,953,954}" by auto
      then show "x\<in>system_definitions complete_data_admission_system"
        using x membership_complete_definitions lookup_complete_definitions
        unfolding extension_package_sites extension_formation_sites by blast
    qed
  qed
  have audit: "systems_agree_on payload_audit_system guard_readers_system
      (system_definitions payload_audit_system\<inter>system_definitions guard_readers_system)"
    by (rule systems_agree_on_subdomain[OF system_union_agree_right[OF use_additions_system_formed readers_agreement,
      folded guard_readers_system_def] Int_lower1])
  have pair: "systems_agree_on additions_pair_readers_system guard_readers_system
      (system_definitions additions_pair_readers_system\<inter>system_definitions guard_readers_system)"
    unfolding additions_pair_readers_system_def
    by (rule overlap_agreement_union[OF extension_formation_system_formed extension_package_system_formed formation package])
  have readers: "systems_agree_on additions_readers_system guard_readers_system
      (system_definitions additions_readers_system\<inter>system_definitions guard_readers_system)"
    unfolding additions_readers_system_def
    by (rule overlap_agreement_union[OF additions_pair_readers_formed payload_audit_system_formed pair audit])
  have inside: "system_definitions additions_readers_system\<subseteq>system_definitions additions_goals_system"
    by (rule whole_agreement_definitions[OF additions_goals_agreement])
  have whole: "systems_agree_on additions_readers_system additions_guard_system (system_definitions additions_readers_system)"
    by (rule systems_agree_on_transitive[OF additions_goals_agreement
      systems_agree_on_subdomain[OF additions_guard.guarded_old_agreement inside]])
  have within: "system_definitions guard_readers_system\<inter>system_definitions additions_guard_system\<subseteq>
      system_definitions guard_readers_system\<inter>system_definitions additions_readers_system"
  proof
    fix x assume x: "x\<in>system_definitions guard_readers_system\<inter>system_definitions additions_guard_system"
    have "x\<notin>{980,981,982,983,984,985,986,987,988,989,990,991,992}" using x guard_low by auto
    then show "x\<in>system_definitions guard_readers_system\<inter>system_definitions additions_readers_system"
      using x asked_additions_guard_bound by blast
  qed
  have flipped: "systems_agree_on guard_readers_system additions_readers_system
      (system_definitions guard_readers_system\<inter>system_definitions additions_readers_system)"
    using systems_agree_on_sym[OF readers] by (simp only: Int_commute)
  show ?thesis
    by (rule systems_agree_on_transitive[OF systems_agree_on_subdomain[OF flipped within]
      systems_agree_on_subdomain[OF whole subset_trans[OF within Int_lower2]]])
qed

lemma asked_additions_overlap_agreement:
  "systems_agree_on given_program_system additions_guard_system
    (system_definitions given_program_system\<inter>system_definitions additions_guard_system)"
  by (rule common_component_overlap_agreement[OF systems_agree_on_subdomain[OF guard_program_agreement Int_lower1]
    asked_additions_readers_guard_agreement asked_additions_overlap])

definition asked_additions_joined_system :: "(nat,nat,nat,nat) schema_system" where
  "asked_additions_joined_system=system_union given_program_system additions_guard_system"

lemma asked_additions_joined_formed [simp]: "schema_system_formed asked_additions_joined_system"
  unfolding asked_additions_joined_system_def
  by (rule system_union_agree_formed[OF given_program_formed asked_additions_guard_formed asked_additions_overlap_agreement])

lemma asked_additions_joined_definitions:
  "system_definitions asked_additions_joined_system=system_definitions given_program_system\<union>
    system_definitions additions_guard_system"
  by (simp only: asked_additions_joined_system_def system_union_definitions)

lemma asked_additions_guard_meaning_joined:
  assumes "d\<in>system_definitions additions_guard_system"
  shows "(d,t)\<in>positive_meaning asked_additions_joined_system \<longleftrightarrow> (d,t)\<in>positive_meaning additions_guard_system"
  by (rule whole_system_agreement_meaning[OF asked_additions_guard_formed asked_additions_joined_formed
    system_union_agree_right[OF given_program_formed asked_additions_overlap_agreement,
      folded asked_additions_joined_system_def] assms])

lemma asked_additions_given_agreement:
  "systems_agree_on given_program_system asked_additions_joined_system (system_definitions given_program_system)"
  by (rule system_union_agree_left[OF asked_additions_guard_formed asked_additions_overlap_agreement,
    folded asked_additions_joined_system_def])

definition asked_additions_roots :: "nat fset" where
  "asked_additions_roots=given_reader_entries |\<union>| {|990|}"

definition asked_additions_program_system :: "(nat,nat,nat,nat) schema_system" where
  "asked_additions_program_system=rooted_system asked_additions_joined_system (fset asked_additions_roots)"

lemma asked_additions_roots_joined: "fset asked_additions_roots\<subseteq>system_definitions asked_additions_joined_system"
  using given_reader_entries_program
  by (auto simp: asked_additions_roots_def asked_additions_joined_definitions asked_additions_guard_definitions)

lemma asked_additions_program_formed [simp]: "schema_system_formed asked_additions_program_system"
  unfolding asked_additions_program_system_def by (rule rooted_system_formed[OF asked_additions_joined_formed])

lemma asked_additions_program_definitions:
  "system_definitions asked_additions_program_system=
    system_definition_closure asked_additions_joined_system (fset asked_additions_roots)"
  unfolding asked_additions_program_system_def
  by (rule rooted_system_definitions[OF asked_additions_joined_formed asked_additions_roots_joined])

lemma asked_additions_entry_member: "990\<in>system_definitions asked_additions_program_system"
  using rooted_system_roots[OF asked_additions_joined_formed asked_additions_roots_joined]
  unfolding asked_additions_program_system_def by (auto simp: asked_additions_roots_def)

theorem asked_additions_program_guard_meaning:
  assumes "d\<in>system_definitions asked_additions_program_system" and "d\<in>system_definitions additions_guard_system"
  shows "(d,t)\<in>positive_meaning asked_additions_program_system \<longleftrightarrow> (d,t)\<in>positive_meaning additions_guard_system"
  using rooted_system_meaning_at[OF asked_additions_joined_formed assms(1)[unfolded asked_additions_program_system_def]]
    asked_additions_guard_meaning_joined[OF assms(2)] unfolding asked_additions_program_system_def by blast

lemma asked_additions_entries_roots: "fset given_reader_entries\<subseteq>fset asked_additions_roots"
  by (auto simp: asked_additions_roots_def)

lemma asked_additions_readers_inside:
  "system_definitions given_rooted_readers_system\<subseteq>system_definitions asked_additions_program_system"
  unfolding given_rooted_readers_system_def asked_additions_program_system_def
  by (rule rooted_system_agreement_inside(1)[OF given_program_formed asked_additions_joined_formed
    asked_additions_given_agreement given_reader_entries_program asked_additions_entries_roots])

theorem asked_additions_readers_agreement:
  "systems_agree_on given_rooted_readers_system asked_additions_program_system
    (system_definitions given_rooted_readers_system)"
  unfolding given_rooted_readers_system_def asked_additions_program_system_def
  by (rule rooted_system_agreement_inside(2)[OF given_program_formed asked_additions_joined_formed
    asked_additions_given_agreement given_reader_entries_program asked_additions_entries_roots])

subsection \<open>Its finite presentation, derived from its parts'\<close>

text \<open>
  The joined program's presentation is composed from the given's joined program's piece
  (@{const finite_given_program}), the given's readers' (@{const finite_given_readers}), complete data admission's and
  definition admission's, and AX2a's package reader (@{const extension_package_system}), which is a piece of its own,
  presented once from complete data admission's and definition admission's pieces, so that the controls over
  additions and the route read its code equation. The asked program is the joined program's restriction to the closure
  its roots compute (@{thm [source] finite_system_of_rooted}). No piece is reduced again.
\<close>

definition finite_extension_package_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_extension_package_program=finite_system_of extension_package_system"

local_setup \<open>Native_Finite_Equations.note_composed @{binding finite_extension_package_program_code}
  @{thm finite_extension_package_program_def}
  [@{thm finite_complete_data_program_def}, @{thm finite_call_admission_program_def}] []\<close>

lemma finite_extension_package_program_exact:
  "decode_finite_system finite_extension_package_program=extension_package_system"
  unfolding finite_extension_package_program_def by (rule decode_finite_system_of[OF extension_package_system_formed])

definition finite_asked_additions_joined_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_asked_additions_joined_program=finite_system_of asked_additions_joined_system"

local_setup \<open>Native_Finite_Equations.note_composed @{binding finite_asked_additions_joined_program_code}
  @{thm finite_asked_additions_joined_program_def}
  [@{thm finite_given_program_def}, @{thm finite_given_readers_def}, @{thm finite_extension_package_program_def},
   @{thm finite_complete_data_program_def}, @{thm finite_call_admission_program_def}] []\<close>

definition finite_asked_additions_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_asked_additions_program=finite_system_of asked_additions_program_system"

lemma finite_asked_additions_program_code [code]:
  "finite_asked_additions_program=finite_system_restriction finite_asked_additions_joined_program
    (finite_definition_closure finite_asked_additions_joined_program asked_additions_roots)"
  unfolding finite_asked_additions_program_def finite_asked_additions_joined_program_def
    asked_additions_program_system_def
  by (rule finite_system_of_rooted[OF asked_additions_joined_formed])

lemma finite_asked_additions_program_exact:
  "decode_finite_system finite_asked_additions_program=asked_additions_program_system"
  unfolding finite_asked_additions_program_def by (rule decode_finite_system_of[OF asked_additions_program_formed])

lemma finite_asked_additions_program_formed: "finite_system_formed finite_asked_additions_program"
  by (simp only: finite_system_formed_correct finite_asked_additions_program_exact asked_additions_program_formed)

theorem finite_asked_additions_program_extends:
  "systems_agree_on (decode_finite_system finite_rooted_given_readers)
    (decode_finite_system finite_asked_additions_program)
    (system_definitions (decode_finite_system finite_rooted_given_readers))"
  by (simp only: finite_rooted_given_readers_exact finite_asked_additions_program_exact asked_additions_readers_agreement)

subsection \<open>The installation over the given's reader package\<close>

interpretation asked_additions_extension: given_readers_extension finite_asked_additions_program
  by (rule given_readers_extension.intro[OF finite_asked_additions_program_formed])
    (simp only: finite_asked_additions_program_exact asked_additions_readers_agreement)

definition asked_additions_placement :: "nat \<Rightarrow> local_address option definition_site" where
  "asked_additions_placement=given_readers_extension.installed_placement finite_asked_additions_program"

definition asked_additions_installed :: "local_address option finite_artifact_environment\<times>local_address option" where
  "asked_additions_installed=given_readers_extension.installed finite_asked_additions_program"

lemma asked_additions_built:
  "finite_extend_mapped_native given_environment finite_rooted_given_readers finite_asked_additions_program
    given_readers_placement=Some asked_additions_installed"
  unfolding asked_additions_installed_def by (rule asked_additions_extension.built)

definition asked_additions_environment :: "local_address option finite_artifact_environment" where
  "asked_additions_environment=given_readers_extension.installed_environment finite_asked_additions_program"

definition asked_additions_use :: "local_address option" where
  "asked_additions_use=given_readers_extension.installed_use finite_asked_additions_program"

definition asked_additions_entry :: "local_address option definition_site" where
  "asked_additions_entry=asked_additions_placement 990"

lemma asked_additions_installation_code [code]:
  "asked_additions_environment=fst (the (finite_extend_mapped_native given_environment finite_rooted_given_readers
    finite_asked_additions_program given_readers_placement))"
  "asked_additions_use=snd (the (finite_extend_mapped_native given_environment finite_rooted_given_readers
    finite_asked_additions_program given_readers_placement))"
  "asked_additions_placement=finite_program_coordinates given_environment
    (finite_system_definitions finite_rooted_given_readers) (finite_system_definitions finite_asked_additions_program)
    given_readers_placement"
  by (simp_all only: asked_additions_environment_def asked_additions_use_def asked_additions_placement_def
    asked_additions_extension.installed_environment_def asked_additions_extension.installed_use_def
    asked_additions_extension.installed_def asked_additions_extension.installed_placement_def)

definition asked_additions_program :: "local_address option native_system" where
  "asked_additions_program=given_readers_extension.installed_program finite_asked_additions_program"

lemmas asked_additions_installation=asked_additions_extension.installation[folded asked_additions_placement_def
  asked_additions_environment_def asked_additions_use_def asked_additions_program_def,
  unfolded finite_asked_additions_program_exact]

lemmas asked_additions_fresh=asked_additions_extension.fresh[folded asked_additions_placement_def,
  unfolded finite_asked_additions_program_exact]

subsection \<open>The guard over additions' contract at the installed entry\<close>

lemma asked_additions_installed_meaning:
  assumes "d\<in>system_definitions asked_additions_program_system"
  shows "(asked_additions_placement d,t)\<in>positive_meaning asked_additions_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning asked_additions_program_system"
  by (rule asked_additions_extension.installed_meaning[folded asked_additions_placement_def asked_additions_program_def,
    unfolded finite_asked_additions_program_exact, OF assms])

lemma asked_additions_entry_meaning:
  "(asked_additions_entry,t)\<in>positive_meaning asked_additions_program \<longleftrightarrow>
    (990,t)\<in>positive_meaning additions_guard_system"
  unfolding asked_additions_entry_def asked_additions_installed_meaning[OF asked_additions_entry_member]
  by (rule asked_additions_program_guard_meaning[OF asked_additions_entry_member])
    (simp add: asked_additions_guard_definitions)

theorem asked_additions_entry_contract:
  assumes first: "site_value_presents E gu gr t" and presented: "additions_presents E (F,(u,r)) a"
  shows "(asked_additions_entry,Pair_Term t a)\<in>positive_meaning asked_additions_program \<longleftrightarrow>
    environment_included E F \<and> (\<exists>R. native_package_at F u r R \<and>
      (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E gu gr Q \<and> d\<in>system_definitions Q) \<or>
        fst d\<notin>environment_uses E) \<and>
      (\<forall>d\<in>system_definitions R. fst d\<notin>environment_uses E \<longrightarrow>
        (\<exists>p C. native_definition_at F (fst d) (snd d) p C \<and> definition_payloads p C\<subseteq>{[]})))"
  unfolding asked_additions_entry_meaning by (rule additions_guard_contract[OF first presented])

text \<open>
  At the pair of the given's site context and its extension by the additions, the installed entry means the asked
  relation of the program above: the guard over additions is exact to the guard over site values there
  (@{thm [source] additions_guard_first_problem}), which the old installed entry means (@{thm [source] asked_entry_on_values}).
\<close>

theorem asked_additions_entry_relation:
  assumes first: "site_value_presents E gu gr t" and presented: "additions_presents E (F,(u,r)) a"
  shows "(asked_additions_entry,Pair_Term t a)\<in>positive_meaning asked_additions_program \<longleftrightarrow>
    asked_relation ((E,gu,gr),(F,u,r))"
proof -
  have placed: "environment_formed F \<and> (u,r)\<in>environment_positions F"
    using additions_presents_parts(4,5)[OF presented] by simp
  obtain w where candidate: "site_value_presents F u r w" using site_presentations.total[of "(F,(u,r))"] placed by auto
  show ?thesis
    unfolding asked_additions_entry_meaning additions_guard_first_problem[OF first presented candidate]
      asked_entry_meaning[symmetric]
    by (rule asked_entry_on_values[OF first candidate])
qed

corollary asked_additions_entry_renaming:
  "\<forall>h. bij h \<longrightarrow> rel_fun (renaming_correspondence additions_guard_presents
      (product_action site_context_renaming additions_renaming) h) (=)
    (\<lambda>p. (asked_additions_entry,p)\<in>positive_meaning asked_additions_program)
    (\<lambda>p. (asked_additions_entry,p)\<in>positive_meaning asked_additions_program)"
  unfolding asked_additions_entry_meaning by (rule additions_guard_renaming)

text \<open>
  The installed entry's term, the program entry value of the posing over additions
  (@{text Development_First_Problem}).
\<close>

lemma asked_additions_entry_positions:
  "(asked_additions_use,[])\<in>environment_positions (decode_finite_environment asked_additions_environment)"
  "asked_additions_entry\<in>environment_positions (decode_finite_environment asked_additions_environment)"
  using asked_additions_extension.installed_positions[folded asked_additions_placement_def
    asked_additions_environment_def asked_additions_use_def, unfolded finite_asked_additions_program_exact]
    asked_additions_entry_member
  unfolding asked_additions_entry_def by blast+

text \<open>
  Installing the guard over additions over the given's readers is a choice made outside the native process, a
  residual as the installation above is; the given is unchanged, its value, installation and readers standing.
\<close>

end
