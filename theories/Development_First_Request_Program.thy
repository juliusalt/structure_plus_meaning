theory Development_First_Request_Program
  imports Development_Given_Extensions Factor_Package_Requests
begin

text \<open>
  The native request at a package (\<open>Factor_Package_Requests\<close>, task 410) as native content over the given
  (DECISIONS.md "Every distinction a native program relies on comes from a native notion", "The native request at a
  package"; "The native loop's first problem is what a problem is", "How the loop works it", Requests). Its two
  definitions, the membership list 560 and the entry 561, are added as views over the given's joined readers, which
  hold every reader they call (80, 79, 83, 113, 122), and the result is rooted at the given's reader entries and 561.
  The rooted program extends the readers the given carries and agrees with task 410's program rooted at 561: the
  replay and scope readers of task 410's base, which the request does not call, are not taken unless the given's
  readers carry them. It is installed over the given's reader package as every extension of the readers is
  (\<open>given_readers_extension\<close>), beside the guard and not in the asked relation's environment: neither installation
  changes the given. The installed entry means task 410's contract; the first request is constructed at it.
\<close>

section \<open>The request's program: two views over the given's readers, rooted\<close>

lemma first_request_numbers_fresh:
  "560\<notin>system_definitions given_program_system" "561\<notin>system_definitions given_program_system"
proof -
  have bound: "system_definitions given_program_system\<subseteq>{..<506}\<union>{269,270}"
    using guard_readers_bound complete_below granted_readers_bound unfolding given_program_definitions by auto
  show "560\<notin>system_definitions given_program_system" "561\<notin>system_definitions given_program_system"
    using bound by auto
qed

lemma first_request_callees_given: "{79,80,83,113,122}\<subseteq>system_definitions given_program_system"
  using given_reader_entries_program given_rooted_members(3,4,7,8,9) by auto

definition first_request_list_view :: "(nat,nat,nat,nat) schema_system" where
  "first_request_list_view=add_view_definition given_program_system 560 data_x (context_list_clauses 83 560)"

definition first_request_joined_system :: "(nat,nat,nat,nat) schema_system" where
  "first_request_joined_system=add_view_definition first_request_list_view 561 data_x {(0,package_request_schema)}"

lemma first_request_list_view_formed [simp]: "schema_system_formed first_request_list_view"
  unfolding first_request_list_view_def
  by (rule add_recursive_definition_formed[OF given_program_formed first_request_numbers_fresh(1)])
    (use first_request_callees_given in \<open>auto simp: context_list_clauses_def context_list_nil_schema_def
      context_list_step_schema_def schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def
      octets_formed_def\<close>)

lemma first_request_joined_formed [simp]: "schema_system_formed first_request_joined_system"
  unfolding first_request_joined_system_def
  by (rule add_recursive_definition_formed[OF first_request_list_view_formed])
    (use first_request_callees_given first_request_numbers_fresh in \<open>auto simp: first_request_list_view_def
      package_request_schema_def schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def
      octets_formed_def\<close>)

lemma first_request_joined_definitions:
  "system_definitions first_request_joined_system=insert 561 (insert 560 (system_definitions given_program_system))"
  by (simp add: first_request_joined_system_def first_request_list_view_def)

section \<open>It agrees with task 410's program and with the given's readers\<close>

text \<open>
  The readers task 410's program is built over (@{const package_retention_admission_system}) are readers of the
  given's joined program, and agree with it on their whole domain; the two views added at the same fresh sites keep
  that agreement (@{thm [source] view_extension_agreement}).
\<close>

lemma first_request_retention_agreement:
  "systems_agree_on package_retention_admission_system given_program_system
    (system_definitions package_retention_admission_system)"
  by (rule whole_agreement_transitive[OF given_reader_agreements(9)
    whole_agreement_transitive[OF additions_guard_agreement guard_program_agreement]])

theorem first_request_package_agreement:
  "systems_agree_on package_request_system first_request_joined_system (system_definitions package_request_system)"
proof -
  have inside: "system_definitions package_retention_admission_system\<subseteq>system_definitions given_program_system"
    by (rule whole_agreement_definitions[OF first_request_retention_agreement])
  have fresh: "560\<notin>system_definitions package_retention_admission_system"
    "561\<notin>system_definitions package_request_list_system" "561\<notin>system_definitions first_request_list_view"
    using inside first_request_numbers_fresh by (auto simp: first_request_list_view_def)
  have list: "systems_agree_on package_request_list_system first_request_list_view
      (insert 560 (system_definitions package_retention_admission_system))"
    unfolding package_request_list_system_def first_request_list_view_def
    by (rule view_extension_agreement[OF systems_agree_on_subdomain[OF first_request_retention_agreement]
      fresh(1) first_request_numbers_fresh(1) package_retention_admission_system_formed given_program_formed]) blast
  show ?thesis
    unfolding package_request_system_def first_request_joined_system_def
    by (rule view_extension_agreement[OF systems_agree_on_subdomain[OF list] fresh(2,3)
      package_request_list_formed first_request_list_view_formed]) auto
qed

lemma first_request_given_agreement:
  "systems_agree_on given_program_system first_request_joined_system (system_definitions given_program_system)"
  unfolding first_request_joined_system_def first_request_list_view_def
  by (simp only: systems_agree_on_added[OF first_request_numbers_fresh(2)]
    systems_agree_on_added[OF first_request_numbers_fresh(1)] systems_agree_on_reflexive)

text \<open>The roots: every entry the given's readers are rooted at, and the request's entry.\<close>

definition first_request_roots :: "nat fset" where
  "first_request_roots=given_reader_entries |\<union>| {|561|}"

definition first_request_program_system :: "(nat,nat,nat,nat) schema_system" where
  "first_request_program_system=rooted_system first_request_joined_system (fset first_request_roots)"

lemma first_request_roots_joined: "fset first_request_roots\<subseteq>system_definitions first_request_joined_system"
  using given_reader_entries_program by (auto simp: first_request_roots_def first_request_joined_definitions)

lemma first_request_program_formed [simp]: "schema_system_formed first_request_program_system"
  unfolding first_request_program_system_def by (rule rooted_system_formed[OF first_request_joined_formed])

lemma first_request_program_definitions:
  "system_definitions first_request_program_system=
    system_definition_closure first_request_joined_system (fset first_request_roots)"
  unfolding first_request_program_system_def
  by (rule rooted_system_definitions[OF first_request_joined_formed first_request_roots_joined])

lemma first_request_entry_member: "561\<in>system_definitions first_request_program_system"
  using rooted_system_roots[OF first_request_joined_formed first_request_roots_joined]
  unfolding first_request_program_system_def by (auto simp: first_request_roots_def)

text \<open>Every definition task 410's program holds means in the request's program what it means there.\<close>

theorem first_request_request_meaning:
  assumes "d\<in>system_definitions first_request_program_system" and "d\<in>system_definitions package_request_system"
  shows "(d,t)\<in>positive_meaning first_request_program_system \<longleftrightarrow> (d,t)\<in>positive_meaning package_request_system"
  using rooted_system_meaning_at[OF first_request_joined_formed assms(1)[unfolded first_request_program_system_def]]
    whole_system_agreement_meaning[OF package_request_system_formed first_request_joined_formed
      first_request_package_agreement assms(2)]
  unfolding first_request_program_system_def by blast

text \<open>
  Task 410's program rooted at its entry (@{thm [source] rooted_system_meaning}) stands inside the request's program
  and agrees with it there: what the request's program holds beyond it is the given's readers.
\<close>

theorem first_request_rooted_request:
  "system_definitions (rooted_system package_request_system {561})\<subseteq>system_definitions first_request_program_system"
  "systems_agree_on (rooted_system package_request_system {561}) first_request_program_system
    (system_definitions (rooted_system package_request_system {561}))"
proof -
  have roots: "{561}\<subseteq>system_definitions package_request_system" "{561}\<subseteq>fset first_request_roots"
    by (simp_all add: first_request_roots_def)
  show "system_definitions (rooted_system package_request_system {561})\<subseteq>system_definitions first_request_program_system"
    unfolding first_request_program_system_def
    by (rule rooted_system_agreement_inside(1)[OF package_request_system_formed first_request_joined_formed
      first_request_package_agreement roots])
  show "systems_agree_on (rooted_system package_request_system {561}) first_request_program_system
      (system_definitions (rooted_system package_request_system {561}))"
    unfolding first_request_program_system_def
    by (rule rooted_system_agreement_inside(2)[OF package_request_system_formed first_request_joined_formed
      first_request_package_agreement roots])
qed

text \<open>The program keeps every definition of the readers the given carries, and agrees with them there.\<close>

lemma first_request_entries_roots: "fset given_reader_entries\<subseteq>fset first_request_roots"
  by (auto simp: first_request_roots_def)

lemma first_request_readers_inside:
  "system_definitions given_rooted_readers_system\<subseteq>system_definitions first_request_program_system"
  unfolding given_rooted_readers_system_def first_request_program_system_def
  by (rule rooted_system_agreement_inside(1)[OF given_program_formed first_request_joined_formed
    first_request_given_agreement given_reader_entries_program first_request_entries_roots])

theorem first_request_readers_agreement:
  "systems_agree_on given_rooted_readers_system first_request_program_system
    (system_definitions given_rooted_readers_system)"
  unfolding given_rooted_readers_system_def first_request_program_system_def
  by (rule rooted_system_agreement_inside(2)[OF given_program_formed first_request_joined_formed
    first_request_given_agreement given_reader_entries_program first_request_entries_roots])

section \<open>Its finite presentation, derived from the given's joined program's\<close>

text \<open>
  The joined program is two view steps over the given's joined program, whose piece is
  @{const finite_given_program}; the request's program is its restriction to the closure its roots compute
  (@{thm [source] finite_system_of_rooted}). No piece is reduced again.
\<close>

definition finite_first_request_joined_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_first_request_joined_program=finite_system_of first_request_joined_system"

local_setup \<open>Native_Finite_Equations.note_composed @{binding finite_first_request_joined_program_code}
  @{thm finite_first_request_joined_program_def} [@{thm finite_given_program_def}] []\<close>

definition finite_first_request_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_first_request_program=finite_system_of first_request_program_system"

lemma finite_first_request_program_code [code]:
  "finite_first_request_program=finite_system_restriction finite_first_request_joined_program
    (finite_definition_closure finite_first_request_joined_program first_request_roots)"
  unfolding finite_first_request_program_def finite_first_request_joined_program_def first_request_program_system_def
  by (rule finite_system_of_rooted[OF first_request_joined_formed])

lemma finite_first_request_program_exact:
  "decode_finite_system finite_first_request_program=first_request_program_system"
  unfolding finite_first_request_program_def by (rule decode_finite_system_of[OF first_request_program_formed])

lemma finite_first_request_program_formed: "finite_system_formed finite_first_request_program"
  by (simp only: finite_system_formed_correct finite_first_request_program_exact first_request_program_formed)

export_code finite_first_request_program finite_system_formed checking SML

section \<open>The installation over the given's reader package\<close>

interpretation first_request_extension: given_readers_extension finite_first_request_program
  by (rule given_readers_extension.intro[OF finite_first_request_program_formed])
    (simp only: finite_first_request_program_exact first_request_readers_agreement)

definition first_request_placement :: "nat \<Rightarrow> local_address option definition_site" where
  "first_request_placement=given_readers_extension.installed_placement finite_first_request_program"

definition first_request_environment :: "local_address option finite_artifact_environment" where
  "first_request_environment=given_readers_extension.installed_environment finite_first_request_program"

definition first_request_use :: "local_address option" where
  "first_request_use=given_readers_extension.installed_use finite_first_request_program"

definition first_request_program :: "local_address option native_system" where
  "first_request_program=given_readers_extension.installed_program finite_first_request_program"

definition first_request_entry :: "local_address option definition_site" where
  "first_request_entry=first_request_placement 561"

text \<open>
  The installation's constants are defined through the interpretation of @{text given_readers_extension}; their code
  equations are the locale's definitions at the first request's program.
\<close>

lemma first_request_installation_code [code]:
  "first_request_environment=fst (the (finite_extend_mapped_native given_environment finite_rooted_given_readers
    finite_first_request_program given_readers_placement))"
  "first_request_use=snd (the (finite_extend_mapped_native given_environment finite_rooted_given_readers
    finite_first_request_program given_readers_placement))"
  "first_request_placement=finite_program_coordinates given_environment
    (finite_system_definitions finite_rooted_given_readers) (finite_system_definitions finite_first_request_program)
    given_readers_placement"
  by (simp_all only: first_request_environment_def first_request_use_def first_request_placement_def
    first_request_extension.installed_environment_def first_request_extension.installed_use_def
    first_request_extension.installed_def first_request_extension.installed_placement_def)

lemmas first_request_built=first_request_extension.built

lemmas first_request_installation=first_request_extension.installation[folded first_request_placement_def
  first_request_environment_def first_request_use_def first_request_program_def,
  unfolded finite_first_request_program_exact]

text \<open>The request's own definitions stand at uses fresh in the given's environment, each at an artifact root.\<close>

lemmas first_request_fresh=first_request_extension.fresh[folded first_request_placement_def,
  unfolded finite_first_request_program_exact]

lemma first_request_entry_positions:
  "(first_request_use,[])\<in>environment_positions (decode_finite_environment first_request_environment)"
  "first_request_entry\<in>environment_positions (decode_finite_environment first_request_environment)"
  using first_request_extension.installed_positions[folded first_request_placement_def first_request_environment_def
    first_request_use_def, unfolded finite_first_request_program_exact] first_request_entry_member
  unfolding first_request_entry_def by blast+

section \<open>Task 410's contract at the installed entry\<close>

lemma first_request_installed_meaning:
  assumes "d\<in>system_definitions first_request_program_system"
  shows "(first_request_placement d,t)\<in>positive_meaning first_request_program \<longleftrightarrow>
    (d,t)\<in>positive_meaning first_request_program_system"
  by (rule first_request_extension.installed_meaning[folded first_request_placement_def first_request_program_def,
    unfolded finite_first_request_program_exact, OF assms])

theorem first_request_entry_meaning:
  "(first_request_entry,t)\<in>positive_meaning first_request_program \<longleftrightarrow> (561,t)\<in>positive_meaning package_request_system"
  unfolding first_request_entry_def first_request_installed_meaning[OF first_request_entry_member]
  by (rule first_request_request_meaning[OF first_request_entry_member]) simp

theorem first_request_entry_exact:
  "(first_request_entry,t)\<in>positive_meaning first_request_program \<longleftrightarrow>
    presented_predicate package_request_presents package_request_relation t"
  unfolding first_request_entry_meaning by (rule package_request_exact)

corollary first_request_entry_on_values:
  assumes "site_value_presents E u r a" and "site_value_presents F v q b"
  shows "(first_request_entry,Pair_Term a (Pair_Term (data_list_term (map definition_site_value ds)) b))
      \<in>positive_meaning first_request_program \<longleftrightarrow> package_request_holds (E,(u,r)) ds (F,(v,q))"
  unfolding first_request_entry_meaning by (rule package_request_on_values[OF assms])

corollary first_request_entry_renaming:
  "\<forall>h. bij h \<longrightarrow> rel_fun (renaming_correspondence package_request_presents package_request_renaming h) (=)
    (\<lambda>z. (first_request_entry,z)\<in>positive_meaning first_request_program)
    (\<lambda>z. (first_request_entry,z)\<in>positive_meaning first_request_program)"
  unfolding first_request_entry_meaning by (rule package_request_renaming)

section \<open>The payloads the installed program states\<close>

text \<open>
  Stated relative to the given's joined readers' (@{thm [source] add_view_definition_payloads},
  @{thm [source] rooted_system_payloads}): the two views add the empty payload alone
  (@{thm [source] package_request_leaves}), the rooting takes none, and the installation's placement and alpha
  variation move none (@{thm [source] system_payloads_rename}, @{thm [source] system_alpha_variant_payloads}); the
  given's joined readers state the empty payload alone (@{thm [source] given_program_payloads}), so the payload audit
  holds at every definition of the installed package (@{thm [source] payload_audit_package}).
\<close>

theorem first_request_payloads:
  "system_payloads first_request_joined_system\<subseteq>insert [] (system_payloads given_program_system)"
  "system_payloads first_request_program_system\<subseteq>system_payloads first_request_joined_system"
  "system_payloads first_request_program=system_payloads first_request_program_system"
  "system_payloads first_request_program\<subseteq>{[]}"
proof -
  show joined: "system_payloads first_request_joined_system\<subseteq>insert [] (system_payloads given_program_system)"
  proof
    fix x assume "x\<in>system_payloads first_request_joined_system"
    then have "x\<in>system_payloads given_program_system \<or>
        (\<exists>c S. (c,S)\<in>context_list_clauses 83 560 \<and> Payload_Term x\<in>schema_leaves S) \<or>
        Payload_Term x\<in>schema_leaves package_request_schema"
      unfolding first_request_joined_system_def first_request_list_view_def add_view_definition_payloads by auto
    then show "x\<in>insert [] (system_payloads given_program_system)"
      by (auto dest: package_request_leaves(2) simp: package_request_leaves(1))
  qed
  show rooted: "system_payloads first_request_program_system\<subseteq>system_payloads first_request_joined_system"
    unfolding first_request_program_system_def by (rule rooted_system_payloads)
  show installed: "system_payloads first_request_program=system_payloads first_request_program_system"
    by (simp add: system_alpha_variant_payloads[OF first_request_installation(7)] system_payloads_rename)
  show "system_payloads first_request_program\<subseteq>{[]}"
    using joined rooted given_program_payloads(1) unfolding installed by blast
qed

corollary first_request_payload_audit:
  assumes source: "environment_value_presents (decode_finite_environment first_request_environment) e"
  shows "\<forall>d\<in>system_definitions first_request_program.
    (505,source_root_argument e (use_data_term (fst d)) (Payload_Term (snd d)))\<in>positive_meaning payload_audit_system"
  using payload_audit_package[OF source first_request_installation(6)] first_request_payloads(4) by blast

text \<open>
  Installing the request's program over the given's readers is a choice made outside the native process, a residual
  as the guard's installation is. The given is unchanged: the request's program stands in an environment that
  includes the given's, beside the asked relation's and not in it.
\<close>

end
