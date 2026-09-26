theory Development_First_Request_Registrations
  imports Development_First_Request_Program Development_Given_Registrations
begin

text \<open>
  The given's four witness registrations (\<open>Factor_Reader_Witness_Registrations\<close>) at the first request's program
  (@{const finite_first_request_program}, the views 560 and 561 over the given's joined readers, rooted at the
  given's reader entries and 561), and relocated at its installation. A registration's completeness depends on the
  program's meanings and is not carried from another program: each hypothesis is discharged here from this program's
  meanings, which are the given's readers' at every definition both hold. The program holds the clauses of 77, 392
  and 561; 525's stands in the guard's goals program, and names no clause here.
\<close>

section \<open>A single-clause family of a formed program in its finite presentation\<close>

lemma finite_system_of_single_clause:
  assumes formed: "schema_system_formed P"
    and single: "\<And>c T. ((d,c),T)\<in>system_clauses P \<longleftrightarrow> c=0 \<and> T=X"
  shows "((d,c),S) |\<in>| finite_system_clauses (finite_system_of P) \<longleftrightarrow> c=0 \<and> finite_schema_of X=S"
proof -
  have formed_X: "schema_formed X"
    using formed single[of 0 X] unfolding schema_system_formed_def by blast
  have eq: "decode_finite_schema S=X \<longleftrightarrow> finite_schema_of X=S"
    by (metis decode_finite_schema_of[OF formed_X] decode_finite_schema_injective)
  show ?thesis
    by (simp only: finite_system_clause_decoded decode_finite_system_of[OF formed] single eq)
qed

section \<open>The program's clauses and meanings are the given's readers' where both hold a definition\<close>

lemma guard_first_request_agreement:
  "systems_agree_on guard_readers_system first_request_joined_system (system_definitions guard_readers_system)"
  by (rule whole_agreement_transitive[OF guard_program_agreement first_request_given_agreement])

lemma first_request_guard_clause:
  assumes "d\<in>system_definitions first_request_program_system" "d\<in>system_definitions guard_readers_system"
  shows "((d,c),S)\<in>system_clauses first_request_program_system \<longleftrightarrow> ((d,c),S)\<in>system_clauses guard_readers_system"
  using rooted_system_agreement[of first_request_joined_system "fset first_request_roots",
      folded first_request_program_system_def] guard_first_request_agreement assms
  unfolding systems_agree_on_def by blast

lemma first_request_guard_meaning:
  assumes member: "d\<in>system_definitions first_request_program_system" and guard: "d\<in>system_definitions guard_readers_system"
  shows "(d,t)\<in>positive_meaning first_request_program_system \<longleftrightarrow> (d,t)\<in>positive_meaning guard_readers_system"
  using rooted_system_meaning_at[OF first_request_joined_formed member[unfolded first_request_program_system_def]]
    whole_system_agreement_meaning[OF guard_readers_formed first_request_joined_formed guard_first_request_agreement guard]
  unfolding first_request_program_system_def by blast

text \<open>The given's readers' single clauses at 77 and 392, read from the readers' own systems.\<close>

lemma guard_closure_clause:
  "((77,c),T)\<in>system_clauses guard_readers_system \<longleftrightarrow> c=0 \<and> T=package_closure_admission_schema"
proof -
  have "77\<in>system_definitions package_closure_admission_system" by simp
  then have "((77,c),T)\<in>system_clauses package_closure_admission_system \<longleftrightarrow>
      ((77,c),T)\<in>system_clauses guard_readers_system"
    using whole_agreement_transitive[OF given_reader_agreements(2) additions_guard_agreement]
    unfolding systems_agree_on_def by blast
  then show ?thesis by simp
qed

lemma guard_additions_clause:
  "((392,c),T)\<in>system_clauses guard_readers_system \<longleftrightarrow> c=0 \<and> T=package_additions_schema 391"
proof -
  have "392\<in>system_definitions use_additions_system" by simp
  then have "((392,c),T)\<in>system_clauses use_additions_system \<longleftrightarrow> ((392,c),T)\<in>system_clauses guard_readers_system"
    using additions_guard_agreement unfolding systems_agree_on_def by blast
  then show ?thesis by (simp only: use_additions_families(3))
qed

text \<open>
  A callee of a clause the given's rooted readers hold is one of their definitions (their formation); there, their
  clauses are the given's readers' where both hold a definition.
\<close>

lemma given_rooted_reaches:
  assumes member: "d\<in>system_definitions given_rooted_readers_system" and guard: "d\<in>system_definitions guard_readers_system"
    and clause: "((d,c),S)\<in>system_clauses guard_readers_system" and callee: "e\<in>schema_dependencies S"
  shows "e\<in>system_definitions given_rooted_readers_system"
proof -
  have "((d,c),S)\<in>system_clauses given_rooted_readers_system"
    using rooted_system_agreement[of given_program_system "fset given_reader_entries",
        folded given_rooted_readers_system_def] guard_program_agreement member guard clause
    unfolding systems_agree_on_def by blast
  then show ?thesis using given_rooted_readers_formed callee unfolding schema_system_formed_def by blast
qed

subsection \<open>The read sites stand in the given's rooted readers, and so in the program\<close>

text \<open>
  77, 82, 113 and 392 are entries of the given's readers; 47 and 76 are callees of 77's clause, 5 of 47's, 391 of
  392's and 390 of 391's; 12 is reached from 113 through the artifact inclusion 112 and the artifact lookup 37.
\<close>

lemma given_rooted_read_sites:
  "d\<in>{5,12,47,76,82,113,390,391} \<Longrightarrow> d\<in>system_definitions given_rooted_readers_system"
  "d\<in>{5,12,47,76,82,113,390,391} \<Longrightarrow> d\<in>system_definitions guard_readers_system"
proof -
  have roots: "77\<in>system_definitions given_rooted_readers_system" "82\<in>system_definitions given_rooted_readers_system"
    "113\<in>system_definitions given_rooted_readers_system" "392\<in>system_definitions given_rooted_readers_system"
    using given_rooted_entries given_rooted_members(2,6,8,10) by blast+
  have callee: "e\<in>system_definitions guard_readers_system"
    if "((d,c),S)\<in>system_clauses guard_readers_system" "e\<in>schema_dependencies S" for d c S e
    using guard_readers_formed that unfolding schema_system_formed_def by blast
  have inclusion_step: "systems_agree_on artifact_inclusion_system environment_inclusion_system
      (system_definitions artifact_inclusion_system)"
    by (simp add: environment_inclusion_system_def systems_agree_on_added)
  have to_guard: "systems_agree_on X guard_readers_system (system_definitions X)"
    if "systems_agree_on X use_additions_system (system_definitions X)" for X :: "(nat,nat,nat,nat) schema_system"
    by (rule whole_agreement_transitive[OF that additions_guard_agreement])
  have at: "d\<in>system_definitions guard_readers_system \<and>
      (((d,c),S)\<in>system_clauses guard_readers_system \<longleftrightarrow> ((d,c),S)\<in>system_clauses X)"
    if "systems_agree_on X guard_readers_system (system_definitions X)" "d\<in>system_definitions X"
    for X :: "(nat,nat,nat,nat) schema_system" and d c S
    using that whole_agreement_definitions[OF that(1)] unfolding systems_agree_on_def by blast
  have subset_guard: "systems_agree_on data_subset_system guard_readers_system (system_definitions data_subset_system)"
    by (rule to_guard[OF whole_agreement_transitive[OF whole_agreement_transitive[OF row_values_subset_agreement
      row_values_complete_data_agreement] complete_data_additions_agreement]])
  have environment_guard: "systems_agree_on environment_inclusion_system guard_readers_system
      (system_definitions environment_inclusion_system)" by (rule to_guard[OF given_reader_agreements(8)])
  have artifact_guard: "systems_agree_on artifact_inclusion_system guard_readers_system
      (system_definitions artifact_inclusion_system)"
    by (rule whole_agreement_transitive[OF inclusion_step environment_guard])
  have lookup_guard: "systems_agree_on artifact_lookup_system guard_readers_system (system_definitions artifact_lookup_system)"
    by (rule to_guard[OF whole_agreement_transitive[OF complete_data_lookup_agreement complete_data_additions_agreement]])
  have edge_guard: "systems_agree_on definition_edge_reading_system guard_readers_system
      (system_definitions definition_edge_reading_system)" by (rule to_guard[OF given_reader_agreements(6)])
  have c77: "((77,0),package_closure_admission_schema)\<in>system_clauses guard_readers_system"
    and g77: "77\<in>system_definitions guard_readers_system"
    using guard_closure_clause[of 0 package_closure_admission_schema] callee[of 77 0 package_closure_admission_schema]
      guard_readers_formed unfolding schema_system_formed_def by auto
  have c47: "((47,1),data_subset_cons_schema)\<in>system_clauses guard_readers_system"
    and g47: "47\<in>system_definitions guard_readers_system" and g5: "5\<in>system_definitions guard_readers_system"
    using at[OF subset_guard, of 47 1 data_subset_cons_schema] at[OF subset_guard, of 5 0 data_subset_cons_schema]
    by (simp_all add: data_subset_clauses_def)
  have c392: "((392,0),package_additions_schema 391)\<in>system_clauses guard_readers_system"
    and g392: "392\<in>system_definitions guard_readers_system"
    using guard_additions_clause[of 0 "package_additions_schema 391"] guard_readers_formed
    unfolding schema_system_formed_def by auto
  have c391: "((391,1),context_list_step_schema 390 391)\<in>system_clauses guard_readers_system"
    and g391: "391\<in>system_definitions guard_readers_system"
    and g390: "390\<in>system_definitions guard_readers_system"
    using at[OF additions_guard_agreement, of 391 1 "context_list_step_schema 390 391"]
      at[OF additions_guard_agreement, of 390 1 "context_list_step_schema 390 391"] use_additions_families(2)
    by (simp_all add: context_list_clauses_def)
  have c113: "((113,0),environment_inclusion_schema)\<in>system_clauses guard_readers_system"
    and g113: "113\<in>system_definitions guard_readers_system"
    using at[OF environment_guard, of 113 0 environment_inclusion_schema] by simp_all
  have c112: "((112,1),context_list_step_schema 37 112)\<in>system_clauses guard_readers_system"
    and g112: "112\<in>system_definitions guard_readers_system"
    using at[OF artifact_guard, of 112 1 "context_list_step_schema 37 112"] by (simp_all add: context_list_clauses_def)
  have c37: "((37,0),artifact_lookup_schema)\<in>system_clauses guard_readers_system"
    and g37: "37\<in>system_definitions guard_readers_system" and g12: "12\<in>system_definitions guard_readers_system"
    using at[OF lookup_guard, of 37 0 artifact_lookup_schema] at[OF lookup_guard, of 12 0 artifact_lookup_schema]
    by simp_all
  have g82: "82\<in>system_definitions guard_readers_system"
    using at[OF edge_guard, of 82 0 package_closure_admission_schema] given_entry_members(6) by blast
  have dep: "47\<in>schema_dependencies package_closure_admission_schema"
    "76\<in>schema_dependencies package_closure_admission_schema"
    "5\<in>schema_dependencies data_subset_cons_schema"
    "391\<in>schema_dependencies (package_additions_schema 391)"
    "390\<in>schema_dependencies (context_list_step_schema 390 391)"
    "112\<in>schema_dependencies environment_inclusion_schema"
    "37\<in>schema_dependencies (context_list_step_schema 37 112)"
    "12\<in>schema_dependencies artifact_lookup_schema"
    by (simp_all add: schema_dependencies_def rel_ran_image package_closure_admission_schema_def
      data_subset_cons_schema_def package_additions_schema_def context_list_step_schema_def
      environment_inclusion_schema_def artifact_lookup_schema_def)
  have g76: "76\<in>system_definitions guard_readers_system" by (rule callee[OF c77 dep(2)])
  have m47: "47\<in>system_definitions given_rooted_readers_system"
    by (rule given_rooted_reaches[OF roots(1) g77 c77 dep(1)])
  have m76: "76\<in>system_definitions given_rooted_readers_system"
    by (rule given_rooted_reaches[OF roots(1) g77 c77 dep(2)])
  have m5: "5\<in>system_definitions given_rooted_readers_system"
    by (rule given_rooted_reaches[OF m47 g47 c47 dep(3)])
  have m391: "391\<in>system_definitions given_rooted_readers_system"
    by (rule given_rooted_reaches[OF roots(4) g392 c392 dep(4)])
  have m390: "390\<in>system_definitions given_rooted_readers_system"
    by (rule given_rooted_reaches[OF m391 g391 c391 dep(5)])
  have m112: "112\<in>system_definitions given_rooted_readers_system"
    by (rule given_rooted_reaches[OF roots(3) g113 c113 dep(6)])
  have m37: "37\<in>system_definitions given_rooted_readers_system"
    by (rule given_rooted_reaches[OF m112 g112 c112 dep(7)])
  have m12: "12\<in>system_definitions given_rooted_readers_system"
    by (rule given_rooted_reaches[OF m37 g37 c37 dep(8)])
  show "d\<in>system_definitions given_rooted_readers_system" if "d\<in>{5,12,47,76,82,113,390,391}"
    using that m5 m12 m47 m76 m390 m391 roots by blast
  show "d\<in>system_definitions guard_readers_system" if "d\<in>{5,12,47,76,82,113,390,391}"
    using that g5 g12 g47 g76 g82 g113 g390 g391 by blast
qed

lemma first_request_read_sites:
  "d\<in>{5,12,47,76,82,113,390,391} \<Longrightarrow> d\<in>system_definitions first_request_program_system"
  "d\<in>{5,12,47,76,82,113,390,391} \<Longrightarrow> d\<in>system_definitions guard_readers_system"
  using first_request_readers_inside given_rooted_read_sites by blast+

lemma first_request_read_meaning:
  assumes "d\<in>{5,12,47,76,82,113,390,391}"
  shows "(d,t)\<in>positive_meaning first_request_program_system \<longleftrightarrow> (d,t)\<in>positive_meaning guard_readers_system"
  by (rule first_request_guard_meaning[OF first_request_read_sites[OF assms]])

subsection \<open>The meanings the registrations ask\<close>

lemma first_request_meanings:
  "(5,t)\<in>positive_meaning first_request_program_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(12,t)\<in>positive_meaning first_request_program_system \<longleftrightarrow> (12,t)\<in>positive_meaning artifact_identity_system"
  "(47,t)\<in>positive_meaning first_request_program_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  "(76,t)\<in>positive_meaning first_request_program_system \<longleftrightarrow>
    (76,t)\<in>positive_meaning definition_callee_list_system"
  "(82,t)\<in>positive_meaning first_request_program_system \<longleftrightarrow>
    (82,t)\<in>positive_meaning definition_edge_reading_system"
  "(113,t)\<in>positive_meaning first_request_program_system \<longleftrightarrow>
    (113,t)\<in>positive_meaning environment_inclusion_system"
  by (simp_all only: first_request_read_meaning insert_iff simp_thms given_readers_meanings)

lemma first_request_listing: "context_list_rule_relation (positive_meaning first_request_program_system) 390 391"
proof -
  have e: "(390,t)\<in>positive_meaning first_request_program_system \<longleftrightarrow> (390,t)\<in>positive_meaning guard_readers_system"
    "(391,t)\<in>positive_meaning first_request_program_system \<longleftrightarrow> (391,t)\<in>positive_meaning guard_readers_system" for t
    by (simp_all only: first_request_read_meaning insert_iff simp_thms)
  show ?thesis
    by (rule context_list_rule_relation.intro) (unfold e, rule context_list_rule_relation.equation[OF given_readers_listing])
qed

section \<open>The registrations and the construction complete at the program\<close>

theorem first_request_registrations_complete:
  "finite_registration_complete finite_first_request_program n bound_witness_registration"
  "finite_registration_complete finite_first_request_program n (additions_witness_registration 392 391)"
  "finite_registration_complete finite_first_request_program n merge_witness_registration"
proof -
  show "finite_registration_complete finite_first_request_program n bound_witness_registration"
    by (rule bound_witness_registration_complete)
      (simp_all only: finite_first_request_program_exact first_request_meanings)
  show "finite_registration_complete finite_first_request_program n (additions_witness_registration 392 391)"
    by (rule additions_witness_registration_complete[where element_site=390])
      (simp_all only: finite_first_request_program_exact first_request_meanings first_request_listing)
  show "finite_registration_complete finite_first_request_program n merge_witness_registration"
    by (rule merge_witness_registration_complete)
      (simp_all only: finite_first_request_program_exact first_request_meanings)
qed

subsection \<open>The clauses the registrations name\<close>

theorem first_request_registered_clauses:
  "((77,c),S) |\<in>| finite_system_clauses finite_first_request_program \<longleftrightarrow>
    c=0 \<and> finite_registration_matches 77 S bound_witness_registration"
  "((392,c),S) |\<in>| finite_system_clauses finite_first_request_program \<longleftrightarrow>
    c=0 \<and> finite_registration_matches 392 S (additions_witness_registration 392 391)"
  "((561,c),S) |\<in>| finite_system_clauses finite_first_request_program \<longleftrightarrow>
    c=0 \<and> finite_registration_matches 561 S merge_witness_registration"
  "((525,c),S) |\<notin>| finite_system_clauses finite_first_request_program"
proof -
  have roots: "{77,392}\<subseteq>system_definitions first_request_program_system"
    "{77,392}\<subseteq>system_definitions guard_readers_system"
    using first_request_readers_inside given_rooted_entries given_rooted_members(2,10)
    by (auto simp: guard_readers_definitions)
  have at77: "((77,c),T)\<in>system_clauses first_request_program_system \<longleftrightarrow> c=0 \<and> T=package_closure_admission_schema"
    for c T
    using first_request_guard_clause[of 77 c T] roots guard_closure_clause[of c T] by simp
  have at392: "((392,c),T)\<in>system_clauses first_request_program_system \<longleftrightarrow> c=0 \<and> T=package_additions_schema 391"
    for c T
    using first_request_guard_clause[of 392 c T] roots guard_additions_clause[of c T] by simp
  have at561: "((561,c),T)\<in>system_clauses first_request_program_system \<longleftrightarrow> c=0 \<and> T=package_request_schema" for c T
  proof -
    have joined: "((561,c),T)\<in>system_clauses first_request_program_system \<longleftrightarrow>
        ((561,c),T)\<in>system_clauses first_request_joined_system"
      using rooted_system_agreement[of first_request_joined_system "fset first_request_roots",
          folded first_request_program_system_def] first_request_entry_member
      unfolding systems_agree_on_def by blast
    have "561\<in>system_definitions package_request_system" by simp
    then have "((561,c),T)\<in>system_clauses package_request_system \<longleftrightarrow>
        ((561,c),T)\<in>system_clauses first_request_joined_system"
      using first_request_package_agreement unfolding systems_agree_on_def by blast
    then show ?thesis using joined package_request_clauses(1)[of c T] by simp
  qed
  show "((77,c),S) |\<in>| finite_system_clauses finite_first_request_program \<longleftrightarrow>
      c=0 \<and> finite_registration_matches 77 S bound_witness_registration"
    by (simp only: finite_first_request_program_def finite_system_of_single_clause[OF first_request_program_formed at77]
      finite_registration_matches_def bound_witness_registration_def closure_witness_registration_def
      collection_registration.simps simp_thms)
  show "((392,c),S) |\<in>| finite_system_clauses finite_first_request_program \<longleftrightarrow>
      c=0 \<and> finite_registration_matches 392 S (additions_witness_registration 392 391)"
    by (simp only: finite_first_request_program_def finite_system_of_single_clause[OF first_request_program_formed at392]
      finite_registration_matches_def additions_witness_registration_def closure_witness_registration_def
      collection_registration.simps simp_thms)
  show "((561,c),S) |\<in>| finite_system_clauses finite_first_request_program \<longleftrightarrow>
      c=0 \<and> finite_registration_matches 561 S merge_witness_registration"
    by (simp only: finite_first_request_program_def finite_system_of_single_clause[OF first_request_program_formed at561]
      finite_registration_matches_def merge_witness_registration_def collection_registration.simps simp_thms)
  have bound: "system_definitions given_program_system\<subseteq>{..<506}\<union>{269,270}"
    using guard_readers_bound complete_below granted_readers_bound unfolding given_program_definitions by auto
  show "((525,c),S) |\<notin>| finite_system_clauses finite_first_request_program"
  proof
    assume "((525,c),S) |\<in>| finite_system_clauses finite_first_request_program"
    then have clause: "((525,c),decode_finite_schema S)\<in>system_clauses first_request_program_system"
      by (simp only: finite_system_clause_decoded finite_first_request_program_exact)
    then have member: "525\<in>system_definitions first_request_program_system"
      using first_request_program_formed unfolding schema_system_formed_def by blast
    have "((525,c),decode_finite_schema S)\<in>system_clauses first_request_joined_system"
      using rooted_system_agreement[of first_request_joined_system "fset first_request_roots",
          folded first_request_program_system_def] member clause
      unfolding systems_agree_on_def by blast
    then have "525\<in>system_definitions first_request_joined_system"
      using first_request_joined_formed unfolding schema_system_formed_def by blast
    then show False using bound unfolding first_request_joined_definitions by auto
  qed
qed

subsection \<open>The construction complete and the resolver exact there\<close>

theorem first_request_construction_complete:
  "finite_construction_complete (finite_collection_construction given_witness_registrations n) finite_first_request_program"
proof (rule finite_collection_construction_complete_at)
  fix R c
  assume R: "R \<in> set given_witness_registrations"
    and clause: "((registration_site R,c),registration_schema R) |\<in>| finite_system_clauses finite_first_request_program"
  show "finite_registration_complete finite_first_request_program n R"
    using R clause first_request_registrations_complete first_request_registered_clauses(4) registration_sites
    by (auto simp: given_witness_registrations_def)
qed

text \<open>
  The exact forms at that construction, R5's at no commitment, the construction's formation discharged
  (@{thm [source] finite_collection_construction_formed}): each leaves its consumer the resolution's premise alone.
\<close>

lemmas first_request_resolution_refutation_exact =
  finite_complete_resolution_refutation_exact[OF finite_collection_construction_formed first_request_construction_complete]

lemmas first_request_verdict_exact =
  finite_complete_verdict_exact[OF finite_collection_construction_formed first_request_construction_complete]

lemmas first_request_demand_exact =
  finite_complete_demand_exact[OF finite_collection_construction_formed first_request_construction_complete]

section \<open>Relocated at the installation\<close>

text \<open>
  The installation places the request's program by @{const first_request_placement}
  (@{thm [source] given_readers_extension.installed_placement_def}); the construction relocated by it is complete at
  the placed program (@{text relocated_construction_complete}), and every variable it registers names a clause
  of it (@{text relocated_registered_clause}). The placed program is the program the installation compiles
  into the installed package, whose meaning is the placed program's (@{thm [source] first_request_installation}).
\<close>

abbreviation first_request_relocated where
  "first_request_relocated n \<equiv> finite_relocated_construction first_request_placement finite_first_request_program
    (finite_collection_construction given_witness_registrations n)"

abbreviation first_request_placed where
  "first_request_placed \<equiv> finite_rename_system first_request_placement finite_first_request_program"


theorem first_request_relocated_complete:
  "finite_construction_complete (first_request_relocated n) first_request_placed"
  unfolding first_request_placement_def first_request_extension.installed_placement_def
  by (rule finite_mapped_native_extension.relocated_construction_complete[OF first_request_extension.mapped_extension
    first_request_construction_complete])

lemma first_request_relocated_clause:
  assumes "a |\<in>| witness_registered (first_request_relocated n) e T"
  shows "\<exists>c. ((e,c),T) |\<in>| finite_system_clauses first_request_placed"
  using assms unfolding first_request_placement_def first_request_extension.installed_placement_def
  by (rule finite_mapped_native_extension.relocated_registered_clause[OF first_request_extension.mapped_extension])

lemma first_request_relocated_formed: "finite_witness_construction_formed (first_request_relocated n)"
  by (rule finite_relocated_construction_formed[OF finite_collection_construction_formed])

lemmas first_request_placed_resolution_refutation_exact =
  finite_complete_resolution_refutation_exact[OF first_request_relocated_formed first_request_relocated_complete]

lemmas first_request_placed_verdict_exact =
  finite_complete_verdict_exact[OF first_request_relocated_formed first_request_relocated_complete]

lemmas first_request_placed_demand_exact =
  finite_complete_demand_exact[OF first_request_relocated_formed first_request_relocated_complete]

text \<open>
  Each definition means at its placed site in the placed program what it means in the program, and so what the
  installed program means there (@{thm [source] given_readers_extension.installed_meaning}): stated once for every
  extension of the given's readers.
\<close>

context given_readers_extension
begin

lemma placed_meaning:
  assumes "d\<in>system_definitions (decode_finite_system Q)"
  shows "(installed_placement d,t)\<in>positive_meaning (decode_finite_system (finite_rename_system installed_placement Q))
    \<longleftrightarrow> (d,t)\<in>positive_meaning (decode_finite_system Q)"
  unfolding finite_rename_system_correct by (rule renamed_meaning_at[OF target_formed installation(5) assms])

lemma placed_installed_meaning:
  assumes "d\<in>system_definitions (decode_finite_system Q)"
  shows "(installed_placement d,t)\<in>positive_meaning (decode_finite_system (finite_rename_system installed_placement Q))
    \<longleftrightarrow> (installed_placement d,t)\<in>positive_meaning installed_program"
  using placed_meaning[OF assms] installed_meaning[OF assms] by simp

end

lemma first_request_placed_meaning:
  assumes "d\<in>system_definitions first_request_program_system"
  shows "(first_request_placement d,t)\<in>positive_meaning (decode_finite_system first_request_placed) \<longleftrightarrow>
    (d,t)\<in>positive_meaning first_request_program_system"
  using first_request_extension.placed_meaning[of d t] assms
  unfolding first_request_placement_def finite_first_request_program_exact by simp

lemma first_request_placed_entry_meaning:
  "(first_request_entry,t)\<in>positive_meaning (decode_finite_system first_request_placed) \<longleftrightarrow>
    (first_request_entry,t)\<in>positive_meaning first_request_program"
  using first_request_extension.placed_installed_meaning[of 561 t] first_request_entry_member
  unfolding first_request_entry_def first_request_placement_def first_request_program_def finite_first_request_program_exact
  by simp

subsection \<open>561's registration's code, from the program's own clause\<close>

text \<open>
  As 77's and the additions notion's (@{thm [source] given_readers_registrations_code}): 561's registration's schema
  is the schema the first request's program holds at 561, read through its functional clause relation
  (@{const finite_relation_option}), proved equal to its definition from the program's clause
  (@{thm [source] first_request_registered_clauses}).
\<close>

lemma first_request_registration_schema:
  "finite_relation_option (finite_system_clauses finite_first_request_program) (561,0)=
    Some (finite_schema_of package_request_schema)"
proof -
  have functional: "finite_relation_functional (finite_system_clauses finite_first_request_program)"
    using finite_first_request_program_formed by (simp add: finite_system_formed_def)
  show ?thesis
    by (simp only: finite_relation_option_correct[OF functional])
      (simp add: first_request_registered_clauses finite_registration_matches_def merge_witness_registration_def)
qed

lemma first_request_registration_code [code]:
  "merge_witness_registration=\<lparr>registration_site=561,
    registration_schema=the (finite_relation_option (finite_system_clauses finite_first_request_program) (561,0)),
    registration_variable=7,
    registration_families=Paired_Families
      (row_witness_family 0 4 0 (Some artifact_row_witness_identity)) (row_witness_family 0 4 1 None)\<rparr>"
  by (simp only: first_request_registration_schema option.sel merge_witness_registration_def)

export_code merge_witness_registration finite_first_request_program checking SML

end