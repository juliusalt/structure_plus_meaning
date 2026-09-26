theory Development_Rooted_Registrations
  imports Development_Given_Installation Development_Given_Registrations
begin

text \<open>
  The given's witness registrations of 77 and 392 (\<open>Factor_Reader_Witness_Registrations\<close>) complete at the program
  the given's own installation places, the rooted readers (@{const finite_rooted_given_readers}), discharged there
  from that program's meanings, as \<open>Development_Given_Registrations\<close> discharges them at the given's readers
  (@{const finite_given_readers}). The rooted readers agree with the given's readers on their common definitions
  (the rooted closure of the joined program, which agrees with the given's readers on theirs); the read sites the
  registrations ask stand in both (@{text given_rooted_read_sites}, the walks over the given's readers' clauses), and
  mean there what the given's readers mean (@{thm [source] given_readers_meanings}, @{thm [source] given_readers_listing}): 82 and 113, guard
  entries, through @{thm [source] given_rooted_guard_meaning}, the others through the agreement. The clauses at 77
  and 392 are the given's readers' there, matched as @{thm [source] given_readers_registered_clauses} matches them; no
  clause stands at 525 or 561. No completeness is carried from another program.
\<close>

section \<open>The rooted readers agree with the given's readers\<close>

lemma given_rooted_guard_agreement:
  "systems_agree_on guard_readers_system given_rooted_readers_system
    (system_definitions guard_readers_system\<inter>system_definitions given_rooted_readers_system)"
proof -
  let ?U="system_definitions guard_readers_system\<inter>system_definitions given_rooted_readers_system"
  have rooted: "systems_agree_on given_program_system given_rooted_readers_system
      (system_definitions given_rooted_readers_system)"
    unfolding given_rooted_readers_system_def by (rule rooted_system_agreement)
  have "systems_agree_on guard_readers_system given_program_system ?U"
    by (rule systems_agree_on_subdomain[OF guard_program_agreement]) blast
  moreover have "systems_agree_on given_program_system given_rooted_readers_system ?U"
    by (rule systems_agree_on_subdomain[OF rooted]) blast
  ultimately show ?thesis by (rule systems_agree_on_transitive)
qed

lemma given_rooted_readers_meaning_at:
  assumes "d\<in>system_definitions guard_readers_system" "d\<in>system_definitions given_rooted_readers_system"
  shows "(d,t)\<in>positive_meaning given_rooted_readers_system \<longleftrightarrow> (d,t)\<in>positive_meaning guard_readers_system"
  using positive_meaning_shared_definitions[OF guard_readers_formed given_rooted_readers_formed
    given_rooted_guard_agreement assms] by simp

section \<open>The sites the registrations read stand in the rooted readers\<close>

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

lemma given_rooted_read_meaning:
  assumes "d\<in>{5,12,47,76,82,113,390,391}"
  shows "(d,t)\<in>positive_meaning given_rooted_readers_system \<longleftrightarrow> (d,t)\<in>positive_meaning guard_readers_system"
  by (rule given_rooted_readers_meaning_at[OF given_rooted_read_sites(2)[OF assms] given_rooted_read_sites(1)[OF assms]])

text \<open>77 and 392 are entries of the given's readers and roots of the rooted readers.\<close>

lemma given_rooted_entry_sites:
  "392\<in>system_definitions guard_readers_system" "392\<in>system_definitions given_rooted_readers_system"
  "77\<in>system_definitions guard_readers_system" "77\<in>system_definitions given_rooted_readers_system"
  using given_guard_entries_members given_rooted_entries given_guard_members(2,10) given_rooted_members(2,10)
  by blast+

text \<open>The rooted readers hold neither 525 nor 561: their definitions are the given's readers' and the granted ones.\<close>

lemma given_rooted_absent:
  assumes d: "d\<in>{525,561}"
  shows "d\<notin>system_definitions given_rooted_readers_system"
proof
  assume member: "d\<in>system_definitions given_rooted_readers_system"
  have "system_definitions given_rooted_readers_system\<subseteq>system_definitions given_program_system"
    unfolding given_rooted_readers_system_def by (rule rooted_system_subdomain)
  then have "d\<in>system_definitions guard_readers_system \<or> d\<in>system_definitions granted_readers_system"
    using member by (auto simp: given_program_definitions)
  moreover have "d\<notin>system_definitions guard_readers_system"
  proof
    assume "d\<in>system_definitions guard_readers_system"
    then have "d<506" using guard_readers_definitions additions_below audit_below by auto
    then show False using d by auto
  qed
  moreover have "d\<notin>system_definitions granted_readers_system" using granted_readers_bound d by auto
  ultimately show False by blast
qed

section \<open>The meanings and the listing the registrations ask\<close>

lemma given_rooted_readers_meanings:
  "(5,t)\<in>positive_meaning given_rooted_readers_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(47,t)\<in>positive_meaning given_rooted_readers_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  "(76,t)\<in>positive_meaning given_rooted_readers_system \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
  "(82,t)\<in>positive_meaning given_rooted_readers_system \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
  "(113,t)\<in>positive_meaning given_rooted_readers_system \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
  using given_rooted_read_meaning[of 5 t] given_rooted_read_meaning[of 47 t] given_rooted_read_meaning[of 76 t]
    given_rooted_guard_meaning[OF given_guard_members(6)] given_rooted_guard_meaning[OF given_guard_members(8)]
    given_readers_meanings
  by simp_all

lemma given_rooted_readers_listing: "context_list_rule_relation (positive_meaning given_rooted_readers_system) 390 391"
proof -
  have e: "(390,t)\<in>positive_meaning given_rooted_readers_system \<longleftrightarrow> (390,t)\<in>positive_meaning guard_readers_system"
    "(391,t)\<in>positive_meaning given_rooted_readers_system \<longleftrightarrow> (391,t)\<in>positive_meaning guard_readers_system" for t
    using given_rooted_read_meaning[of 390 t] given_rooted_read_meaning[of 391 t]
    by simp_all
  show ?thesis
    by (rule context_list_rule_relation.intro) (unfold e, rule context_list_rule_relation.equation[OF given_readers_listing])
qed

section \<open>The registrations complete there\<close>

theorem given_rooted_registrations_complete:
  "finite_registration_complete finite_rooted_given_readers n bound_witness_registration"
  "finite_registration_complete finite_rooted_given_readers n (additions_witness_registration 392 391)"
proof -
  show "finite_registration_complete finite_rooted_given_readers n bound_witness_registration"
    by (rule bound_witness_registration_complete)
      (simp_all only: finite_rooted_given_readers_exact given_rooted_readers_meanings)
  show "finite_registration_complete finite_rooted_given_readers n (additions_witness_registration 392 391)"
    by (rule additions_witness_registration_complete[where element_site=390])
      (simp_all only: finite_rooted_given_readers_exact given_rooted_readers_meanings given_rooted_readers_listing)
qed

section \<open>The clauses the registrations name\<close>

lemma given_rooted_finite_clauses:
  assumes "d\<in>system_definitions guard_readers_system" "d\<in>system_definitions given_rooted_readers_system"
  shows "((d,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers \<longleftrightarrow>
    ((d,c),S) |\<in>| finite_system_clauses finite_given_readers"
proof -
  have "((d,c),decode_finite_schema S)\<in>system_clauses given_rooted_readers_system \<longleftrightarrow>
      ((d,c),decode_finite_schema S)\<in>system_clauses guard_readers_system"
    using given_rooted_guard_agreement assms unfolding systems_agree_on_def by blast
  then show ?thesis
    by (simp only: finite_system_clause_decoded finite_rooted_given_readers_exact finite_given_readers_exact)
qed

theorem given_rooted_registered_clauses:
  "((77,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers \<longleftrightarrow>
    c=0 \<and> finite_registration_matches 77 S bound_witness_registration"
  "((392,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers \<longleftrightarrow>
    c=0 \<and> finite_registration_matches 392 S (additions_witness_registration 392 391)"
  "((525,c),S) |\<notin>| finite_system_clauses finite_rooted_given_readers"
  "((561,c),S) |\<notin>| finite_system_clauses finite_rooted_given_readers"
proof -
  show "((77,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers \<longleftrightarrow>
      c=0 \<and> finite_registration_matches 77 S bound_witness_registration"
    by (simp only: given_rooted_finite_clauses[OF given_rooted_entry_sites(3,4)] given_readers_registered_clauses(1))
  show "((392,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers \<longleftrightarrow>
      c=0 \<and> finite_registration_matches 392 S (additions_witness_registration 392 391)"
    by (simp only: given_rooted_finite_clauses[OF given_rooted_entry_sites(1,2)] given_readers_registered_clauses(2))
  have absent: "((d,c),S) |\<notin>| finite_system_clauses finite_rooted_given_readers" if d: "d\<in>{525,561}" for d
  proof
    assume "((d,c),S) |\<in>| finite_system_clauses finite_rooted_given_readers"
    then have "((d,c),decode_finite_schema S)\<in>system_clauses given_rooted_readers_system"
      by (simp only: finite_system_clause_decoded finite_rooted_given_readers_exact)
    then have "d\<in>system_definitions given_rooted_readers_system"
      using given_rooted_readers_formed unfolding schema_system_formed_def by blast
    then show False using given_rooted_absent[OF d] by blast
  qed
  show "((525,c),S) |\<notin>| finite_system_clauses finite_rooted_given_readers" by (rule absent) simp
  show "((561,c),S) |\<notin>| finite_system_clauses finite_rooted_given_readers" by (rule absent) simp
qed

section \<open>The construction complete and the resolver exact there\<close>

theorem given_rooted_construction_complete:
  "finite_construction_complete (finite_collection_construction given_witness_registrations n)
    finite_rooted_given_readers"
proof (rule finite_collection_construction_complete_at)
  fix R c
  assume R: "R \<in> set given_witness_registrations"
    and clause: "((registration_site R,c),registration_schema R) |\<in>| finite_system_clauses finite_rooted_given_readers"
  show "finite_registration_complete finite_rooted_given_readers n R"
    using R clause given_rooted_registrations_complete given_rooted_registered_clauses(3,4) registration_sites
    by (auto simp: given_witness_registrations_def)
qed

text \<open>
  The exact forms at that construction, R5's at no commitment, the construction's formation discharged
  (@{thm [source] finite_collection_construction_formed}): the complete forms, since the registered forms ask the
  registrations of 525 and 561 complete at a program holding neither clause.
\<close>

lemmas given_rooted_resolution_refutation_exact =
  finite_complete_resolution_refutation_exact[OF finite_collection_construction_formed given_rooted_construction_complete]

lemmas given_rooted_verdict_exact =
  finite_complete_verdict_exact[OF finite_collection_construction_formed given_rooted_construction_complete]

lemmas given_rooted_demand_exact =
  finite_complete_demand_exact[OF finite_collection_construction_formed given_rooted_construction_complete]

end
