theory Development_Asked_Registrations
  imports Development_First_Problem_Asked Development_Given_Registrations
begin

text \<open>
  The given's witness registrations (\<open>Factor_Reader_Witness_Registrations\<close>) at the asked program, the two courses
  of the answer's judgment (DECISIONS.md, task 496's entry, "The route"). First, the numbered asked program
  (@{const finite_asked_program}): the registrations of 77 and 392 complete there from the discharges at the given's
  readers (\<open>Development_Given_Registrations\<close>), carried by the asked program's agreement with them; 525's, its listing
  at 524 over 523, from the guard's own facts on its goals program, carried by the asked program's agreement with the
  guard's program; the asked program holds no 561. The four's construction is complete there, the exact forms the
  complete ones at it, and the meaning at 526 is the installed entry's (@{thm [source] asked_installed_meaning}).
  Second, the program the installation places (\<open>asked_placed_program\<close>): the construction relocated by
  @{const asked_placement} is complete there (@{thm [source] finite_mapped_native_extension.relocated_construction_complete}),
  its exact forms at it, the meaning at the installed entry the installed package's. Every hypothesis is discharged
  from a fact the programs state; none is proved again.
\<close>

section \<open>The asked program agrees with the guard's program and with the given's readers\<close>

lemma asked_guard_agreement:
  "systems_agree_on first_problem_guard_system asked_program_system
    (system_definitions first_problem_guard_system\<inter>system_definitions asked_program_system)"
proof -
  let ?U="system_definitions first_problem_guard_system\<inter>system_definitions asked_program_system"
  have joined: "systems_agree_on first_problem_guard_system asked_joined_system
      (system_definitions first_problem_guard_system)"
    by (rule system_union_agree_right[OF given_program_formed asked_overlap_agreement, folded asked_joined_system_def])
  have rooted: "systems_agree_on asked_joined_system asked_program_system (system_definitions asked_program_system)"
    unfolding asked_program_system_def by (rule rooted_system_agreement)
  have "systems_agree_on first_problem_guard_system asked_joined_system ?U"
    by (rule systems_agree_on_subdomain[OF joined]) blast
  moreover have "systems_agree_on asked_joined_system asked_program_system ?U"
    by (rule systems_agree_on_subdomain[OF rooted]) blast
  ultimately show ?thesis by (rule systems_agree_on_transitive)
qed

lemma asked_readers_guard_agreement:
  "systems_agree_on guard_readers_system asked_program_system
    (system_definitions guard_readers_system\<inter>system_definitions asked_program_system)"
proof -
  let ?U="system_definitions guard_readers_system\<inter>system_definitions asked_program_system"
  have goals: "system_definitions guard_readers_system\<subseteq>system_definitions first_problem_goals_system"
    by (rule whole_agreement_definitions[OF goals_extension_agreement])
  have guard: "system_definitions first_problem_goals_system\<subseteq>system_definitions first_problem_guard_system"
    unfolding asked_guard_definitions by blast
  have "systems_agree_on guard_readers_system first_problem_goals_system ?U"
    by (rule systems_agree_on_subdomain[OF goals_extension_agreement]) blast
  moreover have "systems_agree_on first_problem_goals_system first_problem_guard_system ?U"
    by (rule systems_agree_on_subdomain[OF first_problem_guard.guarded_old_agreement]) (use goals in blast)
  moreover have "systems_agree_on first_problem_guard_system asked_program_system ?U"
    by (rule systems_agree_on_subdomain[OF asked_guard_agreement]) (use goals guard in blast)
  ultimately show ?thesis by (rule systems_agree_on_transitive[OF systems_agree_on_transitive])
qed

text \<open>
  A callee of a clause of a program agreeing with the asked program on their common definitions stands in both, when
  the clause's definition stands in the asked program: their common definitions are closed under the callees
  (@{thm [source] systems_agree_on_intersection_closed}).
\<close>

lemma asked_callee:
  assumes formed: "schema_system_formed P"
    and agree: "systems_agree_on P asked_program_system (system_definitions P\<inter>system_definitions asked_program_system)"
    and member: "d\<in>system_definitions asked_program_system" and clause: "((d,c),S)\<in>system_clauses P"
    and premise: "(s,e,p)\<in>schema_premises S"
  shows "e\<in>system_definitions P \<and> e\<in>system_definitions asked_program_system"
proof -
  have "d\<in>system_definitions P" using formed clause unfolding schema_system_formed_def by blast
  moreover have "(d,e)\<in>system_dependency_edges P"
    using clause premise unfolding system_dependency_edges_def schema_dependencies_def rel_ran_def by force
  ultimately show ?thesis
    using systems_agree_on_intersection_closed[OF formed asked_program_formed agree] member
    unfolding system_dependency_closed_def by blast
qed

lemma asked_readers_meaning_at:
  assumes "d\<in>system_definitions guard_readers_system" "d\<in>system_definitions asked_program_system"
  shows "(d,t)\<in>positive_meaning asked_program_system \<longleftrightarrow> (d,t)\<in>positive_meaning guard_readers_system"
  using positive_meaning_shared_definitions[OF guard_readers_formed asked_program_formed
    asked_readers_guard_agreement assms] by simp

lemma asked_goals_meaning_at:
  assumes goals: "d\<in>system_definitions first_problem_goals_system" and member: "d\<in>system_definitions asked_program_system"
  shows "(d,t)\<in>positive_meaning asked_program_system \<longleftrightarrow> (d,t)\<in>positive_meaning first_problem_goals_system"
proof -
  have "d\<in>system_definitions first_problem_guard_system" using goals unfolding asked_guard_definitions by blast
  then show ?thesis
    using asked_program_guard_meaning[OF member] first_problem_guard.unchanged_original_meaning[OF goals] by simp
qed

section \<open>The sites the registrations read stand in the asked program\<close>

lemma asked_reader_sites:
  "5\<in>system_definitions guard_readers_system" "5\<in>system_definitions asked_program_system"
  "47\<in>system_definitions guard_readers_system" "47\<in>system_definitions asked_program_system"
  "76\<in>system_definitions guard_readers_system" "76\<in>system_definitions asked_program_system"
  "82\<in>system_definitions guard_readers_system" "82\<in>system_definitions asked_program_system"
  "113\<in>system_definitions guard_readers_system" "113\<in>system_definitions asked_program_system"
  "390\<in>system_definitions guard_readers_system" "390\<in>system_definitions asked_program_system"
  "391\<in>system_definitions guard_readers_system" "391\<in>system_definitions asked_program_system"
  "392\<in>system_definitions guard_readers_system" "392\<in>system_definitions asked_program_system"
  "77\<in>system_definitions guard_readers_system" "77\<in>system_definitions asked_program_system"
proof -
  note callee=asked_callee[OF guard_readers_formed asked_readers_guard_agreement]
  have roots: "fset asked_roots\<subseteq>system_definitions asked_program_system"
    unfolding asked_program_system_def by (rule rooted_system_roots[OF asked_joined_formed asked_roots_joined])
  have entry: "d|\<in>|given_reader_entries \<Longrightarrow> d\<in>system_definitions asked_program_system" for d
    using roots by (auto simp: asked_roots_def)
  have guard: "d|\<in>|given_guard_entries \<Longrightarrow> d\<in>system_definitions guard_readers_system" for d
    using given_guard_entries_members by blast
  have transfer: "((d,c),S)\<in>system_clauses guard_readers_system"
    if agree: "systems_agree_on Q guard_readers_system (system_definitions Q)"
      and d: "d\<in>system_definitions Q" and clause: "((d,c),S)\<in>system_clauses Q" for Q d c S
    using agree d clause unfolding systems_agree_on_def by blast
  have a77: "77\<in>system_definitions asked_program_system" by (rule entry[OF given_rooted_members(2)])
  have c77: "((77,0),package_closure_admission_schema)\<in>system_clauses guard_readers_system"
    by (rule transfer[OF whole_agreement_transitive[OF given_reader_agreements(2) additions_guard_agreement]]) simp_all
  have p47: "(1,47,Pattern_Pair data_y data_z)\<in>schema_premises package_closure_admission_schema"
    by (simp add: package_closure_admission_schema_def)
  have p76: "(2,76,Pattern_Pair (Pattern_Pair data_x data_z) data_z)\<in>schema_premises package_closure_admission_schema"
    by (simp add: package_closure_admission_schema_def)
  have s47: "47\<in>system_definitions guard_readers_system \<and> 47\<in>system_definitions asked_program_system"
    by (rule callee[OF a77 c77 p47])
  have s76: "76\<in>system_definitions guard_readers_system \<and> 76\<in>system_definitions asked_program_system"
    by (rule callee[OF a77 c77 p76])
  have c47: "((47,1),data_subset_cons_schema)\<in>system_clauses guard_readers_system"
    by (rule transfer[OF whole_agreement_transitive[OF whole_agreement_transitive[OF whole_agreement_transitive[OF
      row_values_subset_agreement row_values_complete_data_agreement] complete_data_additions_agreement]
      additions_guard_agreement]]) (simp_all add: data_subset_clauses_def)
  have p5: "(0,5,Pattern_Pair data_x (Pattern_Pair data_z data_w))\<in>schema_premises data_subset_cons_schema"
    by (simp add: data_subset_cons_schema_def)
  have s5: "5\<in>system_definitions guard_readers_system \<and> 5\<in>system_definitions asked_program_system"
    using s47 by (intro callee[OF _ c47 p5]) blast
  have a392: "392\<in>system_definitions asked_program_system" by (rule entry[OF given_rooted_members(10)])
  have c392: "((392,0),package_additions_schema 391)\<in>system_clauses guard_readers_system"
    by (rule transfer[OF additions_guard_agreement]) (simp_all add: use_additions_families(3))
  have p391: "(5,391,Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair data_z data_w)))
      (Pattern_Variable 5))\<in>schema_premises (package_additions_schema 391)"
    by (simp add: package_additions_schema_def)
  have s391: "391\<in>system_definitions guard_readers_system \<and> 391\<in>system_definitions asked_program_system"
    by (rule callee[OF a392 c392 p391])
  have c391: "((391,1),context_list_step_schema 390 391)\<in>system_clauses guard_readers_system"
    by (rule transfer[OF additions_guard_agreement]) (simp_all add: use_additions_families(2) context_list_clauses_def)
  have p390: "(0,390,Pattern_Pair data_x data_y)\<in>schema_premises (context_list_step_schema 390 391)"
    by (simp add: context_list_step_schema_def)
  have s390: "390\<in>system_definitions guard_readers_system \<and> 390\<in>system_definitions asked_program_system"
    using s391 by (intro callee[OF _ c391 p390]) blast
  show "5\<in>system_definitions guard_readers_system" "5\<in>system_definitions asked_program_system"
    "47\<in>system_definitions guard_readers_system" "47\<in>system_definitions asked_program_system"
    "76\<in>system_definitions guard_readers_system" "76\<in>system_definitions asked_program_system"
    "390\<in>system_definitions guard_readers_system" "390\<in>system_definitions asked_program_system"
    "391\<in>system_definitions guard_readers_system" "391\<in>system_definitions asked_program_system"
    using s5 s47 s76 s390 s391 by blast+
  show "82\<in>system_definitions guard_readers_system" "113\<in>system_definitions guard_readers_system"
    "392\<in>system_definitions guard_readers_system" "77\<in>system_definitions guard_readers_system"
    by (rule guard[OF given_guard_members(6)], rule guard[OF given_guard_members(8)],
      rule guard[OF given_guard_members(10)], rule guard[OF given_guard_members(2)])
  show "82\<in>system_definitions asked_program_system" "113\<in>system_definitions asked_program_system"
    "392\<in>system_definitions asked_program_system" "77\<in>system_definitions asked_program_system"
    by (rule entry[OF given_rooted_members(6)], rule entry[OF given_rooted_members(8)], rule a392, rule a77)
qed

lemma asked_goal_sites:
  "523\<in>system_definitions first_problem_goals_system" "523\<in>system_definitions asked_program_system"
  "524\<in>system_definitions first_problem_goals_system" "524\<in>system_definitions asked_program_system"
  "525\<in>system_definitions first_problem_goals_system" "525\<in>system_definitions asked_program_system"
proof -
  note callee=asked_callee[OF asked_guard_formed asked_guard_agreement]
  have transfer: "((d,c),S)\<in>system_clauses first_problem_guard_system"
    if d: "d\<in>system_definitions first_problem_goals_system"
      and clause: "((d,c),S)\<in>system_clauses first_problem_goals_system" for d c S
    using first_problem_guard.guarded_old_agreement d clause unfolding systems_agree_on_def by blast
  show g: "523\<in>system_definitions first_problem_goals_system" "524\<in>system_definitions first_problem_goals_system"
    "525\<in>system_definitions first_problem_goals_system"
    by simp_all
  have c526: "((526,0),requirement_guard_schema first_problem_requirements)\<in>system_clauses first_problem_guard_system"
    by (simp add: first_problem_guard.guarded_clauses)
  have p525: "(3,525,data_x)\<in>schema_premises (requirement_guard_schema first_problem_requirements)"
    by (simp add: requirement_guard_schema_def first_problem_requirements_def)
  have a525: "525\<in>system_definitions asked_program_system"
    using callee[OF asked_entry_member c526 p525] by blast
  have c525: "((525,0),package_additions_schema 524)\<in>system_clauses first_problem_guard_system"
    by (rule transfer[OF g(3)]) (simp only: first_problem_goals_families(6) simp_thms)
  have p524: "(5,524,Pattern_Pair (Pattern_Pair data_x (Pattern_Pair data_y (Pattern_Pair data_z data_w)))
      (Pattern_Variable 5))\<in>schema_premises (package_additions_schema 524)"
    by (simp add: package_additions_schema_def)
  have a524: "524\<in>system_definitions asked_program_system"
    using callee[OF a525 c525 p524] by blast
  have c524: "((524,1),context_list_step_schema 523 524)\<in>system_clauses first_problem_guard_system"
    by (rule transfer[OF g(2)]) (simp add: first_problem_goals_families(5) context_list_clauses_def)
  have p523: "(0,523,Pattern_Pair data_x data_y)\<in>schema_premises (context_list_step_schema 523 524)"
    by (simp add: context_list_step_schema_def)
  show "523\<in>system_definitions asked_program_system" using callee[OF a524 c524 p523] by blast
  show "524\<in>system_definitions asked_program_system" "525\<in>system_definitions asked_program_system"
    by (rule a524, rule a525)
qed

text \<open>The asked program holds no 561: its definitions are the given's joined program's and the guard's.\<close>

lemma asked_absent_561: "561\<notin>system_definitions asked_program_system"
proof
  assume member: "561\<in>system_definitions asked_program_system"
  have "system_definitions asked_program_system\<subseteq>system_definitions asked_joined_system"
    unfolding asked_program_system_def by (rule rooted_system_subdomain)
  then have "561\<in>system_definitions given_program_system \<or> 561\<in>system_definitions first_problem_guard_system"
    using member asked_joined_definitions by blast
  moreover have readers: "561\<notin>system_definitions guard_readers_system"
  proof
    assume "561\<in>system_definitions guard_readers_system"
    then have "(561::nat)<506" using guard_readers_definitions additions_below audit_below by auto
    then show False by simp
  qed
  moreover have "561\<notin>system_definitions granted_readers_system" using granted_readers_bound by auto
  ultimately show False using readers by (auto simp: given_program_definitions asked_guard_definitions)
qed

section \<open>The first course: the numbered asked program\<close>

subsection \<open>The meanings and the listings the registrations ask\<close>

lemma asked_readers_meanings:
  "(5,t)\<in>positive_meaning asked_program_system \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  "(47,t)\<in>positive_meaning asked_program_system \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
  "(76,t)\<in>positive_meaning asked_program_system \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
  "(82,t)\<in>positive_meaning asked_program_system \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
  "(113,t)\<in>positive_meaning asked_program_system \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
  using asked_readers_meaning_at[OF asked_reader_sites(1,2)] asked_readers_meaning_at[OF asked_reader_sites(3,4)]
    asked_readers_meaning_at[OF asked_reader_sites(5,6)] asked_readers_meaning_at[OF asked_reader_sites(7,8)]
    asked_readers_meaning_at[OF asked_reader_sites(9,10)] given_readers_meanings
  by simp_all

lemma asked_readers_listing: "context_list_rule_relation (positive_meaning asked_program_system) 390 391"
proof -
  have e: "(390,t)\<in>positive_meaning asked_program_system \<longleftrightarrow> (390,t)\<in>positive_meaning guard_readers_system"
    "(391,t)\<in>positive_meaning asked_program_system \<longleftrightarrow> (391,t)\<in>positive_meaning guard_readers_system" for t
    using asked_readers_meaning_at[OF asked_reader_sites(11,12)] asked_readers_meaning_at[OF asked_reader_sites(13,14)]
    by simp_all
  show ?thesis
    by (rule context_list_rule_relation.intro) (unfold e, rule context_list_rule_relation.equation[OF given_readers_listing])
qed

lemma asked_goals_listing: "context_list_rule_relation (positive_meaning asked_program_system) 523 524"
proof -
  have e: "(523,t)\<in>positive_meaning asked_program_system \<longleftrightarrow> (523,t)\<in>positive_meaning first_problem_goals_system"
    "(524,t)\<in>positive_meaning asked_program_system \<longleftrightarrow> (524,t)\<in>positive_meaning first_problem_goals_system" for t
    using asked_goals_meaning_at[OF asked_goal_sites(1,2)] asked_goals_meaning_at[OF asked_goal_sites(3,4)]
    by simp_all
  show ?thesis
    by (rule context_list_rule_relation.intro) (unfold e, rule audit_additions.listing.semantics.equation)
qed

subsection \<open>The registrations complete there\<close>

theorem asked_registrations_complete:
  "finite_registration_complete finite_asked_program n bound_witness_registration"
  "finite_registration_complete finite_asked_program n (additions_witness_registration 392 391)"
  "finite_registration_complete finite_asked_program n (additions_witness_registration 525 524)"
proof -
  show "finite_registration_complete finite_asked_program n bound_witness_registration"
    by (rule bound_witness_registration_complete)
      (simp_all only: finite_asked_program_exact asked_readers_meanings)
  show "finite_registration_complete finite_asked_program n (additions_witness_registration 392 391)"
    by (rule additions_witness_registration_complete[where element_site=390])
      (simp_all only: finite_asked_program_exact asked_readers_meanings asked_readers_listing)
  show "finite_registration_complete finite_asked_program n (additions_witness_registration 525 524)"
    by (rule additions_witness_registration_complete[where element_site=523])
      (simp_all only: finite_asked_program_exact asked_readers_meanings asked_goals_listing)
qed

subsection \<open>The clauses the registrations name\<close>

lemma asked_readers_finite_clauses:
  assumes "d\<in>system_definitions guard_readers_system" "d\<in>system_definitions asked_program_system"
  shows "((d,c),S) |\<in>| finite_system_clauses finite_asked_program \<longleftrightarrow>
    ((d,c),S) |\<in>| finite_system_clauses finite_given_readers"
proof -
  have "((d,c),decode_finite_schema S)\<in>system_clauses asked_program_system \<longleftrightarrow>
      ((d,c),decode_finite_schema S)\<in>system_clauses guard_readers_system"
    using asked_readers_guard_agreement assms unfolding systems_agree_on_def by blast
  then show ?thesis by (simp only: finite_system_clause_decoded finite_asked_program_exact finite_given_readers_exact)
qed

lemma asked_single_clause:
  assumes single: "\<And>c T. ((d,c),T)\<in>system_clauses asked_program_system \<longleftrightarrow> c=0 \<and> T=X"
  shows "((d,c),S) |\<in>| finite_system_clauses finite_asked_program \<longleftrightarrow> c=0 \<and> finite_schema_of X=S"
proof -
  have formed: "schema_formed X"
    using asked_program_formed single[of 0 X] unfolding schema_system_formed_def by blast
  have eq: "decode_finite_schema S=X \<longleftrightarrow> finite_schema_of X=S"
    by (metis decode_finite_schema_of[OF formed] decode_finite_schema_injective)
  show ?thesis
    by (simp only: finite_system_clause_decoded finite_asked_program_exact single eq)
qed

theorem asked_registered_clauses:
  "((77,c),S) |\<in>| finite_system_clauses finite_asked_program \<longleftrightarrow>
    c=0 \<and> finite_registration_matches 77 S bound_witness_registration"
  "((392,c),S) |\<in>| finite_system_clauses finite_asked_program \<longleftrightarrow>
    c=0 \<and> finite_registration_matches 392 S (additions_witness_registration 392 391)"
  "((525,c),S) |\<in>| finite_system_clauses finite_asked_program \<longleftrightarrow>
    c=0 \<and> finite_registration_matches 525 S (additions_witness_registration 525 524)"
  "((561,c),S) |\<notin>| finite_system_clauses finite_asked_program"
proof -
  show "((77,c),S) |\<in>| finite_system_clauses finite_asked_program \<longleftrightarrow>
      c=0 \<and> finite_registration_matches 77 S bound_witness_registration"
    by (simp only: asked_readers_finite_clauses[OF asked_reader_sites(17,18)] given_readers_registered_clauses(1))
  show "((392,c),S) |\<in>| finite_system_clauses finite_asked_program \<longleftrightarrow>
      c=0 \<and> finite_registration_matches 392 S (additions_witness_registration 392 391)"
    by (simp only: asked_readers_finite_clauses[OF asked_reader_sites(15,16)] given_readers_registered_clauses(2))
  have guard: "525\<in>system_definitions first_problem_guard_system"
    using asked_goal_sites(5) unfolding asked_guard_definitions by blast
  have at525: "((525,c),T)\<in>system_clauses asked_program_system \<longleftrightarrow> c=0 \<and> T=package_additions_schema 524" for c T
  proof -
    have "((525,c),T)\<in>system_clauses asked_program_system \<longleftrightarrow> ((525,c),T)\<in>system_clauses first_problem_guard_system"
      using asked_guard_agreement guard asked_goal_sites(6) unfolding systems_agree_on_def by blast
    also have "\<dots> \<longleftrightarrow> ((525,c),T)\<in>system_clauses first_problem_goals_system"
      using first_problem_guard.guarded_old_agreement asked_goal_sites(5) unfolding systems_agree_on_def by blast
    finally show ?thesis by (simp only: first_problem_goals_families(6))
  qed
  show "((525,c),S) |\<in>| finite_system_clauses finite_asked_program \<longleftrightarrow>
      c=0 \<and> finite_registration_matches 525 S (additions_witness_registration 525 524)"
    by (simp only: asked_single_clause[OF at525] finite_registration_matches_def
      additions_witness_registration_def closure_witness_registration_def collection_registration.simps simp_thms)
  show "((561,c),S) |\<notin>| finite_system_clauses finite_asked_program"
  proof
    assume "((561,c),S) |\<in>| finite_system_clauses finite_asked_program"
    then have "((561,c),decode_finite_schema S)\<in>system_clauses asked_program_system"
      by (simp only: finite_system_clause_decoded finite_asked_program_exact)
    then have "561\<in>system_definitions asked_program_system"
      using asked_program_formed unfolding schema_system_formed_def by blast
    then show False using asked_absent_561 by blast
  qed
qed

subsection \<open>The construction complete and the resolver exact there\<close>

theorem asked_construction_complete:
  "finite_construction_complete (finite_collection_construction given_witness_registrations n) finite_asked_program"
proof (rule finite_collection_construction_complete_at)
  fix R c
  assume R: "R \<in> set given_witness_registrations"
    and clause: "((registration_site R,c),registration_schema R) |\<in>| finite_system_clauses finite_asked_program"
  show "finite_registration_complete finite_asked_program n R"
    using R clause asked_registrations_complete asked_registered_clauses(4) registration_sites
    by (auto simp: given_witness_registrations_def)
qed

text \<open>
  The exact forms at that construction, R5's at no commitment: the complete forms, since the registered forms ask
  561's registration complete at a program holding no 561 clause.
\<close>

lemmas asked_resolution_refutation_exact =
  finite_complete_resolution_refutation_exact[OF finite_collection_construction_formed asked_construction_complete]

lemmas asked_verdict_exact =
  finite_complete_verdict_exact[OF finite_collection_construction_formed asked_construction_complete]

lemmas asked_demand_exact =
  finite_complete_demand_exact[OF finite_collection_construction_formed asked_construction_complete]

text \<open>The meaning at the numbered entry is the installed entry's.\<close>

lemma asked_entry_numbered_meaning:
  "(asked_entry,t)\<in>positive_meaning asked_program \<longleftrightarrow>
    (526,t)\<in>positive_meaning (decode_finite_system finite_asked_program)"
  unfolding asked_entry_def finite_asked_program_exact by (rule asked_installed_meaning[OF asked_entry_member])

section \<open>The second course: the placed program, the registrations relocated\<close>

definition asked_placed_program where
  "asked_placed_program=finite_rename_system asked_placement finite_asked_program"

definition asked_relocated_construction where
  "asked_relocated_construction n=finite_relocated_construction asked_placement finite_asked_program
    (finite_collection_construction given_witness_registrations n)"

lemma asked_placement_coordinates:
  "asked_placement=finite_program_coordinates given_environment (finite_system_definitions finite_rooted_given_readers)
    (finite_system_definitions finite_asked_program) given_readers_placement"
  by (simp only: asked_placement_def asked_extension.installed_placement_def)

text \<open>The installation is the mapped extension of the given's reader package by the asked program.\<close>

lemma asked_mapped_extension:
  "finite_mapped_native_extension given_environment finite_rooted_given_readers finite_asked_program
    (snd given_readers_installed) [] given_readers_program given_readers_placement"
  by (rule finite_mapped_native_extension.intro[OF given_readers_extensible(1,2) finite_asked_program_formed
    finite_asked_program_extends given_readers_extensible(3,4)])

theorem asked_relocated_construction_complete:
  "finite_construction_complete (asked_relocated_construction n) asked_placed_program"
  unfolding asked_relocated_construction_def asked_placed_program_def asked_placement_coordinates
  by (rule finite_mapped_native_extension.relocated_construction_complete[OF asked_mapped_extension
    asked_construction_complete])

lemma asked_relocated_registered_clause:
  assumes "a |\<in>| witness_registered (asked_relocated_construction n) e T"
  shows "\<exists>c. ((e,c),T) |\<in>| finite_system_clauses asked_placed_program"
  using finite_mapped_native_extension.relocated_registered_clause[OF asked_mapped_extension] assms
  unfolding asked_relocated_construction_def asked_placed_program_def asked_placement_coordinates by blast

lemma asked_relocated_formed: "finite_witness_construction_formed (asked_relocated_construction n)"
  unfolding asked_relocated_construction_def
  by (rule finite_relocated_construction_formed[OF finite_collection_construction_formed])

lemmas asked_placed_resolution_refutation_exact =
  finite_complete_resolution_refutation_exact[OF asked_relocated_formed asked_relocated_construction_complete]

lemmas asked_placed_verdict_exact =
  finite_complete_verdict_exact[OF asked_relocated_formed asked_relocated_construction_complete]

lemmas asked_placed_demand_exact =
  finite_complete_demand_exact[OF asked_relocated_formed asked_relocated_construction_complete]

text \<open>The placed program means the numbered program at the placed sites, and the installed package at its entry.\<close>

lemma asked_placement_injective: "inj_on asked_placement (system_definitions asked_program_system)"
  by (rule asked_correct[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1])

lemma asked_placed_meaning:
  assumes "d\<in>system_definitions asked_program_system"
  shows "(asked_placement d,t)\<in>positive_meaning (decode_finite_system asked_placed_program) \<longleftrightarrow>
    (d,t)\<in>positive_meaning asked_program_system"
  unfolding asked_placed_program_def finite_rename_system_correct finite_asked_program_exact
  by (rule renamed_meaning_at[OF asked_program_formed asked_placement_injective assms])

lemma asked_placed_entry_meaning:
  "(asked_entry,t)\<in>positive_meaning (decode_finite_system asked_placed_program) \<longleftrightarrow>
    (asked_entry,t)\<in>positive_meaning asked_program"
  by (simp only: asked_entry_def asked_placed_meaning[OF asked_entry_member]
    asked_installed_meaning[OF asked_entry_member])

end
