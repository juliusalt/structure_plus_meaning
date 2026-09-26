theory Development_Asked_Registrations
  imports Development_First_Problem_Asked Development_Rooted_Registrations
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
  unfolding asked_program_system_def
  by (rule rooted_intersection_agreement[OF whole_agreement_transitive[OF guard_program_agreement asked_given_agreement]])

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

lemma asked_sites: "{5,12,47,76,82,113,390,391}\<subseteq>system_definitions asked_program_system"
  using given_rooted_read_sites(1) asked_readers_inside by blast

lemma asked_readers_meaning_at:
  assumes "d\<in>system_definitions guard_readers_system" "d\<in>system_definitions asked_program_system"
  shows "(d,t)\<in>positive_meaning asked_program_system \<longleftrightarrow> (d,t)\<in>positive_meaning guard_readers_system"
  by (rule readers_agreement_meanings(1)[OF asked_program_formed asked_readers_guard_agreement asked_sites assms])

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
  have g: "d\<in>system_definitions guard_readers_system" if "d\<in>{5,47,76,82,113,390,391,392,77}" for d
    using that given_rooted_read_sites(2)[of d] given_rooted_entry_sites(1,3) by auto
  have a: "d\<in>system_definitions asked_program_system" if "d\<in>{5,47,76,82,113,390,391,392,77}" for d
    using that given_rooted_read_sites(1)[of d] given_rooted_entry_sites(2,4) asked_readers_inside by auto
  show "5\<in>system_definitions guard_readers_system" "5\<in>system_definitions asked_program_system"
    "47\<in>system_definitions guard_readers_system" "47\<in>system_definitions asked_program_system"
    "76\<in>system_definitions guard_readers_system" "76\<in>system_definitions asked_program_system"
    "82\<in>system_definitions guard_readers_system" "82\<in>system_definitions asked_program_system"
    "113\<in>system_definitions guard_readers_system" "113\<in>system_definitions asked_program_system"
    "390\<in>system_definitions guard_readers_system" "390\<in>system_definitions asked_program_system"
    "391\<in>system_definitions guard_readers_system" "391\<in>system_definitions asked_program_system"
    "392\<in>system_definitions guard_readers_system" "392\<in>system_definitions asked_program_system"
    "77\<in>system_definitions guard_readers_system" "77\<in>system_definitions asked_program_system"
    by (simp_all only: g a insert_iff simp_thms)
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
  by (simp_all only: readers_agreement_meanings(3,5,6,7,8)[OF asked_program_formed asked_readers_guard_agreement
    asked_sites])

lemma asked_readers_listing: "context_list_rule_relation (positive_meaning asked_program_system) 390 391"
  by (rule readers_agreement_meanings(9)[OF asked_program_formed asked_readers_guard_agreement asked_sites])

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
  note by_agreement=readers_agreement_registrations_complete[where P=finite_asked_program,
    unfolded finite_asked_program_exact, OF asked_program_formed asked_readers_guard_agreement asked_sites]
  show "finite_registration_complete finite_asked_program n bound_witness_registration"
    by (rule by_agreement(1))
  show "finite_registration_complete finite_asked_program n (additions_witness_registration 392 391)"
    by (rule by_agreement(2))
  show "finite_registration_complete finite_asked_program n (additions_witness_registration 525 524)"
    by (rule additions_witness_registration_complete[where element_site=523])
      (simp_all only: finite_asked_program_exact asked_readers_meanings asked_goals_listing)
qed

subsection \<open>The clauses the registrations name\<close>

lemma asked_readers_finite_clauses:
  assumes "d\<in>system_definitions guard_readers_system" "d\<in>system_definitions asked_program_system"
  shows "((d,c),S) |\<in>| finite_system_clauses finite_asked_program \<longleftrightarrow>
    ((d,c),S) |\<in>| finite_system_clauses finite_given_readers"
  by (rule readers_agreement_finite_clauses[where P=finite_asked_program,
    unfolded finite_asked_program_exact, OF asked_readers_guard_agreement assms])

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

lemmas asked_mapped_extension=asked_extension.mapped_extension

text \<open>The placed course is the instance of the one every extension of the given's readers has.\<close>

theorem asked_relocated_construction_complete:
  "finite_construction_complete (asked_relocated_construction n) asked_placed_program"
  unfolding asked_relocated_construction_def asked_placed_program_def asked_placement_def
  by (rule given_readers_extension.relocated_complete[OF asked_extension.readers_extension asked_construction_complete])

lemma asked_relocated_registered_clause:
  assumes "a |\<in>| witness_registered (asked_relocated_construction n) e T"
  shows "\<exists>c. ((e,c),T) |\<in>| finite_system_clauses asked_placed_program"
  using assms unfolding asked_relocated_construction_def asked_placed_program_def asked_placement_def
  by (rule given_readers_extension.relocated_clause[OF asked_extension.readers_extension])

lemma asked_relocated_formed: "finite_witness_construction_formed (asked_relocated_construction n)"
  unfolding asked_relocated_construction_def
  by (rule finite_relocated_construction_formed[OF finite_collection_construction_formed])

lemmas asked_placed_resolution_refutation_exact =
  given_readers_extension.placed_resolution_refutation_exact[OF asked_extension.readers_extension finite_collection_construction_formed asked_construction_complete,
    folded asked_placement_def asked_relocated_construction_def asked_placed_program_def]

lemmas asked_placed_verdict_exact =
  given_readers_extension.placed_verdict_exact[OF asked_extension.readers_extension finite_collection_construction_formed asked_construction_complete,
    folded asked_placement_def asked_relocated_construction_def asked_placed_program_def]

lemmas asked_placed_demand_exact =
  given_readers_extension.placed_demand_exact[OF asked_extension.readers_extension finite_collection_construction_formed asked_construction_complete,
    folded asked_placement_def asked_relocated_construction_def asked_placed_program_def]

text \<open>The placed program means the numbered program at the placed sites, and the installed package at its entry.\<close>

lemma asked_placement_injective: "inj_on asked_placement (system_definitions asked_program_system)"
  by (rule asked_correct[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1])

lemma asked_placed_meaning:
  assumes "d\<in>system_definitions asked_program_system"
  shows "(asked_placement d,t)\<in>positive_meaning (decode_finite_system asked_placed_program) \<longleftrightarrow>
    (d,t)\<in>positive_meaning asked_program_system"
  using asked_extension.placed_meaning[of d t] assms
  unfolding asked_placed_program_def asked_placement_def finite_asked_program_exact by simp

lemma asked_placed_entry_meaning:
  "(asked_entry,t)\<in>positive_meaning (decode_finite_system asked_placed_program) \<longleftrightarrow>
    (asked_entry,t)\<in>positive_meaning asked_program"
  by (simp only: asked_entry_def asked_placed_meaning[OF asked_entry_member]
    asked_installed_meaning[OF asked_entry_member])

end
