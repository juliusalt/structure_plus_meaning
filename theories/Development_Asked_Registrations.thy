theory Development_Asked_Registrations
  imports Development_First_Problem_Asked Development_Rooted_Registrations Factor_Extension_Registrations
begin

text \<open>
  The given's witness registrations (\<open>Factor_Reader_Witness_Registrations\<close>) and the added part's bound
  (\<open>Factor_Extension_Registrations\<close>) at the asked relation's program, the two courses of the answer's judgment
  (DECISIONS.md, task 496's entry, "The route"), at the asked relation over additions (task 928's entry, course (c),
  AX4). First, the numbered program (@{const finite_asked_additions_program}): the registrations of 77, 392 and 561
  complete there from the discharges at the given's readers, carried by the program's agreement with them; 960's from
  AX2a's facts, carried by its agreement with AX2a's program. The construction is complete there, the exact forms the
  complete ones at it. Second, the program the installation places (\<open>asked_additions_placed_program\<close>): the
  construction relocated by @{const asked_additions_placement} is complete there, its exact forms at it. Every
  hypothesis is discharged from a fact the programs state; none is proved again. The registrations at the asked
  program over pairs of site values (\<open>Development_First_Problem_Asked\<close>'s first section), which this program
  supersedes, are retired (task 928's entry); that program and its guard stay as landed content.
\<close>

section \<open>The asked relation over additions: the registrations at its program\<close>

text \<open>
  Course (c) of task 928's entry (AX4): the asked relation reads a candidate by its additions, its program the guard
  over additions joined with the given's readers and rooted at their entries and 990
  (@{const finite_asked_additions_program}). The given's registrations there: 77's, 392's and 561's complete by the
  program's agreement with the given's readers (@{thm [source] readers_agreement_registrations_complete_in}); 525 and
  561 are held by no clause there, the guard over additions reading the added members through G3 and G4 instead. The
  added part's bound (960, @{const extension_bound_registration}) is complete there by the program's agreement with
  AX2a's program at 959. The least environment's registration (961/0) is not: its rows are read at 965, which no
  clause calls, so 965 stands outside the rooted program. The construction is the given's four with 960's bound, the
  placed course its relocation.
\<close>

text \<open>A callee of a clause of an agreeing program stands in both, when the clause's definition stands in the second.\<close>

lemma agreeing_clause_callee:
  assumes formed: "schema_system_formed P" and target: "schema_system_formed Q"
    and agree: "systems_agree_on P Q (system_definitions P\<inter>system_definitions Q)"
    and member: "d\<in>system_definitions Q" and clause: "((d,c),S)\<in>system_clauses P"
    and callee: "e\<in>schema_dependencies S"
  shows "e\<in>system_definitions P \<and> e\<in>system_definitions Q"
proof -
  have "d\<in>system_definitions P" using formed clause unfolding schema_system_formed_def by blast
  moreover have "(d,e)\<in>system_dependency_edges P"
    using clause callee by (force simp: system_dependency_edges_def schema_dependencies_def rel_ran_def)
  ultimately show ?thesis
    using systems_agree_on_intersection_closed[OF formed target agree] member
    unfolding system_dependency_closed_def by blast
qed

subsection \<open>The program agrees with the guard over additions, AX2a's program and the given's readers\<close>

lemma asked_additions_guard_joined:
  "systems_agree_on additions_guard_system asked_additions_joined_system (system_definitions additions_guard_system)"
  unfolding asked_additions_joined_system_def
  by (rule system_union_agree_right[OF given_program_formed asked_additions_overlap_agreement])

lemma asked_additions_package_joined:
  "systems_agree_on extension_package_system asked_additions_joined_system (system_definitions extension_package_system)"
proof -
  have pair: "systems_agree_on extension_package_system additions_pair_readers_system
      (system_definitions extension_package_system)"
    unfolding additions_pair_readers_system_def
    by (rule system_union_agree_right[OF extension_formation_system_formed formation_package_agreement])
  have readers: "systems_agree_on additions_pair_readers_system additions_readers_system
      (system_definitions additions_pair_readers_system)"
    unfolding additions_readers_system_def
    by (rule system_union_agree_left[OF payload_audit_system_formed pair_audit_agreement])
  show ?thesis
    by (rule whole_agreement_transitive[OF whole_agreement_transitive[OF whole_agreement_transitive[OF
      whole_agreement_transitive[OF pair readers] additions_goals_agreement] additions_guard.guarded_old_agreement]
      asked_additions_guard_joined])
qed

lemma asked_additions_rooted_agreement:
  assumes "systems_agree_on X asked_additions_joined_system (system_definitions X)"
  shows "systems_agree_on X asked_additions_program_system
    (system_definitions X\<inter>system_definitions asked_additions_program_system)"
  unfolding asked_additions_program_system_def by (rule rooted_intersection_agreement[OF assms])

lemma asked_additions_guard_readers_agreement:
  "systems_agree_on guard_readers_system asked_additions_program_system
    (system_definitions guard_readers_system\<inter>system_definitions asked_additions_program_system)"
  by (rule asked_additions_rooted_agreement[OF whole_agreement_transitive[OF guard_program_agreement
    asked_additions_given_agreement]])

lemma asked_additions_sites: "{5,12,47,76,82,113,390,391}\<subseteq>system_definitions asked_additions_program_system"
  using given_rooted_read_sites(1) asked_additions_readers_inside by blast

subsection \<open>The sites the bound reads stand in the program\<close>

text \<open>990's guard calls 981, whose view calls 961; 961's added-site clause calls 964, its clause 960, and 960's 959.\<close>

lemma asked_additions_reached:
  "981\<in>system_definitions asked_additions_program_system" "961\<in>system_definitions asked_additions_program_system"
  "964\<in>system_definitions asked_additions_program_system" "960\<in>system_definitions asked_additions_program_system"
  "959\<in>system_definitions asked_additions_program_system"
proof -
  note guard=agreeing_clause_callee[OF asked_additions_guard_formed asked_additions_program_formed
    asked_additions_rooted_agreement[OF asked_additions_guard_joined]]
  note goals=agreeing_clause_callee[OF additions_goals_formed asked_additions_program_formed
    asked_additions_rooted_agreement[OF whole_agreement_transitive[OF additions_guard.guarded_old_agreement
      asked_additions_guard_joined]]]
  note package=agreeing_clause_callee[OF extension_package_system_formed asked_additions_program_formed
    asked_additions_rooted_agreement[OF asked_additions_package_joined]]
  have c990: "((990,0),requirement_guard_schema additions_requirements)\<in>system_clauses additions_guard_system"
    by (simp add: additions_guard.guarded_clauses)
  have d981: "981\<in>schema_dependencies (requirement_guard_schema additions_requirements)"
    by (force simp: schema_dependencies_def rel_ran_def requirement_guard_schema_def additions_requirements_def)
  show a981: "981\<in>system_definitions asked_additions_program_system"
    using guard[OF asked_additions_entry_member c990 d981] by blast
  have c981: "((981,0),additions_package_schema)\<in>system_clauses additions_goals_system"
    by (simp add: additions_goals_families)
  have d961: "961\<in>schema_dependencies additions_package_schema"
    by (force simp: schema_dependencies_def rel_ran_def additions_package_schema_def)
  show a961: "961\<in>system_definitions asked_additions_program_system"
    using goals[OF a981 c981 d961] by blast
  have c961: "((961,0),extension_added_site_schema)\<in>system_clauses extension_package_system"
    by (simp add: extension_package_families extension_package_clauses_def)
  have d964: "964\<in>schema_dependencies extension_added_site_schema"
    by (force simp: schema_dependencies_def rel_ran_def extension_added_site_schema_def)
  show a964: "964\<in>system_definitions asked_additions_program_system"
    using package[OF a961 c961 d964] by blast
  have c964: "((964,0),added_site_schema)\<in>system_clauses extension_package_system"
    by (simp add: extension_package_families)
  have d960: "960\<in>schema_dependencies added_site_schema"
    by (force simp: schema_dependencies_def rel_ran_def added_site_schema_def)
  show a960: "960\<in>system_definitions asked_additions_program_system"
    using package[OF a964 c964 d960] by blast
  have c960: "((960,0),bounded_closure_schema)\<in>system_clauses extension_package_system"
    by (simp add: extension_package_families)
  have d959: "959\<in>schema_dependencies bounded_closure_schema"
    by (force simp: schema_dependencies_def rel_ran_def bounded_closure_schema_def)
  show "959\<in>system_definitions asked_additions_program_system"
    using package[OF a960 c960 d959] by blast
qed

lemma asked_additions_package_meaning:
  assumes "d\<in>system_definitions extension_package_system" "d\<in>system_definitions asked_additions_program_system"
  shows "(d,t)\<in>positive_meaning asked_additions_program_system \<longleftrightarrow> (d,t)\<in>positive_meaning extension_package_system"
  using positive_meaning_shared_definitions[OF extension_package_system_formed asked_additions_program_formed
    asked_additions_rooted_agreement[OF asked_additions_package_joined] assms] by blast

lemma asked_additions_members_meaning:
  "(959,t)\<in>positive_meaning asked_additions_program_system \<longleftrightarrow> (959,t)\<in>positive_meaning extension_package_system"
  by (rule asked_additions_package_meaning[OF _ asked_additions_reached(5)]) simp

text \<open>The program's definitions are the given's, below 506, and the guard over additions', 950 to 966 and 980 to 992.\<close>

lemma asked_additions_bound:
  "system_definitions asked_additions_program_system\<subseteq>{..<506}\<union>
    {950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966}\<union>
    {980,981,982,983,984,985,986,987,988,989,990,991,992}"
proof
  fix x assume x: "x\<in>system_definitions asked_additions_program_system"
  have "system_definitions asked_additions_program_system\<subseteq>system_definitions asked_additions_joined_system"
    unfolding asked_additions_program_system_def by (rule rooted_system_subdomain)
  then have "x\<in>system_definitions given_program_system \<or> x\<in>system_definitions additions_guard_system"
    using x by (simp only: asked_additions_joined_definitions) blast
  then show "x\<in>{..<506}\<union>{950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966}\<union>
      {980,981,982,983,984,985,986,987,988,989,990,991,992}"
  proof
    assume "x\<in>system_definitions given_program_system"
    then show ?thesis using asked_additions_given_below by blast
  next
    assume g: "x\<in>system_definitions additions_guard_system"
    show ?thesis
    proof (cases "x\<in>{980,981,982,983,984,985,986,987,988,989,990,991,992} \<or> x\<in>{950,951,952,953,954} \<or>
        x\<in>{955,956,957,958,959,960,961,962,963,964,965,966}")
      case True then show ?thesis by blast
    next
      case False
      then have far: "x\<notin>{980,981,982,983,984,985,986,987,988,989,990,991,992}" "x\<notin>{950,951,952,953,954}"
        "x\<notin>{955,956,957,958,959,960,961,962,963,964,965,966}" by blast+
      have readers: "x\<in>system_definitions additions_readers_system" using g far(1) asked_additions_guard_bound by blast
      have audit: "system_definitions payload_audit_system\<subseteq>system_definitions guard_readers_system"
        by (simp only: guard_readers_definitions) blast
      have "x\<in>system_definitions guard_readers_system"
        using readers far(2,3) lookup_complete_definitions membership_complete_definitions asked_additions_complete_guard
          audit unfolding additions_readers_definitions extension_formation_sites extension_package_sites by blast
      then have "x\<in>system_definitions given_program_system"
        using whole_agreement_definitions[OF guard_program_agreement] by blast
      then show ?thesis using asked_additions_given_below by blast
    qed
  qed
qed

lemma asked_additions_absent_clauses:
  "((525,c),S) |\<notin>| finite_system_clauses finite_asked_additions_program"
  "((561,c),S) |\<notin>| finite_system_clauses finite_asked_additions_program"
proof -
  have absent: "((d,c),S) |\<notin>| finite_system_clauses finite_asked_additions_program"
    if outside: "d\<notin>system_definitions asked_additions_program_system" for d
  proof
    assume "((d,c),S) |\<in>| finite_system_clauses finite_asked_additions_program"
    then have "((d,c),decode_finite_schema S)\<in>system_clauses asked_additions_program_system"
      by (simp only: finite_system_clause_decoded finite_asked_additions_program_exact)
    then have "d\<in>system_definitions asked_additions_program_system"
      using asked_additions_program_formed unfolding schema_system_formed_def by blast
    then show False using outside by blast
  qed
  show "((525,c),S) |\<notin>| finite_system_clauses finite_asked_additions_program"
    by (rule absent) (use asked_additions_bound in auto)
  show "((561,c),S) |\<notin>| finite_system_clauses finite_asked_additions_program"
    by (rule absent) (use asked_additions_bound in auto)
qed

subsection \<open>The registrations complete there\<close>

theorem asked_additions_registrations_complete_in:
  assumes exact: "finite_query_exact \<Xi> finite_asked_additions_program n"
  shows "finite_registration_complete_in \<Xi> finite_asked_additions_program n bound_witness_registration"
  "finite_registration_complete_in \<Xi> finite_asked_additions_program n (additions_witness_registration 392 391)"
  "finite_registration_complete_in \<Xi> finite_asked_additions_program n merge_witness_registration"
  "finite_registration_complete_in \<Xi> finite_asked_additions_program n extension_bound_registration"
proof -
  note by_agreement=readers_agreement_registrations_complete_in[where P=finite_asked_additions_program,
    unfolded finite_asked_additions_program_exact, OF exact asked_additions_program_formed
    asked_additions_guard_readers_agreement asked_additions_sites]
  note read=readers_agreement_meanings[OF asked_additions_program_formed asked_additions_guard_readers_agreement
    asked_additions_sites]
  show "finite_registration_complete_in \<Xi> finite_asked_additions_program n bound_witness_registration"
    by (rule by_agreement(1))
  show "finite_registration_complete_in \<Xi> finite_asked_additions_program n (additions_witness_registration 392 391)"
    by (rule by_agreement(2))
  show "finite_registration_complete_in \<Xi> finite_asked_additions_program n merge_witness_registration"
    by (rule by_agreement(3))
  show "finite_registration_complete_in \<Xi> finite_asked_additions_program n extension_bound_registration"
    by (rule extension_bound_registration_complete_in[OF exact])
      (simp_all only: finite_asked_additions_program_exact read(3) read(5) read(7) asked_additions_members_meaning)
qed

lemmas asked_additions_registrations_complete = asked_additions_registrations_complete_in[OF finite_query_exact_plain]

subsection \<open>The construction complete and the resolver exact there\<close>

definition asked_additions_registrations :: "(nat,nat,nat,nat) collection_registration list" where
  "asked_additions_registrations=given_witness_registrations@[extension_bound_registration]"

theorem asked_additions_construction_complete_in:
  assumes exact: "finite_query_exact \<Xi> finite_asked_additions_program n"
  shows "finite_construction_complete (finite_collection_construction_in \<Xi> asked_additions_registrations n)
    finite_asked_additions_program"
proof (rule finite_collection_construction_complete_at)
  fix R c
  assume R: "R \<in> set asked_additions_registrations"
    and clause: "((registration_site R,c),registration_schema R) |\<in>| finite_system_clauses finite_asked_additions_program"
  show "finite_registration_complete_in \<Xi> finite_asked_additions_program n R"
    using R clause asked_additions_registrations_complete_in[OF exact] asked_additions_absent_clauses(1) registration_sites
    by (auto simp: asked_additions_registrations_def given_witness_registrations_def)
qed

lemmas asked_additions_construction_complete = asked_additions_construction_complete_in[OF finite_query_exact_plain]

lemmas asked_additions_resolution_refutation_exact =
  finite_complete_resolution_refutation_exact[OF finite_collection_construction_formed asked_additions_construction_complete]

lemmas asked_additions_verdict_exact =
  finite_complete_verdict_exact[OF finite_collection_construction_formed asked_additions_construction_complete]

lemmas asked_additions_demand_exact =
  finite_complete_demand_exact[OF finite_collection_construction_formed asked_additions_construction_complete]

text \<open>The meaning at the numbered entry is the installed entry's.\<close>

lemma asked_additions_entry_numbered_meaning:
  "(asked_additions_entry,t)\<in>positive_meaning asked_additions_program \<longleftrightarrow>
    (990,t)\<in>positive_meaning (decode_finite_system finite_asked_additions_program)"
  unfolding asked_additions_entry_def finite_asked_additions_program_exact
  by (rule asked_additions_installed_meaning[OF asked_additions_entry_member])

subsection \<open>The placed program, the registrations relocated\<close>

definition asked_additions_placed_program where
  "asked_additions_placed_program=finite_rename_system asked_additions_placement finite_asked_additions_program"

definition asked_additions_relocated_construction where
  "asked_additions_relocated_construction n=finite_relocated_construction asked_additions_placement
    finite_asked_additions_program (finite_collection_construction asked_additions_registrations n)"

theorem asked_additions_relocated_construction_complete:
  "finite_construction_complete (asked_additions_relocated_construction n) asked_additions_placed_program"
  unfolding asked_additions_relocated_construction_def asked_additions_placed_program_def asked_additions_placement_def
  by (rule given_readers_extension.relocated_complete[OF asked_additions_extension.readers_extension
    asked_additions_construction_complete])

lemma asked_additions_relocated_formed: "finite_witness_construction_formed (asked_additions_relocated_construction n)"
  unfolding asked_additions_relocated_construction_def asked_additions_placement_def
  by (rule finite_relocated_construction_formed[OF finite_collection_construction_formed])

lemmas asked_additions_placed_resolution_refutation_exact =
  given_readers_extension.placed_resolution_refutation_exact[OF asked_additions_extension.readers_extension
    finite_collection_construction_formed asked_additions_construction_complete,
    folded asked_additions_placement_def asked_additions_relocated_construction_def asked_additions_placed_program_def]

lemmas asked_additions_placed_verdict_exact =
  given_readers_extension.placed_verdict_exact[OF asked_additions_extension.readers_extension
    finite_collection_construction_formed asked_additions_construction_complete,
    folded asked_additions_placement_def asked_additions_relocated_construction_def asked_additions_placed_program_def]

lemmas asked_additions_placed_demand_exact =
  given_readers_extension.placed_demand_exact[OF asked_additions_extension.readers_extension
    finite_collection_construction_formed asked_additions_construction_complete,
    folded asked_additions_placement_def asked_additions_relocated_construction_def asked_additions_placed_program_def]

lemma asked_additions_placed_meaning:
  assumes "d\<in>system_definitions asked_additions_program_system"
  shows "(asked_additions_placement d,t)\<in>positive_meaning (decode_finite_system asked_additions_placed_program) \<longleftrightarrow>
    (d,t)\<in>positive_meaning asked_additions_program_system"
  using asked_additions_extension.placed_meaning[of d t] assms
  unfolding asked_additions_placed_program_def asked_additions_placement_def finite_asked_additions_program_exact by simp

subsection \<open>The clause the bound names\<close>

text \<open>960's one clause at the program is AX2a's, by the program's agreement with AX2a's program there.\<close>

lemma asked_additions_bound_clause:
  "((960,c),S) |\<in>| finite_system_clauses finite_asked_additions_program \<longleftrightarrow>
    c=0 \<and> finite_schema_of bounded_closure_schema=S"
proof -
  have ext960: "960\<in>system_definitions extension_package_system" by simp
  have at960: "((960,c),T)\<in>system_clauses asked_additions_program_system \<longleftrightarrow> c=0 \<and> T=bounded_closure_schema"
    for c T
  proof -
    have "((960,c),T)\<in>system_clauses asked_additions_program_system \<longleftrightarrow>
        ((960,c),T)\<in>system_clauses extension_package_system"
      using asked_additions_rooted_agreement[OF asked_additions_package_joined] ext960 asked_additions_reached(4)
      unfolding systems_agree_on_def by blast
    then show ?thesis by (simp only: extension_package_families)
  qed
  have formed: "schema_formed bounded_closure_schema"
    using asked_additions_program_formed at960[of 0 bounded_closure_schema] unfolding schema_system_formed_def by blast
  have eq: "decode_finite_schema S=bounded_closure_schema \<longleftrightarrow> finite_schema_of bounded_closure_schema=S"
    by (metis decode_finite_schema_of[OF formed] decode_finite_schema_injective)
  show ?thesis
    by (simp only: finite_system_clause_decoded finite_asked_additions_program_exact at960 eq)
qed

lemma asked_additions_bound_schema:
  "finite_relation_option (finite_system_clauses finite_asked_additions_program) (960,0)=
    Some (finite_schema_of bounded_closure_schema)"
proof -
  have functional: "finite_relation_functional (finite_system_clauses finite_asked_additions_program)"
    using finite_asked_additions_program_formed by (simp add: finite_system_formed_def)
  show ?thesis
    by (simp only: finite_relation_option_correct[OF functional]) (simp add: asked_additions_bound_clause)
qed

end
