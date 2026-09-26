theory Development_First_Request_Registrations
  imports Development_First_Request_Program Development_Rooted_Registrations
begin

text \<open>
  The given's four witness registrations (\<open>Factor_Reader_Witness_Registrations\<close>) at the first request's program
  (@{const finite_first_request_program}, the views 560 and 561 over the given's joined readers, rooted at the
  given's reader entries and 561), and relocated at its installation. A registration's completeness depends on the
  program's meanings and is not carried from another program: it is discharged here by agreement with the given's
  readers (@{thm [source] readers_agreement_registrations_complete}): the program agrees with them on their common
  definitions, so at the read sites it means what they mean (@{thm [source] readers_agreement_meanings}). The program
  holds the clauses of 77, 392 and 561; 525's stands in the guard's goals program, and names no clause here.
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

lemma first_request_readers_guard_agreement:
  "systems_agree_on guard_readers_system first_request_program_system
    (system_definitions guard_readers_system\<inter>system_definitions first_request_program_system)"
  unfolding first_request_program_system_def by (rule rooted_intersection_agreement[OF guard_first_request_agreement])

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

lemma first_request_read_sites:
  "d\<in>{5,12,47,76,82,113,390,391} \<Longrightarrow> d\<in>system_definitions first_request_program_system"
  "d\<in>{5,12,47,76,82,113,390,391} \<Longrightarrow> d\<in>system_definitions guard_readers_system"
  using first_request_readers_inside given_rooted_read_sites by blast+

lemma first_request_sites: "{5,12,47,76,82,113,390,391}\<subseteq>system_definitions first_request_program_system"
  using first_request_read_sites(1) by blast

lemma first_request_read_meaning:
  assumes "d\<in>{5,12,47,76,82,113,390,391}"
  shows "(d,t)\<in>positive_meaning first_request_program_system \<longleftrightarrow> (d,t)\<in>positive_meaning guard_readers_system"
  by (rule readers_agreement_meanings(2)[OF first_request_program_formed first_request_readers_guard_agreement
    first_request_sites assms])

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
  by (simp_all only: readers_agreement_meanings(3,4,5,6,7,8)[OF first_request_program_formed
    first_request_readers_guard_agreement first_request_sites])

lemma first_request_listing: "context_list_rule_relation (positive_meaning first_request_program_system) 390 391"
  by (rule readers_agreement_meanings(9)[OF first_request_program_formed first_request_readers_guard_agreement
    first_request_sites])

section \<open>The registrations and the construction complete at the program\<close>

text \<open>
  The program agrees with the given's readers on their common definitions (@{thm [source] rooted_intersection_agreement}),
  so the registrations are complete at it by agreement (@{thm [source] readers_agreement_registrations_complete}).
\<close>

theorem first_request_registrations_complete:
  "finite_registration_complete finite_first_request_program n bound_witness_registration"
  "finite_registration_complete finite_first_request_program n (additions_witness_registration 392 391)"
  "finite_registration_complete finite_first_request_program n merge_witness_registration"
proof -
  note by_agreement=readers_agreement_registrations_complete[where P=finite_first_request_program,
    unfolded finite_first_request_program_exact, OF first_request_program_formed first_request_readers_guard_agreement
    first_request_sites]
  show "finite_registration_complete finite_first_request_program n bound_witness_registration"
    by (rule by_agreement(1))
  show "finite_registration_complete finite_first_request_program n (additions_witness_registration 392 391)"
    by (rule by_agreement(2))
  show "finite_registration_complete finite_first_request_program n merge_witness_registration"
    by (rule by_agreement(3))
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
  the placed program, and every variable it registers names a clause of it: the placed course of every extension of
  the given's readers (@{thm [source] given_readers_extension.relocated_complete},
  @{thm [source] given_readers_extension.relocated_clause}), at this installation. The placed program is the program
  the installation compiles into the installed package, whose meaning is the placed program's
  (@{thm [source] first_request_installation}).
\<close>

abbreviation first_request_relocated where
  "first_request_relocated n \<equiv> finite_relocated_construction first_request_placement finite_first_request_program
    (finite_collection_construction given_witness_registrations n)"

abbreviation first_request_placed where
  "first_request_placed \<equiv> finite_rename_system first_request_placement finite_first_request_program"

theorem first_request_relocated_complete:
  "finite_construction_complete (first_request_relocated n) first_request_placed"
  unfolding first_request_placement_def
  by (rule given_readers_extension.relocated_complete[OF first_request_extension.readers_extension
    first_request_construction_complete])

lemma first_request_relocated_clause:
  assumes "a |\<in>| witness_registered (first_request_relocated n) e T"
  shows "\<exists>c. ((e,c),T) |\<in>| finite_system_clauses first_request_placed"
  using assms unfolding first_request_placement_def by (rule given_readers_extension.relocated_clause[OF first_request_extension.readers_extension])

lemma first_request_relocated_formed: "finite_witness_construction_formed (first_request_relocated n)"
  by (rule finite_relocated_construction_formed[OF finite_collection_construction_formed])

lemmas first_request_placed_resolution_refutation_exact =
  given_readers_extension.placed_resolution_refutation_exact[OF first_request_extension.readers_extension finite_collection_construction_formed
    first_request_construction_complete, folded first_request_placement_def]

lemmas first_request_placed_verdict_exact =
  given_readers_extension.placed_verdict_exact[OF first_request_extension.readers_extension finite_collection_construction_formed
    first_request_construction_complete, folded first_request_placement_def]

lemmas first_request_placed_demand_exact =
  given_readers_extension.placed_demand_exact[OF first_request_extension.readers_extension finite_collection_construction_formed
    first_request_construction_complete, folded first_request_placement_def]

text \<open>
  Each definition means at its placed site in the placed program what it means in the program, and so what the
  installed program means there (@{thm [source] given_readers_extension.placed_meaning}).
\<close>

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
